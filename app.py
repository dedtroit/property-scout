import os, re, time, threading, csv, io, sqlite3, json
from pathlib import Path
from datetime import datetime, timezone
from urllib.parse import quote_plus, urlparse
import requests
from flask import Flask, render_template_string, jsonify
app=Flask(__name__)
CITIES=['Roseville','Rocklin','Antelope','Citrus Heights','Folsom','Granite Bay','Orangevale']
DISTRESS=re.compile(r'\b(bank[ -]owned|reo|foreclos\w*|short sale|tax delinquent|tax default\w*|estate sale|probate|fixer|motivated seller)\b',re.I)
CASH=re.compile(r'\b(cash only|all cash only|no financing|cash buyers only|will not qualify for financing|minimum (?:down payment|down) (?:of )?(?:1[3-9]|[2-9]\d|100)%)\b',re.I)
CONV=re.compile(r'\b(conventional(?: financing| loan)?|financing accepted)\b',re.I)
lock=threading.Lock(); state={'rejected':[],'listings':[],'errors':[],'updated':None,'running':False}
def safeurl(s):
    return s if isinstance(s,str) and urlparse(s).scheme in ('https','http') and urlparse(s).netloc else ''
def listing_price(raw, source=None):
    keys=('listPrice','listingPrice','askingPrice','salePrice','price','list_price','listing_price','asking_price','priceFormatted','formattedPrice','priceDisplay')
    if source in ('hud','fanniemae','freddiemac','redfin'):keys=keys+('openingBid',)
    for obj in (raw,raw.get('pricing'),raw.get('listing'),raw.get('property')):
        if not isinstance(obj,dict):continue
        normalized={re.sub(r'[^a-z0-9]','',str(k).lower()):v for k,v in obj.items()}
        for key in keys:
            value=normalized.get(re.sub(r'[^a-z0-9]','',key.lower()))
            if isinstance(value,dict):
                value=value.get('amount') or value.get('value') or value.get('formatted')
            if isinstance(value,bool) or value is None:continue
            m=re.fullmatch(r'\s*'+re.escape(chr(36))+'?'+r'\s*([\d,]+(?:\.\d+)?)\s*([kKmM]?)\s*',str(value))
            if m:
                amount=float(m.group(1).replace(',',''))*{'':1,'k':1000,'m':1000000}[m.group(2).lower()]
                if amount>0:return amount
    return None

def restrictions(raw):
    prop=raw.get('property') if isinstance(raw.get('property'),dict) else {}
    text=' '.join(str(obj.get(k) or '') for obj in (raw,prop) for k in ('propertyType','propertyTypeGroup','property_type','type','subType','propertySubType','remarks','description','title','financing','community','assetType'))
    if re.search(r'\b(?:mobile|manufactured|modular)\s*(?:home|housing|house)?\b|\btrailer park\b|\b(?:space|lot)\s+rent\b',text,re.I):return 'Mobile or manufactured home'
    unknown=True
    for obj in (raw,prop,raw.get('hoa'),raw.get('association')):
        if not isinstance(obj,dict):continue
        for k,v in obj.items():
            key=re.sub(r'[^a-z0-9]','',str(k).lower())
            if key in ('hoa','hoafee','hoafees','hoaamount','monthlyhoa','hoamonthly','hoaassociation','hashoa','associationfee','associationfee2','associationyn','hasassociation','associationfeeamount','hoafeeamount'):
                if isinstance(v,bool):
                    if v:return 'HOA present'
                    unknown=False
                elif isinstance(v,(str,int,float)):
                    val=str(v).strip().lower()
                    if val in ('yes','true','y','required'):return 'HOA present'
                    if val in ('no','false','n','none','no hoa','not applicable'):unknown=False
                    else:
                        try:
                            amount=float(val.replace(chr(36),'').replace(',','').strip())
                            if amount>0:return 'HOA fee present'
                            if amount==0:unknown=False
                        except ValueError:pass
        if obj is raw.get('hoa') or obj is raw.get('association'):
            for k in ('fee','amount','monthlyFee','required','exists'):
                if k not in obj:continue
                v=obj[k]
                if v is True:return 'HOA present'
                if v is False:unknown=False;continue
                try:
                    amount=float(str(v).replace(chr(36),'').replace(',',''))
                    if amount>0:return 'HOA fee present'
                    if amount==0:unknown=False
                except (TypeError,ValueError):pass
    if re.search(r'\b(?:no HOA|no homeowners association|without an? HOA|HOA[: ]+none)\b',text,re.I):unknown=False
    if re.search(r'\b(?:HOA required|mandatory HOA|HOA dues|HOA fees|association dues|HOA community|HOA fee)\b',text,re.I) and not re.search(r'\b(?:no HOA|zero HOA|HOA fee[: ]+0)\b',text,re.I):return 'HOA indicated'
    return 'HOA status unverified' if unknown else ''

def closing_status(raw):
    for obj in (raw,raw.get('terms'),raw.get('financing'),raw.get('property')):
        if not isinstance(obj,dict):continue
        for k in ('closingDays','maxClosingDays','settlementDays','paymentDeadlineDays','daysToClose','closeWithinDays'):
            try:
                v=obj.get(k)
                if v is not None and not isinstance(v,bool):
                    days=float(v)
                    if days>0:
                        return ('Closing too short' if days<21 else '21-day closing appears possible')
            except (TypeError,ValueError):pass
    text=' '.join(str(raw.get(k) or '') for k in ('remarks','description','financing','terms','closingTerms','saleTerms'))
    for m in re.finditer(r'(?:clos(?:e|ing)|settlement|payment|balance(?:\s+due)?)\s*(?:must\s+be\s+completed\s+)?(?:within|in|no\s+later\s+than)\s+(\d+)\s*(?:calendar\s+|business\s+)?days',text,re.I):
        if int(m.group(1))<21:return 'Closing too short'
    if re.search(r'\b(?:21|30|45|60)[ -]day closing (?:accepted|available|allowed)\b',text,re.I):return '21-day closing appears possible'
    return '21-day closing unverified'

def normalize(raw, source):
    a=raw.get('address') or {}; a=a if isinstance(a,dict) else {'full':a}
    city=str(a.get('city') or raw.get('city') or '').strip().title()
    if city not in CITIES or str(a.get('state') or raw.get('state') or '').upper() not in ('CA','CALIFORNIA'): return
    price=listing_price(raw)
    close=closing_status(raw)
    if close=='Closing too short':return
    if price is None or not 0<price<260000:return
    restriction=restrictions(raw)
    if restriction and restriction!='HOA status unverified':return
    prop=raw.get('property') if isinstance(raw.get('property'),dict) else {}; typ=str(raw.get('property_type') or prop.get('type') or '').lower().replace('_',' ').replace('-',' '); sub=str(prop.get('subType') or '').lower().replace('_',' ').replace('-',' ')
    if typ not in ('residential','single family','single family residence','singlefamily','house','single family home','single family detached') or any(x in sub+' '+typ for x in ('condo','manufactured','mobile','townhouse','land')):return
    status=str(raw.get('status') or ((raw.get('mls') or {}).get('status') if isinstance(raw.get('mls'),dict) else '') or '').lower().replace('_',' ')
    if status not in ('active','for sale'):return
    remarks=' '.join(str(raw.get(k) or '') for k in ('remarks','description','distress_type','financing'))
    match=DISTRESS.search(remarks)
    if not match or CASH.search(remarks):return
    financing='Conventional mentioned; verify terms' if CONV.search(remarks) and not re.search(r'\b(no|not|cannot accept)\s+conventional\b',remarks,re.I) else 'Financing unverified'
    address=a.get('full') or raw.get('street_address') or ' '.join(str(a.get(k) or '') for k in ('streetNumber','streetName')).strip()
    if not address:return
    photos=raw.get('photos') or []; photos=photos if isinstance(photos,list) else [photos]
    link=safeurl(raw.get('listing_url') or raw.get('url'))
    return dict(closing_status=close,hoa_verified=not bool(restriction),hoa_status=restriction or 'No HOA reported',address=address,city=city,price=price,source=source,distress=match.group(),financing=financing,remarks=remarks[:1800],photos=[safeurl(p) for p in photos if safeurl(p)],url=link,search_url='https://www.google.com/search?q='+quote_plus(address+' '+city+' CA real estate listing'),photo_search='https://www.google.com/search?tbm=isch&q='+quote_plus(address+' '+city+' CA'))
def reserve_request(detail=False):
    # Persist on a mounted Railway volume; rolling 31-day cap protects billing cycles.
    path=os.getenv('QUOTA_DB','/data/quota.sqlite3')
    Path(path).parent.mkdir(parents=True,exist_ok=True)
    with sqlite3.connect(path,timeout=15) as db:
        db.execute('CREATE TABLE IF NOT EXISTS calls (ts REAL)')
        db.execute('BEGIN IMMEDIATE')
        now=time.time()
        db.execute('DELETE FROM calls WHERE ts < ?', (now-31*86400,))
        count=db.execute('SELECT COUNT(*) FROM calls').fetchone()[0]
        daily=db.execute('SELECT COUNT(*) FROM calls WHERE ts >= ?', (now-86400,)).fetchone()[0]
        if count>=190:return False
        db.execute('CREATE TABLE IF NOT EXISTS diagnostic (id INTEGER PRIMARY KEY)')
        # Allow an initial complete regional recovery without changing the monthly cap.
        db.execute('CREATE TABLE IF NOT EXISTS recovery_window (id INTEGER PRIMARY KEY, started REAL)')
        db.execute('INSERT OR IGNORE INTO recovery_window VALUES (1,?)',(now,))
        started=db.execute('SELECT started FROM recovery_window WHERE id=1').fetchone()[0]
        ceiling=14 if now-started<86400 else 7
        if daily>=ceiling or (detail and (daily>=5 or count>=185)):return False
        db.execute('INSERT INTO calls VALUES (?)',(now,))
        return True
def detail_lookup(item,source,key):
    from urllib.parse import quote
    ident=item.get('listingId')
    if not ident:return item,'No listing ID'
    path=Path(os.getenv('QUOTA_DB','/data/quota.sqlite3')).with_name('details.sqlite3')
    with sqlite3.connect(path) as db:
        db.execute('CREATE TABLE IF NOT EXISTS details (id TEXT PRIMARY KEY, ts REAL, payload TEXT)')
        cachekey=source+':'+str(ident)
        cached=db.execute('SELECT ts,payload FROM details WHERE id=?',(cachekey,)).fetchone()
        if cached and time.time()-cached[0]<86400*7:return {**item,**json.loads(cached[1])},'Cached details'
        if not reserve_request(detail=True):return item,'Detail quota reached'
        try:
            response=requests.get('https://foreclosure-finder1.p.rapidapi.com/listing/'+quote(source,safe='')+'/'+quote(str(ident),safe=''),params={'url':item['propertyLink']} if safeurl(item.get('propertyLink')) else {},headers={'X-RapidAPI-Key':key,'X-RapidAPI-Host':'foreclosure-finder1.p.rapidapi.com'},timeout=35,allow_redirects=False)
            response.raise_for_status();payload=response.json()
            if not isinstance(payload,dict):raise ValueError('Unexpected detail format')
            detail=payload.get('listing') or payload.get('data') or payload.get('property') or payload
            if not isinstance(detail,dict):raise ValueError('Unexpected detail format')
            nested=detail.get('details')
            if isinstance(nested,dict):detail={**detail,**nested}
            detail={k:v for k,v in detail.items() if v is not None and v!='' and k not in ('source','listingId','address','city','state','status','statusLabel','propertyLink','openingBid','price','listPrice')}
            db.execute('INSERT OR REPLACE INTO details VALUES (?,?,?)',(cachekey,time.time(),json.dumps(detail)))
            return {**item,**detail},'Details retrieved'
        except Exception as e:return item,'Detail lookup failed: '+type(e).__name__

def hud_snapshot():
    endpoint='https://services.arcgis.com/VTyQ9soqVukalItT/arcgis/rest/services/SF_REO/FeatureServer/0/query'
    path=Path(os.getenv('QUOTA_DB','/data/quota.sqlite3')).with_name('hud_snapshot.json')
    try:old=json.loads(path.read_text())
    except Exception:old={}
    if time.time()-old.get('checked_epoch',0)<86400:return old
    result={'checked_epoch':time.time(),'checked':datetime.now(timezone.utc).isoformat(),'url':'https://catalog.data.gov/dataset/fha-single-family-reo-properties-for-sale','documents':[],'records':old.get('records',[])}
    try:
        where="STATE_CODE = 'CA' AND UPPER(CITY) IN ("+','.join("'"+c.upper()+"'" for c in CITIES)+")"
        response=requests.get(endpoint,params={'where':where,'outFields':'CASE_NUM,ADDRESS,STREET_NUM,STREET_NAME,CITY,STATE_CODE,DISPLAY_ZIP_CODE','returnGeometry':'false','f':'json'},timeout=30)
        response.raise_for_status();payload=response.json()
        if 'error' in payload or 'features' not in payload:raise ValueError('HUD query failed')
        records=[]
        for feature in payload['features']:
            a=feature['attributes']; address=a.get('ADDRESS') or ' '.join(str(a.get(k) or '') for k in ('STREET_NUM','STREET_NAME')).strip()
            if not address:continue
            city=str(a.get('CITY') or '').title()
            records.append({'address':address,'city':city,'case':a.get('CASE_NUM'),'url':'https://www.google.com/search?q='+quote_plus(address+' '+city+' CA HUD home'),'status':'Historical HUD snapshot; asking price, availability, HOA and property type must be verified'})
        result['records']=records
        result['status']=str(len(records))+' local snapshot records; not live listings and no asking prices supplied'
        if payload.get('exceededTransferLimit'):result['status']+='; query truncated'
    except Exception as e:result['status']='HUD dataset check failed: '+type(e).__name__+'; retaining prior snapshot'
    path.parent.mkdir(parents=True,exist_ok=True);tmp=path.with_suffix('.tmp');tmp.write_text(json.dumps(result));tmp.replace(path)
    return result

def public_sources():
    from urllib.robotparser import RobotFileParser
    from urllib.parse import urljoin
    from html.parser import HTMLParser
    import hashlib
    class Links(HTMLParser):
        def __init__(self):
            super().__init__();self.links=[];self.href=None;self.label=[]
        def handle_starttag(self,tag,attrs):
            if tag=='a':
                self.href=dict(attrs).get('href');self.label=[]
        def handle_data(self,data):
            if self.href:self.label.append(data)
        def handle_endtag(self,tag):
            if tag=='a' and self.href:
                self.links.append((self.href,' '.join(' '.join(self.label).split())));self.href=None
    urls={'Sacramento County tax sales':'https://finance.saccounty.gov/us/en/tax/tax/tax-sales.html','Sacramento auction platform':'https://sacramento.mytaxsale.com/auctions'}
    path=Path(os.getenv('QUOTA_DB','/data/quota.sqlite3')).with_name('public_sources.json')
    try:old=json.loads(path.read_text())
    except Exception:old={}
    result={k:v for k,v in old.items() if k in urls}; now=time.time()
    for name,url in urls.items():
        previous=old.get(name,{})
        if now-previous.get('checked_epoch',0)<86400:continue
        record={'url':url,'checked_epoch':now,'checked':datetime.now(timezone.utc).isoformat(),'documents':previous.get('documents',[])}
        try:
            root=urlparse(url); robots=requests.get(root.scheme+'://'+root.netloc+'/robots.txt',timeout=12,headers={'User-Agent':'PropertyScoutBot/1.0'})
            parser=RobotFileParser()
            if robots.status_code==404:parser.parse([])
            elif robots.status_code==200:parser.parse(robots.text.splitlines())
            else:raise ValueError('Robots access unavailable: '+str(robots.status_code))
            if not parser.can_fetch('PropertyScoutBot',url):raise ValueError('Automated access disallowed')
            page=requests.get(url,timeout=20,headers={'User-Agent':'PropertyScoutBot/1.0'},allow_redirects=False);page.raise_for_status()
            if page.status_code!=200:raise ValueError('Redirect or non-HTML response; manual review required')
            links=Links();links.feed(page.text)
            digest=hashlib.sha256(page.text.encode()).hexdigest()
            record['changed']=bool(previous.get('hash') and previous['hash']!=digest);record['hash']=digest
            record['documents']=[{'title':label,'url':urljoin(url,href)} for href,label in links.links if label and 'excess proceeds' not in label.lower() and safeurl(urljoin(url,href)) and re.search(r'auction|tax.default|delinquen|parcel|property list|sale list|notice of sale|homes for sale|search homes|search properties',label,re.I)][:40]
            record['status']='Page checked; linked documents are unverified leads, not qualified homes'
        except Exception as e:record['status']=str(e)[:160] if isinstance(e,ValueError) else 'Fetch failed: '+type(e).__name__
        result[name]=record
    path.parent.mkdir(parents=True,exist_ok=True);tmp=path.with_suffix('.tmp');tmp.write_text(json.dumps(result));tmp.replace(path)
    return result

def rentcast_scan():
    key=os.getenv('RENTCAST_API_KEY')
    if not key:return [],'RentCast: RENTCAST_API_KEY not configured',False
    path=Path(os.getenv('QUOTA_DB','/data/quota.sqlite3')).with_name('rentcast.sqlite3')
    path.parent.mkdir(parents=True,exist_ok=True)
    cache=path.with_suffix('.json')
    try:old=json.loads(cache.read_text())
    except Exception:old={'rows':[]}
    def persist(message, rows, rejected, returned, outcome):
        result={'rows':rows,'rejected':rejected,'returned':returned,'message':message,'outcome':outcome,'checked':datetime.now(timezone.utc).isoformat()}
        tmp=cache.with_suffix('.tmp');tmp.write_text(json.dumps(result));tmp.replace(cache)
        return result
    now=time.time()
    with sqlite3.connect(path,timeout=15) as db:
        db.execute('CREATE TABLE IF NOT EXISTS calls (ts REAL)')
        db.execute('BEGIN IMMEDIATE')
        db.execute('DELETE FROM calls WHERE ts < ?',(now-31*86400,))
        count=db.execute('SELECT COUNT(*) FROM calls').fetchone()[0]
        last=db.execute('SELECT MAX(ts) FROM calls').fetchone()[0] or 0
        # One bounded recovery request when the original result was never recorded.
        recovery=count<9
        if count>=50 or (now-last<31*86400/50 and not recovery):
            state['rentcast_diagnostics']={k:v for k,v in old.items() if k!='rows'}
            state['rentcast_diagnostics'].update({'used':count,'limit':50,'next_eligible':datetime.fromtimestamp(max(last+31*86400/50,(db.execute('SELECT MIN(ts) FROM calls').fetchone()[0] or 0)+31*86400 if count>=50 else 0),timezone.utc).isoformat()})
            return old['rows'],'RentCast: '+str(count)+'/50 requests; '+old.get('message','Previous request outcome was not recorded')+'; waiting for quota interval',False
        db.execute('CREATE TABLE IF NOT EXISTS city_cursor (id INTEGER PRIMARY KEY, next_index INTEGER)')
        cursor=db.execute('SELECT next_index FROM city_cursor WHERE id=1').fetchone()
        index=cursor[0] if cursor else 0
        city=['Citrus Heights','Antelope','Roseville','Rocklin','Orangevale','Folsom','Granite Bay'][index%7]
        db.execute('INSERT OR REPLACE INTO city_cursor VALUES (1,?)',(index+1,))
        db.execute('INSERT INTO calls VALUES (?)',(now,))
    try:
        print('RentCast: starting request '+str(count+1)+'/50',flush=True)
        response=requests.get('https://api.rentcast.io/v1/listings/sale',params={'city':city,'state':'CA','status':'Active','propertyType':'Single Family','price':'1:259999','limit':100},headers={'X-Api-Key':key,'Accept':'application/json'},timeout=(10,90),allow_redirects=False)
        response.raise_for_status();batch=response.json()
        if not isinstance(batch,list):raise ValueError('Unexpected response')
        rows=[]; rejected=[]
        for x in batch:
            def reject(reason):
                rejected.append({'source':'RentCast','address':x.get('formattedAddress') or x.get('addressLine1'),'city':x.get('city'),'price':listing_price(x),'type':x.get('propertyType'),'status':x.get('status'),'reason':reason})
            if str(x.get('city') or '').strip().title() not in CITIES or str(x.get('state')).upper()!='CA':reject('Outside target cities');continue
            price=listing_price(x)
            if price is None or not 0<price<260000:reject('Missing price or outside budget');continue
            if str(x.get('propertyType','')).lower()!='single family':reject('Not single family');continue
            if str(x.get('status','')).lower()!='active':reject('Not active');continue
            restriction=restrictions(x)
            if restriction and restriction!='HOA status unverified':reject(restriction);continue
            if CASH.search(' '.join(str(x.get(k) or '') for k in ('description','remarks','financing','terms'))):reject('Cash only or financing restriction');continue
            if closing_status(x)=='Closing too short':reject('Closing deadline under 21 days');continue
            history=x.get('history') or {}
            past=[v.get('price') for v in history.values() if isinstance(v,dict) and isinstance(v.get('price'),(int,float))] if isinstance(history,dict) else []
            label='Price reduction indicated' if any(p>price for p in past) else 'Budget listing; distress unverified'
            typ=str(x.get('listingType') or '')
            if DISTRESS.search(typ):label=typ
            address=x.get('formattedAddress') or x.get('addressLine1')
            if not address:reject('Missing address');continue
            dom=x.get('daysOnMarket')
            remarks='Listing type: '+(typ or 'Unknown')+'; days on market: '+str(dom if dom is not None else 'Unknown')+'. Seller motivation and financing require verification.'
            rows.append(dict(address=address,city=str(x['city']).title(),price=price,source='RentCast',distress=label,hoa_verified=not bool(restriction),hoa_status=restriction or 'No HOA reported',closing_status='21-day closing unverified',financing='Financing unverified',remarks=remarks,photos=[],url='',search_url='https://www.google.com/search?q='+quote_plus(address+' real estate listing'),photo_search='https://www.google.com/search?tbm=isch&q='+quote_plus(address)))
        message=city+': '+str(len(batch))+' returned; '+str(len(rows))+' local budget candidates; '+str(len(rejected))+' rejected'+('; response at page limit; coverage may be incomplete' if len(batch)>=100 else '')
        rows=[x for x in old.get('rows',[]) if x.get('city')!=city]+rows
        rejected=[x for x in old.get('rejected',[]) if str(x.get('city') or '').title()!=city]+rejected
        print('RentCast: '+message,flush=True)
        record=persist(message,rows,rejected,len(batch),'success');state['rentcast_diagnostics']={k:v for k,v in record.items() if k!='rows'};state['rentcast_diagnostics'].update({'used':count+1,'limit':50})
        return rows,'RentCast: '+str(count+1)+'/50 requests; '+message,True
    except Exception as e:
        message='Request failed: '+(str(e.response.status_code) if isinstance(e,requests.HTTPError) else type(e).__name__)
        print('RentCast: '+message,flush=True)
        record=persist(message,old['rows'],old.get('rejected',[]),old.get('returned'),'error');state['rentcast_diagnostics']={k:v for k,v in record.items() if k!='rows'};state['rentcast_diagnostics'].update({'used':count+1,'limit':50})
        return old['rows'],'RentCast: '+message+'; '+str(count+1)+'/50 requests',False

def property_key(row):
    a=row.get('address') or ''
    if isinstance(a,dict):
        a=a.get('full') or a.get('streetAddress') or a.get('street') or ''
    city=str(row.get('city') or '').strip().lower()
    m=re.search(r',\s*([^,]+),\s*(?:CA|California)(?:\s+\d{5}(?:-\d{4})?)?\s*$',str(a),re.I)
    if m:
        city=city or m.group(1).strip().lower()
        a=str(a)[:m.start()]
    a=re.sub(r'\b(street|avenue|drive|road|court|circle|lane|boulevard|place|way|terrace|parkway)\b',lambda m:{'street':'st','avenue':'ave','drive':'dr','road':'rd','court':'ct','circle':'cir','lane':'ln','boulevard':'blvd','place':'pl','way':'way','terrace':'ter','parkway':'pkwy'}[m.group().lower()],str(a).lower())
    a=re.sub(r'(?:\b(?:unit|apt|apartment|suite)\s*|#\s*)([a-z0-9-]+)',r' unit \1',a)
    return re.sub(r'[^a-z0-9]','',a)+'|'+re.sub(r'[^a-z0-9]','',city) if a else str(row.get('url') or row.get('source') or '')+'|'+str(row.get('price') or '')

def merge_properties(records):
    unique={}
    for row in records:
        key=property_key(row)
        prior=unique.get(key)
        if not prior:
            unique[key]={**row,'sources':list(dict.fromkeys(row.get('sources') or [row.get('source','Unknown')])),'listing_links':list(dict.fromkeys(row.get('listing_links') or ([row['url']] if row.get('url') else [])))}
            continue
        best,other=(row,prior) if (bool(row.get('url')),len(row.get('photos') or []))>(bool(prior.get('url')),len(prior.get('photos') or [])) else (prior,row)
        unique[key]={**best,'sources':list(dict.fromkeys((prior.get('sources') or [prior.get('source','Unknown')])+(row.get('sources') or [row.get('source','Unknown')]))),'listing_links':list(dict.fromkeys((prior.get('listing_links') or [])+(row.get('listing_links') or ([row['url']] if row.get('url') else [])))),'photos':list(dict.fromkeys((best.get('photos') or [])+(other.get('photos') or [])))}
        if prior.get('reason') or row.get('reason'):
            unique[key]['reason']='; '.join(dict.fromkeys(x for x in (prior.get('reason'),row.get('reason')) if x))
    return list(unique.values())

def scan():
    if not lock.acquire(False):return
    state['running']=True; rows=[]; errors=[]; successes=0; rejected=[]; completed_zips=[]; zip_records={}
    provider_cache=Path(os.getenv('QUOTA_DB','/data/quota.sqlite3')).with_name('foreclosure_scan.json')
    try:zip_records=json.loads(provider_cache.read_text())
    except Exception:pass
    try:
        try:
            state['public_sources']=public_sources()
            state['public_sources']['HUD open data snapshot']=hud_snapshot()
        except Exception as e:errors.append('Public sources: '+type(e).__name__)
        key=os.getenv('RAPIDAPI_KEY')
        if key:
            for zipcode in sorted(['95678','95765','95843','95610','95630','95746','95662'],key=lambda z:zip_records.get(z,{}).get('checked','')):
                try:
                    previous=zip_records.get(zipcode,{})
                    if previous.get('checked') and (datetime.now(timezone.utc)-datetime.fromisoformat(previous['checked'])).total_seconds()<86400:continue
                    if not reserve_request():
                        errors.append('Daily or rolling request budget reached; retaining cached results')
                        break
                    response=requests.get('https://foreclosure-finder1.p.rapidapi.com/zipcode/all',params={'zipcode':zipcode,'radius':25,'limit':500,'maxPrice':259999,'minPrice':1000,'sort':'price_asc','sources':'hud,fanniemae,freddiemac,redfin'},headers={'X-RapidAPI-Key':key,'X-RapidAPI-Host':'foreclosure-finder1.p.rapidapi.com'},timeout=65,allow_redirects=False)
                    response.raise_for_status()
                    payload=response.json()
                    meta=payload.get('meta',{})
                    if meta.get('failedSources') or meta.get('totalCount',0)>len(payload.get('listings',[])):errors.append(zipcode+': incomplete source coverage or results truncated')
                    accepted=0; row_start=len(rows); reject_start=len(rejected)
                    for item in payload['listings']:
                        source=re.sub(r'[^a-z0-9]','',str(item.get('source','')).lower())
                        source={'homepath':'fanniemae','homesteps':'freddiemac','hudhomestore':'hud'}.get(source,source)
                        def reject(reason):
                            rejected.append({'reason':reason,'address':item.get('address'),'city':item.get('city'),'price':listing_price(item,source),'price_fields':{k:v for k,v in item.items() if 'price' in k.lower() and isinstance(v,(str,int,float))},'source':source,'type':item.get('propertyType'),'status':item.get('status'),'url':safeurl(item.get('propertyLink') or item.get('url'))})
                        a=item.get('address') or ''
                        if isinstance(a,dict):
                            city=a.get('city') or item.get('city')
                            address=a.get('full') or a.get('streetAddress') or a.get('street') or ''
                            region=a.get('state') or item.get('state')
                        else:
                            address=str(a)
                            match=re.search(r',\s*([^,]+),\s*(?:CA|California)(?:\s+\d{5})?',address,re.I)
                            city=item.get('city') or (match.group(1) if match else '')
                            region=item.get('state') or ('CA' if match else '')
                        if str(city or '').strip().title() not in CITIES or str(region or '').upper() not in ('CA','CALIFORNIA'):
                            reject('Outside target cities or missing location');continue
                        status=str(item.get('status','')).lower().replace('_',' ')
                        label=str(item.get('statusLabel','')).lower().replace('_',' ')
                        if any(x in status+' '+label for x in ('pending','sold','closed','cancel','off market','auction','withdrawn','coming soon')):reject('Unavailable or auction status');continue
                        # Non-auction REO search results can omit or use source-specific status labels.
                        if any(x in status+' '+label for x in ('unavailable','not for sale','inactive','under contract')):reject('Unavailable status');continue
                        if source not in ('hud','fanniemae','freddiemac','redfin'):reject('Unsupported source');continue
                        price=listing_price(item,source)
                        if price is None:reject('Missing asking price');continue
                        if closing_status(item)=='Closing too short':reject('Closing deadline under 21 days');continue
                        early_type=str(item.get('propertyType') or item.get('propertyTypeGroup') or '').lower().replace('_',' ').replace('-',' ')
                        if any(t in early_type for t in ('manufactured','mobile','condo','townhouse','land')):reject('Excluded property type');continue
                        if source in ('hud','fanniemae','freddiemac') and 0<price<260000:
                            item,detail_status=detail_lookup(item,source,key)
                            errors.append(str(address)+': '+detail_status)
                        restriction=restrictions(item)
                        if restriction and restriction!='HOA status unverified':reject(restriction);continue
                        if not 0<price<260000:reject('Price outside budget');continue
                        typ=str(item.get('propertyTypeGroup') or item.get('propertyType') or '').lower().replace('_',' ').replace('-',' ')
                        if typ in ('single family residential','single family house','single family dwelling'):typ='single family home'
                        photos=item.get('photos') or item.get('photoUrl') or item.get('photo') or []
                        row=normalize({**item,'address':address,'city':city,'state':'CA','price':price,'listPrice':price,'property_type':typ,'status':'active','distress_type':str(item.get('assetType') or '').replace('_',' ')+' '+('bank owned' if source!='redfin' else 'foreclosure'),'description':item.get('description'),'financing':item.get('financing'),'photos':photos,'listing_url':item.get('propertyLink')},source)
                        if row:rows.append(row);accepted+=1
                        else:reject('Property type, address or financing restriction')
                    successes+=1
                    errors.append(zipcode+': '+str(len(payload['listings']))+' source listings; '+str(accepted)+' matched; source failures: '+str(meta.get('failedSources',[])))
                    failed=set(re.sub(r'[^a-z0-9]','',str(v).lower()) for v in (meta.get('failedSources') or []))
                    previous=zip_records.get(zipcode,{})
                    if failed or meta.get('partial') or meta.get('totalCount',0)>len(payload['listings']):
                        prior_rows=[x for x in previous.get('rows',[]) if x.get('source') in failed or meta.get('partial') or meta.get('totalCount',0)>len(payload['listings'])]
                        rows.extend(prior_rows)
                        rejected.extend(x for x in previous.get('rejected',[]) if x.get('source') in failed)
                    zip_records[zipcode]={'rows':rows[row_start:],'rejected':rejected[reject_start:],'message':errors[-1],'checked':datetime.now(timezone.utc).isoformat(),'source_counts':{name:sum(1 for item in payload['listings'] if re.sub(r'[^a-z0-9]','',str(item.get('source','')).lower())==name) for name in ('hud','fanniemae','freddiemac','redfin')},'failed_sources':list(failed)};completed_zips.append(zipcode)
                    tmp=provider_cache.with_suffix('.tmp');tmp.write_text(json.dumps(zip_records));tmp.replace(provider_cache)
                    print(errors[-1],flush=True)
                except requests.HTTPError as e:
                    errors.append(zipcode+': HTTP '+str(e.response.status_code));print(errors[-1],flush=True)
                    if e.response.status_code in (401,403,429):break
                except Exception as e:errors.append(zipcode+': '+type(e).__name__);print(errors[-1],flush=True)
                if 'response' in locals() and response.status_code==429:break
        else:errors.append('RAPIDAPI_KEY not configured')
        for zipcode,record in zip_records.items():
            if zipcode not in completed_zips:
                rows.extend(record.get('rows',[]));rejected.extend(record.get('rejected',[]));errors.append('Cached '+record.get('message',zipcode))
        state['foreclosure_diagnostics']={k:{a:b for a,b in v.items() if a not in ('rows','rejected')} for k,v in zip_records.items()}
        for name,source in [('HomePath','fanniemae'),('HomeSteps','freddiemac'),('HUD listing feed','hud'),('Redfin','redfin')]:
            checked=[v for v in zip_records.values() if 'source_counts' in v]
            count=sum(v['source_counts'].get(source,0) for v in checked)
            failed=sum(source in v.get('failed_sources',[]) for v in checked)
            state.setdefault('public_sources',{})[name]={'url':'https://foreclosureapi.com/','status':(str(count)+' returned source records across '+str(len(checked))+' cached ZIP searches (may overlap); '+str(failed)+' failed source checks') if checked else 'Awaiting first recorded inventory response','documents':[]}
        if not completed_zips and not zip_records:
            rows.extend(x for x in state['listings'] if x.get('source')!='RentCast')
            rejected.extend(x for x in state['rejected'] if x.get('source')!='RentCast')
        for feed in os.getenv('AUTHORIZED_FEEDS','').split(','):
            if not feed.strip():continue
            try:
                r=requests.get(feed.strip(),timeout=25);r.raise_for_status(); batch=r.json() if 'json' in r.headers.get('Content-Type','') else list(csv.DictReader(io.StringIO(r.text)))
                rows.extend(filter(None,(normalize(x,urlparse(feed).netloc) for x in batch)))
                successes+=1
            except Exception as e:errors.append('Feed '+urlparse(feed).netloc+': '+type(e).__name__)
        # Bootstrap every city rather than waiting 15 hours between first searches.
        for _ in range(7):
            rent_rows,rent_message,rent_success=rentcast_scan()
            errors.append(rent_message)
            print(rent_message,flush=True)
            if 'waiting for quota interval' in rent_message or 'not configured' in rent_message:break
            if state.get('rentcast_diagnostics',{}).get('used',50)>=9:break
        rejected.extend(state.get('rentcast_diagnostics',{}).get('rejected',[]))
        if rent_success or rent_rows:
            rows.extend(rent_rows);successes+=1
        if zip_records:successes+=1
        # Earlier rejected records were lost on a cache migration. Restore the actual historical response only as an audit record.
        history=provider_cache.with_name('historical_rejected.json')
        if not history.exists():
            historical=[{"address":"210 Pau Hanna Cir, Citrus Heights, CA 95621","price":84900,"reason":"Excluded manufactured home","source":"redfin","type":"MANUFACTURED_HOME","url":"https://www.redfin.com/CA/Citrus-Heights/210-Pau-Hana-Cir-95621/home/19092113"},{"address":"100 LA CONTERA CT 143, Sacramento, CA 95834","price":144900,"reason":"Outside target cities; condominium","source":"fanniemae","type":"CONDOMINIUM_UNIT","url":"https://homepath.fanniemae.com/property-detail/b0cd8452-eae4-49f2-b517-ad8de1996ef8"},{"address":"4750 GREENHOLME DR UNIT 1, Sacramento, CA 95842","price":169900,"reason":"Outside target cities; condominium","source":"fanniemae","type":"CONDOMINIUM_UNIT","url":"https://homepath.fanniemae.com/property-detail/2b7e1f77-26d5-4793-aafe-bef19df7c21e"},{"address":"11640 Garnet Way #4, Auburn, CA 95602","price":184500,"reason":"Outside target cities; condominium","source":"fanniemae","type":"CONDOMINIUM_UNIT","url":"https://homepath.fanniemae.com/property-detail/259e2b53-2a50-458a-a291-c14b92d9ebcf"},{"address":"14587 Poncho Conde Circle, Rancho Murieta, CA 95683","price":242250,"reason":"Outside target cities; manufactured home","source":"fanniemae","type":"MANUFACTURED_HOME","url":"https://homepath.fanniemae.com/property-detail/67ebb086-25be-4703-aae3-d9ffa2f2f3a1"},{"address":"1965 Benita Dr Unit 2, Rancho Cordova, CA 95670","price":249900,"reason":"Outside target cities","source":"fanniemae","type":"SINGLE_FAMILY_HOME","url":"https://homepath.fanniemae.com/property-detail/bd7c35bc-d91a-4c0f-bc2a-fb367a3e37e8"}]
            history.write_text(json.dumps(historical))
        historical=json.loads(history.read_text())
        # Historical audit rows have no independently verified listing URL.
        historical=[{**x,'url':''} for x in historical]
        known={str(x.get('address')).lower() for x in rejected}
        rejected.extend({**x,'reason':'Historical Nov 25 scan: '+x['reason']} for x in historical if str(x.get('address')).lower() not in known)
        state['rejected']=rejected
        provider_cache.with_name('rejected.json').write_text(json.dumps(rejected))
        rows=merge_properties(rows)
        if successes:
            state['listings']=sorted(rows,key=lambda x:x['price'])
            cache=Path(os.getenv('QUOTA_DB','/data/quota.sqlite3')).with_name('listings.json')
            cache.parent.mkdir(parents=True,exist_ok=True)
            tmp=cache.with_suffix('.tmp');tmp.write_text(json.dumps(state['listings']));tmp.replace(cache)
        if successes:
            state['rejected']=rejected
            Path(os.getenv('QUOTA_DB','/data/quota.sqlite3')).with_name('rejected.json').write_text(json.dumps(rejected))
        state['errors']=errors;state['updated']=datetime.now(timezone.utc).isoformat()
        print('Scan complete: '+str(len(state['listings']))+' candidates; '+str(len(state['rejected']))+' rejected',flush=True)
        diagnostics=provider_cache.with_name('scan_diagnostics.json');tmp=diagnostics.with_suffix('.tmp');tmp.write_text(json.dumps({k:state.get(k) for k in ('errors','updated','rentcast_diagnostics','foreclosure_diagnostics')}));tmp.replace(diagnostics)
    finally:state['running']=False;lock.release()
def loop():
    try:
        cache=Path(os.getenv('QUOTA_DB','/data/quota.sqlite3')).with_name('listings.json')
        if cache.exists():state['listings']=[x for x in json.loads(cache.read_text()) if (x.get('hoa_status') in ('HOA status unverified','No HOA reported') or x.get('hoa_verified') is True) and x.get('closing_status')!='Closing too short']
        diagnostics=cache.with_name('scan_diagnostics.json')
        if diagnostics.exists():state.update(json.loads(diagnostics.read_text()))
        reject_cache=cache.with_name('rejected.json')
        if reject_cache.exists():state['rejected']=json.loads(reject_cache.read_text())
    except Exception:pass
    while True:
        try:scan()
        except Exception as e:
            state['errors']=(state.get('errors') or [])+['Scanner crashed: '+type(e).__name__]
            print('Scanner crashed: '+type(e).__name__,flush=True)
        time.sleep(3*3600)
@app.get('/api/listings')
def listings():
    snapshot=dict(state)
    snapshot['listings']=merge_properties(state.get('listings',[]))
    keys={property_key(x) for x in snapshot['listings']}
    rejected=merge_properties(state.get('rejected',[]))
    overlaps={property_key(x):x for x in rejected if property_key(x) in keys}
    for row in snapshot['listings']:
        other=overlaps.get(property_key(row))
        if other:
            row['review_note']=other.get('reason')
            row['sources']=list(dict.fromkeys(row.get('sources',[])+other.get('sources',[])))
            row['listing_links']=list(dict.fromkeys(row.get('listing_links',[])+other.get('listing_links',[])))
    snapshot['rejected']=[x for x in rejected if property_key(x) not in keys]
    return jsonify(snapshot)
@app.get('/')
def home():return render_template_string(r'''<!doctype html><html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>Property Scout</title><style>
*{box-sizing:border-box}body{margin:0;background:#f5f6f3;color:#203329;font:15px/1.5 system-ui,sans-serif}main{max-width:1200px;margin:auto;padding:28px 20px 60px}h1{margin:2px 0;font-size:36px;letter-spacing:-1.2px}h2{font-size:21px;margin:0}small,.muted{color:#66766c}p{margin:5px 0}header{padding-bottom:18px}nav{display:flex;gap:5px;flex-wrap:wrap;position:sticky;top:0;background:#f5f6f3;padding:10px 0;border-bottom:1px solid #d6dfd5;z-index:3}button,input,select{font:inherit;color:inherit;background:white;border:1px solid #ccd6cd;border-radius:8px;padding:9px 12px}button{cursor:pointer;font-weight:600}nav button{background:transparent;border-color:transparent}nav button[aria-current=true]{color:white;background:#245d46}nav span{font-size:12px;opacity:.8}.filters{display:flex;gap:10px;flex-wrap:wrap;align-items:end;padding:15px 0}.field{display:grid;gap:4px;font-size:12px;font-weight:650}.check{padding:9px 0}.stats{display:flex;gap:10px;flex-wrap:wrap}.stat{background:white;border:1px solid #dce2da;border-radius:10px;padding:10px 16px;flex:1;min-width:120px}.stat strong{display:block;font-size:22px}.toolbar{display:flex;justify-content:space-between;align-items:center;gap:10px;margin:22px 0 10px}.toolbar button[aria-pressed=true]{background:#e3eee5;border-color:#82a48d}#grid{display:grid;gap:10px}.cards{grid-template-columns:repeat(auto-fill,minmax(270px,1fr))}.property{display:grid;grid-template-columns:170px minmax(0,1fr);background:#fff;border:1px solid #dbe2da;border-radius:12px;overflow:hidden}.property.fresh{border-left:3px solid #28674b}.property.noimage{grid-template-columns:1fr}.cards .property{display:flex;flex-direction:column}.cover{background:#e4ebe3;color:#6a7c70;display:grid;place-items:center;min-height:150px;font-size:12px}.cover img{width:100%;height:100%;object-fit:cover;max-height:230px}.cards .cover{height:180px}.noimage .cover{display:none}.content{padding:15px;min-width:0;display:grid;gap:8px}.top{display:flex;justify-content:space-between;gap:10px;align-items:start}.price{font-size:25px;font-weight:750;letter-spacing:-.5px}.address{font-size:16px;font-weight:650;overflow-wrap:anywhere}.tags,.actions{display:flex;gap:6px;flex-wrap:wrap}.tag{font-size:11px;font-weight:650;background:#edf1eb;border-radius:5px;padding:4px 8px}.new{background:#245d46;color:white}.warning{background:#fff1d5;color:#795411}.reason{font-size:13px;color:#72541e;background:#fff7e7;padding:8px 10px;border-radius:6px}.numbers{display:flex;gap:18px;font-size:13px}.actions a,.actions button{font-size:13px;text-decoration:none;border:1px solid #cbd8cd;color:#245d46;border-radius:7px;padding:7px 10px;background:white;font-weight:650}.actions a:first-child{background:#245d46;color:white}.actions button[aria-pressed=true]{background:#e0ede3}.empty{padding:24px;background:white;border:1px solid #dce2da;border-radius:12px;color:#62716a}.source{background:white;border:1px solid #dce2da;border-radius:10px;padding:14px;margin:10px 0}.source a{display:inline-block;margin:5px 10px 0 0;color:#245d46}details{font-size:13px}summary{cursor:pointer;font-weight:600}#diagnostics{white-space:pre-wrap}footer{margin-top:24px;color:#68796e;font-size:12px}[hidden]{display:none!important}@media(max-width:600px){main{padding:18px 12px}.property{grid-template-columns:100px minmax(0,1fr)}.top{flex-wrap:wrap}.filters input[type=search]{max-width:240px}nav button{padding:8px;font-size:12px}}

:root{color-scheme:light;--ink:#182823;--muted:#67756d;--line:#dce3dc;--green:#245d46}body{background:#f4f6f3;color:var(--ink)}main{max-width:1440px;padding:30px 32px 64px}header{display:flex;align-items:flex-end;justify-content:space-between;gap:20px;padding:0 0 20px}header h1{font-size:36px;font-weight:750;letter-spacing:-1.7px}header .muted{max-width:670px;font-size:13px}.brand small{font-size:10px;font-weight:750;letter-spacing:1.6px;color:#66796d}.header-status{display:flex;gap:6px;align-items:center;white-space:nowrap;font-size:12px;color:var(--muted)}.status-dot{height:8px;width:8px;border-radius:50%;background:#4f8d64}.status-dot.running{background:#c18b35}.status-dot.error{background:#a14838}nav{gap:6px;padding:12px 0;top:0}nav button{border-radius:7px;padding:9px 14px;font-size:13px}nav span{margin-left:3px;font-variant-numeric:tabular-nums}.filters{padding:15px 0;gap:10px;background:white;border:1px solid var(--line);border-radius:12px;margin:16px 0;padding:14px}.filters .field:first-child{flex:1;min-width:200px}.filters input[type=search]{width:100%;min-width:0}.field{color:#56685d}.filters .field select,.filters input{min-height:40px;font-size:13px}.filters .check{font-size:12px}.filters button{font-size:12px;min-height:40px}.stats{gap:0;background:white;border:1px solid var(--line);border-radius:12px;overflow:hidden}.stat{border:0;border-radius:0;padding:12px 18px;min-width:110px}.stat+.stat{border-left:1px solid var(--line)}.stat small{font-size:11px;font-weight:600}.stat strong{font-size:23px;font-variant-numeric:tabular-nums}.toolbar{margin:24px 0 12px}.toolbar h2{font-size:20px;font-weight:730}.toolbar small{display:block;margin-top:2px}.layout-buttons{display:flex;border:1px solid var(--line);border-radius:8px;overflow:hidden;background:white}.layout-buttons button{border:0;border-radius:0;font-size:12px;padding:8px 12px}.layout-buttons button+button{border-left:1px solid var(--line)}.property{grid-template-columns:154px minmax(0,1fr);border-radius:10px;box-shadow:0 1px 2px #172d1d08}.property.fresh{border-left:3px solid #2a7452}.property.reviewed{border-left:3px solid transparent}.property.noimage{grid-template-columns:1fr}.content{padding:14px 16px;gap:9px}.top{align-items:center}.price{font-size:24px;line-height:1.2;letter-spacing:-.5px}.address{font-size:15px;margin-top:3px}.tag{border-radius:5px;font-size:11px;font-weight:600}.tag.new{background:#dfeee4;color:#235d3f}.tag.warning{background:#f6eddf;color:#785620}.reason{font-size:12px;padding:8px 10px;line-height:1.45;border-left:2px solid #d9b77c}.actions{align-items:center;gap:6px}.actions a,.actions button{padding:7px 10px;font-size:12px;border-color:#d5ded5}.actions a:first-child{background:var(--green);border-color:var(--green)}.actions .quiet{background:#f3f6f2;color:#55695c}.numbers{background:#f4f7f3;border-radius:7px;padding:8px 10px;font-size:12px;font-variant-numeric:tabular-nums}.cards{grid-template-columns:repeat(auto-fill,minmax(295px,1fr));gap:14px}.cards .property{height:100%}.cards .content{flex:1;display:flex;flex-direction:column}.cards .actions{margin-top:auto}.cards .cover{min-height:155px;max-height:180px}.cards .noimage .cover{display:grid;min-height:54px;height:54px;background:#edf1ec}.cards .top{align-items:start;flex-wrap:wrap}.source{border-radius:10px}.sources-grid{display:grid;grid-template-columns:repeat(auto-fit,minmax(280px,1fr));gap:12px}.source{margin:0}.source-panel-head{display:flex;align-items:center;justify-content:space-between;margin:20px 0 12px}.empty{line-height:1.6}button:hover,a:hover{filter:brightness(.96)}button:focus-visible,a:focus-visible,input:focus-visible,select:focus-visible{outline:2px solid #2a7452;outline-offset:2px}.notice{background:#fff;border:1px solid var(--line);border-radius:10px;padding:12px 16px;margin:12px 0;font-size:13px;color:var(--muted)}.city-chips{display:flex;gap:6px;flex-wrap:wrap;margin:0 0 10px}.city-chips button{font-size:12px;font-weight:550;padding:6px 10px;border-radius:16px}.city-chips button[aria-pressed=true]{background:#e2ede4;border-color:#85a58d;color:#245d46}.city-chips span{color:#78887e;margin-left:4px;font-variant-numeric:tabular-nums}.meta{font-size:11px;color:var(--muted)}.toast{position:fixed;bottom:18px;right:18px;background:#263b31;color:white;box-shadow:0 5px 25px #0002;padding:12px 16px;border-radius:9px;z-index:10;font-size:13px;max-width:calc(100% - 36px)}@media(max-width:700px){main{padding:20px 12px 45px}header{align-items:start;flex-direction:column;gap:8px}header h1{font-size:30px}.filters{padding:10px}.filters .field:first-child{flex-basis:100%}.filters .field{flex:1;min-width:120px}.stats .stat{padding:10px 12px}.stats .stat:last-child{flex-basis:100%;border-left:0;border-top:1px solid var(--line)}.property{grid-template-columns:105px minmax(0,1fr)}.content{padding:12px}.property.noimage{grid-template-columns:1fr}nav{overflow-x:auto;flex-wrap:nowrap;white-space:nowrap}nav button{padding:8px 10px}.cards{grid-template-columns:1fr}.top{align-items:flex-start}.city-chips{gap:5px}}
</style></head><body><main><header><div class="brand"><small>SACRAMENTO REGION / REAL ESTATE</small><h1>Property Scout</h1><p class="muted">Find homes below $260,000. No known HOA or mobile homes, conventional financing and 21 days to close.</p></div><div class="header-status"><span id="statusDot" class="status-dot"></span><span id="headerStatus">Connecting</span></div></header>
<nav><button data-tab="all">All <span id="allCount"></span></button><button data-tab="matches">Matches <span id="matchCount"></span></button><button data-tab="review">Needs review <span id="reviewCount"></span></button><button data-tab="unviewed">Unviewed <span id="unviewedCount"></span></button><button data-tab="saved">Saved <span id="savedCount"></span></button><button data-tab="archived">Archived <span id="archiveCount"></span></button><button data-tab="sources">Sources</button></nav>
<div id="filters" class="filters"><label class="field">Search<input id="search" type="search" placeholder="Address, city, reason"></label><label class="field">City<select id="city"><option value="">All cities</option>{% for c in cities %}<option>{{c}}</option>{% endfor %}<option value="other">Other cities</option></select></label><label class="field">Viewed<select id="viewFilter"><option value="">All</option><option value="new">Unviewed</option><option value="seen">Viewed</option></select></label><label class="field">Sort<select id="sort"><option value="new">Unviewed first</option><option value="low">Lowest price</option><option value="high">Highest price</option><option value="city">City</option></select></label><label class="field">Down payment<select id="down"><option value="10">10%</option><option value="12">12%</option></select></label><label class="check"><input type="checkbox" id="verified"> Conventional mentioned</label><label class="check"><input type="checkbox" id="closingVerified"> 21 days indicated</label><button id="clearFilters" type="button">Reset filters</button></div><div id="cityChips" class="city-chips"></div>
<div class="stats"><div class="stat"><small>Showing</small><strong id="count">0</strong></div><div class="stat"><small>Unviewed</small><strong id="newCount">0</strong></div><div class="stat"><small>Last scan</small><strong id="scanTime" style="font-size:15px">Waiting</strong><small id="scanState"></small></div></div>
<section id="listingPanel"><div id="reviewNotice" class="notice" hidden></div><div class="toolbar"><div><h2 id="panelTitle">All properties</h2><small id="panelNote"></small></div><div class="layout-buttons"><button id="listView">List</button><button id="cardView">Cards</button></div></div><div id="grid"></div></section>
<section id="sourcePanel" hidden><div class="source-panel-head"><h2>Source activity</h2><button id="refreshNow">Refresh display</button></div><div id="publicSources" class="sources-grid"></div><details><summary>Scanner diagnostics</summary><p id="diagnostics"></p></details></section><footer>Review leads include previously rejected and historical results; eligibility and availability are unverified. Saved and viewed states stay in this browser.</footer></main><div id="toast" class="toast" role="status" hidden></div>
<script>
const el=id=>document.getElementById(id),money=n=>Number(n).toLocaleString('en-US',{style:'currency',currency:'USD',maximumFractionDigits:0}),cities={{cities|tojson}};
let data={listings:[],rejected:[]},tab='all',loaded=false,lastPayload='',toastTimer;const tabs=['all','matches','review','unviewed','saved','archived','sources'];
function load(k,f){try{return JSON.parse(localStorage.getItem(k))??f}catch(e){return f}}
function store(k,v){try{localStorage.setItem(k,JSON.stringify(v))}catch(e){}}
const own=(o,k)=>Object.prototype.hasOwnProperty.call(o,k);
let saved=load('propertyScoutSavedV1',{})||{},viewed=load('propertyScoutViewedV1',{})||{},archived=load('propertyScoutArchivedV1',{})||{},layout=load('propertyScoutLayout','list')==='cards'?'cards':'list';
function addr(a){return typeof a==='object'&&a?([a.full||a.streetAddress||a.street,a.city,a.state,a.zipcode||a.zip].filter(Boolean).join(', ')||'Address unavailable'):(a||'Address unavailable')}
function cityOf(x){return String(x.city||((x.address&&typeof x.address==='object')?x.address.city:'')||addr(x.address).match(/,\s*([^,]+),\s*(?:CA|California)(?:\s+\d{5}(?:-\d{4})?)?\s*$/i)?.[1]||'').trim()}
function key(x){let a=addr(x.address).replace(/,\s*[^,]+,\s*(?:CA|California)(?:\s+\d{5}(?:-\d{4})?)?\s*$/i,'').toLowerCase();if(a==='address unavailable')return String(x.url||x.source||'')+'|'+String(x.price||'');const types={street:'st',avenue:'ave',drive:'dr',road:'rd',court:'ct',circle:'cir',lane:'ln',boulevard:'blvd',place:'pl',way:'way',terrace:'ter',parkway:'pkwy'};a=a.replace(/\b(street|avenue|drive|road|court|circle|lane|boulevard|place|way|terrace|parkway)\b/g,m=>types[m]).replace(/(?:\b(?:unit|apt|apartment|suite)\s*|#\s*)([a-z0-9-]+)/g,' unit $1');return a.replace(/[^a-z0-9]/g,'')+'|'+cityOf(x).toLowerCase().replace(/[^a-z0-9]/g,'')}
saved=Object.fromEntries(Object.values(saved).filter(x=>x&&x.address).map(x=>[key(x),x]));store('propertyScoutSavedV1',saved);
function add(p,t,v,c){const x=document.createElement(t);if(v!==undefined)x.textContent=v;if(c)x.className=c;p.append(x);return x}
function link(p,u,t,fn){if(!u)return;try{const parsed=new URL(u);if(!['http:','https:'].includes(parsed.protocol))return;const a=add(p,'a',t);a.href=parsed.href;a.target='_blank';a.rel='noopener noreferrer';if(fn){a.addEventListener('click',fn);a.addEventListener('auxclick',e=>{if(e.button===1)fn()})}return a}catch(e){}}
function button(p,t,fn,pressed){const b=add(p,'button',t);b.type='button';if(pressed!==undefined)b.setAttribute('aria-pressed',String(pressed));b.onclick=fn;return b}
function tag(p,t,c=''){add(p,'span',t,'tag '+c)}
function seen(x){return own(viewed,key(x))}
function notify(msg){el('toast').textContent=msg;el('toast').hidden=false;clearTimeout(toastTimer);toastTimer=setTimeout(()=>el('toast').hidden=true,2600)}
function mark(x,v,defer=false){if(v)viewed[key(x)]=new Date().toISOString();else delete viewed[key(x)];store('propertyScoutViewedV1',viewed);if(defer)setTimeout(render,0);else render()}
function archive(x){const k=key(x);if(own(archived,k)){delete archived[k];notify('Restored to active properties')}else{archived[k]=x;notify('Archived. Restore it from Archived anytime.')}store('propertyScoutArchivedV1',archived);render()}
function save(x){if(own(saved,key(x))){delete saved[key(x)];notify('Removed from saved')}else{saved[key(x)]=x;notify('Saved property')}store('propertyScoutSavedV1',saved);render()}
function hasPrice(x){return x.price!=null&&Number(x.price)>0&&Number.isFinite(Number(x.price))}
function distinct(rows){const m=new Map();for(const x of rows){const k=key(x);if(!m.has(k))m.set(k,x);else{const a=m.get(k);m.set(k,{...a,sources:[...new Set([...(a.sources||[a.source]),...(x.sources||[x.source])])],listing_links:[...new Set([...(a.listing_links||[a.url]),...(x.listing_links||[x.url])].filter(Boolean))]})}}return [...m.values()]}
function renderCard(grid,x){const k=key(x),v=seen(x),review=!!x.review,photos=Array.isArray(x.photos)?x.photos:[],city=cityOf(x),address=addr(x.address);const card=add(grid,'article',undefined,'property'+(!v?' fresh':' reviewed')+(!photos.length?' noimage':''));const cover=add(card,'div','Photo unavailable','cover');if(photos.length){const img=document.createElement('img');img.alt=address;img.loading='lazy';img.onload=()=>cover.replaceChildren(img);img.src=photos[0]}
const body=add(card,'div',undefined,'content'),top=add(body,'div',undefined,'top'),title=add(top,'div');add(title,'div',hasPrice(x)?money(x.price):'Price unknown','price');add(title,'div',address,'address');if(city&&!address.toLowerCase().includes(city.toLowerCase()))add(title,'small',city+', CA');const labels=add(top,'div',undefined,'tags');tag(labels,v?'Viewed':'Unviewed',v?'':'new');tag(labels,review?'Needs review':'Potential match',review?'warning':'');if(own(archived,k))tag(labels,'Archived');if(own(saved,k))tag(labels,'Saved');
if(review||x.review_note)add(body,'div',x.reason||x.review_note||'Review eligibility','reason');const tags=add(body,'div',undefined,'tags');if(x.type)tag(tags,String(x.type).replace(/_/g,' '));if(x.distress)tag(tags,x.distress);if(!review){tag(tags,x.hoa_status||'HOA unknown',x.hoa_verified?'':'warning');tag(tags,x.financing||'Financing unverified','warning');tag(tags,x.closing_status||'21 days unverified','warning')}if(x.saved_snapshot)tag(tags,'Saved snapshot','warning');
if(hasPrice(x)){const d=Number(el('down').value),n=add(body,'div',undefined,'numbers');add(n,'span',d+'% down: '+money(x.price*d/100));add(n,'span','Loan: '+money(x.price*(1-d/100)))}
add(body,'small','Sources: '+(x.sources||[x.source||'Unknown']).filter(Boolean).join(', '));if(v&&viewed[k])add(body,'small','Viewed '+new Date(viewed[k]).toLocaleDateString('en-US'),'meta');if(x.remarks){const d=add(body,'details');d.dataset.key=k;d.open=openDetails.has(k);d.ontoggle=()=>{if(d.open)openDetails.add(k);else openDetails.delete(k)};add(d,'summary','Property details');add(d,'p',x.remarks)}
const actions=add(body,'div',undefined,'actions');const urls=[...new Set([x.url,...(x.listing_links||[])].filter(Boolean))];if(urls.length){urls.forEach((url,i)=>link(actions,url,i===0?'Open listing':'Other source '+(i+1),()=>mark(x,true,true)))}else link(actions,x.search_url||'https://www.google.com/search?q='+encodeURIComponent(address+' '+city+' real estate listing'),'Find listing',()=>mark(x,true,true));button(actions,own(saved,k)?'Unsave':'Save',()=>save(x),own(saved,k));button(actions,v?'Mark unviewed':'Mark viewed',()=>mark(x,!v),v);button(actions,own(archived,k)?'Restore':'Archive',()=>archive(x),own(archived,k)).className='quiet';link(actions,x.photo_search||'https://www.google.com/search?tbm=isch&q='+encodeURIComponent(address+' '+city),'Photos');link(actions,'https://www.google.com/maps/search/?api=1&query='+encodeURIComponent(address+' '+city),'Map')}
const openDetails=new Set();function render(){const matches=distinct((data.listings||[]).map(x=>({...x,review:false}))),mk=new Set(matches.map(key)),review=distinct((data.rejected||[]).map(x=>({...x,review:true}))).filter(x=>!mk.has(key(x))),all=distinct([...matches,...review]),live=new Map(all.map(x=>[key(x),x]));const active=all.filter(x=>!own(archived,key(x))),archiveRows=Object.entries(archived).map(([k,x])=>live.get(k)||{...x,saved_snapshot:true}),savedRows=Object.entries(saved).map(([k,x])=>live.get(k)||{...x,saved_snapshot:true});
el('allCount').textContent=active.length;el('matchCount').textContent=matches.filter(x=>!own(archived,key(x))).length;el('reviewCount').textContent=review.filter(x=>!own(archived,key(x))).length;el('savedCount').textContent=savedRows.length;el('archiveCount').textContent=archiveRows.length;el('unviewedCount').textContent=active.filter(x=>!seen(x)).length;document.querySelectorAll('nav button').forEach(b=>b.setAttribute('aria-current',String(b.dataset.tab===tab)));el('sourcePanel').hidden=tab!=='sources';el('listingPanel').hidden=tab==='sources';el('filters').hidden=tab==='sources';el('cityChips').hidden=tab==='sources';el('statusDot').className='status-dot'+(data.running?' running':!loaded?' error':'');el('headerStatus').textContent=data.running?'Scan running':loaded?'Connected':'Connecting';el('scanTime').textContent=data.updated?new Date(data.updated).toLocaleString('en-US',{timeZone:'America/Los_Angeles',month:'short',day:'numeric',hour:'numeric',minute:'2-digit'})+' PT':'Waiting';el('scanState').textContent=data.running?'Scanning now':'Automatic scans';
const pool=tab==='matches'?active.filter(x=>!x.review):tab==='review'?active.filter(x=>x.review):tab==='saved'?savedRows:tab==='archived'?archiveRows:tab==='unviewed'?active.filter(x=>!seen(x)):active,q=el('search').value.trim().toLowerCase(),c=el('city').value,filter=el('viewFilter').value;
const chips=el('cityChips');chips.replaceChildren();for(const city of ['',...cities,'other']){const n=pool.filter(x=>!city||(city==='other'?!cities.some(v=>v.toLowerCase()===cityOf(x).toLowerCase()):cityOf(x).toLowerCase()===city.toLowerCase())).length;const b=button(chips,city==='other'?'Other cities':city||'All cities',()=>{el('city').value=city;render()},c===city);add(b,'span',String(n))}const rows=pool.filter(x=>{const city=cityOf(x);return (!c||(c==='other'?!cities.some(v=>v.toLowerCase()===city.toLowerCase()):city.toLowerCase()===c.toLowerCase()))&&(!q||[addr(x.address),city,x.reason,x.source,x.type,x.distress,...(x.sources||[])].join(' ').toLowerCase().includes(q))&&(!filter||(filter==='seen'?seen(x):!seen(x)))&&(!el('verified').checked||String(x.financing).startsWith('Conventional'))&&(!el('closingVerified').checked||x.closing_status==='21-day closing appears possible')});
const sort=el('sort').value;rows.sort((a,b)=>{const ap=hasPrice(a)?Number(a.price):Infinity,bp=hasPrice(b)?Number(b.price):Infinity;if(sort==='high')return (hasPrice(b)?bp:-1)-(hasPrice(a)?ap:-1);if(sort==='city')return cityOf(a).localeCompare(cityOf(b))||ap-bp;if(sort==='new')return Number(seen(a))-Number(seen(b))||Number(a.review)-Number(b.review)||ap-bp;return ap-bp});el('count').textContent=rows.length;el('newCount').textContent=rows.filter(x=>!seen(x)).length;el('panelTitle').textContent={all:'All properties',matches:'Potential matches',review:'Needs review',unviewed:'Unviewed properties',saved:'Saved properties',archived:'Archived properties',sources:'Sources'}[tab];el('panelNote').textContent=tab==='review'?'Filtered by your criteria, still available for manual review.':tab==='all'?'Matches and review leads, combined by property.':tab==='archived'?'Hidden from active views. Restore any property.':'';const notice=el('reviewNotice');notice.hidden=!(loaded&&matches.length===0&&review.length>0&&['all','matches','review'].includes(tab));notice.textContent='No potential matches from the latest cached results. '+review.length+' unique properties are available for manual review; source coverage and availability may be incomplete.';
const grid=el('grid');grid.className=layout==='cards'?'cards':'';grid.replaceChildren();el('listView').setAttribute('aria-pressed',String(layout==='list'));el('cardView').setAttribute('aria-pressed',String(layout==='cards'));if(!rows.length){const empty=add(grid,'div',undefined,'empty');add(empty,'strong',!loaded?'Loading properties…':data.running?'Scanning sources…':'No properties in this view');if(loaded){add(empty,'p','Try resetting filters or opening Needs review.');button(empty,'Reset filters',resetFilters);if(tab==='matches')button(empty,'See review leads',()=>setTab('review'))}}rows.forEach(x=>renderCard(grid,x));
const pub=el('publicSources');pub.replaceChildren();for(const [name,rec] of Object.entries(data.public_sources||{})){const p=add(pub,'div',undefined,'source');add(p,'strong',name);add(p,'p',rec.status||'Unknown');link(p,rec.url,'Source');for(const doc of rec.documents||[])link(p,doc.url,doc.title);for(const item of rec.records||[]){add(p,'p',item.address+' | '+item.status);link(p,item.url,'Find property')}}el('diagnostics').textContent=(data.errors||[]).join('\n')||'No messages'}
function resetFilters(){el('city').value='';el('search').value='';el('viewFilter').value='';el('verified').checked=false;el('closingVerified').checked=false;render()}function setTab(t){if(!tabs.includes(t))return;tab=t;el('viewFilter').value='';el('verified').checked=false;el('closingVerified').checked=false;render();window.scrollTo({top:0,behavior:'instant'})}document.querySelectorAll('nav button').forEach(b=>b.onclick=()=>setTab(b.dataset.tab));el('clearFilters').onclick=resetFilters;el('refreshNow').onclick=()=>refresh(true);for(const id of ['city','sort','down','viewFilter','verified','closingVerified'])el(id).onchange=render;el('search').oninput=render;el('listView').onclick=()=>{layout='list';store('propertyScoutLayout',layout);render()};el('cardView').onclick=()=>{layout='cards';store('propertyScoutLayout',layout);render()};async function refresh(force=false){try{const r=await fetch('/api/listings',{cache:'no-store'});if(!r.ok)throw Error();const payload=await r.text();if(!loaded||payload!==lastPayload||force){data=JSON.parse(payload);lastPayload=payload;loaded=true;render()}if(force)notify('Display refreshed')}catch(e){el('scanState').textContent='Connection lost; showing last available data';el('statusDot').className='status-dot error';el('headerStatus').textContent='Offline'}}render();refresh();setInterval(()=>{if(!document.hidden)refresh()},30000);document.addEventListener('visibilitychange',()=>{if(!document.hidden)refresh()});window.addEventListener('storage',e=>{if(['propertyScoutSavedV1','propertyScoutViewedV1','propertyScoutArchivedV1'].includes(e.key)){saved=load('propertyScoutSavedV1',{})||{};viewed=load('propertyScoutViewedV1',{})||{};archived=load('propertyScoutArchivedV1',{})||{};render()}});
</script></body></html>''',cities=CITIES)
if __name__=='__main__':
    threading.Thread(target=loop,daemon=True).start();app.run(host='0.0.0.0',port=int(os.getenv('PORT','8000')),debug=False,use_reloader=False)
