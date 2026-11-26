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
    return dict(**property_attributes(raw),closing_status=close,hoa_verified=not bool(restriction),hoa_status=restriction or 'No HOA reported',address=address,city=city,price=price,source=source,distress=match.group(),financing=financing,remarks=remarks[:1800],photos=[safeurl(p) for p in photos if safeurl(p)],url=link,search_url='https://www.google.com/search?q='+quote_plus(address+' '+city+' CA real estate listing'),photo_search='https://www.google.com/search?tbm=isch&q='+quote_plus(address+' '+city+' CA'))
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
        db.execute('CREATE TABLE IF NOT EXISTS rent_calls (ts REAL)')
        db.execute('DELETE FROM rent_calls WHERE ts < ?',(now-31*86400,))
        rent_count=db.execute('SELECT COUNT(*) FROM rent_calls').fetchone()[0]
        last=db.execute('SELECT MAX(ts) FROM calls').fetchone()[0] or 0
        # One bounded recovery request when the original result was never recorded.
        recovery=count<9
        if count+rent_count>=50 or (now-last<31*86400/35 and not recovery):
            state['rentcast_diagnostics']={k:v for k,v in old.items() if k!='rows'}
            state['rentcast_diagnostics'].update({'used':count,'limit':50,'next_eligible':datetime.fromtimestamp(max(last+31*86400/35,(db.execute('SELECT MIN(ts) FROM calls').fetchone()[0] or 0)+31*86400 if count>=50 else 0),timezone.utc).isoformat()})
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
                rejected.append({**property_attributes(x),'source':'RentCast','address':x.get('formattedAddress') or x.get('addressLine1'),'city':x.get('city'),'price':listing_price(x),'type':x.get('propertyType'),'status':x.get('status'),'reason':reason})
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
            rows.append(dict(**property_attributes(x),type=x.get('propertyType'),address=address,city=str(x['city']).title(),price=price,source='RentCast',distress=label,hoa_verified=not bool(restriction),hoa_status=restriction or 'No HOA reported',closing_status='21-day closing unverified',financing='Financing unverified',remarks=remarks,photos=[],url='',search_url='https://www.google.com/search?q='+quote_plus(address+' real estate listing'),photo_search='https://www.google.com/search?tbm=isch&q='+quote_plus(address)))
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

def property_attributes(raw):
    p=raw.get('property') if isinstance(raw.get('property'),dict) else {}
    result={}
    for name,aliases in {'bedrooms':('bedrooms','beds','bedroomCount'),'bathrooms':('bathrooms','baths','bathroomCount'),'squareFootage':('squareFootage','sqft','livingArea','livingAreaSqFt','buildingArea'),'yearBuilt':('yearBuilt',)}.items():
        for obj in (raw,p):
            for alias in aliases:
                try:
                    val=float(str(obj.get(alias,'')).replace(',',''))
                    if val>0 and val<100000:
                        result[name]=val
                        break
                except (ValueError,TypeError):pass
            if name in result:break
    return result

def rent_address(row):
    a=row.get('address') or ''
    city=str(row.get('city') or '').strip()
    if isinstance(a,dict):
        city=city or str(a.get('city') or '')
        a=a.get('full') or a.get('streetAddress') or a.get('street') or ''
    a=str(a).strip()
    if not re.match(r'^\d+\s+',a):return ''
    if re.search(r',\s*[^,]+,\s*(CA|California)(?:\s+\d{5}(?:-\d{4})?)?\s*$',a,re.I):return a
    return a+', '+city+', CA' if city else ''

def rent_estimates_scan():
    key=os.getenv('RENTCAST_API_KEY')
    path=Path(os.getenv('QUOTA_DB','/data/quota.sqlite3')).with_name('rentcast.sqlite3')
    path.parent.mkdir(parents=True,exist_ok=True)
    cache=path.with_name('rental_estimates.json')
    try: records=json.loads(cache.read_text())
    except Exception:records={}
    state['rental_estimates']=records
    if not key:return
    now=time.time()
    def rank(x):
        city=property_key(x).split('|')[-1]
        return (city not in {re.sub(r'[^a-z0-9]','',c.lower()) for c in CITIES},'Historical' in str(x.get('reason','')),not bool(x.get('url')),x.get('price') or 1e9)
    candidates=merge_properties(state.get('listings',[]))+merge_properties(state.get('rejected',[]))
    candidates=sorted(candidates,key=lambda x:(x.get('reason') is not None,rank(x)))
    row=next((x for x in candidates if rent_address(x) and now-records.get(property_key(x),{}).get('attempted_epoch',0)> (30 if records.get(property_key(x),{}).get('rent') else 7)*86400),None)
    with sqlite3.connect(path,timeout=15) as db:
        db.execute('CREATE TABLE IF NOT EXISTS calls (ts REAL)')
        db.execute('CREATE TABLE IF NOT EXISTS rent_calls (ts REAL)')
        db.execute('BEGIN IMMEDIATE')
        for table in ('calls','rent_calls'):db.execute('DELETE FROM '+table+' WHERE ts < ?',(now-31*86400,))
        sales=db.execute('SELECT COUNT(*) FROM calls').fetchone()[0]
        rentals=db.execute('SELECT COUNT(*) FROM rent_calls').fetchone()[0]
        daily=db.execute('SELECT COUNT(*) FROM rent_calls WHERE ts >= ?',(now-86400,)).fetchone()[0]
        state['rental_quota']={'sales':sales,'rental':rentals,'total':sales+rentals,'limit':50,'rental_limit':15}
        if row is None or sales+rentals>=50 or rentals>=15 or daily>=2:return
        db.execute('INSERT INTO rent_calls VALUES (?)',(now,))
        state['rental_quota'].update({'rental':rentals+1,'total':sales+rentals+1})
    ident=property_key(row); address=rent_address(row)
    params={'address':address}
    for name in ('bedrooms','bathrooms','squareFootage'):
        if row.get(name) is not None:params[name]=row[name]
    t=re.sub(r'[^a-z]','',str(row.get('type') or '').lower())
    types={'singlefamily':'Single Family','singlefamilyhome':'Single Family','singlefamilyresidence':'Single Family','condominiumunit':'Condo','condominium':'Condo','condo':'Condo','townhouse':'Townhouse','manufacturedhome':'Manufactured','mobilehome':'Manufactured'}
    if t in types:params['propertyType']=types[t]
    try:
        response=requests.get('https://api.rentcast.io/v1/avm/rent/long-term',params=params,headers={'X-Api-Key':key,'Accept':'application/json'},timeout=(10,40),allow_redirects=False)
        response.raise_for_status();payload=response.json()
        rent=payload.get('rent')
        if not isinstance(rent,(int,float)) or rent<=0:raise ValueError('No rental estimate returned')
        subject=payload.get('subjectProperty') or {}
        # Do not assign another unit's valuation to this address.
        actual=subject.get('formattedAddress') or subject.get('addressLine1') or ''
        if not actual or property_key({'address':actual,'city':subject.get('city')})!=ident:raise ValueError('Subject address did not match')
        comps=[]
        for c in (payload.get('comparables') or [])[:12]:
            if isinstance(c,dict):
                comps.append({k:c.get(k) for k in ('formattedAddress','propertyType','bedrooms','bathrooms','squareFootage','yearBuilt','price','status','distance','daysOld','listedDate','lastSeenDate','correlation')})
        rec={'rent':rent,'low':payload.get('rentRangeLow'),'high':payload.get('rentRangeHigh'),'subject':{k:subject.get(k) for k in ('formattedAddress','propertyType','bedrooms','bathrooms','squareFootage','yearBuilt')},'comparables':comps,'checked':datetime.now(timezone.utc).isoformat(),'attempted_epoch':now,'source':'RentCast','status':'success'}
        print('Rent valuation succeeded; '+str(len(comps))+' comparable records',flush=True)
    except Exception as e:
        rec={**records.get(ident,{}),'attempted_epoch':now,'status':'error','error':('HTTP '+str(e.response.status_code) if isinstance(e,requests.HTTPError) else str(e)[:120] if isinstance(e,ValueError) else type(e).__name__)}
        print('Rent valuation failed: '+rec['error'],flush=True)
    records[ident]=rec
    tmp=cache.with_suffix('.tmp');tmp.write_text(json.dumps(records));tmp.replace(cache);state['rental_estimates']=records

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
                            rejected.append({**property_attributes(item),'reason':reason,'address':item.get('address'),'city':item.get('city'),'price':listing_price(item,source),'price_fields':{k:v for k,v in item.items() if 'price' in k.lower() and isinstance(v,(str,int,float))},'source':source,'type':item.get('propertyType'),'status':item.get('status'),'url':safeurl(item.get('propertyLink') or item.get('url'))})
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
        try:rent_estimates_scan()
        except Exception as e:
            print('Rent estimate scanner: '+type(e).__name__,flush=True)
        print('Scan complete: '+str(len(state['listings']))+' candidates; '+str(len(state['rejected']))+' rejected',flush=True)
        diagnostics=provider_cache.with_name('scan_diagnostics.json');tmp=diagnostics.with_suffix('.tmp');tmp.write_text(json.dumps({k:state.get(k) for k in ('errors','updated','rentcast_diagnostics','foreclosure_diagnostics')}));tmp.replace(diagnostics)
    finally:state['running']=False;lock.release()
def loop():
    try:
        cache=Path(os.getenv('QUOTA_DB','/data/quota.sqlite3')).with_name('listings.json')
        if cache.exists():state['listings']=[x for x in json.loads(cache.read_text()) if (x.get('hoa_status') in ('HOA status unverified','No HOA reported') or x.get('hoa_verified') is True) and x.get('closing_status')!='Closing too short']
        diagnostics=cache.with_name('scan_diagnostics.json')
        if diagnostics.exists():state.update(json.loads(diagnostics.read_text()))
        rent_cache=cache.with_name('rental_estimates.json')
        if rent_cache.exists():state['rental_estimates']=json.loads(rent_cache.read_text())
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
    estimates=snapshot.pop('rental_estimates',{})
    for row in snapshot['listings']+snapshot['rejected']:
        row['rent_estimate']=estimates.get(property_key(row))
    return jsonify(snapshot)
@app.get('/')
def home():return render_template_string(r'''<!doctype html><html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>Property Scout</title><style>
:root{color-scheme:light;--bg:#f5f5f7;--surface:#fff;--ink:#1d1d1f;--muted:#68686d;--line:#e6e6ea;--accent:#0066cc;--green:#28724d;--shadow:0 3px 14px #00000008}
*{box-sizing:border-box}body{margin:0;background:var(--bg);color:var(--ink);font:15px/1.45 -apple-system,BlinkMacSystemFont,"Segoe UI",sans-serif;-webkit-font-smoothing:antialiased}main{max-width:1440px;margin:auto;padding:0 38px 55px}button,input,select,textarea{font:inherit;color:inherit}button{cursor:pointer;border:0;background:none}button:disabled{opacity:.35;cursor:default}button:focus-visible,a:focus-visible,input:focus-visible,select:focus-visible,summary:focus-visible,textarea:focus-visible{outline:2px solid var(--accent);outline-offset:3px}a{color:var(--accent);text-decoration:none}a:hover{text-decoration:underline}small,.muted,.meta{color:var(--muted)}small{font-size:12px}p{margin:6px 0}h1,h2,h3{letter-spacing:-.035em;line-height:1.18;margin:0}h1{font-size:22px;font-weight:720}h2{font-size:32px;font-weight:730}h3{font-size:19px;font-weight:690}[hidden]{display:none!important}
header{height:77px;display:flex;justify-content:space-between;align-items:center;gap:16px;border-bottom:1px solid var(--line)}.brand{display:flex;align-items:center;gap:10px}.brand-mark{width:34px;height:34px;border-radius:10px;background:#20252c;color:white;display:grid;place-items:center}.brand-mark svg{width:20px;height:20px}.header-status{display:flex;align-items:center;gap:7px;font-size:12px;color:var(--muted)}.status-dot{width:7px;height:7px;border-radius:50%;background:#389961}.status-dot.running{background:#ca8e28}.status-dot.error{background:#b74c42}
nav{position:sticky;top:0;z-index:4;background:#f5f5f7ed;backdrop-filter:blur(18px);display:flex;gap:5px;align-items:center;overflow-x:auto;padding:12px 0;margin-bottom:18px;scrollbar-width:none}nav button{white-space:nowrap;font-weight:600;font-size:13px;border-radius:20px;padding:8px 13px;color:#535359;display:flex;gap:7px;align-items:center}nav button:hover{background:#e9e9ed}nav button[aria-current=true]{background:#1d1d1f;color:#fff}nav button span{font-size:11px;opacity:.72}nav button[data-tab=sources]{margin-left:auto}
.hero{display:flex;justify-content:space-between;align-items:flex-end;gap:16px;margin:0 0 22px}.hero h2{font-size:42px;font-weight:740;letter-spacing:-.055em}.hero p{font-size:15px;color:var(--muted);max-width:650px;margin:6px 0 0}.hero-summary{display:flex;gap:22px;white-space:nowrap}.hero-summary div{display:grid;gap:0}.hero-summary strong{font-size:26px;font-weight:730;font-variant-numeric:tabular-nums;letter-spacing:-.04em}.hero-summary small{font-size:11px}
.filters{display:flex;gap:10px;align-items:center;flex-wrap:wrap;margin:0 0 12px}.search-wrap{display:flex;align-items:center;gap:9px;background:white;border:1px solid var(--line);border-radius:12px;padding:0 13px;flex:1;min-width:220px;box-shadow:var(--shadow)}.search-wrap svg{width:17px;height:17px;color:#83838a;flex-shrink:0}.search-wrap input{width:100%;height:46px;border:0;background:transparent;outline:none!important;font-size:15px}.search-wrap:focus-within{outline:2px solid var(--accent);outline-offset:1px}.field{display:grid;gap:5px;font-size:12px;color:var(--muted);font-weight:550}.filters>.field{display:flex;align-items:center;gap:7px;background:white;border:1px solid var(--line);border-radius:12px;padding:0 11px;min-height:46px}.field select,.field input{border:0;background:transparent;max-width:180px;padding:7px 0;font-size:13px;color:var(--ink);font-weight:550}.filter-button,.layout-buttons button,.secondary-button{border:1px solid var(--line);border-radius:12px;background:white;padding:12px 15px;min-height:46px;font-size:13px;font-weight:600}.filter-button[aria-expanded=true]{border-color:#9bc3e8;background:#eaf3fc;color:#0066cc}.advanced{background:white;border:1px solid var(--line);border-radius:14px;padding:16px;display:grid;grid-template-columns:repeat(auto-fit,minmax(150px,1fr));gap:14px;margin-bottom:14px}.advanced .field select,.advanced .field input{border:1px solid var(--line);border-radius:8px;padding:10px;max-width:none;width:100%}.check{display:flex;align-items:center;gap:7px;font-size:12px;color:#56565b}.check input{accent-color:var(--accent)}.advanced button{color:var(--accent);font-weight:600;align-self:end;padding:10px}.city-chips{display:flex;gap:7px;overflow-x:auto;scrollbar-width:none;margin:0 0 18px}.city-chips button{flex-shrink:0;border-radius:18px;border:1px solid #e0e0e4;background:transparent;padding:7px 12px;font-size:12px;font-weight:550;color:#626268}.city-chips button[aria-pressed=true]{background:#e6f0fa;color:#005bb9;border-color:#c5ddf5}.city-chips span{font-size:10px;margin-left:5px;opacity:.7}
.toolbar{display:flex;justify-content:space-between;align-items:center;gap:10px;margin:18px 0 15px}.toolbar h2{font-size:18px;letter-spacing:-.02em}.toolbar small{display:block;margin-top:3px}.layout-buttons{display:flex;background:#e8e8ec;border-radius:9px;padding:3px;gap:2px;flex-shrink:0}.layout-buttons button{background:transparent;border:0;border-radius:7px;min-height:0;padding:6px 12px;color:#65656a;font-size:12px}.layout-buttons button[aria-pressed=true]{background:white;color:#1d1d1f;box-shadow:0 1px 4px #00000012}.notice{padding:12px 15px;background:#fff;border:1px solid var(--line);border-radius:12px;font-size:13px;color:var(--muted);margin:12px 0}
#grid{display:grid;gap:14px}.cards{grid-template-columns:repeat(auto-fill,minmax(285px,1fr))}.property{border-radius:18px;background:white;border:1px solid #e9e9ed;overflow:hidden;box-shadow:var(--shadow);min-width:0;display:flex;flex-direction:column;transition:box-shadow .2s,transform .2s}.property:hover{box-shadow:0 8px 24px #0000000b;transform:translateY(-1px)}.cover{height:184px;background:#e9eaed;position:relative;overflow:hidden;display:grid;place-items:center;cursor:pointer}.cover img{width:100%;height:100%;object-fit:cover;position:absolute;inset:0}.cover .placeholder{display:grid;justify-items:center;gap:7px;color:#83838c;font-size:11px}.cover .placeholder svg{width:32px;height:32px;stroke:#9696a1}.cover.no-photo{height:110px;background:linear-gradient(145deg,#f1f1f4,#e8e9ed)}.cover-overlay{position:absolute;inset:12px 12px auto;display:flex;align-items:center;justify-content:space-between;gap:10px;z-index:1;pointer-events:none}.cover-overlay>*{pointer-events:auto}.cover-overlay .tag{background:#ffffffed;backdrop-filter:blur(12px);box-shadow:0 1px 4px #0000000c}.heart{display:grid;place-items:center;width:36px;height:36px;border-radius:50%;background:#ffffffed;box-shadow:0 1px 5px #00000013;color:#55555b}.heart svg{width:19px;height:19px}.heart[aria-pressed=true]{color:#c43d58}.heart[aria-pressed=true] svg{fill:currentColor}.content{padding:16px;display:flex;flex-direction:column;gap:10px;flex:1}.price{font-size:28px;letter-spacing:-.045em;font-weight:740;line-height:1.16;font-variant-numeric:tabular-nums}.property-link{display:block;text-align:left;line-height:1.4;font-weight:650;font-size:14px;padding:0;color:var(--ink);overflow-wrap:anywhere}.property-link:hover{color:var(--accent)}.location{font-size:12px;color:var(--muted);margin-top:2px}.tags{display:flex;flex-wrap:wrap;align-items:center;gap:6px}.tag{display:inline-flex;align-items:center;gap:4px;padding:4px 8px;border-radius:6px;background:#f0f0f3;color:#606068;font-size:11px;line-height:1.4;font-weight:600}.tag.fits,.tag.new{background:#e5f2e9;color:#2c6846}.tag.unknown{background:#edf0f5;color:#586477}.tag.outside,.tag.warning{background:#faf1e1;color:#85611f}.tag.seen{background:#f0f0f3;color:#74747b}.reason{font-size:12px;color:#77716a;line-height:1.4;overflow-wrap:anywhere}.card-metrics{display:grid;grid-template-columns:1fr 1fr;gap:12px;border-top:1px solid #efeff1;border-bottom:1px solid #efeff1;padding:11px 0}.card-metrics div{min-width:0}.card-metrics small{display:block;font-size:10px;color:var(--muted)}.card-metrics strong{display:block;font-weight:680;font-size:16px;letter-spacing:-.02em;margin-top:2px;font-variant-numeric:tabular-nums}.card-bottom{display:flex;align-items:center;justify-content:space-between;gap:10px;margin-top:auto;padding-top:2px}.card-bottom small{font-size:11px}.open-button{border-radius:9px;background:#e8f1fb;color:#0066cc;padding:8px 13px;font-size:12px;font-weight:650;white-space:nowrap}.open-button:hover{background:#dceafd}.subtle{font-size:12px;color:var(--muted)}.actions{display:flex;gap:7px;flex-wrap:wrap;align-items:center}.actions button,.actions a,.drawer-actions button,.drawer-source a{font-size:13px;font-weight:600;border:1px solid var(--line);background:white;border-radius:9px;padding:9px 12px;text-decoration:none}.actions button[aria-pressed=true],.drawer-actions button[aria-pressed=true]{color:#0066cc;background:#eaf3fc;border-color:#d6e8fa}.empty{background:white;border:1px solid var(--line);border-radius:18px;padding:48px 20px;text-align:center;grid-column:1/-1}.empty strong{font-size:20px;letter-spacing:-.03em}.empty p{color:var(--muted)}.empty button{color:var(--accent);padding:10px;font-weight:600}
.table-shell{background:white;border:1px solid var(--line);border-radius:16px;overflow:auto}.inventory{width:100%;border-collapse:collapse;min-width:850px;text-align:left;font-size:13px}.inventory th{font-size:11px;font-weight:650;color:var(--muted);background:#fafafa;padding:13px 14px;border-bottom:1px solid var(--line);white-space:nowrap}.inventory td{padding:14px;border-bottom:1px solid #eeeef0;vertical-align:middle}.inventory tr:last-child td{border-bottom:0}.inventory tbody tr:hover{background:#fafafa}.inventory tr.is-new td:first-child{border-left:3px solid #308552;padding-left:11px}.inventory tr.is-seen td:first-child{border-left:3px solid transparent;padding-left:11px}.cell-secondary{font-size:11px;color:var(--muted);margin-top:3px;max-width:230px;overflow-wrap:anywhere}.cell-price{font-size:16px;font-weight:700;white-space:nowrap;letter-spacing:-.025em}.payment-mini{font-size:11px;font-weight:600;color:var(--green);margin-top:3px}.cell-actions{display:flex;gap:5px}.cell-actions button{padding:6px 9px;background:#f0f0f3;border-radius:7px;font-size:11px;font-weight:600;white-space:nowrap}.cell-actions .open{color:var(--accent);background:#e9f2fb}.cell-actions button[aria-pressed=true]{color:var(--accent)}.pager{display:flex;align-items:center;justify-content:space-between;font-size:12px;color:var(--muted);margin-top:16px}.pager button{padding:8px 13px;background:white;border:1px solid var(--line);border-radius:8px;margin-left:5px}
dialog{position:fixed;inset:0 0 0 auto;margin:0;width:min(670px,100vw);max-width:100vw;height:100dvh;max-height:100dvh;border:0;padding:0;background:white;color:var(--ink);box-shadow:-16px 0 60px #00000020;overscroll-behavior:contain}dialog::backdrop{background:#00000050;backdrop-filter:blur(3px)}#detailBody{padding:25px 28px 45px}.drawer-head{display:flex;justify-content:space-between;align-items:flex-start;gap:15px}.drawer-head h2{font-size:25px;margin:4px 0;line-height:1.22}.drawer-head button{background:#f0f0f3;border-radius:20px;font-size:12px;font-weight:600;padding:8px 12px}.drawer-price{font-size:40px;font-weight:740;letter-spacing:-.055em;margin:12px 0}.drawer-img{display:block;width:100%;max-height:250px;object-fit:cover;border-radius:14px;margin:15px 0}.drawer-actions{display:flex;gap:6px;flex-wrap:wrap;margin:16px 0}.drawer-nav{position:sticky;top:0;display:flex;gap:4px;background:#f5f5f7f5;backdrop-filter:blur(12px);border-radius:11px;padding:4px;z-index:2;margin:16px 0}.drawer-nav button{flex:1;border-radius:8px;font-size:13px;font-weight:600;padding:9px 4px;color:#66666c}.drawer-nav button[aria-pressed=true]{background:white;color:var(--ink);box-shadow:0 1px 4px #0000000e}.drawer-section{border-top:1px solid var(--line);padding-top:18px;margin-top:18px}.drawer-section h3{font-size:18px;margin-bottom:12px}.drawer-section .reason{padding:10px 12px;border-radius:9px;background:#f8f4ec;margin-bottom:10px}.criteria-row{display:grid;grid-template-columns:122px 1fr;gap:10px;padding:10px 0;border-bottom:1px solid #f0f0f2;font-size:13px}.criteria-row strong{font-size:12px;color:var(--muted);font-weight:600}.drawer-source{display:flex;gap:7px;flex-wrap:wrap}.drawer-source a:first-child{background:var(--accent);color:white;border-color:var(--accent)}.drawer-note{width:100%;min-height:140px;resize:vertical;border:1px solid var(--line);border-radius:12px;background:#fafafa;padding:13px}.detail-raw{white-space:pre-wrap;overflow-wrap:anywhere;font-size:13px}.mortgage-heading{display:flex;align-items:center;justify-content:space-between;gap:10px}.mortgage-heading button{font-size:12px;color:var(--accent);font-weight:600}.mortgage-total,.rental-hero{background:#f5f7fa;border-radius:16px;padding:19px;margin:12px 0}.mortgage-total strong,.rental-hero strong{display:block;font-size:36px;font-weight:740;letter-spacing:-.05em;line-height:1.25;color:#1d1d1f;font-variant-numeric:tabular-nums}.mortgage-bar{height:8px;display:flex;overflow:hidden;border-radius:8px;background:#e4e4e8;margin-top:12px}.mortgage-line{display:flex;justify-content:space-between;font-size:13px;padding:6px 0}.mortgage-line i{display:inline-block;width:9px;height:9px;border-radius:3px;margin-right:8px}.mortgage-fields{display:grid;grid-template-columns:1fr 1fr;gap:12px;margin:16px 0}.mortgage-fields label{display:grid;gap:5px;font-size:12px;font-weight:600;color:var(--muted)}.mortgage-fields input,.mortgage-fields select{width:100%;min-width:0;border:1px solid var(--line);background:white;border-radius:9px;padding:10px;color:var(--ink);font-variant-numeric:tabular-nums}.mortgage-fields input[type=range]{border:0;padding:0;accent-color:var(--accent)}.mortgage-fields .wide{grid-column:1/-1}.mortgage-summary{display:grid;grid-template-columns:1fr 1fr;gap:8px;margin:12px 0}.mortgage-summary div{background:#f5f5f7;border-radius:12px;padding:13px}.mortgage-summary strong{display:block;font-size:21px;font-weight:700;letter-spacing:-.03em}.mortgage-summary .cash{background:#e8f1fb}.mortgage-note{font-size:11px;line-height:1.6;color:var(--muted)}.rental-hero{display:flex;align-items:baseline;justify-content:space-between;gap:10px;flex-wrap:wrap}.rent-comps{overflow:auto;margin-top:10px}.rent-comps table{border-collapse:collapse;width:100%;font-size:12px;text-align:left}.rent-comps th,.rent-comps td{padding:9px 6px;border-bottom:1px solid var(--line);vertical-align:top}.rent-comps th{font-size:10px;color:var(--muted)}.rent-comps td:not(:first-child){white-space:nowrap}.positive-flow{color:var(--green)}.negative-flow{color:#a64646}summary{cursor:pointer;font-weight:600;font-size:13px}
.source-panel-head{display:flex;align-items:center;justify-content:space-between;margin:10px 0 16px}.source-panel-head h2{font-size:24px}.source-panel-head button{font-size:13px;color:var(--accent)}.sources-grid{display:grid;grid-template-columns:repeat(auto-fit,minmax(260px,1fr));gap:12px}.source{background:white;border-radius:15px;border:1px solid var(--line);padding:17px;font-size:13px}.source a{display:inline-block;margin:5px 8px 0 0}.source p{color:var(--muted)}#diagnostics{white-space:pre-wrap;font-size:12px;color:var(--muted)}#sourcePanel details{margin-top:20px}.toast{position:fixed;bottom:20px;right:20px;max-width:calc(100% - 40px);z-index:10;padding:13px 17px;background:#202124;color:white;border-radius:12px;font-size:13px;box-shadow:0 5px 22px #00000020}footer{font-size:11px;color:#77777e;margin-top:28px}
@media(max-width:800px){main{padding:0 18px 40px}header{height:65px}nav{margin-bottom:10px}nav button[data-tab=sources]{margin-left:0}.hero{align-items:flex-start;flex-direction:column;gap:12px;margin-bottom:18px}.hero h2{font-size:34px}.hero-summary{gap:24px}.hero-summary strong{font-size:23px}.filters>.field{flex:1}.search-wrap{flex-basis:100%}.cards{grid-template-columns:repeat(auto-fill,minmax(240px,1fr))}.toolbar{margin-top:14px}#detailBody{padding:20px 18px 40px}}
@media(max-width:520px){main{padding:0 13px 32px}.cards{grid-template-columns:1fr}.cover{height:200px}.cover.no-photo{height:104px}.hero h2{font-size:32px}.header-status{font-size:11px}.advanced{grid-template-columns:1fr 1fr}.drawer-price{font-size:34px}.mortgage-fields{gap:9px}.drawer-nav button{font-size:12px}.card-metrics strong{font-size:17px}}
@media(prefers-reduced-motion:reduce){*{scroll-behavior:auto!important;transition:none!important}}
</style></head><body><main><header><div class="brand"><span class="brand-mark"><svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="m3 10 9-7 9 7v10h-6v-6H9v6H3z"/></svg></span><h1>Property Scout</h1></div><div class="header-status"><span id="statusDot" class="status-dot"></span><span id="headerStatus">Connecting</span></div></header>
<nav><button data-tab="all">Explore <span id="allCount"></span></button><button data-tab="matches">Matches <span id="matchCount"></span></button><button data-tab="review">Other homes <span id="reviewCount"></span></button><button data-tab="unviewed">New to you <span id="unviewedCount"></span></button><button data-tab="saved">Saved <span id="savedCount"></span></button><button data-tab="archived">Archived <span id="archiveCount"></span></button><button data-tab="sources">Sources</button></nav>
<section class="hero" id="hero"><div><h2 id="heroTitle">Find your next property.</h2><p id="heroSubtitle">Discover and compare homes across the Sacramento region.</p></div><div class="hero-summary"><div><small>Properties shown</small><strong id="count">0</strong></div><div><small>Not yet viewed</small><strong id="newCount">0</strong></div></div></section>
<div id="filters" class="filters"><label class="search-wrap"><svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" aria-hidden="true"><circle cx="10.8" cy="10.8" r="6.8"/><path d="m16 16 5 5"/></svg><input id="search" type="search" aria-label="Search properties" placeholder="Search address or city"></label><label class="field">City<select id="city"><option value="">All cities</option>{% for c in cities %}<option>{{c}}</option>{% endfor %}<option value="other">Other cities</option></select></label><label class="field">Sort<select id="sort"><option value="new">Unviewed first</option><option value="low">Lowest price</option><option value="high">Highest price</option><option value="city">City</option><option value="rent">Highest rent</option><option value="cash">Lowest cash to close</option></select></label><button id="filterToggle" class="filter-button" aria-expanded="false" aria-controls="advanced">Filters</button></div>
<div id="advanced" class="advanced" hidden><label class="field">Viewed<select id="viewFilter"><option value="">All</option><option value="new">Unviewed</option><option value="seen">Viewed</option></select></label><label class="field">Eligibility<select id="eligibility"><option value="">Any status</option><option value="fits">Meets filters</option><option value="outside">Outside criteria</option><option value="unknown">Missing information</option></select></label><label class="field">Down payment (%)<input id="down" type="number" min="0" max="100" step="any" value="12" inputmode="decimal"></label><label class="check"><input type="checkbox" id="verified"> Conventional mentioned</label><label class="check"><input type="checkbox" id="closingVerified"> 21 days indicated</label><button id="clearFilters" type="button">Clear filters</button></div><div id="cityChips" class="city-chips"></div>
<section id="listingPanel"><div id="reviewNotice" class="notice" hidden></div><div class="toolbar"><div><h2 id="panelTitle">All properties</h2><small id="panelNote"></small></div><div class="layout-buttons"><button id="cardView">Cards</button><button id="listView">Table</button></div></div><div id="grid"></div><div class="pager" id="pager" hidden></div></section>
<section id="sourcePanel" hidden><div class="source-panel-head"><h2>Source activity</h2><button id="refreshNow">Refresh display</button></div><div id="publicSources" class="sources-grid"></div><details><summary>Scanner diagnostics</summary><p id="diagnostics"></p></details></section><footer><span id="scanTime">Waiting</span> · <span id="scanState">Connecting</span><br>Listings reflect the latest available provider records, not confirmed sale availability. Your saved, viewed, archived and note history stays in this browser.</footer></main><div id="toast" class="toast" role="status" hidden></div><dialog id="propertyDialog" aria-labelledby="detailTitle"><div id="detailBody"></div></dialog>
<script>
const el=id=>document.getElementById(id),money=n=>Number(n).toLocaleString('en-US',{style:'currency',currency:'USD',maximumFractionDigits:0}),cities={{cities|tojson}};
let data={listings:[],rejected:[]},tab='all',loaded=false,lastPayload='',toastTimer,page=1,selected=null;const pageSize=25;const tabs=['all','matches','review','unviewed','saved','archived','sources'];
function load(k,f){try{return JSON.parse(localStorage.getItem(k))??f}catch(e){return f}}
function store(k,v){try{localStorage.setItem(k,JSON.stringify(v))}catch(e){}}
const own=(o,k)=>Object.prototype.hasOwnProperty.call(o,k);
let saved=load('propertyScoutSavedV1',{})||{},viewed=load('propertyScoutViewedV1',{})||{},archived=load('propertyScoutArchivedV1',{})||{},notes=load('propertyScoutNotesV1',{})||{},layout=load('propertyScoutLayoutV2','cards')==='list'?'list':'cards';
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
const mortgageDefaults={down:12,rate:6.5,years:30,tax:1.25,insurance:150,pmi:0.6,closing:3};
function bound(v,min,max,fallback){return v===''||v==null||!Number.isFinite(Number(v))?fallback:Math.max(min,Math.min(max,Number(v)))}
function cleanMortgage(v){v=v||{};return {down:bound(v.down,0,100,12),rate:bound(v.rate,0,25,6.5),years:[10,15,20,25,30,40].includes(Number(v.years))?Number(v.years):30,tax:bound(v.tax,0,10,1.25),insurance:bound(v.insurance,0,10000,150),pmi:bound(v.pmi,0,5,.6),closing:bound(v.closing,0,20,3)}}
let mortgage=cleanMortgage(load('propertyScoutMortgageV1',mortgageDefaults)),offers=load('propertyScoutOffersV1',{})||{};
el('down').value=mortgage.down;
function scenario(x){const custom=offers[key(x)]||{};return {...mortgage,price:bound(custom.price,1,100000000,Number(x.price)),hoa:bound(custom.hoa,0,100000,0)}}
function calculateMortgage(a){const price=Number(a.price),down=price*a.down/100,loan=Math.max(0,price-down),r=a.rate/1200,n=a.years*12;const principalInterest=loan===0?0:r===0?loan/n:loan*r/(-Math.expm1(-n*Math.log1p(r)));const tax=price*a.tax/1200,insurance=a.insurance,pmi=loan>0&&a.down<20?loan*a.pmi/1200:0,hoa=a.hoa,closing=price*a.closing/100;return {price,down,loan,principalInterest,tax,insurance,pmi,hoa,closing,total:principalInterest+tax+insurance+pmi+hoa,cash:down+closing,totalInterest:Math.max(0,principalInterest*n-loan)}}
function persistMortgage(){store('propertyScoutMortgageV1',mortgage);el('down').value=Number(mortgage.down.toFixed(4))}
function mortgagePanel(parent,x){
 const f=add(parent,'section',undefined,'drawer-section'),k=key(x),head=add(f,'div',undefined,'mortgage-heading');add(head,'h3','Mortgage calculator');button(head,'Reset estimates',()=>{mortgage={...mortgageDefaults};delete offers[k];persistMortgage();store('propertyScoutOffersV1',offers);drawDetails();render()});
 add(f,'p','Adjust the offer price and HOA for this property. Financing assumptions apply to all properties.','mortgage-note');
 const total=add(f,'div',undefined,'mortgage-total');add(total,'small','Estimated monthly payment');const totalNumber=add(total,'strong');const bar=add(total,'div',undefined,'mortgage-bar');bar.setAttribute('aria-hidden','true');
 const breakdown=add(f,'div'),components=[['Principal & interest','principalInterest','#255d46'],['Property taxes','tax','#769a7f'],['Homeowners insurance','insurance','#b1c7af'],['Mortgage insurance (PMI)','pmi','#b19a73'],['HOA dues','hoa','#8893a7']],segments={},amounts={};
 for(const [label,prop,color] of components){const piece=add(bar,'span');piece.style.background=color;segments[prop]=piece;const row=add(breakdown,'div',undefined,'mortgage-line'),name=add(row,'span');const sw=add(name,'i');sw.style.background=color;name.append(document.createTextNode(label));amounts[prop]=add(row,'strong')}
 const fields=add(f,'div',undefined,'mortgage-fields'),inputs={},a=scenario(x);let range,dollars;
 function field(label,prop,min,max,step,local=false){const l=add(fields,'label',label),i=add(l,'input');i.type='number';i.min=String(min);i.max=String(max);i.step=String(step);i.inputMode='decimal';i.value=String(a[prop]);inputs[prop]=i;i.oninput=()=>{if(i.value===''||!Number.isFinite(Number(i.value))||Number(i.value)<min||Number(i.value)>max)return;const value=Number(i.value);if(local){offers[k]={...(offers[k]||{}),[prop]:value};store('propertyScoutOffersV1',offers)}else{mortgage={...mortgage,[prop]:value};persistMortgage()}if(prop==='down'){range.value=String(value);dollars.value=String(Math.round(scenario(x).price*value/100))}if(prop==='price')dollars.value=String(Math.round(value*mortgage.down/100));update()};i.onchange=()=>{i.value=String(scenario(x)[prop]);update();render()};return i}
 field('Purchase / offer price ($)','price',1,100000000,'any',true);field('Down payment (%)','down',0,100,'any');
 const rl=add(fields,'label','Down payment slider','wide');range=add(rl,'input');range.type='range';range.min='0';range.max='100';range.step='.1';range.value=String(a.down);
 const dl=add(fields,'label','Down payment ($)');dollars=add(dl,'input');dollars.type='number';dollars.min='0';dollars.step='1';dollars.value=String(Math.round(a.price*a.down/100));
 function setDown(v){mortgage={...mortgage,down:bound(v,0,100,mortgage.down)};persistMortgage();inputs.down.value=String(Number(mortgage.down.toFixed(4)));range.value=String(mortgage.down);update()}
 range.oninput=()=>{setDown(Number(range.value));dollars.value=String(Math.round(scenario(x).price*mortgage.down/100))};range.onchange=()=>render();
 dollars.oninput=()=>{if(dollars.value!=='')setDown(Number(dollars.value)/scenario(x).price*100)};dollars.onchange=()=>{dollars.value=String(Math.round(scenario(x).price*mortgage.down/100));render()};
 field('Interest rate (%)','rate',0,25,'any');
 const tl=add(fields,'label','Loan term'),term=add(tl,'select');for(const n of [10,15,20,25,30,40]){const o=add(term,'option',n+' years');o.value=String(n)}term.value=String(a.years);term.onchange=()=>{mortgage={...mortgage,years:Number(term.value)};persistMortgage();update();render()};
 field('Annual property tax (%)','tax',0,10,'any');field('Home insurance ($/month)','insurance',0,10000,'any');field('Annual PMI (% of loan)','pmi',0,5,'any');field('HOA ($/month, if any)','hoa',0,100000,'any',true);field('Closing costs (% of price)','closing',0,20,'any');
 const summary=add(f,'div',undefined,'mortgage-summary'),out={};for(const [label,prop] of [['Down payment','down'],['Loan amount','loan'],['Estimated closing costs','closing'],['Estimated cash to close','cash'],['Total loan interest','totalInterest']]){const item=add(summary,'div',undefined,prop==='cash'?'cash':'');add(item,'small',label);out[prop]=add(item,'strong')}
 const closingNote=add(f,'p',undefined,'mortgage-note');add(f,'p','Illustrative defaults: 6.5% rate, 30-year term, 1.25% annual property tax, $150/month insurance, 0.6% annual PMI and 3% closing costs. These are estimates, not live lender quotes or verified property expenses. HOA defaults to $0 until entered. PMI is estimated below 20% down on conventional loans; actual costs vary.','mortgage-note');
 function update(){const c=calculateMortgage(scenario(x));parent.querySelectorAll('.drawer-section').forEach(section=>section.dispatchEvent(new Event('mortgage-updated')));totalNumber.textContent=money(c.total)+' /mo';for(const [,prop] of components){amounts[prop].textContent=money(c[prop]);segments[prop].style.width=(c.total?100*c[prop]/c.total:0)+'%'}for(const prop of Object.keys(out))out[prop].textContent=money(c[prop]);dollars.max=String(c.price);closingNote.textContent='Cash to close = '+money(c.down)+' down + '+money(c.closing)+' estimated closing costs. Closing costs may include lender fees, appraisal, escrow, title, recording and prepaid taxes/insurance; excludes seller credits and deposits already paid.'}
 update()
}
function distinct(rows){const m=new Map();for(const x of rows){const k=key(x);if(!m.has(k))m.set(k,x);else{const a=m.get(k);m.set(k,{...a,sources:[...new Set([...(a.sources||[a.source]),...(x.sources||[x.source])])],listing_links:[...new Set([...(a.listing_links||[a.url]),...(x.listing_links||[x.url])].filter(Boolean))]})}}return [...m.values()]}
function eligibility(x){
    if(x.saved_snapshot)return {kind:'unknown',label:'Not in latest results',reason:x.reason||'Availability is not confirmed.'};
    if(!x.review&&!x.review_note)return {kind:'fits',label:'Meets filters',reason:'HOA, financing and availability may still require confirmation.'};
    const reason=String(x.reason||x.review_note||'Eligibility information unavailable');
    const outside=/outside|excluded|manufactured|mobile|condo|townhouse|land\b|hoa present|hoa fee present|hoa indicated|cash only|financing restriction|closing deadline|closing too short|unavailable|auction status|not active|not single family/i.test(reason);
    return {kind:outside?'outside':'unknown',label:outside?'Outside criteria':'Missing information',reason};
}
function sourceLabel(x){const labels={fanniemae:'HomePath',freddiemac:'HomeSteps',hud:'HUD',redfin:'Redfin',RentCast:'RentCast'};return [...new Set((x.sources||[x.source||'Unknown']).filter(Boolean).map(v=>labels[v]||v))].join(', ')}
function rentPanel(parent,x){
 const f=add(parent,'section',undefined,'drawer-section');add(f,'h3','Rental income estimate');const est=x.rent_estimate||{},valid=Number(est.rent)>0,hero=add(f,'div',undefined,'rental-hero');const main=add(hero,'div');add(main,'small','RentCast market rent');add(main,'strong',valid?money(est.rent)+'/mo':'Not available');if(valid&&est.low!=null&&est.high!=null)add(hero,'small',money(est.low)+'–'+money(est.high)+'/mo');
 if(valid){const sub=est.subject||{},facts=[sub.propertyType,sub.bedrooms!=null?sub.bedrooms+' beds':'',sub.bathrooms!=null?sub.bathrooms+' baths':'',sub.squareFootage?Number(sub.squareFootage).toLocaleString()+' sqft':'',sub.yearBuilt?'Built '+sub.yearBuilt:''].filter(Boolean);add(f,'p',facts.join(' · '),'muted');add(f,'small','Valuation retrieved '+new Date(est.checked).toLocaleDateString()+'. Comparable asking rents may differ from signed leases. Property condition, rental restrictions and repairs require verification.');if(est.status==='error')add(f,'p','Last refresh failed; showing the prior estimate.','mortgage-note')}
 else add(f,'p',est.error?'Provider could not verify this address: '+est.error:'Address-level rental valuation is queued automatically within the shared API allowance. No rent estimate is invented.','mortgage-note');
 const comps=est.comparables||[];if(comps.length){const d=add(f,'details');add(d,'summary','Nearby comparable rentals ('+comps.length+')');const wrap=add(d,'div',undefined,'rent-comps'),t=add(wrap,'table'),head=add(add(t,'thead'),'tr');for(const h of ['Address','Rent','Beds / baths','Size','Distance','Status'])add(head,'th',h);const body=add(t,'tbody');for(const c of comps){const tr=add(body,'tr'),ad=add(tr,'td');link(ad,'https://www.google.com/search?q='+encodeURIComponent((c.formattedAddress||'')+' rental listing'),c.formattedAddress||'Unknown');if(c.daysOld!=null)add(ad,'small',c.daysOld+' days old');add(tr,'td',c.price!=null?money(c.price):'Unknown');add(tr,'td',(c.bedrooms??'?')+' / '+(c.bathrooms??'?'));add(tr,'td',c.squareFootage?Number(c.squareFootage).toLocaleString():'Unknown');add(tr,'td',c.distance!=null?Number(c.distance).toFixed(2)+' mi':'Unknown');add(tr,'td',c.status||'Unknown')}}
 const k=key(x);let assumptions=load('propertyScoutRentalV1',{})||{};const local=assumptions[k]||{},fields=add(f,'div',undefined,'mortgage-fields');function input(label,prop,value,max){const l=add(fields,'label',label),i=add(l,'input');i.type='number';i.min='0';i.max=String(max);i.step='any';i.value=value==null?'':String(value);i.oninput=()=>{if(i.value===''){delete local[prop]}else if(i.validity.valid)local[prop]=Number(i.value);else return;assumptions[k]=local;store('propertyScoutRentalV1',assumptions);update()};return i}
 const rent=input('Monthly rent override ($)','rent',local.rent??(valid?est.rent:null),100000),vac=input('Vacancy reserve (%)','vacancy',local.vacancy??5,100),maint=input('Maintenance reserve (%)','maintenance',local.maintenance??8,100),mgmt=input('Management fee (%)','management',local.management??8,100);
 const grid=add(f,'div',undefined,'mortgage-summary'),out={};for(const [label,k] of [['Gross rental yield','yield'],['Monthly operating reserves','reserves'],['Estimated monthly cash flow','flow'],['Annual cash-on-cash return','coc']]){const item=add(grid,'div');add(item,'small',label);out[k]=add(item,'strong')}
 function update(){const amount=rent.value===''?null:Number(rent.value);if(amount==null||!hasPrice(x)){Object.values(out).forEach(n=>n.textContent='Not available');return}const c=calculateMortgage(scenario(x)),reserve=amount*(Number(vac.value||0)+Number(maint.value||0)+Number(mgmt.value||0))/100,flow=amount-reserve-c.total;out.yield.textContent=(amount*12/c.price*100).toFixed(1)+'%';out.reserves.textContent=money(reserve);out.flow.textContent=money(flow)+'/mo';out.flow.className=flow>=0?'positive-flow':'negative-flow';out.coc.textContent=c.cash>0?(flow*12/c.cash*100).toFixed(1)+'%':'Not available'}
 f.addEventListener('mortgage-updated',update);update();add(f,'p','Cash flow subtracts estimated mortgage payment, taxes, insurance, PMI, HOA, vacancy, maintenance and management. Excludes major capital repairs, utilities paid by owner, income taxes and financing changes; adjust assumptions before relying on it.','mortgage-note');
}
let detailTab='overview';function showDetails(x){selected=x;detailTab='overview';mark(x,true,true);drawDetails();const d=el('propertyDialog');if(!d.open)d.showModal()}
function drawDetails(){if(!selected)return;const x=selected,k=key(x),fit=eligibility(x),city=cityOf(x),a=addr(x.address),p=el('detailBody');p.replaceChildren();const head=add(p,'div',undefined,'drawer-head'),left=add(head,'div');add(left,'small',sourceLabel(x));const h=add(left,'h2',a);h.id='detailTitle';add(left,'small',city||'City unverified');button(head,'Close',()=>el('propertyDialog').close());add(p,'div',hasPrice(x)?money(x.price):'Price unavailable','drawer-price');const tags=add(p,'div',undefined,'tags');tag(tags,fit.label,fit.kind);tag(tags,seen(x)?'Viewed':'Unviewed',seen(x)?'seen':'new');if(own(saved,k))tag(tags,'Saved');if(own(archived,k))tag(tags,'Archived');if(x.saved_snapshot)tag(tags,'Historical snapshot','unknown');
    if(x.photos?.length){const img=add(p,'img',undefined,'drawer-img');img.alt=a;img.onerror=()=>img.remove();img.src=x.photos[0]}
    const actions=add(p,'div',undefined,'drawer-actions');button(actions,own(saved,k)?'Unsave property':'Save property',()=>{save(x);drawDetails()},own(saved,k));button(actions,seen(x)?'Mark unviewed':'Mark viewed',()=>{mark(x,!seen(x));drawDetails()});button(actions,own(archived,k)?'Restore property':'Archive property',()=>{archive(x);drawDetails()});
    const nav=add(p,'div',undefined,'drawer-nav');const sections={};const overview=add(p,'div');sections.overview=overview;const sec=add(overview,'section',undefined,'drawer-section');add(sec,'h3','Property overview');if(x.review||x.review_note)add(sec,'div',fit.reason,'reason');
    const cityOK=cities.some(c=>c.toLowerCase()===city.toLowerCase()),type=String(x.type||x.distress||'').replace(/_/g,' '),reason=fit.reason.toLowerCase();
    const criteria=[['Location',city?city+(cityOK?' · Target city':' · Outside target cities'):'Unknown'],['Asking price',hasPrice(x)?money(x.price)+(x.price<260000?' · Within budget':' · At or above budget'):'Unknown'],['Property type',x.type?type:!x.review?'Single family per listing filter':'Unverified'],['HOA',x.hoa_status||(reason.includes('hoa')?fit.reason:'Unverified')],['Financing',x.financing||(reason.includes('cash only')||reason.includes('financing restriction')?fit.reason:'Unverified')],['Closing',x.closing_status||(reason.includes('closing')?fit.reason:'Unverified')]];
    for(const [label,value] of criteria){const row=add(sec,'div',undefined,'criteria-row');add(row,'strong',label);add(row,'span',value)}
    const finance=add(p,'div');sections.finance=finance;if(hasPrice(x))mortgagePanel(finance,x);else add(finance,'p','A purchase price is needed to calculate financing.','muted');const rental=add(p,'div');sections.rental=rental;rentPanel(rental,x);finance.addEventListener('input',()=>rental.querySelectorAll('.drawer-section').forEach(z=>z.dispatchEvent(new Event('mortgage-updated'))));finance.addEventListener('change',()=>rental.querySelectorAll('.drawer-section').forEach(z=>z.dispatchEvent(new Event('mortgage-updated'))));
    const sources=add(overview,'section',undefined,'drawer-section');add(sources,'h3','Explore this property');const links=add(sources,'div',undefined,'drawer-source');const urls=[...new Set([x.url,...(x.listing_links||[])].filter(Boolean))];urls.forEach((u,i)=>link(links,u,i?'Source '+(i+1):'Open listing'));link(links,x.search_url||'https://www.google.com/search?q='+encodeURIComponent(a+' '+city+' CA real estate listing'),'Search web');link(links,'https://www.google.com/maps/search/?api=1&query='+encodeURIComponent(a+' '+city+' CA'),'Map');link(links,x.photo_search||'https://www.google.com/search?tbm=isch&q='+encodeURIComponent(a+' '+city),'Photos');if(x.remarks)add(sources,'p',x.remarks,'detail-raw');
    const research=add(p,'section',undefined,'drawer-section');sections.notes=research;add(research,'h3','Private research notes');const t=add(research,'textarea',undefined,'drawer-note');t.value=notes[k]||'';t.placeholder='Questions for the agent, offer strategy, follow-up…';t.setAttribute('aria-label','Private research notes');t.oninput=()=>{notes[k]=t.value;store('propertyScoutNotesV1',notes)};add(research,'small','Automatically saved in this browser.');function activate(t){detailTab=t;for(const [name,section] of Object.entries(sections))section.hidden=name!==t;nav.querySelectorAll('button').forEach(b=>b.setAttribute('aria-pressed',String(b.dataset.section===t)));if(t==='rental')rental.querySelectorAll('.drawer-section').forEach(z=>z.dispatchEvent(new Event('mortgage-updated')))}for(const [k,label] of [['overview','Overview'],['finance','Mortgage'],['rental','Rental'],['notes','Notes']]){const b=button(nav,label,()=>activate(k),false);b.dataset.section=k}activate(detailTab)
}
function renderTable(grid,rows){const shell=add(grid,'div',undefined,'table-shell'),table=add(shell,'table',undefined,'inventory'),head=add(table,'thead'),tr=add(head,'tr');for(const h of ['Property','Asking price','Rent estimate','Eligibility','Activity','Actions'])add(tr,'th',h);const body=add(table,'tbody');for(const x of rows){const k=key(x),f=eligibility(x),row=add(body,'tr',undefined,seen(x)?'is-seen':'is-new'),a=add(row,'td'),b=button(a,addr(x.address),()=>showDetails(x));b.className='property-link';add(a,'div',[cityOf(x),sourceLabel(x)].filter(Boolean).join(' · '),'cell-secondary');const price=add(row,'td');add(price,'div',hasPrice(x)?money(x.price):'Unknown','cell-price');if(hasPrice(x)){const calc=calculateMortgage(scenario(x));add(price,'div',money(calc.total)+'/mo est.','payment-mini');add(price,'div',money(calc.cash)+' cash to close est.','cell-secondary')}const rental=add(row,'td');const re=x.rent_estimate;if(re?.rent){add(rental,'div',money(re.rent)+'/mo','cell-price');if(re.low!=null&&re.high!=null)add(rental,'div',money(re.low)+'–'+money(re.high),'cell-secondary')}else add(rental,'small',re?.error?'Unavailable':'Pending');const e=add(row,'td',undefined,'cell-fit');tag(e,f.label,f.kind);if(x.review||x.review_note||x.saved_snapshot)add(e,'div',f.reason,'cell-secondary');const activity=add(row,'td');tag(activity,seen(x)?'Viewed':'Unviewed',seen(x)?'seen':'new');if(notes[k])add(activity,'div','Has notes','cell-secondary');const actions=add(add(row,'td'),'div',undefined,'cell-actions');button(actions,'Details',()=>showDetails(x)).className='open';button(actions,own(saved,k)?'Saved':'Save',()=>save(x),own(saved,k));button(actions,own(archived,k)?'Restore':'Archive',()=>archive(x))}
}
function renderCard(grid,x){
 const k=key(x),v=seen(x),photos=Array.isArray(x.photos)?x.photos:[],city=cityOf(x),address=addr(x.address),fit=eligibility(x),card=add(grid,'article',undefined,'property');
 const cover=add(card,'div',undefined,'cover'+(photos.length?'':' no-photo'));cover.onclick=()=>showDetails(x);
 const placeholder=add(cover,'div',undefined,'placeholder');placeholder.innerHTML='<svg viewBox="0 0 24 24" fill="none" stroke-width="1.4" stroke-linejoin="round"><path d="m3 10 9-7 9 7v10h-6v-6H9v6H3z"/></svg>';add(placeholder,'span','No listing photo');
 if(photos.length){const img=add(cover,'img');img.alt=address;img.loading='lazy';img.onerror=()=>{img.remove();cover.classList.add('no-photo')};img.src=photos[0]}
 const overlay=add(cover,'div',undefined,'cover-overlay');tag(overlay,v?'Viewed':'New to you',v?'seen':'new');const heart=button(overlay,'',()=>{},own(saved,k));heart.className='heart';heart.setAttribute('aria-label',own(saved,k)?'Remove from saved':'Save property');heart.innerHTML='<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M20.8 4.6a5.5 5.5 0 0 0-7.8 0l-1 1-1-1a5.5 5.5 0 0 0-7.8 7.8l1 1L12 21l7.8-7.6 1-1a5.5 5.5 0 0 0 0-7.8z"/></svg>';heart.onclick=e=>{e.stopPropagation();save(x)};
 const body=add(card,'div',undefined,'content'),title=add(body,'div');add(title,'div',hasPrice(x)?money(x.price):'Price unavailable','price');button(title,address,()=>showDetails(x)).className='property-link';const subject=x.rent_estimate?.subject||{},facts=[x.bedrooms??subject.bedrooms,x.bathrooms??subject.bathrooms,x.squareFootage??subject.squareFootage],parts=[facts[0]!=null?facts[0]+' beds':'',facts[1]!=null?facts[1]+' baths':'',facts[2]?Number(facts[2]).toLocaleString()+' sqft':''].filter(Boolean);add(title,'div',parts.length?parts.join(' · '):(city||'Location unverified'),'location');
 const tags=add(body,'div',undefined,'tags');tag(tags,fit.label,fit.kind);if(own(archived,k))tag(tags,'Archived');if(x.saved_snapshot)tag(tags,'Older record','unknown');if(x.review||x.review_note)add(body,'p',fit.reason,'reason');
 if(hasPrice(x)){const c=calculateMortgage(scenario(x)),metrics=add(body,'div',undefined,'card-metrics');for(const [label,val] of [['Monthly payment',money(c.total)],['Cash to close',money(c.cash)],['Estimated rent',x.rent_estimate?.rent?money(x.rent_estimate.rent)+'/mo':'Not available'],['Down payment',Number(mortgage.down.toFixed(2))+'%']]){const b=add(metrics,'div');add(b,'small',label);add(b,'strong',val)}}
 const bottom=add(body,'div',undefined,'card-bottom');add(bottom,'small',sourceLabel(x));button(bottom,'View property',()=>showDetails(x)).className='open-button'
}
const openDetails=new Set();function render(){const matches=distinct((data.listings||[]).map(x=>({...x,review:false}))),mk=new Set(matches.map(key)),review=distinct((data.rejected||[]).map(x=>({...x,review:true}))).filter(x=>!mk.has(key(x))),all=distinct([...matches,...review]),live=new Map(all.map(x=>[key(x),x]));const active=all.filter(x=>!own(archived,key(x))),archiveRows=Object.entries(archived).map(([k,x])=>live.get(k)||{...x,saved_snapshot:true}),savedRows=Object.entries(saved).map(([k,x])=>live.get(k)||{...x,saved_snapshot:true});
el('allCount').textContent=active.length;el('matchCount').textContent=matches.filter(x=>!own(archived,key(x))).length;el('reviewCount').textContent=review.filter(x=>!own(archived,key(x))).length;el('savedCount').textContent=savedRows.length;el('archiveCount').textContent=archiveRows.length;el('unviewedCount').textContent=active.filter(x=>!seen(x)).length;document.querySelectorAll('nav button').forEach(b=>b.setAttribute('aria-current',String(b.dataset.tab===tab)));el('sourcePanel').hidden=tab!=='sources';el('listingPanel').hidden=tab==='sources';el('filters').hidden=tab==='sources';el('advanced').hidden=tab==='sources'||el('filterToggle').getAttribute('aria-expanded')!=='true';el('cityChips').hidden=tab==='sources';el('hero').hidden=tab==='sources';el('statusDot').className='status-dot'+(data.running?' running':!loaded?' error':'');el('headerStatus').textContent=data.running?'Scan running':loaded?'Connected':'Connecting';el('scanTime').textContent=data.updated?new Date(data.updated).toLocaleString('en-US',{timeZone:'America/Los_Angeles',month:'short',day:'numeric',hour:'numeric',minute:'2-digit'})+' PT':'Waiting';el('scanState').textContent=data.running?'Scanning now':'Automatic scans';
const pool=tab==='matches'?active.filter(x=>!x.review):tab==='review'?active.filter(x=>x.review):tab==='saved'?savedRows:tab==='archived'?archiveRows:tab==='unviewed'?active.filter(x=>!seen(x)):active,q=el('search').value.trim().toLowerCase(),c=el('city').value,filter=el('viewFilter').value;
const chips=el('cityChips');chips.replaceChildren();for(const city of ['',...cities,'other']){const n=pool.filter(x=>!city||(city==='other'?!cities.some(v=>v.toLowerCase()===cityOf(x).toLowerCase()):cityOf(x).toLowerCase()===city.toLowerCase())).length;const b=button(chips,city==='other'?'Other cities':city||'All cities',()=>{el('city').value=city;page=1;render()},c===city);add(b,'span',String(n))}const rows=pool.filter(x=>{const city=cityOf(x);return (!c||(c==='other'?!cities.some(v=>v.toLowerCase()===city.toLowerCase()):city.toLowerCase()===c.toLowerCase()))&&(!q||[addr(x.address),city,x.reason,x.source,x.type,x.distress,...(x.sources||[])].join(' ').toLowerCase().includes(q))&&(!filter||(filter==='seen'?seen(x):!seen(x)))&&(!el('eligibility').value||eligibility(x).kind===el('eligibility').value)&&(!el('verified').checked||String(x.financing).startsWith('Conventional'))&&(!el('closingVerified').checked||x.closing_status==='21-day closing appears possible')});
const sort=el('sort').value;rows.sort((a,b)=>{const ap=hasPrice(a)?Number(a.price):Infinity,bp=hasPrice(b)?Number(b.price):Infinity;if(sort==='high')return (hasPrice(b)?bp:-1)-(hasPrice(a)?ap:-1);if(sort==='city')return cityOf(a).localeCompare(cityOf(b))||ap-bp;if(sort==='rent')return (Number(b.rent_estimate?.rent)||0)-(Number(a.rent_estimate?.rent)||0);if(sort==='cash')return (hasPrice(a)?calculateMortgage(scenario(a)).cash:Infinity)-(hasPrice(b)?calculateMortgage(scenario(b)).cash:Infinity);if(sort==='new')return Number(seen(a))-Number(seen(b))||Number(a.review)-Number(b.review)||ap-bp;return ap-bp});el('count').textContent=rows.length;el('newCount').textContent=rows.filter(x=>!seen(x)).length;el('heroTitle').textContent={all:'Find your next property.',matches:'Your potential matches.',review:'Explore other homes.',unviewed:'New to you.',saved:'Your saved homes.',archived:'Your archive.',sources:'Sources'}[tab];el('heroSubtitle').textContent={all:'Browse every unique property found across the Sacramento region.',matches:'Homes that pass the automated search filters. Verify the remaining details.',review:'Properties outside your search criteria or with missing information.',unviewed:'Properties you haven’t opened yet.',saved:'Keep your favorite opportunities in one place.',archived:'Properties you chose to set aside.',sources:''}[tab];el('panelTitle').textContent=rows.length+' '+(rows.length===1?'property':'properties');el('panelNote').textContent='Estimates based on '+Number(mortgage.down.toFixed(2))+'% down · '+mortgage.years+' years · '+mortgage.rate+'% interest';const notice=el('reviewNotice');notice.hidden=!(loaded&&matches.length===0&&review.length>0&&['all','matches','review'].includes(tab));notice.textContent='No listings currently meet all automated filters. '+review.length+' other properties were found. Each property shows why it was excluded.';
const grid=el('grid');grid.className=layout==='cards'?'cards':'';grid.replaceChildren();el('listView').setAttribute('aria-pressed',String(layout==='list'));el('cardView').setAttribute('aria-pressed',String(layout==='cards'));if(!rows.length){const empty=add(grid,'div',undefined,'empty');add(empty,'strong',!loaded?'Loading properties…':data.running?'Scanning sources…':'No properties in this view');if(loaded){add(empty,'p','Try resetting filters or opening Other listings.');button(empty,'Reset filters',resetFilters);if(tab==='matches')button(empty,'See other listings',()=>setTab('review'))}}const maxPage=Math.max(1,Math.ceil(rows.length/pageSize));page=Math.min(page,maxPage);const visible=rows.slice((page-1)*pageSize,page*pageSize);if(visible.length){if(layout==='cards')visible.forEach(x=>renderCard(grid,x));else renderTable(grid,visible)}const pager=el('pager');pager.hidden=rows.length<=pageSize;pager.replaceChildren();add(pager,'span',rows.length?'Showing '+((page-1)*pageSize+1)+'–'+Math.min(page*pageSize,rows.length)+' of '+rows.length:'');const controls=add(pager,'div');const prev=button(controls,'Previous',()=>{page--;render()});prev.disabled=page<=1;const next=button(controls,'Next',()=>{page++;render()});next.disabled=page>=maxPage;
const pub=el('publicSources');pub.replaceChildren();for(const [name,rec] of Object.entries(data.public_sources||{})){const p=add(pub,'div',undefined,'source');add(p,'strong',name);add(p,'p',rec.status||'Unknown');link(p,rec.url,'Source');for(const doc of rec.documents||[])link(p,doc.url,doc.title);for(const item of rec.records||[]){add(p,'p',item.address+' | '+item.status);link(p,item.url,'Find property')}}el('diagnostics').textContent=(data.errors||[]).join('\n')||'No messages'}
function resetFilters(){page=1;el('eligibility').value='';el('city').value='';el('search').value='';el('viewFilter').value='';el('verified').checked=false;el('closingVerified').checked=false;render()}function setTab(t){if(!tabs.includes(t))return;tab=t;page=1;el('eligibility').value='';el('viewFilter').value='';el('verified').checked=false;el('closingVerified').checked=false;render();window.scrollTo({top:0,behavior:'instant'})}document.querySelectorAll('nav button').forEach(b=>b.onclick=()=>setTab(b.dataset.tab));el('clearFilters').onclick=resetFilters;el('filterToggle').onclick=()=>{const open=el('filterToggle').getAttribute('aria-expanded')!=='true';el('filterToggle').setAttribute('aria-expanded',String(open));el('advanced').hidden=!open};el('refreshNow').onclick=()=>refresh(true);for(const id of ['city','sort','viewFilter','eligibility','verified','closingVerified'])el(id).onchange=()=>{page=1;render()};el('down').oninput=()=>{if(el('down').value!==''&&el('down').validity.valid){mortgage={...mortgage,down:Number(el('down').value)};store('propertyScoutMortgageV1',mortgage);render()}};el('down').onchange=()=>{persistMortgage();render()};el('search').oninput=()=>{page=1;render()};el('propertyDialog').addEventListener('close',()=>{selected=null;render()});el('listView').onclick=()=>{layout='list';store('propertyScoutLayoutV2',layout);render()};el('cardView').onclick=()=>{layout='cards';store('propertyScoutLayoutV2',layout);render()};async function refresh(force=false){try{const r=await fetch('/api/listings',{cache:'no-store'});if(!r.ok)throw Error();const payload=await r.text();if(!loaded||payload!==lastPayload||force){data=JSON.parse(payload);lastPayload=payload;loaded=true;render()}if(force)notify('Display refreshed')}catch(e){el('scanState').textContent='Connection lost; showing last available data';el('statusDot').className='status-dot error';el('headerStatus').textContent='Offline'}}render();refresh();setInterval(()=>{if(!document.hidden)refresh()},30000);document.addEventListener('visibilitychange',()=>{if(!document.hidden)refresh()});window.addEventListener('storage',e=>{if(['propertyScoutSavedV1','propertyScoutViewedV1','propertyScoutArchivedV1','propertyScoutNotesV1'].includes(e.key)){saved=load('propertyScoutSavedV1',{})||{};viewed=load('propertyScoutViewedV1',{})||{};archived=load('propertyScoutArchivedV1',{})||{};notes=load('propertyScoutNotesV1',{})||{};render()}});
</script></body></html>''',cities=CITIES)
if __name__=='__main__':
    threading.Thread(target=loop,daemon=True).start();app.run(host='0.0.0.0',port=int(os.getenv('PORT','8000')),debug=False,use_reloader=False)
