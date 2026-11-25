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
        if detail and (daily>=6 or count>=185):return False
        if daily>=5 and not detail:
            if daily>=7 or db.execute('SELECT COUNT(*) FROM diagnostic').fetchone()[0]:return False
            db.execute('INSERT INTO diagnostic VALUES (1)')
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
        recovery=(count==1 and not old.get('outcome')) or (count==2 and old.get('outcome')=='error' and 'ReadTimeout' in old.get('message',''))
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
        rent_rows,rent_message,rent_success=rentcast_scan()
        errors.append(rent_message)
        print(rent_message,flush=True)
        rejected.extend(state.get('rentcast_diagnostics',{}).get('rejected',[]))
        if rent_success or rent_rows:
            rows.extend(rent_rows);successes+=1
        if zip_records:successes+=1
        unique={}
        for row in rows:
            key=(re.sub(r'[^a-z0-9]','',row['address'].lower()),row['city']); old=unique.get(key)
            if not old or (bool(row['url']),len(row['photos']))>(bool(old['url']),len(old['photos'])):unique[key]=row
        if successes:
            state['listings']=sorted(unique.values(),key=lambda x:x['price'])
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
def listings():return jsonify(state)
@app.get('/')
def home():return render_template_string(r'''<!doctype html>
<html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>Property Scout</title>
<style>
*{box-sizing:border-box}body{margin:0;background:#f4f5f2;color:#21312b;font:15px/1.5 system-ui,sans-serif}main{max-width:1280px;margin:auto;padding:32px 24px 64px}header{border-bottom:1px solid #dce2da;padding-bottom:24px}h1{font-size:38px;letter-spacing:-1.5px;line-height:1.1;margin:8px 0}h2{font-size:21px;letter-spacing:-.4px;margin:24px 0 12px}p{margin:6px 0}small,.muted{color:#62716a}.eyebrow{font-size:11px;font-weight:750;letter-spacing:1.8px;color:#476758}.filters{display:flex;flex-wrap:wrap;gap:12px;align-items:end;padding:18px 0}.field{display:grid;gap:5px;font-size:12px;font-weight:650}select,button{font:inherit;padding:10px 14px;border:1px solid #d0d9d0;border-radius:8px;background:white;color:inherit}label.check{display:flex;align-items:center;gap:6px;padding:10px 0}.stats{display:flex;gap:12px;flex-wrap:wrap}.stat{background:white;border:1px solid #dce2da;border-radius:12px;padding:12px 18px;min-width:140px;flex:1}.stat strong{display:block;font-size:25px}.stat small{display:block}#grid{display:grid;grid-template-columns:repeat(auto-fill,minmax(290px,1fr));gap:18px}article{background:white;border:1px solid #dce2da;border-radius:14px;overflow:hidden;display:flex;flex-direction:column;min-width:0}.cover{height:200px;background:#e5eae3;display:grid;place-items:center;color:#64766b;font-size:12px}.cover img{width:100%;height:200px;object-fit:cover}.content{padding:18px;flex:1;display:flex;flex-direction:column;gap:10px}.price{font-size:29px;line-height:1.15;font-weight:750;letter-spacing:-.7px}.address{font-size:16px;font-weight:650;overflow-wrap:anywhere}.tags{display:flex;gap:6px;flex-wrap:wrap}.tag{display:inline-block;background:#edf1eb;padding:4px 8px;border-radius:5px;font-size:11px;font-weight:650}.warning{background:#fff3da;color:#795411}.numbers{display:grid;grid-template-columns:1fr 1fr;gap:8px;background:#f5f7f4;border-radius:9px;padding:12px}.numbers strong{display:block;font-size:18px}.numbers small{font-size:11px}.actions{display:flex;flex-wrap:wrap;gap:8px;margin-top:auto}.actions a{padding:9px 12px;border-radius:8px;border:1px solid #ced9d0;text-decoration:none;color:#235b45;font-weight:650;font-size:13px}.save{cursor:pointer;border-color:#cbd7ce;color:#225d46;font-size:13px;font-weight:650;padding:9px 12px}.save[aria-pressed=true]{background:#e4eee6;border-color:#558065}.actions a:first-child{background:#225d46;color:white;border-color:#225d46}details{margin:16px 0;background:white;border:1px solid #dce2da;border-radius:10px;padding:13px 16px}summary{cursor:pointer;font-weight:650}article details{margin:0;padding:8px 0;border:0;border-radius:0;font-size:13px}article details p{white-space:pre-wrap;overflow-wrap:anywhere}a{color:#245e48}.empty{grid-column:1/-1;background:white;border:1px solid #dce2da;border-radius:12px;padding:28px;color:#62716a}.tablewrap{overflow-x:auto;margin-top:12px}table{width:100%;border-collapse:collapse;text-align:left;font-size:13px}th,td{padding:10px 12px;border-bottom:1px solid #e4e8e2;vertical-align:top}th{color:#63746b;font-size:11px;text-transform:uppercase;letter-spacing:.5px}td:nth-child(2){white-space:nowrap}.source{padding:12px 0;border-bottom:1px solid #e4e8e2}.source a{display:inline-block;margin:4px 12px 4px 0}#diagnostics{white-space:pre-wrap;font-size:12px;color:#64736b}footer{margin-top:24px;font-size:12px;color:#64736b}@media(max-width:540px){main{padding:20px 14px}h1{font-size:32px}#grid{grid-template-columns:1fr}.stat{min-width:120px}.filters{gap:9px}}
</style></head><body><main>
<header><div class="eyebrow">SACRAMENTO REGION / REAL ESTATE</div><h1>Property Scout</h1><p class="muted">Distressed homes below $260,000. No known HOA, no mobile homes. Conventional financing and a 21-day closing required; unknown terms must be verified.</p></header>
<div class="filters"><label class="field">Location<select id="city"><option>All cities</option>{% for c in cities %}<option>{{c}}</option>{% endfor %}</select></label><label class="field">Down payment<select id="down"><option value="10">10%</option><option value="12">12%</option></select></label><label class="field">Sort by<select id="sort"><option value="low">Lowest price</option><option value="high">Highest price</option><option value="city">City</option></select></label><label class="check"><input type="checkbox" id="verified"> Conventional mentioned only</label><label class="check"><input type="checkbox" id="closingVerified"> 21-day closing indicated only</label><label class="check"><input type="checkbox" id="savedOnly"> Saved listings <span id="savedCount"></span></label></div>
<div class="stats"><div class="stat"><small>Matching properties</small><strong id="count">0</strong></div><div class="stat"><small>Lowest asking price</small><strong id="lowest">Not available</strong></div><div class="stat"><small>Last scan</small><strong id="scanTime" style="font-size:16px">Waiting</strong><small id="scanState"></small></div></div>
<h2>Available candidates</h2><div id="grid"></div>
<details><summary id="rejectTitle">Rejected listings</summary><div class="tablewrap"><table><thead><tr><th>Property</th><th>Price</th><th>Reason</th><th>Source</th></tr></thead><tbody id="rejected"></tbody></table></div></details>
<details><summary>Daily source checks</summary><div id="publicSources"></div></details>
<details><summary>Scanner diagnostics</summary><p id="diagnostics"></p></details>
<footer>Financing, HOA status and availability require independent confirmation. Down payment estimates exclude closing costs and PMI. Saved listings are stored in this browser, not synchronized across devices.</footer>
</main><script>
const el=id=>document.getElementById(id), money=n=>Number(n).toLocaleString('en-US',{style:'currency',currency:'USD',maximumFractionDigits:0});let data={listings:[]};let saved={};try{const v=JSON.parse(localStorage.getItem('propertyScoutSavedV1')||'{}');if(v&&typeof v==='object'&&!Array.isArray(v))saved=v}catch(e){}function listingKey(x){return String(x.address||'').toLowerCase().replace(/[^a-z0-9]/g,'')+'|'+String(x.city||'').toLowerCase()}function toggleSaved(x){const key=listingKey(x);if(Object.prototype.hasOwnProperty.call(saved,key))delete saved[key];else saved[key]=x;try{localStorage.setItem('propertyScoutSavedV1',JSON.stringify(saved))}catch(e){el('scanState').textContent='Saved for this session only'}render()}
function add(p,t,v,cls){const x=document.createElement(t);if(v!==undefined)x.textContent=v;if(cls)x.className=cls;p.append(x);return x}
function link(p,u,t){if(!u)return;try{const parsed=new URL(u);if(!['https:','http:'].includes(parsed.protocol))return;const a=add(p,'a',t);a.href=parsed.href;a.target='_blank';a.rel='noopener noreferrer'}catch(e){}}
function addr(a){return typeof a==='object'&&a?([a.full||a.streetAddress||a.street,a.city,a.state,a.zipcode||a.zip].filter(Boolean).join(', ')||'Address unavailable'):(a||'Address unavailable')}
function tag(p,v,warn){add(p,'span',v,warn?'tag warning':'tag')}
function render(){
 const grid=el('grid');grid.replaceChildren();const down=Number(el('down').value);
 const current=data.listings||[];const savedOnly=el('savedOnly').checked;const live=new Map(current.map(x=>[listingKey(x),x]));const pool=savedOnly?Object.entries(saved).map(([k,x])=>live.get(k)||{...x,saved_snapshot:true}):current;el('savedCount').textContent='('+Object.keys(saved).length+')';
 const rows=pool.filter(x=>(el('city').value==='All cities'||x.city===el('city').value)&&(!el('verified').checked||String(x.financing).startsWith('Conventional'))&&(!el('closingVerified').checked||x.closing_status==='21-day closing appears possible'));
 rows.sort((a,b)=>(Number(b.closing_status==='21-day closing appears possible'&&String(b.financing).startsWith('Conventional'))-Number(a.closing_status==='21-day closing appears possible'&&String(a.financing).startsWith('Conventional')))||(el('sort').value==='city'?String(a.city).localeCompare(String(b.city))||a.price-b.price:el('sort').value==='high'?b.price-a.price:a.price-b.price));
 el('count').textContent=rows.length;el('lowest').textContent=rows.length?money(Math.min(...rows.map(x=>x.price))):'Not available';
 el('scanTime').textContent=data.updated?new Date(data.updated).toLocaleString('en-US',{timeZone:'America/Los_Angeles',month:'short',day:'numeric',hour:'numeric',minute:'2-digit'})+' PT':'Waiting';el('scanState').textContent=data.running?'Scanning now':'Daily refresh';el('diagnostics').textContent=(data.errors||[]).join('\n')||'No messages';
 if(!rows.length)add(grid,'div',data.running?'Searching for properties…':'No matching properties in the current scan. Review the rejected listings and diagnostics below.','empty');
 for(const x of rows){const card=add(grid,'article');const cover=add(card,'div',undefined,'cover');const placeholder=add(cover,'span','Photo unavailable');if(x.photos&&x.photos.length){const img=add(cover,'img');img.alt=addr(x.address);img.loading='lazy';img.onload=()=>placeholder.remove();img.onerror=()=>img.remove();img.src=x.photos[0];img.style.gridArea='1 / 1';placeholder.style.gridArea='1 / 1'}
 const s=add(card,'div',undefined,'content');add(s,'div',money(x.price),'price');add(s,'div',addr(x.address),'address');add(s,'small',x.city+', California');const tags=add(s,'div',undefined,'tags');tag(tags,x.distress||'Distressed');tag(tags,x.hoa_status||'HOA unknown',!x.hoa_verified);tag(tags,x.financing||'Financing unverified',!String(x.financing).startsWith('Conventional'));tag(tags,x.closing_status||'21-day closing unverified',x.closing_status!=='21-day closing appears possible');if(x.saved_snapshot)tag(tags,'Saved snapshot; availability unverified',true);
 const nums=add(s,'div',undefined,'numbers');const dp=add(nums,'div');add(dp,'small',down+'% down');add(dp,'strong',money(x.price*down/100));const loan=add(nums,'div');add(loan,'small','Loan principal');add(loan,'strong',money(x.price*(1-down/100)));add(s,'small','Source: '+(x.source||'Unknown'));if(x.remarks){const d=add(s,'details');add(d,'summary','Property details');add(d,'p',x.remarks)}const actions=add(s,'div',undefined,'actions');link(actions,x.url||x.search_url,x.url?'View listing':'Find listing');const button=add(actions,'button',Object.prototype.hasOwnProperty.call(saved,listingKey(x))?'Unsave':'Save listing','save');button.type='button';button.setAttribute('aria-pressed',String(Object.prototype.hasOwnProperty.call(saved,listingKey(x))));button.onclick=()=>toggleSaved(x);link(actions,x.photo_search,'Photos');link(actions,'https://www.google.com/maps/search/?api=1&query='+encodeURIComponent(addr(x.address)+' '+x.city+' CA'),'Map')}
 const rejected=el('rejected');rejected.replaceChildren();const bad=data.rejected||[];el('rejectTitle').textContent='Rejected listings ('+bad.length+')';for(const x of bad){const tr=add(rejected,'tr');add(tr,'td',addr(x.address));add(tr,'td',x.price?money(x.price):'Unknown');add(tr,'td',x.reason||'Unspecified');const td=add(tr,'td',x.source||'');if(x.url){td.append(document.createElement('br'));link(td,x.url,'View listing')}}if(!bad.length){const tr=add(rejected,'tr');const td=add(tr,'td','No rejected listings saved yet.');td.colSpan=4}
 const pub=el('publicSources');pub.replaceChildren();for(const [name,rec] of Object.entries(data.public_sources||{})){const section=add(pub,'div',undefined,'source');add(section,'strong',name);add(section,'p',rec.status||'Unknown','muted');link(section,rec.url,'Source');for(const doc of rec.documents||[])link(section,doc.url,doc.title);for(const record of rec.records||[]){const p=add(section,'p',record.address+', '+record.city+' | '+record.status);link(p,record.url,'Find property')}}if(!pub.children.length)add(pub,'p','No source check results yet.');
}
async function refresh(){try{const response=await fetch('/api/listings');if(!response.ok)throw Error();data=await response.json();render()}catch(e){el('scanState').textContent='Unable to load scan'}}
for(const id of ['city','down','sort','verified','closingVerified','savedOnly'])el(id).onchange=render;refresh();setInterval(refresh,30000);
</script></body></html>''',cities=CITIES)
if __name__=='__main__':
    threading.Thread(target=loop,daemon=True).start();app.run(host='0.0.0.0',port=int(os.getenv('PORT','8000')),debug=False,use_reloader=False)
