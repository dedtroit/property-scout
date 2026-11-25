import os, re, time, threading, csv, io, sqlite3
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
lock=threading.Lock(); state={'listings':[],'errors':[],'updated':None,'running':False}
def safeurl(s):
    return s if isinstance(s,str) and urlparse(s).scheme in ('https','http') and urlparse(s).netloc else ''
def normalize(raw, source):
    a=raw.get('address') or {}; a=a if isinstance(a,dict) else {'full':a}
    city=str(a.get('city') or raw.get('city') or '').strip().title()
    if city not in CITIES or str(a.get('state') or raw.get('state') or '').upper() not in ('CA','CALIFORNIA'): return
    try: price=float(raw.get('listPrice') or raw.get('price') or 0)
    except (TypeError,ValueError): return
    if not 0<price<260000:return
    prop=raw.get('property') or {}; typ=str(prop.get('type') or raw.get('property_type') or '').lower(); sub=str(prop.get('subType') or '').lower()
    if typ not in ('residential','single family','single family residence','singlefamily','house','single family home','single family detached') or any(x in sub+' '+typ for x in ('condo','manufactured','mobile','townhouse','land')):return
    status=str((raw.get('mls') or {}).get('status') or raw.get('status') or '').lower()
    if status not in ('active','for sale'):return
    remarks=' '.join(str(raw.get(k) or '') for k in ('remarks','description','distress_type','financing'))
    match=DISTRESS.search(remarks)
    if not match or CASH.search(remarks):return
    financing='Conventional mentioned; verify terms' if CONV.search(remarks) and not re.search(r'\b(no|not|cannot accept)\s+conventional\b',remarks,re.I) else 'Financing unverified'
    address=a.get('full') or raw.get('street_address') or ' '.join(str(a.get(k) or '') for k in ('streetNumber','streetName')).strip()
    if not address:return
    photos=raw.get('photos') or []; photos=photos if isinstance(photos,list) else [photos]
    link=safeurl(raw.get('listing_url') or raw.get('url'))
    return dict(address=address,city=city,price=price,source=source,distress=match.group(),financing=financing,remarks=remarks[:1800],photos=[safeurl(p) for p in photos if safeurl(p)],url=link,search_url='https://www.google.com/search?q='+quote_plus(address+' '+city+' CA real estate listing'),photo_search='https://www.google.com/search?tbm=isch&q='+quote_plus(address+' '+city+' CA'))
def reserve_request():
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
        if count>=200 or daily>=5:return False
        db.execute('INSERT INTO calls VALUES (?)',(now,))
        return True
def scan():
    if not lock.acquire(False):return
    state['running']=True; rows=[]; errors=[]; successes=0
    try:
        key=os.getenv('RAPIDAPI_KEY')
        if key:
            for zipcode in ['95678','95765','95843','95610','95630']:
                try:
                    if not reserve_request():break
                    response=requests.get('https://foreclosure-finder1.p.rapidapi.com/zipcode/all',params={'zipcode':zipcode,'radius':15,'limit':100,'sources':'hud,fanniemae,freddiemac,redfin'},headers={'X-RapidAPI-Key':key,'X-RapidAPI-Host':'foreclosure-finder1.p.rapidapi.com'},timeout=65,allow_redirects=False)
                    response.raise_for_status()
                    payload=response.json()
                    meta=payload.get('meta',{})
                    if meta.get('failedSources') or meta.get('totalCount',0)>len(payload.get('listings',[])):errors.append(zipcode+': incomplete source coverage or results truncated')
                    for item in payload['listings']:
                        source=str(item.get('source','')).lower()
                        address=str(item.get('address',''))
                        match=re.search(r',\s*([^,]+),\s*CA\s+\d{5}',address,re.I)
                        if not match:continue
                        status=str(item.get('status','')).lower()
                        if status not in ('active','for sale','available','listed'):continue
                        if source not in ('hud','fanniemae','freddiemac','redfin'):continue
                        price=item.get('listPrice') or item.get('price') or (item.get('openingBid') if source in ('hud','fanniemae','freddiemac') else None)
                        typ=str(item.get('propertyType','')).lower().replace('_',' ')
                        photos=item.get('photos') or item.get('photoUrl') or item.get('photo') or []
                        row=normalize({'address':address,'city':match.group(1),'state':'CA','price':price,'property_type':typ,'status':'active','distress_type':item.get('assetType') or ('bank owned' if source!='redfin' else 'foreclosure'),'description':item.get('description'),'financing':item.get('financing'),'photos':photos,'listing_url':item.get('propertyLink')},source)
                        if row:rows.append(row)
                    successes+=1
                except Exception as e:errors.append(zipcode+': '+type(e).__name__)
                if 'response' in locals() and response.status_code==429:break
        else:errors.append('RAPIDAPI_KEY not configured')
        for feed in os.getenv('AUTHORIZED_FEEDS','').split(','):
            if not feed.strip():continue
            try:
                r=requests.get(feed.strip(),timeout=25);r.raise_for_status(); batch=r.json() if 'json' in r.headers.get('Content-Type','') else list(csv.DictReader(io.StringIO(r.text)))
                rows.extend(filter(None,(normalize(x,urlparse(feed).netloc) for x in batch)))
                successes+=1
            except Exception as e:errors.append('Feed '+urlparse(feed).netloc+': '+type(e).__name__)
        unique={}
        for row in rows:
            key=(re.sub(r'[^a-z0-9]','',row['address'].lower()),row['city']); old=unique.get(key)
            if not old or (bool(row['url']),len(row['photos']))>(bool(old['url']),len(old['photos'])):unique[key]=row
        if successes:state['listings']=sorted(unique.values(),key=lambda x:x['price'])
        state['errors']=errors;state['updated']=datetime.now(timezone.utc).isoformat()
    finally:state['running']=False;lock.release()
def loop():
    while True:scan();time.sleep(86400)
@app.get('/api/listings')
def listings():return jsonify(state)
@app.get('/')
def home():return render_template_string('''<!doctype html><html><meta name="viewport" content="width=device-width,initial-scale=1"><title>Property Scout</title><style>body{font:16px system-ui;background:#f5f5f0;color:#24332f;margin:0}main{max-width:1100px;margin:auto;padding:24px}h1{font-size:40px;margin:8px 0}select,button{padding:10px;border:1px solid #abb8ae;border-radius:8px;background:white}#grid{display:grid;grid-template-columns:repeat(auto-fit,minmax(260px,1fr));gap:16px}article{background:white;border-radius:12px;overflow:hidden;border:1px solid #ddd}article img{width:100%;height:180px;object-fit:cover}section{padding:16px}a{color:#17634e}small{color:#52665b}#status{white-space:pre-wrap}</style><main><small>SACRAMENTO REGION / DISTRESSED HOMES</small><h1>Property Scout</h1><p>Below $260,000 • Conventional financing candidates</p><select id="city"><option>All cities</option>{% for c in cities %}<option>{{c}}</option>{% endfor %}</select> <select id="down"><option value="10">10% down</option><option value="12">12% down</option></select> <label><input type="checkbox" id="verified"> Conventional mentioned only</label><p id="status"></p><div id="grid"></div><h2>Additional lead sources</h2><p><a href="https://homepath.fanniemae.com/">HomePath</a> · <a href="https://www.homesteps.com/">HomeSteps</a> · <a href="https://www.hudhomestore.gov/">HUD</a> · <a href="https://www.google.com/search?q=Sacramento+County+tax+sale">Sacramento tax sales</a> · <a href="https://www.google.com/search?q=Placer+County+tax+sale">Placer tax sales</a></p><small>Tax auctions frequently require cash; source links are not verified matches. Financing and property condition require lender review.</small></main><script>
let data={listings:[]}; const el=id=>document.getElementById(id), money=n=>n.toLocaleString('en-US',{style:'currency',currency:'USD',maximumFractionDigits:0});function add(p,t,v){let x=document.createElement(t);x.textContent=v;p.append(x);return x}function link(p,u,t){let a=add(p,'a',t);a.href=u;a.target='_blank';a.rel='noopener noreferrer';p.append(' · ')}function render(){let grid=el('grid');grid.replaceChildren();let rows=data.listings.filter(x=>(el('city').value==='All cities'||x.city===el('city').value)&&(!el('verified').checked||x.financing.startsWith('Conventional')));el('status').textContent=rows.length+' candidates | '+(data.updated||'Waiting for scan')+(data.running?' | Scanning':'')+'\\n'+(data.errors||[]).join('\\n');for(let x of rows){let card=document.createElement('article');if(x.photos.length){let img=document.createElement('img');img.src=x.photos[0];img.alt=x.address;img.onerror=()=>img.remove();card.append(img)}let s=document.createElement('section');card.append(s);add(s,'h2',money(x.price));add(s,'strong',x.address+', '+x.city);add(s,'p',x.distress+' | '+x.financing);add(s,'p','Down payment '+money(x.price*Number(el('down').value)/100));add(s,'small',x.source);add(s,'p',x.remarks);link(s,x.url||x.search_url,x.url?'Open listing':'Find listing');link(s,x.photo_search,'Photos');grid.append(card)}}async function refresh(){try{data=await (await fetch('/api/listings')).json();render()}catch(e){el('status').textContent='Unable to load scan'}}for(let id of ['city','down','verified'])el(id).onchange=render;refresh();setInterval(refresh,30000);
</script></html>''',cities=CITIES)
if __name__=='__main__':
    threading.Thread(target=loop,daemon=True).start();app.run(host='0.0.0.0',port=int(os.getenv('PORT','8000')),debug=False,use_reloader=False)
