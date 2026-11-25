"""Daily public recorder index reader. Never bypasses access restrictions."""
import csv, io, json, os, re, time
from datetime import datetime, timedelta, timezone
from pathlib import Path
from urllib.robotparser import RobotFileParser
import requests

URL = 'https://recordersdocumentindex.saccounty.gov/'
AGENT = 'PropertyScoutBot/1.0'
NOTICE = re.compile(r'NOTICE\s+OF\s+DEFAULT', re.I)
DOC = re.compile(r'^\d{8,14}$')
DATE = re.compile(r'\b(?:\d{1,2}/\d{1,2}/\d{4}|\d{4}-\d{2}-\d{2})\b')

def parse_rows(rows):
    found = {}
    for cells in rows:
        cells = [' '.join(str(v or '').split()) for v in cells]
        if not any(NOTICE.search(c) for c in cells): continue
        if any(re.search(r'\b(?:RESCISSION|CANCELLATION|CANCEL)\b',c,re.I) for c in cells if NOTICE.search(c)): continue
        number = next((c for c in cells if DOC.fullmatch(c)), None)
        date = next((DATE.search(c).group() for c in cells if DATE.search(c)), None)
        if not number or not date: continue
        found[number] = {'document_number':number,'recorded_date':date,'document_type':'Notice of Default','county':'Sacramento','url':URL}
    return list(found.values())

def check_access():
    r = requests.get(URL+'robots.txt',headers={'User-Agent':AGENT},timeout=15,allow_redirects=False)
    if r.status_code in (404,410): return
    if r.status_code != 200: raise RuntimeError('Recorder robots access HTTP '+str(r.status_code))
    parser=RobotFileParser(); parser.parse(r.text.splitlines())
    if not parser.can_fetch(AGENT,URL): raise RuntimeError('Recorder disallows automated access')

def browser_rows():
    from playwright.sync_api import sync_playwright
    check_access()
    def blocked(page):
        text=page.locator('body').inner_text(timeout=10000)
        if re.search(r'requested URL was rejected|access denied|verify you are human|captcha|automated access (?:is )?(?:prohibited|disallowed)',text,re.I):
            raise RuntimeError('Recorder blocked access or requires human verification')
        return text
    with sync_playwright() as p:
        browser=p.chromium.launch(headless=True)
        try:
            page=browser.new_page(user_agent=AGENT)
            response=page.goto(URL,wait_until='domcontentloaded',timeout=30000)
            if response and response.status>=400: raise RuntimeError('Recorder HTTP '+str(response.status))
            blocked(page)
            agree=page.get_by_role('button',name=re.compile(r'^agree$',re.I))
            if not agree.count(): agree=page.get_by_text('Agree',exact=True)
            if agree.count()==1:
                agree.click(timeout=10000);page.wait_for_timeout(1200)
            blocked(page)
            selected=False
            for select in page.locator('select').all():
                for option in select.locator('option').all():
                    label=option.inner_text().strip(); value=option.get_attribute('value') or ''
                    if value=='531' or re.search(r'\b531\b.*NOTICE OF DEFAULT|^NOTICE OF DEFAULT$',label,re.I):
                        select.select_option(value=value);selected=True;break
                if selected:break
            if not selected:
                raise RuntimeError('Filing code 531 control not recognized; county search form needs mapping')
            dates=page.locator('input[type=date]').all()
            if len(dates)!=2:
                dates=[]
                for item in page.locator('input').all():
                    if not item.is_visible():continue
                    meta=' '.join(item.get_attribute(k) or '' for k in ('id','name','placeholder','aria-label'))
                    if re.search(r'date|mm/dd/yyyy',meta,re.I) and (item.get_attribute('type') or 'text') in ('text','date'):dates.append(item)
            if len(dates)!=2:raise RuntimeError('Start and end date controls not recognized')
            today=datetime.now(timezone.utc).date()
            for item,d in zip(dates,(today-timedelta(days=7),today)):
                item.fill(d.isoformat() if item.get_attribute('type')=='date' else d.strftime('%m/%d/%Y'))
            search=page.get_by_role('button',name=re.compile(r'^search$',re.I))
            if search.count()!=1:raise RuntimeError('Search button not recognized')
            search.click(timeout=10000);page.wait_for_timeout(1800)
            all_rows=[];seen=set()
            for _ in range(10):
                body=blocked(page)
                rows=page.locator('table tr').evaluate_all('(rows)=>rows.map(r=>Array.from(r.querySelectorAll("td")).map(c=>c.innerText))')
                records=parse_rows(rows)
                if not records:
                    if not all_rows and re.search(r'no (?:matching )?(?:records|results|documents)(?: found)?|0 results',body,re.I):return [],False
                    raise RuntimeError('Results table not recognized or no explicit zero-results message')
                fresh=[x for x in records if x['document_number'] not in seen]
                if not fresh:raise RuntimeError('Pagination did not advance')
                all_rows.extend(fresh);seen.update(x['document_number'] for x in fresh)
                nxt=page.get_by_role('link',name=re.compile(r'^next(?: page)?$',re.I))
                if not nxt.count():nxt=page.get_by_role('button',name=re.compile(r'^next(?: page)?$',re.I))
                if not nxt.count():return all_rows,False
                if nxt.count()!=1:raise RuntimeError('Pagination ambiguous')
                if not nxt.is_enabled() or nxt.get_attribute('aria-disabled')=='true' or 'disabled' in (nxt.get_attribute('class') or '').lower():return all_rows,False
                nxt.click(timeout=10000);page.wait_for_timeout(1500)
            return all_rows,True
        finally:browser.close()

def authorized_csv(url):
    response=requests.get(url,timeout=30,allow_redirects=False)
    if response.status_code!=200:raise RuntimeError('Authorized CSV HTTP '+str(response.status_code))
    if 'html' in response.headers.get('Content-Type','').lower():raise RuntimeError('Expected CSV, received HTML')
    reader=csv.DictReader(io.StringIO(response.content.decode('utf-8-sig')))
    if not reader.fieldnames:raise RuntimeError('CSV missing headers')
    def canonical(k):return re.sub(r'[^a-z0-9]','',k.lower())
    headers={canonical(k):k for k in reader.fieldnames}
    def field(*keys):return next((headers[k] for k in keys if k in headers),None)
    doc=field('documentnumber','instrumentnumber','docnumber')
    date=field('recordeddate','recordingdate','documentdate','date')
    typ=field('documenttype','documenttitle','title','filingcode')
    if not all((doc,date,typ)):raise RuntimeError('CSV requires document number, recorded date, and document type')
    return parse_rows([[r[doc],r[date],'Notice of Default' if str(r[typ]).strip()=='531' else r[typ]] for r in reader]),False

def scan_recorder(base):
    path=Path(base).with_name('recorder_notices.json')
    try:old=json.loads(path.read_text())
    except Exception:old={}
    now=time.time()
    if now-old.get('checked_epoch',0)<86400:return old
    result={'url':URL,'checked_epoch':now,'checked':datetime.now(timezone.utc).isoformat(),'records':old.get('records',[])}
    try:
        feed=os.getenv('SACRAMENTO_RECORDER_CSV_URL')
        fresh,truncated=authorized_csv(feed) if feed else browser_rows()
        merged={x['document_number']:x for x in result['records']}
        merged.update({x['document_number']:x for x in fresh})
        result['records']=list(merged.values())
        result['last_success']=result['checked']
        result['status']=str(len(fresh))+' notices in latest search; '+str(len(merged))+' unique recorded notices'+('; page limit reached' if truncated else '')
    except Exception as e:
        result['last_success']=old.get('last_success')
        result['status']='Recorder search unavailable: '+(str(e)[:220] if isinstance(e,RuntimeError) else type(e).__name__)+'; retained prior records'
    path.parent.mkdir(parents=True,exist_ok=True)
    tmp=path.with_suffix('.tmp');tmp.write_text(json.dumps(result));tmp.replace(path)
    return result
