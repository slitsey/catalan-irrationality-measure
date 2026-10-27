"""Relocate only path labels in exact source/dependency/output-bound copied Lake traces."""
import json,hashlib,re,sys,os
from pathlib import Path
W=Path(r'C:\Users\seanl\Documents\Codex\2026-10-11\plea\work\catalan-uniform');R=W.parent/'catalan-release';E=W.parent.parent/'outputs/Compatibility programme/lean-plan-2026-10-27/evidence/phase1/bank/cache-relocation';E.mkdir(exist_ok=True)
memo={};checked={}
source_hashes=dict(line.split('	')for line in (E/'source-hashes.txt').read_text(encoding='utf-8-sig').splitlines()if '	'in line)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def locate(base,m):
 rel=Path(m.replace('.','/')+'.lean')
 if (base/rel).exists():return base,rel
 for p in (base/'.lake/packages').iterdir():
  if (p/rel).exists():return p,rel
 return None,None

def audit(m):
 if m in memo:return memo[m]
 b,rel=locate(W,m);rb,rrel=locate(R,m)
 if b is None or rb is None: # Lean/Init compiler-owned imports are bound by exact toolchain identity.
  if m.split('.')[0]not in ('Init','Lean','Lake','Std'):raise ValueError('missing source '+m)
  memo[m]=True;return True
 a=b/'.lake/build/lib/lean'/rel.with_suffix('.trace');z=rb/'.lake/build/lib/lean'/rrel.with_suffix('.trace')
 if not a.exists()or not z.exists():raise ValueError('missing trace '+m)
 x=json.loads(a.read_text(encoding='utf-8-sig'));y=json.loads(z.read_text(encoding='utf-8-sig'))
 packageCache='inputs'not in x or 'inputs'not in y
 if packageCache and (b==W or rb==R):raise ValueError('no complete project trace inputs '+m)
 exact_bytes=sha(b/rel)==sha(rb/rrel)
 if not exact_bytes:
  if (b/rel).read_bytes().decode('utf8').replace('\r\n','\n')!=(rb/rrel).read_bytes().decode('utf8').replace('\r\n','\n'):raise ValueError('substantive source mismatch '+m)
 if b==W:
  source_entries=[pair[1]for pair in x['inputs']if isinstance(pair[0],str)and pair[0].replace('\\','/').endswith(str(rel).replace('\\','/'))]
  if len(source_entries)!=1 or source_entries[0]!=source_hashes.get(str(b/rel)):raise ValueError('actual Lake source hash mismatch '+m)
 # Relative versus absolute source input labels may differ; all input values and every other key must match.
 def normalized(t):
  t=json.loads(json.dumps(t));t.pop('log',None)
  for pair in t.get('inputs',[]):
   if isinstance(pair[0],str)and pair[0].replace('\\','/').endswith(str(rel).replace('\\','/')):pair[0]='SOURCE'
  return t
 if normalized(x)!=normalized(y):raise ValueError('substantive trace difference '+m)
 artifacts=[]
 for key,suffixes in [('o',['.olean','.olean.server','.olean.private']),('i',['.ilean']),('rs',['.ir.sig']),('r',['.ir'])]:
  val=x['outputs'].get(key)
  if val is None:continue
  vals=val if isinstance(val,list)else[val]
  for v,suffix in zip(vals,suffixes):
   ap=b/'.lake/build/lib/lean'/rel.with_suffix(suffix);zp=rb/'.lake/build/lib/lean'/rrel.with_suffix(suffix)
   if not ap.exists()or not zp.exists():raise ValueError('missing output '+str(ap))
   h=sha(ap)
   if h!=sha(zp):raise ValueError('artifact mismatch '+str(ap))
   hp=Path(str(ap)+'.hash')
   if not hp.exists()or hp.read_text().strip()!=v.split('.')[0]:raise ValueError('Lake output hash mismatch '+str(ap))
   artifacts.append(dict(path=str(ap),sha256=h,lake_hash=v.split('.')[0]))
 deps=[]
 def walk(node):
  if isinstance(node,list):
   if len(node)==2 and isinstance(node[0],str) and node[0].endswith(':importArts'):deps.append(node[0][:-11])
   for v in node:walk(v)
 walk(x.get('inputs',[]))
 for d in deps:audit(d)
 memo[m]=True
 checked[m]=dict(immutable_package_cache=packageCache,exact_source_bytes=exact_bytes,source_sha256=sha(b/rel),release_source_sha256=sha(rb/rrel),normalized_source_sha256=hashlib.sha256((b/rel).read_text(encoding='utf-8-sig').encode('utf8')).hexdigest(),trace_sha256=sha(a),outputs=artifacts,dependencies=deps)
 return True
receipts=[]
for m in sys.argv[1:]:
 try:
  ownership=E/'arithmetic-old-import-closure.json'
  if ownership.exists()and m in json.loads(ownership.read_text())and os.environ.get('BANK_CACHE_OWNER')!='arithmetic':raise ValueError('arithmetic partition owns target '+m)
  exclusions=E/'exclusions.txt'
  if exclusions.exists()and m in exclusions.read_text(encoding='utf-8-sig').splitlines():raise ValueError('other lane owns active/qualified target '+m)
  audit(m);b,rel=locate(W,m);rb,rrel=locate(R,m);p=b/'.lake/build/lib/lean'/rel.with_suffix('.trace');old=p.read_bytes();t=json.loads(old)
  c=t['outputs'].get('c');copied=[]
  if c:
   cp=b/'.lake/build/ir'/rel.with_suffix('.c');rcp=rb/'.lake/build/ir'/rrel.with_suffix('.c');rh=Path(str(rcp)+'.hash')
   if not rcp.exists()or not rh.exists()or rh.read_text().strip()!=c.split('.')[0]:raise ValueError('unbound C artifact '+m)
   if cp.exists()and sha(cp)!=sha(rcp):raise ValueError('different existing C artifact '+m)
   cp.parent.mkdir(parents=True,exist_ok=True)
   if not cp.exists():cp.write_bytes(rcp.read_bytes());Path(str(cp)+'.hash').write_bytes(rh.read_bytes());copied.append(dict(path=str(cp),sha256=sha(cp),lake_hash=c.split('.')[0]))
  changes=[]
  for pair in t.get('inputs',[]):
   if isinstance(pair[0],str)and pair[0].replace('\\','/').endswith(str(rel).replace('\\','/')):
    before=pair[0];after=str(b/rel)
    if before!=after:pair[0]=after;changes.append(dict(before=before,after=after))
  backup=E/(m+'-before.trace')
  if not backup.exists():backup.write_bytes(old)
  if changes:
   tmp=Path(str(p)+'.relocate-tmp');tmp.write_text(json.dumps(t,ensure_ascii=False,indent=1)+'\n',encoding='utf8');tmp.replace(p)
  rec=dict(module=m,status='relocated'if changes else'already_bound',changes=changes,copied_c_artifacts=copied,before_sha256=hashlib.sha256(old).hexdigest(),after_sha256=sha(p),rationale='Only source input label relocated; exact normalized source text and Lake source hash (byte hashes separately recorded), complete input values/options/toolchain/module identity/dependency hashes, and output hashes identical. Original compiler log preserved as provenance; no fresh compilation claimed.')
 except Exception as ex:rec=dict(module=m,status='rejected',error=str(ex))
 receipts.append(rec);print(json.dumps(rec),flush=True)
(E/('receipt-'+sys.argv[1].replace('.','_')+'.json')).write_text(json.dumps(dict(receipts=receipts,recursively_checked=checked),indent=2)+'\n')









