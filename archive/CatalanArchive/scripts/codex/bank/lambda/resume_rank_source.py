from pathlib import Path
import json,subprocess,sys,itertools
r=Path(__file__).resolve().parents[4];s=r/'scripts/codex/bank/lambda';d=r.parent/'tools/lanes/done';latest={}
for p in d.glob('*.json'):
 try:x=json.loads(p.read_text(encoding='utf-8-sig'))
 except (OSError,ValueError):continue
 t=x.get('target','')
 if x.get('submitted',0)>latest.get(t,{}).get('submitted',-1):latest[t]=x
rank=[x['module'] for x in json.loads((s/'rank-manifest.json').read_text())['certificates']]
source=json.loads((s/'source-manifest.json').read_text())
work=[t for pair in itertools.zip_longest(rank,source) for t in pair if t and latest.get(t,{}).get('rc')!=0]
print('Resuming unfinished rank/source',len(work),flush=True)
sys.exit(subprocess.call([sys.executable,'-I','-X','utf8',str(s/'queue_nouf.py'),*work],cwd=r))
