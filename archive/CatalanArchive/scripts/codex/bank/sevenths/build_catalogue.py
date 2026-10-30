"""Validate the complete q7 local catalogue through the shared driver; adopt queued work."""
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor, as_completed
import hashlib, json, os, subprocess, sys, threading, time

ROOT = Path(r'C:/Users/seanl/Documents/Codex/2026-10-11/plea/work/catalan-uniform')
LANES = ROOT.parents[0]/'tools/lanes'
LOGS = ROOT.parents[1]/'outputs/Compatibility programme/lean-plan-2026-10-27/evidence/claude/logs'
HERE = Path(__file__).parent
OUT = HERE/'catalogue-receipts'
OUT.mkdir(exist_ok=True)
import importlib.util
_admit_spec=importlib.util.spec_from_file_location('sevenths_admit',Path(__file__).parent/'admit.py')
admit=importlib.util.module_from_spec(_admit_spec)
_admit_spec.loader.exec_module(admit)

PREFIX = 'CatalanCore.Uniform.Bank.Sevenths.'
lock = threading.Lock()
manifest = [dict(module=r['data']) for r in
            json.loads((HERE/'grouped-catalogue.json').read_text())['roots']]

def source(target):
    return ROOT/(target.replace('.', '/')+'.lean')

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def previous(target):
    path = source(target)
    candidates = sorted(LOGS.glob(target.replace('.', '_')+'-build*.json'), key=lambda p:p.stat().st_mtime)
    for meta in reversed(candidates):
        r = json.loads(meta.read_text(encoding='utf-8-sig'))
        log = Path(r['log'])
        if r.get('rc') == 0 and log.exists() and log.stat().st_mtime >= path.stat().st_mtime:
            text = log.read_text(encoding='utf-8')
            peaks = list(r.get('lean_process_peak_working_sets_bytes', {}).values())
            if 'Build completed successfully' in text and 'sorryAx' not in text and max(peaks, default=0) <= 2.5*2**30:
                return dict(target=target, accepted=True, sha256=digest(path), log=str(log), reused=True)
    return None

def existing(target):
    for folder in ('running', 'queue'):
        for p in (LANES/folder).glob('*.json'):
            try:
                r=json.loads(p.read_text(encoding='utf-8-sig'))
                if r.get('target') == target:
                    return p.stem
            except (OSError, ValueError):
                continue
    return None

def save(r):
    p=OUT/(r['target'].replace('.', '_')+'.json')
    tmp=p.with_suffix('.tmp')
    tmp.write_text(json.dumps(r, indent=2)+'\n', encoding='utf-8')
    tmp.replace(p)
    with lock:
        print(r['target'], 'accepted='+str(r['accepted']), flush=True)

def build(target):
    cached=previous(target)
    if cached:
        save(cached)
        return True
    path=source(target)
    sha=digest(path)
    start=time.time()
    job=existing(target)
    if job:
        done=LANES/'done'/(job+'.json')
        while not done.exists():
            time.sleep(3)
        r=json.loads(done.read_text(encoding='utf-8-sig'))
        rc=r['rc']
    else:
        rc=admit.ensure(target)
    checked=previous(target) if rc == 0 and digest(path) == sha else None
    r=checked or dict(target=target, accepted=False, sha256=sha, rc=rc)
    r.update(started=start, ended=time.time(), adopted_job=job)
    save(r)
    return r['accepted']

def pair(entry):
    data=entry['module']
    if not build(data):
        return False
    return build(data.replace('.RankData.', '.RankPalette.'))

if __name__ == '__main__':
    # The generic lemma is already queued. Adopting avoids a duplicate build.
    if not build('CatalanCore.Uniform.Content.RankProducer.Denominators'):
        raise SystemExit(1)
    results=[]
    with ThreadPoolExecutor(max_workers=3) as pool:
        jobs=[pool.submit(pair, e) for e in manifest]
        for future in as_completed(jobs):
            results.append(future.result())
    if not all(results):
        raise SystemExit(1)
    for suffix in ('RankData.Audit', 'RankPalette.Audit'):
        if not build(PREFIX+suffix):
            raise SystemExit(1)
    print('ALL_240_DATA_AND_PALETTE_CERTIFICATES_ACCEPTED_IN_SIX_ROOT_CLASSES', flush=True)
