"""Sequential leaf-first submissions to the authorized shared build driver."""
from pathlib import Path
import hashlib
import json
import subprocess
import sys
import time

ROOT = Path(r'C:/Users/seanl/Documents/Codex/2026-10-11/plea/work/catalan-uniform')
LOGS = ROOT.parents[1]/'outputs/Compatibility programme/lean-plan-2026-10-27/evidence/claude/logs'
HERE = Path(__file__).parent
receipt_path = HERE/'build-evidence.json'
import importlib.util
_admit_spec=importlib.util.spec_from_file_location('sevenths_admit',Path(__file__).parent/'admit.py')
admit=importlib.util.module_from_spec(_admit_spec)
_admit_spec.loader.exec_module(admit)

from types import SimpleNamespace
receipts = json.loads(receipt_path.read_text()) if receipt_path.exists() else []

targets = sys.argv[1:]
if not targets:
    targets = ['Final', 'Members', 'Audit', 'TwoTerm', 'UF', 'Content']
for short in targets:
    target = short if short.startswith('Catalan') else 'CatalanCore.Uniform.Bank.Sevenths.'+short
    path = ROOT/(target.replace('.', '/')+'.lean')
    identity = hashlib.sha256(path.read_bytes()).hexdigest()
    started = time.time()
    proc = SimpleNamespace(returncode=admit.ensure(target), stdout='', stderr='')
    (HERE/(target.replace('.', '_')+'.lane.txt')).write_text(proc.stdout+proc.stderr, encoding='utf-8')
    logs = sorted(LOGS.glob(target.replace('.', '_')+'-build*.log'), key=lambda p: p.stat().st_mtime)
    log = logs[-1] if logs else LOGS/'missing-build-log'
    accepted = (proc.returncode == 0 and log.exists() and log.stat().st_mtime >= path.stat().st_mtime
                and 'Build completed successfully' in log.read_text(encoding='utf-8')
                and hashlib.sha256(path.read_bytes()).hexdigest() == identity)
    receipts.append(dict(target=target, rc=proc.returncode, accepted=accepted,
                         sha256=identity, started=started, ended=time.time()))
    per_module = HERE/'module-receipts'
    per_module.mkdir(exist_ok=True)
    (per_module/(target.replace('.', '_')+'.json')).write_text(json.dumps(receipts[-1], indent=2)+'\n', encoding='utf-8')
    print(target, 'accepted=', accepted, 'rc=', proc.returncode, flush=True)
    if not accepted:
        print(proc.stdout+proc.stderr, flush=True)
        raise SystemExit(proc.returncode or 1)
