import json,datetime,hashlib
from pathlib import Path
E=Path(r'C:/Users/seanl/Documents/Codex/2026-10-11/plea/outputs/Compatibility programme/lean-plan-2026-10-27/evidence/phase1');p=E/'bank-provider-hold.json';cfg=dict(target='CatalanMeasure.GenD.Uniform.Bank.Providers532',reason='Parent-authorized exact provider hold while prefix lane owns UpperPrime/PL/OddProfile refresh',created_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),new_invocations_only=True,before_guard_reservation=True)
p.write_text(json.dumps(cfg,indent=2)+'\n');(E/'bank/provider-hold-config.json').write_text(json.dumps(cfg,indent=2)+'\n')
r=Path(r'C:/Users/seanl/Documents/Codex/2026-10-11/plea/work/catalan-uniform/scripts/uniform-phase0/run_guarded.py');(E/'bank/provider-hold-install.json').write_text(json.dumps(dict(runner_sha256=hashlib.sha256(r.read_bytes()).hexdigest(),target=cfg['target'],no_other_targets_held=True),indent=2)+'\n')
