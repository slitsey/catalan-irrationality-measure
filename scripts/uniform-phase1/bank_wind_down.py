import json,datetime
from pathlib import Path
E=Path(r'C:/Users/seanl/Documents/Codex/2026-10-11/plea/outputs/Compatibility programme/lean-plan-2026-10-27/evidence/phase1');now=datetime.datetime.now(datetime.timezone.utc).isoformat()
p=E/'bank/provider-builds.json';d=json.loads(p.read_text());d.update(status='stopped_user_wind_down',stopped_utc=now,controller_pid=26912,controller_parent_pid=21620,controller_created_local='2026-10-27 15:03:33',controller_only_stopped=True,owned_live_jobs_remaining=[])
d['admitted_child_completion']=json.loads((E/'logs/CatalanMeasure_GenD_D58_Circle-build.json').read_text());p.write_text(json.dumps(d,indent=2)+'\n')
cfg=dict(target='CatalanMeasure.GenD.Uniform.Bank.Providers532',reason='User requested immediate wind-down and Claude handoff; no new admissions until explicit continuation',created_utc=now,new_invocations_only=True,before_guard_reservation=True)
(E/'bank-provider-hold.json').write_text(json.dumps(cfg,indent=2)+'\n');(E/'bank/wind-down-hold-config.json').write_text(json.dumps(cfg,indent=2)+'\n')
