import importlib.util,json
from pathlib import Path
spec=importlib.util.spec_from_file_location('weighted',str(Path(__file__).with_name('nonclean-weighted-model.py')));P=importlib.util.module_from_spec(spec);spec.loader.exec_module(P)
rows=json.loads(Path(__file__).with_name('weighted-law-controls.json').read_text());out=[]
for x in rows:
 y=P.run(x['r'],x['m'],x['p'],int(x['kind']),x['u']);out.append(y)
 assert y['predicted_fit'] and y['free_long_zero'] and y['free_short_constant'] and y['pole_jumps_nonzero'],y
 if len(out)%100==0:print('exact weighted controls passed',len(out),flush=True)
assert len(out)==685
Path(__file__).with_name('weighted-law-controls.json').write_text(json.dumps(out))
print('ALL exact weighted/source/geometry controls passed',len(out),flush=True)
