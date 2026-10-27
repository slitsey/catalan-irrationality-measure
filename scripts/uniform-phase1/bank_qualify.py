"""Independent frozen-trial requalification against corrected D58 field/u1 constraints (E)."""
import os,sys,json,re,ast,hashlib,time
for k in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS'):os.environ[k]='1'
sys.dont_write_bytecode=True
from pathlib import Path
from fractions import Fraction as Q
ROOT=Path(r'C:\Users\seanl\Documents\Codex\2026-10-11\plea');SRC=ROOT/'outputs/Compatibility programme';WORK=ROOT/'work/catalan-uniform'
OUT=SRC/'lean-plan-2026-10-27/evidence/phase1/bank';OUT.mkdir(exist_ok=True)
END=SRC/'analytic-decay-2026-10-25/endpoints-v1'
sys.path[:0]=[str(ROOT/'work/pylibs'),str(END)]
from g_trial_check import check, digest
from g_providers import first_check,circle_check
D=(58,9,3,5,3)
def parse(path):
 text=path.read_text(encoding='utf-8-sig');data={}
 for name in ('Pc','Vc'):
  data[name]=ast.literal_eval(re.search(r'def '+name+r' : List ℤ := (\[.*?\])',text,re.S)[1])
 for name in ('P','V'):
  body=re.search(r'def '+name+r' : List TailQ := \[(.*?)\]',text,re.S)[1];rows=[]
  for row in re.findall('⟨(.*?)⟩',body,re.S):
   v=[Q(''.join(x.split())) for x in re.findall(r'\(([^():]+): ℚ\)',row)]
   assert len(v)==4
   rows.append(v)
  data[name]=rows
 return data
started=time.time()
trial=SRC/'G-displacement-2026-10-23/w590/q/data_k160_gi.json';j=json.loads(trial.read_text());lp=WORK/'CatalanMeasure/GenD/D58/Cert590/Data.lean';l=parse(lp)
for name in ('Pc','Vc'):assert l[name]==j[name]
for name,jn in (('P','tailsP'),('V','tailsV')):
 assert l[name]==[[Q(*t[k])for k in ('zr','zi','rr','ri')]for t in j[jn]]
 assert all(zr*zr+zi*zi<1 for zr,zi,rr,ri in l[name])
u1=Q(l['Pc'][0],2**j['bits'])+sum(rr*zr-ri*zi for zr,zi,rr,ri in l['P'])
assert u1>=Q(9,50)
cf=tuple(Q(v,D[0])for v in (D[1]+D[2]+2*D[3],2*D[4],sum(D),D[1],D[2],D[0]-D[3]))
assert cf==tuple(map(Q,('11/29','3/29','39/29','9/58','3/58','53/58')))
first=first_check(D,OUT/'first-requalified.json',WORK/'CatalanMeasure/FirstStrongTrial/Data.lean')
circle=circle_check(D,OUT/'circle-requalified.json')
second=check(SRC/'G-analytic-decay-2026-10-26/codex-prototype/d58-gi.json',OUT/'second-requalified.json')
assert Q(second['u1'])==u1
assert Q(second['weighted_norm_upper'])<=Q(1547241039,2000000000)
assert sum(Q(second['caps'][k])for k in 'XY')==Q(-253949899,100000000)
assert Q(second['caps']['R'])==Q(-315531,5000000)
assert Q(first['norm_cap'])<=Q(67761,100000)
assert Q(first['field_cap'])==Q(-248835,100000)
gain=Q(534121468871212736197,24183176360959455840);eta=Q(3007,100);rho=58*Q(214443,50000)+Q(29,10)*Q(18203,1000);B=Q(532);k=B/rho;delta=Q(29,10)*Q(1,10**7);w=Q(3,4);d0=Q(53)
gates=[rho*k==B,eta>0,rho>0,w>0,2*w<k,delta>0,1<2*(w-delta*(2*k-w)),eta<2*d0,d0+4*d0*delta*k<eta*k]
assert all(gates)
# Use a rigorous rational upper bound on log 2 to lower bound tDelta - gD.
etaLower=58**2*Q(563964709,250000000)-Q(24733,4)+gain-(Q(58**2,2)+Q(2673,8))*Q(6931471808,10**10)
assert eta<etaLower
record=dict(schema='D58-CORRECTED-CONSTRAINT-REQUALIFICATION-1',evidence='E',kernel_checked=False,design=D,coefficients=list(map(str,cf)),gap='401/2500',stored_scale='1/'+str(2**j['bits']),u1=str(u1),u1_constraint='9/50',u1_slack=str(u1-Q(9,50)),physical_first_p_multiplier=2,second_u_multiplier=1,source_json_matches_all_lean_coefficients_and_tails=True,trial_sha256=digest(trial),lean_sha256=digest(lp),generator_sha256=digest(SRC/'G-analytic-decay-2026-10-26/geq.py'),gain=str(gain),eta=str(eta),rho=str(rho),B=str(B),kappa=str(k),delta=str(delta),pay_gates=gates,payment_margin=str(eta*k-d0-4*d0*delta*k),eta_lower=str(etaLower),eta_margin=str(etaLower-eta),seconds=time.time()-started,scope='An existing feasible analytic trial is requalified directly against corrected field coefficients, first-coefficient constraint, and exact gap; no claim that it reproduces the corrected optimizer solution, and no new denominator theorem.')
(OUT/'qualification.json').write_text(json.dumps(record,indent=2)+'\n');print(json.dumps(record,indent=2),flush=True)
