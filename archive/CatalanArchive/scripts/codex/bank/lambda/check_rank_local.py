from pathlib import Path
from fractions import Fraction as Q
import json,hashlib
R=Path(r'C:\Users\seanl\Documents\Codex\2026-10-11\plea\work\catalan-uniform')
P=R.parents[1]/'outputs/Compatibility programme/bank-specs-2026-10-28'
d=json.loads((P/'rank-lambda.json').read_text())
def mul(A,B):
 n=len(B[0]) if B else 0
 return [[sum((x*y for x,y in zip(row,col)),Q(0)) for col in zip(*B)] for row in A] if B else [[] for row in A]
checks=0
for c in d['cases']:
 for tid,t in c['types'].items():
  rows=t['rows'];cols=t['columns'];j=c['root_index'];z=t['pole_bit']
  for x in rows+cols:
   n=x['digit'];l=sum((Q(1,1+m) for m in range(n)),Q(0))-sum((Q(4,j+4*m) for m in range(n+z)),Q(0))
   e=sum((Q(1,(1+m)**2) for m in range(n)),Q(0))-sum((Q(16,(j+4*m)**2) for m in range(n+z)),Q(0))
   assert l==Q(x['L']) and e==Q(x['E'])
  L,Li,Pm,Pi,K=([[Q(x) for x in row] for row in t[k]] for k in ('L','Linv','P','Pinv','K'))
  for A,B in ((L,Li),(Pm,Pi)):
   if A:
    assert mul(A,B)==[[Q(int(i==j)) for j in range(len(A))] for i in range(len(A))]
  if rows and cols:
   red=mul(mul(L,K),Pm)
   assert all(red[i][j]==0 for i in t['killed_rows'] for j in range(len(cols)))
   assert all(red[i][j]==0 for i in range(len(rows)) for j in t['killed_columns'])
  assert [[sum(L[i],Q(0)),sum((v*Q(x['L']) for v,x in zip(L[i],rows)),Q(0))] for i in t['killed_rows']]==[[Q(x) for x in v] for v in t['row_loads']]
  assert [[sum((Pm[i][j] for i in range(len(cols))),Q(0)),sum((Pm[i][j]*Q(cols[i]['L']) for i in range(len(cols))),Q(0))] for j in t['killed_columns']]==[[Q(x) for x in v] for v in t['column_loads']]
  checks+=1
v=json.loads((P/'replay-lambda.json').read_text())['noUF']
lo=2*sum((Q(1,(2*k+1)*3**(2*k+1)) for k in range(25)),Q(0))
hi=lo+Q(2,51)*Q(1,3**51)/(1-Q(1,9))
assert hi<Q(693147181,10**9)
D=Q(14627817894518751186053,3906250000000000000000);C=Q(1438085452130567,200000000000000)
A=Q(v['rational']);B=Q(v['log2']);eta=D-A-B*hi
assert eta>0
mu=C/eta
assert mu<=Q(159693,5000)
r=dict(rank_types_checked=checks,palette_inverse_kernel_load_checks=True,log2_lower=str(lo),log2_upper=str(hi),lambda_rational=str(A),lambda_log2=str(B),mu_upper_exact=str(mu),mu_upper_decimal=str(float(mu)),safe_bound='159693/5000',source_sha256=hashlib.sha256((P/'rank-lambda.json').read_bytes()).hexdigest(),lean_acceptance=False)
(R/'scripts/codex/bank/lambda/local-checks.json').write_text(json.dumps(r,indent=2),encoding='utf-8')
print('Exact local identities:',checks,'; directed no-UF ratio upper:',float(mu))
