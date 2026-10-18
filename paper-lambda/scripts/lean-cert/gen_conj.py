import sys; sys.set_int_max_str_digits(0)
from mirror2 import *
R='./CatalanLambda/Cert/'
idx={}
for k,(X,Y,n) in enumerate(spts): idx.setdefault((X,Y,n),k)
assert len(idx)==300
cj=[idx[(X,-Y,n)] for X,Y,n in spts]
assert all(cj[cj[k]]==k for k in range(300))
mx=max(max(abs(p[0]) for p in spts),max(abs(p[1]) for p in spts))
print("max |coord|/2^40 =",mx/2**40, "min X",min(p[0] for p in spts)/2**40,"max X",max(p[0] for p in spts)/2**40,"maxY",max(p[1] for p in spts)/2**40)
open(R+'ConjData.lean','w',encoding='utf-8',newline='\n').write(
"import CatalanLambda.Cert.Bridge\n\n/-! Generated (gen_conj.py): conjugation involution on the sorted sigma list. -/\nnamespace CatalanLambda.Cert\n\ndef conjIdx : List ℕ := [%s]\n\nend CatalanLambda.Cert\n"%", ".join(map(str,cj)))
