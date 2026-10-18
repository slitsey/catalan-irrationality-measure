import sys; sys.set_int_max_str_digits(0)
from mirror2 import *
R='./CatalanLambda/Cert/'
def z(v): return "(%d : ℤ)"%v if v<0 else str(v)
with open(R+'SigmaSorted.lean','w',encoding='utf-8',newline='\n') as f:
    f.write("import CatalanLambda.Cert.RayBox\n\n/-! Generated (gensigma.py): sigma300 sorted by (X,Y); X,Y scaled 2^40, masses n/2^32. -/\nnamespace CatalanLambda.Cert\n\ndef sigmaS : List Pt := [\n"
      + ",\n".join("  (%s, %s, %d)"%(z(X),z(Y),n) for X,Y,n in spts) + "]\n\nend CatalanLambda.Cert\n")
print(len(spts), sum(p[2] for p in spts))
