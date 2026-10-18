import sys, math; sys.set_int_max_str_digits(0)
from mirror2 import *
R='./CatalanLambda/Cert/'
def qII(p,q): return (p[0]-q[0])**2+(p[1]-q[1])**2+2**60
def irow(p): return sum(q[2]*logLoS(qII(p,q)) for q in spts)
CH=30
vals=[]
for r in range(300//CH):
    vals.append(sum(p[2]*irow(p) for p in spts[r*CH:(r+1)*CH]))
tot=sum(vals)
Ival=F(-tot,2**129)
Ib=F(math.ceil(Ival*10**5),10**5)+F(1,10**5)*0   # round up to 1e-5
print(float(Ival),Ib,float(Ib))
txt=["import CatalanLambda.Cert.Bridge\n\n/-! Generated (gen_I.py): I_rho(sigma) upper bound; 300 rows in 10 chunks of 30. -/\nnamespace CatalanLambda.Cert\n\nset_option maxRecDepth 100000\n\n"]
txt.append("""def qII (p q : Pt) : ℕ := (p.1 - q.1).natAbs ^ 2 + (p.2.1 - q.2.1).natAbs ^ 2 + 2 ^ 60

def iRow (p : Pt) : List Pt → ℤ
  | [] => 0
  | q :: qs => (q.2.2 : ℤ) * logLoS (qII p q) + iRow p qs

def iTot : List Pt → ℤ
  | [] => 0
  | p :: ps => (p.2.2 : ℤ) * iRow p sigmaS + iTot ps

def iChunk (r : ℕ) : List Pt := (sigmaS.drop (30 * r)).take 30

""")
for r,v in enumerate(vals):
    txt.append("theorem iChunk_%d : iTot (iChunk %d) = (%d : ℤ) := by decide +kernel\n"%(r,r,v))
txt.append("\ntheorem sigmaS_chunks : sigmaS = %s := by decide +kernel\n"%(" ++ ".join("iChunk %d"%r for r in range(10))))
txt.append("\ndef IBOUND : ℚ := %d / %d\n\nend CatalanLambda.Cert\n"%(Ib.numerator,Ib.denominator))
open(R+'IBoundData.lean','w',encoding='utf-8',newline='\n').write("".join(txt))
