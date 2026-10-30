import sys, re
sys.path.insert(0, 'scripts/claude/bank/check')
import emit_bank_uf as U
from fractions import Fraction as F
s=open('CatalanCore/Uniform/Bank/SeventhsContent/AutoData.lean').read()
m=re.search(r'Λ := qq (\d+) (\d+)',s); L=F(int(m[1]),int(m[2]))
b=dict(U.BANKS['sevenths'], lp2w=False, pre_nmax=0)
lo,hi=150,1000
while hi-lo>1:
    mid=(lo+hi)//2
    lam=U.lam_fin('sevenths',b,mid); print(mid,float(lam),lam==L,flush=True)
    if lam==L: break
    if lam>L: lo=mid
    else: hi=mid
