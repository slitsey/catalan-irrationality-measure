import sys
sys.path.insert(0, 'scripts/claude/bank/check')
import emit_bank_uf as U
from fractions import Fraction as F
from decimal import getcontext
getcontext().prec = 60
name='lambda'; b0=U.BANKS[name]
lean=F(1210311102638262342320035956005798112815887869094387160908759870704652772848920804229732609,344177131462169657795373231423307558604484064066486973702905124405340834755793255170400000)
c=U.lam_fin(name, dict(b0,lp2w=False,pre_nmax=0),100)
print('control exact equal to Lean Lambda:', c==lean, float(lean))
for k in (4,6):
    b=dict(b0,lp2w=True,pre_nmax=k)
    lr,ll=U.exact_lam(name,b)
    from decimal import Decimal
    lam=U.dec(lr)+U.dec(ll)*Decimal(2).ln()
    print(k,'mu_ex',U.dec(b0['c'])/(U.dec(b0['D'])-lam), flush=True)
