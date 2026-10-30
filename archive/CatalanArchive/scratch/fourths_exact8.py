import sys
sys.path.insert(0, 'scripts/claude/bank/check')
import emit_bank_uf as U
from fractions import Fraction as F
from decimal import Decimal, getcontext
getcontext().prec = 60
name='lambda'; b0=U.BANKS[name]
b=dict(b0,lp2w=True,pre_nmax=8)
lr,ll=U.exact_lam(name,b)
lam=U.dec(lr)+U.dec(ll)*Decimal(2).ln()
mex=U.dec(b0['c'])/(U.dec(b0['D'])-lam)
print('nmax8 mu_ex',mex,flush=True)
for n in (100,120,150,200,300):
    L=U.lam_fin(name,b,n)
    print('n',n,'mu_fin',U.dec(U.mu(b,L)),flush=True)
