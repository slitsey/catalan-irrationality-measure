import sys
sys.path.insert(0, 'scripts/claude/bank/check')
import emit_bank_uf as U
from decimal import getcontext
getcontext().prec=60
for k in (6,8):
    b=dict(U.BANKS['sevenths'], lp2w=True, pre_nmax=k, target=U.F(2810))
    lr,ll=U.exact_lam('sevenths',b)
    lam=U.dec(lr)+U.dec(ll)*U.Decimal(2).ln()
    mu=U.dec(b['c'])/(U.dec(b['D'])-lam)
    print(k,'mu_ex',mu,flush=True)
    print(k,'choose_n',U.choose_n('sevenths',b),flush=True)
