import sys
sys.path.insert(0, 'scripts/claude/bank/check')
import emit_bank_uf as U
from decimal import getcontext
getcontext().prec = 60
b0 = U.BANKS['sevenths']
name = 'sevenths'
n = 100
def run(tag, **kw):
    b = dict(b0, **kw)
    lam = U.lam_fin(name, b, n)
    print(tag, kw, 'Lam_fin', float(lam), 'mu', float(U.dec(U.mu(b, lam))), flush=True)
    return lam
lam = run('control', lp2w=False, pre_nmax=0)
open('scratch/sevenths_control_lam.txt', 'w').write(f'{lam.numerator}/{lam.denominator}')
for k in (0, 1, 2, 4, 6, 8):
    run('scan', lp2w=True, pre_nmax=k)
