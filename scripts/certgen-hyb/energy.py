from hybmirror import *
import json
def iTotL(B, A):
    t = 0
    for p in A:
        row = 0
        for q in B:
            N = (p[0]-q[0])**2 + (p[1]-q[1])**2 + 2**60
            row += q[2] * logLoS(N)
        t += p[2] * row
    return t
if __name__ != "__main__": raise SystemExit
X1 = iTotL(LAM, SIG); X2 = iTotL(LAM, LAM)
IBOUND = F(211073, 100000)
Itot = IBOUND - 2*F(X1, 2**129) - F(X2, 2**129)
print('X1', X1, 'X2', X2, 'cross', float(-F(X1,2**129)), 'll', float(-F(X2,2**129)), 'Itot', float(Itot))
Ib = Itot * F(64, 81)
print('Ibound normalized', float(Ib))
json.dump(dict(X1=str(X1), X2=str(X2)), open(ROOT+'outputs/claude-2026-10-16/FX-lean-wp/CERTH/energy.json','w'))
# D estimate
mp = F(22147,10000); S = F(json.load(open(ROOT+'outputs/claude-2026-10-16/FX-lean-wp/CERTH/S.json'))['Sbase'])
Inu = F(3,2) + F(3,2)*F(1,64) - F(1,64)*0  # placeholder replaced below
import math
Jf = 243/128 - math.log(2)/32 - 25/32*math.log(1.25)
print('Jfun(1/8)', Jf)
D = 2*(float(F(9,8)*mp) + 2*float(S)) - float(F(81,64)*Ib) + Jf
print('D', D, 'c(G=-1.6093)', 2*(2.2147+1.6093))
