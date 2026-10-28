"""H12 planner: exact combinatorics of the thirds UF window cells.

q=3, o=2.  For (r even, p prime, p>=P0) the border is [r, N0), m=(3r+9)//20, N0=r+2m.
The singular indices of [r, r+p) are exactly M1 = jm*p (multiple) and P1 = (j1*p+2)/3 (pole, j1 = rho mod 3).
Runs: R0=[r,s1-1], R1=[st1,s2-1], R2=[st2,r+p-1] (s1<s2 the two singular indices, st = s (pole) or s+1 (multiple)).
A window cell = one run Rk as J-window [t0=start, tv=end], kills of all other border nodes (not multiples of p).
The start type of a run: pole j -> (A,B)=((j-rho)//3, j); multiple jp -> start jp+1: (j, 3j); r -> (r//p,(3r-2)//p).
"""
import sys, itertools, json
from fractions import Fraction as F

sys.path.insert(0, 'C:/Users/seanl/Documents/Codex/2026-10-11/plea/outputs/Compatibility programme/lean-plan-2026-10-27/evidence/claude/H11/py')
import ufcore as C

Q, O = 3, 2

def isprime(n):
    if n < 2: return False
    i = 2
    while i * i <= n:
        if n % i == 0: return False
        i += 1
    return True

def msize(r): return (3 * r + 9) // 20

def run_structure(r, p):
    """returns dict with jm, j1, order, runs (list of (kind, start, end, startType)), N0, m."""
    rho = p % 3
    jm = (r - 1) // p + 1
    M1 = jm * p
    j1 = ((3 * r - 2 + p - 1) // p)          # ceil((3r-2)/p)
    while j1 % 3 != rho: j1 += 1
    P1 = (j1 * p + 2) // 3
    assert (j1 * p + 2) % 3 == 0 and r <= P1 < r + p and r <= M1 < r + p, (r, p, M1, P1)
    sings = sorted([(M1, 'M', jm), (P1, 'P', j1)])
    m = msize(r); N0 = r + 2 * m
    starts = []
    # run 0
    s1, k1, j_1 = sings[0]; s2, k2, j_2 = sings[1]
    runs = []
    # R0
    runs.append(dict(idx=0, start=r, end=s1 - 1, stype=(r // p, (3 * r - 2) // p), lab='r'))
    def st(s, k, j):
        if k == 'P': return s, ((j - p % 3) // 3, j)
        return s + 1, (j, 3 * j)
    a, ty = st(s1, k1, j_1)
    runs.append(dict(idx=1, start=a, end=s2 - 1, stype=ty, lab=(k1, j_1)))
    a, ty = st(s2, k2, j_2)
    runs.append(dict(idx=2, start=a, end=r + p - 1, stype=ty, lab=(k2, j_2)))
    return dict(rho=rho, jm=jm, j1=j1, order=''.join(s[1] for s in sings), runs=runs, N0=N0, m=m, s=(s1, s2), kinds=(k1, k2), js=(j_1, j_2))

_sig = {}
def sig(rho, A, B):
    key = (rho, A, B)
    if key in _sig: return _sig[key]
    nodes = [(A - j, B - 3 * j) for j in range(1, A + 1)]
    items = tuple((a1 - A, C.cval(1, Q, O, rho, a1, a2), C.cval(2, Q, O, rho, a1, a2)) for a1, a2 in nodes)
    s = (items, C.cval(1, Q, O, rho, A, B))
    _sig[key] = s
    return s

def base3(m, r, p, t0, tv):
    Lb = max(min(tv + 1, r + 2 * m) - t0, 0)
    sg = max(Lb - m, 0)
    u = max(tv + 1 - t0, 0) + max(2 * m - Lb - 1, 0)
    return 2 * (r + m) - (m + sg + max(sg - max(p - u, 0), 0)) if True else 0

def nsub(a, b): return max(a - b, 0)

def base3_exact(m, r, p, t0, tv):
    Lb = nsub(min(tv + 1, r + 2 * m), t0)
    sg = nsub(Lb, m)
    u = nsub(tv + 1, t0) + nsub(nsub(2 * m, Lb), 1)
    return nsub(2 * (r + m), m + sg + nsub(sg, nsub(p, u)))

def analyse(r, p):
    S = run_structure(r, p)
    m, N0, rho = S['m'], S['N0'], S['rho']
    runs = S['runs']
    # which runs meet the border (nonempty intersection with [r,N0), start<=end)
    meets = []
    for R in runs:
        a, b = R['start'], R['end']
        meets.append(a <= b and a < N0)
    # window candidates: runs meeting the border with start non-multiple
    cands = []
    for i, R in enumerate(runs):
        if not meets[i]: continue
        t0, tv = R['start'], R['end']
        # feasibility: every other run meeting the border has different signature
        J = sig(rho, *R['stype'])
        ok = all(sig(rho, *runs[k]['stype']) != J for k in range(3) if k != i and meets[k])
        cands.append(dict(i=i, t0=t0, tv=tv, ok=ok, base=base3_exact(m, r, p, t0, tv)))
    return S, meets, cands

def key_of(S, meets):
    return (S['rho'], S['jm'], S['j1'], tuple(meets))

if __name__ == '__main__':
    import collections
    polys = collections.OrderedDict()
    P0 = int(sys.argv[1]) if len(sys.argv) > 1 else 40
    rmax = int(sys.argv[2]) if len(sys.argv) > 2 else 3000
    for r in range(200, rmax, 2):
        for p in range(max(P0, int(0.299 * r)), int(3.95 * r) + 1):
            if not isprime(p) or p < 5: continue
            S, meets, cands = analyse(r, p)
            k = key_of(S, meets)
            e = polys.setdefault(k, dict(n=0, best=collections.Counter(), pmin=10**9, order=S['order'], ex=None))
            e['n'] += 1
            feas = [c for c in cands if c['ok']]
            if feas:
                b = min(feas, key=lambda c: (c['base'], c['i']))
                e['best'][b['i']] += 1
            else:
                e['best'][-1] += 1
            if e['ex'] is None: e['ex'] = (r, p)
    print(len(polys), 'polygons')
    for k, e in sorted(polys.items()):
        print(k, e['order'], e['n'], dict(e['best']), e['ex'])

