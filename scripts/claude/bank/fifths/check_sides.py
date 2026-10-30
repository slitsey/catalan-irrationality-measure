"""Check the side conditions of every generated piece lemma at sampled integers (boundary stress)."""
import sys, json, random
sys.path.insert(0, 'C:/Users/seanl/Documents/Codex/2026-10-11/plea/work/catalan-uniform/scripts/claude/bank/fifths')
from closed import *
from fractions import Fraction as Q
R = 'C:/Users/seanl/Documents/Codex/2026-10-11/plea/work/catalan-uniform/scripts/claude/bank/fifths/'
mode = sys.argv[1] if len(sys.argv) > 1 else 'nouf'
meta = json.load(open(R + ('uf-meta.json' if mode == 'uf' else 'nouf-meta.json')))
random.seed(1)
TEND = Q(63, 10)
bad = 0
def prange(r, a, b):
    lo = (a.numerator * r) // a.denominator + 1
    hi = (b.numerator * r) // b.denominator
    return lo, hi
for jk, c in meta['classes'].items():
    j = int(jk)
    pcs = list(c['pieces']) + [dict(layer='T', left='55/9', right='63/10', line=['0', '0'], meta=dict(kind='D6'))]
    for pc in pcs:
        a, b = Q(pc['left']), Q(pc['right']); lay = pc['layer']; meta_ = pc.get('meta') or {}
        for r in (10**7, 10**7 + 2, 10**7 + 16, 12345678, 123456790, 1234567892):
            m = border(r)
            lo, hi = prange(r, a, b)
            if hi < lo: continue
            pts = set(range(lo, min(hi, lo + 300) + 1)) | set(range(max(lo, hi - 300), hi + 1)) | {random.randint(lo, hi) for _ in range(600)}
            for p in sorted(pts):
                for u in (1, 2, 3, 4):
                    if (j * p + u) % 5: continue
                    k = (j * p + u) // 5
                    if k >= p: continue
                    ok = True; why = ''
                    if lay == 'M3D': ok = m <= p; why = 'm<=p'
                    elif lay == 'T':
                        kd = meta_.get('kind') or 'D6'
                        if kd == 'saw0':
                            q0 = 0; ok = (q0*p <= m < (q0+3)*p)
                        elif kd == 'D3': ok = (0*p <= m < 3*p)
                        elif kd in ('D45', 'D45z'): ok = (r < p and 2*m <= r)
                        else: ok = (r + 2*m <= p and r <= k)
                        why = kd
                    elif lay == 'LP':
                        if b <= 1:
                            ok = (p <= r and r < p + k and r + 2*m <= 2*p and k <= r and 0 < k and k < p and 10 <= p); why = 'LP1'
                        else:
                            if p < r + m: ok = (r < p and r + 2*m <= p + k and k <= r and 0 < k and k < p and 10 <= p)
                            else: ok = (r < p and 2*m <= r)
                            why = 'LP2'
                    elif lay == 'S':
                        cd = meta_['cand']; q = cd['q']
                        okc = candOK(m, r, p, k, cd['kappa'], cd['zeta'])
                        ok = (q*p <= r < (q+1)*p) and 2*m <= p and okc; why = 'S okc=%s' % okc
                    if not ok:
                        bad += 1
                        if bad < 40: print('FAIL', mode, j, lay, meta_.get('kind'), pc['left'], pc['right'], 'r', r, 'p', p, 'u', u, why)
print('mode', mode, 'failures', bad)
