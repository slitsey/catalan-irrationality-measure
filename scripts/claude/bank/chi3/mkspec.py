"""Spec file for Gen.lean: receipt cover mapped to edge parameters (odd-grid rounding of interior boundaries)."""
import sys, os
from fractions import Fraction as Fr
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
import gen_bank
d = gen_bank.derive('Chi3')
G = 3 ** 40
def rb(q):
    n = q * G
    return Fr(n.numerator // n.denominator, G)
V = d['poly']['vertices']            # base first
tmax = Fr(13943, 2000)
s = d['poly']['tailSlope']
L = V[-1]
tail_end = (L[0] - tmax, L[1] + s * tmax)
pts = V + [tail_end]
ys = [p[1] for p in pts]
assert ys[-1] == 8
nE = len(pts) - 1                    # 8 edges (7 polygon + tail)
spec = []
# tube: map y-cells to edges; bound = shared interior boundary list per edge
ycuts = {e: [] for e in range(nE)}
for c in d['covers']['ray']:
    a, b = c['a'], c['b']
    for e in range(nE):
        lo, hi = ys[e], ys[e + 1]
        x0, x1 = max(a, lo), min(b, hi)
        if x1 > x0:
            ycuts[e].append((x0, x1))
for e in range(nE):
    lo, hi = ys[e], ys[e + 1]
    cuts = sorted(set([lo, hi] + [p for c in ycuts[e] for p in c]))
    us = [(y - lo) / (hi - lo) for y in cuts]
    us = [u if u in (0, 1) else rb(u) for u in us]
    us = sorted(set(us))
    for a, b in zip(us, us[1:]):
        spec.append(f"T {e} {a.numerator} {a.denominator} {b.numerator} {b.denominator}")
# line
lc = d['covers']['line']
cuts = sorted(set([c['a'] for c in lc] + [c['b'] for c in lc]))
cuts = [u if u in (0, 1) else rb(u) for u in cuts]
cuts = sorted(set(cuts))
for a, b in zip(cuts, cuts[1:]):
    spec.append(f"L {a.numerator} {a.denominator} {b.numerator} {b.denominator}")
# cap
sc = d['covers']['seg']
r0 = d['sc']['r0']
cuts = sorted(set([c['a'] for c in sc] + [c['b'] for c in sc]))
cuts = [u if u in (-r0, 0) else rb(u) for u in cuts]
cuts = sorted(set(cuts))
for a, b in zip(cuts, cuts[1:]):
    spec.append(f"C {a.numerator} {a.denominator} {b.numerator} {b.denominator}")
out = sys.argv[1] if len(sys.argv) > 1 else 'spec.txt'
open(out, 'w').write('\n'.join(spec) + '\n')
print(len(spec), 'cells', sum(1 for x in spec if x[0]=='T'), 'tube', sum(1 for x in spec if x[0]=='L'), 'line', sum(1 for x in spec if x[0]=='C'), 'cap')
