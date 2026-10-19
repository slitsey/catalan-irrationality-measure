import json, bisect
from hybmirror import *
OUTD = ROOT + 'outputs/claude-2026-10-16/FX-lean-wp/CERTH/'
A = json.load(open(OUTD + 'A.json')); B = json.load(open(OUTD + 'B.json'))
YEND = A['YEND']; groups = A['groups']
rc = legacy_ray()
ylo = [c[2] for c in rc]; yhi = [c[3] for c in rc]
assert all(ylo[i] <= ylo[i + 1] for i in range(len(ylo) - 1))
assert all(ylo[i + 1] <= yhi[i] for i in range(len(ylo) - 1))
cuts = sorted(set([y for y in ylo if y < YEND] + [g[0] for g in groups] + [YEND]))
assert cuts[0] == 0 and cuts[-1] == YEND
gl = [g[0] for g in groups]
I = []; J = []
for t in range(len(cuts) - 1):
    b0, b1 = cuts[t], cuts[t + 1]
    i = bisect.bisect_right(ylo, b0) - 1
    assert ylo[i] <= b0 and b1 <= yhi[i], t
    j = bisect.bisect_right(gl, b0) - 1
    assert groups[j][0] <= b0 and b1 <= groups[j][1]
    I.append(i); J.append(j)
NR = len(cuts) - 1
print('NR', NR, 'nA', len(groups), 'nB', len(B['groups']), 'maxI', max(I), 'maxJ', max(J))
BIAS = 2 ** 62
by = sum((v + BIAS) << (64 * k) for k, v in enumerate(cuts))
ni = sum(v << (16 * k) for k, v in enumerate(I)); nj = sum(v << (16 * k) for k, v in enumerate(J))
open(ROOT + 'work/catalan-thmA/CatalanCore/Cert/SigmaHyb/RayRef.lean', 'w', encoding='utf-8', newline='\n').write(
 "module\n\n@[expose] public section\n\n/-! Generated (emitref.py): common refinement of the legacy ray cells and the coarse h-cells on y in [0, YEND]. -/\nnamespace CatalanCore.Cert.SigmaHyb\n\n"
 "def NR : Nat := %d\ndef NAH : Nat := %d\ndef NBH : Nat := %d\ndef YENDR : Nat := %d\n\ndef refBY : Nat := %d\ndef refI : Nat := %d\ndef refJ : Nat := %d\n\nend CatalanCore.Cert.SigmaHyb\n" % (NR, len(groups), len(B['groups']), YEND, by, ni, nj))
