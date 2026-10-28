"""H13: exhaustive coverage check of the Reg families over ALL (r even, p, p%3!=0, 60<=p, band), r<=RMAX."""
import sys, os
sys.dont_write_bytecode = True
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import regs
fams = [regs.Fam(f) for f in regs.load(sys.argv[1])]
rmax = int(sys.argv[2]); bad = []; multi = 0; tot = 0
for r in range(2, rmax + 1, 2):
    for p in range(max(60, (3 * r) // 10 + 1), (39 * r) // 10 + 1):
        if p % 3 == 0 or p % 2 == 0 or not (3 * r < 10 * p <= 39 * r): continue
        tot += 1
        n = sum(1 for F in fams if F.holds(r, p))
        if n == 0: bad.append((r, p))
        if n > 1: multi += 1
print('tot', tot, 'uncovered', len(bad), 'multi', multi)
print(bad[:60])
