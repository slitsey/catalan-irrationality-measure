"""H13 task (c): what the missing top extension would gain, evaluated on the Lean prices (no Lean needed).
For a family window [t0=r, tv] the extension [lo, r-1], lo = max((jm-1)p, P1-p, tv+1-p, r+2m-p), adds e = r-lo residues to u
(valid when lo <= r-1): base3X = 2(r+m) - (m + sg + (sg - (p-u-e))).
Usage: topext.py FAMS.json RMAX"""
import sys, os, random
sys.dont_write_bytecode = True
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import regs, plan as P
fj = regs.load(sys.argv[1]); fams = [regs.Fam(f) for f in fj]
rmax = int(sys.argv[2]); random.seed(3)
def nsub(a, b): return max(a - b, 0)
def base3x(m, r, p, t0, tv, e):
    Lb = nsub(min(tv + 1, r + 2 * m), t0); sg = nsub(Lb, m)
    u = nsub(tv + 1, t0) + nsub(nsub(2 * m, Lb), 1) + e
    return nsub(2 * (r + m), m + sg + nsub(sg, nsub(p, u)))
gl = []; tot = 0; sg_old = 0; sg_new = 0; worst = (0, None); n_ext = 0; byf = {}
for r in range(200, rmax, 2):
    lo_p, hi_p = max(60, 3 * r // 10 + 1), 39 * r // 10
    for _ in range(40):
        p = random.randint(lo_p, hi_p)
        if p % 2 == 0 or p % 3 == 0 or not P.isprime(p): continue
        for k, Fm in enumerate(fams):
            if Fm.holds(r, p): break
        else: continue
        F = fj[k]; run = F['D']['runs'][F['w']]
        env = dict(r=r, p=p)
        t0 = eval(compile(regs.pyexpr(run['start']), 'a', 'eval'), {}, env); tv = eval(compile(regs.pyexpr(run['end']), 'a', 'eval'), {}, env)
        m = (3 * r + 9) // 20
        old = P.base3_exact(m, r, p, t0, tv)
        new = old
        if t0 == r:
            rho, jm, j1, br, meets = F['key']
            P1 = (j1 * p + 2) // 3
            lo = max((jm - 1) * p, P1 - p, tv + 1 - p, r + 2 * m - p, 0)
            if lo <= r - 1:
                new = min(old, base3x(m, r, p, t0, tv, r - lo)); n_ext += 1
        tot += 1; sg_old += old / r; sg_new += new / r; gl.append((old - new) / r)
        if (old - new) / r > worst[0]: worst = ((old - new) / r, (r, p, old, new))
gains = sorted(gl)
print("points", tot, "with ext", n_ext, "mean price/r old", sg_old / tot, "new", sg_new / tot, "mean gain/r", (sg_old - sg_new) / tot, "worst", worst)
print("share gain>0.001r", sum(1 for g in gl if g > 0.001) / tot, ">0.01r", sum(1 for g in gl if g > 0.01) / tot, ">0.05r", sum(1 for g in gl if g > 0.05) / tot)
