"""G8f generator: PData (Meta, Cert, CovData) for the verified packet-host checker `checkHost` (Charts6/Check/Host.lean).
usage: gencheck.py KEY            (prints status of the Python mirror of checkHost)
       gencheck.py --emit KEY OUT (writes the Lean instance)
The Python functions mirror the Lean checkers one to one; if the mirror accepts, `decide +kernel` accepts."""
import os, sys, re, json, math
sys.dont_write_bytecode = True
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fractions import Fraction as F
import rowgen as RG, spec as SP

ROOT = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..', '..'))
PKDIR = os.path.join(ROOT, 'CatalanMeasure', 'GenD', 'Uniform', 'Bank532', 'Pk')

# ---------------------------------------------------------------- affine forms (a N + b hp + c)
def aadd(f, g): return (f[0] + g[0], f[1] + g[1], f[2] + g[2])
def asub(f, g): return (f[0] - g[0], f[1] - g[1], f[2] - g[2])
def ascl(k, f): return (k * f[0], k * f[1], k * f[2])
ZERO = (0, 0, 0)
PAFF = (0, 2, 1)
RAFF = (3, 0, 0)
HPA = (0, 1, 0)
def aeval(f, N, hp): return f[0] * N + f[1] * hp + f[2]
def afold(L):
    r = ZERO
    for f in L: r = aadd(r, f)
    return r

# ---------------------------------------------------------------- certificates (Chvatal-Gomory over the window hyps)
def win_hyps(N0, a, b, c, d):
    return [(1, 0, -N0), (-a, 2 * b, b - 1), (d, -2 * c, -c)]

def solutions(vecs, cons, target, limit_c):
    """yield nonneg rational combinations (<=2 vectors) of vecs equal to target with sum lam*cons <= limit_c"""
    n = len(vecs)
    if target == (0, 0):
        yield []
        return
    for i in range(n):
        v = vecs[i]
        if v == (0, 0): continue
        if v[0] * target[1] == v[1] * target[0]:
            lam = F(target[0], v[0]) if v[0] != 0 else F(target[1], v[1])
            if lam > 0 and lam * cons[i] <= limit_c:
                yield [(i, lam)]
    for i in range(n):
        a = vecs[i]
        for j in range(i + 1, n):
            b = vecs[j]
            det = a[0] * b[1] - a[1] * b[0]
            if det == 0: continue
            li = F(target[0] * b[1] - target[1] * b[0], det)
            lj = F(a[0] * target[1] - a[1] * target[0], det)
            if li > 0 and lj > 0 and li * cons[i] + lj * cons[j] <= limit_c:
                yield [(i, li), (j, lj)]

class Cert:
    """Builds a certificate pool.  Each stored entry is (form, steps); steps is the program (list of step tuples)
    ending with a derived form equal to `form`."""
    def __init__(self, win):
        self.win = win
        self.entries = []          # list of (form, steps)
        self.memo = {}
        self.have = {}             # (a,b) -> list of entries
        # basic derived forms: hyps and their tightenings, built as programs
        self.base = []             # (form, program)
        for i, h in enumerate(win):
            self.base.append((h, [('hyp', i)]))
        self._extend()
    def _extend(self):
        # one round of tightening of hyps and small combinations, as programs (programs are self-contained step lists)
        cand = list(self.base)
        for rnd in range(2):
            cur = list(cand)
            for (f1, p1) in cur:
                g = math.gcd(abs(f1[0]), abs(f1[1]))
                if g > 1:
                    f = (f1[0] // g, f1[1] // g, math.floor(F(f1[2], g)))
                    cand.append((f, p1 + [('tighten', g, len(p1) - 1)]))
            for i in range(len(cur)):
                for j in range(i, len(cur)):
                    (f1, p1), (f2, p2) = cur[i], cur[j]
                    for l1 in (1, 2, 3, 4):
                        for l2 in (1, 2, 3, 4):
                            f = aadd(ascl(l1, f1), ascl(l2, f2))
                            g = math.gcd(abs(f[0]), abs(f[1]))
                            if g > 1:
                                prog = self._combine(p1, l1, p2, l2)
                                ft = (f[0] // g, f[1] // g, math.floor(F(f[2], g)))
                                cand.append((ft, prog + [('tighten', g, len(prog) - 1)]))
            # prune: keep best constant per direction, bounded program length
            best = {}
            for (f, p) in cand:
                k = (f[0], f[1])
                if k not in best or f[2] < best[k][0][2] or (f[2] == best[k][0][2] and len(p) < len(best[k][1])):
                    best[k] = (f, p)
            cand = list(best.values())
        self.base = cand
    @staticmethod
    def _combine(p1, l1, p2, l2):
        """program deriving l1*last(p1) + l2*last(p2)"""
        prog = list(p1)
        i1 = len(prog) - 1
        off = len(prog)
        for s in p2:
            prog.append(Cert._shift(s, off))
        i2 = len(prog) - 1
        prog.append(('scale', l1, i1)); a1 = len(prog) - 1
        prog.append(('scale', l2, i2)); a2 = len(prog) - 1
        prog.append(('add', a1, a2))
        return prog
    @staticmethod
    def _shift(s, off):
        if s[0] == 'hyp': return s
        if s[0] == 'tighten': return ('tighten', s[1], s[2] + off)
        if s[0] == 'scale': return ('scale', s[1], s[2] + off)
        if s[0] == 'add': return ('add', s[1] + off, s[2] + off)
        return s
    def prove(self, goal):
        """returns True and registers a certificate if goal >= 0 is provable on the window"""
        if goal in self.memo: return self.memo[goal]
        r = self._prove(goal)
        self.memo[goal] = r
        return r
    def _prove(self, goal):
        k = (goal[0], goal[1])
        for f, st in self.entries:
            if (f[0], f[1]) == k and f[2] <= goal[2]: return True
        if k == (0, 0):
            if goal[2] >= 0:
                self.entries.append(((0, 0, goal[2]), [('const', goal[2])]))
                return True
            return False
        vecs = [(f[0], f[1]) for f, _ in self.base]
        cons = [f[2] for f, _ in self.base]
        best = None
        for sol in solutions(vecs, cons, k, goal[2]):
            D = 1
            for _, lam in sol: D = D * lam.denominator // math.gcd(D, lam.denominator)
            cost = sum(len(self.base[i][1]) for i, _ in sol) + (2 if D > 1 else 0)
            if best is None or cost < best[0]: best = (cost, sol, D)
            if cost <= 4: break
        if best is None: return False
        _, sol, D = best
        prog = []
        idxs = []
        for i, lam in sol:
            off = len(prog)
            for s in self.base[i][1]: prog.append(self._shift(s, off))
            top = len(prog) - 1
            m = int(lam * D)
            if m != 1:
                prog.append(('scale', m, top)); top = len(prog) - 1
            idxs.append(top)
        top = idxs[0]
        for t in idxs[1:]:
            prog.append(('add', top, t)); top = len(prog) - 1
        fa = sum(int(lam * D) * self.base[i][0][0] for i, lam in sol)
        fb = sum(int(lam * D) * self.base[i][0][1] for i, lam in sol)
        fc = sum(int(lam * D) * self.base[i][0][2] for i, lam in sol)
        assert (fa, fb) == (D * k[0], D * k[1])
        if D > 1:
            prog.append(('tighten', D, top))
            fform = (k[0], k[1], math.floor(F(fc, D)))
        else:
            fform = (fa, fb, fc)
        assert fform[2] <= goal[2]
        self.entries.append((fform, prog))
        return True

def lean_step(s):
    if s[0] == 'hyp': return '.hyp %d' % s[1]
    if s[0] == 'add': return '.add %d %d' % (s[1], s[2])
    if s[0] == 'scale': return '.scale %d %d' % (s[1], s[2])
    if s[0] == 'tighten': return '.tighten %d %d' % (s[1], s[2])
    if s[0] == 'const': return '.const %d' % s[1]
    raise ValueError(s)
