"""G8f generator part 4: regions (unique graph), zones (cover), PData assembly, Lean emission.
usage:  gencheck4.py --check KEY...     mirror + regions + zones, report
        gencheck4.py --emit KEY OUTDIR   write the Lean instance file"""
import os, sys, re, json, math, itertools, time
sys.dont_write_bytecode = True
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fractions import Fraction as F
from gencheck import *
from gencheck2 import *
from gencheck3 import *
import rowgen as RG

def kinds(P):
    labs = P.labels
    P.bot_zero = any(l.startswith('bottom_virtual:E_zero') for l in labs)
    P.top_zero = any(l.startswith('top_virtual:E_zero') for l in labs)
    P.vlow = P.bot_zero
    return (P.high, P.bot_zero, P.top_zero)

SUPPORTED = {(h, b, t) for h in (True, False) for b in (True, False) for t in (True, False)}

class Gen:
    def __init__(self, key, winp=None):
        self.key = key
        self.P = load(key)
        if winp is not None: self.P.winp = tuple(winp)
        self.kind = kinds(self.P)
        self.M = Mirror(self.P)
        self.prof = ProfK(self.P.k0, self.P.b)
        self.samples = self._samples()
        self.errors = []
        P = self.P
        self.cj = P.iota.index(4 * P.b + 2)
        self.ec = [P.iota.index(4 * P.b + 2 + j) for j in range(P.ex)]
    # ---------------------------------------------------------- window samples
    def _samples(self):
        N0, a, b, c, d = self.P.winp
        pts = []
        for N in (N0, N0 + 7, 3 * N0, 20 * N0, 200 * N0):
            lo = (a * N) // b + 1
            hi = (d * N) // c
            if hi < lo: continue
            for fr in (0.02, 0.5, 0.98):
                p = lo + int((hi - lo) * fr)
                if p % 2 == 0: p += 1 if p + 1 <= hi else -1
                if p < lo or p > hi or p % 2 == 0: continue
                hp = (p - 1) // 2
                if all(aeval(h, N, hp) >= 0 for h in self.M.win):
                    pts.append((N, hp))
        assert pts, 'no sample points'
        return pts
    def val(self, f): return tuple(aeval(f, N, hp) for N, hp in self.samples)
    def H(self, goal): return self.M.cert.prove(goal)
    # ---------------------------------------------------------- group geometry
    def off(self, g):
        P = self.P
        gs = [h for h in range(len(P.pts)) if P.pts[h] == P.pts[g]]
        base = asub(PAFF, P.cm) if P.pts[g] == 'inf' else ZERO
        return aadd(base, afold([P.ws[h] for h in gs[:gs.index(g)]]))
    def actrange(self, g):
        pt = self.P.pts[g]
        o = self.off(g); w = self.P.ws[g]
        if pt == 'z0': return (o, aadd(o, w))
        if pt == 'inf': return (asub(asub(PAFF, o), w), asub(PAFF, o))
        return None
    def active(self, g, lo, hi):
        r = self.actrange(g)
        if r is None: return False
        return self.H(asub(lo, r[0])) and self.H(asub(r[1], hi))
    # ---------------------------------------------------------- breakpoints
    def segments(self, L, Pp, bps):
        """ordered boundary list L = s0 <= s1 <= ... <= Pp (all provably ordered), from candidate forms bps"""
        cand = []
        seen = set()
        for b in bps:
            if b in seen: continue
            seen.add(b)
            if b == L or b == Pp: continue
            if self.H(asub(b, L)) and self.H(asub(Pp, b)): cand.append(b)
        cand.sort(key=self.val)
        out = [L]
        for b in cand:
            if self.val(b) == self.val(out[-1]) and not self.H(asub(b, out[-1])): continue
            if not self.H(asub(b, out[-1])):
                self.errors.append(('unordered', out[-1], b)); continue
            out.append(b)
        if not self.H(asub(Pp, out[-1])): self.errors.append(('end', out[-1], Pp))
        out.append(Pp)
        return list(zip(out[:-1], out[1:]))
    # ---------------------------------------------------------- unique-graph regions
    def region_sel(self, a, b):
        P = self.P
        act = [g for g in range(len(P.pts)) if P.pts[g] in ('z0', 'inf') and self.active(g, a, b)]
        cands = {}
        for g in act:
            for i, r in enumerate(P.rows[g]):
                v = tuple(r[c] for c in self.ec)
                if all(x == 0 for x in v): continue
                if v not in cands: cands[v] = (g, i)
        vecs = list(cands.items())
        ex = P.ex
        best = None
        for combo in itertools.combinations(range(len(vecs)), ex):
            M = [list(vecs[k][0]) for k in combo]
            d = detm(M)
            if smooth(d):
                if best is None or abs(d) < best[0]: best = (abs(d), combo)
        if best is None: return None
        return [vecs[k][1] for k in best[1]]
    def regions(self):
        P = self.P
        bps = []
        for g in range(len(P.pts)):
            r = self.actrange(g)
            if r: bps += [r[0], r[1]]
        segs = self.segments(ZERO, P.cm, bps)
        out = []
        for (a, b) in segs:
            if a == b: continue
            sel = self.region_sel(a, b)
            if sel is None:
                self.errors.append(('noregion', a, b)); return None
            if out and set(out[-1][2]) == set(sel) and all(self.active(g, out[-1][0], b) for g, _ in sel):
                out[-1] = (out[-1][0], b, out[-1][2])
            else:
                out.append((a, b, sel))
        return out
    # ---------------------------------------------------------- cover parameters
    def cover_params(self):
        P = self.P
        S0s = set(((78 * N - 1) // (2 * hp + 1)) for N, hp in self.samples)
        if len(S0s) != 1:
            self.errors.append(('S0 not constant', S0s)); return None
        S0 = S0s.pop()
        if not (self.H((78, -2 * S0, -S0 - 1)) and self.H((-78, 2 * (S0 + 1), S0 + 1))):
            self.errors.append(('S0 unprovable', S0)); return None
        Jlo = min((9 * N) // (2 * hp + 1) for N, hp in self.samples)
        while Jlo > 0 and not self.H((9, -2 * Jlo, -Jlo)): Jlo -= 1
        Jb = max(-((-70 * N) // (2 * hp + 1)) for N, hp in self.samples)
        while not self.H((-70, 2 * Jb, Jb)): Jb += 1
        if not (self.H((78, 0, -(S0 + 3))) and self.H(ZERO)):
            self.errors.append(('w5',)); return None
        return S0, Jlo, Jb
    # ---------------------------------------------------------- psi rows
    def psi_rows(self, Z, J, S):
        """all (g,i,eps) with rowOKg true"""
        P = self.P; b = P.b; cj = self.cj
        psi = {}
        for c in range(P.n):
            k = P.iota[c]
            if k < 4 * b + 2: psi[c] = rowInt(self.prof, Z, J, S, k)
        for j in range(P.ex):
            if rowInt(self.prof, Z, J, S, 4 * b + 2 + j) != 0: return []
        out = []
        for g in range(len(P.pts)):
            if P.pts[g] not in ('z0', 'inf'): continue
            for i, r in enumerate(P.rows[g]):
                rj = r[cj]
                if not (rj < 0 and SMOOTH % (-rj) == 0): continue
                eps = []
                ok = True
                for j in range(P.ex):
                    x = r[self.ec[j]]
                    if x % rj != 0: ok = False; break
                    eps.append(x // rj)
                if not ok: continue
                if all(r[c] * Z == -rj * psi[c] for c in psi):
                    out.append((g, i, eps))
        return out
    def unit_row(self, g, j):
        P = self.P
        u = [1 if k == self.ec[j] else 0 for k in range(P.n)]
        for i, r in enumerate(P.rows[g]):
            if r == u: return i
        return None
    def zones(self, Z, J, S, L, Pp):
        P = self.P
        rows = self.psi_rows(Z, J, S)
        if not rows:
            self.errors.append(('norows', J, S)); return None
        groups = sorted(set(g for g, _, _ in rows))
        # killer groups: any z0/inf group
        bps = []
        for g in range(len(P.pts)):
            r = self.actrange(g)
            if r: bps += [r[0], r[1]]
        segs = self.segments(L, Pp, bps)
        out = []
        for (a, b) in segs:
            if a == b: continue
            cand = None
            for (g, i, eps) in rows:
                if not self.active(g, a, b): continue
                need = [j for j in range(1, P.ex) if eps[j] != 0]
                g2s = [g] + [h for h in range(len(P.pts)) if h != g and P.pts[h] in ('z0', 'inf')]
                for g2 in g2s:
                    if not self.active(g2, a, b): continue
                    kill = [0] * P.ex
                    ok = True
                    for j in need:
                        ki = self.unit_row(g2, j)
                        if ki is None: ok = False; break
                        kill[j] = ki
                    if ok:
                        cand = (g, i, g2, eps, kill); break
                if cand: break
            if cand is None:
                self.errors.append(('nozone', J, S, a, b)); return None
            if out and out[-1][2:] == cand and self.active(cand[0], out[-1][0], b) and self.active(cand[2], out[-1][0], b):
                out[-1] = (out[-1][0], b) + cand
            else:
                out.append((a, b) + cand)
        return out
    def cover(self):
        cp = self.cover_params()
        if cp is None: return None
        S0, Jlo, Jb = cp
        Z = Zmom(S0 + 3, Jb)
        assert SMOOTH % Z == 0
        T = (78, -2 * S0, -S0)
        hiZ, loZ, hiB, loB = [], [], [], []
        for J in range(Jlo, Jb):
            d = J - S0
            for side in (0, 1):
                if side == 0:
                    L0, Lc, P0, Pc, S = ZERO, (8, 2 * d, d), T, (69, 2 * d, d), S0
                else:
                    L0, Lc, P0, Pc, S = T, (8, 2 * d + 2, d + 1), PAFF, (69, 2 * d + 2, d + 1), S0 - 1
                lo = Lc if self.H(asub(Lc, L0)) else L0
                hi = Pc if self.H(asub(P0, Pc)) else P0
                if self.H(asub(hi, self.P.cm)): hi = self.P.cm
                if self.H(asub(lo, hi)):
                    zs = []
                else:
                    zs = self.zones(Z, J, S, lo, hi)
                    if zs is None: return None
                (hiZ if side == 0 else loZ).append(zs)
                (hiB if side == 0 else loB).append((lo, hi))
        Ub = S0 + 3
        AT = [[qscale(alphaQ(u, J), Z) for u in range(Ub)] if J >= Jlo else [] for J in range(Jb)]
        BT = [[qscale(betaQ(u, J), Z) for u in range(Ub)] if J >= Jlo else [] for J in range(Jb)]
        return dict(S0=S0, Jlo=Jlo, Z=Z, hiZ=hiZ, loZ=loZ, hiB=hiB, loB=loB, AT=AT, BT=BT)

def detm(M):
    n = len(M)
    if n == 1: return M[0][0]
    if n == 2: return M[0][0] * M[1][1] - M[0][1] * M[1][0]
    if n == 3:
        return (M[0][0] * (M[1][1] * M[2][2] - M[1][2] * M[2][1]) - M[0][1] * (M[1][0] * M[2][2] - M[1][2] * M[2][0])
                + M[0][2] * (M[1][0] * M[2][1] - M[1][1] * M[2][0]))
    raise ValueError

def check(key, winp=None):
    g = Gen(key, winp)
    P = g.P
    res = dict(kind=g.kind)
    if g.kind not in SUPPORTED:
        res['skip'] = 'unsupported kind'
        return g, res
    M = g.M
    res['basic'] = M.basic(); res['geom'] = M.geom(); res['hdom'] = M.hdom(); res['graph'] = M.graph()
    if not all(res[k] for k in ('basic', 'geom', 'hdom', 'graph')): return g, res
    t = time.time()
    regs = g.regions()
    res['regions'] = None if regs is None else len(regs)
    g.regs = regs
    cov = g.cover() if regs is not None else None
    res['cover'] = None if cov is None else (cov['S0'], cov['Jlo'], len(cov['hiZ']), sum(len(z) for z in cov['hiZ']), sum(len(z) for z in cov['loZ']))
    g.cov = cov
    res['t'] = round(time.time() - t, 1)
    res['errors'] = g.errors[:3]
    return g, res

def split_check(key, winp=None, depth=0):
    """list of (g, res) covering the window; splits at the crossing of unordered breakpoints"""
    g, res = check(key, winp)
    if res.get('cover') is not None or res.get('skip') or not all(res.get(k) for k in ('basic', 'geom', 'hdom', 'graph')):
        return [(g, res)]
    un = [e for e in g.errors if e[0] == 'unordered']
    if not un or depth >= 2: return [(g, res)]
    a, b = un[0][1], un[0][2]
    dn, dhp = a[0] - b[0], a[1] - b[1]
    if dhp == 0: return [(g, res)]
    r = F(-2 * dn, dhp)
    N0, a0, b0, c0, d0 = g.P.winp
    if not (F(a0, b0) < r < F(d0, c0)): return [(g, res)]
    num, den = r.numerator, r.denominator
    w1 = (N0, a0, b0, den, num)
    w2 = (N0, num, den, c0, d0)
    return split_check(key, w1, depth + 1) + split_check(key, w2, depth + 1)

if __name__ == '__main__' and len(sys.argv) > 1 and sys.argv[1] == '--check':
    keys = sys.argv[2:] or [k for k in all_keys() if 'L0146' not in k]
    for key in keys:
        try:
            g, res = check(key)
            print(key, res, flush=True)
        except Exception as e:
            import traceback
            print(key, 'ERR', repr(e)[:300], flush=True)
            traceback.print_exc()
