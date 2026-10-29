"""G8f generator part 2: loading a packet and the Python mirror of the Lean checkers (Charts6/Check/*.lean)."""
import os, sys, re, json, math
sys.dont_write_bytecode = True
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fractions import Fraction as F
from gencheck import *
import rowgen as RG, spec as SP

def modname(key): return re.sub(r'[^A-Za-z0-9_]', '_', key.replace('D58-', '').replace('|', '_'))

def parse_rows(text, nm):
    m = re.search(r'def %s : List \(List ℤ\) := \[(.*?)\]\s*\n\s*\n' % re.escape(nm), text, re.S)
    if not m:
        m = re.search(r'def %s : List \(List ℤ\) := \[(.*?)\]\s*\n' % re.escape(nm), text, re.S)
    body = m.group(1)
    return [[int(x) for x in r.split(',')] if r.strip() else [] for r in re.findall(r'raw_ints% \[([^\]]*)\]', body)]

PT = {'-1': 'm1', '0': 'z0', '1': 'p1', 'inf': 'inf'}

class Packet:
    pass

def load(key):
    P = Packet()
    P.key = key
    P.nm = modname(key)
    text = open(os.path.join(PKDIR, P.nm + '.lean'), encoding='utf-8').read()
    P.text = text
    P.n = int(re.search(r'\n  n := (\d+)', text).group(1))
    P.d = int(re.search(r'\n  d := (\d+)', text).group(1))
    m = re.search(r'def Win \(N p : ℕ\) : Prop := (\d+) ≤ N ∧ (\d+) \* N < (\d+) \* p ∧ (\d+) \* p ≤ (\d+) \* N ∧ p % 2 = 1', text)
    P.winp = tuple(int(x) for x in m.groups())   # (N0, a, b, c, d)
    nch = int(re.search(r'theorem pk_len : pk\.charts\.length = (\d+)', text).group(1))
    P.rows = [parse_rows(text, 'chRows%d' % j) for j in range(nch)]
    s, maps = RG.packet_maps(key)
    P.names = s['coordinate_names']
    meta = {g['source_map']: g for g in s['point_chain_metadata']}
    sp = SP.spec(key)
    assert len(sp['maps']) == nch
    P.pts = [PT[str(meta[x['sm']]['point'])] for x in sp['maps']]
    P.ws = []
    for x in sp['maps']:
        w = x['w']
        for kk in w: assert F(w[kk]).denominator == 1
        P.ws.append((int(F(w.get('N', 0))), int(F(w.get('hp', 0))), int(F(w.get('1', 0)))))
    P.labels = [l for g in s['point_chain_metadata'] for l in g['row_labels']]
    P.sp = sp
    names = P.names
    blocks = sorted(set(int(mm.group(1)) for nme in names for mm in [re.match(r'[AC]\[(-?\d+)\]', nme)] if mm))
    assert blocks == list(range(blocks[0], blocks[-1] + 1))
    P.k0 = blocks[0]; P.b = len(blocks)
    P.high = not any(nme == 'left_centre:F' for nme in names)
    P.vlow = any('E_zero' in l for l in P.labels)
    lows = [nme for nme in names if nme.startswith('@low')]
    P.ex = 1 + len(lows)
    P.lows = lows
    io = []
    lowi = 0
    for nme in names:
        mm = re.match(r'([AC])\[(-?\d+)\]:([FE])$', nme)
        if mm:
            k = int(mm.group(2)) - P.k0
            u = {('A', 'F'): 0, ('A', 'E'): 1, ('C', 'F'): 2, ('C', 'E'): 3}[(mm.group(1), mm.group(3))]
            io.append(4 * k + u); continue
        if nme == 'left_centre:F': io.append(4 * P.b); continue
        if nme == 'left_centre:E': io.append(4 * P.b + 1); continue
        if nme == 'jet_0': io.append(4 * P.b + 2); continue
        if nme.startswith('@low'):
            lowi += 1; io.append(4 * P.b + 2 + lowi); continue
        raise ValueError(nme)
    P.iota = io
    i0 = text.index('def cNat')
    seg = text[i0:i0 + 400]
    cl = [ln for ln in seg.split(chr(10)) if ln.strip().endswith('.toNat')][0].strip()
    mc = re.match(r'\((.*)\)\.toNat$', cl)
    cform = {'N': 0, 'hp': 0, '1': 0}
    for term in mc.group(1).split(' + '):
        term = term.strip()
        mm2 = re.match(r'\((-?\d+)\) \* (N|hp)$', term)
        if mm2: cform[mm2.group(2)] += int(mm2.group(1))
        else:
            mm3 = re.match(r'\((-?\d+)\)$', term)
            cform['1'] += int(mm3.group(1))
    P.cm = (cform['N'], cform['hp'], cform['1'])
    assert len(io) == P.n
    return P

class Mirror:
    def __init__(self, P):
        self.P = P
        self.win = win_hyps(*P.winp)
        self.cert = Cert(self.win)
        self.failed = []
        self.fctx = []
    def H(self, goal):
        ok = self.cert.prove(goal)
        if not ok:
            self.failed.append(goal)
        return ok
    def pcOf(self, idx):
        io = self.P.iota
        return io.index(idx) if idx in io else None
    def vecOf(self, ts):
        v = [0] * self.P.n
        for a, idx in ts:
            c = self.pcOf(idx)
            if c is not None: v[c] += a
        return v
    def ptGroups(self, pt): return [g for g, q in enumerate(self.P.pts) if q == pt]
    def lead(self, pt, v):
        out = []
        for g in self.ptGroups(pt):
            if v in self.P.rows[g]: out.append(g)
            else: break
        return out
    def leadAff(self, pt, v): return afold([self.P.ws[g] for g in self.lead(pt, v)])
    def T(self, pt, ts, req):
        self.ctx = ('T', pt, ts, req, self.lead(pt, self.vecOf(ts)))
        r = self.H(asub(self.leadAff(pt, self.vecOf(ts)), req))
        if not r: self.fctx.append(self.ctx)
        return r
    def I(self, ts, lo):
        self.ctx = ('I', 'inf', ts, lo, self.lead('inf', self.vecOf(ts)))
        la = aadd(self.leadAff('inf', self.vecOf(ts)), asub(PAFF, self.P.cm))
        r1 = self.H(asub(la, asub(PAFF, lo)))
        r2 = self.H(asub(PAFF, la))
        if not (r1 and r2): self.fctx.append(self.ctx)
        return r1 and r2
    def ja(self): return (-5, -2 * self.P.k0, -self.P.k0)
    def rho(self): k0, b = self.P.k0, self.P.b; return (53, -2 * (k0 + b - 1), -1 - (k0 + b - 1))
    def geom(self):
        P = self.P
        r = [self.H(self.ja()), self.H(asub(asub(PAFF, (0, 0, 1)), self.ja())), self.H(self.rho()),
             self.H(asub(asub(PAFF, (0, 0, 1)), self.rho())), self.H(asub(PAFF, aadd(RAFF, (0, 0, 1)))),
             P.winp[0] > 0, P.b > 0]
        return all(r)
    def hdom(self):
        P = self.P; b = P.b; high = P.high; vlow = P.vlow
        T, I, H = self.T, self.I, self.H
        lob = asub(RAFF, self.ja()); lot = asub(aadd(RAFF, self.rho()), PAFF)
        res = []
        rh = aadd(RAFF, HPA)
        for k in range(b):
            if high:
                res.append(self.pcOf(4 * k) is None)
                res.append(T('p1', [(1, 4 * k + 1)], asub(rh, PAFF)))
            else:
                res.append(T('p1', [(1, 4 * k)], rh))
            res.append(I([(1, 4 * k + 1)], RAFF))
            res.append(T('p1', [(1, 4 * k + 2)], RAFF))
            res.append(T('m1', [(1, 4 * k + 2), (-2, 4 * k + 3)], HPA))
            res.append(I([(1, 4 * k + 3)], asub(RAFF, (0, 0, 1))))
        if high:
            res.append(self.pcOf(4 * b) is None)
            res.append(T('p1', [(1, 4 * b + 1)], asub(rh, PAFF)))
        else:
            res.append(T('p1', [(1, 4 * b)], rh))
        res.append(I([(1, 4 * b + 1)], RAFF))
        res.append(T('m1', [(1, 4 * b), (-2, 4 * b + 1)], HPA))
        if vlow:
            res.append(T('z0', [(1, 1), (-1, 3), (1, 4 * b + 1)], PAFF))
            res.append(I([(1, 0), (-1, 2), (1, 4 * b)], aadd(lob, PAFF)))
        else:
            res.append(I([(1, 1), (-1, 3), (1, 4 * b + 1)], lob))
        zt = getattr(P, 'top_zero', False)
        if zt:
            res.append(T('z0', [(1, 4 * (b - 1) + 1), (1, 4 * (b - 1) + 3)], PAFF))
            res.append(I([(1, 4 * (b - 1)), (1, 4 * (b - 1) + 2)], aadd(lot, PAFF)))
        else:
            res.append(I([(1, 4 * (b - 1) + 1), (1, 4 * (b - 1) + 3)], lot))
        if not vlow: res.append(H(lob))
        if not zt: res.append(H(lot))
        res.append(H(asub(rh, PAFF)) if high else H(asub(PAFF, aadd(rh, (0, 0, 1)))))
        res.append(H(asub(PAFF, aadd(RAFF, (0, 0, 1)))))
        res.append(H(asub(RAFF, (0, 0, 1))))
        res.append(b > 0)
        return all(res)
    def graph(self):
        return self.T('p1', [(1, 4 * self.P.b + 2)], asub(PAFF, RAFF))
    def basic(self):
        P = self.P
        ok = [len(P.pts) == len(P.rows), len(P.pts) == len(P.ws), P.ex >= 1]
        ok += [self.H(w) for w in P.ws]
        ok.append(self.H((0, 2, -59)))
        ok.append(self.H(P.cm))
        ok.append(self.H(asub(PAFF, P.cm)))
        return all(ok)

def all_keys():
    sel = json.load(open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'sel532.json')))
    return sorted(set(k for g, k, *_ in sel))

if __name__ == '__main__' and len(sys.argv) > 1 and sys.argv[1] == '--mirror':
    keys = sys.argv[2:] or all_keys()
    for key in keys:
        try:
            P = load(key)
            M = Mirror(P)
            r = dict(basic=M.basic(), geom=M.geom(), hdom=M.hdom(), graph=M.graph())
            print(key, 'b=%d k0=%d ex=%d high=%s vlow=%s' % (P.b, P.k0, P.ex, P.high, P.vlow), r, 'fail:', M.fctx[:2])
        except Exception as e:
            print(key, 'ERR', repr(e)[:300])
