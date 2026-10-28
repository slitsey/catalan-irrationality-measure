"""H12 translator: thirds UF window cells -> Lean (UFFamily3) data + families.

Usage (python -I):  gen.py plan  OUT.json [RMAX]          sample the domain, build the family list
                    gen.py emit  OUT.json OUTDIR [--per N] write Lean modules
The families are exact polygons {(r,p)} of the (r,p)-plane (integer linear inequalities with one
floor, m=(3r+9)//20): the singular indices M1=jm*p, P1=(j1*p+2)/3 of [r,r+p), the border position
of the three runs R0,R1,R2, and the floor b_r=(3r-2)//p when R0 meets the border.  A family is a
polygon together with the run chosen as J-window (best base3 price among feasible runs).
Types (A,B) at run starts are polygon constants; LU data for ordered pairs (J,K) of start types.
"""
import sys, os, json, collections
sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import plan as P
C = P.C
Q, O = 3, 2
P0 = 60
PRIMES60 = [p for p in range(2, 60) if P.isprime(p)]
LPRIM = 1
for _p in PRIMES60: LPRIM *= _p


def structure(r, p):
    """polygon key + per-run data at (r,p)."""
    S = P.run_structure(r, p)
    m, N0, rho = S['m'], S['N0'], S['rho']
    runs = S['runs']
    meets = tuple(bool(R['start'] <= R['end'] and R['start'] < N0) for R in runs)
    br = (3 * r - 2) // p if meets[0] else None
    key = (rho, S['jm'], S['j1'], br, meets)
    return S, key, meets


def run_descr(S, rho, jm, j1):
    """symbolic run descriptions (strings), types, kinds for a polygon (from a sample S)."""
    M = f"{jm}*p"; Pp = f"({j1}*p+2)/3"
    sing = sorted([(S['s'][0], S['kinds'][0], S['js'][0]), (S['s'][1], S['kinds'][1], S['js'][1])])
    def sx(k): return M if k == 'M' else Pp
    def stx(k): return f"({M}+1)" if k == 'M' else f"({Pp})"
    s1, s2 = sing[0], sing[1]
    S1, S2 = f"({sx(s1[1])})", f"({sx(s2[1])})"
    ST1, ST2 = stx(s1[1]), stx(s2[1])
    runs = [dict(start='r', end=f"({S1}-1)", kind='r'),
            dict(start=ST1, end=f"({S2}-1)", kind=s1[1]),
            dict(start=ST2, end="(r+p-1)", kind=s2[1])]
    return dict(S1=S1, S2=S2, ST1=ST1, ST2=ST2, runs=runs, kinds=(s1[1], s2[1]))


def plan(rmax):
    polys = collections.OrderedDict()
    def sweep(rs):
        for r in rs:
            pmin = max(P0, (3 * r) // 10 + 1)
            for p in range(pmin, (39 * r) // 10 + 1):
                if not P.isprime(p): continue
                S, key, meets = structure(r, p)
                m, N0, rho = S['m'], S['N0'], S['rho']
                runs = S['runs']
                cands = []
                for i, R in enumerate(runs):
                    if not meets[i]: continue
                    J = P.sig(rho, *R['stype'])
                    ok = all(P.sig(rho, *runs[k]['stype']) != J for k in range(3) if k != i and meets[k])
                    cands.append(dict(i=i, ok=ok, base=P.base3_exact(m, r, p, R['start'], R['end'])))
                feas = [c for c in cands if c['ok']]
                e = polys.setdefault(key, dict(n=0, best=collections.Counter(), feas=None, ex=None, order=S['order'],
                                               types=None, blocks=None, bad=0))
                e['n'] += 1
                if e['ex'] is None: e['ex'] = (r, p)
                fi = tuple(c['i'] for c in feas)
                if e['feas'] is None: e['feas'] = fi
                elif e['feas'] != fi: e['bad'] += 1
                ty = tuple(R['stype'] for R in runs)
                bl = tuple((R['start'] // p, R['end'] // p) if R['start'] <= R['end'] else None for R in runs)
                if e['types'] is None: e['types'] = ty; e['blocks'] = bl
                else:
                    for k in range(3):
                        if meets[k] and (e['types'][k] != ty[k] or e['blocks'][k] != bl[k]): e['bad'] += 1
                if feas:
                    b = min(feas, key=lambda c: (c['base'], c['i']))
                    e['best'][b['i']] += 1
                else:
                    e['best'][-1] += 1
    sweep(range(100, 1200, 2))
    sweep(range(1200, rmax, 26))
    return polys


def families(polys):
    fams = []
    for key, e in sorted(polys.items(), key=lambda kv: str(kv[0])):
        rho, jm, j1, br, meets = key
        S, _, _ = structure(*e['ex'])
        D = run_descr(S, rho, jm, j1)
        for w, cnt in sorted(e['best'].items()):
            if w < 0:
                fams.append(dict(key=list(key), w=-1, infeasible=True, n=cnt)); continue
            fams.append(dict(key=list(key), w=w, n=cnt, feas=list(e['feas']), order=e['order'], D=D,
                             types=[list(t) for t in e['types']], blocks=[list(b) if b else None for b in e['blocks']],
                             bad=e['bad'], ex=list(e['ex'])))
    return fams


# ---------------------------------------------------------------- pairs / LU data
def smooth_exp(g):
    g = abs(g)
    if g == 0: return None
    E = 0
    L = 1
    while L % g != 0:
        L *= LPRIM; E += 1
        if E > 60: return None
    return E


def mkdata(rho, A, B, u0):
    J = C.fam_type(Q, A, B, 1, A)
    Dn = C.min_dn(Q, O, rho, P.F(1), u0, J)
    X = C.lu_record(Q, O, rho, P.F(1), u0, J, Dn)
    return Dn, X


def egcd(a, b):
    if b == 0: return (a, 1, 0) if a >= 0 else (-a, -1, 0)
    g, x, y = egcd(b, a % b)
    return g, y, x - (a // b) * y


def pair_plan(rho, J, K):
    """choose evaluation point(s): ('single', u0, cross, E) or ('bez', ua, ub, ca, cb, x, y, g, E)."""
    data = {}
    for u0 in range(2, 40):
        try:
            data[u0] = (mkdata(rho, J[0], J[1], u0), mkdata(rho, K[0], K[1], u0))
        except Exception:
            continue
    cross = {u: C.cross(d[0][1], d[1][1]) for u, d in data.items()}
    for u in sorted(cross):
        c = cross[u]
        if c != 0 and smooth_exp(c) is not None:
            return ('single', u, c, smooth_exp(c)), data
    us = sorted(cross)
    for i, ua in enumerate(us):
        for ub in us[i + 1:]:
            ca, cb = cross[ua], cross[ub]
            if ca == 0 and cb == 0: continue
            g, x, y = egcd(ca, cb)
            E = smooth_exp(g)
            if E is not None:
                return ('bez', ua, ub, ca, cb, x, y, g, E), data
    raise ValueError('no certificate for %s %s %s' % (rho, J, K))


# ---------------------------------------------------------------- Lean emission
def ints_mat(M): return '[' + ', '.join('[' + ', '.join(str(x) for x in r) + ']' for r in M) + ']'


class Data:
    def __init__(self):
        self.lu = {}       # record key -> name
        self.lines = []
        self.ok = set()
        self.pairs = {}
    def lu_name(self, rho, X):
        key = (rho, tuple(map(str, [X['LM'], X['UM'], X['LA'], X['UA'], X['LB'], X['UB'], X['a'], X['b']])))
        if key not in self.lu:
            nm = 'lu%d_%d' % (rho, len(self.lu))
            self.lu[key] = nm
            self.lines.append(f"def {nm} : LuData where\n  LM := {ints_mat(X['LM'])}\n  UM := {ints_mat(X['UM'])}\n"
                              f"  LA := {ints_mat(X['LA'])}\n  UA := {ints_mat(X['UA'])}\n  LB := {ints_mat(X['LB'])}\n"
                              f"  UB := {ints_mat(X['UB'])}\n  a := {X['a']}\n  b := {X['b']}\n")
        return self.lu[key]
    def typ(self, rho, A, B, u0, d):
        """emit IntOK/ok theorems for type (A,B) at u0; returns (luname)"""
        Dn, X = d
        nm = self.lu_name(rho, X)
        key = (rho, A, B, u0)
        if key not in self.ok:
            self.ok.add(key)
            ty = f"(famType 3 {A} {B} 1 {A})"
            self.lines.append(f"theorem intOK_{rho}_{A}_{B}_{u0} : IntOK 3 2 {rho} (1 : ℚ) {u0} {ty} {Dn} := by decide +kernel")
            self.lines.append(f"theorem ok_{rho}_{A}_{B}_{u0} : {nm}.ok {ty}.nodes.length (mkFib 3 2 {rho} (1 : ℚ) {u0} {ty} {Dn}) {Dn} = true := by\n  decide +kernel")
        return nm, Dn
    def pair(self, rho, J, K):
        key = (rho, tuple(J), tuple(K))
        if key in self.pairs: return self.pairs[key]
        pl, data = pair_plan(rho, J, K)
        name = 'pair_%d_%d_%d_%d_%d' % (rho, J[0], J[1], K[0], K[1])
        tJ, tK = f"(famType 3 {J[0]} {J[1]} 1 {J[0]})", f"(famType 3 {K[0]} {K[1]} 1 {K[0]})"
        head = (f"theorem {name} {{Fr : Frame}} {{p : ℕ}} [Fact p.Prime] (hp3 : p % 3 = {rho}) (hp : 60 ≤ p) (hn : Fr.norm = 1) :\n"
                f"    ∃ (u0 DJ DK : ℤ) (XJ XK : LuData),\n"
                f"      IntOK 3 2 (p % 3) Fr.norm u0 {tJ} DJ ∧ IntOK 3 2 (p % 3) Fr.norm u0 {tK} DK ∧\n"
                f"      XJ.ok {tJ}.nodes.length (mkFib 3 2 (p % 3) Fr.norm u0 {tJ} DJ) DJ = true ∧\n"
                f"      XK.ok {tK}.nodes.length (mkFib 3 2 (p % 3) Fr.norm u0 {tK} DK) DK = true ∧\n"
                f"      ¬ (p : ℤ) ∣ XJ.b * XK.a - XJ.a * XK.b := by\n  rw [hp3, hn]\n")
        def entry(u):
            (dJ, dK) = data[u]
            nJ, DJ = self.typ(rho, J[0], J[1], u, dJ)
            nK, DK = self.typ(rho, K[0], K[1], u, dK)
            return nJ, DJ, nK, DK
        if pl[0] == 'single':
            _, u, c, E = pl
            nJ, DJ, nK, DK = entry(u)
            body = (f"  exact ⟨{u}, {DJ}, {DK}, {nJ}, {nK}, intOK_{rho}_{J[0]}_{J[1]}_{u}, intOK_{rho}_{K[0]}_{K[1]}_{u},\n"
                    f"    ok_{rho}_{J[0]}_{J[1]}_{u}, ok_{rho}_{K[0]}_{K[1]}_{u},\n"
                    f"    not_dvd_smooth (Fact.out) hp _ {E} (by decide +kernel)⟩\n")
        else:
            _, ua, ub, ca, cb, x, y, g, E = pl
            nJa, DJa, nKa, DKa = entry(ua)
            nJb, DJb, nKb, DKb = entry(ub)
            ea = f"({nJa}.b * {nKa}.a - {nJa}.a * {nKa}.b)"
            eb = f"({nJb}.b * {nKb}.a - {nJb}.a * {nKb}.b)"
            body = (f"  have hb : ({x} : ℤ) * {ea} + ({y} : ℤ) * {eb} = {g} := by decide +kernel\n"
                    f"  have hg : ¬ (p : ℤ) ∣ ({g} : ℤ) := not_dvd_smooth (Fact.out) hp _ {E} (by decide +kernel)\n"
                    f"  rcases not_dvd_or_of_bezout hb hg with h | h\n"
                    f"  · exact ⟨{ua}, {DJa}, {DKa}, {nJa}, {nKa}, intOK_{rho}_{J[0]}_{J[1]}_{ua}, intOK_{rho}_{K[0]}_{K[1]}_{ua},\n"
                    f"      ok_{rho}_{J[0]}_{J[1]}_{ua}, ok_{rho}_{K[0]}_{K[1]}_{ua}, h⟩\n"
                    f"  · exact ⟨{ub}, {DJb}, {DKb}, {nJb}, {nKb}, intOK_{rho}_{J[0]}_{J[1]}_{ub}, intOK_{rho}_{K[0]}_{K[1]}_{ub},\n"
                    f"      ok_{rho}_{J[0]}_{J[1]}_{ub}, ok_{rho}_{K[0]}_{K[1]}_{ub}, h⟩\n")
        self.lines.append(head + body)
        self.pairs[key] = name
        return name


N0X = "(r + 2 * ((3 * r + 9) / 20))"


def fam_lean(F, fid, data):
    rho, jm, j1, br, meets = F['key']
    D = F['D']; w = F['w']; runs = D['runs']
    types = F['types']; blocks = F['blocks']
    T0, TV = runs[w]['start'], runs[w]['end']
    fields = [('hr', 'r % 2 = 0'), ('hp3', f'p % 3 = {rho}'), ('hlo', '3 * r < 10 * p'), ('hhi', '10 * p ≤ 39 * r'),
              ('hp60', '60 ≤ p'), ('hM1', f'{jm - 1} * p < r'), ('hM2', f'r ≤ {jm} * p'),
              ('hP1', f'{j1 - 3} * p + 2 < 3 * r' if j1 >= 4 else '0 < r'), ('hP2', f'3 * r ≤ {j1} * p + 2')]
    if br is not None:
        fields += [('hb1', f'{br} * p + 2 ≤ 3 * r'), ('hb2', f'3 * r < {br + 1} * p + 2')]
    S1 = D['S1']
    fields.append(('hm0', f'r < {S1}' if meets[0] else f'{S1} ≤ r'))
    fields.append(('hf1', f"{D['ST1']} < {N0X}" if meets[1] else f"{N0X} ≤ {D['ST1']}"))
    fields.append(('hf2', f"{D['ST2']} < {N0X}" if meets[2] else f"{N0X} ≤ {D['ST2']}"))
    cmp_ = []
    for w2 in F['feas']:
        if w2 == w: continue
        b = lambda k: f"base3 ((3 * r + 9) / 20) r p {runs[k]['start']} {runs[k]['end']}"
        cmp_.append((f'hc{w2}', f"{b(w)} < {b(w2)}" if w2 < w else f"{b(w)} ≤ {b(w2)}"))
    fields += cmp_
    names = [f[0] for f in fields if not f[0].startswith('hc')]
    L = []
    L.append(f"namespace F{fid}\n")
    L.append("structure Reg (r p : ℕ) : Prop where")
    for n, t in fields: L.append(f"  {n} : {t}")
    L.append("")
    have = '\n'.join(f"  have {n} := h.{n}" for n in names)
    def startnd(k):
        kind = runs[k]['kind']
        if kind == 'r': return f"notdvd_between (a := {jm - 1}) (by omega) (by omega)"
        if kind == 'P': return f"notdvd_pole (j := {j1}) (by omega) (by omega)"
        return f"notdvd_succ_mult (j := {jm}) (by omega)"
    # win
    x = blocks[w][0]
    L.append(f"theorem win {{r p : ℕ}} (h : Reg r p) :\n    Win3 cT cT_pos 3 2 r p (r + p) ({T0}) ({TV}) ((3 * r + 9) / 20) := by\n{have}")
    L.append(f"  have hm : (altGeom cT cT_pos).borderSize r = (3 * r + 9) / 20 := borderSize_T hr (by omega)")
    L.append(f"  have hnd : ¬ p ∣ {T0} := {startnd(w)}")
    L.append(f"  exact\n    {{ hr2 := hr, hr0 := by omega, hbs := hm, hrN := by omega, hNp := hNp_T hlo (by omega), hpm := by omega,\n"
             f"      hp2 := by omega, hq0 := by norm_num, hqp := by omega, ho0 := by norm_num, hop := by omega, hqo := by norm_num,\n"
             f"      ht0r := by omega, ht0b := by omega, ht0tv := by omega, htvp := by omega, htvN := by omega,\n"
             f"      hdiv := div_both (x := {x}) (by omega) (by omega) (by omega) (by omega), hnt0 := hnd }}\n")
    # per-run lemmas
    need = sorted(set([w] + [k for k in range(3) if meets[k] and k != w]))
    for k in need:
        R = runs[k]; xk = blocks[k][0]
        L.append(f"theorem nd{k} {{r p : ℕ}} (h : Reg r p) : ¬ p ∣ {R['start']} := by\n{have}\n  exact {startnd(k)}\n")
        L.append(f"theorem ns{k} {{Fr : Frame}} (T : TwoTermData Fr 3 2) {{r p : ℕ}} [Fact p.Prime] (h : Reg r p)\n"
                 f"    (hsq : ∀ t, 1 ≤ t → t < r + p → ¬ p ^ 2 ∣ 3 * t - 2) (hnorm : Fr.norm ∈ S p) (hnorm0 : red p Fr.norm ≠ 0) :\n"
                 f"    NoSingWin (twoTermPoleData T (hNp_T h.hlo (by have := h.hp60; omega)).le hsq hnorm hnorm0) ({R['start']}) (({R['end']}) - ({R['start']})) := by\n{have}\n"
                 f"  have hnd := nd{k} h\n"
                 f"  refine noSing_T T _ hsq hnorm hnorm0 _ _ (by omega) (fun k h1 h2 => ?_)\n"
                 f"    (nopole_T (fun k h1 h2 => by omega) (fun j hj k h1 h2 h3 => by interval_cases j <;> omega))\n"
                 f"  exact notdvd_between (a := {xk}) (by omega) (by omega)\n")
    # kill
    AJ, BJ = types[w]
    kb = []
    kb.append(f"theorem kill {{Fr : Frame}} (T : TwoTermData Fr 3 2) {{r p : ℕ}} [Fact p.Prime] (h : Reg r p) (hn : Fr.norm = 1)\n"
              f"    (hsq : ∀ t, 1 ≤ t → t < r + p → ¬ p ^ 2 ∣ 3 * t - 2) (hnorm : Fr.norm ∈ S p) (hnorm0 : red p Fr.norm ≠ 0) :\n"
              f"    ∀ v, r ≤ v → v < r + 2 * ((3 * r + 9) / 20) → (v < ({T0}) ∨ ({TV}) < v) → ¬ p ∣ v →\n"
              f"      Nonempty (AltKill cT cT_pos (win h).hr2 T (win h).hNp hsq hnorm hnorm0 ((win h).hbs ▸ (win h).hrN) ({T0}) v) := by\n{have}")
    kb.append(f"  intro v h1 h2 h3 h4\n  have hnv : v ≠ {jm} * p := fun e => h4 ⟨{jm}, by rw [e]; ring⟩")
    kb.append(f"  rcases (by omega : v < {D['S1']} ∨ ({D['ST1']} ≤ v ∧ v < {D['S2']}) ∨ {D['ST2']} ≤ v) with hA | hB | hC")
    for k, hh in zip(range(3), ['hA', 'hB', 'hC']):
        R = runs[k]
        kb.append(f"  · -- run {k}")
        if k == w or not meets[k]:
            kb.append("    exfalso; omega")
            continue
        AK, BK = types[k]
        pn = data.pair(rho, [AJ, BJ], [AK, BK])
        xk = blocks[k][0]; x0 = blocks[w][0]
        kb.append(f"    exact kill_of_pair T (win h) hsq hnorm hnorm0 ({R['start']}) v {AJ} {BJ} {AK} {BK}\n"
                  f"      (by omega) (by omega) (by omega) (nd{k} h) (by omega) (by omega)\n"
                  f"      (div_both (x := {xk}) (by omega) (by omega) (by omega) (by omega))\n"
                  f"      (nosing_mono (ns{k} T h hsq hnorm hnorm0) (by omega))\n"
                  f"      (Nat.div_eq_of_lt_le (by omega) (by omega)) (Nat.div_eq_of_lt_le (by omega) (by omega))\n"
                  f"      (Nat.div_eq_of_lt_le (by omega) (by omega)) (Nat.div_eq_of_lt_le (by omega) (by omega))\n"
                  f"      ({pn} hp3 hp60 hn)")
    L.append('\n'.join(kb) + "\n")
    L.append(f"noncomputable def cell {{Fr : Frame}} (T : TwoTermData Fr 3 2) {{r p : ℕ}} [Fact p.Prime] (h : Reg r p)\n"
             f"    (hn : Fr.norm = 1) (hnorm : Fr.norm ∈ S p) (hnorm0 : red p Fr.norm ≠ 0) : Cell3 cT cT_pos Fr 3 2 T r p :=\n"
             f"  cell3Gen T (win h) (hsq_T h.hlo (by have := h.hp60; omega)) hnorm hnorm0\n"
             f"    (ns{w} T h (hsq_T h.hlo (by have := h.hp60; omega)) hnorm hnorm0)\n"
             f"    (kill T h hn (hsq_T h.hlo (by have := h.hp60; omega)) hnorm hnorm0)\n")
    L.append(f"theorem cell_bound {{Fr : Frame}} (T : TwoTermData Fr 3 2) {{r p : ℕ}} [Fact p.Prime] (h : Reg r p)\n"
             f"    (hn : Fr.norm = 1) (hnorm : Fr.norm ∈ S p) (hnorm0 : red p Fr.norm ≠ 0) :\n"
             f"    (cell T h hn hnorm hnorm0).bound = base3 ((3 * r + 9) / 20) r p ({T0}) ({TV}) := by\n"
             f"  unfold cell; exact cell3Gen_bound T (win h) _ _ _ _ _\n")
    L.append(f"def T0 (r p : ℕ) : ℕ := {T0}\ndef TV (r p : ℕ) : ℕ := {TV}\n")
    L.append(f"end F{fid}\n")
    return '\n'.join(L)


HDR = """module

public import CatalanCore.Uniform.Content.UFFamily3.Sing3

@[expose] public section

open Polynomial Matrix Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Arith.Hybrid.Periodic CatalanCore.Uniform.Content.UFMember
  CatalanCore.Uniform.Content.Hybrid CatalanCore.Uniform.Content.UFMoments
  CatalanCore.Uniform.Content.UFWedge CatalanCore.Uniform.Content.Smith
  CatalanCore.Uniform CatalanCore.Uniform.Content.Shape CatalanCore.Uniform.Content.UFWire
  CatalanCore.Uniform.Content.Member CatalanCore.Uniform.Content.Wire
  CatalanCore.Uniform.Content.UFFamily CatalanCore.Uniform.Content.UFFamily.SevE
  CatalanCore.Uniform.Content.UFFamily2

namespace CatalanCore.Uniform.Content.UFFamily3
"""
FTR = "\nend CatalanCore.Uniform.Content.UFFamily3\n"


from thirds_asm import thirds_lean

def main():
    cmd = sys.argv[1]
    if cmd == 'plan':
        rmax = int(sys.argv[3]) if len(sys.argv) > 3 else 3000
        polys = plan(rmax)
        fams = families(polys)
        json.dump(fams, open(sys.argv[2], 'w'))
        print(len(polys), 'polygons', len(fams), 'families', 'bad', sum(e['bad'] for e in polys.values()))
        for f in fams:
            print(f['key'], f['w'], f['n'], f.get('feas'), f.get('bad'))
    elif cmd == 'emit':
        fams = [f for f in json.load(open(sys.argv[2])) if not f.get('infeasible')]
        outdir = sys.argv[3]
        per = 4
        os.makedirs(outdir, exist_ok=True)
        data = Data()
        texts = []
        for i, F in enumerate(fams):
            F['key'][4] = tuple(F['key'][4])
            texts.append(fam_lean(F, i, data))
        # data modules per rho are one module
        dtxt = HDR.replace('Sing3', 'Sing3') + "\n".join(data.lines) + FTR
        # Data imports Kill3 (not families)
        open(os.path.join(outdir, 'DataThirds.lean'), 'w', encoding='utf-8').write(dtxt)
        mods = []
        for j in range(0, len(texts), per):
            name = 'FamThirds%d' % (j // per)
            body = HDR.replace('Sing3', 'DataThirds') + "\n".join(texts[j:j + per]) + FTR
            open(os.path.join(outdir, name + '.lean'), 'w', encoding='utf-8').write(body)
            mods.append(name)
        open(os.path.join(outdir, 'Thirds.lean'), 'w', encoding='utf-8').write(thirds_lean(len(fams), mods))
        json.dump(dict(mods=mods, nfam=len(fams), nlu=len(data.lu), npairs=len(data.pairs)), open(os.path.join(outdir, 'index.json'), 'w'))
        print(len(fams), 'families', len(data.pairs), 'pairs', len(data.lu), 'lu records')


if __name__ == '__main__':
    main()
