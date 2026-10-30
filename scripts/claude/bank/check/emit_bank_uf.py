"""The UF template of a two-term bank for the Lean bank check (lane C1L), generalising emit_thirds_uf.py.

C1's checker generates the Theorem C template (prefix truncation n, maximal affine runs of the profile minimum, zero
tail); certificates are searched over the Lean catalogue `tableT ++ [LP1, LP2, R, S] ++ windows` by the exact mirror,
re-verified in the Lean form (explicit R and V) together with the per-member class sums, and emitted as Lean data
modules (a header, one module per root class, the assembly; one `decide +kernel` per chunk).  n is the smallest n >= n_min with
mu(n) = c / (D - Lambda_fin(n)) <= target - slack/2, slack = target - mu at the exact Lambda; mu(n) decreases in n.
Usage: python -I -X utf8 emit_bank_uf.py <bank>     (bank in BANKS below)"""
import sys
from fractions import Fraction as F
from decimal import Decimal, getcontext
from pathlib import Path
sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
C1 = HERE.parents[3].parents[1] / 'outputs/Compatibility programme/automatic-banks-2026-10-28/C1'
sys.path.insert(1, str(C1))
import mirror as X
import gen_thirds_check as G
import emit_thirds as E
import checker as CK
import layers as LY
import template_check as TC
from pl import PL, pl_min

CBIG = F(10) ** 12
NL = chr(10)
BANKS = {
    'fifths': dict(q=5, M=10, members=[1, 2, 3, 4], Pbad=9, cF=49, alpha0=F(20, 9), t0=F(1, 900),
                   alpha0b=F(20, 9), n_min=100, lp2w=True, pre_nmax=8,
                   D=F(4826561916291581150063627, 1265625000000000000000000), c=F(2239239458955067, 312500000000000),
                   target=F(47823, 2000), lam_rat=F(18614248183031951531578379, 5321679222691225544230080),
                   lam_log2=F(2, 81), module='CatalanCore.Uniform.Bank.FifthsContent.AutoData',
                   path='CatalanCore/Uniform/Bank/FifthsContent/AutoData.lean', ns='CatalanCore.Uniform.Bank.FifthsContent.Auto'),
    'lambda': dict(q=4, M=4, members=[1, 3], Pbad=28, cF=36, alpha0=F(11, 5), t0=F(1, 1000),
                   alpha0b=F(11, 5), n_min=100, lp2w=True, pre_nmax=8,
                   D=F(14627817894518751186053, 3906250000000000000000), c=F(1438085452130567, 200000000000000),
                   target=F(314411, 10000), lam_rat=F(25845089911312474748789, 7378677391061896920000),
                   lam_log2=F(1, 50), module='CatalanCore.Uniform.Bank.FourthsContent.AutoData',
                   path='CatalanCore/Uniform/Bank/FourthsContent/AutoData.lean', ns='CatalanCore.Uniform.Bank.FourthsContent.Auto'),
    'sevenths': dict(q=7, M=14, members=[1, 2, 3, 4, 5, 6], Pbad=13, cF=81, alpha0=F(13, 6), t0=F(1, 1000),
                     alpha0b=F(13, 6), n_min=100, class_split=True, lp2w=True, pre_nmax=8,
                     windows=[(m, m + e) for m in range(0, 41) for e in (0, 1)],
                     parts=3, chunk=10,
                     D=F(2185487560184413390033, 600000000000000000000), c=F(7425954607455103, 1000000000000000),
                     target=F(2801),
                     lam_rat=F(8926987763346083870538925313134246938568387, 2458710375447819602863559629392237970329600),
                     lam_log2=F(1, 72), module='CatalanCore.Uniform.Bank.SeventhsContent.AutoData',
                     path='CatalanCore/Uniform/Bank/SeventhsContent/AutoData.lean', ns='CatalanCore.Uniform.Bank.SeventhsContent.Auto'),
}


def dec(x):
    return Decimal(x.numerator) / Decimal(x.denominator)


def lam_fin(name, b, n):
    T = templates_new(name, b, n, CBIG)
    return sum(b['alpha0'] * T[j][0] + sum(a * (t - s) + bb * (t * t - s * s) / 2 for s, t, a, bb, _ in T[j][1])
               for j in T) / len(T)


def mu(b, lam):
    return b['c'] / (b['D'] - lam)


def exact_lam(name, b, nref=150):
    """(lam_rat, lam_log2) of the limit n -> infinity.  For a catalogue with the widened LP2 and/or prefix branches the
    rational part is the legacy `lam_rat` minus the exact drop of the finite template mass (legacy catalogue minus new
    catalogue, same n; the sawtooth beyond the strips <= pre_nmax is identical, so the drop does not depend on n)."""
    if not (b.get('lp2w') or b.get('pre_nmax')):
        return b['lam_rat'], b['lam_log2']
    old = dict(b, lp2w=False, pre_nmax=0)
    drop = lam_fin(name, old, nref) - lam_fin(name, b, nref)
    assert drop == lam_fin(name, old, nref + 37) - lam_fin(name, b, nref + 37), 'drop depends on n'
    return b['lam_rat'] - drop, b['lam_log2']


def choose_n(name, b):
    getcontext().prec = 80
    lr, ll = exact_lam(name, b)
    lam_ex = dec(lr) + dec(ll) * Decimal(2).ln()
    mu_ex = dec(b['c']) / (dec(b['D']) - lam_ex)
    slack = dec(b['target']) - mu_ex
    bound = dec(b['target']) - slack / 2
    ok = lambda n: dec(mu(b, lam_fin(name, b, n))) <= bound
    lo, hi = b['n_min'] - 1, 4 * b['n_min']
    if ok(b['n_min']):
        return b['n_min'], mu_ex, slack
    while not ok(hi):
        lo, hi = hi, 2 * hi
        assert hi <= 10 ** 6
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if ok(mid):
            hi = mid
        else:
            lo = mid
    return hi, mu_ex, slack


def catalogue(wins, b=None):
    """Mirror catalogue = Lean `tableT ++ ([LP1, LP2(w), R, S] ++ windows) ++ pres`."""
    b = b or {}
    base = X.BASE_W if b.get('lp2w') else X.BASE
    pres = X.pres_list(b.get('pre_nmax', 0))
    names = [n for n, _ in base] + ['S'] + [f'W{a}_{c}' for a, c in wins] + [f'P{n}_{j0}_{j1}' for n, j0, j1 in pres]
    cat = [x for _, x in base] + [X.UFS] + [X.window(a, c) for a, c in wins] + [X.prefix(*x) for x in pres]
    return names, cat


# ------------------------------------------------------------------ profile with LP2w and prefix (exact)
_ORIG = (LY.LP_branches, LY.conditions)


def set_lp2w(on):
    """Switch C1's template_check between the strict LP2 and the widened LP2 (validity from 1, condition N <= 2p)."""
    orig_lp, orig_cond = _ORIG
    if not on:
        LY.LP_branches, LY.conditions = orig_lp, orig_cond
        return
    LY.LP_branches = lambda al, ka, L, H, strict=True: orig_lp(al, ka, L, H, strict=False)
    def cond(al, ka, q):
        C, B = orig_cond(al, ka, q)
        B = dict(B); B['LP2'] = ['r<p', 'k<=r', 'N<=2p', 'p<r+m']
        return C, B
    LY.conditions = cond


def branch_pl(e, al, ka, L, H):
    """The exact PL function of theta on (L, H] of a catalogue expression (homogenised at r = 1, p = theta, m = al)."""
    pts = [L] + X.subdivide(e, al, ka, L, H) + [H]
    return PL([(u, v, X.aff(e, al, ka, u, v)) for u, v in zip(pts, pts[1:])])


def pre_region_templates(al, ka, lo, hi, nmax):
    """pieces (s, t, a, b) of the envelope min(D1x, brPre(n, j0, j1) : n <= nmax) on (lo, hi].  Adjacent elementary
    pieces with the same line are merged only while ONE branch attains the line on the whole run (so every template
    piece has a single-branch certificate)."""
    exprs = [X.D1x[0]] + [X.prefix(*x)[0] for x in X.pres_list(nmax)]
    bps = [branch_pl(e, al, ka, lo, hi) for e in exprs]
    f = pl_min(bps)
    el = [(a_, b_, l) for a_, b_, l in f.ps]
    # per elementary piece: the set of branches attaining the line there
    att = []
    for a_, b_, l in el:
        m = (a_ + b_) / 2
        att.append({i for i, g in enumerate(bps) if g.line_at(m) == l})
        assert att[-1], (a_, b_)
    out = []
    for (a_, b_, l), A in zip(el, att):
        if out and out[-1][2] == l and out[-1][1] == a_ and (out[-1][3] & A):
            out[-1] = (out[-1][0], b_, l, out[-1][3] & A)
        else:
            out.append((a_, b_, l, set(A)))
    return [(a_, b_, l[0], l[1]) for a_, b_, l, _ in out]


def templates_new(name, b, n, Cbig):
    """Templates of Theorem C for the catalogue with LP2w (b['lp2w']) and prefixes (b['pre_nmax']): the core of C1's
    class_template (profile for theta >= alpha, LP2 widened), the sawtooth D1x for the strips i > nmax and the exact
    envelope of D1x and the prefix branches on theta in (alpha/(nmax+1), alpha]."""
    set_lp2w(bool(b.get('lp2w')))
    nmax = b.get('pre_nmax', 0)
    bk = CK.Bank(name, True)
    al, q, P_bad = bk.al, bk.q, b['Pbad']
    TC.QQ[0] = q
    out = {}
    for c in bk.rk['cases']:
        ka = F(c['pole_cut']); j = int(ka * q)
        res = TC.class_template(bk.bank, al, ka, al, bk.H, [x for cell in c['cells'] for x in cell['price_pieces']], bk.uf)
        core = [(F(P['s']), F(P['t']), F(P['line'][0]), F(P['line'][1]), Cbig) for P in res['detail'] if F(P['s']) >= al]
        pre = []
        for i in range(n - 1, nmax, -1):
            u, v, w = al / (i + 1), 2 * al / (2 * i + 1), al / i
            pre.append((u, v, 2 + 3 * al, F(-(i + 1)), Cbig))
            pre.append((v, w, 2 + al, F(i), Cbig))
        if nmax:
            lo = al / (nmax + 1)
            assert n - 1 >= nmax
            pre += [(s_, t_, a_, b_, Cbig) for s_, t_, a_, b_ in pre_region_templates(al, ka, lo, al, nmax)]
        tau0 = max(q * (1 + 2 * al), F(P_bad, 2))
        if core[-1][1] < tau0:
            core.append((core[-1][1], tau0, F(0), F(0), Cbig))
        out[j] = (al / n, pre + core)
    return out


def fast_search(P, cat, names, q, al, ka, depth, cF, Pbad):
    """G.search restricted to the branches that lie on or below the piece's line at its midpoint (necessary for a
    certificate); falls back to the full search on failure.  Same result as the full search up to ties."""
    s, t, a, b = P[:4]
    m = (s + t) / 2
    d = (t - s) / 8
    cands = set()
    for bi, (tau, conds, deb) in enumerate(cat):
        ln = X.aff(tau, al, ka, m - d, m)
        if ln is None or X.lv(ln, m) <= a + b * m:
            cands.add(bi)
    r = G.search(P, cat, names, q, al, ka, depth, cF, Pbad, only=cands)
    return r if r is not None else G.search(P, cat, names, q, al, ka, depth, cF, Pbad)


def build(name, b, wins, n):
    names, cat = catalogue(wins, b)
    bk = CK.Bank(name, True)
    T = templates_new(name, b, n, CBIG)
    q, al = b['q'], bk.al
    D = dict(q=q, M=b['M'], al=al, members=b['members'], depth=64, cF=b['cF'], Pbad=b['Pbad'],
             alpha0=b['alpha0'], tau=None, alpha0b=b['alpha0b'], t0=b['t0'], cat=cat, iD6=5, tmpls={})
    assert all(T[j][0] <= b['t0'] for j in T), 't1 > t0'
    used = set()
    for j, (t1, pieces) in T.items():
        ka = F(j, q)
        rows = []
        for P in pieces:
            r = fast_search(P, cat, names, q, al, ka, D['depth'], D['cF'], D['Pbad'])
            assert r is not None, ('no certificate', j, P[:4])
            _, cert, _ = r
            used.add(names[cert[0]])
            for _, y, _ in cert[2]:
                used.add(names[y])
            rows.append((P, cert))
        D['tmpls'][j] = (t1, rows)
    D['tau'] = max(D['tmpls'][j][1][-1][0][1] for j in D['tmpls'])
    D['Lam'] = sum(X.mass(D['alpha0'], *D['tmpls'][j]) for j in D['tmpls']) / len(D['tmpls'])
    return D, names, used


def lpiece(P):
    return '⟨%s, %s, %s, %s, %s⟩' % tuple(E.lq(x) for x in P)


def emit(name, b, D, T, wins, n, chunk=20):
    """Split emission (each data module small): `AutoData/Head.lean` (qq, bankExtra, the header bank `bankHead`
    with `Λ := 0`, `tmpls := []`), one `AutoData/U<j>.lean` per root class (chunks, `tmpl<j>`, the checks against
    `bankHead`), and `AutoData.lean` (`bankData = {bankHead with Λ, tmpls}`, the transport `tmplOK_withTmpls`,
    params, classes, `bank_check`, `bankData_Λ`)."""
    ns, mod = b['ns'], b['module']
    main = G.WORK / b['path']
    sub = main.with_suffix('')
    sub.mkdir(parents=True, exist_ok=True)
    Lam, tau, al, t0, a0, a0b = D['Lam'], D['tau'], D['al'], b['t0'], b['alpha0'], b['alpha0b']
    wl = ', '.join(f'brWin {a} {c}' for a, c in wins)
    newcat = bool(b.get('lp2w') or b.get('pre_nmax'))
    pres = X.pres_list(b.get('pre_nmax', 0))
    cat_txt = 'tableT ++ [LP1, LP2w, R, S] ++ windows ++ prefixes' if newcat else 'tableT ++ [LP1, LP2, R, S] ++ windows'
    opn = 'open CatalanCore.Uniform.Content.BankShared.Check\n'
    if newcat:
        wtxt = str([tuple(w) for w in wins])
        ptxt = str([tuple(x) for x in pres])
        nm_ = b.get('pre_nmax', 0)
        extra_txt = NL.join([
            '/-- The M3D windows of the catalogue. -/',
            f'def bankWins : List (ℕ × ℕ) := {wtxt}',
            '',
            f'/-- The prefix branches `brPre n j0 j1` (`1 ≤ n ≤ {nm_}`, `j0 < 2`, `j1 < 3`). -/',
            f'def bankPres : List (ℕ × ℕ × ℕ) := {ptxt}',
            '',
            '/-- LP1, LP2w, the rank branch, the UF branch (indices 6, 7, 8, 9), the M3D windows, then the prefix branches. -/',
            'def bankExtra : List Branch :=',
            '  ([brLP1, brLP2w, brRank, brS] ++ bankWins.map (fun w => brWin w.1 w.2)) ++',
            '    bankPres.map (fun x => brPre x.1 x.2.1 x.2.2)', ''])
    else:
        extra_txt = NL.join(['/-- LP1, LP2, the rank branch, the UF branch and the M3D windows (indices 6, 7, 8, 9, 10, ...). -/',
                             f'def bankExtra : List Branch := [brLP1, brLP2, brRank, brS, {wl}]', ''])
    head = f"""import CatalanCore.Uniform.Content.BankShared.Check.Split
import CatalanCore.Uniform.Content.BankShared.Check.{'Prefix' if newcat else 'UF'}
set_option Elab.async false

/-! # Data header: the {name} bank parameters (lane C1L)

Generated by `scripts/claude/bank/check/emit_bank_uf.py {name}`.  The header bank `bankHead` carries the parameters
of the {name} UF bank (`P_bad = {b['Pbad']}`, `c_Fr ≤ {b['cF']}`, depth `≤ 64`, catalogue
`{cat_txt}`) with `Λ := 0` and no templates; the per-class modules `U<j>` check their
template against it, and `AutoData` assembles the bank (`Check.Split`). -/

namespace {ns}
{opn}
/-- `n / d`. -/
abbrev qq (n : ℤ) (d : ℕ) : ℚ := (n : ℚ) / d

{extra_txt}
/-- The {name} bank parameters, without templates. -/
def bankHead : BankData where
  q := {b['q']}
  M := {b['M']}
  α := qq {al.numerator} {al.denominator}
  members := {b['members']}
  depth := 64
  cF := {b['cF']}
  Pbad := {b['Pbad']}
  α0 := qq {a0.numerator} {a0.denominator}
  τ := qq {tau.numerator} {tau.denominator}
  Λ := 0
  α0b := qq {a0b.numerator} {a0b.denominator}
  t0 := qq {t0.numerator} {t0.denominator}
  extra := bankExtra
  tmpls := []

end {ns}
"""
    (sub / 'Head.lean').write_text(head, encoding='utf-8')
    for j in sorted(T):
        rows = T[j][1]
        L = [f"""import {mod}.Head
set_option Elab.async false
set_option maxRecDepth 100000

/-! # Data: root class `j = {j}` of the {name} UF template (lane C1L)

Generated by `scripts/claude/bank/check/emit_bank_uf.py {name}`: C1's Theorem C template with UF for the class
`j = {j}` (prefix truncation `n = {n}` chosen from the μ target, the maximal affine runs of the profile minimum, the
zero tail, `C = 10¹²`), certificates verified by the exact mirror; `tmpl{j}_ok : tmplOK bankHead {j} tmpl{j} = true`,
one `decide +kernel` per chunk of `≤ {chunk}` pieces. -/

namespace {ns}
{opn}"""]
        nms = []
        for ci in range(0, len(rows), chunk):
            nm = f'u{j}_{ci // chunk}'
            nms.append(nm)
            body = ',\n  '.join('(%s, %s)' % (lpiece(P), E.lcert(c)) for P, c in rows[ci:ci + chunk])
            L.append(f'def {nm} : List (QPiece × Cert) := [\n  {body}]\n')
        t1 = T[j][0]
        L.append(f'def tmpl{j} : QTmpl := ⟨qq {t1.numerator} {t1.denominator}, {E.nest(nms)}⟩\n')
        for nm in nms:
            L.append(f'set_option profiler true in\ntheorem {nm}_ok : pieceAll bankHead {j} {nm} = true := by decide +kernel\n')
        L.append(f'set_option profiler true in\ntheorem tmpl{j}_head : tmplHead bankHead {j} tmpl{j} = true := by decide +kernel\n')
        oks = ', '.join(f'{nm}_ok' for nm in nms)
        L.append(f"""theorem tmpl{j}_ok : tmplOK bankHead {j} tmpl{j} = true := by
  unfold tmplOK
  rw [tmpl{j}_head]
  show (true && pieceAll bankHead {j} ({E.nest(nms)})) = true
  simp only [pieceAll_append, {oks}, Bool.and_self]

end {ns}
""")
        (sub / f'U{j}.lean').write_text('\n'.join(L), encoding='utf-8')
    tl = ', '.join(f'({j}, tmpl{j})' for j in sorted(T))
    imps = '\n'.join(f'import {mod}.U{j}' for j in sorted(T))
    okd = '\n'.join(f'theorem tmpl{j}_okD : tmplOK bankData {j} tmpl{j} = true :=\n'
                    f'  tmplOK_withTmpls bankHead _ _ {j} tmpl{j} tmpl{j}_ok\n' for j in sorted(T))
    oks = ', '.join(f'tmpl{j}_okD' for j in sorted(T))
    if b.get('class_split'):
        mem = b['members']
        cl = ''.join(f'set_option profiler true in\ntheorem bank_class{a} : classOK bankData {a} = true := by decide +kernel\n\n'
                     for a in mem)
        cl += (f'theorem bank_classes : bankData.members.all (classOK bankData) = true := by\n'
               f'  show {mem}.all (classOK bankData) = true\n'
               '  simp only [List.all_cons, List.all_nil, ' + ', '.join(f'bank_class{a}' for a in mem) + ', Bool.and_self]\n')
    else:
        cl = ('set_option profiler true in\n'
              'theorem bank_classes : bankData.members.all (classOK bankData) = true := by decide +kernel\n')
    classes = cl
    cat_thm = '' if not newcat else NL.join([
        '/-- The catalogue of `bankData` in the shape of `catValid_bankUFwP`. -/',
        'theorem bankData_cat : bankData.cat = tableT ++ ([brLP1, brLP2w, brRank, brS] ++',
        '    bankWins.map (fun w => brWin w.1 w.2)) ++ bankPres.map (fun x => brPre x.1 x.2.1 x.2.2) :=',
        '  (List.append_assoc _ _ _).symm', '', ''])
    body = f"""{imps}
set_option Elab.async false
set_option maxRecDepth 100000

/-! # Data: the {name} UF bank for the bank check (lane C1L)

Generated by `scripts/claude/bank/check/emit_bank_uf.py {name}`: the header `bankHead` (`AutoData/Head`) with the
templates of `AutoData/U<j>` and the finite content constant `Λ_fin` (prefix truncation `n = {n}`).  The template
checks transport from `bankHead` (`tmplOK_withTmpls`); `bank_check : check bankData = true`. -/

namespace {ns}
{opn}
/-- The {name} UF bank data, with its finite `Λ_fin`. -/
def bankData : BankData := {{ bankHead with Λ := qq {Lam.numerator} {Lam.denominator}, tmpls := [{tl}] }}

{okd}
{cat_thm}set_option profiler true in
theorem bank_params : checkParams bankData = true := by decide +kernel

{classes}
theorem bank_tmpls : bankData.tmpls.all (fun x => tmplOK bankData x.1 x.2) = true := by
  show [{tl}].all (fun x => tmplOK bankData x.1 x.2) = true
  simp only [List.all_cons, List.all_nil, {oks}, Bool.and_self]

/-- **The bank check accepts the {name} UF data.** -/
theorem bank_check : check bankData = true := by
  unfold check
  rw [bank_params, bank_tmpls, bank_classes]
  rfl

/-- The finite content constant. -/
theorem bankData_Λ : bankData.Λ = ({Lam.numerator} /
    {Lam.denominator} : ℚ) := by
  decide +kernel

end {ns}
"""
    main.write_text(body, encoding='utf-8')
    return main


def qmass(P):
    s, t, a, bb = P[:4]
    return a * (t - s) + bb * (t * t - s * s) / 2


def lrat(x):
    return '(%d / %d : ℚ)' % (x.numerator, x.denominator) if x.denominator != 1 else '(%d : ℚ)' % x.numerator


def cat_theorem(b):
    """`bankData_cat` (the catalogue of bankData in the shape of catValid_bankUFwP); empty for legacy catalogues."""
    if not (b.get('lp2w') or b.get('pre_nmax')):
        return ''
    return NL.join([
        '/-- The catalogue of `bankData` in the shape of `catValid_bankUFwP`. -/',
        'theorem bankData_cat : bankData.cat = tableT ++ ([brLP1, brLP2w, brRank, brS] ++',
        '    bankWins.map (fun w => brWin w.1 w.2)) ++ bankPres.map (fun x => brPre x.1 x.2.1 x.2.2) :=',
        '  (List.append_assoc _ _ _).symm', '', ''])


def emit_parts(name, b, D, T, wins, n):
    """Large banks: the `emit` layout with each class split into part modules `U<j>P<k>` (chunks, their checks and
    their masses), the class module `U<j>` (template, head, `tmplOK`, `tmpl<j>_mass`), and the assembly using the
    supplied masses (`Check.Mass.classOK_of_masses`), so that no template mass is evaluated more than once."""
    emit(name, b, D, T, wins, n, chunk=b.get('chunk', 20))   # Head (the class and assembly files are rewritten below)
    chunk, parts = b.get('chunk', 20), b['parts']
    ns, mod = b['ns'], b['module']
    main = G.WORK / b['path']
    sub = main.with_suffix('')
    opn = 'open CatalanCore.Uniform.Content.BankShared.Check\n'
    a0 = b['alpha0']
    masses = {}
    for j in sorted(T):
        rows = T[j][1]
        chunks = [rows[ci:ci + chunk] for ci in range(0, len(rows), chunk)]
        nms = [f'u{j}_{k}' for k in range(len(chunks))]
        per = -(-len(chunks) // parts)
        groups = [list(range(g, min(g + per, len(chunks)))) for g in range(0, len(chunks), per)]
        for gi, grp in enumerate(groups):
            L = [f"""import {mod}.Head
set_option Elab.async false
set_option maxRecDepth 100000

/-! # Data: root class `j = {j}` of the {name} UF template, part {gi} (lane C1L)

Generated by `scripts/claude/bank/check/emit_bank_uf.py {name}` (prefix truncation `n = {n}`): chunks
`{nms[grp[0]]}` … `{nms[grp[-1]]}` of `≤ {chunk}` pieces, each with `pieceAll bankHead {j}` and its mass by
`decide +kernel`. -/

namespace {ns}
{opn}"""]
            for k in grp:
                body = ',\n  '.join('(%s, %s)' % (lpiece(P), E.lcert(c)) for P, c in chunks[k])
                L.append(f'def {nms[k]} : List (QPiece × Cert) := [\n  {body}]\n')
            for k in grp:
                m = sum((qmass(P) for P, _ in chunks[k]), F(0))
                L.append(f'set_option profiler true in\ntheorem {nms[k]}_ok : pieceAll bankHead {j} {nms[k]} = true := by decide +kernel\n')
                L.append(f'set_option profiler true in\ntheorem {nms[k]}_mass : ({nms[k]}.map (fun x => x.1.mass)).sum = {lrat(m)} := by\n  decide +kernel\n')
            L.append(f'end {ns}\n')
            (sub / f'U{j}P{gi}.lean').write_text('\n'.join(L), encoding='utf-8')
        t1 = T[j][0]
        M = a0 * t1 + sum((qmass(P) for P, _ in rows), F(0))
        masses[j] = M
        imps = '\n'.join(f'import {mod}.U{j}P{gi}' for gi in range(len(groups)))
        oks = ', '.join(f'{nm}_ok' for nm in nms)
        ms = ', '.join(f'{nm}_mass' for nm in nms)
        cls = f"""{imps}
set_option Elab.async false
set_option maxRecDepth 100000

/-! # Data: the template of the root class `j = {j}` of the {name} UF bank (lane C1L)

Generated by `scripts/claude/bank/check/emit_bank_uf.py {name}`: `tmpl{j}` (chunks of the parts `U{j}P<k>`),
`tmpl{j}_ok : tmplOK bankHead {j} tmpl{j} = true`, and its mass `tmpl{j}_mass` (from the chunk masses). -/

namespace {ns}
{opn}
def tmpl{j} : QTmpl := ⟨qq {t1.numerator} {t1.denominator}, {E.nest(nms)}⟩

set_option profiler true in
theorem tmpl{j}_head : tmplHead bankHead {j} tmpl{j} = true := by decide +kernel

theorem tmpl{j}_ok : tmplOK bankHead {j} tmpl{j} = true := by
  unfold tmplOK
  rw [tmpl{j}_head]
  show (true && pieceAll bankHead {j} ({E.nest(nms)})) = true
  simp only [pieceAll_append, {oks}, Bool.and_self]

set_option profiler true in
/-- The mass `α0 t1 + Σ ∫ P` of `tmpl{j}`. -/
theorem tmpl{j}_mass : tmpl{j}.mass (qq {a0.numerator} {a0.denominator}) = {lrat(M)} := by
  simp only [QTmpl.mass, tmpl{j}, List.map_append, List.sum_append, {ms}]
  decide +kernel

end {ns}
"""
        (sub / f'U{j}.lean').write_text(cls, encoding='utf-8')
    Lam = D['Lam']
    assert sum(masses.values(), F(0)) / len(masses) == Lam, 'template masses do not average to Lambda_fin'
    tl = ', '.join(f'({j}, tmpl{j})' for j in sorted(T))
    imps = '\n'.join(f'import {mod}.U{j}' for j in sorted(T))
    cat_thm = cat_theorem(b)
    okd = '\n'.join(f'theorem tmpl{j}_okD : tmplOK bankData {j} tmpl{j} = true :=\n'
                    f'  tmplOK_withTmpls bankHead _ _ {j} tmpl{j} tmpl{j}_ok\n' for j in sorted(T))
    oks = ', '.join(f'tmpl{j}_okD' for j in sorted(T))
    ml = ', '.join(f'({j}, {lrat(masses[j])})' for j in sorted(T))
    mpf = ',\n    '.join(f'tmpl{j}_mass.trans rfl' for j in sorted(T))
    body = f"""{imps}
import CatalanCore.Uniform.Content.BankShared.Check.Mass
set_option Elab.async false
set_option maxRecDepth 100000

/-! # Data: the {name} UF bank for the bank check (lane C1L)

Generated by `scripts/claude/bank/check/emit_bank_uf.py {name}`: the header `bankHead` (`AutoData/Head`) with the
templates of `AutoData/U<j>` and the finite content constant `Λ_fin` (prefix truncation `n = {n}`).  The template
checks transport from `bankHead` (`tmplOK_withTmpls`); (D1, D6) use the template masses `bankMasses` proved in
`U<j>` (`classOK_of_masses`); `bank_check : check bankData = true`. -/

namespace {ns}
{opn}
/-- The {name} UF bank data, with its finite `Λ_fin`. -/
def bankData : BankData := {{ bankHead with Λ := qq {Lam.numerator} {Lam.denominator}, tmpls := [{tl}] }}

{okd}
{cat_thm}/-- The template masses. -/
def bankMasses : List (ℕ × ℚ) := [{ml}]

theorem bank_masses : ∀ x ∈ bankData.tmpls, x.2.mass bankData.α0 = massOf bankMasses x.1 := by
  show ∀ x ∈ [{tl}], x.2.mass (qq {a0.numerator} {a0.denominator}) = massOf bankMasses x.1
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ⟨{mpf}⟩

set_option profiler true in
theorem bank_params : checkParams bankData = true := by decide +kernel

set_option profiler true in
theorem bank_classesM : bankData.members.all (classOKM bankData bankMasses) = true := by decide +kernel

theorem bank_classes : bankData.members.all (classOK bankData) = true := by
  rw [show classOK bankData = classOKM bankData bankMasses from
    funext (classOK_of_masses bankData bankMasses bank_masses)]
  exact bank_classesM

theorem bank_tmpls : bankData.tmpls.all (fun x => tmplOK bankData x.1 x.2) = true := by
  show [{tl}].all (fun x => tmplOK bankData x.1 x.2) = true
  simp only [List.all_cons, List.all_nil, {oks}, Bool.and_self]

/-- **The bank check accepts the {name} UF data.** -/
theorem bank_check : check bankData = true := by
  unfold check
  rw [bank_params, bank_tmpls, bank_classes]
  rfl

/-- The finite content constant. -/
theorem bankData_Λ : bankData.Λ = ({Lam.numerator} /
    {Lam.denominator} : ℚ) := by
  decide +kernel

end {ns}
"""
    main.write_text(body, encoding='utf-8')
    return main


if __name__ == '__main__':
    name = sys.argv[1]
    b = BANKS[name]
    n, mu_ex, slack = choose_n(name, b)
    print(name, 'n', n, 'mu at the exact Lambda', float(mu_ex), 'slack', float(slack))
    D, names, used = build(name, b, b.get('windows', G.WINDOWS), n)
    wins = sorted({tuple(map(int, w[1:].split('_'))) for w in used if w.startswith('W')})
    D, names, used = build(name, b, wins, n)
    ok, st = X.check(D)
    assert ok, 'mirror check rejected'
    T = E.lean_form(D)
    E.unit_check(D, T)
    out = (emit_parts if b.get('parts') else emit)(name, b, D, T, wins, n)
    print('windows', wins)
    print('pieces', {j: len(D['tmpls'][j][1]) for j in D['tmpls']}, 'tau', D['tau'])
    print('max R_P', float(st['max_R_P']), 'max C_needed', float(st['max_C_needed']))
    print('Lam_fin', float(D['Lam']), 'num digits', len(str(D['Lam'].numerator)))
    print('mu(Lam_fin)', float(mu(b, D['Lam'])), '<= target', mu(b, D['Lam']) <= b['target'],
          'excess over exact', float(dec(mu(b, D['Lam'])) - mu_ex))
    print('wrote', out)
