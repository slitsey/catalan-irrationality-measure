"""G10: Lean module for ONE packet at the gi witness, original-label chart rows (Data146O format):
V, adjugate data, per-chart kernel certificates, check, exact weights, window theorems (host as explicit hypothesis).
usage: genpk.py KEY OUT.lean N0 'a,b,c0,c1' ['a,b,c0,c1' ...]   (fractions as p/q)"""
import os, sys; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import json, importlib.util, re, time
sys.dont_write_bytecode = True
from fractions import Fraction as F
from math import gcd
import packetinfo as PI, rowgen as RG, spec as SP
R = "C:/Users/seanl/Documents/Codex/2026-10-11/plea/outputs/Compatibility programme/"
_s = importlib.util.spec_from_file_location('L', R + 'G-kernel-degrees-2026-10-27/partial-rank/lll/lll.py')
L = importlib.util.module_from_spec(_s); _s.loader.exec_module(L)
def lcm(a, b): return a // gcd(a, b) * b
def inv(M):
    k = len(M); A = [[F(x) for x in r] + [F(int(i == j)) for j in range(k)] for i, r in enumerate(M)]
    for c in range(k):
        r = next(r for r in range(c, k) if A[r][c]); A[c], A[r] = A[r], A[c]
        iv = 1 / A[c][c]; A[c] = [x * iv for x in A[c]]
        for r in range(k):
            if r != c and A[r][c]:
                q = A[r][c]; A[r] = [x - q * y for x, y in zip(A[r], A[c])]
    return [r[k:] for r in A]
def adjdata(rows, k):
    Rr, piv = L.rref([[F(x) for x in r] for r in rows], len(rows[0])); assert len(piv) == k
    Vp = [[rows[b][c] for c in piv] for b in range(k)]
    VpT = [[Vp[b][i] for b in range(k)] for i in range(k)]
    Iv = inv(VpT); D = 1
    for r in Iv:
        for x in r: D = lcm(D, x.denominator)
    Wm = [[int(x * D) for x in r] for r in Iv]
    for a in range(k):
        for b in range(k):
            assert sum(Wm[a][i] * Vp[b][i] for i in range(k)) == (D if a == b else 0)
    return piv, Wm, D
def rowint(r):
    D = 1
    for x in r: D = lcm(D, F(x).denominator)
    return [int(F(x) * D) for x in r]
def rl(x):
    x = F(x)
    return '(%d : ℝ)' % x.numerator if x.denominator == 1 else '(%d / %d : ℝ)' % (x.numerator, x.denominator)
def lit(rows): return 'raw_ints%% [%s]' % ', '.join(str(x) for x in rows)
def rowsdef(nm, rows): return 'def %s : List (List ℤ) := [\n  %s]' % (nm, ',\n  '.join(lit(r) for r in rows))
def hp_form(f):
    """form dict over (1,N,hp) -> Lean expr in N hp (ℤ)"""
    parts = []
    for k, nm in (('N', 'N'), ('hp', 'hp'), ('1', None)):
        v = f.get(k, F(0))
        if v == 0: continue
        assert v.denominator == 1
        parts.append('(%d) * %s' % (v, nm) if nm else '(%d)' % v)
    return ' + '.join(parts) if parts else '0'
def gen(key, out, N0, wins):
    t0 = time.time()
    sp = SP.spec(key); P = sp['P']; n, d = sp['n'], sp['d']
    res, names, ok = RG.build(key, verbose=False); assert ok, 'row spaces differ'
    assert len(names) == n
    ranks_d = P['ranks']; ranks_d = eval(ranks_d) if isinstance(ranks_d, str) else ranks_d
    rk = lambda j: int(ranks_d[str(j)] if str(j) in ranks_d else ranks_d[j])
    V = [[F(r.get(str(j), '0')) for j in range(n)] for r in P['rref']]
    Lr = L.lll(L.saturate(V, n))
    pivV, WV, dV = adjdata(Lr, d)
    charts = []
    for x in res:
        j = x['j']; rows = [rowint(r) for r in x['rows'] if any(r)]
        Mt = [[sum(r[c] * v[c] for c in range(n) if v[c] and r[c]) for r in rows] for v in Lr]
        Ku = L.kern([[F(z) for z in col] for col in zip(*Mt)], d)
        if Ku:
            Sc = L.lll(L.saturate(Ku, d))
            assert d - len(Sc) == rk(j), (j, len(Sc), rk(j))
            qp, WK, dK = adjdata(Sc, len(Sc))
        else:
            assert rk(j) == d; Sc = []; qp = []; WK = []; dK = 1
        for k in Sc:
            u = [sum(k[a] * Lr[a][c] for a in range(d)) for c in range(n)]
            for r in rows: assert sum(r[c] * u[c] for c in range(n)) == 0
        charts.append(dict(rows=rows, r=rk(j), ker=Sc, qpiv=qp, qadj=WK, qdelta=dK))
    m = len(charts)
    nm = re.sub(r'[^A-Za-z0-9_]', '_', key.replace('D58-', '').replace('|', '_'))
    ns = 'CatalanMeasure.GenD.Uniform.Bank532.Pk.' + nm
    val = sp['val']
    v2 = tuple(2 * x for x in val)
    for x in v2: assert x.denominator == 1
    v2 = tuple(int(x) for x in v2)
    Wins = []
    for (a, b, c0, c1) in wins:
        assert 2 * c0 == int(2 * c0) and 2 * c1 == int(2 * c1)
        assert v2[1] == 2 * c0 and v2[2] == 2 * c1, (key, v2, c0, c1)
        assert val[0] >= -2, ('const < -2', key, val[0])
        Wins.append((F(a), F(b), F(c0), F(c1)))
    ha = min(w[0] for w in Wins); hb = max(w[1] for w in Wins)
    bad = SP.weights_ok(sp, ha, hb, N0); assert not bad, ('weights negative', key, bad)
    bad = SP.check_domain(sp, ha, hb, N0); assert not bad, ('domain forms fail', key, bad)
    L_ = ['module', 'public import CatalanMeasure.GenD.Uniform.W.Prof.Packet', 'public import CatalanMeasure.CellCert.RawInts',
          'public import Mathlib.Tactic.IntervalCases', 'public import CatalanMeasure.GenD.Uniform.Bank532.WinHost',
          '@[expose] public section', 'set_option Elab.async false', '',
          '/-! Generated by scripts/claude/bank/g532/genpk.py for %s (n=%d, d=%d, %d charts).' % (key, n, d, m),
          '    Original (label) chart rows; V, kernel certificates; exact weights; window theorems with the host as hypothesis. -/',
          'namespace ' + ns,
          'open CatalanMeasure.CellCert CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W.Prof CatalanMeasure.GenD.Uniform.W.Charts3',
          '  CatalanMeasure.GenD.Uniform.Bank540.Ledger CatalanMeasure.GenD.Uniform.Bank540.Ledger3 CatalanMeasure.GenD.Uniform.LedgerW',
          '  CatalanMeasure.GenD.Uniform.Bank532 CatalanMeasure.Parametric OAI.InternalCatalan', 'noncomputable section', '']
    L_.append(rowsdef('vRows', Lr)); L_.append('')
    L_.append(rowsdef('vAdj', WV)); L_.append('')
    for j, c in enumerate(charts):
        L_.append(rowsdef('chRows%d' % j, c['rows'])); L_.append('')
        L_.append(rowsdef('chKer%d' % j, c['ker']) if c['ker'] else 'def chKer%d : List (List ℤ) := []' % j)
        L_.append(rowsdef('chAdj%d' % j, c['qadj']) if c['qadj'] else 'def chAdj%d : List (List ℤ) := []' % j)
        L_.append('def chPiv%d : List ℕ := %s' % (j, str(c['qpiv']))); L_.append('')
    L_.append('def vPiv : List ℕ := %s' % str(pivV)); L_.append('def vDelta : ℤ := %d' % dV)
    L_.append('def chart (j : ℕ) : Chart :=\n  match j with')
    for j, c in enumerate(charts):
        L_.append('  | %d => { rows := chRows%d, r := %d, ker := chKer%d, qpiv := chPiv%d, qadj := chAdj%d, qdelta := %d }' % (j, j, c['r'], j, j, j, c['qdelta']))
    L_.append('  | _ => { rows := [], r := 0, ker := [], qpiv := [], qadj := [], qdelta := 1 }'); L_.append('')
    L_ += ['def pk : Packet where', '  n := %d' % n, '  d := %d' % d, '  v := vRows', '  piv := vPiv', '  adj := vAdj', '  delta := vDelta',
           '  charts := (List.range %d).map chart' % m, '',
           'set_option maxRecDepth 100000', '',
           'theorem head_ok : pk.checkHead = true := by decide +kernel', '']
    for j in range(m):
        L_.append('theorem ch_ok%d : (chart %d).check pk.n pk.d pk.v = true := by decide +kernel' % (j, j))
    L_ += ['', 'theorem pk_check : pk.check = true :=', '  Packet.check_of_parts head_ok (by', '    intro c hc',
           '    simp only [pk, List.mem_map, List.mem_range] at hc', '    obtain ⟨j, hj, rfl⟩ := hc', '    interval_cases j',
           '    exacts [%s])' % ', '.join('ch_ok%d' % j for j in range(m)), '',
           'theorem pk_sound : pk.Sound := Packet.check_sound pk_check', '',
           'theorem pk_D_ne : pk.D ≠ 0 := by decide +kernel', '']
    wl = [hp_form(x['w']) for x in sp['maps']]
    L_ += ['def wInt (N p : ℕ) : List ℤ :=', '  let N : ℤ := N', '  let hp : ℤ := ((p : ℤ) - 1) / 2',
           '  [%s]' % ',\n   '.join(wl), '',
           'def wNat (g : Fin pk.charts.length) (N p : ℕ) : ℕ := ((wInt N p).getD g.val 0).toNat', '',
           'def cNat (N p : ℕ) : ℕ :=', '  let N : ℤ := N', '  let hp : ℤ := ((p : ℤ) - 1) / 2',
           '  (%s).toNat' % hp_form(sp['central']), '',
           'def ranks : List ℕ := %s' % str([x['r'] for x in sp['maps']]), '']
    na, da = ha.numerator, ha.denominator; nb, db = hb.numerator, hb.denominator
    L_ += ['/-- The hull window of the packet pieces. -/',
           'def Win (N p : ℕ) : Prop := %d ≤ N ∧ %d * N < %d * p ∧ %d * p ≤ %d * N ∧ p %% 2 = 1' % (N0, na, da, db, nb), '',
           'def Phys : Prop := PhysHost design pk Win cNat wNat', '',
           'theorem pk_len : pk.charts.length = %d := by decide +kernel' % m,
           'theorem pk_d : pk.d = %d := by decide +kernel' % d, '',
           'theorem pk_ranks (g : Fin pk.charts.length) : (pk.chart g).r = ranks.getD g.val 0 := by',
           '  obtain ⟨i, hi⟩ := g', '  rw [pk_len] at hi', '  interval_cases i <;> rfl', '',
           'theorem val2_ge {N p : ℕ} (h : Win N p) :',
           '    (%d : ℤ) + (%d) * (N : ℤ) + (%d) * (p : ℤ) ≤ 2 * ((packetVal pk cNat wNat N p : ℕ) : ℤ) := by' % v2,
           '  obtain ⟨h1, h2, h3, h4⟩ := h', '  unfold packetVal cNat',
           '  have hs : ∑ g : Fin pk.charts.length, wNat g N p * (pk.chart g).r =',
           '      ∑ i ∈ Finset.range %d, ((wInt N p).getD i 0).toNat * ranks.getD i 0 := by' % m,
           '    have e : ∑ g : Fin pk.charts.length, wNat g N p * (pk.chart g).r =',
           '        ∑ g : Fin pk.charts.length, ((wInt N p).getD g.val 0).toNat * ranks.getD g.val 0 :=',
           '      Finset.sum_congr rfl (fun g _ => by rw [pk_ranks g]; rfl)',
           '    rw [e, Fin.sum_univ_eq_sum_range',
           '      (fun i => ((wInt N p).getD i 0).toNat * ranks.getD i 0) pk.charts.length, pk_len]',
           '  rw [hs, pk_d]',
           '  simp only [Finset.sum_range_succ, Finset.sum_range_zero, wInt, ranks]',
           '  simp', '  omega', '']
    for i, (a, b, c0, c1) in enumerate(Wins):
        A, B = int(2 * c0), int(2 * c1)
        pa, qa, pb, qb = a.numerator, a.denominator, b.numerator, b.denominator
        L_ += ['theorem win_hull%d {N p : ℕ} (hN : %d ≤ N) (hp : p.Prime) (h1 : %d * N < %d * p) (h2 : %d * p ≤ %d * N) : Win N p := by' % (i, N0, pa, qa, qb, pb),
               '  rcases hp.eq_two_or_odd with rfl | hodd', '  · omega',
               '  · refine ⟨hN, ?_, ?_, hodd⟩ <;> omega', '',
               'theorem cell%d : ∀ N p : ℕ, %d ≤ N → p.Prime → %d * N < %d * p → %d * p ≤ %d * N →' % (i, N0, pa, qa, qb, pb),
               '    (%d : ℤ) * (N : ℤ) + (%d : ℤ) * (p : ℤ) ≤ ((2 : ℕ) : ℤ) * (((packetVal pk cNat wNat N p : ℕ) : ℤ) + 2) := by' % (A, B),
               '  intro N p hN hp h1 h2', '  have h := val2_ge (win_hull%d hN hp h1 h2)' % i, '  push_cast', '  omega', '',
               'theorem win%d (hP : Admissible design) (phys : Phys) :' % i,
               '    WinCert (NullityLB.ofPacketHost hP pk pk_sound Win cNat wNat phys) (cw %s %s %s %s) :=' % (rl(a), rl(b), rl(c0), rl(c1)),
               '  winCert_host_cw hP pk pk_sound pk_D_ne Win cNat wNat phys (d := 2) (A := %d) (B := %d) (N0 := %d)' % (A, B, N0),
               '    (na := %d) (da := %d) (nb := %d) (db := %d)' % (pa, qa, pb, qb),
               '    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)',
               '    (fun N p hN hp h1 h2 => win_hull%d hN hp h1 h2) cell%d' % (i, i), '']
    L_ += ['end', 'end ' + ns, '#print axioms %s.pk_sound' % ns, '#print axioms %s.pk_D_ne' % ns]
    for i in range(len(Wins)): L_.append('#print axioms %s.win%d' % (ns, i))
    open(out, 'w', encoding='utf-8').write('\n'.join(L_) + '\n')
    return dict(key=key, ns=ns, n=n, d=d, m=m, wins=[[str(x) for x in w] for w in Wins], bytes=os.path.getsize(out),
                secs=round(time.time() - t0, 1), val=[str(x) for x in val])
if __name__ == '__main__':
    key, out, N0 = sys.argv[1], sys.argv[2], int(sys.argv[3])
    wins = [tuple(F(x) for x in a.split(',')) for a in sys.argv[4:]]
    print(json.dumps(gen(key, out, N0, wins)))
