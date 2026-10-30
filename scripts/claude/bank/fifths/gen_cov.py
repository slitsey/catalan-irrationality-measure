"""Fifths no-UF template + piece covers -> Lean (lane B, B5c).
Usage: gen_cov.py [N]    (needs nouf-meta.json from profile2.py)
Writes Bank/FifthsContent/{Profile/J1..J4, Prefix/P*, Covers/J1..J4, Covers/P*}.lean.
Pieces are `mkPiece sn sd tn td A B E D` (C = C0 = E/D).  Each piece gets a theorem
`PieceOK T depth j sn sd tn td A B E D` proved by one of the kinds of Cov.lean (omega on numerals).
LP pieces are left as hypotheses `hLP*` of the dispatcher."""
from pathlib import Path
from fractions import Fraction as Q
from math import lcm
import json, sys
NL = chr(10)
R = Path(r'C:\Users\seanl\Documents\Codex\2026-10-11\plea\work\catalan-uniform')
B = R / 'CatalanCore/Uniform/Bank/FifthsContent'
S = R / 'scripts/claude/bank/fifths'
N = int(sys.argv[1]) if len(sys.argv) > 1 else 100
C0 = 2600000000 if N <= 100 else 27800000000
CH = 33
al = Q(1, 9)
NS = 'CatalanCore.Uniform.Bank.FifthsContent'
meta = json.loads((S / 'nouf-meta.json').read_text())
classes = meta['classes']
TEND = Q(63, 10)

for d in ('Profile', 'Prefix', 'Covers'):
    (B / d).mkdir(parents=True, exist_ok=True)


def pdata(left, right, a0, b0):
    left, right, a0, b0 = Q(left), Q(right), Q(a0), Q(b0)
    D = lcm(a0.denominator, b0.denominator)
    return (left.numerator, left.denominator, right.numerator, right.denominator,
            int(a0 * D), int(b0 * D), C0 * D, D)


def mk(args):
    sn, sd, tn, td, A, Bc, E, D = args
    return 'mkPiece %d %d %d %d (%d) (%d) (%d) (%d)' % (sn, sd, tn, td, A, Bc, E, D)


def qf(x):
    return '(%d / %d)' % (x.numerator, x.denominator)


HDR = ('import CatalanCore.Uniform.Content.Member.Template' + NL +
       'import CatalanCore.Arith.Hybrid.PieceTools' + NL +
       'set_option Elab.async false' + NL + 'set_option maxRecDepth 10000' + NL +
       'set_option maxHeartbeats 1600000' + NL +
       'namespace ' + NS + NL + 'open CatalanCore.Arith.Hybrid' + NL)


def leaf_def(name, start, end, pieces, doc=''):
    rows = (',' + NL).join('  ' + mk(a) for a in pieces)
    mass = sum((Q(a[4], a[7]) * (Q(a[2], a[3]) - Q(a[0], a[1])) +
                Q(a[5], a[7]) * (Q(a[2], a[3]) ** 2 - Q(a[0], a[1]) ** 2) / 2 for a in pieces), Q(0))
    t = HDR + doc + 'noncomputable def %s : List Piece := [%s%s]%s%s' % (name, NL, rows, NL, NL)
    t += 'def %sMass : ℚ := %s%s' % (name, qf(mass), NL)
    t += 'theorem %s_chain : Chain %s %s := by%s  norm_num [%s, Chain, mkPiece]%s' % (name, qf(start), name, NL, name, NL)
    t += 'theorem %s_end : lastEnd %s %s = %s := by%s  norm_num [%s, lastEnd, mkPiece]%s' % (name, qf(start), name, qf(end), NL, name, NL)
    t += 'theorem %s_mass : listInt %s = (%sMass : ℝ) := by%s  norm_num [%s, listInt, Piece.int, %sMass, mkPiece]%s' % (name, name, name, NL, name, name, NL)
    for suf in ('chain', 'end', 'mass'):
        t += '#print axioms %s_%s%s' % (name, suf, NL)
    t += 'end ' + NS + NL
    return t, mass


# ---------------- profile pieces ----------------
prof = {}
for jk, c in classes.items():
    j = int(jk)
    pcs = []
    for p in c['pieces']:
        pcs.append(dict(layer=p['layer'], meta=p.get('meta'), args=pdata(p['left'], p['right'], p['line'][0], p['line'][1])))
    last = pcs[-1]['args']
    assert Q(last[2], last[3]) == Q(55, 9), (j, last)
    pcs.append(dict(layer='T', meta=dict(kind='D6'), args=pdata(Q(55, 9), TEND, 0, 0)))
    prof[j] = pcs
profmass = {}
for j, pcs in prof.items():
    txt, mass = leaf_def('profile%d' % j, al, TEND, [p['args'] for p in pcs],
                         '/-- No-UF strict envelope min(T, LP, M3D) for the pole index `j = %d`, then zero. -/%s' % (j, NL))
    (B / ('Profile/J%d.lean' % j)).write_text(txt, encoding='utf-8')
    profmass[j] = mass

# ---------------- prefix pieces ----------------
pre = []
for n in range(N - 1, 0, -1):
    u = al / (n + 1); v = 2 * al / (2 * n + 1); w = al / n
    pre.append(dict(args=pdata(u, v, 2 + 3 * al, -(n + 1)), q0=n - 1))
    pre.append(dict(args=pdata(v, w, 2 + al, n), q0=n - 1))
nleaf = (len(pre) + CH - 1) // CH
premass = []; leafspan = []
for ci in range(nleaf):
    ps = pre[ci * CH:(ci + 1) * CH]
    st = Q(ps[0]['args'][0], ps[0]['args'][1]); en = Q(ps[-1]['args'][2], ps[-1]['args'][3])
    txt, mass = leaf_def('prefix%d' % ci, st, en, [p['args'] for p in ps])
    (B / ('Prefix/P%d.lean' % ci)).write_text(txt, encoding='utf-8')
    premass.append(mass); leafspan.append((st, en))
assert leafspan[-1][1] == al
t1 = al / N
a0 = 2 + 2 * al
pre0 = a0 * t1
Lfin = pre0 + sum(premass, Q(0)) + sum(profmass.values(), Q(0)) / 4
D5 = Q(4826561916291581150063627, 1265625000000000000000000)
c5 = Q(2239239458955067, 312500000000000)
mu = c5 / (D5 - Lfin)
BOUND = Q(243052, 10000)
assert mu < BOUND, (float(mu), float(BOUND))
(S / 'finite.json').write_text(json.dumps(dict(N=N, leaves=nleaf, Lfin=str(Lfin), mu=float(mu), bound=str(BOUND),
                                               pre0=str(pre0), t1=str(t1), C0=C0), indent=1))
print('N', N, 'Lfin', float(Lfin), 'mu', float(mu), 'prefix leaves', nleaf)


# ---------------- covers ----------------
def num4():
    return '(by norm_num) (by norm_num) (by norm_num) (by norm_num)'


def head_j(name, j, args, extra_j=False, dep=False):
    sn, sd, tn, td, A, Bc, E, D = args
    h = 'theorem %s {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49)' % name
    if dep:
        h += ' (hdepth : depth ≤ 1000)'
    if extra_j:
        h += ' (j : ℕ)'
    h += ' :' + NL
    h += '    PieceOK T depth %s %d %d %d %d (%d) (%d) (%d) (%d) := by%s' % ('j' if extra_j else str(j), sn, sd, tn, td, A, Bc, E, D, NL)
    return h


def piece_proof(name, j, args, layer, meta):
    sn, sd, tn, td, A, Bc, E, D = args
    nn = '(by intro r p h1 h2; omega)'
    if layer == 'M3D':
        n0, n1, n3 = meta['n0'], meta['n1'], meta['n3']
        return head_j(name, j, args) + (
            '  refine pieceOK_m3 T depth hcF %d %d %d %d %d %d %d %d _ _ _ _ %s %s ?_%s' % (n0, n1, n3, j, sn, sd, tn, td, num4(), nn, NL) +
            '  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2' + NL + '  unfold R0 at hR' + NL +
            '  exact ⟨by omega, by omega⟩' + NL)
    if layer == 'LP':
        lpk = 'pieceOK_lp1' if Q(tn, td) <= 1 else 'pieceOK_lp2'
        return head_j(name, j, args, False, True) + (
            '  refine %s T depth hcF hdepth %d %d %d %d %d _ _ _ _ %s %s ?_%s' % (lpk, j, sn, sd, tn, td, num4(), nn, NL) +
            '  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2' + NL + '  unfold R0 at hR' + NL +
            ('  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩ <;> omega' + NL if lpk == 'pieceOK_lp1' else
             '  refine ⟨fun hlt => ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩, fun hge => ⟨⟨?_, ?_⟩, ?_⟩⟩ <;> omega' + NL))
    kd = meta['kind'] or 'D6'
    if kd in ('saw0', 'saw', 'D3'):
        return head_j(name, j, args) + (
            '  refine pieceOK_saw T depth hcF 0 %d %d %d %d %d _ _ _ _ %s %s ?_%s' % (j, sn, sd, tn, td, num4(), nn, NL) +
            '  intro r p m hR hb1 hb2 h1 h2' + NL + '  unfold R0 at hR' + NL +
            '  refine ⟨⟨by omega, by omega⟩, ?_⟩' + NL + '  intro s0 hs0 hd' + NL + '  omega' + NL)
    k2 = {'D3': 'pieceOK_D3', 'D45': 'pieceOK_D45', 'D45z': 'pieceOK_D45', 'D6': 'pieceOK_D6'}[kd]
    return head_j(name, j, args) + (
        '  refine %s T depth hcF %d %d %d %d %d _ _ _ _ %s %s ?_%s' % (k2, j, sn, sd, tn, td, num4(), nn, NL) +
        '  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2' + NL + '  unfold R0 at hR' + NL +
        '  exact ⟨⟨by omega, by omega⟩, by omega⟩' + NL)


def piece_proof_saw(name, args, q0):
    sn, sd, tn, td, A, Bc, E, D = args
    return head_j(name, 0, args, True) + (
        '  refine pieceOK_saw T depth hcF %d j %d %d %d %d _ _ _ _ %s (by intro r p h1 h2; omega) ?_%s' % (q0, sn, sd, tn, td, num4(), NL) +
        '  intro r p m hR hb1 hb2 h1 h2' + NL + '  unfold R0 at hR' + NL +
        '  refine ⟨⟨by omega, by omega⟩, ?_⟩' + NL + '  intro s0 hs0 hd' + NL + '  omega' + NL)


def cover_header(extra_imp):
    return ('import %s.Cov%s' % (NS, NL) + extra_imp +
            'set_option Elab.async false' + NL + 'set_option maxRecDepth 10000' + NL +
            'set_option maxHeartbeats 1600000' + NL +
            'namespace %s%sopen CatalanCore CatalanCore.Arith.Hybrid CatalanFrames.Fifths%s%s' % (NS, NL, NL, NL))


for j, pcs in prof.items():
    out = cover_header('import %s.Profile.J%d%simport %s.LP%s' % (NS, j, NL, NS, NL))
    plist = []
    for idx, p in enumerate(pcs):
        nm = 'pJ%d_%d' % (j, idx)
        out += piece_proof(nm, j, p['args'], p['layer'], p['meta']) + NL
        plist.append((nm, p['layer']))
    out += 'theorem covProfile%d {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (hdepth : depth ≤ 1000) :%s' % (j, NL)
    out += '    ∀ P ∈ profile%d, CovP T depth %d P := by%s' % (j, j, NL)
    out += '  intro P hP' + NL + '  simp only [profile%d, List.mem_cons, List.mem_nil_iff, or_false] at hP%s' % (j, NL)
    out += '  rcases hP with ' + ' | '.join('rfl' for _ in plist) + NL
    for lem, lay in plist:
        extra = ' hdepth' if lay == 'LP' else ''
        out += '  · exact covP_mk T depth %d _ _ _ _ _ _ _ _ (by norm_num) (%s T depth hcF%s)%s' % (j, lem, extra, NL)
    out += NL + '#print axioms covProfile%d%send %s%s' % (j, NL, NS, NL)
    (B / ('Covers/J%d.lean' % j)).write_text(out, encoding='utf-8')

for ci in range(nleaf):
    ps = pre[ci * CH:(ci + 1) * CH]
    out = cover_header('import %s.Prefix.P%d%s' % (NS, ci, NL))
    names = []
    for idx, p in enumerate(ps):
        nm = 'pP%d_%d' % (ci, idx)
        out += piece_proof_saw(nm, p['args'], p['q0']) + NL
        names.append(nm)
    out += 'theorem covPrefix%d {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (j : ℕ) :%s' % (ci, NL)
    out += '    ∀ P ∈ prefix%d, CovP T depth j P := by%s' % (ci, NL)
    out += '  intro P hP' + NL + '  simp only [prefix%d, List.mem_cons, List.mem_nil_iff, or_false] at hP%s' % (ci, NL)
    out += '  rcases hP with ' + ' | '.join('rfl' for _ in names) + NL
    for nm in names:
        out += '  · exact covP_mk T depth j _ _ _ _ _ _ _ _ (by norm_num) (%s T depth hcF j)%s' % (nm, NL)
    out += NL + '#print axioms covPrefix%d%send %s%s' % (ci, NL, NS, NL)
    (B / ('Covers/P%d.lean' % ci)).write_text(out, encoding='utf-8')
print('written')

# ---------------- Full.lean: full template lists ----------------
imps = NL.join(['import %s.Prefix.P%d' % (NS, i) for i in range(nleaf)] +
               ['import %s.Profile.J%d' % (NS, j) for j in (1, 2, 3, 4)])
nest = 'profileOf j'
for i in reversed(range(nleaf)):
    nest = 'prefix%d ++ (%s)' % (i, nest)
mass_sum = ' + '.join('prefix%dMass' % i for i in range(nleaf))
chain_pf = ''.join('  rw [chain_app]' + NL + '  refine ⟨prefix%d_chain, ?_⟩' % i + NL + '  rw [prefix%d_end]' % i + NL for i in range(nleaf))
end_pf = ''.join('  rw [lastEnd_app, prefix%d_end]' % i + NL for i in range(nleaf))
mass_simp = ', '.join(['listInt_app'] + ['prefix%d_mass' % i for i in range(nleaf)])
t1q = qf(t1)
full = (imps + NL + 'import CatalanCore.Uniform.Content.Member.Template' + NL +
        'set_option Elab.async false' + NL + 'set_option maxRecDepth 10000' + NL +
        'set_option maxHeartbeats 1600000' + NL +
        'namespace %s%sopen CatalanCore.Arith.Hybrid CatalanCore.Uniform.Content.Member%s%s' % (NS, NL, NL, NL) +
        '''theorem chain_app : ∀ (l1 l2 : List Piece) (s0 : ℝ),
    Chain s0 (l1 ++ l2) ↔ Chain s0 l1 ∧ Chain (lastEnd s0 l1) l2
  | [], l2, s0 => by simp [Chain, lastEnd]
  | P :: l, l2, s0 => by
    simp only [List.cons_append, Chain, lastEnd]
    rw [chain_app l l2 P.t]
    tauto

theorem lastEnd_app : ∀ (l1 l2 : List Piece) (s0 : ℝ),
    lastEnd s0 (l1 ++ l2) = lastEnd (lastEnd s0 l1) l2
  | [], l2, s0 => by simp [lastEnd]
  | P :: l, l2, s0 => by simp only [List.cons_append, lastEnd]; exact lastEnd_app l l2 P.t

theorem listInt_app : ∀ (l1 l2 : List Piece), listInt (l1 ++ l2) = listInt l1 + listInt l2
  | [], l2 => by simp [listInt]
  | P :: l, l2 => by simp only [List.cons_append, listInt]; rw [listInt_app l l2]; ring

/-- The class envelope of the pole index `j` (`j = 1, 2, 3, 4`). -/
noncomputable def profileOf : ℕ → List Piece
  | 1 => profile1
  | 2 => profile2
  | 3 => profile3
  | _ => profile4

def profileMass : ℕ → ℚ
  | 1 => profile1Mass
  | 2 => profile2Mass
  | 3 => profile3Mass
  | _ => profile4Mass

theorem profileOf_chain (j : ℕ) : Chain (1 / 9) (profileOf j) := by
  match j with
  | 1 => exact profile1_chain
  | 2 => exact profile2_chain
  | 3 => exact profile3_chain
  | n + 4 => exact profile4_chain
  | 0 => exact profile4_chain

theorem profileOf_end (j : ℕ) : lastEnd (1 / 9) (profileOf j) = (63 / 10) := by
  match j with
  | 1 => exact profile1_end
  | 2 => exact profile2_end
  | 3 => exact profile3_end
  | n + 4 => exact profile4_end
  | 0 => exact profile4_end

theorem profileOf_mass (j : ℕ) : listInt (profileOf j) = (profileMass j : ℝ) := by
  match j with
  | 1 => exact profile1_mass
  | 2 => exact profile2_mass
  | 3 => exact profile3_mass
  | n + 4 => exact profile4_mass
  | 0 => exact profile4_mass

/-- Sawtooth prefix on `[1/(9N), 1/9]`, the class envelope, and the zero tail. -/
noncomputable def fullList (j : ℕ) : List Piece := ''' + nest + NL + NL +
        'def prefixMass : ℚ := ' + mass_sum + NL + NL +
        '')
# simpler: write the proofs by hand-built strings
fl_chain = ('theorem fullList_chain (j : ℕ) : Chain %s (fullList j) := by%s  unfold fullList%s' % (t1q, NL, NL) + chain_pf +
            '  exact profileOf_chain j' + NL)
fl_end = ('theorem fullList_end (j : ℕ) : lastEnd %s (fullList j) = (63 / 10) := by%s  unfold fullList%s' % (t1q, NL, NL) + end_pf +
          '  exact profileOf_end j' + NL)
fl_mass = ('theorem fullList_mass (j : ℕ) : listInt (fullList j) = ((prefixMass + profileMass j : ℚ) : ℝ) := by%s  unfold fullList%s' % (NL, NL) +
           '  simp only [%s]%s  rw [profileOf_mass j]%s  push_cast [prefixMass]%s  ring%s' % (mass_simp, NL, NL, NL, NL))
head_full = full
tmpl_txt = '''
/-- The class template of the pole index `j` (constant `20/9` on `(0, 1/(9N)]`). -/
noncomputable def tmplJ (j : ℕ) : Template where
  α0 := 20 / 9
  t1 := %s
  l := fullList j
  hα0 := by norm_num
  ht1 := by norm_num
  chain := fullList_chain j

theorem tmplJ_tend (j : ℕ) : (tmplJ j).tend = 63 / 10 := fullList_end j

theorem tmplJ_mass (j : ℕ) :
    (tmplJ j).mass = (((20 / 9) * %s + prefixMass + profileMass j : ℚ) : ℝ) := by
  unfold Template.mass tmplJ
  simp only
  rw [fullList_mass j]
  push_cast
  ring

theorem mem_fullList {j : ℕ} {P : Piece} (h : P ∈ fullList j) :
    %s ∨ P ∈ profileOf j := by
  unfold fullList at h
  simp only [List.mem_append] at h
  tauto

#print axioms fullList_chain
#print axioms fullList_end
#print axioms tmplJ_mass
end %s
''' % (t1q, t1q, ' ∨ '.join('P ∈ prefix%d' % i for i in range(nleaf)), NS)
(B / 'Full.lean').write_text(head_full + fl_chain + NL + fl_end + NL + fl_mass + tmpl_txt, encoding='utf-8')
print('Full written')

# ---------------- LamFin5, LPHyp ----------------
unf = ', '.join(['prefix%dMass' % i for i in range(nleaf)] + ['profile%dMass' % j for j in (1, 2, 3, 4)] + ['prefixMass', 'profileMass'])
lam_txt = (NL + 'def LamFin5 : ℚ := %s' % qf(Lfin) + NL + NL +
           'theorem LamFin5_eq : (20 / 9) * %s + prefixMass + (profileMass 1 + profileMass 2 + profileMass 3 + profileMass 4) / 4 = LamFin5 := by%s  norm_num [%s, LamFin5]%s' % (t1q, NL, unf, NL))
txt = (B / 'Full.lean').read_text(encoding='utf-8')
txt = txt.replace('#print axioms fullList_chain', lam_txt + NL + '#print axioms fullList_chain', 1)
(B / 'Full.lean').write_text(txt, encoding='utf-8')
print('LamFin5 written')
