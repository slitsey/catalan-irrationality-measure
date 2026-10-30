"""Fifths UF-stage template + piece covers -> Lean (lane B, B5c).
Usage: gen_uf.py    (needs uf-meta.json from `profile2.py uf`; reuses the Prefix leaves of gen_cov.py with N = 100)
Writes Bank/FifthsContent/{ProfileUF/J1..J4, CoversUF/J1..J4, FullUF}.lean."""
import sys
sys.path.insert(0, str(__import__('pathlib').Path(__file__).resolve().parent))
from genlib import *

N = 100
CH = 33
meta = json.loads((S / 'uf-meta.json').read_text())
classes = meta['classes']
for d in ('ProfileUF', 'CoversUF'):
    (B / d).mkdir(parents=True, exist_ok=True)


def piece_proof_S(name, j, args, m):
    sn, sd, tn, td, A, Bc, E, D = args
    kap = 'true' if m['kappa'] else 'false'
    zet = 'true' if m['zeta'] else 'false'
    q = m['q']
    nn = '(by intro r p h1 h2; omega)'
    return head_j(name, j, args, False, True) + (
        '  refine pieceOK_S T depth hcF hdepth %s %s %d %d %d %d %d _ _ _ _ %s %s ?_%s' % (kap, zet, j, sn, sd, tn, td, num4(), nn, NL) +
        '  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2' + NL + '  unfold R0 at hR' + NL +
        '  have hqa : %d * p ≤ r := by omega%s' % (q, NL) +
        '  have hqb : r < (%d + 1) * p := by omega%s' % (q, NL) +
        '  have hp0 : 0 < p := by omega' + NL +
        '  obtain ⟨hdq, hms⟩ := div_mod_of r p %d hqa hqb%s' % (q, NL) +
        '  refine ⟨⟨by omega, by omega, by omega⟩, ?_⟩' + NL +
        '  have hok : CandOK m r p k %s %s := by%s' % (kap, zet, NL) +
        '    simp [CandOK, candB, candL, candU, candUb, hdq, hms] <;> omega' + NL +
        '  rw [candPrice, if_pos hok]' + NL +
        '  simp [closedBound, beta3, ovl, candB, candL, candU, candUb, hdq, hms] <;> omega' + NL)


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
    txt, mass = leaf_def('profileU%d' % j, al, TEND, [p['args'] for p in pcs],
                         '/-- UF strict envelope min(T, S, LP, M3D) for the pole index `j = %d`, then zero. -/%s' % (j, NL))
    (B / ('ProfileUF/J%d.lean' % j)).write_text(txt, encoding='utf-8')
    profmass[j] = mass

# prefix mass (the Prefix leaves are those of gen_cov.py, N = 100)
premass = Q(0)
for n in range(N - 1, 0, -1):
    u = al / (n + 1); v = 2 * al / (2 * n + 1); w = al / n
    premass += (2 + 3 * al - (n + 1) * (u + v) / 2) * (v - u) + (2 + al + n * (v + w) / 2) * (w - v)
t1 = al / N
pre0 = (2 + 2 * al) * t1
Lfin = pre0 + premass + sum(profmass.values(), Q(0)) / 4
D5 = Q(4826561916291581150063627, 1265625000000000000000000)
c5 = Q(2239239458955067, 312500000000000)
mu = c5 / (D5 - Lfin)
BOUND = Q(59983, 2500)
assert mu < BOUND, (float(mu), float(BOUND))
(S / 'finite-uf.json').write_text(json.dumps(dict(N=N, Lfin=str(Lfin), mu=float(mu), bound=str(BOUND)), indent=1))
print('UF finite Lambda', float(Lfin), 'mu', float(mu))

# ---------------- covers ----------------
for j, pcs in prof.items():
    out = cover_header('import %s.ProfileUF.J%d%simport %s.LP%simport %s.UF%s' % (NS, j, NL, NS, NL, NS, NL))
    plist = []
    for idx, p in enumerate(pcs):
        nm = 'pU%d_%d' % (j, idx)
        if p['layer'] == 'S':
            out += piece_proof_S(nm, j, p['args'], p['meta']['cand']) + NL
        else:
            out += piece_proof(nm, j, p['args'], p['layer'], p['meta']) + NL
        plist.append((nm, p['layer']))
    out += 'theorem covProfileU%d {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) (hdepth : depth ≤ 1000) :%s' % (j, NL)
    out += '    ∀ P ∈ profileU%d, CovP T depth %d P := by%s' % (j, j, NL)
    out += '  intro P hP' + NL + '  simp only [profileU%d, List.mem_cons, List.mem_nil_iff, or_false] at hP%s' % (j, NL)
    out += '  rcases hP with ' + ' | '.join('rfl' for _ in plist) + NL
    for lem, lay in plist:
        extra = ' hdepth' if lay in ('LP', 'S') else ''
        out += '  · exact covP_mk T depth %d _ _ _ _ _ _ _ _ (by norm_num) (%s T depth hcF%s)%s' % (j, lem, extra, NL)
    out += NL + '#print axioms covProfileU%d%send %s%s' % (j, NL, NS, NL)
    (B / ('CoversUF/J%d.lean' % j)).write_text(out, encoding='utf-8')

# ---------------- FullUF.lean ----------------
nleaf = 6
imps = NL.join(['import %s.Full' % NS] + ['import %s.ProfileUF.J%d' % (NS, j) for j in (1, 2, 3, 4)])
nest = 'profileOfU j'
for i in reversed(range(nleaf)):
    nest = 'prefix%d ++ (%s)' % (i, nest)
chain_pf = ''.join('  rw [chain_app]' + NL + '  refine ⟨prefix%d_chain, ?_⟩' % i + NL + '  rw [prefix%d_end]' % i + NL for i in range(nleaf))
end_pf = ''.join('  rw [lastEnd_app, prefix%d_end]' % i + NL for i in range(nleaf))
mass_simp = ', '.join(['listInt_app'] + ['prefix%d_mass' % i for i in range(nleaf)])
t1q = qf(t1)
unf = ', '.join(['prefix%dMass' % i for i in range(nleaf)] + ['profileU%dMass' % j for j in (1, 2, 3, 4)] + ['prefixMass', 'profileMassU'])
txt = (imps + NL + 'set_option Elab.async false' + NL + 'set_option maxRecDepth 10000' + NL + 'set_option maxHeartbeats 1600000' + NL +
       'namespace %s%sopen CatalanCore.Arith.Hybrid CatalanCore.Uniform.Content.Member%s%s' % (NS, NL, NL, NL))
txt += '''noncomputable def profileOfU : ℕ → List Piece
  | 1 => profileU1
  | 2 => profileU2
  | 3 => profileU3
  | _ => profileU4

def profileMassU : ℕ → ℚ
  | 1 => profileU1Mass
  | 2 => profileU2Mass
  | 3 => profileU3Mass
  | _ => profileU4Mass

theorem profileOfU_chain (j : ℕ) : Chain (1 / 9) (profileOfU j) := by
  match j with
  | 1 => exact profileU1_chain
  | 2 => exact profileU2_chain
  | 3 => exact profileU3_chain
  | n + 4 => exact profileU4_chain
  | 0 => exact profileU4_chain

theorem profileOfU_end (j : ℕ) : lastEnd (1 / 9) (profileOfU j) = (63 / 10) := by
  match j with
  | 1 => exact profileU1_end
  | 2 => exact profileU2_end
  | 3 => exact profileU3_end
  | n + 4 => exact profileU4_end
  | 0 => exact profileU4_end

theorem profileOfU_mass (j : ℕ) : listInt (profileOfU j) = (profileMassU j : ℝ) := by
  match j with
  | 1 => exact profileU1_mass
  | 2 => exact profileU2_mass
  | 3 => exact profileU3_mass
  | n + 4 => exact profileU4_mass
  | 0 => exact profileU4_mass

noncomputable def fullListU (j : ℕ) : List Piece := ''' + nest + NL + NL
txt += 'theorem fullListU_chain (j : ℕ) : Chain %s (fullListU j) := by%s  unfold fullListU%s' % (t1q, NL, NL) + chain_pf + '  exact profileOfU_chain j' + NL + NL
txt += 'theorem fullListU_end (j : ℕ) : lastEnd %s (fullListU j) = (63 / 10) := by%s  unfold fullListU%s' % (t1q, NL, NL) + end_pf + '  exact profileOfU_end j' + NL + NL
txt += ('theorem fullListU_mass (j : ℕ) : listInt (fullListU j) = ((prefixMass + profileMassU j : ℚ) : ℝ) := by%s  unfold fullListU%s' % (NL, NL) +
        '  simp only [%s]%s  rw [profileOfU_mass j]%s  push_cast [prefixMass]%s  ring%s%s' % (mass_simp, NL, NL, NL, NL, NL))
txt += '''noncomputable def tmplJU (j : ℕ) : Template where
  α0 := 20 / 9
  t1 := %s
  l := fullListU j
  hα0 := by norm_num
  ht1 := by norm_num
  chain := fullListU_chain j

theorem tmplJU_tend (j : ℕ) : (tmplJU j).tend = 63 / 10 := fullListU_end j

theorem tmplJU_mass (j : ℕ) :
    (tmplJU j).mass = (((20 / 9) * %s + prefixMass + profileMassU j : ℚ) : ℝ) := by
  unfold Template.mass tmplJU
  simp only
  rw [fullListU_mass j]
  push_cast
  ring

theorem mem_fullListU {j : ℕ} {P : Piece} (h : P ∈ fullListU j) :
    %s ∨ P ∈ profileOfU j := by
  unfold fullListU at h
  simp only [List.mem_append] at h
  tauto

def LamFinU : ℚ := %s

theorem LamFinU_eq : (20 / 9) * %s + prefixMass + (profileMassU 1 + profileMassU 2 + profileMassU 3 + profileMassU 4) / 4 = LamFinU := by
  norm_num [%s, LamFinU]

#print axioms fullListU_chain
#print axioms tmplJU_mass
end %s
''' % (t1q, t1q, ' ∨ '.join('P ∈ prefix%d' % i for i in range(nleaf)), qf(Lfin), t1q, unf, NS)
(B / 'FullUF.lean').write_text(txt, encoding='utf-8')
print('UF written')
