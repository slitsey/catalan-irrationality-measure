"""Fifths no-UF finite template data -> Lean (lane B, B5c).  Usage: gen_profile_lean.py [N]
Writes Bank/FifthsContent/{Profile/C1,C3,C7,C9, Prefix/P0.., Tmpl, FiniteRate}.lean from nouf-profile.json (profile.py).
Template per unit class of ZMod 10: constant prefix 20/9 on (0, 1/(9N)], sawtooth prefix, then the exact envelope."""
from pathlib import Path
from fractions import Fraction as Q
import json, sys
R = Path(r'C:\Users\seanl\Documents\Codex\2026-10-11\plea\work\catalan-uniform')
B = R / 'CatalanCore/Uniform/Bank/FifthsContent'
S = R / 'scripts/claude/bank/fifths'
N = int(sys.argv[1]) if len(sys.argv) > 1 else 100
BOUND = Q(sys.argv[2]) if len(sys.argv) > 2 else Q(243052, 10000)
CH = 33
al = Q(1, 9)
NS = 'CatalanCore.Uniform.Bank.FifthsContent'


def q(x):
    x = Q(x)
    return f'({x.numerator} / {x.denominator})'


HDR = '''import CatalanCore.Uniform.Content.Member.Template
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace ''' + NS + '''
open CatalanCore.Arith.Hybrid
'''
(B / 'Profile').mkdir(parents=True, exist_ok=True)
(B / 'Prefix').mkdir(parents=True, exist_ok=True)
d = json.loads((S / 'nouf-profile.json').read_text())
right = Q(d['right'])


def leaf(name, start, end, rows, mass, doc=''):
    txt = HDR + doc + f'noncomputable def {name} (C0 : ℝ) : List Piece := [\n' + ',\n'.join(rows) + ']\n'
    txt += f'\ndef {name}Mass : ℚ := {q(mass)}\n'
    txt += f'''theorem {name}_chain (C0 : ℝ) (hC : 0 ≤ C0) : Chain {q(start)} ({name} C0) := by
  norm_num [{name}, Chain, hC]
theorem {name}_end (C0 : ℝ) : lastEnd {q(start)} ({name} C0) = {q(end)} := by
  norm_num [{name}, lastEnd]
theorem {name}_mass (C0 : ℝ) : listInt ({name} C0) = ({name}Mass : ℝ) := by
  norm_num [{name}, listInt, Piece.int, {name}Mass]
#print axioms {name}_chain
#print axioms {name}_end
#print axioms {name}_mass
end {NS}
'''
    return txt


pm = {}
for c in d['classes']:
    n = c['prime_class']
    rows = ['  { s := ' + q(p['left']) + ', t := ' + q(p['right']) + ', α := ' + q(p['line'][0]) +
            ', β := ' + q(p['line'][1]) + ', C := C0 }' for p in c['pieces']]
    (B / f'Profile/C{n}.lean').write_text(
        leaf(f'profile{n}', al, right, rows, Q(c['mass']),
             f'/-- No-UF strict envelope min(T,R,LP,M3D), prime class {n} mod 10. -/\n'), encoding='utf-8')
    pm[n] = Q(c['mass'])

pcs = []
for n in range(N - 1, 0, -1):
    u = al / (n + 1); v = 2 * al / (2 * n + 1); w = al / n
    pcs.extend([(u, v, 2 + 3 * al, Q(-n - 1)), (v, w, 2 + al, Q(n))])
nleaf = (len(pcs) + CH - 1) // CH
masses = []; ends = []
for ci in range(nleaf):
    ps = pcs[ci * CH:(ci + 1) * CH]
    mass = sum((A * (v - u) + bb * (v * v - u * u) / 2 for u, v, A, bb in ps), Q(0))
    masses.append(mass); ends.append((ps[0][0], ps[-1][1]))
    rows = ['  { s := ' + q(u) + ', t := ' + q(v) + ', α := ' + q(A) + ', β := ' + q(bb) + ', C := C0 }'
            for u, v, A, bb in ps]
    (B / f'Prefix/P{ci}.lean').write_text(leaf(f'prefix{ci}', ps[0][0], ps[-1][1], rows, mass), encoding='utf-8')
assert ends[-1][1] == al
t1 = al / N
a0 = 2 + 2 * al
pre0 = a0 * t1
Lfin = pre0 + sum(masses, Q(0)) + sum(pm.values(), Q(0)) / 4
D = Q(4826561916291581150063627, 1265625000000000000000000)
C = Q(2239239458955067, 312500000000000)
mu = C / (D - Lfin)
assert mu < BOUND, (float(mu), float(BOUND))
(S / 'finite.json').write_text(json.dumps(dict(N=N, leaves=nleaf, Lfin=str(Lfin), mu=float(mu), bound=str(BOUND),
                                               pre0=str(pre0), t1=str(t1)), indent=1))

imps = '\n'.join([f'import {NS}.Prefix.P{i}' for i in range(nleaf)] +
                 [f'import {NS}.Profile.C{n}' for n in (1, 3, 7, 9)])
full = ' ++ ('.join(f'prefix{i} C0' for i in range(nleaf)) + ' ++ (prof C0' + ')' * nleaf
# right nested: prefix0 ++ (prefix1 ++ (... ++ (prefixK ++ prof C0)))
nest = 'prof C0'
for i in reversed(range(nleaf)):
    nest = f'prefix{i} C0 ++ ({nest})' if i < nleaf else nest
chain_pf = f'''  unfold fullList
'''
for i in range(nleaf):
    chain_pf += f'  rw [chain_app]\n  refine ⟨prefix{i}_chain C0 hC, ?_⟩\n  rw [prefix{i}_end]\n'
chain_pf += '  exact hprof\n'
mass_sum = ' + '.join(f'prefix{i}Mass' for i in range(nleaf))
mass_pf = '  unfold fullList\n  simp only [' + ', '.join(['listInt_app'] + [f'prefix{i}_mass' for i in range(nleaf)]) + ']\n  rw [hprof]\n  push_cast [prefixMass]\n  ring\n'
end_pf = ''.join('  rw [lastEnd_app, prefix%d_end]'%i + chr(10) for i in range(nleaf)) + '  exact hprof' + chr(10)
unf = ', '.join([f'prefix{i}Mass' for i in range(nleaf)]+[f'profile{n}Mass' for n in (1,3,7,9)]+['prefixMass','LamFin5'])
lam_def = f'def LamFin5 : ℚ := {q(Lfin)}'
tm = f'''{imps}
import CatalanCore.Uniform.Bank.Fifths.Final
import CatalanCore.Uniform.Bank.FifthsContent.Units10
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace {NS}
open CatalanCore.Arith.Hybrid CatalanCore.Uniform.Content.Member

theorem chain_app : ∀ (l1 l2 : List Piece) (s0 : ℝ),
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

/-- Sawtooth prefix on `[1/(9N), 1/9]` followed by the class envelope `prof C0`. -/
noncomputable def fullList (prof : ℝ → List Piece) (C0 : ℝ) : List Piece := {nest}

def prefixMass : ℚ := {mass_sum}

theorem fullList_chain (prof : ℝ → List Piece) (C0 : ℝ) (hC : 0 ≤ C0) (hprof : Chain (1 / 9) (prof C0)) :
    Chain {q(t1)} (fullList prof C0) := by
{chain_pf}
theorem fullList_end (prof : ℝ → List Piece) (C0 : ℝ) (hC : 0 ≤ C0) (e : ℝ)
    (hprof : lastEnd (1 / 9) (prof C0) = e) : lastEnd {q(t1)} (fullList prof C0) = e := by
  unfold fullList
{end_pf}
theorem fullList_mass (prof : ℝ → List Piece) (C0 : ℝ) (m : ℚ) (hprof : listInt (prof C0) = (m : ℝ)) :
    listInt (fullList prof C0) = ((prefixMass + m : ℚ) : ℝ) := by
{mass_pf}
/-- The class template (constant `20/9` on `(0, 1/(9N)]`). -/
noncomputable def tmplF (prof : ℝ → List Piece) (C0 : ℝ) (hC : 0 ≤ C0) (hprof : Chain (1 / 9) (prof C0)) :
    Template where
  α0 := 20 / 9
  t1 := {q(t1)}
  l := fullList prof C0
  hα0 := by norm_num
  ht1 := by norm_num
  chain := fullList_chain prof C0 hC hprof

theorem tmplF_mass (prof : ℝ → List Piece) (C0 : ℝ) (hC : 0 ≤ C0) (hprof : Chain (1 / 9) (prof C0))
    (m : ℚ) (hm : listInt (prof C0) = (m : ℝ)) :
    (tmplF prof C0 hC hprof).mass = (({q(pre0)} + prefixMass + m : ℚ) : ℝ) := by
  unfold Template.mass tmplF
  simp only
  rw [fullList_mass prof C0 m hm]
  push_cast
  ring

/-- The template of the unit class `c` of `ZMod 10`. -/
noncomputable def tmpl5 (C0 : ℝ) (hC : 0 ≤ C0) (c : ZMod 10) : Template :=
  if c = 1 then tmplF profile1 C0 hC (profile1_chain C0 hC)
  else if c = 3 then tmplF profile3 C0 hC (profile3_chain C0 hC)
  else if c = 7 then tmplF profile7 C0 hC (profile7_chain C0 hC)
  else tmplF profile9 C0 hC (profile9_chain C0 hC)

{lam_def}

theorem contentConstant_tmpl5 (C0 : ℝ) (hC : 0 ≤ C0) :
    contentConstant 10 (tmpl5 C0 hC) = (LamFin5 : ℝ) := by
  have t1 : (tmpl5 C0 hC 1).mass = (({q(pre0)} + prefixMass + profile1Mass : ℚ) : ℝ) := by
    unfold tmpl5; rw [if_pos rfl]; exact tmplF_mass _ _ _ _ _ (profile1_mass C0)
  have t3 : (tmpl5 C0 hC 3).mass = (({q(pre0)} + prefixMass + profile3Mass : ℚ) : ℝ) := by
    unfold tmpl5; rw [if_neg (by decide), if_pos rfl]; exact tmplF_mass _ _ _ _ _ (profile3_mass C0)
  have t7 : (tmpl5 C0 hC 7).mass = (({q(pre0)} + prefixMass + profile7Mass : ℚ) : ℝ) := by
    unfold tmpl5; rw [if_neg (by decide), if_neg (by decide), if_pos rfl]; exact tmplF_mass _ _ _ _ _ (profile7_mass C0)
  have t9 : (tmpl5 C0 hC 9).mass = (({q(pre0)} + prefixMass + profile9Mass : ℚ) : ℝ) := by
    unfold tmpl5; rw [if_neg (by decide), if_neg (by decide), if_neg (by decide)]; exact tmplF_mass _ _ _ _ _ (profile9_mass C0)
  unfold contentConstant
  rw [unitClasses_ten, totient_ten]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, t1, t3, t7, t9]
  have hq : (({q(pre0)} + prefixMass + profile1Mass : ℚ) : ℝ) + (({q(pre0)} + prefixMass + profile3Mass : ℚ) : ℝ) +
      (({q(pre0)} + prefixMass + profile7Mass : ℚ) : ℝ) + (({q(pre0)} + prefixMass + profile9Mass : ℚ) : ℝ) =
      ((4 * LamFin5 : ℚ) : ℝ) := by
    rw [← Rat.cast_add, ← Rat.cast_add, ← Rat.cast_add]
    congr 1
    norm_num [{unf}]
  rw [hq]; push_cast; ring

#print axioms fullList_chain
#print axioms tmplF_mass
end {NS}
'''
(B / 'Tmpl.lean').write_text(tm, encoding='utf-8')
print('N', N, 'leaves', nleaf, 'Lfin', float(Lfin), 'mu', float(mu))
