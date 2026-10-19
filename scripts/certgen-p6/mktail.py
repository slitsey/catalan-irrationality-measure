# Tail.lean for row D: derived from legacy Tail.lean (changes: r0 = 1/10, atoms in |Re| <= 11/10, |Im| <= 14/5, 12 -> 30)
import sys; sys.path.insert(0, '.')
import re
src = open('C:/Users/seanl/Documents/Codex/2026-10-11/plea/work/catalan-repo/CatalanLambda/Cert/Tail.lean', encoding='utf-8').read()
import importlib.util
# reuse conv() without re-running the file loop
code = open('mkengine.py', encoding='utf-8').read().split('for src, dst in MAP.items():')[0]
ns = {}; exec(code, ns)
t = ns['conv']('Tail', src).replace('public import CatalanLambda.Cert.Symm', 'public import CatalanCore.Cert.SigmaP6.Symm')
i = t.index('def posOK'); j = t.index('theorem tail_core')
pos = '''def posOK (k : ℕ) : Bool :=
  decide (-(11 * 2 ^ 40 : ℤ) ≤ 10 * (ptAt k).1) && decide ((ptAt k).1 ≤ 0) &&
    decide (10 * (ptAt k).2.1 ≤ 28 * 2 ^ 40) && decide (-(28 * 2 ^ 40 : ℤ) ≤ 10 * (ptAt k).2.1)

theorem pos_check : (List.range 699).all posOK = true := by decide +kernel

lemma pos_bounds (k : Fin 699) :
    -(11 / 10 : ℝ) ≤ (cS k).re ∧ (cS k).re ≤ 0 ∧ -(14 / 5 : ℝ) ≤ (cS k).im ∧ (cS k).im ≤ 14 / 5 := by
  have h := List.all_eq_true.mp pos_check k (List.mem_range.mpr k.2)
  simp only [posOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  have r1 : (-(11 * 2 ^ 40 : ℝ)) ≤ 10 * ((ptAt k).1 : ℝ) := by exact_mod_cast h1
  have r2 : ((ptAt k).1 : ℝ) ≤ 0 := by exact_mod_cast h2
  have r3 : 10 * ((ptAt k).2.1 : ℝ) ≤ 28 * 2 ^ 40 := by exact_mod_cast h3
  have r4 : (-(28 * 2 ^ 40 : ℝ)) ≤ 10 * ((ptAt k).2.1 : ℝ) := by exact_mod_cast h4
  simp only [cS]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [le_div_iff₀ (by positivity)]; nlinarith
  · exact div_nonpos_of_nonpos_of_nonneg r2 (by positivity)
  · rw [le_div_iff₀ (by positivity)]; nlinarith
  · rw [div_le_iff₀ (by positivity)]; nlinarith

'''
t = t[:i] + pos + t[j:]
t = t.replace('(197179 / 100000 : ℝ)', '(1883395 / 1000000 : ℝ)').replace('7 / 50', '1 / 10').replace('12 * u ^ 2', '30 * u ^ 2')
t = t.replace('''    rw [hre, him]
    nlinarith [sq_nonneg (u - 3 / 2)]''', '''    have hd : |δ| ≤ 1 / 100 := hδ.trans (by norm_num)
    have hd' := abs_le.mp hd
    have ha : (z.re - (cS k).re) ^ 2 ≤ (u + 11 / 100) ^ 2 :=
      sq_le_sq' (by rw [hre]; linarith [hd'.1, hd'.2]) (by rw [hre]; linarith [hd'.1, hd'.2])
    have hb : (z.im - (cS k).im) ^ 2 ≤ (3 * u + 14 / 5) ^ 2 :=
      sq_le_sq' (by rw [him]; linarith) (by rw [him]; linarith)
    nlinarith [mul_nonneg (sub_nonneg.2 hu) hu0.le]''')
t = t.replace('-(1 / 6 : ℝ) ≤ Real.log (3 * u)', '-(7 / 6 : ℝ) ≤ Real.log (3 * u)').replace('= (1 / 3 : ℝ) := by field_simp; ring', '= (7 / 3 : ℝ) := by field_simp; ring')
open('C:/Users/seanl/Documents/Codex/2026-10-11/plea/work/catalan-thmA/CatalanCore/Cert/SigmaP6/Tail.lean', 'w', encoding='utf-8', newline='\n').write(t)
