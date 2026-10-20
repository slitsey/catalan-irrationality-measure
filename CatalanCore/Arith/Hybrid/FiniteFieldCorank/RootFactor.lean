module

public import CatalanCore.Arith.Hybrid.FiniteFieldCorank
public import CatalanCore.Arith.Hybrid.FiniteFieldCorank.Interpolation
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.RingTheory.Coprime.Lemmas

@[expose] public section

open Polynomial Finset

namespace CatalanCore.Arith.Hybrid.FiniteFieldCorank

variable {k : Type*} [Field k]

lemma eval_wronskian (F P : k[X]) (a : k) :
    (wronskian F P).eval a = F.eval (a + 1) * P.eval a -
      F.eval a * P.eval (a + 1) := by
  simp [wronskian]

lemma wronskian_jets (F P : k[X]) (a z : k)
    (h0 : F.eval a = 0) (h1 : F.eval (a + 1) = 0)
    (hd0 : F.derivative.eval a = 0) (hd1 : F.derivative.eval (a + 1) = 0)
    (hdd0 : F.derivative.derivative.eval a = 2 * z * P.eval a)
    (hdd1 : F.derivative.derivative.eval (a + 1) = 2 * z * P.eval (a + 1)) :
    (wronskian F P).eval a = 0 ∧
      (wronskian F P).derivative.eval a = 0 ∧
      (wronskian F P).derivative.derivative.eval a = 0 := by
  constructor
  · simp [eval_wronskian, h0, h1]
  constructor
  · simp [wronskian, derivative_comp, h0, h1, hd0, hd1]
  · simp [wronskian, derivative_comp, h0, h1, hd0, hd1, hdd0, hdd1]
    ring

lemma cube_dvd_of_jets (W : k[X]) (a : k) (h2 : (2 : k) ≠ 0)
    (h0 : W.eval a = 0) (h1 : W.derivative.eval a = 0)
    (hdd : W.derivative.derivative.eval a = 0) :
    (X - C a) ^ 3 ∣ W := by
  by_cases hW : W = 0
  · simp [hW]
  have hf : ((2 : ℕ).factorial : k) ∈ nonZeroDivisors k := by
    simpa using (mem_nonZeroDivisors_iff_ne_zero.mpr h2)
  have hm : 2 < W.rootMultiplicity a :=
    (lt_rootMultiplicity_iff_isRoot_iterate_derivative_of_mem_nonZeroDivisors hW hf).2 (by
      intro j hj
      interval_cases j
      · exact h0
      · simpa using h1
      · simpa [Function.iterate_succ_apply] using hdd)
  exact (le_rootMultiplicity_iff hW).1 (by omega : 3 ≤ W.rootMultiplicity a)

/-- Pointwise root powers combine without any root-multiplicity bookkeeping. -/
lemma prod_root_powers_dvd (s : Finset k) (e : k → ℕ) (W : k[X])
    (h : ∀ a ∈ s, (X - C a) ^ e a ∣ W) :
    (∏ a ∈ s, (X - C a) ^ e a) ∣ W := by
  classical
  apply Finset.prod_dvd_of_coprime _ h
  intro a ha b hb hab
  exact (isCoprime_X_sub_C_of_isUnit_sub
    (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hab))).pow

/-- Same scalar values on two adjacent support nodes give a simple root. -/
lemma wronskian_eval_of_same_values (F P : k[X]) (a c : k)
    (h0 : F.eval a = c * P.eval a)
    (h1 : F.eval (a + 1) = c * P.eval (a + 1)) :
    (wronskian F P).eval a = 0 := by
  rw [eval_wronskian, h0, h1]
  ring

lemma rootProducts_isCoprime (s t : Finset k) (hd : Disjoint s t) :
    IsCoprime (rootProduct s) (rootProduct t) := by
  classical
  unfold rootProduct
  apply IsCoprime.prod_left
  intro a ha
  apply IsCoprime.prod_right
  intro b hb
  apply isCoprime_X_sub_C_of_isUnit_sub
  apply isUnit_iff_ne_zero.mpr
  apply sub_ne_zero.mpr
  intro hab
  subst b
  exact Finset.disjoint_left.1 hd ha hb

lemma rootProduct_pow_dvd (s : Finset k) (e : ℕ) (W : k[X])
    (h : ∀ a ∈ s, (X - C a) ^ e ∣ W) : (rootProduct s) ^ e ∣ W := by
  classical
  have he : (∏ a ∈ s, (X - C a : k[X]) ^ e) = (rootProduct s) ^ e := by
    simp [rootProduct, Finset.prod_pow]
  rw [← he]
  exact prod_root_powers_dvd s (fun _ => e) W h

lemma rootProduct_eval_ne_zero (s : Finset k) (u : k) (hu : u ∉ s) :
    (rootProduct s).eval u ≠ 0 := by
  classical
  simp only [rootProduct, eval_prod, eval_sub, eval_X, eval_C]
  apply Finset.prod_ne_zero_iff.2
  intro a ha
  exact sub_ne_zero.mpr (fun h => hu (h ▸ ha))

lemma natDegree_rootProduct (s : Finset k) : (rootProduct s).natDegree = s.card := by
  simp [rootProduct]

lemma rootProduct_monic (s : Finset k) : (rootProduct s).Monic := by
  classical
  exact monic_prod_of_monic s _ (fun _ _ => monic_X_sub_C _)

end CatalanCore.Arith.Hybrid.FiniteFieldCorank
