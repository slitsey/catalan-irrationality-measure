module

public import CatalanCore.Rect.CharZeroNV.Interpolation

@[expose] public section

/-! # Barycentric coordinates of Loewner kernel vectors

These identities work on arbitrary distinct field nodes. They connect a
Loewner row equation with value or first-jet interpolation, reusing the
existing interpolation numerator rather than defining another one.
-/

open Polynomial Finset
open CatalanCore.Arith.Hybrid.FiniteFieldCorank

namespace CatalanCore.Rect.CharZeroNV

variable {K : Type*} [Field K] [DecidableEq K]

noncomputable def loewnerRow (B : Finset K) (f tau w : K → K) (a : K) : K :=
  ∑ b ∈ B, (if a = b then tau a else (f a - f b) / (a - b)) * w b

lemma punctured_eval_ne_zero (B : Finset K) (a : K) : (punctured B a).eval a ≠ 0 := by
  simp only [punctured, eval_prod, eval_sub, eval_X, eval_C]
  apply Finset.prod_ne_zero_iff.mpr
  intro b hb
  exact sub_ne_zero.mpr (Ne.symm (Finset.mem_erase.mp hb).1)

lemma numerator_zero_implies_weights (B : Finset K) (w : K → K)
    (hz : numerator B w = 0) : ∀ a ∈ B, w a = 0 := by
  intro a ha
  have he := eval_numerator B w ha
  rw [hz, eval_zero, rootProduct_factor B ha, derivative_mul] at he
  simp only [eval_add, eval_mul, derivative_sub, derivative_X, derivative_C,
    sub_zero, one_mul, eval_sub, eval_X, eval_C, sub_self,
    zero_mul, add_zero] at he
  exact (mul_eq_zero.mp he.symm).resolve_right (punctured_eval_ne_zero B a)

lemma punctured_eval_quotient (B : Finset K) {a b : K} (hb : b ∈ B) (hab : a ≠ b) :
    (punctured B b).eval a = (rootProduct B).eval a / (a - b) := by
  apply (eq_div_iff (sub_ne_zero.mpr hab)).mpr
  have he := congrArg (fun P : K[X] => P.eval a) (rootProduct_factor B hb)
  simpa [mul_comm] using he.symm

theorem value_defect_eq (B : Finset K) (f tau w : K → K) (a : K)
    (ha : a ∉ B) :
    (numerator B (fun b => w b * f b)).eval a -
      f a * (numerator B w).eval a = -(rootProduct B).eval a * loewnerRow B f tau w a := by
  have hid : (numerator B (fun b => w b * f b)).eval a -
      f a * (numerator B w).eval a = -(rootProduct B).eval a * loewnerRow B f tau w a := by
    simp only [numerator, eval_finsetSum, eval_mul, eval_C, loewnerRow,
      Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro b hb
    have hab : a ≠ b := by intro h; exact ha (h ▸ hb)
    rw [punctured_eval_quotient B hb hab, ite_eq_right hab]
    ring
  exact hid

theorem kernel_value_outside (B : Finset K) (f tau w : K → K) (a : K)
    (ha : a ∉ B) (hk : loewnerRow B f tau w a = 0) :
    (numerator B (fun b => w b * f b)).eval a =
      f a * (numerator B w).eval a := by
  exact sub_eq_zero.mp (by simpa [hk] using value_defect_eq B f tau w a ha)

theorem kernel_value_inside (B : Finset K) (f w : K → K) (a : K) (ha : a ∈ B) :
    (numerator B (fun b => w b * f b)).eval a =
      f a * (numerator B w).eval a := by
  rw [eval_numerator B _ ha, eval_numerator B _ ha]
  ring

lemma punctured_derivative_relation (B : Finset K) {a b : K}
    (ha : a ∈ B) (hb : b ∈ B) (hab : a ≠ b) :
    (punctured B b).derivative.eval a = (punctured B a).eval a / (a - b) := by
  have hpa : punctured B b = (X - C a) * punctured (B.erase a) b := by
    have he := rootProduct_factor (B.erase b) (mem_erase.mpr ⟨hab, ha⟩)
    simpa [rootProduct, punctured, Finset.erase_right_comm] using he
  have hpb : punctured B a = (X - C b) * punctured (B.erase a) b := by
    exact rootProduct_factor (B.erase a) (mem_erase.mpr ⟨hab.symm, hb⟩)
  rw [hpa, hpb]
  simp only [derivative_mul, derivative_sub, derivative_X, derivative_C,
    sub_zero, one_mul, eval_add, eval_mul, eval_sub, eval_X, eval_C,
    sub_self, zero_mul, add_zero]
  field_simp

theorem jet_defect_eq (B : Finset K) (f tau w : K → K) (a : K)
    (ha : a ∈ B) :
    (numerator B (fun b => w b * f b)).derivative.eval a -
      f a * (numerator B w).derivative.eval a - tau a * (numerator B w).eval a =
        -(punctured B a).eval a * loewnerRow B f tau w a := by
  have hid : (numerator B (fun b => w b * f b)).derivative.eval a -
      f a * (numerator B w).derivative.eval a - tau a * (numerator B w).eval a =
        -(punctured B a).eval a * loewnerRow B f tau w a := by
    have hn : (numerator B w).eval a = w a * (punctured B a).eval a := by
      rw [eval_numerator B _ ha, rootProduct_factor B ha, derivative_mul]
      simp
    rw [hn]
    simp only [numerator, derivative_sum, derivative_mul, derivative_C,
      zero_mul, zero_add, eval_finsetSum, eval_mul, eval_C, loewnerRow,
      Finset.mul_sum, ← Finset.sum_sub_distrib]
    have hc : tau a * (w a * (punctured B a).eval a) =
        ∑ b ∈ B, if b = a then tau a * (w a * (punctured B a).eval a) else 0 := by
      simp [ha]
    rw [hc, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro b hb
    by_cases hba : b = a
    · subst b
      simp
      ring
    · rw [ite_eq_right hba, ite_eq_right (Ne.symm hba),
        punctured_derivative_relation B ha hb (Ne.symm hba)]
      ring
  exact hid

theorem kernel_jet (B : Finset K) (f tau w : K → K) (a : K)
    (ha : a ∈ B) (hk : loewnerRow B f tau w a = 0) :
    (numerator B (fun b => w b * f b)).derivative.eval a =
      f a * (numerator B w).derivative.eval a + tau a * (numerator B w).eval a := by
  have hz : (numerator B (fun b => w b * f b)).derivative.eval a -
      f a * (numerator B w).derivative.eval a - tau a * (numerator B w).eval a = 0 := by
    simpa [hk] using jet_defect_eq B f tau w a ha
  linear_combination hz

lemma eval_numerator_punctured (B : Finset K) (w : K → K) {a : K} (ha : a ∈ B) :
    (numerator B w).eval a = w a * (punctured B a).eval a := by
  rw [eval_numerator B _ ha, rootProduct_factor B ha, derivative_mul]
  simp

/-- Barycentric reconstruction, including polynomials zero at data nodes. -/
theorem reconstruct (B : Finset K) (hB : 1 ≤ B.card) (p : K[X])
    (hp : p.natDegree ≤ B.card - 1) :
    numerator B (fun b => p.eval b / (punctured B b).eval b) = p := by
  apply sub_eq_zero.mp
  apply eq_zero_of_hermite_roots B ∅ (by simp)
  · intro a ha
    rw [eval_sub, eval_numerator_punctured B _ ha]
    field_simp [punctured_eval_ne_zero B a]
    ring
  · simp
  · simp only [card_empty, add_zero]
    have hnum := natDegree_numerator_le B (fun b => p.eval b / (punctured B b).eval b)
    have hd := natDegree_sub_le (numerator B (fun b => p.eval b / (punctured B b).eval b)) p
    omega

theorem reconstruct_value_numerator (B : Finset K) (hB : 1 ≤ B.card)
    (f : K → K) (p q : K[X]) (hq : q.natDegree ≤ B.card - 1)
    (hv : ∀ b ∈ B, q.eval b = f b * p.eval b) :
    numerator B (fun b => p.eval b / (punctured B b).eval b * f b) = q := by
  rw [← reconstruct B hB q hq]
  unfold numerator
  apply Finset.sum_congr rfl
  intro b hb
  dsimp only
  rw [hv b hb]
  congr 2
  ring

/-- The reverse barycentric direction: an interpolation pair supplies every
Loewner kernel row. The common-node case uses its first jet. -/
theorem pair_gives_kernel_row (B : Finset K) (hB : 1 ≤ B.card)
    (f tau : K → K) (p q : K[X])
    (hp : p.natDegree ≤ B.card - 1) (hq : q.natDegree ≤ B.card - 1)
    (hvB : ∀ b ∈ B, q.eval b = f b * p.eval b)
    (a : K) (hv : q.eval a = f a * p.eval a)
    (hj : a ∈ B → q.derivative.eval a = f a * p.derivative.eval a + tau a * p.eval a) :
    loewnerRow B f tau (fun b => p.eval b / (punctured B b).eval b) a = 0 := by
  let w := fun b => p.eval b / (punctured B b).eval b
  have hp' : numerator B w = p := reconstruct B hB p hp
  have hq' : numerator B (fun b => w b * f b) = q :=
    reconstruct_value_numerator B hB f p q hq hvB
  by_cases ha : a ∈ B
  · have he := jet_defect_eq B f tau w a ha
    rw [hp', hq', hj ha] at he
    have hz : -(punctured B a).eval a * loewnerRow B f tau w a = 0 := by
      linear_combination -he
    exact (mul_eq_zero.mp hz).resolve_left (neg_ne_zero.mpr (punctured_eval_ne_zero B a))
  · have he := value_defect_eq B f tau w a ha
    rw [hp', hq', hv] at he
    have hz : -(rootProduct B).eval a * loewnerRow B f tau w a = 0 := by
      linear_combination -he
    exact (mul_eq_zero.mp hz).resolve_left
      (neg_ne_zero.mpr (rootProduct_eval_ne_zero B a ha))

end CatalanCore.Rect.CharZeroNV
