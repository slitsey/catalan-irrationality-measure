module

public import CatalanCore.Uniform.Decay.Jet.PoleGram
public import Mathlib.Algebra.BigOperators.Intervals

@[expose] public section
set_option Elab.async false
open Finset MeasureTheory Set Filter Complex
open scoped Polynomial

namespace CatalanCore.Uniform.Decay.Jet
open CatalanCore.Uniform.Support

/-! Padded Hankel forms and the actual finite jet heads.  Arbitrarily many
zero-weight padding labels are permitted; no minimal-split assumption is used. -/

theorem sum_padded_hankel (J w : ℕ) (hw : w ≤ J + 1) (c : ℕ → ℂ)
    (hc : ∀ k, w < k → c k = 0) (A B : ℂ) :
    (∑ j : Fin (J + 1), ∑ k : Fin (J + 1),
      c (j.val + k.val + 1) * (A⁻¹) ^ (j.val + 1) * (B⁻¹) ^ (k.val + 1)) =
      ∑ l ∈ Finset.Icc 1 w, c l * poleGeom l A B := by
  let F : ℕ → ℕ → ℂ := fun j k => c (j + k + 1) * (A⁻¹) ^ (j + 1) * (B⁻¹) ^ (k + 1)
  have hout : (∑ j ∈ Finset.range (J + 1), ∑ k ∈ Finset.range (J + 1), F j k) =
      ∑ j ∈ Finset.range w, ∑ k ∈ Finset.range (J + 1), F j k := by
    symm
    apply Finset.sum_subset (Finset.range_mono hw)
    intro j hj hjw
    apply Finset.sum_eq_zero
    intro k hk
    have hjw' : w ≤ j := by simpa using hjw
    simp only [F, hc (j + k + 1) (by omega), zero_mul]
  have hin : ∀ j ∈ Finset.range w,
      (∑ k ∈ Finset.range (J + 1), F j k) = ∑ k ∈ Finset.range (w - j), F j k := by
    intro j hj
    symm
    apply Finset.sum_subset (Finset.range_mono (by omega : w - j ≤ J + 1))
    intro k hk hkw
    have hkw' : w - j ≤ k := by simpa using hkw
    simp only [F, hc (j + k + 1) (by omega), zero_mul]
  have hfin : (∑ j : Fin (J + 1), ∑ k : Fin (J + 1), F j k) =
      ∑ j ∈ Finset.range (J + 1), ∑ k ∈ Finset.range (J + 1), F j k := by
    rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => ∑ k : Fin (J + 1), F j k) (J + 1)]
    apply Finset.sum_congr rfl
    intro j hj
    exact Fin.sum_univ_eq_sum_range (F j) (J + 1)
  change (∑ j : Fin (J + 1), ∑ k : Fin (J + 1), F j k) = _
  rw [hfin, hout]
  have htri : (∑ j ∈ Finset.range w, ∑ k ∈ Finset.range (J + 1), F j k) =
      ∑ j ∈ Finset.range w, ∑ k ∈ Finset.range (w - j), F j k :=
    Finset.sum_congr rfl hin
  rw [htri, ← Finset.sum_range_diag_flip w F]
  rw [JetFrame.sum_Icc_shift']
  apply Finset.sum_congr rfl
  intro l hl
  rw [poleGeom, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjl : j ≤ l := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  dsimp [F]
  rw [show j + (l - j) + 1 = l + 1 by omega,
    show l + 1 - j = l - j + 1 by omega]
  ring

theorem iteratedDeriv_inv_negative (j : ℕ) {s : ℝ} (hs : 0 < s) (x m : ℕ) :
    iteratedDeriv j (fun z : ℂ => (z - (x : ℂ))⁻¹) (-(m : ℂ) - (s : ℂ)) =
      -(j.factorial : ℂ) * (((m : ℂ) + (s : ℂ) + (x : ℂ))⁻¹) ^ (j + 1) := by
  have hx : -(m : ℂ) - (s : ℂ) ≠ (x : ℂ) := by
    intro h
    have he := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.neg_re, Complex.natCast_re, Complex.ofReal_re] at he
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
    have hx : (0 : ℝ) ≤ x := Nat.cast_nonneg _
    linarith
  rw [iteratedDeriv_inv_sub j _ hx]
  have he : (-(m : ℂ) - (s : ℂ) - (x : ℂ))⁻¹ =
      -((m : ℂ) + (s : ℂ) + (x : ℂ))⁻¹ := by
    rw [← inv_neg]
    congr 1
    ring
  rw [he, neg_pow (((m : ℂ) + (s : ℂ) + (x : ℂ))⁻¹) (j + 1)]
  have hsign : (-1 : ℂ) ^ j * (-1 : ℂ) ^ (j + 1) = -1 := by
    rw [← pow_add, show j + (j + 1) = 2 * j + 1 by omega, pow_succ, pow_mul]
    norm_num
  calc
    _ = ((-1 : ℂ) ^ j * (-1 : ℂ) ^ (j + 1)) * (j.factorial : ℂ) *
        (((m : ℂ) + (s : ℂ) + (x : ℂ))⁻¹) ^ (j + 1) := by ring
    _ = _ := by rw [hsign]; ring

theorem pole_head_split (D : PoleDatum) (S : PoleGramSplit D) (i : Fin D.n) (m x y : ℕ) :
    (∑ q : Fin (S.count i), (S.weight ⟨i, q⟩ : ℂ) *
      (∑ j : Fin (S.J + 1), (S.coeff ⟨i, q⟩ j : ℂ) *
        iteratedDeriv j.val (fun z : ℂ => (z - (x : ℂ))⁻¹) (-(m : ℂ) - (D.s i : ℂ))) *
      (∑ k : Fin (S.J + 1), (S.coeff ⟨i, q⟩ k : ℂ) *
        iteratedDeriv k.val (fun z : ℂ => (z - (y : ℂ))⁻¹) (-(m : ℂ) - (D.s i : ℂ)))) =
      ((∑ j ∈ Finset.Icc 1 (D.w i), (D.coeff i j : ℝ) *
        poleAtom j (D.s i : ℝ) x y m : ℝ) : ℂ) := by
  rw [← pole_split_bilinear S i]
  have hs : (0 : ℝ) < (D.s i : ℝ) := by exact_mod_cast (D.hs i).1
  have he (j k : Fin (S.J + 1)) :
      ((D.coeff i (j.val + k.val + 1) /
        ((j.val.factorial : ℚ) * k.val.factorial) : ℚ) : ℂ) *
        iteratedDeriv j.val (fun z : ℂ => (z - (x : ℂ))⁻¹) (-(m : ℂ) - (D.s i : ℂ)) *
        iteratedDeriv k.val (fun z : ℂ => (z - (y : ℂ))⁻¹) (-(m : ℂ) - (D.s i : ℂ)) =
        (D.coeff i (j.val + k.val + 1) : ℂ) *
          (((m : ℂ) + (D.s i : ℂ) + (x : ℂ))⁻¹) ^ (j.val + 1) *
          (((m : ℂ) + (D.s i : ℂ) + (y : ℂ))⁻¹) ^ (k.val + 1) := by
    have hj : (j.val.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j.val
    have hk : (k.val.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k.val
    rw [show (D.s i : ℂ) = ((D.s i : ℝ) : ℂ) by simp,
      iteratedDeriv_inv_negative j.val hs x m, iteratedDeriv_inv_negative k.val hs y m]
    push_cast
    field_simp
    <;> ring
  simp_rw [he]
  rw [sum_padded_hankel S.J (D.w i) (S.order_le i)
    (fun j => (D.coeff i j : ℂ)) (fun j hj => by rw [D.coeff_above i j hj]; simp)]
  push_cast
  apply Finset.sum_congr rfl
  intro j hj
  rw [poleAtom_eq_geom j hs x y m]
  simp only [poleGeom, Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_pow,
    Complex.ofReal_inv, Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_ratCast]


#print axioms sum_padded_hankel
#print axioms iteratedDeriv_inv_negative
#print axioms pole_head_split

end CatalanCore.Uniform.Decay.Jet
