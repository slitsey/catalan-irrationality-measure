module

public import CatalanCore.Frame.Spec
public import CatalanLambda.Defs

/-!
# The λ frame (WP7)

`λ = G/2 - 5π²/96` as a Loewner frame: `μ = ![3/4, 1]`, `w = ![-1, 1]` (the sign of design 2.2 is
corrected, see WP0 notes), `norm = 16`.  We prove that `Frame.Mn` agrees with the legacy `M0n`,
so that `Frame.M = M0` and `Frame.P = CatalanLambda.P`.
-/

@[expose] public section

open Finset CatalanCore

namespace CatalanFrames.Lambda

/-- The frame of `λ = G/2 - 5π²/96`. -/
def lamFrame : Frame where
  d := 2
  μ := ![3 / 4, 1]
  w := ![-1, 1]
  norm := 16
  xs := 3 / 8
  δ0 := 3 / 8
  n0off := 0
  hμ := by intro i; fin_cases i <;> norm_num
  hμinj := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all <;> norm_num
  hw := by simp [Fin.sum_univ_two]
  hnorm := by norm_num

lemma one_le_ne {k : ℕ} (hk : 1 ≤ k) : (k : ℚ) ≠ 0 ∧ (4 * (k : ℚ) - 1) ≠ 0 ∧
    (k : ℚ) - 1 + 3 / 4 ≠ 0 := by
  have : (1 : ℚ) ≤ k := by exact_mod_cast hk
  refine ⟨by positivity, ?_, ?_⟩ <;> intro h <;> linarith

lemma Dsq_eq (k : ℕ) (hk : 1 ≤ k) :
    lamFrame.Dsq k = 1 / (k : ℚ) ^ 2 - 16 / (4 * (k : ℚ) - 1) ^ 2 := by
  obtain ⟨h1, h2, h3⟩ := one_le_ne hk
  have e : lamFrame.Dsq k =
      ∑ i : Fin 2, ((![-1, 1] i : ℤ) : ℚ) / ((k : ℚ) - 1 + ![3 / 4, 1] i) ^ 2 := rfl
  rw [e, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  push_cast
  have e1 : (k : ℚ) - 1 + 1 = k := by ring
  have e2 : (k : ℚ) - 1 + 3 / 4 = (4 * k - 1) / 4 := by ring
  rw [e1, e2]
  field_simp
  ring

lemma Delta_eq (k : ℕ) (hk : 1 ≤ k) :
    lamFrame.Delta k = -(4 / (4 * (k : ℚ) * (4 * (k : ℚ) - 1))) := by
  obtain ⟨h1, h2, h3⟩ := one_le_ne hk
  have h4 : (k : ℚ) - 1 + 1 ≠ 0 := by simpa using h1
  have e : lamFrame.Delta k =
      ∑ i : Fin 2, ((![-1, 1] i : ℤ) : ℚ) / ((k : ℚ) - 1 + ![3 / 4, 1] i) := rfl
  rw [e, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  push_cast
  have e1 : (k : ℚ) - 1 + 1 = k := by ring
  have e2 : (k : ℚ) - 1 + 3 / 4 = (4 * k - 1) / 4 := by ring
  rw [e1, e2]
  field_simp
  ring

/-- **The λ frame reproduces the legacy matrix entries.** -/
theorem Mn_eq (a b : ℕ) : lamFrame.Mn a b = CatalanLambda.M0n a b := by
  have hn : lamFrame.norm = 16 := rfl
  unfold Frame.Mn CatalanLambda.M0n
  split_ifs with hab
  · rw [hn, neg_mul, Finset.mul_sum, neg_inj]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    have hk1 : 1 ≤ k := (Finset.mem_Icc.1 hk).1
    obtain ⟨h1, h2, _⟩ := one_le_ne hk1
    rw [Dsq_eq k hk1]
    field_simp
  · rw [hn]
    have hs : ∑ k ∈ Ioc (min a b) (max a b), lamFrame.Delta k =
        ∑ k ∈ Ioc (min a b) (max a b), -(4 * (1 / (4 * (k : ℚ) * (4 * (k : ℚ) - 1)))) := by
      refine Finset.sum_congr rfl (fun k hk => ?_)
      have hk1 : 1 ≤ k := by have := (Finset.mem_Ioc.1 hk).1; omega
      rw [Delta_eq k hk1]; ring
    rw [hs, Finset.sum_neg_distrib, ← Finset.mul_sum]
    generalize ((max a b : ℕ) : ℚ) - ((min a b : ℕ) : ℚ) = d
    generalize (∑ k ∈ Ioc (min a b) (max a b), 1 / (4 * (k : ℚ) * (4 * (k : ℚ) - 1))) = S
    simp only [one_div, mul_inv]
    ring

end CatalanFrames.Lambda
