module

public import CatalanFrames.Lambda.PolyEval
public import CatalanLambda.Mirror.NVMod

/-!
# The mirror frame (WP8)

`λ' = G/2 + 5π²/96` as a Loewner frame: `μ = ![1/4, 1]`, `w = ![1, -1]`, `norm = 16`.
`Frame.Mn` agrees with the legacy mirror entries `N0n`, so `Frame.P = Pbar`.
-/

@[expose] public section

open Finset CatalanCore

namespace CatalanFrames.LambdaMirror

/-- The frame of `λ' = G/2 + 5π²/96`. -/
def mirFrame : Frame where
  d := 2
  μ := ![1 / 4, 1]
  w := ![1, -1]
  norm := 16
  xs := 5 / 8
  δ0 := 3 / 8
  n0off := 1
  hμ := by intro i; fin_cases i <;> norm_num
  hμinj := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all
  hw := by simp [Fin.sum_univ_two]
  hnorm := by norm_num

lemma one_le_ne {k : ℕ} (hk : 1 ≤ k) : (k : ℚ) ≠ 0 ∧ (4 * (k : ℚ) - 3) ≠ 0 ∧
    (k : ℚ) - 1 + 1 / 4 ≠ 0 := by
  have : (1 : ℚ) ≤ k := by exact_mod_cast hk
  refine ⟨by positivity, ?_, ?_⟩ <;> intro h <;> linarith

lemma Dsq_eq (k : ℕ) (hk : 1 ≤ k) :
    mirFrame.Dsq k = 16 / (4 * (k : ℚ) - 3) ^ 2 - 1 / (k : ℚ) ^ 2 := by
  obtain ⟨h1, h2, h3⟩ := one_le_ne hk
  have e : mirFrame.Dsq k =
      ∑ i : Fin 2, ((![1, -1] i : ℤ) : ℚ) / ((k : ℚ) - 1 + ![1 / 4, 1] i) ^ 2 := rfl
  rw [e, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  push_cast
  have e1 : (k : ℚ) - 1 + 1 = k := by ring
  have e2 : (k : ℚ) - 1 + 1 / 4 = (4 * k - 3) / 4 := by ring
  rw [e1, e2]
  field_simp
  ring

lemma Delta_eq (k : ℕ) (hk : 1 ≤ k) :
    mirFrame.Delta k = 3 / ((k : ℚ) * (4 * (k : ℚ) - 3)) := by
  obtain ⟨h1, h2, h3⟩ := one_le_ne hk
  have e : mirFrame.Delta k =
      ∑ i : Fin 2, ((![1, -1] i : ℤ) : ℚ) / ((k : ℚ) - 1 + ![1 / 4, 1] i) := rfl
  rw [e, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  push_cast
  have e1 : (k : ℚ) - 1 + 1 = k := by ring
  have e2 : (k : ℚ) - 1 + 1 / 4 = (4 * k - 3) / 4 := by ring
  rw [e1, e2]
  field_simp
  ring

/-- **The mirror frame reproduces the legacy mirror matrix entries.** -/
theorem Mn_eq (a b : ℕ) : mirFrame.Mn a b = CatalanLambda.Mirror.N0n a b := by
  have hn : mirFrame.norm = 16 := rfl
  unfold Frame.Mn CatalanLambda.Mirror.N0n
  split_ifs with hab
  · rw [hn, neg_mul, Finset.mul_sum, neg_eq_iff_eq_neg, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    have hk1 : 1 ≤ k := (Finset.mem_Icc.1 hk).1
    obtain ⟨h1, h2, _⟩ := one_le_ne hk1
    rw [Dsq_eq k hk1]
    field_simp
    ring
  · rw [hn]
    have hs : ∑ k ∈ Ioc (min a b) (max a b), mirFrame.Delta k =
        ∑ k ∈ Ioc (min a b) (max a b), 3 * (1 / ((k : ℚ) * (4 * (k : ℚ) - 3))) := by
      refine Finset.sum_congr rfl (fun k hk => ?_)
      have hk1 : 1 ≤ k := by have := (Finset.mem_Ioc.1 hk).1; omega
      rw [Delta_eq k hk1]; ring
    rw [hs, ← Finset.mul_sum]
    generalize ((max a b : ℕ) : ℚ) - ((min a b : ℕ) : ℚ) = d
    generalize (∑ k ∈ Ioc (min a b) (max a b), 1 / ((k : ℚ) * (4 * (k : ℚ) - 3))) = S
    simp only [one_div]
    ring

/-- `mirFrame.M h` is the legacy matrix `N0 h`. -/
theorem M_eq (h : ℕ) : mirFrame.M h = CatalanLambda.Mirror.N0 h := by
  ext a b
  simp [Frame.M, Frame.MRect, CatalanLambda.Mirror.N0, Mn_eq]

theorem P_eq (h : ℕ) (r : ℚ) : mirFrame.P h r = CatalanLambda.Mirror.Pbar h r := by
  unfold Frame.P CatalanLambda.Mirror.Pbar; rw [M_eq]

end CatalanFrames.LambdaMirror
