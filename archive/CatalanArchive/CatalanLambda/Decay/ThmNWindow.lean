module

public import CatalanLambda.Decay.ThmNFinal
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.Data.Nat.Choose.Sum

@[expose] public section

/-!
# Theorem N_ρ: the window corollary
-/

open Finset CatalanLambda.Decay

namespace CatalanLambda.Decay

/-- `det(T + t I) = ∑_S t^{h-|S|} det T[S]`. -/
theorem det_add_scalar_expansion {h : ℕ} (T : Matrix (Fin h) (Fin h) ℝ) (t : ℝ) :
    (T + t • (1 : Matrix (Fin h) (Fin h) ℝ)).det
      = ∑ k ∈ range (h + 1), t ^ (h - k) *
          ∑ s ∈ (univ : Finset (Fin h)).powersetCard k,
            (T.submatrix (Subtype.val : s → Fin h) (Subtype.val : s → Fin h)).det := by
  have h1 : (T + t • (1 : Matrix (Fin h) (Fin h) ℝ)).det = (-T).charpoly.eval t := by
    rw [Matrix.eval_charpoly]
    congr 1
    rw [Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
    simp [sub_neg_eq_add, add_comm]
  rw [h1, Polynomial.eval_eq_sum_range]
  have hnd : (-T).charpoly.natDegree = h := by
    simpa using (-T).charpoly_natDegree_eq_dim
  rw [hnd, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  have hk' : k ≤ h := by have := Finset.mem_range.1 hk; omega
  have e : h + 1 - 1 - k = h - k := by omega
  rw [e]
  have hc := Matrix.charpoly_coeff_eq_sum_minors (-T) k (by rw [Fintype.card_fin]; omega)
  rw [Fintype.card_fin] at hc
  have hsum : (-1 : ℝ) ^ k * ∑ s ∈ (univ : Finset (Fin h)).powersetCard k,
        ((-T).submatrix (Subtype.val : s → Fin h) (Subtype.val : s → Fin h)).det
      = ∑ s ∈ (univ : Finset (Fin h)).powersetCard k,
        (T.submatrix (Subtype.val : s → Fin h) (Subtype.val : s → Fin h)).det := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun s hs => ?_)
    have hcard : s.card = k := (Finset.mem_powersetCard.1 hs).2
    have hn : (-T).submatrix (Subtype.val : s → Fin h) (Subtype.val : s → Fin h)
        = -(T.submatrix (Subtype.val : s → Fin h) (Subtype.val : s → Fin h)) := by
      ext i j; simp
    rw [hn, Matrix.det_neg, Fintype.card_coe, hcard, ← mul_assoc, ← pow_add,
      ← two_mul, pow_mul]
    simp
  rw [hc, hsum]; ring

/-- The real `h × h` matrix `T` (entries `Tent a b`). -/
noncomputable def Tmat (h : ℕ) : Matrix (Fin h) (Fin h) ℝ := Matrix.of fun a b => Tent a b

/-- Theorem N_ρ for a principal submatrix indexed by a finset of `Fin h`. -/
theorem minor_bound {K : ℕ} {ρ ε : ℝ} {c : Fin K → ℂ} {m : Fin K → ℝ}
    (F : CertFacts K ρ ε c m) {h : ℕ} (hh : 0 < h) (hW : 5 / (8 * (F.W : ℝ)) ≤ h)
    (k : ℕ) (s : Finset (Fin h)) (hs : s.card = k) :
    |((Tmat h).submatrix (Subtype.val : s → Fin h) (Subtype.val : s → Fin h)).det|
      ≤ Real.exp (-(h : ℝ) ^ 2 * F.Dcert + h * ((h : ℝ) - k) * F.ccert + Eerr F h) := by
  let e := s.orderIsoOfFin hs
  let sf : Fin k → Fin h := fun i => (e i).1
  have hsf : Function.Injective sf := fun a b hab => e.injective (Subtype.ext hab)
  have hdet : ((Tmat h).submatrix (Subtype.val : s → Fin h) (Subtype.val : s → Fin h)).det
      = (Matrix.of fun i j : Fin k => Tent (((sf i : Fin h) : ℕ)) (((sf j : Fin h) : ℕ))).det := by
    rw [← Matrix.det_submatrix_equiv_self e.toEquiv]
    congr 1
  rw [hdet]
  exact theoremN F hh hW sf hsf

/-- **Window corollary.**  For `h ≥ 5/(8W)` and `|t| ≤ e^{-c_cert h}`,
`|det(T + t I)| ≤ exp(-h² D_cert + E(h) + h log 2)`. -/
theorem window {K : ℕ} {ρ ε : ℝ} {c : Fin K → ℂ} {m : Fin K → ℝ}
    (F : CertFacts K ρ ε c m) {h : ℕ} (hh : 0 < h) (hW : 5 / (8 * (F.W : ℝ)) ≤ h)
    {t : ℝ} (ht : |t| ≤ Real.exp (-(F.ccert : ℝ) * h)) :
    |(Tmat h + t • (1 : Matrix (Fin h) (Fin h) ℝ)).det|
      ≤ Real.exp (-(h : ℝ) ^ 2 * F.Dcert + Eerr F h + h * Real.log 2) := by
  rw [det_add_scalar_expansion]
  set B : ℝ := Real.exp (-(h : ℝ) ^ 2 * F.Dcert + Eerr F h) with hB
  have hB0 : 0 < B := Real.exp_pos _
  have hterm : ∀ k ∈ range (h + 1), |t ^ (h - k) *
      ∑ s ∈ (univ : Finset (Fin h)).powersetCard k,
        ((Tmat h).submatrix (Subtype.val : s → Fin h) (Subtype.val : s → Fin h)).det|
      ≤ B * (h.choose k) := by
    intro k hk
    have hk' : k ≤ h := by have := Finset.mem_range.1 hk; omega
    have hts : |t| * Real.exp (F.ccert * h) ≤ 1 := by
      calc |t| * Real.exp (F.ccert * h) ≤ Real.exp (-(F.ccert : ℝ) * h) * Real.exp (F.ccert * h) :=
            mul_le_mul_of_nonneg_right ht (Real.exp_pos _).le
        _ = 1 := by rw [← Real.exp_add]; simp
    rw [abs_mul, abs_pow]
    calc |t| ^ (h - k) * |∑ s ∈ (univ : Finset (Fin h)).powersetCard k,
            ((Tmat h).submatrix (Subtype.val : s → Fin h) (Subtype.val : s → Fin h)).det|
        ≤ |t| ^ (h - k) * ∑ s ∈ (univ : Finset (Fin h)).powersetCard k,
            Real.exp (-(h : ℝ) ^ 2 * F.Dcert + h * ((h : ℝ) - k) * F.ccert + Eerr F h) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun s hs => ?_))
          exact minor_bound F hh hW k s (Finset.mem_powersetCard.1 hs).2
      _ = (|t| * Real.exp (F.ccert * h)) ^ (h - k) * B * (h.choose k) := by
          rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul]
          have : Real.exp (-(h : ℝ) ^ 2 * F.Dcert + h * ((h : ℝ) - k) * F.ccert + Eerr F h)
              = Real.exp (F.ccert * h) ^ (h - k) * B := by
            rw [hB, ← Real.exp_nat_mul, ← Real.exp_add]
            congr 1
            have : ((h - k : ℕ) : ℝ) = (h : ℝ) - k := by rw [Nat.cast_sub hk']
            rw [this]; ring
          rw [this, mul_pow]; ring
      _ ≤ B * (h.choose k) := by
          have h1 : (|t| * Real.exp (F.ccert * h)) ^ (h - k) ≤ 1 :=
            pow_le_one₀ (by positivity) hts
          have : (0 : ℝ) ≤ (h.choose k) := Nat.cast_nonneg _
          nlinarith [mul_nonneg hB0.le this]
  calc |∑ k ∈ range (h + 1), t ^ (h - k) *
        ∑ s ∈ (univ : Finset (Fin h)).powersetCard k,
          ((Tmat h).submatrix (Subtype.val : s → Fin h) (Subtype.val : s → Fin h)).det|
      ≤ ∑ k ∈ range (h + 1), |t ^ (h - k) *
        ∑ s ∈ (univ : Finset (Fin h)).powersetCard k,
          ((Tmat h).submatrix (Subtype.val : s → Fin h) (Subtype.val : s → Fin h)).det| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ range (h + 1), B * (h.choose k) := Finset.sum_le_sum hterm
    _ = B * 2 ^ h := by
        rw [← Finset.mul_sum]
        congr 1
        exact_mod_cast Nat.sum_range_choose h
    _ = _ := by
        rw [hB, show (2 : ℝ) ^ h = Real.exp (h * Real.log 2) by
          rw [mul_comm, Real.exp_mul, Real.exp_log (by norm_num)]; simp, ← Real.exp_add]

end CatalanLambda.Decay
