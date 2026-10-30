module

public import CatalanCore.NV.Hybrid.Reduce
public import CatalanCore.Star.Leonard.DeltaUnit

/-!
# Discharging `hΔ`: `det (W_Xᵀ W_Y)` is a unit of `𝔽_ℓ` (DO Corollary hRXY)

`det(W_{X'}ᵀ W_{Y'})` over `ZMod ℓ` is the reduction of the `ℓ`-integral rational
`det[∑_{a<K} 1/((x-a)(y-a))]` (all `x-a, y-a ∈ [1, ℓ-1]`), which is the closed form of
`Delta_closed` at `θ = 0`, an `ℓ`-unit by `Delta_LU`.
-/

@[expose] public section

open Finset Matrix CatalanCore CatalanCore.Rect CatalanCore.ThmA CatalanCore.Star CatalanCore.Star.Leonard

namespace CatalanFrames.LambdaHybrid.NV

variable {ℓ : ℕ} [Fact ℓ.Prime]

/-- `ℓ`-integral inverse of a natural number in `(0, ℓ)`. -/
noncomputable def invR (ℓ : ℕ) [Fact ℓ.Prime] (N : ℕ) : Rl ℓ :=
  if h : 0 < N ∧ N < ℓ then ⟨(N : ℚ)⁻¹, (LU_natCast_lt h.1 h.2).2.2⟩ else 0

lemma invR_val {N : ℕ} (h0 : 0 < N) (hN : N < ℓ) : ((invR ℓ N : Rl ℓ) : ℚ) = (N : ℚ)⁻¹ := by
  simp [invR, h0, hN]

lemma phi_invR {N : ℕ} (h0 : 0 < N) (hN : N < ℓ) :
    phi ℓ (invR ℓ N) = ((N : ℕ) : ZMod ℓ)⁻¹ := by
  have hNr : (N : ℚ) ∈ Rl ℓ := (LU_natCast_lt (l := ℓ) h0 hN).2.1
  have h1 : phi ℓ (invR ℓ N) * phi ℓ ⟨(N : ℚ), hNr⟩ = 1 := by
    rw [← map_mul, ← map_one (phi ℓ)]
    congr 1
    apply Subtype.ext
    simp [invR_val h0 hN, h0.ne']
  have h2 : phi ℓ ⟨(N : ℚ), hNr⟩ = (N : ZMod ℓ) := by
    simp [phi_apply]
  rw [h2] at h1
  exact eq_inv_of_mul_eq_one_left h1

/-- The `ℚ`-matrix `[∑_{a<K} 1/((x_i - a)(y_j - a))]`. -/
noncomputable def Mq (K : ℕ) (G : Geometry) : Matrix (Fin G.k) (Fin G.k) ℚ :=
  Matrix.of fun i j => ∑ a : Fin K, (((G.xs i - (a : ℕ) : ℕ) : ℚ))⁻¹ * (((G.ys j - (a : ℕ) : ℕ) : ℚ))⁻¹

theorem det_WXWY_phi (K : ℕ) (G : Geometry) (hx : ∀ i, K ≤ G.xs i ∧ G.xs i < ℓ)
    (hy : ∀ i, K ≤ G.ys i ∧ G.ys i < ℓ) :
    ∃ d : Rl ℓ, ((d : Rl ℓ) : ℚ) = (Mq K G).det ∧
      phi ℓ d = ((WX ℓ K G)ᵀ * WY ℓ K G).det := by
  let M : Matrix (Fin G.k) (Fin G.k) (Rl ℓ) := Matrix.of fun i j =>
    ∑ a : Fin K, invR ℓ (G.xs i - (a : ℕ)) * invR ℓ (G.ys j - (a : ℕ))
  refine ⟨M.det, ?_, ?_⟩
  · have h := (Rl ℓ).subtype.map_det M
    simp only [Subring.subtype_apply] at h
    rw [h]
    congr 1
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, M, Matrix.of_apply, Mq]
    rw [map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    have a1 := hx i; have a2 := hy j; have a3 := a.2
    rw [map_mul, Subring.subtype_apply, Subring.subtype_apply,
      invR_val (by omega) (by omega), invR_val (by omega) (by omega)]
  · rw [(phi ℓ).map_det]
    congr 1
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, M, Matrix.of_apply, Matrix.mul_apply,
      Matrix.transpose_apply, WX, WY, Wnode]
    rw [map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    have a1 := hx i; have a2 := hy j; have a3 := a.2
    rw [map_mul, phi_invR (by omega) (by omega), phi_invR (by omega) (by omega),
      Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    rw [← neg_sub (a : ZMod ℓ), ← neg_sub (a : ZMod ℓ)]
    rw [one_div, one_div, inv_neg, inv_neg, neg_mul_neg]

theorem Mq_after_eq (K m r : ℕ) (hrK : K ≤ r) :
    (Mq K (after r m)).submatrix (finCongr (after_k r m).symm) (finCongr (after_k r m).symm) =
      ((Wb K (0 : ℚ) (bX m ((r - K : ℕ) : ℤ)))ᵀ * Wb K (0 : ℚ) (bY m ((r - K : ℕ) : ℤ)))ᵀ := by
  ext i j
  simp only [Matrix.submatrix_apply, Mq, Matrix.of_apply, Matrix.transpose_apply, Matrix.mul_apply,
    Wb, wcol, bX, bY, after_xs, after_ys, finCongr_apply, Fin.val_cast]
  rw [← Equiv.sum_comp Fin.revPerm]
  refine Finset.sum_congr rfl fun a _ => ?_
  have ha := a.2
  simp only [Fin.revPerm_apply, Fin.val_rev]
  have e1 : r + 2 * (i : ℕ) - (K - ((a : ℕ) + 1)) = (r - K) + 1 + 2 * (i : ℕ) + (a : ℕ) := by omega
  have e2 : r + 2 * (j : ℕ) + 1 - (K - ((a : ℕ) + 1)) = (r - K) + 2 + 2 * (j : ℕ) + (a : ℕ) := by omega
  rw [e1, e2]
  push_cast
  rw [one_div, one_div, mul_comm]
  congr 2 <;> ring

/-- **`hΔ` discharged.** For `1 ≤ K`, `m ≤ K ≤ r`, `r + 2m ≤ ℓ`, the border determinant of the
hybrid geometry `after r m` is a unit of `𝔽_ℓ`. -/
theorem hDelta_after (K m r : ℕ) (hK : 1 ≤ K) (hmK : m ≤ K) (hrK : K ≤ r) (hrl : r + 2 * m ≤ ℓ) :
    IsUnit ((WX ℓ K (after r m))ᵀ * WY ℓ K (after r m)).det := by
  have hk := after_k r m
  obtain ⟨d, hd1, hd2⟩ := det_WXWY_phi (ℓ := ℓ) K (after r m)
    (fun i => by rw [after_xs]; have := i.2; omega)
    (fun i => by rw [after_ys]; have := i.2; omega)
  have hdet : (Mq K (after r m)).det =
      ((Wb K (0 : ℚ) (bX m ((r - K : ℕ) : ℤ)))ᵀ * Wb K (0 : ℚ) (bY m ((r - K : ℕ) : ℤ))).det := by
    rw [← Matrix.det_submatrix_equiv_self (finCongr (after_k r m).symm), Mq_after_eq K m r hrK,
      Matrix.det_transpose]
  have hLU : LU ℓ (Mq K (after r m)).det := by
    rw [hdet]
    exact Delta_LU K m (r - K) hmK hK (by omega)
  have hinv : ((Mq K (after r m)).det)⁻¹ ∈ Rl ℓ := hLU.2.2
  let d' : Rl ℓ := ⟨((Mq K (after r m)).det)⁻¹, hinv⟩
  have hdd : d * d' = 1 := by
    apply Subtype.ext
    simp only [Subring.coe_mul, Subring.coe_one, d']
    rw [hd1]; exact mul_inv_cancel₀ hLU.1
  rw [← hd2]
  exact IsUnit.of_mul_eq_one (phi ℓ d') (by rw [← map_mul, hdd, map_one])

end CatalanFrames.LambdaHybrid.NV
