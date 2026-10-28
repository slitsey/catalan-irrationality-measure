module
public import CatalanCore.Uniform.Decay.Nodes.SelfEnergy
@[expose] public section

/-!
# Self-energy lower bound in scaled coordinates

* `Hfun_scale`, `pairEnergy_scale`, `mutE_scale`: scaling of the closed-form energies,
  `I_phys = r² I - r² (log r) m²`.
* `rows_as_scaled`/`cols_as_scaled`:
  `r² I(μ_R) - E ≤ ∑_{a,b ∈ R_r} elog (a/r) (b/r)`, with the explicit `E` below (the paper's
  `r² I_0 - O(r log r)`), uniform in the balancing trim.
-/

namespace CatalanCore.Uniform
open Decay.Nodes Finset CatalanLambda.Decay

namespace Decay.Nodes

theorem Hfun_scale {r : ℝ} (hr : 0 < r) (s : ℝ) :
    Hfun (r * s) = r ^ 2 * Hfun s + (1 / 2) * r ^ 2 * s ^ 2 * Real.log r := by
  by_cases hs : s = 0
  · subst hs; simp [Hfun]
  · unfold Hfun
    rw [Real.log_mul hr.ne' hs]
    ring

theorem pairEnergy_scale {r : ℝ} (hr : 0 < r) (a b c d : ℝ) :
    pairEnergy (r * a) (r * b) (r * c) (r * d) =
      r ^ 2 * pairEnergy a b c d - r ^ 2 * Real.log r * ((b - a) * (d - c)) := by
  unfold pairEnergy
  rw [← mul_sub, ← mul_sub, ← mul_sub, ← mul_sub, Hfun_scale hr, Hfun_scale hr, Hfun_scale hr,
    Hfun_scale hr]
  ring

/-- Scaling of a piece (`lo, hi ↦ r lo, r hi`). -/
def pscaleR (r : ℝ) (P : Piece) : Piece := ⟨P.w, P.lo * r, P.hi * r⟩

theorem pairInteraction_scale {r : ℝ} (hr : 0 < r) (P Q : Piece) :
    pairInteraction (pscaleR r P) (pscaleR r Q) =
      r ^ 2 * pairInteraction P Q - r ^ 2 * Real.log r * (P.mass * Q.mass) := by
  unfold pairInteraction pscaleR Piece.mass
  simp only
  rw [mul_comm P.lo r, mul_comm P.hi r, mul_comm Q.lo r, mul_comm Q.hi r,
    pairEnergy_scale hr]
  ring

theorem mutE_scale {r : ℝ} (hr : 0 < r) (ps qs : List Piece) :
    mutE (ps.map (pscaleR r)) (qs.map (pscaleR r)) =
      r ^ 2 * mutE ps qs - r ^ 2 * Real.log r * (pmass ps * pmass qs) := by
  induction ps with
  | nil => simp [mutE_nil_left, pmass]
  | cons P ps ih =>
    rw [List.map_cons, mutE_cons_left, mutE_cons_left, ih]
    have h1 : ((qs.map (pscaleR r)).map fun Q => pairInteraction (pscaleR r P) Q).sum =
        r ^ 2 * (qs.map fun Q => pairInteraction P Q).sum -
          r ^ 2 * Real.log r * (P.mass * pmass qs) := by
      rw [List.map_map]
      have : (qs.map ((fun Q => pairInteraction (pscaleR r P) Q) ∘ pscaleR r)) =
          qs.map (fun Q => r ^ 2 * pairInteraction P Q -
            r ^ 2 * Real.log r * (P.mass * Q.mass)) :=
        List.map_congr_left (fun Q _ => pairInteraction_scale hr P Q)
      rw [this, lsum_sub, List.sum_map_mul_left, List.sum_map_mul_left]
      unfold pmass
      rw [← List.sum_map_mul_left]
      simp [List.sum_map_mul_left]
    rw [h1]
    unfold pmass
    simp only [List.map_cons, List.sum_cons]
    ring

/-- Passing from physical to scaled coordinates for a node set `A` of distinct naturals. -/
theorem as_scaled_eq (A : Finset ℕ) {r : ℕ} (hr : 0 < r) :
    ∑ a ∈ A, ∑ b ∈ A, elog ((a : ℂ) / r) ((b : ℂ) / r) =
      ∑ a ∈ A, ∑ b ∈ A, elog (a : ℂ) (b : ℂ) +
        (A.card : ℝ) * ((A.card : ℝ) - 1) * Real.log r := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hterm : ∀ a b : ℕ, elog ((a : ℂ) / r) ((b : ℂ) / r) =
      elog (a : ℂ) (b : ℂ) + (if b = a then 0 else Real.log r) := by
    intro a b
    by_cases hba : b = a
    · subst hba; simp [elog]
    · rw [if_neg hba]
      have hne : ‖(a : ℂ) - (b : ℂ)‖ ≠ 0 := by
        apply norm_ne_zero_iff.mpr
        exact sub_ne_zero.mpr (by exact_mod_cast Ne.symm hba)
      unfold elog
      have : (a : ℂ) / r - (b : ℂ) / r = ((a : ℂ) - (b : ℂ)) / r := by ring
      rw [this, norm_div, Complex.norm_natCast, Real.log_div hne hr'.ne']
      ring
  have hrow : ∀ a ∈ A, ∑ b ∈ A, elog ((a : ℂ) / r) ((b : ℂ) / r) =
      ∑ b ∈ A, elog (a : ℂ) (b : ℂ) + ((A.card : ℝ) - 1) * Real.log r := by
    intro a ha
    simp_rw [hterm]
    rw [Finset.sum_add_distrib]
    congr 1
    have h1 : ∑ b ∈ A, (if b = a then (0 : ℝ) else Real.log r) =
        ∑ b ∈ A.erase a, (if b = a then (0 : ℝ) else Real.log r) :=
      (Finset.sum_erase _ (by simp)).symm
    rw [h1, Finset.sum_congr rfl (fun b hb => if_neg (Finset.mem_erase.mp hb).1),
      Finset.sum_const, nsmul_eq_mul, Finset.card_erase_of_mem ha]
    have : 1 ≤ A.card := Finset.card_pos.mpr ⟨a, ha⟩
    rw [Nat.cast_sub this]
    simp
  rw [Finset.sum_congr rfl hrow, Finset.sum_add_distrib]
  simp only [Finset.sum_const, nsmul_eq_mul]
  ring

end Decay.Nodes

namespace BlockGeom

/-- **Self-energy, rows (scaled)**: the counting self-energy of the scaled row list is at least
`r² I(μ_R)` minus an explicit `O(r log r)` error.  Uniform in `r` and in the balancing trim. -/
theorem rows_as_scaled (G : BlockGeom) {r : ℕ} (hr : 0 < r) {Bd : ℝ}
    (hBd0 : 0 ≤ Bd) (hBc : ∀ i, ((G.common.block i).v : ℝ) ≤ Bd)
    (hBr : ∀ i, ((G.row.block i).v : ℝ) ≤ Bd) :
    (r : ℝ) ^ 2 * selfEnergy G.rowPieces
      - (((G.geometry r).rows.card : ℝ) * (G.rowConstR * (3 * Real.log (Bd * r + 1)))
        + ((G.rowU r).map fun P' => P'.w * (6 * pmass (G.rowU r) +
          G.rowConstR * (5 * ((P'.hi - P'.lo) * ((1 / 2) * Real.log (1 + (Bd * r) ^ 2)))))).sum)
      - (G.rowConst * (((G.geometry r).rows.card : ℝ) + r * (G.totalMass : ℝ)) +
          ((G.geometry r).rows.card : ℝ)) * Real.log r
    ≤ ∑ a ∈ (G.geometry r).rows, ∑ b ∈ (G.geometry r).rows,
        elog ((a : ℂ) / r) ((b : ℂ) / r) := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hphys := G.rows_as_phys (r := r) hBd0 hBc hBr
  have hsc : mutE (G.rowU r) (G.rowU r) =
      (r : ℝ) ^ 2 * selfEnergy G.rowPieces -
        (r : ℝ) ^ 2 * Real.log r * ((G.totalMass : ℝ) * (G.totalMass : ℝ)) := by
    rw [G.rowU_eq r]
    have := mutE_scale hr' G.rowPieces G.rowPieces
    rw [G.pmass_rowPieces] at this
    unfold selfEnergy
    exact this
  have heq := as_scaled_eq (G.geometry r).rows hr
  rw [heq]
  have hcard := abs_le.mp (G.card_rows_bound r)
  have hlog : 0 ≤ Real.log r := Real.log_nonneg (by exact_mod_cast hr)
  set N : ℝ := ((G.geometry r).rows.card : ℝ) with hN
  set M : ℝ := (G.totalMass : ℝ) with hM
  have hM0 : 0 ≤ M := by
    rw [hM]
    have : 0 ≤ G.totalMass := by
      unfold BlockGeom.totalMass BlockGeom.gamma BlockGeom.beta
      have := G.common_pos
      have h2 : 0 ≤ G.row.mass := by
        unfold BlockCollection.mass
        exact Finset.sum_nonneg (fun i _ => (G.row.block i).mass_pos.le)
      linarith
    exact_mod_cast this
  have hN0 : 0 ≤ N := Nat.cast_nonneg _
  have hprod : -(G.rowConst * (N + r * M)) ≤ (N - M * r) * (N + M * r) := by
    have h1 : -(G.rowConst : ℝ) ≤ N - M * r := by linarith [hcard.1]
    have h2 : 0 ≤ N + M * r := by positivity
    nlinarith [mul_le_mul_of_nonneg_right h1 h2]
  have hkey : (N * (N - 1) - r ^ 2 * M * M) * Real.log r ≥
      -((G.rowConst * (N + r * M) + N) * Real.log r) := by
    have : N * (N - 1) - r ^ 2 * M * M ≥ -(G.rowConst * (N + r * M) + N) := by
      nlinarith [hprod]
    nlinarith [mul_le_mul_of_nonneg_right this hlog]
  rw [hsc] at hphys
  nlinarith [hphys, hkey]

/-- **Self-energy, columns (scaled)**: the counting self-energy of the scaled column list is at least
`r² I(μ_Q)` minus an explicit `O(r log r)` error.  Uniform in `r` and in the balancing trim. -/
theorem cols_as_scaled (G : BlockGeom) {r : ℕ} (hr : 0 < r) {Bd : ℝ}
    (hBd0 : 0 ≤ Bd) (hBc : ∀ i, ((G.common.block i).v : ℝ) ≤ Bd)
    (hBq : ∀ i, ((G.column.block i).v : ℝ) ≤ Bd) :
    (r : ℝ) ^ 2 * selfEnergy G.colPieces
      - (((G.geometry r).cols.card : ℝ) * (G.colConstR * (3 * Real.log (Bd * r + 1)))
        + ((G.colU r).map fun P' => P'.w * (6 * pmass (G.colU r) +
          G.colConstR * (5 * ((P'.hi - P'.lo) * ((1 / 2) * Real.log (1 + (Bd * r) ^ 2)))))).sum)
      - (G.colConst * (((G.geometry r).cols.card : ℝ) + r * (G.totalMass : ℝ)) +
          ((G.geometry r).cols.card : ℝ)) * Real.log r
    ≤ ∑ a ∈ (G.geometry r).cols, ∑ b ∈ (G.geometry r).cols,
        elog ((a : ℂ) / r) ((b : ℂ) / r) := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hphys := G.cols_as_phys (r := r) hBd0 hBc hBq
  have hsc : mutE (G.colU r) (G.colU r) =
      (r : ℝ) ^ 2 * selfEnergy G.colPieces -
        (r : ℝ) ^ 2 * Real.log r * ((G.totalMass : ℝ) * (G.totalMass : ℝ)) := by
    rw [G.colU_eq r]
    have := mutE_scale hr' G.colPieces G.colPieces
    rw [G.pmass_colPieces] at this
    unfold selfEnergy
    exact this
  have heq := as_scaled_eq (G.geometry r).cols hr
  rw [heq]
  have hcard := abs_le.mp (G.card_cols_bound r)
  have hlog : 0 ≤ Real.log r := Real.log_nonneg (by exact_mod_cast hr)
  set N : ℝ := ((G.geometry r).cols.card : ℝ) with hN
  set M : ℝ := (G.totalMass : ℝ) with hM
  have hM0 : 0 ≤ M := by
    rw [hM]
    have : 0 ≤ G.totalMass := by
      unfold BlockGeom.totalMass BlockGeom.gamma BlockGeom.beta
      have := G.common_pos
      have h2 : 0 ≤ G.row.mass := by
        unfold BlockCollection.mass
        exact Finset.sum_nonneg (fun i _ => (G.row.block i).mass_pos.le)
      linarith
    exact_mod_cast this
  have hN0 : 0 ≤ N := Nat.cast_nonneg _
  have hprod : -(G.colConst * (N + r * M)) ≤ (N - M * r) * (N + M * r) := by
    have h1 : -(G.colConst : ℝ) ≤ N - M * r := by linarith [hcard.1]
    have h2 : 0 ≤ N + M * r := by positivity
    nlinarith [mul_le_mul_of_nonneg_right h1 h2]
  have hkey : (N * (N - 1) - r ^ 2 * M * M) * Real.log r ≥
      -((G.colConst * (N + r * M) + N) * Real.log r) := by
    have : N * (N - 1) - r ^ 2 * M * M ≥ -(G.colConst * (N + r * M) + N) := by
      nlinarith [hprod]
    nlinarith [mul_le_mul_of_nonneg_right this hlog]
  rw [hsc] at hphys
  nlinarith [hphys, hkey]

end BlockGeom

end CatalanCore.Uniform
