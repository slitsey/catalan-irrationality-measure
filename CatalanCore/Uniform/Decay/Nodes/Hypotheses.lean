module
public import CatalanCore.Uniform.Decay.Nodes.SelfScaled
public import CatalanCore.Uniform.Decay.Nodes.EnergyBlock
@[expose] public section

/-!
# The three node-sum hypotheses of `energy_block`, for a `BlockGeom`

* `BlockGeom.ps_hyp`: free-point potentials of the row and column lists,
  `PS_R + PS_Q ≤ 2 r U(z/r) + E1 + E2 |Im z| / r`, `U = (U_{μ_R} + U_{μ_Q})/2` (average).
* `BlockGeom.rs_hyp`: punctured node potentials.
* `BlockGeom.as_hyp`: self-energies, `AS_R + AS_Q ≥ 2 r² J_node - E4`, `J_node` the average of the
  separate row and column energies (not the energy of the averaged measure).

All error terms are explicit and `O(r log r)`; they depend only on the finite block data.
-/

namespace CatalanCore.Uniform
open Decay.Nodes Finset CatalanLambda.Decay

theorem log_add_le' {x y : ℝ} (hx : 0 < x) (hy : 0 ≤ y) : Real.log (x + y) ≤ Real.log x + y / x := by
  have h := Real.log_le_sub_one_of_pos (show 0 < 1 + y / x by positivity)
  have e : Real.log (x + y) = Real.log x + Real.log (1 + y / x) := by
    rw [← Real.log_mul hx.ne' (by positivity)]
    congr 1; field_simp
  rw [e]; linarith

/-- The averaged node potential `U = (U_{μ_R} + U_{μ_Q}) / 2`. -/
noncomputable def BlockGeom.nodePot (G : BlockGeom) (σ : ℂ) : ℝ :=
  (ppotC G.rowPieces σ + ppotC G.colPieces σ) / 2

namespace BlockGeom

/-- Error terms of the free-point hypothesis. -/
noncomputable def E1 (G : BlockGeom) (r : ℕ) (Bd a0 m0 : ℝ) : ℝ :=
  ((G.rowConstR : ℝ) + G.colConstR) * (6 * |Real.log m0| + 3 * Real.log (1 + (a0 + Bd) * r)) +
    ((G.rowConst : ℝ) + G.colConst) * Real.log r

noncomputable def E2 (G : BlockGeom) : ℝ := 6 * ((G.rowConstR : ℝ) + G.colConstR)

/-- **Free-point hypothesis** of `energy_block`. -/
theorem ps_hyp (G : BlockGeom) {r : ℕ} (hr : 0 < r) {Bd m0 a0 : ℝ}
    (hBd0 : 0 ≤ Bd) (hBc : ∀ i, ((G.common.block i).v : ℝ) ≤ Bd)
    (hBr : ∀ i, ((G.row.block i).v : ℝ) ≤ Bd) (hBq : ∀ i, ((G.column.block i).v : ℝ) ≤ Bd)
    (hm0 : 0 < m0) (ha1 : 1 ≤ a0) (z : ℂ) (hre : m0 ≤ -z.re)
    (hnorm : ‖z‖ ≤ a0 * r + 2 * |z.im|) :
    (∑ j ∈ (G.geometry r).rows, elog (z / r) ((j : ℂ) / r)) +
        (∑ j ∈ (G.geometry r).cols, elog (z / r) ((j : ℂ) / r)) ≤
      2 * (r * G.nodePot (z / r)) + G.E1 r Bd a0 m0 + G.E2 * |z.im| / r := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hb : 0 ≤ Bd * r := by positivity
  set M : ℝ := ‖z‖ + Bd * r with hM
  have hd : ∀ t ∈ Set.Icc (0 : ℝ) (Bd * r), m0 ≤ ‖z - (t : ℂ)‖ := by
    intro t ht
    have h1 : |(z - (t : ℂ)).re| ≤ ‖z - (t : ℂ)‖ := Complex.abs_re_le_norm _
    have h2 : (z - (t : ℂ)).re = z.re - t := by simp
    rw [h2] at h1
    have h3 : -(z.re - t) ≤ |z.re - t| := neg_le_abs _
    linarith [ht.1]
  have hMM : ∀ t ∈ Set.Icc (0 : ℝ) (Bd * r), ‖z - (t : ℂ)‖ ≤ M := by
    intro t ht
    have h1 := norm_sub_le z (t : ℂ)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1] at h1
    linarith [ht.2]
  have hnz : m0 ≤ ‖z‖ := by
    have h1 : |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm z
    have h3 : -z.re ≤ |z.re| := neg_le_abs _
    linarith
  have hMge : m0 ≤ M := by rw [hM]; have : 0 ≤ Bd * r := hb; linarith
  have hlogM : |Real.log M| ≤ Real.log (1 + M) + |Real.log m0| := by
    by_cases h1 : 1 ≤ M
    · rw [abs_of_nonneg (Real.log_nonneg h1)]
      have := Real.log_le_log (by linarith) (show M ≤ 1 + M by linarith)
      have := abs_nonneg (Real.log m0)
      linarith
    · push Not at h1
      have : Real.log m0 ≤ Real.log M := Real.log_le_log hm0 hMge
      have h2 : Real.log M ≤ 0 := Real.log_nonpos (by linarith) h1.le
      rw [abs_of_nonpos h2]
      have : 0 ≤ Real.log (1 + M) := Real.log_nonneg (by linarith)
      have := neg_abs_le (Real.log m0)
      linarith
  have hlog1M : Real.log (1 + M) ≤ Real.log (1 + (a0 + Bd) * r) + 2 * |z.im| / r := by
    have hx : 0 < 1 + (a0 + Bd) * r := by positivity
    have hle : 1 + M ≤ (1 + (a0 + Bd) * r) + 2 * |z.im| := by
      rw [hM]; nlinarith [hnorm]
    have h1 := Real.log_le_log (by linarith [norm_nonneg z, hb]) hle
    have h2 := log_add_le' hx (by positivity : 0 ≤ 2 * |z.im|)
    have h3 : 2 * |z.im| / (1 + (a0 + Bd) * r) ≤ 2 * |z.im| / r := by
      apply div_le_div_of_nonneg_left (by positivity) hr'
      nlinarith
    linarith
  -- generic bound for one side
  have side : ∀ D : ℝ, 0 ≤ D → D * (|kern z (Bd * r)| + 2 * (Real.log M - Real.log m0)) ≤
      D * (6 * |Real.log m0| + 3 * Real.log (1 + (a0 + Bd) * r) + 6 * |z.im| / r) := by
    intro D hD
    refine mul_le_mul_of_nonneg_left ?_ hD
    have hbm : Bd * r ∈ Set.Icc (0 : ℝ) (Bd * r) := ⟨hb, le_rfl⟩
    have k1 := kern_le hb hm0 hd hbm
    have k2 := ge_kern hb hm0 hd hMM hbm
    have hk : |kern z (Bd * r)| ≤ |Real.log M| + |Real.log m0| := by
      rw [abs_le]
      constructor
      · have := le_abs_self (Real.log M); have := abs_nonneg (Real.log m0); linarith
      · have := neg_le_abs (Real.log m0); have := abs_nonneg (Real.log M); linarith
    have e1 : Real.log M - Real.log m0 ≤ |Real.log M| + |Real.log m0| := by
      have := le_abs_self (Real.log M); have := neg_le_abs (Real.log m0); linarith
    have : 6 * |z.im| / r = 3 * (2 * |z.im| / r) := by ring
    nlinarith [hlogM, hlog1M, hk, e1, abs_nonneg (Real.log m0)]
  have hrow := G.rows_ps_scaled hr z hBd0 hBc hBr hm0 hd hMM
  have hcol := G.cols_ps_scaled hr z hBd0 hBc hBq hm0 hd hMM
  have hsr := side (G.rowConstR : ℝ) (Nat.cast_nonneg _)
  have hsc := side (G.colConstR : ℝ) (Nat.cast_nonneg _)
  have hlogr : 0 ≤ Real.log r := Real.log_nonneg (by exact_mod_cast hr)
  have hrow' := (abs_le.mp hrow).2
  have hcol' := (abs_le.mp hcol).2
  unfold nodePot E1 E2
  have e3 : ((G.rowConstR : ℝ) + G.colConstR) * (6 * |z.im| / r) =
      (6 * ((G.rowConstR : ℝ) + G.colConstR)) * |z.im| / r := by ring
  nlinarith [hrow', hcol', hsr, hsc, e3]

/-- Error term of the punctured-node hypothesis. -/
noncomputable def E3 (G : BlockGeom) (r : ℕ) (Bd : ℝ) : ℝ :=
  ((G.rowConstR : ℝ) + G.colConstR) * (3 * Real.log (Bd * r + 1)) + 4 +
    ((G.rowConst : ℝ) + G.colConst) * Real.log r

/-- **Punctured-node hypothesis** of `energy_block` at a common node `a`. -/
theorem rs_hyp (G : BlockGeom) {r : ℕ} (hr : 0 < r) {Bd : ℝ}
    (hBd0 : 0 ≤ Bd) (hBc : ∀ i, ((G.common.block i).v : ℝ) ≤ Bd)
    (hBr : ∀ i, ((G.row.block i).v : ℝ) ≤ Bd) (hBq : ∀ i, ((G.column.block i).v : ℝ) ≤ Bd)
    {a : ℕ} (har : a ∈ (G.geometry r).rows) (hac : a ∈ (G.geometry r).cols) :
    (∑ b ∈ (G.geometry r).rows, elog ((a : ℂ) / r) ((b : ℂ) / r)) +
        (∑ b ∈ (G.geometry r).cols, elog ((a : ℂ) / r) ((b : ℂ) / r)) ≤
      2 * (r * G.nodePot ((a : ℂ) / r)) + G.E3 r Bd := by
  have h1 := G.rows_rs_scaled hr hBd0 hBc hBr har
  have h2 := G.cols_rs_scaled hr hBd0 hBc hBq hac
  unfold nodePot E3
  nlinarith [h1, h2]

/-- Error term of the self-energy hypothesis. -/
noncomputable def E4 (G : BlockGeom) (r : ℕ) (Bd : ℝ) : ℝ :=
  (((G.geometry r).rows.card : ℝ) * (G.rowConstR * (3 * Real.log (Bd * r + 1)))
        + ((G.rowU r).map fun P' => P'.w * (6 * pmass (G.rowU r) +
          G.rowConstR * (5 * ((P'.hi - P'.lo) * ((1 / 2) * Real.log (1 + (Bd * r) ^ 2)))))).sum)
      + (G.rowConst * (((G.geometry r).rows.card : ℝ) + r * (G.totalMass : ℝ)) +
          ((G.geometry r).rows.card : ℝ)) * Real.log r
  + ((((G.geometry r).cols.card : ℝ) * (G.colConstR * (3 * Real.log (Bd * r + 1)))
        + ((G.colU r).map fun P' => P'.w * (6 * pmass (G.colU r) +
          G.colConstR * (5 * ((P'.hi - P'.lo) * ((1 / 2) * Real.log (1 + (Bd * r) ^ 2)))))).sum)
      + (G.colConst * (((G.geometry r).cols.card : ℝ) + r * (G.totalMass : ℝ)) +
          ((G.geometry r).cols.card : ℝ)) * Real.log r)

/-- **Self-energy hypothesis** of `energy_block`:
`AS_R + AS_Q ≥ 2 r² J_node - E4`, with `J_node` the AVERAGE of the separate row and column
self-energies. -/
theorem as_hyp (G : BlockGeom) {r : ℕ} (hr : 0 < r) {Bd : ℝ}
    (hBd0 : 0 ≤ Bd) (hBc : ∀ i, ((G.common.block i).v : ℝ) ≤ Bd)
    (hBr : ∀ i, ((G.row.block i).v : ℝ) ≤ Bd) (hBq : ∀ i, ((G.column.block i).v : ℝ) ≤ Bd) :
    2 * (r : ℝ) ^ 2 * G.nodeEnergy - G.E4 r Bd ≤
      (∑ a ∈ (G.geometry r).rows, ∑ b ∈ (G.geometry r).rows,
          elog ((a : ℂ) / r) ((b : ℂ) / r)) +
        (∑ a ∈ (G.geometry r).cols, ∑ b ∈ (G.geometry r).cols,
          elog ((a : ℂ) / r) ((b : ℂ) / r)) := by
  have h1 := G.rows_as_scaled hr hBd0 hBc hBr
  have h2 := G.cols_as_scaled hr hBd0 hBc hBq
  have hJ : G.nodeEnergy = (selfEnergy G.rowPieces + selfEnergy G.colPieces) / 2 := rfl
  unfold E4
  rw [hJ]
  linarith

end BlockGeom
end CatalanCore.Uniform
