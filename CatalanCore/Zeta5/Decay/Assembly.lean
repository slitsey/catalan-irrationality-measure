module

public import CatalanCore.Zeta5.Decay.Tail
public import CatalanCore.Zeta5.Energy.All
public import CatalanCore.Zeta5.Criterion.Final

@[expose] public section

/-!
# Z5-DECAY, part 2: the decay assembly (ZD32, ZD33, ZD34) and `zeta5_decay`

Producer: `real_bound_nu` (Z5-ENERGY): for `n > 0`, `F_{40n}(ξ) > 0` and
`log F ≤ (C* + λM₀ - I(ν)) K² + 24 K log K + (47 + 2 C_circ) K`, `K = 40 n`, at `ν = nu c N b`
under `CellHyp (nu c N b) M₀`.  Consumer: `DecayAtConst D` of `Criterion.Final`
(`∀ δ > 0, ∃ N0, ∀ n ≥ N0, F_{40n}(ξ) ≤ exp (-(D - δ) (40 n)²)`).

* ZD32: `nu_support`, `nu_noAtoms`.
* ZD33: `zd33_log_eventually` (`log F_K ≤ -(D - δ) K²` eventually, i.e. `limsup K⁻² log F_K ≤ -D`
  in its `δ`-form), with `D = Dnu c N b M₀ = I(ν) - λM₀ - C*`.
* ZD34: `decay_nu_const : DecayAtConst (Dnu c N b M₀)` from `CellHyp`.
* `zeta5_decay`: `DecayAtConst (138500086/10^8)` from the bounded-region cell inequality and the
  exact constant inequality `138500086/10^8 ≤ Dnu c N b M₀` (ZD22, supplied by Z5-CELLS,
  see `Dnu_eq` for the match with its `Dval`).
-/

open MeasureTheory Set Filter Topology CatalanCore.Zeta5.Potential CatalanCore.Zeta5.Energy

namespace CatalanCore.Zeta5.Decay

/-! ### ZD32: support and no atoms -/

/-- `ν = nu c N b` lives on `[0, b]` (ZD32). -/
theorem nu_support {c : ℕ → ℝ} {N : ℕ} {b : ℝ} (hb : 0 ≤ b) : nu c N b (Icc 0 b)ᶜ = 0 :=
  nu_compl_Icc hb

/-- `ν = nu c N b` has no atom anywhere (ZD32; via the arcsine majorant, ZD04). -/
theorem nu_noAtoms {c : ℕ → ℝ} {N : ℕ} {b : ℝ} (hb : 0 < b) (x : ℝ) : nu c N b {x} = 0 :=
  (arcMaj_nu (c := c) (N := N) hb).singleton_zero x

/-! ### The decay rate -/

/-- `D = I(ν) - λ M₀ - C*` with `I(ν) = c₀² log(b/4) - Σ_{k ≥ 1} c_k²/(2k)` (ZD14, ZD22). -/
noncomputable def Dnu (c : ℕ → ℝ) (N : ℕ) (b M₀ : ℝ) : ℝ :=
  (c 0 ^ 2 * Real.log (b / 4) - ∑ k ∈ Finset.range N, c (k + 1) ^ 2 / (2 * ((k + 1 : ℕ) : ℝ))) -
    lam * M₀ - Cstar

/-- The match with the exact-constant row ZD22 (`Cells.Dval`): with `c₀ = λ`,
`D = (λ² log(b/4) - E) - λ M₀ - (-2λ + 12αλ(1 - log α) + 3λ² - 2λ² log(2λ))`, `E = Σ c_k²/(2k)`. -/
theorem Dnu_eq {c : ℕ → ℝ} (N : ℕ) (b M₀ : ℝ) (h0 : c 0 = 37 / 40) :
    Dnu c N b M₀ =
      (lam ^ 2 * Real.log (b / 4) -
          ∑ k ∈ Finset.range N, c (k + 1) ^ 2 / (2 * ((k + 1 : ℕ) : ℝ))) - lam * M₀ -
        (-2 * lam + 12 * alph * lam * (1 - Real.log alph) + 3 * lam ^ 2 -
          2 * lam ^ 2 * Real.log (2 * lam)) := by
  unfold Dnu Cstar
  rw [h0]

/-! ### The `K log K` and `K` terms are absorbed -/

lemma loglin_eventually (A δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, 24 * Kr n * Real.log (Kr n) + A * Kr n ≤ δ * Kr n ^ 2 := by
  have hK : Tendsto (fun n : ℕ => Kr n) atTop atTop :=
    Filter.Tendsto.const_mul_atTop (by norm_num) tendsto_natCast_atTop_atTop
  have h1 : ∀ᶠ x : ℝ in atTop, ‖Real.log x‖ ≤ δ / 48 * ‖x‖ :=
    Real.isLittleO_log_id_atTop.bound (by positivity)
  have h2 : ∀ᶠ x : ℝ in atTop, 2 * |A| / δ ≤ x := eventually_ge_atTop _
  have h3 : ∀ᶠ x : ℝ in atTop, 0 < x := eventually_gt_atTop 0
  filter_upwards [hK.eventually (h1.and (h2.and h3))] with n hn
  obtain ⟨a, b, c⟩ := hn
  have hlog : Real.log (Kr n) ≤ δ / 48 * Kr n := by
    have := le_trans (le_abs_self _) (by simpa [Real.norm_eq_abs, abs_of_pos c] using a)
    exact this
  have hA : A ≤ δ / 2 * Kr n := by
    have h4 : 2 * |A| ≤ δ * Kr n := by
      rw [div_le_iff₀ hδ] at b; linarith
    nlinarith [le_abs_self A]
  have hKpos := c
  have h5 : 24 * Real.log (Kr n) + A ≤ δ * Kr n := by linarith
  nlinarith [mul_le_mul_of_nonneg_left h5 hKpos.le]

/-- **ZD33** (`δ`-form of `limsup K⁻² log F_K(ξ) ≤ -D`): for `CellHyp`, every `δ > 0` and all
large `n`, `log F_{40n}(ξ) ≤ -(D - δ) (40 n)²`, with `D = Dnu c N b M₀`. -/
theorem zd33_log_eventually {c : ℕ → ℝ} {N : ℕ} {b : ℝ} (hb : 0 < b)
    (hpos : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ chebF c N x) (h0 : c 0 = 37 / 40) {M₀ : ℝ}
    (hcell : CellHyp (nu c N b) M₀) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, 0 < Polynomial.aeval Apery.zeta5 (Apery.F n) ∧
      Real.log (Polynomial.aeval Apery.zeta5 (Apery.F n)) ≤ -(Dnu c N b M₀ - δ) * Kr n ^ 2 := by
  filter_upwards [loglin_eventually (47 + 2 * circC b (∑ k ∈ Finset.range (N + 1), |c k|)) δ hδ,
    eventually_gt_atTop 0] with n hle hn0
  obtain ⟨hF, hlog⟩ := real_bound_nu hb hpos h0 hcell n hn0
  refine ⟨hF, ?_⟩
  have e : -(Dnu c N b M₀ - δ) * Kr n ^ 2 =
      (Cstar + lam * M₀ - (c 0 ^ 2 * Real.log (b / 4) - ∑ k ∈ Finset.range N,
        c (k + 1) ^ 2 / (2 * ((k + 1 : ℕ) : ℝ)))) * Kr n ^ 2 + δ * Kr n ^ 2 := by
    unfold Dnu; ring
  rw [e]
  linarith

/-- **ZD34**: `DecayAtConst (Dnu c N b M₀)` from `CellHyp (nu c N b) M₀`. -/
theorem decay_nu_const {c : ℕ → ℝ} {N : ℕ} {b : ℝ} (hb : 0 < b)
    (hpos : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ chebF c N x) (h0 : c 0 = 37 / 40) {M₀ : ℝ}
    (hcell : CellHyp (nu c N b) M₀) : DecayAtConst (Dnu c N b M₀) := by
  intro δ hδ
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 (zd33_log_eventually hb hpos h0 hcell hδ)
  refine ⟨N0, fun n hn => ?_⟩
  obtain ⟨hF, hlog⟩ := hN0 n hn
  have hK : ((40 * n : ℕ) : ℝ) = Kr n := by simp [Kr]
  rw [hK]
  exact (Real.log_le_iff_le_exp hF).1 hlog

theorem decayAtConst_mono {D D' : ℝ} (h : D' ≤ D) (hD : DecayAtConst D) : DecayAtConst D' := by
  intro δ hδ
  obtain ⟨N0, hN0⟩ := hD δ hδ
  refine ⟨N0, fun n hn => (hN0 n hn).trans (Real.exp_le_exp.2 ?_)⟩
  nlinarith [mul_nonneg (sub_nonneg.2 h) (sq_nonneg (((40 * n : ℕ) : ℝ)))]

/-- **`zeta5_decay`.**  At a comparison measure `ν = nu c N b` (`c` from the positive sum of
squares data, `c₀ = 37/40`, `0 < b < 4`) and `M₀ ≥ -8`:
the bounded-region cell inequality `2U - V ≤ M₀` on `[0, 4]` (first conjunct of `CellHyp`,
discharged by Z5-CELLS) and the exact constant inequality `138500086/10^8 ≤ D = I(ν) - λM₀ - C*`
(ZD22) give `DecayAtConst (138500086/10^8)`, the decay hypothesis of `zeta5_measure`.
The tail `t ≥ 4` (second conjunct of `CellHyp`) is proved here (`Tail`). -/
theorem zeta5_decay {c : ℕ → ℝ} {N : ℕ} {b M₀ : ℝ} (hb : 0 < b) (hb4 : b < 4)
    (hpos : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ chebF c N x) (h0 : c 0 = 37 / 40) (hM : -8 ≤ M₀)
    (hcell : ∀ t ∈ Icc (0 : ℝ) 4, 2 * potU (nu c N b) t - Vfield t ≤ M₀)
    (hconst : (138500086 : ℝ) / 10 ^ 8 ≤ Dnu c N b M₀) :
    DecayAtConst (138500086 / 10 ^ 8) := by
  have : IsFiniteMeasure (nu c N b) := isFiniteMeasure_nu hpos
  have hmass : (nu c N b).real univ = 37 / 40 := by
    rw [nu_real_univ hpos (by rw [h0]; norm_num), h0]
  have hC : CellHyp (nu c N b) M₀ :=
    cellHyp_of_bounded (nu_compl_Icc hb.le) hb4 hmass hM hcell
  exact decayAtConst_mono hconst (decay_nu_const hb hpos h0 hC)

end CatalanCore.Zeta5.Decay
