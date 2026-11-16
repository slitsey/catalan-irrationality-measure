module

public import CatalanCore.Zeta5.Energy.Bound
public import CatalanCore.Zeta5.Potential.All

@[expose] public section

/-!
# The decay chain at the comparison measure `ν = f ω_{[0,b]}` (Z5-ENERGY, instance)

The generic chain (`Design`, `config_ineq`, `real_bound`) is specialised to
`nu c N b` of `CatalanCore.Zeta5.Potential` (`f = Σ_{k ≤ N} c_k T_k(2t/b - 1)`).
The only hypothesis left for the decay cells is `CellHyp (nu c N b) M₀`, namely

* `∀ t ∈ Icc 0 4, 2 * potU (nu c N b) t - Vfield t ≤ M₀`,
* `∀ t, 4 ≤ t → 2 * potU (nu c N b) t - Vfield t + √t / 2 ≤ M₀`,

where `potU (nu c N b) t = logPot (nu c N b) t = c₀ log(b/4) - Σ c_k T_k(x)/k` (ZD13) for `t ∈ [0, b]`.
-/

open MeasureTheory Set CatalanCore.Zeta5.Potential

namespace CatalanCore.Zeta5.Energy

theorem potU_nu_eq (c : ℕ → ℝ) (N : ℕ) (b t : ℝ) :
    potU (nu c N b) t = logPot (nu c N b) t := rfl

/-- The arcsine majorant of `ν = f ω` with `F = Σ |c_k|` (ZD04 and ZD16). -/
theorem arcMaj_nu {c : ℕ → ℝ} {N : ℕ} {b : ℝ} (hb : 0 < b) :
    ArcMaj (nu c N b) b (∑ k ∈ Finset.range (N + 1), |c k|) where
  b_pos := hb
  F_nonneg := Finset.sum_nonneg fun k _ => abs_nonneg _
  supp := nu_compl_Icc hb.le
  maj m r := by
    have h1 := nu_le_omega c N b (Icc (m - r) (m + r)) measurableSet_Icc
    have h2 := omega_Icc_le hb m r
    refine h1.trans ?_
    calc ENNReal.ofReal (∑ k ∈ Finset.range (N + 1), |c k|) * omega b (Icc (m - r) (m + r))
        ≤ ENNReal.ofReal (∑ k ∈ Finset.range (N + 1), |c k|) *
            ENNReal.ofReal (Real.sqrt (2 * r / b)) := by gcongr
      _ = _ := (ENNReal.ofReal_mul (Finset.sum_nonneg fun k _ => abs_nonneg _)).symm

/-- The design data of the decay chain for `ν = nu c N b` of mass `c₀ = 37/40`. -/
theorem design_nu {c : ℕ → ℝ} {N : ℕ} {b : ℝ} (hb : 0 < b)
    (hpos : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ chebF c N x) (h0 : c 0 = 37 / 40) {M₀ : ℝ}
    (hcell : CellHyp (nu c N b) M₀) :
    Design (nu c N b) b (∑ k ∈ Finset.range (N + 1), |c k|) M₀ where
  arc := arcMaj_nu hb
  mass := by rw [nu_real_univ hpos (by rw [h0]; norm_num), h0]
  cell := hcell

/-- `I(ν) = c₀² log(b/4) - Σ_{k ≥ 1} c_k²/(2k)` (ZD14). -/
theorem energyI_nu {c : ℕ → ℝ} {N : ℕ} {b : ℝ} (hb : 0 < b)
    (hpos : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ chebF c N x) :
    energyI (nu c N b) = c 0 ^ 2 * Real.log (b / 4) - ∑ k ∈ Finset.range N,
      c (k + 1) ^ 2 / (2 * ((k + 1 : ℕ) : ℝ)) :=
  energy_nu hb hpos

/-- **The real bound at the comparison measure** (ZD30 for `ν = nu c N b`): for `n > 0`,
`F_K(ξ) > 0` and `log F_K(ξ) ≤ (C* + λM₀ - I(ν)) K² + 24 K log K + (47 + 2 C_circ) K`,
`K = 40 n`, with `I(ν)` the closed form of ZD14 and `C_circ = 2√2 (Σ|c_k|)/√b`.
The only hypothesis on the cells is `CellHyp (nu c N b) M₀`. -/
theorem real_bound_nu {c : ℕ → ℝ} {N : ℕ} {b : ℝ} (hb : 0 < b)
    (hpos : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ chebF c N x) (h0 : c 0 = 37 / 40) {M₀ : ℝ}
    (hcell : CellHyp (nu c N b) M₀) (n : ℕ) (hn : 0 < n) :
    0 < Polynomial.aeval Apery.zeta5 (Apery.F n) ∧
      Real.log (Polynomial.aeval Apery.zeta5 (Apery.F n)) ≤
        (Cstar + lam * M₀ - (c 0 ^ 2 * Real.log (b / 4) - ∑ k ∈ Finset.range N,
            c (k + 1) ^ 2 / (2 * ((k + 1 : ℕ) : ℝ)))) * Kr n ^ 2 +
          24 * Kr n * Real.log (Kr n) +
          (47 + 2 * circC b (∑ k ∈ Finset.range (N + 1), |c k|)) * Kr n := by
  have : IsFiniteMeasure (nu c N b) := isFiniteMeasure_nu hpos
  have := real_bound (design_nu hb hpos h0 hcell) n hn
  rwa [energyI_nu hb hpos] at this

end CatalanCore.Zeta5.Energy
