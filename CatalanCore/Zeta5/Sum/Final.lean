module

public import CatalanCore.Zeta5.Sum.OuterBridge
public import CatalanCore.Zeta5.Sum.DataOuter
public import CatalanCore.Zeta5.Sum.DataR
public import CatalanCore.Zeta5.Sum.DataG
public import CatalanCore.Zeta5.Sum.Tail200
public import CatalanCore.Zeta5.Sum.PrimeBounds

@[expose] public section

/-!
# ZC34 – ZC39 in the form of CONTENT-LEDGER, and the content rate `Λ`

* `zc34` : `∫_{1/3}^{2λ} T₀(y) dy = 127751/96000`        (ZC34, `T0` of `OuterBridge`).
* `zc35` : `∫₁³ [x T₀(1/x) − R(x)]₊ x⁻³ dx = 3203/163200`   (ZC35, `S_out`).
* `zc36` : `∫₃^200 R(x) x⁻³ dx = I200`                       (ZC36, `DataR`).
* `zc37` : `∫₂₀₀^∞ R(x) x⁻³ dx ≤ −103109/24000000`          (ZC37, `Tail200`).
* `zc38` : `∫₃^200 g_ref(x) x⁻³ dx > 5847/10⁶`               (ZC38, `DataG`).
* `zc39` : the right-hand side of ZC32 at `X = 200`,
  `lambdaRHS200 = ∫₃^∞ R/x³ + (∫_{1/3}^{2λ} T₀ − S_out) − ∫₃^200 g_ref/x³`, is at most
  `127751/96000 − 3203/163200 + I200 − 103109/24000000 − 5847/10⁶ = 1.2879953310…` (the ledger's
  `1.28799532…` is the same sum with the exact gain `G200` in place of `5847/10⁶`), and
  this is below `1288003/10⁶`.
-/

open Set MeasureTheory

namespace CatalanCore.Zeta5.Sum

open CatalanCore.Zeta5.Profile

/-- **ZC34.** `∫_{1/3}^{2λ} T₀(y) dy = 127751/96000`. -/
theorem zc34 : ∫ y in (1 / 3 : ℝ)..(37 / 20), T0 y = 127751 / 96000 := by
  have h1 := integral_inv_comp T0 (a := 20 / 37) (b := 3) (by norm_num) (by norm_num)
  have e1 : (1 / (3 : ℝ)) = 1 / 3 := rfl
  have e2 : (1 / (20 / 37 : ℝ)) = 37 / 20 := by norm_num
  rw [e2] at h1
  rw [← h1]
  rw [← zc34_x]
  apply intervalIntegral.integral_congr_uIoo
  intro x hx
  rw [Set.uIoo_of_le (by norm_num)] at hx
  have hx0 : 0 < x := by linarith [hx.1]
  have hx3 : x < 3 := hx.2
  simp only []
  rw [T0_inv hx0 hx3]
  field_simp

/-- **ZC35.** `S_out = ∫₁³ [x T₀(1/x) − R(x)]₊ x⁻³ dx = 3203/163200`. -/
theorem zc35 : ∫ x in (1 : ℝ)..3, max 0 (x * T0 (1 / x) - Rg x) / x ^ 3 = 3203 / 163200 := by
  rw [← zc35_x]
  apply intervalIntegral.integral_congr_uIoo
  intro x hx
  rw [Set.uIoo_of_le (by norm_num)] at hx
  have hx0 : 0 < x := by linarith [hx.1]
  have hx3 : x < 3 := hx.2
  simp only []
  rw [T0_inv hx0 hx3]
  field_simp

/-- **ZC37.** `∫₂₀₀^∞ R(x) x⁻³ dx ≤ −103109/24000000`. -/
theorem zc37 : ∫ x in Ioi (200 : ℝ), Rg x / x ^ 3 ≤ -103109 / 24000000 := TL200

/-- `R(x) x⁻³` is integrable on `(3, ∞)`. -/
theorem integrableOn_Rg_Ioi_three : IntegrableOn (fun x : ℝ => Rg x / x ^ 3) (Ioi 3) := by
  have h1 : IntegrableOn (fun x : ℝ => Rg x / x ^ 3) (Ioc 3 200) := by
    have := zc36_seg.2.1
    have h := (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (3 : ℝ) ≤ 200)).1
      (by simpa using this)
    exact h
  have h2 : IntegrableOn (fun x : ℝ => Rg x / x ^ 3) (Ioi 200) :=
    integrableOn_Rg.mono_set (Ioi_subset_Ioi (by norm_num))
  rw [← Ioc_union_Ioi_eq_Ioi (by norm_num : (3 : ℝ) ≤ 200)]
  exact h1.union h2

/-- The right-hand side of ZC32 at `X = 200`:
`∫₃^∞ R/x³ + ∫_{1/3}^{2λ} W_out − ∫₃^200 g_ref/x³`, with
`∫ W_out = ∫ T₀ − S_out`. -/
noncomputable def lambdaRHS200 : ℝ :=
  (∫ x in Ioi (3 : ℝ), Rg x / x ^ 3)
    + ((∫ y in (1 / 3 : ℝ)..(37 / 20), T0 y)
        - ∫ x in (1 : ℝ)..3, max 0 (x * T0 (1 / x) - Rg x) / x ^ 3)
    - ∫ x in (3 : ℝ)..200, gref x / x ^ 3

/-- The rational of ZC39. -/
def lambdaQ : ℚ :=
  127751 / 96000 - 3203 / 163200 + I200 - 103109 / 24000000 - 5847 / 1000000

theorem lambdaQ_lt : lambdaQ < 1288003 / 1000000 := by
  unfold lambdaQ
  decide +kernel

theorem lambdaQ_value : (1287995331 / 1000000000 : ℚ) < lambdaQ ∧ lambdaQ < 1287995332 / 1000000000 := by
  unfold lambdaQ
  constructor <;> decide +kernel

/-- **ZC39.** `Λ ≤ 127751/96000 − 3203/163200 + I200 − 103109/24000000 − 5847/10⁶`, i.e.
`lambdaRHS200 ≤ lambdaQ = 1.2879953310… < 1.288003`. -/
theorem zc39 : lambdaRHS200 ≤ (lambdaQ : ℝ) := by
  have hR3 : (∫ x in Ioi (3 : ℝ), Rg x / x ^ 3)
      = (∫ x in (3 : ℝ)..200, Rg x / x ^ 3) + ∫ x in Ioi (200 : ℝ), Rg x / x ^ 3 := by
    have h1 : IntegrableOn (fun x : ℝ => Rg x / x ^ 3) (Ioc 3 200) := by
      have := zc36_seg.2.1
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (3 : ℝ) ≤ 200)).1
        (by simpa using this)
    have h2 : IntegrableOn (fun x : ℝ => Rg x / x ^ 3) (Ioi 200) :=
      integrableOn_Rg.mono_set (Ioi_subset_Ioi (by norm_num))
    rw [← Ioc_union_Ioi_eq_Ioi (by norm_num : (3 : ℝ) ≤ 200),
      setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi h1 h2,
      intervalIntegral.integral_of_le (by norm_num)]
  have h36 := zc36
  have h37 := zc37
  have h38 := zc38
  have h34 := zc34
  have h35 := zc35
  unfold lambdaRHS200
  rw [hR3, h36, h34, h35]
  unfold lambdaQ
  push_cast
  linarith

/-- The numerical form of ZC39: the right-hand side is below `1.288003`. -/
theorem zc39_lt : lambdaRHS200 < 1288003 / 1000000 := by
  have h := zc39
  have h2 : (lambdaQ : ℝ) < 1288003 / 1000000 := by
    have := lambdaQ_lt
    have h3 : ((lambdaQ : ℚ) : ℝ) < ((1288003 / 1000000 : ℚ) : ℝ) := Rat.cast_lt.mpr this
    simpa using h3
  linarith

end CatalanCore.Zeta5.Sum

#print axioms CatalanCore.Zeta5.Sum.theta_le_linear
#print axioms CatalanCore.Zeta5.Sum.pnt_theta
#print axioms CatalanCore.Zeta5.Sum.weighted_prime_sum_tendsto
#print axioms CatalanCore.Zeta5.Sum.weighted_prime_sum_tendsto_nat
#print axioms CatalanCore.Zeta5.Sum.band_error_bound
#print axioms CatalanCore.Zeta5.Sum.inner_tail_bound
#print axioms CatalanCore.Zeta5.Sum.small_primes_bound
#print axioms CatalanCore.Zeta5.Sum.small_primes_o
#print axioms CatalanCore.Zeta5.Sum.inner_error_o
#print axioms CatalanCore.Zeta5.Sum.outer_error_o
#print axioms CatalanCore.Zeta5.Sum.Ex_chain_sound
#print axioms CatalanCore.Zeta5.Sum.Hp_chain_sound
#print axioms CatalanCore.Zeta5.Sum.zc34
#print axioms CatalanCore.Zeta5.Sum.zc35
#print axioms CatalanCore.Zeta5.Sum.zc36
#print axioms CatalanCore.Zeta5.Sum.zc37
#print axioms CatalanCore.Zeta5.Sum.zc38
#print axioms CatalanCore.Zeta5.Sum.lambdaQ_lt
#print axioms CatalanCore.Zeta5.Sum.lambdaQ_value
#print axioms CatalanCore.Zeta5.Sum.zc39
#print axioms CatalanCore.Zeta5.Sum.zc39_lt
