module

public import Mathlib.NumberTheory.LSeries.PrimesInAP
public import Mathlib.NumberTheory.Chebyshev
public import PrimeNumberTheoremAnd.Catalan.Wiener

@[expose] public section

/-!
# PNT in a unit residue class, any modulus (design WP5)

For a modulus `m` and a unit class `r : ZMod m`, with
`thetaClass m r x = ∑_{p ≤ x prime, p ≡ r (m)} log p`:

* `pnt_class`        : `thetaClass m r x / x → 1 / φ(m)` (real `x → ∞`);
* `thetaClass_lower` : `(1/φ(m) - ε) x ≤ thetaClass m r x` eventually;
* `thetaClass_upper` : `thetaClass m r x ≤ (1/φ(m) + ε) x` eventually.

Source: Wiener–Ikehara (`CatalanPNT.WienerIkeharaTheorem'`) for the von Mangoldt sum in the
class (as in the legacy `CatalanLambda/PNTAP.lean`, copied here so that `CatalanCore` does not
import `CatalanLambda`), plus Mathlib's `ψ - θ ≤ 2 √x log x`.  This machinery is not imported by
the measure (G) development.
-/

open Asymptotics Filter Topology ArithmeticFunction ArithmeticFunction.vonMangoldt CatalanPNT Chebyshev

namespace CatalanCore.NT

/-- Chebyshev theta of a residue class, indexed by `N : ℕ`. -/
noncomputable def thetaClassN (m : ℕ) (r : ZMod m) (N : ℕ) : ℝ :=
  ∑ n ∈ (Finset.range (N + 1)).filter (fun n : ℕ ↦ n.Prime ∧ (n : ZMod m) = r), Real.log n

/-- `∑_{p ≤ x, p prime, p ≡ r (m)} log p` for real `x`. -/
noncomputable def thetaClass (m : ℕ) (r : ZMod m) (x : ℝ) : ℝ := thetaClassN m r ⌊x⌋₊

/-- PNT for `Λ` in a unit class, sum form over `range N`. -/
theorem pnt_psiClassN {q : ℕ} [NeZero q] {a : ZMod q} (ha : IsUnit a) :
    Tendsto (fun N : ℕ ↦ cumsum (residueClass a) N / N) atTop (𝓝 ((q.totient : ℝ)⁻¹)) := by
  have l1 : 0 ≤ residueClass a := fun n ↦ residueClass_nonneg a n
  have l5 (σ' : ℝ) (hσ' : 1 < σ') : Summable (nterm (fun n ↦ (residueClass a n : ℂ)) σ') := by
    have h := @ArithmeticFunction.LSeriesSummable_vonMangoldt σ' hσ'
    have h2 : Summable (nterm (fun n ↦ ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) σ') := by
      simpa only [← nterm_eq_norm_term] using h.norm
    refine Summable.of_nonneg_of_le (fun n ↦ ?_) (fun n ↦ ?_) h2
    · unfold nterm; split_ifs <;> positivity
    · unfold nterm; split_ifs
      · exact le_rfl
      · simp only [Complex.norm_real, Real.norm_eq_abs]
        rw [abs_of_nonneg (residueClass_nonneg a n), abs_of_nonneg vonMangoldt_nonneg]
        gcongr
        exact residueClass_le a n
  have l4 : ∃ C : ℝ, ∀ n : ℕ, cumsum (fun k : ℕ ↦ ‖((residueClass a k : ℝ) : ℂ)‖) n ≤ C * n := by
    obtain ⟨C, hC⟩ := vonMangoldt_cheby
    refine ⟨C, fun n ↦ le_trans ?_ (hC n)⟩
    unfold cumsum
    refine Finset.sum_le_sum fun k _ ↦ ?_
    simp only [Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg (residueClass_nonneg a k), abs_of_nonneg vonMangoldt_nonneg]
    exact residueClass_le a k
  have l3 := continuousOn_LFunctionResidueClassAux a
  have l2 : Set.EqOn (LFunctionResidueClassAux a)
      (fun s ↦ LSeries (fun n ↦ (residueClass a n : ℂ)) s - (((q.totient : ℝ)⁻¹ : ℝ) : ℂ) / (s - 1))
      {s | 1 < s.re} := by
    intro s hs
    have := eqOn_LFunctionResidueClassAux ha hs
    simpa using this
  exact WienerIkeharaTheorem' (f := residueClass a) (A := (q.totient : ℝ)⁻¹)
    l1 l5 l4 l3 l2

/-- The class `ψ`-sum up to the real `x`: `cumsum (residueClass a) (⌊x⌋₊ + 1)`. -/
theorem pnt_psiClass_real {q : ℕ} [NeZero q] {a : ZMod q} (ha : IsUnit a) :
    Tendsto (fun x : ℝ ↦ cumsum (residueClass a) (⌊x⌋₊ + 1) / x) atTop
      (𝓝 ((q.totient : ℝ)⁻¹)) := by
  have h1 := (pnt_psiClassN ha).comp ((tendsto_add_atTop_nat 1).comp
    (tendsto_nat_floor_atTop (α := ℝ)))
  have h2 : Tendsto (fun x : ℝ ↦ ((⌊x⌋₊ : ℝ) + 1) / x) atTop (𝓝 1) := by
    have h3 : Tendsto (fun x : ℝ ↦ (⌊x⌋₊ : ℝ) / x + 1 / x) atTop (𝓝 (1 + 0)) :=
      tendsto_nat_floor_div_atTop.add (tendsto_const_nhds.div_atTop tendsto_id)
    rw [add_zero] at h3
    refine h3.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    field_simp
  have h4 := h1.mul h2
  rw [mul_one] at h4
  refine h4.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have : ((⌊x⌋₊ + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  simp only [Function.comp, Nat.cast_add, Nat.cast_one] at this ⊢
  field_simp

theorem thetaClassN_le_cumsum (m : ℕ) (r : ZMod m) (N : ℕ) :
    thetaClassN m r N ≤ cumsum (residueClass r) (N + 1) := by
  unfold thetaClassN cumsum
  calc _ ≤ ∑ n ∈ (Finset.range (N + 1)).filter (fun n : ℕ ↦ n.Prime ∧ (n : ZMod m) = r),
        residueClass r n := by
        refine Finset.sum_le_sum fun n hn ↦ ?_
        obtain ⟨-, hp, hna⟩ := by simpa using hn
        simp [residueClass, hna, ArithmeticFunction.vonMangoldt_apply_prime hp]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun n _ _ ↦ residueClass_nonneg r n)

/-- The prime-power part of the class sum is at most that of the full sum. -/
theorem cumsum_sub_thetaClassN_le (m : ℕ) (r : ZMod m) (N : ℕ) :
    cumsum (residueClass r) (N + 1) - thetaClassN m r N ≤ ψ (N : ℝ) - θ (N : ℝ) := by
  have hI : Finset.Icc 0 N = Finset.range (N + 1) := by
    ext n; simp
  rw [psi_eq_sum_Icc, theta_eq_sum_Icc, Nat.floor_natCast, hI, Finset.sum_filter]
  unfold thetaClassN cumsum
  rw [Finset.sum_filter, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun n _ ↦ ?_
  by_cases hp : n.Prime
  · by_cases hn : (n : ZMod m) = r
    · simp [residueClass, hp, hn, ArithmeticFunction.vonMangoldt_apply_prime hp]
    · simp [residueClass, hp, hn, ArithmeticFunction.vonMangoldt_apply_prime hp]
  · by_cases hn : (n : ZMod m) = r
    · simp [residueClass, hp, hn]
    · simp [residueClass, hp, hn]

/-- `√x log x / x → 0`. -/
theorem tendsto_sqrt_log_div :
    Tendsto (fun x : ℝ ↦ 2 * Real.sqrt x * Real.log x / x) atTop (𝓝 0) := by
  have hlog : (fun x : ℝ ↦ Real.log x) =o[atTop] (fun x : ℝ ↦ x ^ (1 / 2 : ℝ)) :=
    isLittleO_log_rpow_atTop (by norm_num)
  have h := (hlog.tendsto_div_nhds_zero).const_mul 2
  rw [mul_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have hs : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx.le
  have hs0 : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  rw [← Real.sqrt_eq_rpow]
  field_simp
  rw [Real.sq_sqrt hx.le]

theorem thetaClass_ge_sub {m : ℕ} (r : ZMod m) {x : ℝ} (hx : 1 ≤ x) :
    cumsum (residueClass r) (⌊x⌋₊ + 1) - 2 * Real.sqrt x * Real.log x ≤ thetaClass m r x := by
  have hN : (1 : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast Nat.le_floor (by simpa using hx)
  have h1 := cumsum_sub_thetaClassN_le m r ⌊x⌋₊
  have h2 := psi_sub_theta_le hN
  have hle : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
  have h3 : 2 * Real.sqrt (⌊x⌋₊ : ℝ) * Real.log (⌊x⌋₊ : ℝ) ≤ 2 * Real.sqrt x * Real.log x := by
    have := Real.sqrt_le_sqrt hle
    have := Real.log_le_log (by linarith) hle
    have := Real.log_nonneg hN
    have := Real.sqrt_nonneg (⌊x⌋₊ : ℝ)
    have := Real.sqrt_nonneg x
    have := Real.log_nonneg (show (1 : ℝ) ≤ x by linarith)
    nlinarith [mul_le_mul (Real.sqrt_le_sqrt hle) (Real.log_le_log (by linarith) hle)
      (Real.log_nonneg hN) (Real.sqrt_nonneg x)]
  unfold thetaClass
  linarith

/-- **PNT in a unit class** (any modulus): `θ(x; m, r) / x → 1 / φ(m)`. -/
theorem pnt_class {m : ℕ} [NeZero m] {r : ZMod m} (hr : IsUnit r) :
    Tendsto (fun x : ℝ ↦ thetaClass m r x / x) atTop (𝓝 ((m.totient : ℝ)⁻¹)) := by
  have hψ := pnt_psiClass_real hr
  have hlow : Tendsto (fun x : ℝ ↦ (cumsum (residueClass r) (⌊x⌋₊ + 1) -
      2 * Real.sqrt x * Real.log x) / x) atTop (𝓝 ((m.totient : ℝ)⁻¹)) := by
    have := hψ.sub tendsto_sqrt_log_div
    rw [sub_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    ring
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hψ ?_ ?_
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    exact div_le_div_of_nonneg_right (thetaClass_ge_sub r hx) (by linarith)
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact div_le_div_of_nonneg_right (thetaClassN_le_cumsum m r _) hx.le

theorem thetaClass_lower {m : ℕ} [NeZero m] {r : ZMod m} (hr : IsUnit r) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ((m.totient : ℝ)⁻¹ - ε) * x ≤ thetaClass m r x := by
  filter_upwards [(pnt_class hr).eventually (lt_mem_nhds (by linarith :
      (m.totient : ℝ)⁻¹ - ε < (m.totient : ℝ)⁻¹)), eventually_gt_atTop (0 : ℝ)] with x hx hx0
  exact (lt_div_iff₀ hx0).mp hx |>.le

theorem thetaClass_upper {m : ℕ} [NeZero m] {r : ZMod m} (hr : IsUnit r) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, thetaClass m r x ≤ ((m.totient : ℝ)⁻¹ + ε) * x := by
  filter_upwards [(pnt_class hr).eventually (gt_mem_nhds (by linarith :
      (m.totient : ℝ)⁻¹ < (m.totient : ℝ)⁻¹ + ε)), eventually_gt_atTop (0 : ℝ)] with x hx hx0
  exact (div_lt_iff₀ hx0).mp hx |>.le

end CatalanCore.NT
