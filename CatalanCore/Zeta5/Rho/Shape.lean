module

public import CatalanCore.Zeta5.Rho.Riemann
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

@[expose] public section

/-!
# The field exponent `V` has one interior minimum (ledger ZR06)

With `y = √t`, `V(y²)` has `y`-derivative `2ψ(y)`, `ψ(y) = π + arctan(1/y) - 6 arctan(α/y)`,
`α = 3/40`.  `ψ` is increasing on `(0, 3/20]` and `> 0` on `[3/20, ∞)`, so the sign of `ψ` is
"once nonnegative, always nonnegative".  Hence for `0 < p ≤ q`, `V(y²) ≤ max(V(p²), V(q²))` on
`[p, q]`: the maximum of `V` over `[a, b]` is at an endpoint.
-/

namespace CatalanCore.Zeta5.Rho

open Set Real

/-- `ψ(y) = π + arctan(1/y) - 6 arctan(α/y)`, `α = 3/40`. -/
noncomputable def psiS (y : ℝ) : ℝ := Real.pi + Real.arctan (1 / y) - 6 * Real.arctan ((3 / 40) / y)

/-- `V` as a function of `y = √t`. -/
noncomputable def Vy (y : ℝ) : ℝ := 2 * Real.pi * y + Jf (y ^ 2) 1 - 6 * Jf (y ^ 2) (3 / 40)

theorem Vf_eq_Vy {t : ℝ} (ht : 0 ≤ t) : Vf t = Vy (√t) := by
  unfold Vf Vy; rw [Real.sq_sqrt ht]

/-- `J_A(y²)` in the variable `y`. -/
theorem Jf_sq {y : ℝ} (hy : 0 < y) (A : ℝ) :
    Jf (y ^ 2) A = A * Real.log (y ^ 2 + A ^ 2) - 2 * A + 2 * y * Real.arctan (A / y) := by
  unfold Jf; rw [Real.sqrt_sq hy.le]

theorem hasDerivAt_Jy {y : ℝ} (hy : 0 < y) (A : ℝ) :
    HasDerivAt (fun y : ℝ => A * Real.log (y ^ 2 + A ^ 2) - 2 * A + 2 * y * Real.arctan (A / y))
      (2 * Real.arctan (A / y)) y := by
  have hpos : y ^ 2 + A ^ 2 ≠ 0 := by positivity
  have h1 := (((hasDerivAt_pow 2 y).add_const (A ^ 2)).log hpos).const_mul A
  have hd := (hasDerivAt_const y A).div (hasDerivAt_id' y) hy.ne'
  have h3 := ((hasDerivAt_id' y).const_mul 2).mul hd.arctan
  have := (h1.sub_const (2 * A)).add h3
  simp only [Pi.div_apply] at this
  convert this using 1
  field_simp
  ring

theorem hasDerivAt_Vy {y : ℝ} (hy : 0 < y) : HasDerivAt Vy (2 * psiS y) y := by
  have a1 := (hasDerivAt_id' y).const_mul (2 * Real.pi)
  have a2 := hasDerivAt_Jy hy 1
  have a3 := (hasDerivAt_Jy hy (3 / 40)).const_mul 6
  have := (a1.add a2).sub a3
  have hev : Vy =ᶠ[nhds y] fun z : ℝ => 2 * Real.pi * z +
      (1 * Real.log (z ^ 2 + 1 ^ 2) - 2 * 1 + 2 * z * Real.arctan (1 / z)) -
      6 * ((3 / 40) * Real.log (z ^ 2 + (3 / 40) ^ 2) - 2 * (3 / 40) +
        2 * z * Real.arctan ((3 / 40) / z)) := by
    filter_upwards [lt_mem_nhds hy] with z hz
    unfold Vy; rw [Jf_sq hz, Jf_sq hz]
  refine (HasDerivAt.congr_of_eventuallyEq ?_ hev)
  convert this using 1
  unfold psiS; ring


theorem hasDerivAt_arctan_div {y : ℝ} (hy : 0 < y) (c : ℝ) :
    HasDerivAt (fun y : ℝ => Real.arctan (c / y)) (-c / (y ^ 2 + c ^ 2)) y := by
  have hd := (hasDerivAt_const y c).div (hasDerivAt_id' y) hy.ne'
  have := hd.arctan
  simp only [Pi.div_apply] at this
  convert this using 1
  field_simp
  ring

theorem hasDerivAt_psiS {y : ℝ} (hy : 0 < y) :
    HasDerivAt psiS (-1 / (y ^ 2 + 1 ^ 2) + 6 * (3 / 40) / (y ^ 2 + (3 / 40) ^ 2)) y := by
  have h1 := (hasDerivAt_arctan_div hy 1)
  have h2 := (hasDerivAt_arctan_div hy (3 / 40)).const_mul 6
  have := ((h1.const_add Real.pi)).sub h2
  convert this using 1
  · funext z; simp [psiS]
  · field_simp
    ring

theorem psiS_mono {y1 y2 : ℝ} (h1 : 0 < y1) (h12 : y1 ≤ y2) (h2 : y2 ≤ 3 / 20) :
    psiS y1 ≤ psiS y2 := by
  have hmono : MonotoneOn psiS (Icc y1 y2) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc y1 y2) ?_ ?_ ?_
    · intro y hy
      exact (hasDerivAt_psiS (lt_of_lt_of_le h1 hy.1)).continuousAt.continuousWithinAt
    · intro y hy
      rw [interior_Icc] at hy
      exact (hasDerivAt_psiS (lt_trans h1 hy.1)).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [interior_Icc] at hy
      have hy0 : 0 < y := lt_trans h1 hy.1
      rw [(hasDerivAt_psiS hy0).deriv]
      have hy2 : y < 3 / 20 := lt_of_lt_of_le hy.2 h2
      have hyy : y ^ 2 ≤ 9 / 400 := by nlinarith
      have e : -1 / (y ^ 2 + 1 ^ 2) + 6 * (3 / 40) / (y ^ 2 + (3 / 40) ^ 2) =
          (-(y ^ 2 + (3 / 40) ^ 2) + 6 * (3 / 40) * (y ^ 2 + 1 ^ 2)) /
            ((y ^ 2 + 1 ^ 2) * (y ^ 2 + (3 / 40) ^ 2)) := by
        field_simp
      rw [e]
      apply div_nonneg _ (by positivity)
      nlinarith
  exact hmono ⟨le_refl y1, h12⟩ ⟨h12, le_refl y2⟩ h12

theorem psiS_pos_of_ge {y : ℝ} (hy : 3 / 20 ≤ y) : 0 < psiS y := by
  have hy0 : 0 < y := lt_of_lt_of_le (by norm_num) hy
  unfold psiS
  have h1 : 0 ≤ Real.arctan (1 / y) := Real.arctan_nonneg.mpr (by positivity)
  have h2 : Real.arctan ((3 / 40) / y) ≤ (3 / 40) / y := Real.arctan_le_self (by positivity)
  have h3 : (3 / 40) / y ≤ 1 / 2 := by
    rw [div_le_iff₀ hy0]; linarith
  have := Real.pi_gt_three
  linarith

theorem psiS_upclosed {y1 y2 : ℝ} (h1 : 0 < y1) (h12 : y1 ≤ y2) (h : 0 ≤ psiS y1) :
    0 ≤ psiS y2 := by
  rcases le_or_gt (3 / 20) y2 with h2 | h2
  · exact (psiS_pos_of_ge h2).le
  · exact le_trans h (psiS_mono h1 h12 h2.le)

/-- **ZR06 (in `y = √t`).**  For `0 < p ≤ y ≤ q`: `V(y²) ≤ max (V(p²)) (V(q²))`. -/
theorem Vy_le_max {p q y : ℝ} (hp : 0 < p) (hpy : p ≤ y) (hyq : y ≤ q) :
    Vy y ≤ max (Vy p) (Vy q) := by
  have hy0 : 0 < y := lt_of_lt_of_le hp hpy
  by_cases hs : 0 ≤ psiS y
  · -- monotone on [y, q]
    have hmono : MonotoneOn Vy (Icc y q) := by
      refine monotoneOn_of_deriv_nonneg (convex_Icc y q) ?_ ?_ ?_
      · intro z hz
        exact (hasDerivAt_Vy (lt_of_lt_of_le hy0 hz.1)).continuousAt.continuousWithinAt
      · intro z hz
        rw [interior_Icc] at hz
        exact (hasDerivAt_Vy (lt_trans hy0 hz.1)).differentiableAt.differentiableWithinAt
      · intro z hz
        rw [interior_Icc] at hz
        have hz0 : 0 < z := lt_trans hy0 hz.1
        rw [(hasDerivAt_Vy hz0).deriv]
        have := psiS_upclosed hy0 hz.1.le hs
        linarith
    exact le_trans (hmono ⟨le_refl y, hyq⟩ ⟨hyq, le_refl q⟩ hyq) (le_max_right _ _)
  · -- antitone on [p, y]
    have hneg : ∀ z ∈ Icc p y, psiS z < 0 := by
      intro z hz
      by_contra hc
      exact hs (psiS_upclosed (lt_of_lt_of_le hp hz.1) hz.2 (not_lt.mp hc))
    have hanti : AntitoneOn Vy (Icc p y) := by
      refine antitoneOn_of_deriv_nonpos (convex_Icc p y) ?_ ?_ ?_
      · intro z hz
        exact (hasDerivAt_Vy (lt_of_lt_of_le hp hz.1)).continuousAt.continuousWithinAt
      · intro z hz
        rw [interior_Icc] at hz
        exact (hasDerivAt_Vy (lt_trans hp hz.1)).differentiableAt.differentiableWithinAt
      · intro z hz
        rw [interior_Icc] at hz
        have hz0 : 0 < z := lt_trans hp hz.1
        rw [(hasDerivAt_Vy hz0).deriv]
        have := hneg z ⟨hz.1.le, hz.2.le⟩
        linarith
    exact le_trans (hanti ⟨le_refl p, hpy⟩ ⟨hpy, le_refl y⟩ hpy) (le_max_left _ _)

/-- **ZR06.**  For `0 < a ≤ t ≤ b`: `V(t) ≤ max (V a) (V b)`. -/
theorem Vf_le_max {a b t : ℝ} (ha : 0 < a) (hat : a ≤ t) (htb : t ≤ b) :
    Vf t ≤ max (Vf a) (Vf b) := by
  have ht : 0 ≤ t := by linarith
  have h := Vy_le_max (p := √a) (q := √b) (y := √t) (Real.sqrt_pos.mpr ha)
    (Real.sqrt_le_sqrt hat) (Real.sqrt_le_sqrt htb)
  rw [Vf_eq_Vy ht, Vf_eq_Vy ha.le, Vf_eq_Vy (by linarith : 0 ≤ b)]
  exact h


/-- `V(y²)` is increasing from `y = 3/20` on. -/
theorem Vy_mono {y y' : ℝ} (h : 3 / 20 ≤ y) (hy : y ≤ y') : Vy y ≤ Vy y' := by
  have hy0 : 0 < y := lt_of_lt_of_le (by norm_num) h
  have hmono : MonotoneOn Vy (Icc y y') := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc y y') ?_ ?_ ?_
    · intro z hz
      exact (hasDerivAt_Vy (lt_of_lt_of_le hy0 hz.1)).continuousAt.continuousWithinAt
    · intro z hz
      rw [interior_Icc] at hz
      exact (hasDerivAt_Vy (lt_trans hy0 hz.1)).differentiableAt.differentiableWithinAt
    · intro z hz
      rw [interior_Icc] at hz
      have hz0 : 0 < z := lt_trans hy0 hz.1
      rw [(hasDerivAt_Vy hz0).deriv]
      have := psiS_pos_of_ge (le_trans h hz.1.le)
      linarith
  exact hmono ⟨le_refl y, hy⟩ ⟨hy, le_refl y'⟩ hy

end CatalanCore.Zeta5.Rho
