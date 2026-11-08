module

public import CatalanMeasure.GenD.Signed.RouteI.UnsignedInstance

@[expose] public section

/-!
# G5 shiftG: generic shift constructors for the record skeletons of `TerminalC`

`UnsignedInstance.shiftSecond` / `shiftFirst` fix the node correction `d` and the window `G` of the
base record; the K590 base records are `SecondTrialBounds` / `FirstTrialBounds` (`d = 0`, no `G` in the
marked field, endpoint column field).  The constructors below take the old base record and change
`d`, `G`, the window `W` and the column field at once:

* `shiftSecondG`: `p = p₀ + τ du`, `v = v₀ + τ dv`; the fields `row`, `column`, `norm_le`, `field_sum`
  come from linearity (finite support) and the old caps; `marked`, `near`, `budget` are passed
  through in the shape of the new record.
* `shiftFirstG`: as `shiftSecond`, and additionally the damping `λ = λ₀ + τ dl` (the K = 24
  constrained trial), whose row term `τ dl · paramCaseField` joins the row shift `ΔX`.
* `Interp`: the convexity lemmas that turn the endpoint checks (`τ = 0, 1`; two knots in `γ`) into
  the statement at every `τ ∈ [0, 1]`.
-/

open Set Filter

namespace CatalanMeasure.GenD.Signed.RouteI.ShiftG
open CatalanMeasure.GenD CatalanMeasure.GenD.Analytic CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Signed.RouteI.UnsignedInstance CatalanMeasure.GenD.Signed.RouteI.CompletedGas

noncomputable section

/-- **Second-population shift record over a K590 base record**, with new node correction `d`,
window `G`, window set `W` and column field `Cf'`.  `hY` compares `Cf'` with the endpoint column
field of the base record. -/
def shiftSecondG {P : Parameters} {W : Set ℝ} {Cf' : ℕ → ℝ → ℝ} {d : ℝ → ℝ} {G0 G : ℝ → Prop}
    {target0 residual0 nearCap0 cost0 target residual nearCap cost : ℝ}
    (D : SecondTrialBounds P target0 residual0 nearCap0 cost0 G0)
    {du dv : ℕ → ℝ} {K : ℕ} (hdu : ∀ k, K ≤ k → du k = 0) (hdv : ∀ k, K ≤ k → dv k = 0) (τ : ℝ)
    (ΔX ΔY normCap : ℝ)
    (hnorm : D.normCap + τ * (4 * barrierInner D.p du + barrierInner D.v dv) +
      τ ^ 2 * (2 * barrierTrialNormSq du + barrierTrialNormSq dv / 2) ≤ normCap)
    (hX : ∀ x ∈ Ico (-1 : ℝ) 0 ∪ Ioo 0 1,
      -(4 * (τ * barrierTrialT du x)) - τ * barrierTrialS dv x ≤ ΔX)
    (hY : ∀ᶠ N : ℕ in atTop, ∀ s ∈ Ioo (0 : ℝ) 1,
      Cf' N s + 2 * (τ * barrierTrialT dv s) ≤ populationEndpointColumnField P N 0 s + ΔY)
    (hmarked : ∀ {N : ℕ}, 0 < N → ∀ {x : ℝ}, x ∈ Icc (-1 : ℝ) 1 → G x →
      groupedMarkedField P N x - 2 * barrierTrialT (fun k => D.p k + τ * du k) x + d x ≤
        residual + Real.log 2 / (P.n N : ℝ))
    (hnear : ∀ {N : ℕ}, 0 < N → ∀ {y : ℝ}, y ∈ Ioo (0 : ℝ) 1 → G y →
      groupedNearField P N y - (D.p 1 + τ * du 1) * y + d y ≤ nearCap + Real.log 2 / (P.n N : ℝ))
    (hbudget : ∀ {a t : ℝ}, a ∈ W → 0 ≤ a → 0 ≤ t →
      (-gC0 P + gC1 P * a - a ^ 2 + t - t ^ 2) * Real.log 2 +
        normCap + (1 - a) * (D.fieldCap + ΔX + ΔY) + (a - t) * residual + t * nearCap ≤
          -target + Real.log 2 / 2 + cost * a) :
    SecondTrialBoundsEnd P W Cf' d target residual nearCap cost G where
  p := fun k => D.p k + τ * du k
  v := fun k => D.v k + τ * dv k
  MX := D.MX + ΔX
  MY := D.MY + ΔY
  normCap := normCap
  fieldCap := D.fieldCap + ΔX + ΔY
  p_summable := summable_shift τ D.p_summable hdu
  v_summable := summable_shift τ D.v_summable hdv
  norm_le := by
    have h1 := D.norm_le
    rw [normSq_shift τ D.p_summable hdu, normSq_shift τ D.v_summable hdv]
    rw [CompletedGas.barrierInner_comm D.p, CompletedGas.barrierInner_comm D.v] at *
    nlinarith only [h1, hnorm]
  field_sum := by rw [← D.field_sum]; ring
  row := fun {ε} hε => by
    filter_upwards [D.row hε] with N hN x hx
    have hx1 : |x| ≤ 1 := by
      rcases hx with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;> rw [abs_le] <;> constructor <;> linarith
    rw [barrierTrialT_shift _ _ τ D.p_summable hdu hx1, barrierTrialS_shift _ _ τ D.v_summable hdv hx1]
    have := hN x hx
    have := hX x hx
    linarith
  column := fun {ε} hε => by
    filter_upwards [D.column hε, hY] with N hN hYN s hs
    have hs1 : |s| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hs.1, hs.2]
    rw [barrierTrialT_shift _ _ τ D.v_summable hdv hs1]
    have := hN s hs
    have := hYN s hs
    linarith
  marked := hmarked
  near := hnear
  budget := hbudget

/-- **First-population shift record over a K590 first record** (`p = p₀ + τ du`, `v = v₀ + τ dv`,
`λ = λ₀ + τ dl`).  The row cap shift `ΔX` bounds `-2 τ T(du) - τ S(dv) + τ dl · paramCaseField`. -/
def shiftFirstG {P : Parameters} {W : Set ℝ} {Cf' : ℕ → ℝ → ℝ} {d : ℝ → ℝ} {G : ℝ → Prop}
    {target0 cost0 target cost : ℝ}
    (D : FirstTrialBounds P target0 cost0)
    {du dv : ℕ → ℝ} {K : ℕ} (hdu : ∀ k, K ≤ k → du k = 0) (hdv : ∀ k, K ≤ k → dv k = 0) (τ dl : ℝ)
    (ΔX ΔY normCap M₁ : ℝ) (hlam : 0 ≤ D.lambda + τ * dl)
    (hnorm : D.normCap + τ * (2 * barrierInner D.p du + barrierInner D.v dv) +
      τ ^ 2 * (barrierTrialNormSq du + barrierTrialNormSq dv / 2) ≤ normCap)
    (hX : ∀ {N : ℕ}, 0 < N → ∀ x ∈ Ico (-1 : ℝ) 0 ∪ Ioo 0 1,
      -(2 * (τ * barrierTrialT du x)) - τ * barrierTrialS dv x + τ * dl * paramCaseField P N x ≤ ΔX)
    (hY : ∀ᶠ N : ℕ in atTop, ∀ s ∈ Ioo (0 : ℝ) 1,
      Cf' N s + 2 * (τ * barrierTrialT dv s) ≤ populationEndpointColumnField P N 0 s + ΔY)
    (hmarked : ∀ {N : ℕ}, 0 < N → ∀ {x : ℝ}, x ∈ Ioo (-1 : ℝ) 1 → x ≠ 0 → G x →
      (D.lambda + τ * dl) * paramCaseField P N x + d x ≤ M₁)
    (hbudget : ∀ a ∈ W,
      (-gC0 P + gC1 P * a - a ^ 2) * Real.log 2 +
        normCap + (1 - a) * (D.fieldCap + ΔX + ΔY) + a * M₁ ≤
          -target + Real.log 2 / 2 + cost * a) :
    FirstTrialBoundsEnd P W Cf' d G target cost where
  p := fun k => D.p k + τ * du k
  v := fun k => D.v k + τ * dv k
  lambda := D.lambda + τ * dl
  MX := D.MX + ΔX
  MY := D.MY + ΔY
  normCap := normCap
  fieldCap := D.fieldCap + ΔX + ΔY
  M₁ := M₁
  lambda_nonneg := hlam
  p_summable := summable_shift τ D.p_summable hdu
  v_summable := summable_shift τ D.v_summable hdv
  norm_le := by
    have h1 := D.norm_le
    rw [normSq_shift τ D.p_summable hdu, normSq_shift τ D.v_summable hdv]
    rw [CompletedGas.barrierInner_comm D.p, CompletedGas.barrierInner_comm D.v] at *
    nlinarith only [h1, hnorm]
  field_sum := by rw [← D.field_sum]; ring
  row := fun {ε} hε => by
    filter_upwards [D.row hε, eventually_gt_atTop (0 : ℕ)] with N hN hN0 x hx
    have hx1 : |x| ≤ 1 := by
      rcases hx with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;> rw [abs_le] <;> constructor <;> linarith
    rw [barrierTrialT_shift _ _ τ D.p_summable hdu hx1, barrierTrialS_shift _ _ τ D.v_summable hdv hx1]
    have h1 := hN x hx
    have h2 := hX hN0 x hx
    nlinarith only [h1, h2]
  marked := hmarked
  column := fun {ε} hε => by
    filter_upwards [D.column hε, hY] with N hN hYN s hs
    have hs1 : |s| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hs.1, hs.2]
    rw [barrierTrialT_shift _ _ τ D.v_summable hdv hs1]
    have := hN s hs
    have := hYN s hs
    linarith
  budget := hbudget

/-! ### Convexity -/

/-- An affine-in-`τ` expression: if `A ≤ r₀` and `A - 2 B ≤ r₁`, then at every `τ ∈ [0,1]`
`A - 2 τ B ≤ (1 - τ) r₀ + τ r₁`. -/
theorem lin_interp {A B r0 r1 τ : ℝ} (h0 : A ≤ r0) (h1 : A - 2 * B ≤ r1) (hτ0 : 0 ≤ τ)
    (hτ1 : τ ≤ 1) : A - 2 * (τ * B) ≤ (1 - τ) * r0 + τ * r1 := by
  nlinarith only [mul_le_mul_of_nonneg_left h0 (sub_nonneg.mpr hτ1), mul_le_mul_of_nonneg_left h1 hτ0]

/-- Same, for the near field `A - (p + τ d) y` with `A - p y ≤ r₀`, `A - (p + d) y ≤ r₁`. -/
theorem lin_interp_near {A p dd y r0 r1 τ : ℝ} (h0 : A - p * y ≤ r0) (h1 : A - (p + dd) * y ≤ r1)
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) : A - (p + τ * dd) * y ≤ (1 - τ) * r0 + τ * r1 := by
  nlinarith only [mul_le_mul_of_nonneg_left h0 (sub_nonneg.mpr hτ1), mul_le_mul_of_nonneg_left h1 hτ0]

/-- Column-field knots: the endpoint checks `2 τ_a T + γ_a g ≤ Y_a` and `2 τ_b T + γ_b g ≤ Y_b`
give `2 τ T + γ g ≤ (1-w) Y_a + w Y_b` on the segment `(τ, γ) = (1-w)(τ_a, γ_a) + w (τ_b, γ_b)`. -/
theorem col_interp {T g ta ga tb gb Ya Yb w : ℝ} (ha : 2 * (ta * T) + ga * g ≤ Ya)
    (hb : 2 * (tb * T) + gb * g ≤ Yb) (hw0 : 0 ≤ w) (hw1 : w ≤ 1) :
    2 * (((1 - w) * ta + w * tb) * T) + ((1 - w) * ga + w * gb) * g ≤ (1 - w) * Ya + w * Yb := by
  nlinarith only [mul_le_mul_of_nonneg_left ha (sub_nonneg.mpr hw1), mul_le_mul_of_nonneg_left hb hw0]

/-- First-case marked cap: `S(τ)` is affine in `τ`; endpoint caps `S₀`, `S₁` serve all `τ ∈ [0,1]`
(`(λ₀ + τ dl) c + d = (1-τ)(λ₀ c + d) + τ((λ₀ + dl) c + d)`). -/
theorem lam_interp {lam dl c dd S0 S1 τ : ℝ} (h0 : lam * c + dd ≤ S0) (h1 : (lam + dl) * c + dd ≤ S1)
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) : (lam + τ * dl) * c + dd ≤ (1 - τ) * S0 + τ * S1 := by
  nlinarith only [mul_le_mul_of_nonneg_left h0 (sub_nonneg.mpr hτ1), mul_le_mul_of_nonneg_left h1 hτ0]

end

end CatalanMeasure.GenD.Signed.RouteI.ShiftG

#print axioms CatalanMeasure.GenD.Signed.RouteI.ShiftG.shiftSecondG
#print axioms CatalanMeasure.GenD.Signed.RouteI.ShiftG.shiftFirstG
#print axioms CatalanMeasure.GenD.Signed.RouteI.ShiftG.lin_interp
