module

public import CatalanCore.Zeta5.Rho.NodeBound
public import Mathlib.Analysis.SpecialFunctions.Arcosh
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

@[expose] public section

/-!
# The node exponent `Φ` is concave on `(α, 1)`: tangent bound (ledger ZR07)

`Φ_{a,b}(u) = L_α(u) + (37/20) arcosh Y(u)`, `Y(u) = (2u² + a + b)/(b - a)`, `α = 3/40`,
`2λ = 37/20`.  Its derivative is
`Φ'(u) = 6 log((u+α)/(u-α)) + log((1-u)/(1+u)) + (37/10) u/√((u²+a)(u²+b))`,
which is antitone on `(α, 1)` when `ab ≤ α⁴`.  By the mean value theorem, for `u₀ ∈ (α, 1)` and
`u ∈ (α, 1]`: `Φ(u) ≤ Φ(u₀) + Φ'(u₀)(u - u₀)`.
-/

namespace CatalanCore.Zeta5.Rho

open Set Real

theorem hasDerivAt_gfun_neg {x : ℝ} (hx : x < 0) : HasDerivAt gfun (Real.log (-x)) x := by
  have h := ((hasDerivAt_gfun (neg_pos.mpr hx)).comp x (hasDerivAt_neg x)).neg
  have e : gfun = fun y => -(gfun ∘ Neg.neg) y := by
    funext y; simp [gfun_neg]
  rw [e]
  convert h using 1
  ring

/-- `Y(u) = (2u² + a + b)/(b - a)`. -/
noncomputable def Yf (a b u : ℝ) : ℝ := (2 * u ^ 2 + a + b) / (b - a)

/-- `Φ_{a,b}(u) = L_{3/40}(u) + 2λ arcosh Y(u)`, `2λ = 37/20`. -/
noncomputable def Phi (a b u : ℝ) : ℝ := Lg (3 / 40) u + 37 / 20 * Real.arcosh (Yf a b u)

/-- The derivative of `Φ`. -/
noncomputable def dPhi (a b u : ℝ) : ℝ :=
  6 * Real.log ((u + 3 / 40) / (u - 3 / 40)) + Real.log ((1 - u) / (1 + u)) +
    37 / 10 * u / √((u ^ 2 + a) * (u ^ 2 + b))

theorem Yf_gt_one {a b u : ℝ} (ha : 0 < a) (hab : a < b) : 1 < Yf a b u := by
  unfold Yf
  rw [lt_div_iff₀ (by linarith)]
  nlinarith [sq_nonneg u]

theorem sqrt_Y_sq {a b u : ℝ} (ha : 0 < a) (hab : a < b) :
    √(Yf a b u ^ 2 - 1) = 2 * √((u ^ 2 + a) * (u ^ 2 + b)) / (b - a) := by
  have hba : 0 < b - a := by linarith
  have hb : 0 < b := by linarith
  have h1 : Yf a b u ^ 2 - 1 = (2 * √((u ^ 2 + a) * (u ^ 2 + b)) / (b - a)) ^ 2 := by
    rw [div_pow, mul_pow, Real.sq_sqrt (by positivity)]
    unfold Yf
    field_simp
    ring
  rw [h1, Real.sqrt_sq (by positivity)]

theorem hasDerivAt_Phi {a b u : ℝ} (ha : 0 < a) (hab : a < b) (hu1 : 3 / 40 < u) (hu2 : u < 1) :
    HasDerivAt (Phi a b) (dPhi a b u) u := by
  have hba : 0 < b - a := by linarith
  -- the L part
  have d1 : HasDerivAt (fun u : ℝ => gfun (3 / 40 - u)) (-Real.log (u - 3 / 40)) u := by
    have h := (hasDerivAt_gfun_neg (x := 3 / 40 - u) (by linarith)).comp u
      ((hasDerivAt_id' u).const_sub (3 / 40))
    convert h using 1
    · rfl
    · rw [show -(3 / 40 - u) = u - 3 / 40 by ring]; ring
  have d2 : HasDerivAt (fun u : ℝ => gfun (3 / 40 + u)) (Real.log (3 / 40 + u)) u := by
    have h := (hasDerivAt_gfun (x := 3 / 40 + u) (by linarith)).comp u
      ((hasDerivAt_id' u).const_add (3 / 40))
    convert h using 1
    · rfl
    · ring
  have d3 : HasDerivAt (fun u : ℝ => gfun (1 - u)) (-Real.log (1 - u)) u := by
    have h := (hasDerivAt_gfun (x := 1 - u) (by linarith)).comp u
      ((hasDerivAt_id' u).const_sub 1)
    convert h using 1
    · rfl
    · ring
  have d4 : HasDerivAt (fun u : ℝ => gfun (1 + u)) (Real.log (1 + u)) u := by
    have h := (hasDerivAt_gfun (x := 1 + u) (by linarith)).comp u
      ((hasDerivAt_id' u).const_add 1)
    convert h using 1
    · rfl
    · ring
  have dL : HasDerivAt (Lg (3 / 40))
      (6 * (-Real.log (u - 3 / 40) + Real.log (3 / 40 + u)) + Real.log (1 - u) - Real.log (1 + u)) u := by
    have := ((d1.add d2).const_mul 6).sub d3 |>.sub d4
    convert this using 1
    · funext z; simp [Lg]
    · ring
  -- the arcosh part
  have dY : HasDerivAt (Yf a b) (4 * u / (b - a)) u := by
    have h := ((((hasDerivAt_pow 2 u).const_mul 2).add_const a).add_const b).div_const (b - a)
    convert h using 1
    · funext z; simp [Yf]
    · simp; ring
  have dA : HasDerivAt (fun u => Real.arcosh (Yf a b u))
      ((√(Yf a b u ^ 2 - 1))⁻¹ * (4 * u / (b - a))) u :=
    (Real.hasDerivAt_arcosh (Yf_gt_one ha hab)).comp u dY
  have hb : 0 < b := by linarith
  have hP : 0 < (u ^ 2 + a) * (u ^ 2 + b) := by positivity
  have hsq : 0 < √((u ^ 2 + a) * (u ^ 2 + b)) := Real.sqrt_pos.mpr hP
  have dPh : HasDerivAt (Phi a b) (6 * (-Real.log (u - 3 / 40) + Real.log (3 / 40 + u)) + Real.log (1 - u) -
      Real.log (1 + u) + 37 / 20 * ((√(Yf a b u ^ 2 - 1))⁻¹ * (4 * u / (b - a)))) u :=
    dL.add (dA.const_mul (37 / 20))
  convert dPh using 1
  unfold dPhi
  rw [sqrt_Y_sq ha hab]
  have h1 : Real.log ((u + 3 / 40) / (u - 3 / 40)) = Real.log (3 / 40 + u) - Real.log (u - 3 / 40) := by
    rw [Real.log_div (by linarith) (by linarith), add_comm]
  have h2 : Real.log ((1 - u) / (1 + u)) = Real.log (1 - u) - Real.log (1 + u) := by
    rw [Real.log_div (by linarith) (by linarith)]
  rw [h1, h2]
  field_simp
  ring


theorem dPhi_lt {a b : ℝ} (ha : 0 < a) (hab : a < b) (hab4 : a * b ≤ (3 / 40) ^ 4)
    {u1 u2 : ℝ} (h1 : 3 / 40 < u1) (h12 : u1 < u2) (h2 : u2 < 1) :
    dPhi a b u2 < dPhi a b u1 := by
  have hb : 0 < b := by linarith
  unfold dPhi
  have hu1 : 0 < u1 := by linarith
  have hu2 : 3 / 40 < u2 := by linarith
  have T1 : Real.log ((u2 + 3 / 40) / (u2 - 3 / 40)) < Real.log ((u1 + 3 / 40) / (u1 - 3 / 40)) := by
    apply Real.log_lt_log (div_pos (by linarith) (by linarith))
    rw [div_lt_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  have T2 : Real.log ((1 - u2) / (1 + u2)) ≤ Real.log ((1 - u1) / (1 + u1)) := by
    apply Real.log_le_log (div_pos (by linarith) (by linarith))
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  have T3 : u2 / √((u2 ^ 2 + a) * (u2 ^ 2 + b)) ≤ u1 / √((u1 ^ 2 + a) * (u1 ^ 2 + b)) := by
    have hP1 : 0 < (u1 ^ 2 + a) * (u1 ^ 2 + b) := by positivity
    have hP2 : 0 < (u2 ^ 2 + a) * (u2 ^ 2 + b) := by positivity
    have s1 := Real.sqrt_pos.mpr hP1
    have s2 := Real.sqrt_pos.mpr hP2
    rw [div_le_div_iff₀ s2 s1]
    have key : u2 ^ 2 * ((u1 ^ 2 + a) * (u1 ^ 2 + b)) ≤ u1 ^ 2 * ((u2 ^ 2 + a) * (u2 ^ 2 + b)) := by
      have hs : (3 / 40) ^ 2 < u1 ^ 2 := by nlinarith
      have ht : (3 / 40) ^ 2 < u2 ^ 2 := by nlinarith
      have hst : (3 / 40) ^ 4 < u1 ^ 2 * u2 ^ 2 := by nlinarith
      have hts : u1 ^ 2 ≤ u2 ^ 2 := by nlinarith
      nlinarith [mul_nonneg (sub_nonneg.mpr hts) (sub_nonneg.mpr (le_of_lt (lt_of_le_of_lt hab4 hst)))]
    have h := (pow_le_pow_iff_left₀ (by positivity : 0 ≤ u2 * √((u1 ^ 2 + a) * (u1 ^ 2 + b)))
      (by positivity : 0 ≤ u1 * √((u2 ^ 2 + a) * (u2 ^ 2 + b))) (by norm_num : (2 : ℕ) ≠ 0)).mp
    apply h
    rw [mul_pow, mul_pow, Real.sq_sqrt hP1.le, Real.sq_sqrt hP2.le]
    exact key
  have T3' : 37 / 10 * u2 / √((u2 ^ 2 + a) * (u2 ^ 2 + b)) ≤
      37 / 10 * u1 / √((u1 ^ 2 + a) * (u1 ^ 2 + b)) := by
    rw [mul_div_assoc, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left T3 (by norm_num)
  linarith

theorem dPhi_antitone {a b : ℝ} (ha : 0 < a) (hab : a < b) (hab4 : a * b ≤ (3 / 40) ^ 4)
    {u1 u2 : ℝ} (h1 : 3 / 40 < u1) (h12 : u1 ≤ u2) (h2 : u2 < 1) :
    dPhi a b u2 ≤ dPhi a b u1 := by
  rcases h12.lt_or_eq with h | h
  · exact (dPhi_lt ha hab hab4 h1 h h2).le
  · rw [h]

theorem continuous_Phi {a b : ℝ} (ha : 0 < a) (hab : a < b) : Continuous (Phi a b) := by
  unfold Phi Lg
  have hY : Continuous (Yf a b) := by unfold Yf; fun_prop
  have hA : Continuous (fun u => Real.arcosh (Yf a b u)) :=
    Real.continuousOn_arcosh.comp_continuous hY (fun u => (Yf_gt_one ha hab).le)
  have g1 : Continuous fun u : ℝ => gfun (3 / 40 - u) := continuous_gfun.comp (by fun_prop)
  have g2 : Continuous fun u : ℝ => gfun (3 / 40 + u) := continuous_gfun.comp (by fun_prop)
  have g3 : Continuous fun u : ℝ => gfun (1 - u) := continuous_gfun.comp (by fun_prop)
  have g4 : Continuous fun u : ℝ => gfun (1 + u) := continuous_gfun.comp (by fun_prop)
  exact (((g1.add g2).const_mul 6).sub g3 |>.sub g4).add (hA.const_mul _)

/-- **ZR07.**  The tangent bound at `u₀ ∈ (α, 1)`: `Φ(u) ≤ Φ(u₀) + Φ'(u₀)(u - u₀)` for `u ∈ (α, 1]`. -/
theorem Phi_tangent {a b : ℝ} (ha : 0 < a) (hab : a < b) (hab4 : a * b ≤ (3 / 40) ^ 4)
    {u0 u : ℝ} (h0 : 3 / 40 < u0) (h01 : u0 < 1) (hu : 3 / 40 < u) (hu1 : u ≤ 1) :
    Phi a b u ≤ Phi a b u0 + dPhi a b u0 * (u - u0) := by
  have hcc := continuous_Phi ha hab
  rcases lt_trichotomy u u0 with h | h | h
  · obtain ⟨ξ, hξ, hd⟩ := exists_hasDerivAt_eq_slope (Phi a b) (dPhi a b) h hcc.continuousOn
      (fun s hs => hasDerivAt_Phi ha hab (by linarith [hs.1]) (by linarith [hs.2]))
    have h1 : dPhi a b u0 ≤ dPhi a b ξ := dPhi_antitone ha hab hab4 (by linarith [hξ.1]) hξ.2.le h01
    have h2 : Phi a b u0 - Phi a b u = dPhi a b ξ * (u0 - u) := by
      rw [hd]; field_simp
    nlinarith [sub_pos.mpr h]
  · subst h; simp
  · obtain ⟨ξ, hξ, hd⟩ := exists_hasDerivAt_eq_slope (Phi a b) (dPhi a b) h hcc.continuousOn
      (fun s hs => hasDerivAt_Phi ha hab (by linarith [hs.1]) (by linarith [hs.2]))
    have h1 : dPhi a b ξ ≤ dPhi a b u0 :=
      dPhi_antitone ha hab hab4 h0 hξ.1.le (by linarith [hξ.2])
    have h2 : Phi a b u - Phi a b u0 = dPhi a b ξ * (u - u0) := by
      rw [hd]; field_simp
    nlinarith [sub_pos.mpr h]

/-- **ZR07 (concavity).**  `Φ_{a,b}` is strictly concave on `(α, 1]` when `ab ≤ α⁴`. -/
theorem Phi_strictConcaveOn {a b : ℝ} (ha : 0 < a) (hab : a < b) (hab4 : a * b ≤ (3 / 40) ^ 4) :
    StrictConcaveOn ℝ (Ioc (3 / 40) 1) (Phi a b) := by
  refine StrictAntiOn.strictConcaveOn_of_deriv (convex_Ioc _ _)
    (continuous_Phi ha hab).continuousOn ?_
  rw [interior_Ioc]
  intro u1 hu1 u2 hu2 h
  rw [(hasDerivAt_Phi ha hab hu1.1 hu1.2).deriv, (hasDerivAt_Phi ha hab hu2.1 hu2.2).deriv]
  exact dPhi_lt ha hab hab4 hu1.1 h hu2.2

end CatalanCore.Zeta5.Rho
