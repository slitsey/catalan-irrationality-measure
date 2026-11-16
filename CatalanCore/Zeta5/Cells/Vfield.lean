module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.Real.Pi.Bounds

@[expose] public section

/-!
# Z5-CELLS, part 1: the external field `V` in the variable `y = √t`, its derivative tower

With `α = 3/40` the field of Fauzan (6.1) is `V(t) = 2π√t + ∫₀¹ log(t+u²)du − 6∫₀^α log(t+u²)du`.
In the variable `y = √t` (ledger ZD09, ZD20) its closed form is
`Vy y = y · V1 y + log(y²+1) − 2 − 6α log(y²+α²) + 12α`, `V1 y = −3π − 2 arctan y + 12 arctan(y/α)`,
which is real analytic on all of `ℝ` (the cells use the continuation to `y < 0`).

* `Vy_eq_Vfld`: `Vfld (y²) = Vy α y` for `y ≥ 0` (bridge to the integral definition).
* `Dv α k`: the derivative tower `Dv 0 = Vy`, `Dv 1 = V1`, `Dv (k+1) = (Dv k)'` for `k ≤ 4`
  (closed rational functions from `k = 2`), `hasDerivAt_Dv`.
* `abs_Dv_le`: the pole-distance bounds `|V^{(m)}| ≤ 2(m-2)!/ρ₁^{m-1} + 12 (m-2)!/ρ_α^{m-1}`
  (ledger ZD20), for `ρ₁² ≤ y²+1`, `ρ_α² ≤ y²+α²`; `abs_V1_le`: `|V1| ≤ 10π`.

Everything is generic in `α > 0`; no design constant appears except in `Vfld`, `alpha0` (the
design value `3/40`).
-/

namespace CatalanCore.Zeta5.Cells

open Real

noncomputable section

/-- `V'(y) = 2ψ(y)`. -/
def V1 (α y : ℝ) : ℝ := -3 * π - 2 * arctan y + 12 * arctan (y / α)

/-- The field in the variable `y = √t`, analytic on `ℝ`. -/
def Vy (α y : ℝ) : ℝ :=
  y * V1 α y + Real.log (y ^ 2 + 1) - 2 - 6 * α * Real.log (y ^ 2 + α ^ 2) + 12 * α

/-- `n`-th derivative (`n ≤ 3`) of `y ↦ a / (y² + a²)`. -/
def Gd : ℕ → ℝ → ℝ → ℝ
  | 0, a, y => a / (y ^ 2 + a ^ 2)
  | 1, a, y => -2 * a * y / (y ^ 2 + a ^ 2) ^ 2
  | 2, a, y => a * (6 * y ^ 2 - 2 * a ^ 2) / (y ^ 2 + a ^ 2) ^ 3
  | 3, a, y => 24 * a * y * (a ^ 2 - y ^ 2) / (y ^ 2 + a ^ 2) ^ 4
  | _, _, _ => 0

/-- The derivative tower of `Vy`: `Dv 0 = Vy`, `Dv 1 = V1`, `Dv (k+2) = d^k/dy^k (V1')`,
`V1' = -2/(y²+1) + 12α/(y²+α²)`. -/
def Dv (α : ℝ) : ℕ → ℝ → ℝ
  | 0 => Vy α
  | 1 => V1 α
  | 2 => fun y => -2 * Gd 0 1 y + 12 * Gd 0 α y
  | 3 => fun y => -2 * Gd 1 1 y + 12 * Gd 1 α y
  | 4 => fun y => -2 * Gd 2 1 y + 12 * Gd 2 α y
  | 5 => fun y => -2 * Gd 3 1 y + 12 * Gd 3 α y
  | _ => fun _ => 0

/-! ### derivatives -/

theorem hasDerivAt_Gd0 {a : ℝ} (ha : 0 < a) (y : ℝ) : HasDerivAt (Gd 0 a) (Gd 1 a y) y := by
  have hs : y ^ 2 + a ^ 2 ≠ 0 := by positivity
  have h1 : HasDerivAt (fun y : ℝ => y ^ 2 + a ^ 2) (2 * y) y := by
    simpa using (hasDerivAt_pow 2 y).add_const (a ^ 2)
  have h := (hasDerivAt_const y a).fun_div h1 hs
  have e : Gd 0 a = fun y => a / (y ^ 2 + a ^ 2) := by funext z; simp [Gd]
  rw [e]
  convert h using 1
  simp only [Gd]; field_simp; ring

theorem hasDerivAt_Gd1 {a : ℝ} (ha : 0 < a) (y : ℝ) : HasDerivAt (Gd 1 a) (Gd 2 a y) y := by
  have hs : y ^ 2 + a ^ 2 ≠ 0 := by positivity
  have h1 : HasDerivAt (fun y : ℝ => y ^ 2 + a ^ 2) (2 * y) y := by
    simpa using (hasDerivAt_pow 2 y).add_const (a ^ 2)
  have h2 := h1.fun_pow 2
  have h3 : HasDerivAt (fun y : ℝ => -2 * a * y) (-2 * a) y := by
    simpa using (hasDerivAt_id y).const_mul (-2 * a)
  have h := h3.fun_div h2 (by positivity)
  have e : Gd 1 a = fun y => -2 * a * y / (y ^ 2 + a ^ 2) ^ 2 := by funext z; simp [Gd]
  rw [e]
  convert h using 1
  simp only [Gd]; field_simp; ring

theorem hasDerivAt_Gd2 {a : ℝ} (ha : 0 < a) (y : ℝ) : HasDerivAt (Gd 2 a) (Gd 3 a y) y := by
  have hs : y ^ 2 + a ^ 2 ≠ 0 := by positivity
  have h1 : HasDerivAt (fun y : ℝ => y ^ 2 + a ^ 2) (2 * y) y := by
    simpa using (hasDerivAt_pow 2 y).add_const (a ^ 2)
  have h2 := h1.fun_pow 3
  have h3 : HasDerivAt (fun y : ℝ => a * (6 * y ^ 2 - 2 * a ^ 2)) (a * (6 * (2 * y))) y := by
    have := (((hasDerivAt_pow 2 y).const_mul 6).sub_const (2 * a ^ 2)).const_mul a
    convert this using 1
    simp
  have h := h3.fun_div h2 (by positivity)
  have e : Gd 2 a = fun y => a * (6 * y ^ 2 - 2 * a ^ 2) / (y ^ 2 + a ^ 2) ^ 3 := by
    funext z; simp [Gd]
  rw [e]
  convert h using 1
  simp only [Gd]; field_simp; ring

theorem hasDerivAt_V1 {α : ℝ} (hα : 0 < α) (y : ℝ) : HasDerivAt (V1 α) (Dv α 2 y) y := by
  have h1 := (hasDerivAt_arctan y).const_mul (-2)
  have h2 := (((hasDerivAt_id' y).div_const α).arctan).const_mul 12
  have h := (h1.const_add (-3 * π)).add h2
  convert h using 1
  · ext z; simp [V1]; ring
  · simp only [Dv, Gd]
    field_simp
    ring

theorem hasDerivAt_Vy {α : ℝ} (hα : 0 < α) (y : ℝ) : HasDerivAt (Vy α) (V1 α y) y := by
  have hy1 : y ^ 2 + 1 ≠ 0 := by positivity
  have hy2 : y ^ 2 + α ^ 2 ≠ 0 := by positivity
  have hq : HasDerivAt (fun y : ℝ => y ^ 2) (2 * y) y := by simpa using hasDerivAt_pow 2 y
  have h1 := (hasDerivAt_id' y).mul (hasDerivAt_V1 hα y)
  have h2 := (hq.add_const 1).log hy1
  have h3 := (hq.add_const (α ^ 2)).log hy2
  have h := (((h1.add h2).sub_const 2).sub (h3.const_mul (6 * α))).add_const (12 * α)
  convert h using 1
  · funext z
    simp only [Vy, Pi.add_apply, Pi.sub_apply, Pi.mul_apply]
  · simp only [Dv, Gd]
    field_simp
    ring


/-! ### the pole-distance bounds (ZD20) -/

/-- from `R² ≤ F² s^(n+1)` to `|R / s^(n+1)| ρ^(n+1) ≤ F`. -/
theorem abs_div_pow_mul_le {R s ρ F : ℝ} (n : ℕ) (hs : 0 < s) (hρ : 0 < ρ) (hρs : ρ ^ 2 ≤ s)
    (hF : 0 ≤ F) (hR : R ^ 2 ≤ F ^ 2 * s ^ (n + 1)) :
    |R / s ^ (n + 1)| * ρ ^ (n + 1) ≤ F := by
  have hsp : 0 < s ^ (n + 1) := pow_pos hs _
  have h1 : (|R / s ^ (n + 1)| * ρ ^ (n + 1)) ^ 2 ≤ F ^ 2 := by
    have e : (|R / s ^ (n + 1)| * ρ ^ (n + 1)) ^ 2 = (R / s ^ (n + 1)) ^ 2 * (ρ ^ 2) ^ (n + 1) := by
      rw [mul_pow, sq_abs, ← pow_mul, ← pow_mul, mul_comm 2 (n + 1)]
    rw [e]
    have h2 : (ρ ^ 2) ^ (n + 1) ≤ s ^ (n + 1) := pow_le_pow_left₀ (by positivity) hρs _
    calc (R / s ^ (n + 1)) ^ 2 * (ρ ^ 2) ^ (n + 1)
        ≤ (R / s ^ (n + 1)) ^ 2 * s ^ (n + 1) :=
          mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
      _ = R ^ 2 / s ^ (n + 1) := by field_simp
      _ ≤ F ^ 2 := by rw [div_le_iff₀ hsp]; exact hR
  exact (sq_le_sq₀ (by positivity) hF).mp h1

theorem abs_Gd_mul_le {a y ρ : ℝ} (ha : 0 < a) (hρ : 0 < ρ) (hρs : ρ ^ 2 ≤ y ^ 2 + a ^ 2)
    (n : ℕ) (hn : n ≤ 3) : |Gd n a y| * ρ ^ (n + 1) ≤ (n.factorial : ℝ) := by
  have hs : 0 < y ^ 2 + a ^ 2 := by positivity
  interval_cases n
  · have := abs_div_pow_mul_le (R := a) (F := 1) 0 hs hρ hρs (by norm_num)
      (by norm_num <;> nlinarith [sq_nonneg y])
    simpa [Gd] using this
  · have := abs_div_pow_mul_le (R := -2 * a * y) (F := 1) 1 hs hρ hρs (by norm_num)
      (by norm_num <;> nlinarith [sq_nonneg (y ^ 2 - a ^ 2)])
    simpa [Gd] using this
  · have := abs_div_pow_mul_le (R := a * (6 * y ^ 2 - 2 * a ^ 2)) (F := 2) 2 hs hρ hρs
      (by norm_num) (by norm_num <;> nlinarith [sq_nonneg (y ^ 3 - 3 * y * a ^ 2)])
    simpa [Gd, Nat.factorial] using this
  · have := abs_div_pow_mul_le (R := 24 * a * y * (a ^ 2 - y ^ 2)) (F := 6) 3 hs hρ hρs
      (by norm_num) (by norm_num <;> nlinarith [sq_nonneg ((a ^ 2 - y ^ 2) ^ 2 - 4 * a ^ 2 * y ^ 2)])
    simpa [Gd, Nat.factorial] using this

theorem abs_Gd_le {a y ρ : ℝ} (ha : 0 < a) (hρ : 0 < ρ) (hρs : ρ ^ 2 ≤ y ^ 2 + a ^ 2)
    (n : ℕ) (hn : n ≤ 3) : |Gd n a y| ≤ (n.factorial : ℝ) / ρ ^ (n + 1) := by
  rw [le_div_iff₀ (by positivity)]
  exact abs_Gd_mul_le ha hρ hρs n hn

/-- **ZD20, the pole-distance bound**: `|V^{(n+2)}(y)| ≤ 2 n!/ρ₁^{n+1} + 12 n!/ρ_α^{n+1}` for
`n ≤ 3`, whenever `ρ₁² ≤ y²+1` and `ρ_α² ≤ y²+α²`. -/
theorem abs_Dv_le {α y ρ1 ρa : ℝ} (hα : 0 < α) (h1 : 0 < ρ1) (ha : 0 < ρa)
    (hs1 : ρ1 ^ 2 ≤ y ^ 2 + 1) (hsa : ρa ^ 2 ≤ y ^ 2 + α ^ 2) (n : ℕ) (hn : n ≤ 3) :
    |Dv α (n + 2) y| ≤
      2 * ((n.factorial : ℝ) / ρ1 ^ (n + 1)) + 12 * ((n.factorial : ℝ) / ρa ^ (n + 1)) := by
  have hs1' : ρ1 ^ 2 ≤ y ^ 2 + (1 : ℝ) ^ 2 := by simpa using hs1
  have e : Dv α (n + 2) y = -2 * Gd n 1 y + 12 * Gd n α y := by
    interval_cases n <;> rfl
  rw [e]
  have b1 := abs_Gd_le (by norm_num : (0 : ℝ) < 1) h1 hs1' n hn
  have b2 := abs_Gd_le hα ha hsa n hn
  calc |-2 * Gd n 1 y + 12 * Gd n α y| ≤ |-2 * Gd n 1 y| + |12 * Gd n α y| := abs_add_le _ _
    _ = 2 * |Gd n 1 y| + 12 * |Gd n α y| := by
        rw [abs_mul, abs_mul]; norm_num
    _ ≤ _ := by linarith

theorem abs_V1_le (α y : ℝ) : |V1 α y| ≤ 10 * π := by
  have a1 := Real.arctan_lt_pi_div_two y
  have a2 := Real.neg_pi_div_two_lt_arctan y
  have a3 := Real.arctan_lt_pi_div_two (y / α)
  have a4 := Real.neg_pi_div_two_lt_arctan (y / α)
  unfold V1
  rw [abs_le]
  constructor <;> nlinarith [Real.pi_pos]

/-! ### the bridge to the integral definition of `V` -/

/-- Ported from mo271/Zeta5 (Apache-2.0), commit 7fe736760f4b96bfdb4334b68e3b3124ecbe10b0,
Apery/PotentialV.lean (`GVpot`, `hasDerivAt_GV`, `integral_log_add_sq`); changes: namespace. -/
def GVpot (t u : ℝ) : ℝ :=
  u * Real.log (t + u ^ 2) - 2 * u + 2 * Real.sqrt t * Real.arctan (u / Real.sqrt t)

theorem hasDerivAt_GV {t : ℝ} (ht : 0 < t) (u : ℝ) :
    HasDerivAt (GVpot t) (Real.log (t + u ^ 2)) u := by
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hs2 : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht.le
  have h1 : HasDerivAt (fun u : ℝ => u * Real.log (t + u ^ 2))
      (1 * Real.log (t + u ^ 2) + u * ((2 * u) / (t + u ^ 2))) u := by
    have hlog : HasDerivAt (fun u : ℝ => Real.log (t + u ^ 2)) ((2 * u) / (t + u ^ 2)) u := by
      have := ((hasDerivAt_pow 2 u).const_add t).log (by positivity)
      simpa using this
    exact (hasDerivAt_id u).mul hlog
  have h2 : HasDerivAt (fun u : ℝ => 2 * u) 2 u := by simpa using (hasDerivAt_id u).const_mul 2
  have h3 : HasDerivAt (fun u : ℝ => 2 * Real.sqrt t * Real.arctan (u / Real.sqrt t))
      (2 * Real.sqrt t * ((1 / (1 + (u / Real.sqrt t) ^ 2)) * (1 / Real.sqrt t))) u := by
    have := ((hasDerivAt_id u).div_const (Real.sqrt t)).arctan
    simpa using this.const_mul (2 * Real.sqrt t)
  have h := (h1.sub h2).add h3
  refine h.congr_deriv ?_
  have hne : t + u ^ 2 ≠ 0 := by positivity
  field_simp
  rw [hs2]
  ring

theorem integral_log_add_sq {t : ℝ} (ht : 0 < t) (c : ℝ) :
    ∫ u in (0 : ℝ)..c, Real.log (t + u ^ 2) =
      c * Real.log (t + c ^ 2) - 2 * c + 2 * Real.sqrt t * Real.arctan (c / Real.sqrt t) := by
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := c) (f := GVpot t)
    (f' := fun u => Real.log (t + u ^ 2)) (fun u _ => hasDerivAt_GV ht u)
    ((Continuous.log (by fun_prop) (fun u => by positivity)).intervalIntegrable _ _)
  rw [this]
  simp [GVpot]

/-- The external field of Fauzan (6.1) in the variable `t`, `α = 3/40`. -/
def Vfld (t : ℝ) : ℝ :=
  2 * Real.pi * Real.sqrt t + (∫ u in (0 : ℝ)..1, Real.log (t + u ^ 2)) -
    6 * ∫ u in (0 : ℝ)..(3 / 40), Real.log (t + u ^ 2)

/-- **ZD09 in the variable `y`**: `V(y²) = Vy (3/40) y` for `y ≥ 0`. -/
theorem Vfld_sq {y : ℝ} (hy : 0 ≤ y) : Vfld (y ^ 2) = Vy (3 / 40) y := by
  unfold Vfld
  rcases hy.eq_or_lt with rfl | hy
  · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Real.sqrt_zero, mul_zero,
      zero_add, Vy, V1, zero_div, Real.arctan_zero, sub_zero, add_zero, one_pow, Real.log_one]
    have hl : ∀ c : ℝ, ∫ u in (0 : ℝ)..c, Real.log (u ^ 2) = 2 * (c * Real.log c - c) := by
      intro c
      have : ∀ u : ℝ, Real.log (u ^ 2) = 2 * Real.log u := fun u => by
        rw [Real.log_pow] <;> norm_num
      simp_rw [this]
      rw [intervalIntegral.integral_const_mul, integral_log]
      simp
    rw [hl, hl]
    have : Real.log ((3 / 40 : ℝ) ^ 2) = 2 * Real.log (3 / 40) := by
      rw [Real.log_pow] <;> norm_num
    rw [this]
    norm_num [Real.log_one]
    ring
  · have hy2 : 0 < y ^ 2 := by positivity
    rw [integral_log_add_sq hy2, integral_log_add_sq hy2, Real.sqrt_sq hy.le]
    have e1 : Real.arctan (1 / y) = π / 2 - Real.arctan y := by
      rw [one_div, Real.arctan_inv_of_pos hy]
    have e2 : Real.arctan (3 / 40 / y) = π / 2 - Real.arctan (y / (3 / 40)) := by
      have := Real.arctan_inv_of_pos (x := y / (3 / 40)) (by positivity)
      rw [inv_div] at this
      exact this
    simp only [Vy, V1]
    rw [e1, e2]
    ring

end

end CatalanCore.Zeta5.Cells
