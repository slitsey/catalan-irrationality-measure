module
public import CatalanCore.Uniform.Decay.Tools.Green
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
@[expose] public section

/-!
# Elementary boundary-energy identity (centred-monomial radial divergence identity)

Put origin at the intersection of two supporting lines.  For segments `s ↦ s u`, `t ↦ t v`,
`|s u - t v|² = A s² + 2 B s t + C t²` (a real quadratic form, `A = |u|²`, `B = -Re(u v̄)`,
`C = |v|²`).  With `L = ½ log (A s² + 2 B s t + C t²)` and the centred monomial `s^i t^j`:
`div ( (s,t) · s^i t^j L ) = (i+j+2) s^i t^j L + s^i t^j`
(Euler's identity `s ∂ₛ L + t ∂ₜ L = 1`).  Hence on a rectangle avoiding the zero set
(`boundary_energy_identity`)
`(i+j+2) ∬ s^i t^j L = ∫ (b^{i+1} t^j L(b,t) - a^{i+1} t^j L(a,t)) dt
   + ∫ (s^i d^{j+1} L(s,d) - s^i c^{j+1} L(s,c)) ds - (b^{i+1}-a^{i+1})(d^{j+1}-c^{j+1})/((i+1)(j+1))`:
the double logarithmic integral is reduced to one-dimensional elementary boundary potential moments
and an exact polynomial moment.  (Rectangles touching the singular corner/line are not covered
by this statement.)
-/

namespace CatalanCore.Uniform.Decay.Tools

open Set intervalIntegral

/-- The quadratic form `|s u - t v|²`. -/
def qf (A B C s t : ℝ) : ℝ := A * s ^ 2 + 2 * B * s * t + C * t ^ 2

/-- `L = ½ log |s u - t v|²`. -/
noncomputable def Lq (A B C s t : ℝ) : ℝ := Real.log (qf A B C s t) / 2

section
variable (A B C : ℝ) (i j : ℕ)

/-- `s ∂ₛ`-part: `G = s^(i+1) t^j L`. -/
noncomputable def Gm (s t : ℝ) : ℝ := s ^ (i + 1) * t ^ j * Lq A B C s t
/-- `H̃ = s^i t^(j+1) L - s^i t^(j+1)/(j+1)`. -/
noncomputable def Hm (s t : ℝ) : ℝ :=
  s ^ i * t ^ (j + 1) * Lq A B C s t - s ^ i * t ^ (j + 1) / ((j : ℝ) + 1)
noncomputable def DgM (s t : ℝ) : ℝ :=
  ((i : ℝ) + 1) * s ^ i * t ^ j * Lq A B C s t +
    s ^ (i + 1) * t ^ j * ((A * s + B * t) / qf A B C s t)
noncomputable def DhM (s t : ℝ) : ℝ :=
  ((j : ℝ) + 1) * s ^ i * t ^ j * Lq A B C s t +
    s ^ i * t ^ (j + 1) * ((B * s + C * t) / qf A B C s t) - s ^ i * t ^ j

theorem hasDerivAt_Lq_s (s t : ℝ) (h : 0 < qf A B C s t) :
    HasDerivAt (fun x => Lq A B C x t) ((A * s + B * t) / qf A B C s t) s := by
  have hq : HasDerivAt (fun x => qf A B C x t) (2 * A * s + 2 * B * t) s := by
    unfold qf
    have := (((hasDerivAt_pow 2 s).const_mul A).add ((hasDerivAt_id s).const_mul (2 * B * t))).add_const
      (C * t ^ 2)
    convert this using 1
    · ext x; simp; ring
    · simp; ring
  have := (hq.log h.ne').div_const 2
  unfold Lq
  convert this using 1
  field_simp
  try ring

theorem hasDerivAt_Lq_t (s t : ℝ) (h : 0 < qf A B C s t) :
    HasDerivAt (fun y => Lq A B C s y) ((B * s + C * t) / qf A B C s t) t := by
  have hq : HasDerivAt (fun y => qf A B C s y) (2 * B * s + 2 * C * t) t := by
    unfold qf
    have := (((hasDerivAt_id t).const_mul (2 * B * s)).const_add (A * s ^ 2)).add
      ((hasDerivAt_pow 2 t).const_mul C)
    convert this using 1
    · ext x; simp
    · simp; ring
  have := (hq.log h.ne').div_const 2
  unfold Lq
  convert this using 1
  field_simp
  try ring

theorem hasDerivAt_Gm (s t : ℝ) (h : 0 < qf A B C s t) :
    HasDerivAt (fun x => Gm A B C i j x t) (DgM A B C i j s t) s := by
  have h1 := ((hasDerivAt_pow (i + 1) s).mul_const (t ^ j))
  have := h1.mul (hasDerivAt_Lq_s A B C s t h)
  unfold Gm DgM
  convert this using 1
  simp only [Nat.add_sub_cancel]
  push_cast
  ring

theorem hasDerivAt_Hm (s t : ℝ) (h : 0 < qf A B C s t) :
    HasDerivAt (fun y => Hm A B C i j s y) (DhM A B C i j s t) t := by
  have h1 := ((hasDerivAt_pow (j + 1) t).const_mul (s ^ i))
  have h2 := h1.mul (hasDerivAt_Lq_t A B C s t h)
  have h3 := (h1.div_const ((j : ℝ) + 1))
  have := h2.sub h3
  unfold Hm DhM
  convert this using 1
  have hj : ((j : ℝ) + 1) ≠ 0 := by positivity
  simp only [Nat.add_sub_cancel]
  push_cast
  field_simp
  try ring

/-- Euler's identity: `DgM + DhM = (i+j+2) s^i t^j L`. -/
theorem DgM_add_DhM (s t : ℝ) (h : 0 < qf A B C s t) :
    DgM A B C i j s t + DhM A B C i j s t
      = ((i : ℝ) + j + 2) * (s ^ i * t ^ j * Lq A B C s t) := by
  unfold DgM DhM
  have hq : qf A B C s t ≠ 0 := h.ne'
  have e : s ^ (i + 1) * t ^ j * ((A * s + B * t) / qf A B C s t) +
      s ^ i * t ^ (j + 1) * ((B * s + C * t) / qf A B C s t) = s ^ i * t ^ j := by
    have : qf A B C s t = s * (A * s + B * t) + t * (B * s + C * t) := by unfold qf; ring
    field_simp
    rw [this]; ring
  linear_combination e

end

set_option maxHeartbeats 1000000 in
theorem boundary_energy_identity (A B C : ℝ) (i j : ℕ) {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (hpos : ∀ s ∈ Icc a b, ∀ t ∈ Icc c d, 0 < qf A B C s t) :
    ((i : ℝ) + j + 2) * ∫ s in a..b, ∫ t in c..d, s ^ i * t ^ j * Lq A B C s t
      = (∫ t in c..d, (b ^ (i + 1) * t ^ j * Lq A B C b t - a ^ (i + 1) * t ^ j * Lq A B C a t))
        + (∫ s in a..b, (s ^ i * d ^ (j + 1) * Lq A B C s d - s ^ i * c ^ (j + 1) * Lq A B C s c))
        - (b ^ (i + 1) - a ^ (i + 1)) * (d ^ (j + 1) - c ^ (j + 1)) / (((i : ℝ) + 1) * ((j : ℝ) + 1)) := by
  set R : Set (ℝ × ℝ) := Icc a b ×ˢ Icc c d with hR
  have hqc : ContinuousOn (fun p : ℝ × ℝ => qf A B C p.1 p.2) R := by
    unfold qf; fun_prop
  have hqne : ∀ p ∈ R, qf A B C p.1 p.2 ≠ 0 := fun p hp => (hpos p.1 hp.1 p.2 hp.2).ne'
  have hlog : ContinuousOn (fun p : ℝ × ℝ => Lq A B C p.1 p.2) R := by
    unfold Lq
    exact (ContinuousOn.log hqc hqne).div_const 2
  have hDg : ContinuousOn (Function.uncurry (DgM A B C i j)) R := by
    unfold DgM
    have h1 : ContinuousOn (fun p : ℝ × ℝ => (A * p.1 + B * p.2) / qf A B C p.1 p.2) R :=
      ContinuousOn.div (by fun_prop) hqc hqne
    show ContinuousOn (fun p : ℝ × ℝ => ((i : ℝ) + 1) * p.1 ^ i * p.2 ^ j * Lq A B C p.1 p.2 +
      p.1 ^ (i + 1) * p.2 ^ j * ((A * p.1 + B * p.2) / qf A B C p.1 p.2)) R
    exact (((by fun_prop : Continuous fun p : ℝ × ℝ => ((i : ℝ) + 1) * p.1 ^ i * p.2 ^ j).continuousOn).mul hlog).add
      ((by fun_prop : Continuous fun p : ℝ × ℝ => p.1 ^ (i + 1) * p.2 ^ j).continuousOn.mul h1)
  have hDh : ContinuousOn (Function.uncurry (DhM A B C i j)) R := by
    unfold DhM
    have h1 : ContinuousOn (fun p : ℝ × ℝ => (B * p.1 + C * p.2) / qf A B C p.1 p.2) R :=
      ContinuousOn.div (by fun_prop) hqc hqne
    show ContinuousOn (fun p : ℝ × ℝ => ((j : ℝ) + 1) * p.1 ^ i * p.2 ^ j * Lq A B C p.1 p.2 +
      p.1 ^ i * p.2 ^ (j + 1) * ((B * p.1 + C * p.2) / qf A B C p.1 p.2) - p.1 ^ i * p.2 ^ j) R
    exact ((((by fun_prop : Continuous fun p : ℝ × ℝ => ((j : ℝ) + 1) * p.1 ^ i * p.2 ^ j).continuousOn).mul hlog).add
      ((by fun_prop : Continuous fun p : ℝ × ℝ => p.1 ^ i * p.2 ^ (j + 1)).continuousOn.mul h1)).sub
      (by fun_prop : Continuous fun p : ℝ × ℝ => p.1 ^ i * p.2 ^ j).continuousOn
  have hg := green_rect (Gm A B C i j) (Hm A B C i j) (DgM A B C i j) (DhM A B C i j) hab hcd
    hDg hDh (fun s hs t ht => hasDerivAt_Gm A B C i j s t (hpos s hs t ht))
    (fun s hs t ht => hasDerivAt_Hm A B C i j s t (hpos s hs t ht))
  -- left side
  have hL : ∫ s in a..b, ∫ t in c..d, (DgM A B C i j s t + DhM A B C i j s t)
      = ((i : ℝ) + j + 2) * ∫ s in a..b, ∫ t in c..d, s ^ i * t ^ j * Lq A B C s t := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun s hs => ?_
    have hs' : s ∈ Icc a b := by simpa [uIcc_of_le hab] using hs
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t ht => ?_
    have ht' : t ∈ Icc c d := by simpa [uIcc_of_le hcd] using ht
    exact DgM_add_DhM A B C i j s t (hpos s hs' t ht')
  rw [hL] at hg
  rw [hg]
  -- right side: split the polynomial part of Hm
  have hc1 : ContinuousOn (fun s => s ^ i * d ^ (j + 1) * Lq A B C s d -
      s ^ i * c ^ (j + 1) * Lq A B C s c) (Icc a b) := by
    have hmd : ∀ s ∈ Icc a b, (s, d) ∈ R := fun s hs => ⟨hs, right_mem_Icc.2 hcd⟩
    have hmc : ∀ s ∈ Icc a b, (s, c) ∈ R := fun s hs => ⟨hs, left_mem_Icc.2 hcd⟩
    have hd : ContinuousOn (fun s => Lq A B C s d) (Icc a b) :=
      ContinuousOn.comp (g := fun p : ℝ × ℝ => Lq A B C p.1 p.2) (f := fun s : ℝ => (s, d))
        hlog (by fun_prop) hmd
    have hc : ContinuousOn (fun s => Lq A B C s c) (Icc a b) :=
      ContinuousOn.comp (g := fun p : ℝ × ℝ => Lq A B C p.1 p.2) (f := fun s : ℝ => (s, c))
        hlog (by fun_prop) hmc
    exact (((by fun_prop : Continuous fun s : ℝ => s ^ i * d ^ (j + 1)).continuousOn).mul hd).sub
      (((by fun_prop : Continuous fun s : ℝ => s ^ i * c ^ (j + 1)).continuousOn).mul hc)
  have hpoly : IntervalIntegrable (fun s : ℝ => s ^ i * ((d ^ (j + 1) - c ^ (j + 1)) / ((j : ℝ) + 1)))
      MeasureTheory.volume a b :=
    (by fun_prop : Continuous fun s : ℝ => s ^ i * ((d ^ (j + 1) - c ^ (j + 1)) / ((j : ℝ) + 1))).intervalIntegrable _ _
  have hsplit : ∫ s in a..b, (Hm A B C i j s d - Hm A B C i j s c)
      = (∫ s in a..b, (s ^ i * d ^ (j + 1) * Lq A B C s d - s ^ i * c ^ (j + 1) * Lq A B C s c))
        - (b ^ (i + 1) - a ^ (i + 1)) * (d ^ (j + 1) - c ^ (j + 1)) /
            (((i : ℝ) + 1) * ((j : ℝ) + 1)) := by
    have e : ∀ s : ℝ, Hm A B C i j s d - Hm A B C i j s c
        = (s ^ i * d ^ (j + 1) * Lq A B C s d - s ^ i * c ^ (j + 1) * Lq A B C s c)
          - s ^ i * ((d ^ (j + 1) - c ^ (j + 1)) / ((j : ℝ) + 1)) := by
      intro s; unfold Hm; ring
    simp_rw [e]
    rw [intervalIntegral.integral_sub (hc1.intervalIntegrable_of_Icc hab) hpoly,
      intervalIntegral.integral_mul_const, integral_pow]
    have hi : ((i : ℝ) + 1) ≠ 0 := by positivity
    have hj : ((j : ℝ) + 1) ≠ 0 := by positivity
    congr 1
    push_cast
    field_simp
  rw [hsplit]
  have hG : (∫ t in c..d, (Gm A B C i j b t - Gm A B C i j a t))
      = ∫ t in c..d, (b ^ (i + 1) * t ^ j * Lq A B C b t - a ^ (i + 1) * t ^ j * Lq A B C a t) := rfl
  rw [hG]
  ring

end CatalanCore.Uniform.Decay.Tools
