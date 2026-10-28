module

public import CatalanCore.Uniform.Decay.Assembly.CornerEdge

@[expose] public section

/-!
# Singular-corner boundary energy, part 2: the identity on `[0, b] × [0, d]`

`boundary_energy_corner`: for a positive definite form (`PD A B C m K`, i.e. the two supporting
lines are distinct and the singular corner is the origin) and `b, d > 0`, the identity of
`boundary_energy_identity` holds on the rectangle `[0,b] × [0,d]` that has the singular corner
`(0,0)` as a vertex (`L = ½ log qf` has a logarithmic, hence integrable, singularity there).

Proof: apply the smooth identity on `[ε,b] × [ε,d]` and let `ε → 0⁺`.  The double integral
converges because `|s^i t^j L| ≤ b^i d^j (c + |log t|)` on `(0,b] × (0,d]` and the inner integrals
over `[0, ε]` are `O(ε |log ε|)`; the single-integral boundary terms converge by continuity of the
primitive, and the two edge terms at `s = ε`, `t = ε` vanish (`edge_vanish`).
-/

namespace CatalanCore.Uniform.Decay.Assembly

open Set intervalIntegral MeasureTheory Filter Topology
open CatalanCore.Uniform.Decay.Tools

theorem tendsto_lower {g : ℝ → ℝ} {d : ℝ} (hd : 0 < d) (h : IntervalIntegrable g volume 0 d) :
    Tendsto (fun ε : ℝ => ∫ t in ε..d, g t) (𝓝[>] 0) (𝓝 (∫ t in (0 : ℝ)..d, g t)) := by
  have hI : IntegrableOn g (uIcc (0 : ℝ) d) volume := by
    rw [uIcc_of_le hd.le]
    exact (integrableOn_Icc_iff_integrableOn_Ioc).2
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hd.le).1 h)
  have hc := (continuousOn_primitive_interval_left hI) 0 (by simp [uIcc_of_le hd.le, hd.le])
  exact hc.mono_of_mem_nhdsWithin (by rw [uIcc_of_le hd.le]; exact Icc_mem_nhdsGT hd)

/-- The integrand `s^i t^j L(s,t)`. -/
noncomputable def ff (A B C : ℝ) (i j : ℕ) (s t : ℝ) : ℝ := s ^ i * t ^ j * Lq A B C s t

variable {A B C m K : ℝ}

theorem PD.qf_pos (h : PD A B C m K) {s t : ℝ} (hst : s ≠ 0 ∨ t ≠ 0) : 0 < qf A B C s t := by
  have hm := h.m_pos
  have h1 : 0 < s ^ 2 + t ^ 2 := by
    rcases hst with h' | h'
    · have : 0 < s ^ 2 := by positivity
      nlinarith [sq_nonneg t]
    · have : 0 < t ^ 2 := by positivity
      nlinarith [sq_nonneg s]
  exact lt_of_lt_of_le (mul_pos hm h1) (h.lower s t)

theorem PD.continuous_Lq_t (h : PD A B C m K) {s : ℝ} (hs : s ≠ 0) :
    Continuous fun t => Lq A B C s t := by
  unfold Lq
  have : Continuous fun t => qf A B C s t := by unfold qf; fun_prop
  exact (Continuous.log this (fun t => (h.qf_pos (Or.inl hs)).ne')).div_const 2

theorem PD.continuous_Lq_s (h : PD A B C m K) {t : ℝ} (ht : t ≠ 0) :
    Continuous fun s => Lq A B C s t := by
  unfold Lq
  have : Continuous fun s => qf A B C s t := by unfold qf; fun_prop
  exact (Continuous.log this (fun s => (h.qf_pos (Or.inr ht)).ne')).div_const 2

theorem measurable_ff (A B C : ℝ) (i j : ℕ) :
    Measurable fun p : ℝ × ℝ => ff A B C i j p.1 p.2 := by
  unfold ff Lq qf
  fun_prop

/-- The logarithmic constant. -/
noncomputable def cc (m K b d : ℝ) : ℝ :=
  (|Real.log m| + |Real.log K| + |Real.log (b ^ 2 + d ^ 2)|) / 2

theorem cc_nonneg (m K b d : ℝ) : 0 ≤ cc m K b d := by unfold cc; positivity

theorem ff_bound (h : PD A B C m K) (i j : ℕ) {b d s t : ℝ} (hs : 0 < s) (hsb : s ≤ b)
    (ht : 0 < t) (htd : t ≤ d) :
    |ff A B C i j s t| ≤ b ^ i * d ^ j * (cc m K b d + |Real.log t|) := by
  have hb : 0 < b := lt_of_lt_of_le hs hsb
  have hd : 0 < d := lt_of_lt_of_le ht htd
  have hL := h.Lq_bound (s := s) (t := t) (ρ := t ^ 2) (R := b ^ 2 + d ^ 2) (by positivity)
    (by nlinarith [sq_nonneg s]) (by nlinarith [sq_nonneg s, sq_nonneg t])
  have hlog : |Real.log (t ^ 2)| = 2 * |Real.log t| := by
    rw [Real.log_pow]; push_cast; rw [abs_mul]; norm_num
  rw [hlog] at hL
  have hLL : |Lq A B C s t| ≤ cc m K b d + |Real.log t| := by
    refine hL.trans (le_of_eq ?_); unfold cc; ring
  unfold ff
  rw [abs_mul, abs_mul, abs_pow, abs_pow, abs_of_pos hs, abs_of_pos ht]
  have h1 : s ^ i ≤ b ^ i := pow_le_pow_left₀ hs.le hsb i
  have h2 : t ^ j ≤ d ^ j := pow_le_pow_left₀ ht.le htd j
  have h3 : 0 ≤ t ^ j := by positivity
  calc s ^ i * t ^ j * |Lq A B C s t| ≤ b ^ i * d ^ j * (cc m K b d + |Real.log t|) :=
        mul_le_mul (mul_le_mul h1 h2 h3 (by positivity)) hLL (abs_nonneg _) (by positivity)

/-- The inner integral `∫_λ^d ff(s,t) dt`. -/
noncomputable def Psi (A B C : ℝ) (i j : ℕ) (d lam s : ℝ) : ℝ := ∫ t in lam..d, ff A B C i j s t

theorem PD.intervalIntegrable_ff (h : PD A B C m K) (i j : ℕ) {s : ℝ} (hs : s ≠ 0) (a b : ℝ) :
    IntervalIntegrable (fun t => ff A B C i j s t) volume a b := by
  unfold ff
  exact ((continuous_const.mul (continuous_id.pow j)).mul (h.continuous_Lq_t hs)).intervalIntegrable
    _ _

/-- `Λ_d = ∫_0^d |log t| dt`. -/
noncomputable def Lam (d : ℝ) : ℝ := ∫ t in (0 : ℝ)..d, |Real.log t|

theorem intervalIntegrable_bd (c b d : ℝ) (i j : ℕ) :
    IntervalIntegrable (fun t : ℝ => b ^ i * d ^ j * (c + |Real.log t|)) volume 0 d := by
  have h1 : IntervalIntegrable (fun t : ℝ => |Real.log t|) volume 0 d :=
    (intervalIntegral.intervalIntegrable_log').abs
  exact (intervalIntegrable_const.add h1).const_mul _

theorem PD.psi_bound (h : PD A B C m K) (i j : ℕ) {b d lam s : ℝ} (hd : 0 < d) (hl0 : 0 ≤ lam)
    (hld : lam ≤ d) (hs : 0 < s) (hsb : s ≤ b) :
    ‖Psi A B C i j d lam s‖ ≤ b ^ i * d ^ j * (cc m K b d * d + Lam d) := by
  unfold Psi
  have hb : 0 < b := lt_of_lt_of_le hs hsb
  have hbd := intervalIntegrable_bd (cc m K b d) b d i j
  have hbd' : IntervalIntegrable (fun t : ℝ => b ^ i * d ^ j * (cc m K b d + |Real.log t|))
      volume lam d := by
    refine hbd.mono_set ?_
    rw [uIcc_of_le hld, uIcc_of_le hd.le]
    exact Icc_subset_Icc hl0 le_rfl
  have h1 := intervalIntegral.norm_integral_le_of_norm_le (a := lam) (b := d) hld
    (f := fun t => ff A B C i j s t)
    (g := fun t : ℝ => b ^ i * d ^ j * (cc m K b d + |Real.log t|))
    (Filter.Eventually.of_forall (fun t ht => by
      have ht0 : 0 < t := lt_of_le_of_lt hl0 ht.1
      rw [Real.norm_eq_abs]
      exact ff_bound h i j hs hsb ht0 ht.2)) hbd'
  have h2 : ∫ t in lam..d, b ^ i * d ^ j * (cc m K b d + |Real.log t|)
      ≤ ∫ t in (0 : ℝ)..d, b ^ i * d ^ j * (cc m K b d + |Real.log t|) :=
    intervalIntegral.integral_mono_interval hl0 hld le_rfl
      (Filter.Eventually.of_forall (fun t => by
        have := cc_nonneg m K b d
        positivity)) hbd
  have h3 : ∫ t in (0 : ℝ)..d, b ^ i * d ^ j * (cc m K b d + |Real.log t|)
      = b ^ i * d ^ j * (cc m K b d * d + Lam d) := by
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add
      intervalIntegrable_const (intervalIntegral.intervalIntegrable_log').abs]
    rw [intervalIntegral.integral_const]
    simp only [smul_eq_mul, sub_zero, Lam]
    ring
  linarith

theorem measurable_Psi (A B C : ℝ) (i j : ℕ) {d lam : ℝ} (hld : lam ≤ d) :
    Measurable fun s => Psi A B C i j d lam s := by
  have hs := (measurable_ff A B C i j).stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (Ioc lam d))
  have e : (fun s => Psi A B C i j d lam s) = fun s : ℝ =>
      ∫ t, (fun p : ℝ × ℝ => ff A B C i j p.1 p.2) (s, t) ∂(volume.restrict (Ioc lam d)) := by
    funext s; unfold Psi; rw [intervalIntegral.integral_of_le hld]
  rw [e]
  exact hs.measurable

theorem PD.intervalIntegrable_Psi (h : PD A B C m K) (i j : ℕ) {b d lam : ℝ} (hb : 0 < b)
    (hd : 0 < d) (hl0 : 0 ≤ lam) (hld : lam ≤ d) :
    IntervalIntegrable (fun s => Psi A B C i j d lam s) volume 0 b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hb.le]
  refine Integrable.mono' (g := fun _ => b ^ i * d ^ j * (cc m K b d * d + Lam d))
    (integrableOn_const (by simp)) (measurable_Psi A B C i j hld).aestronglyMeasurable ?_
  exact (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall (fun s hs =>
    h.psi_bound i j hd hl0 hld hs.1 hs.2))

end CatalanCore.Uniform.Decay.Assembly
