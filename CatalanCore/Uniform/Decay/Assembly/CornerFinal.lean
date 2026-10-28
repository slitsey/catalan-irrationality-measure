module

public import CatalanCore.Uniform.Decay.Assembly.CornerMain

@[expose] public section

/-!
# Singular-corner boundary energy, part 4: assembly

`boundary_energy_corner`: the boundary-energy identity on a rectangle `[0,b] × [0,d]` having the
singular corner `(0,0)` of a positive definite form as a vertex.  The same statement for the
other three corner orientations follows by the reflections `s ↦ -s`, `t ↦ -t`
(which change the sign of `B` and the parity of the monomials).
-/

namespace CatalanCore.Uniform.Decay.Assembly

open Set intervalIntegral MeasureTheory Filter Topology
open CatalanCore.Uniform.Decay.Tools

variable {A B C m K : ℝ}

theorem tendsto_R1a (h : PD A B C m K) (i j : ℕ) {b d : ℝ} (hb : 0 < b) (hd : 0 < d) :
    Tendsto (fun ε : ℝ => ∫ t in ε..d, b ^ (i + 1) * t ^ j * Lq A B C b t) (𝓝[>] 0)
      (𝓝 (∫ t in (0 : ℝ)..d, b ^ (i + 1) * t ^ j * Lq A B C b t)) := by
  refine tendsto_lower hd ?_
  exact ((continuous_const.mul (continuous_id.pow j)).mul
    (h.continuous_Lq_t hb.ne')).intervalIntegrable _ _

theorem tendsto_R2a (h : PD A B C m K) (i j : ℕ) {b d : ℝ} (hb : 0 < b) (hd : 0 < d) :
    Tendsto (fun ε : ℝ => ∫ s in ε..b, s ^ i * d ^ (j + 1) * Lq A B C s d) (𝓝[>] 0)
      (𝓝 (∫ s in (0 : ℝ)..b, s ^ i * d ^ (j + 1) * Lq A B C s d)) := by
  refine tendsto_lower hb ?_
  exact (((continuous_id.pow i).mul continuous_const).mul
    (h.continuous_Lq_s hd.ne')).intervalIntegrable _ _

/-- **Boundary-energy identity at a singular corner.** -/
theorem boundary_energy_corner (h : PD A B C m K) (i j : ℕ) {b d : ℝ} (hb : 0 < b) (hd : 0 < d) :
    ((i : ℝ) + j + 2) * ∫ s in (0 : ℝ)..b, ∫ t in (0 : ℝ)..d, s ^ i * t ^ j * Lq A B C s t
      = (∫ t in (0 : ℝ)..d, (b ^ (i + 1) * t ^ j * Lq A B C b t
            - (0 : ℝ) ^ (i + 1) * t ^ j * Lq A B C 0 t))
        + (∫ s in (0 : ℝ)..b, (s ^ i * d ^ (j + 1) * Lq A B C s d
            - s ^ i * (0 : ℝ) ^ (j + 1) * Lq A B C s 0))
        - (b ^ (i + 1) - (0 : ℝ) ^ (i + 1)) * (d ^ (j + 1) - (0 : ℝ) ^ (j + 1))
            / (((i : ℝ) + 1) * ((j : ℝ) + 1)) := by
  -- the five limits
  have tG := (tendsto_G h i j hb hd).const_mul ((i : ℝ) + j + 2)
  have t1a := tendsto_R1a h i j hb hd
  have t1b := edge_vanish h i j hd
  have t2a := tendsto_R2a h i j hb hd
  have t2b : Tendsto (fun ε : ℝ => ε ^ (j + 1) * ∫ s in ε..b, s ^ i * Lq A B C s ε) (𝓝[>] 0)
      (𝓝 0) := by
    have := edge_vanish h.swap j i hb
    refine this.congr (fun ε => ?_)
    congr 2
    funext s
    rw [Lq_comm A B C s ε]
  have t3 : Tendsto (fun ε : ℝ => (b ^ (i + 1) - ε ^ (i + 1)) * (d ^ (j + 1) - ε ^ (j + 1))
      / (((i : ℝ) + 1) * ((j : ℝ) + 1))) (𝓝[>] 0)
      (𝓝 ((b ^ (i + 1) - (0 : ℝ) ^ (i + 1)) * (d ^ (j + 1) - (0 : ℝ) ^ (j + 1))
        / (((i : ℝ) + 1) * ((j : ℝ) + 1)))) := by
    have hc : Continuous fun ε : ℝ => (b ^ (i + 1) - ε ^ (i + 1)) * (d ^ (j + 1) - ε ^ (j + 1))
        / (((i : ℝ) + 1) * ((j : ℝ) + 1)) :=
      ((continuous_const.sub (continuous_id.pow _)).mul
        (continuous_const.sub (continuous_id.pow _))).div_const _
    exact (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have tR := ((t1a.sub t1b).add (t2a.sub t2b)).sub t3
  -- the identity holds for small ε
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ∈ Ioo (0 : ℝ) (min b d) :=
    Ioo_mem_nhdsGT (lt_min hb hd)
  have hid : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ((i : ℝ) + j + 2) * ∫ s in ε..b, ∫ t in ε..d, s ^ i * t ^ j * Lq A B C s t
        = ((∫ t in ε..d, b ^ (i + 1) * t ^ j * Lq A B C b t)
            - ε ^ (i + 1) * ∫ t in ε..d, t ^ j * Lq A B C ε t)
          + ((∫ s in ε..b, s ^ i * d ^ (j + 1) * Lq A B C s d)
            - ε ^ (j + 1) * ∫ s in ε..b, s ^ i * Lq A B C s ε)
          - (b ^ (i + 1) - ε ^ (i + 1)) * (d ^ (j + 1) - ε ^ (j + 1))
              / (((i : ℝ) + 1) * ((j : ℝ) + 1)) := by
    filter_upwards [hev] with ε hε
    obtain ⟨hε0, hε1⟩ := hε
    have hεb : ε < b := lt_of_lt_of_le hε1 (min_le_left _ _)
    have hεd : ε < d := lt_of_lt_of_le hε1 (min_le_right _ _)
    have hpos : ∀ s ∈ Icc ε b, ∀ t ∈ Icc ε d, 0 < qf A B C s t := fun s hs t _ =>
      h.qf_pos (Or.inl (lt_of_lt_of_le hε0 hs.1).ne')
    have key := boundary_energy_identity A B C i j hεb.le hεd.le hpos
    rw [key]
    -- split the two single integrals
    have c1 : Continuous fun t : ℝ => b ^ (i + 1) * t ^ j * Lq A B C b t :=
      (continuous_const.mul (continuous_id.pow j)).mul (h.continuous_Lq_t hb.ne')
    have c2 : Continuous fun t : ℝ => t ^ j * Lq A B C ε t :=
      (continuous_id.pow j).mul (h.continuous_Lq_t hε0.ne')
    have c3 : Continuous fun s : ℝ => s ^ i * d ^ (j + 1) * Lq A B C s d :=
      ((continuous_id.pow i).mul continuous_const).mul (h.continuous_Lq_s hd.ne')
    have c4 : Continuous fun s : ℝ => s ^ i * Lq A B C s ε :=
      (continuous_id.pow i).mul (h.continuous_Lq_s hε0.ne')
    have e1 : ∫ t in ε..d, (b ^ (i + 1) * t ^ j * Lq A B C b t
          - ε ^ (i + 1) * t ^ j * Lq A B C ε t)
        = (∫ t in ε..d, b ^ (i + 1) * t ^ j * Lq A B C b t)
          - ε ^ (i + 1) * ∫ t in ε..d, t ^ j * Lq A B C ε t := by
      have hv : (fun t : ℝ => ε ^ (i + 1) * t ^ j * Lq A B C ε t)
          = fun t => ε ^ (i + 1) * (t ^ j * Lq A B C ε t) := by funext t; ring
      rw [intervalIntegral.integral_sub (c1.intervalIntegrable _ _)
        (by rw [hv]; exact (continuous_const.mul c2).intervalIntegrable _ _), hv,
        intervalIntegral.integral_const_mul]
    have e2 : ∫ s in ε..b, (s ^ i * d ^ (j + 1) * Lq A B C s d
          - s ^ i * ε ^ (j + 1) * Lq A B C s ε)
        = (∫ s in ε..b, s ^ i * d ^ (j + 1) * Lq A B C s d)
          - ε ^ (j + 1) * ∫ s in ε..b, s ^ i * Lq A B C s ε := by
      have hv : (fun s : ℝ => s ^ i * ε ^ (j + 1) * Lq A B C s ε)
          = fun s => ε ^ (j + 1) * (s ^ i * Lq A B C s ε) := by funext s; ring
      rw [intervalIntegral.integral_sub (c3.intervalIntegrable _ _)
        (by rw [hv]; exact (continuous_const.mul c4).intervalIntegrable _ _), hv,
        intervalIntegral.integral_const_mul]
    rw [e1, e2]
  -- limit identification
  have hlim := tR.congr' (hid.mono fun ε hε => hε.symm)
  have := tendsto_nhds_unique tG hlim
  rw [this]
  simp only [zero_mul, mul_zero, sub_zero]
  have e0 : ∀ t : ℝ, (0 : ℝ) ^ (i + 1) = 0 := fun _ => zero_pow (Nat.succ_ne_zero i)
  have e0' : (0 : ℝ) ^ (j + 1) = 0 := zero_pow (Nat.succ_ne_zero j)
  simp [e0', zero_pow (Nat.succ_ne_zero i)]

end CatalanCore.Uniform.Decay.Assembly
