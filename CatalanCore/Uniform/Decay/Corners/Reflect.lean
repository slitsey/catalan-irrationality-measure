module

public import CatalanCore.Uniform.Decay.Assembly.CornerPD

@[expose] public section

/-!
# Boundary-energy statement `BE` and the two axis reflections

`BE A B C i j a b c d` is the boundary-energy identity of `Tools.boundary_energy_identity` on
`[a,b] × [c,d]`.  The reflections `s ↦ -s` and `t ↦ -t` send `B ↦ -B`, move the rectangle and
multiply both sides of the identity by `(-1)^i` (resp. `(-1)^j`).
-/

namespace CatalanCore.Uniform.Decay.Corners

open Set intervalIntegral MeasureTheory
open CatalanCore.Uniform.Decay.Tools CatalanCore.Uniform.Decay.Assembly

/-- Double integral. -/
noncomputable def BEL (A B C : ℝ) (i j : ℕ) (a b c d : ℝ) : ℝ :=
  ∫ s in a..b, ∫ t in c..d, s ^ i * t ^ j * Lq A B C s t

/-- Boundary terms and polynomial moment. -/
noncomputable def BER (A B C : ℝ) (i j : ℕ) (a b c d : ℝ) : ℝ :=
  (∫ t in c..d, (b ^ (i + 1) * t ^ j * Lq A B C b t - a ^ (i + 1) * t ^ j * Lq A B C a t))
    + (∫ s in a..b, (s ^ i * d ^ (j + 1) * Lq A B C s d - s ^ i * c ^ (j + 1) * Lq A B C s c))
    - (b ^ (i + 1) - a ^ (i + 1)) * (d ^ (j + 1) - c ^ (j + 1)) / (((i : ℝ) + 1) * ((j : ℝ) + 1))

/-- The boundary-energy identity on `[a,b] × [c,d]`. -/
def BE (A B C : ℝ) (i j : ℕ) (a b c d : ℝ) : Prop :=
  ((i : ℝ) + j + 2) * BEL A B C i j a b c d = BER A B C i j a b c d

theorem Lq_negS (A B C s t : ℝ) : Lq A B C (-s) t = Lq A (-B) C s t := by
  unfold Lq qf; congr 2; ring

theorem Lq_negT (A B C s t : ℝ) : Lq A B C s (-t) = Lq A (-B) C s t := by
  unfold Lq qf; congr 2; ring

theorem Lq_negS' (A B C s t : ℝ) : Lq A (-B) C (-s) t = Lq A B C s t := by
  unfold Lq qf; congr 2; ring

theorem Lq_negT' (A B C s t : ℝ) : Lq A (-B) C s (-t) = Lq A B C s t := by
  unfold Lq qf; congr 2; ring

theorem _root_.CatalanCore.Uniform.Decay.Assembly.PD.neg {A B C m K : ℝ} (h : PD A B C m K) : PD A (-B) C m K where
  m_pos := h.m_pos
  lower s t := by
    have := h.lower (-s) t
    rw [show qf A B C (-s) t = qf A (-B) C s t by unfold qf; ring] at this
    simpa using this
  upper s t := by
    have := h.upper (-s) t
    rw [show qf A B C (-s) t = qf A (-B) C s t by unfold qf; ring] at this
    simpa using this

theorem BEL_negS (A B C : ℝ) (i j : ℕ) (a b c d : ℝ) :
    BEL A (-B) C i j (-b) (-a) c d = (-1) ^ i * BEL A B C i j a b c d := by
  unfold BEL
  rw [← intervalIntegral.integral_comp_neg (f := fun s => ∫ t in c..d, s ^ i * t ^ j * Lq A (-B) C s t),
    ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun s _ => ?_
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun t _ => ?_
  rw [← Lq_negS]; simp only [neg_neg]; ring_nf

theorem BER_negS (A B C : ℝ) (i j : ℕ) (a b c d : ℝ) :
    BER A (-B) C i j (-b) (-a) c d = (-1) ^ i * BER A B C i j a b c d := by
  unfold BER
  have e1 : (∫ t in c..d, ((-a) ^ (i + 1) * t ^ j * Lq A (-B) C (-a) t
      - (-b) ^ (i + 1) * t ^ j * Lq A (-B) C (-b) t))
      = (-1) ^ i * ∫ t in c..d, (b ^ (i + 1) * t ^ j * Lq A B C b t
        - a ^ (i + 1) * t ^ j * Lq A B C a t) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t _ => ?_
    rw [Lq_negS' A B C a t, Lq_negS' A B C b t]
    rw [show (-a) ^ (i + 1) = (-1) ^ i * (-(a ^ (i + 1))) by rw [neg_pow, pow_succ]; ring,
      show (-b) ^ (i + 1) = (-1) ^ i * (-(b ^ (i + 1))) by rw [neg_pow, pow_succ]; ring]
    ring
  have e2 : (∫ s in -b..-a, (s ^ i * d ^ (j + 1) * Lq A (-B) C s d
      - s ^ i * c ^ (j + 1) * Lq A (-B) C s c))
      = (-1) ^ i * ∫ s in a..b, (s ^ i * d ^ (j + 1) * Lq A B C s d
        - s ^ i * c ^ (j + 1) * Lq A B C s c) := by
    rw [← intervalIntegral.integral_comp_neg (f := fun s => s ^ i * d ^ (j + 1) * Lq A (-B) C s d
      - s ^ i * c ^ (j + 1) * Lq A (-B) C s c), ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun s _ => ?_
    rw [Lq_negS' A B C s d, Lq_negS' A B C s c]
    rw [neg_pow]; ring
  rw [e1, e2]
  rw [show (-a) ^ (i + 1) = (-1) ^ i * (-(a ^ (i + 1))) by rw [neg_pow, pow_succ]; ring,
      show (-b) ^ (i + 1) = (-1) ^ i * (-(b ^ (i + 1))) by rw [neg_pow, pow_succ]; ring]
  ring

theorem BE_negS_iff (A B C : ℝ) (i j : ℕ) (a b c d : ℝ) :
    BE A (-B) C i j (-b) (-a) c d ↔ BE A B C i j a b c d := by
  unfold BE
  rw [BEL_negS, BER_negS]
  constructor
  · intro h
    have h0 : ((-1 : ℝ) ^ i) ≠ 0 := pow_ne_zero _ (by norm_num)
    apply mul_left_cancel₀ h0
    linear_combination h
  · intro h
    linear_combination (-1 : ℝ) ^ i * h

theorem BEL_negT (A B C : ℝ) (i j : ℕ) (a b c d : ℝ) :
    BEL A (-B) C i j a b (-d) (-c) = (-1) ^ j * BEL A B C i j a b c d := by
  unfold BEL
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun s _ => ?_
  rw [← intervalIntegral.integral_comp_neg (f := fun t => s ^ i * t ^ j * Lq A (-B) C s t),
    ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun t _ => ?_
  rw [Lq_negT' A B C s t, neg_pow]; ring

theorem BER_negT (A B C : ℝ) (i j : ℕ) (a b c d : ℝ) :
    BER A (-B) C i j a b (-d) (-c) = (-1) ^ j * BER A B C i j a b c d := by
  unfold BER
  have e1 : (∫ t in -d..-c, (b ^ (i + 1) * t ^ j * Lq A (-B) C b t
      - a ^ (i + 1) * t ^ j * Lq A (-B) C a t))
      = (-1) ^ j * ∫ t in c..d, (b ^ (i + 1) * t ^ j * Lq A B C b t
        - a ^ (i + 1) * t ^ j * Lq A B C a t) := by
    rw [← intervalIntegral.integral_comp_neg (f := fun t => b ^ (i + 1) * t ^ j * Lq A (-B) C b t
      - a ^ (i + 1) * t ^ j * Lq A (-B) C a t), ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t _ => ?_
    rw [Lq_negT' A B C b t, Lq_negT' A B C a t]
    rw [neg_pow]; ring
  have e2 : (∫ s in a..b, (s ^ i * (-c) ^ (j + 1) * Lq A (-B) C s (-c)
      - s ^ i * (-d) ^ (j + 1) * Lq A (-B) C s (-d)))
      = (-1) ^ j * ∫ s in a..b, (s ^ i * d ^ (j + 1) * Lq A B C s d
        - s ^ i * c ^ (j + 1) * Lq A B C s c) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun s _ => ?_
    rw [Lq_negT' A B C s c, Lq_negT' A B C s d]
    rw [show (-c) ^ (j + 1) = (-1) ^ j * (-(c ^ (j + 1))) by rw [neg_pow, pow_succ]; ring,
      show (-d) ^ (j + 1) = (-1) ^ j * (-(d ^ (j + 1))) by rw [neg_pow, pow_succ]; ring]
    ring
  rw [e1, e2]
  rw [show (-c) ^ (j + 1) = (-1) ^ j * (-(c ^ (j + 1))) by rw [neg_pow, pow_succ]; ring,
      show (-d) ^ (j + 1) = (-1) ^ j * (-(d ^ (j + 1))) by rw [neg_pow, pow_succ]; ring]
  ring

theorem BE_negT_iff (A B C : ℝ) (i j : ℕ) (a b c d : ℝ) :
    BE A (-B) C i j a b (-d) (-c) ↔ BE A B C i j a b c d := by
  unfold BE
  rw [BEL_negT, BER_negT]
  constructor
  · intro h
    have h0 : ((-1 : ℝ) ^ j) ≠ 0 := pow_ne_zero _ (by norm_num)
    apply mul_left_cancel₀ h0
    linear_combination h
  · intro h
    linear_combination (-1 : ℝ) ^ j * h

end CatalanCore.Uniform.Decay.Corners
