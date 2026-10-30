module

public import CatalanCore.Uniform.Decay.FarField.Expand

@[expose] public section
set_option Elab.async false

/-!
# Far-field expansion of a weighted list of segments (lane D, package D15)

`MPData` is the global data of a far-field check: the centre `c`, the radius `R` of the support
about `c`, the truncation orders `J ≤ K`, a bound `Aabs` for the total variation, and the claimed
moments `mu = momList ps c K`.  `mpGlobalOk` verifies all global hypotheses once;
`agg_far` is the aggregated expansion
`-∑ w_P Φ_P(z) = Re ∑_{k=1}^K μ_k / (k (z-c)^k) + error`, `|error| ≤ Aabs ρ^(K+1)/((K+1)(1-ρ))`,
valid when the total weighted mass vanishes.
-/

namespace CatalanCore.Uniform.Decay.FarField

open Finset CatalanCore.Uniform.Decay.Tools CatalanCore.Uniform.Decay.Spline
  CatalanCore.Uniform.Decay.NearCells

structure MPData where
  c : CQ
  R : ℚ
  K : ℕ
  J : ℕ
  Aabs : ℚ
  mu : List CQ

def cqKey (z : CQ) : ℚ × ℚ := (z.re, z.im)

theorem cqKey_inj : Function.Injective cqKey := by
  intro a b h
  cases a; cases b
  simp only [cqKey, Prod.mk.injEq] at h
  rw [h.1, h.2]

/-- All global hypotheses of the far-field lemma, checked once per bank. -/
def mpGlobalOk (ps : List WP) (M : MPData) : Bool :=
  decide (0 ≤ M.R) && decide (M.J ≤ M.K) &&
    decide (M.mu.map cqKey = (momList ps M.c M.K).map cqKey) &&
    decide ((ps.map fun P => P.w * Tm P.a 0).sum = 0) &&
    decide ((ps.map fun P => |P.w| * absM P.a).sum ≤ M.Aabs) &&
    ps.all fun P => decide ((CQ.sub P.A M.c).nsq ≤ M.R ^ 2) && decide ((CQ.sub P.B M.c).nsq ≤ M.R ^ 2)

theorem mpGlobalOk_sound {ps : List WP} {M : MPData} (h : mpGlobalOk ps M = true) :
    0 ≤ M.R ∧ M.J ≤ M.K ∧ M.mu = momList ps M.c M.K ∧
    (ps.map fun P => P.w * Tm P.a 0).sum = 0 ∧
    (ps.map fun P => |P.w| * absM P.a).sum ≤ M.Aabs ∧
    ∀ P ∈ ps, (CQ.sub P.A M.c).nsq ≤ M.R ^ 2 ∧ (CQ.sub P.B M.c).nsq ≤ M.R ^ 2 := by
  simp only [mpGlobalOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, List.map_injective_iff.2 cqKey_inj h3, h4, h5, h6⟩

theorem norm_le_of_nsq_sq {q : CQ} {r : ℚ} (hr : 0 ≤ r) (h : q.nsq ≤ r ^ 2) : ‖q.toC‖ ≤ (r : ℝ) := by
  have h' : (q.nsq : ℝ) ≤ (r : ℝ) ^ 2 := by exact_mod_cast h
  have hn : ‖q.toC‖ ^ 2 = (q.nsq : ℝ) := by rw [Complex.sq_norm, ← CQ.nsq_cast]
  have hr' : (0 : ℝ) ≤ r := by exact_mod_cast hr
  by_contra hc
  push_neg at hc
  nlinarith [norm_nonneg q.toC]

/-- The error of the expansion, for a list of pieces. -/
theorem list_far (c z : ℂ) (R r0 : ℝ) (K : ℕ) (hR0 : 0 ≤ R) (hRr : R < r0) (hz : r0 ≤ ‖z - c‖) :
    ∀ ps : List WP, (∀ P ∈ ps, ‖P.A.toC - c‖ ≤ R ∧ ‖P.B.toC - c‖ ≤ R) →
    |(-(ps.map fun P => (P.w : ℝ) * PhiW P z).sum)
        - (-(Real.log ‖z - c‖) * (ps.map fun P => (P.w : ℝ) * (Tm P.a 0 : ℝ)).sum
          + (∑ k ∈ range K, (ps.map fun P => (P.w : ℂ) * momSem P c (k + 1)).sum
              / (((k + 1 : ℕ) : ℂ) * (z - c) ^ (k + 1))).re)|
      ≤ (ps.map fun P => |(P.w : ℝ)| * (absM P.a : ℝ)).sum * ((R / r0) ^ (K + 1) / ((K + 1) * (1 - R / r0)))
  | [], _ => by simp
  | P :: ps, hps => by
    have ih := list_far c z R r0 K hR0 hRr hz ps (fun Q hQ => hps Q (List.mem_cons_of_mem _ hQ))
    have hP := phiW_far P c z R r0 (hps P (List.mem_cons_self ..)).1 (hps P (List.mem_cons_self ..)).2
      hR0 hRr hz K
    set L := Real.log ‖z - c‖
    set X := (∑ k ∈ range K, momSem P c (k + 1) / (((k + 1 : ℕ) : ℂ) * (z - c) ^ (k + 1))).re with hX
    set Y := (∑ k ∈ range K, (ps.map fun P => (P.w : ℂ) * momSem P c (k + 1)).sum
              / (((k + 1 : ℕ) : ℂ) * (z - c) ^ (k + 1))).re with hY
    have hsplit : (∑ k ∈ range K, ((P :: ps).map fun P => (P.w : ℂ) * momSem P c (k + 1)).sum
              / (((k + 1 : ℕ) : ℂ) * (z - c) ^ (k + 1))).re
        = (P.w : ℝ) * X + Y := by
      rw [hX, hY]
      have : ∀ k ∈ range K, ((P :: ps).map fun P => (P.w : ℂ) * momSem P c (k + 1)).sum
              / (((k + 1 : ℕ) : ℂ) * (z - c) ^ (k + 1))
          = (P.w : ℂ) * (momSem P c (k + 1) / (((k + 1 : ℕ) : ℂ) * (z - c) ^ (k + 1)))
            + (ps.map fun P => (P.w : ℂ) * momSem P c (k + 1)).sum
              / (((k + 1 : ℕ) : ℂ) * (z - c) ^ (k + 1)) := by
        intro k _
        simp only [List.map_cons, List.sum_cons]
        ring
      have hw : (P.w : ℂ) = ((P.w : ℝ) : ℂ) := by simp
      rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, ← Finset.mul_sum, Complex.add_re, hw,
        Complex.re_ofReal_mul]
    rw [hsplit]
    simp only [List.map_cons, List.sum_cons]
    have e : -((P.w : ℝ) * PhiW P z + (ps.map fun P => (P.w : ℝ) * PhiW P z).sum)
        - (-L * ((P.w : ℝ) * (Tm P.a 0 : ℝ) + (ps.map fun P => (P.w : ℝ) * (Tm P.a 0 : ℝ)).sum)
          + ((P.w : ℝ) * X + Y))
        = -((P.w : ℝ) * (PhiW P z - ((Tm P.a 0 : ℝ) * L - X)))
          + ((-(ps.map fun P => (P.w : ℝ) * PhiW P z).sum)
            - (-L * (ps.map fun P => (P.w : ℝ) * (Tm P.a 0 : ℝ)).sum + Y)) := by ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    rw [abs_neg, abs_mul]
    have := mul_le_mul_of_nonneg_left hP (abs_nonneg (P.w : ℝ))
    nlinarith [this, ih]

/-- **Aggregated far-field expansion.** -/
theorem agg_far {ps : List WP} {M : MPData} (hG : mpGlobalOk ps M = true) (z : ℂ) (r0 : ℝ)
    (hRr : (M.R : ℝ) < r0) (hz : r0 ≤ ‖z - M.c.toC‖) :
    |(-(ps.map fun P => (P.w : ℝ) * PhiW P z).sum)
        - (∑ k ∈ range M.K, (M.mu.getD k CQ.zero).toC / (((k + 1 : ℕ) : ℂ) * (z - M.c.toC) ^ (k + 1))).re|
      ≤ (M.Aabs : ℝ) * (((M.R : ℝ) / r0) ^ (M.K + 1) / ((M.K + 1) * (1 - (M.R : ℝ) / r0))) := by
  obtain ⟨hR, hJK, hmu, hmass, hAabs, hP⟩ := mpGlobalOk_sound hG
  have hR' : (0 : ℝ) ≤ M.R := by exact_mod_cast hR
  have hPn : ∀ P ∈ ps, ‖P.A.toC - M.c.toC‖ ≤ (M.R : ℝ) ∧ ‖P.B.toC - M.c.toC‖ ≤ (M.R : ℝ) := by
    intro P hPm
    have := hP P hPm
    rw [← CQ.toC_sub, ← CQ.toC_sub]
    exact ⟨norm_le_of_nsq_sq hR this.1, norm_le_of_nsq_sq hR this.2⟩
  have key := list_far M.c.toC z (M.R : ℝ) r0 M.K hR' hRr hz ps hPn
  have hcast : ∀ ps' : List WP, (((ps'.map fun P => P.w * Tm P.a 0).sum : ℚ) : ℝ)
      = (ps'.map fun P => (P.w : ℝ) * (Tm P.a 0 : ℝ)).sum := by
    intro ps'
    induction ps' with
    | nil => simp
    | cons P ps' ih => simp only [List.map_cons, List.sum_cons, Rat.cast_add, Rat.cast_mul, Rat.cast_abs, ih]
  have hcast2 : ∀ ps' : List WP, (((ps'.map fun P => |P.w| * absM P.a).sum : ℚ) : ℝ)
      = (ps'.map fun P => |(P.w : ℝ)| * (absM P.a : ℝ)).sum := by
    intro ps'
    induction ps' with
    | nil => simp
    | cons P ps' ih => simp only [List.map_cons, List.sum_cons, Rat.cast_add, Rat.cast_mul, Rat.cast_abs, ih]
  have hm0 : (ps.map fun P => (P.w : ℝ) * (Tm P.a 0 : ℝ)).sum = 0 := by
    rw [← hcast, hmass]; simp
  have hA : (ps.map fun P => |(P.w : ℝ)| * (absM P.a : ℝ)).sum ≤ (M.Aabs : ℝ) := by
    rw [← hcast2]; exact_mod_cast hAabs
  have hmuk : ∀ k ∈ range M.K, (M.mu.getD k CQ.zero).toC
      = (ps.map fun P => (P.w : ℂ) * momSem P M.c.toC (k + 1)).sum := by
    intro k hk
    rw [hmu]
    exact momList_getD ps M.c M.K k (Finset.mem_range.1 hk)
  have hsum : (∑ k ∈ range M.K, (M.mu.getD k CQ.zero).toC / (((k + 1 : ℕ) : ℂ) * (z - M.c.toC) ^ (k + 1)))
      = ∑ k ∈ range M.K, (ps.map fun P => (P.w : ℂ) * momSem P M.c.toC (k + 1)).sum
          / (((k + 1 : ℕ) : ℂ) * (z - M.c.toC) ^ (k + 1)) :=
    Finset.sum_congr rfl fun k hk => by rw [hmuk k hk]
  rw [hsum]
  rw [hm0] at key
  have hr0 : 0 < r0 := by linarith
  have hρ : (M.R : ℝ) / r0 < 1 := by rw [div_lt_one hr0]; exact hRr
  have hnn : 0 ≤ ((M.R : ℝ) / r0) ^ (M.K + 1) / ((M.K + 1) * (1 - (M.R : ℝ) / r0)) := by
    have : 0 < 1 - (M.R : ℝ) / r0 := by linarith
    have h0 : 0 ≤ (M.R : ℝ) / r0 := div_nonneg hR' hr0.le
    positivity
  refine le_trans ?_ (mul_le_mul_of_nonneg_right hA hnn)
  simpa using key

end CatalanCore.Uniform.Decay.FarField
