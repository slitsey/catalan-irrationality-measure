module

public import CatalanCore.Zeta5.Sum.PrimeSums
public import CatalanCore.Zeta5.Sum.OuterBridge

@[expose] public section

/-!
# ZC28 for the profile functions: `Σ_p p H(R/p) log p / R² → ∫ H x⁻³`

The profiles `R`, `g_ref`, `x T₀(1/x)` are piecewise affine on the cells of a cut list passing the
rational tests (`okChain`). On such a cut list `l, ts`, the inner/outer prime sums of ZC32 converge:

`R⁻² Σ_{R/e < p ≤ R/l} p H(R/p) log p → ∫_l^e H(x) x⁻³ dx`, `e = endpt l ts`,

because `θ ↦ θ H(1/θ)` is piecewise affine in `θ` on the cells `(1/rᵢ₊₁, 1/rᵢ)` and
`weighted_prime_sum_tendsto` applies (ZC28), followed by the substitution `θ = 1/x`.
-/

open Filter Set MeasureTheory
open scoped Topology

set_option linter.deprecated false

namespace CatalanCore.Zeta5.Sum

open CatalanCore.Zeta5.Profile OAI.Zeta5.Workers.W14

lemma PiecewiseCont.snoc {F : ℝ → ℝ} {c : ℕ → ℝ} {n : ℕ} (h : PiecewiseCont F c n) {d : ℝ}
    (hlt : c n < d) {G : ℝ → ℝ} (hG : ContinuousOn G (Icc (c n) d))
    (hFG : ∀ x ∈ Ioo (c n) d, F x = G x) :
    PiecewiseCont F (fun i => if i ≤ n then c i else d) (n + 1) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · by_cases hin : i < n
    · simp only [if_pos hin.le, if_pos (Nat.succ_le_of_lt hin)]
      exact h1 i hin
    · have : i = n := by omega
      subst this
      simp only [if_pos le_rfl, if_neg (Nat.not_succ_le_self i)]
      exact hlt
  · by_cases hin : i < n
    · obtain ⟨G', hG', hFG'⟩ := h2 i hin
      refine ⟨G', ?_, ?_⟩
      · simp only [if_pos hin.le, if_pos (Nat.succ_le_of_lt hin)]; exact hG'
      · simp only [if_pos hin.le, if_pos (Nat.succ_le_of_lt hin)]; exact hFG'
    · have : i = n := by omega
      subst this
      refine ⟨G, ?_, ?_⟩
      · simp only [if_pos le_rfl, if_neg (Nat.not_succ_le_self i)]; exact hG
      · simp only [if_pos le_rfl, if_neg (Nat.not_succ_le_self i)]; exact hFG

lemma endpt_ge : ∀ (ts : List ℚ) (l : ℚ) (P : ℚ → ℚ → Prop),
    okChain P l ts → l ≤ endpt l ts := by
  intro ts
  induction ts with
  | nil => intro l P _; simp [endpt]
  | cons r t ih =>
    intro l P h
    obtain ⟨hlr, _, hrest⟩ := h
    simp only [endpt]
    exact hlr.le.trans (ih r P hrest)

lemma exists_pc_of_okChain {H : ℝ → ℝ} : ∀ (ts : List ℚ) (l : ℚ), 0 < l →
    okChain (fun l r => ∃ A B : ℝ, ∀ t ∈ Ioo (l : ℝ) r, H t = A * t + B) l ts →
    ∃ (c : ℕ → ℝ) (n : ℕ), PiecewiseCont (fun θ => θ * H (1 / θ)) c n ∧
      c 0 = 1 / ((endpt l ts : ℚ) : ℝ) ∧ c n = 1 / (l : ℝ) := by
  intro ts
  induction ts with
  | nil =>
    intro l _ _
    exact ⟨fun _ => 1 / (l : ℝ), 0, ⟨fun i hi => absurd hi (by omega),
      fun i hi => absurd hi (by omega)⟩, by simp [endpt], rfl⟩
  | cons r t ih =>
    intro l hl hok
    obtain ⟨hlr, ⟨A, B, hAB⟩, hrest⟩ := hok
    have hr : 0 < r := lt_trans hl hlr
    obtain ⟨c, n, hpc, h0, hn⟩ := ih r hr hrest
    have hlr' : (l : ℝ) < r := by exact_mod_cast hlr
    have hl' : (0 : ℝ) < l := by exact_mod_cast hl
    have hr' : (0 : ℝ) < r := by exact_mod_cast hr
    have hlt : c n < 1 / (l : ℝ) := by
      rw [hn]
      exact one_div_lt_one_div_of_lt hl' hlr'
    have hcell : ∀ θ ∈ Ioo (c n) (1 / (l : ℝ)), θ * H (1 / θ) = A + B * θ := by
      intro θ hθ
      rw [hn] at hθ
      have hθ0 : 0 < θ := lt_trans (by positivity) hθ.1
      have hx : 1 / θ ∈ Ioo (l : ℝ) r := by
        constructor
        · rw [lt_div_iff₀ hθ0]
          have := hθ.2
          rw [lt_div_iff₀ hl'] at this
          linarith
        · rw [div_lt_iff₀ hθ0]
          have := hθ.1
          rw [div_lt_iff₀ hr'] at this
          linarith
      rw [hAB _ hx]
      field_simp
    refine ⟨_, n + 1, PiecewiseCont.snoc hpc hlt (G := fun θ => A + B * θ)
      (by fun_prop) hcell, ?_, ?_⟩
    · simp only [if_pos (Nat.zero_le n)]
      rw [h0]; simp [endpt]
    · simp only [if_neg (Nat.not_succ_le_self n)]

/-- **ZC28 for a piecewise affine profile.** On a cut list passing the affine test
(`okChain`), `R⁻² Σ_{R/e < p ≤ R/l} p H(R/p) log p → ∫_l^e H(x) x⁻³ dx`. -/
theorem prime_sum_okChain {H : ℝ → ℝ} {ts : List ℚ} {l : ℚ} (hl : 0 < l)
    (hok : okChain (fun l r => ∃ A B : ℝ, ∀ t ∈ Ioo (l : ℝ) r, H t = A * t + B) l ts) :
    Tendsto (fun R : ℝ =>
      (∑ p ∈ Finset.Ioc ⌊R / ((endpt l ts : ℚ) : ℝ)⌋₊ ⌊R / (l : ℝ)⌋₊ with p.Prime,
        (p : ℝ) * H (R / p) * Real.log (p : ℝ)) / R ^ 2)
      atTop (𝓝 (∫ x in (l : ℝ)..((endpt l ts : ℚ) : ℝ), H x / x ^ 3)) := by
  obtain ⟨c, n, hpc, h0, hn⟩ := exists_pc_of_okChain ts l hl hok
  have hl' : (0 : ℝ) < l := by exact_mod_cast hl
  have hge : (l : ℝ) ≤ ((endpt l ts : ℚ) : ℝ) := by
    exact_mod_cast endpt_ge ts l _ hok
  have he0 : (0 : ℝ) < ((endpt l ts : ℚ) : ℝ) := lt_of_lt_of_le hl' hge
  have hc0 : 0 < c 0 := by rw [h0]; positivity
  have hT := (weighted_prime_sum_tendsto hc0 hpc).2
  rw [h0, hn] at hT
  have hint : (∫ θ in (1 / ((endpt l ts : ℚ) : ℝ))..(1 / (l : ℝ)), θ * H (1 / θ))
      = ∫ x in (l : ℝ)..((endpt l ts : ℚ) : ℝ), H x / x ^ 3 := by
    rw [← integral_inv_comp (fun θ => θ * H (1 / θ)) hl' hge]
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le hge] at hx
    have hx0 : 0 < x := lt_of_lt_of_le hl' hx.1
    simp only [one_div, inv_inv]
    field_simp
  rw [hint] at hT
  refine hT.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  unfold weightedPrimeIntervalSum
  have e1 : (1 / ((endpt l ts : ℚ) : ℝ)) * R = R / ((endpt l ts : ℚ) : ℝ) := by ring
  have e2 : (1 / (l : ℝ)) * R = R / (l : ℝ) := by ring
  rw [e1, e2, Finset.sum_div, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro p hp
  have : 1 / ((p : ℝ) / R) = R / p := one_div_div _ _
  simp only [this]
  field_simp

end CatalanCore.Zeta5.Sum
