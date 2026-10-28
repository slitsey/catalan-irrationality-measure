module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Topology.UniformSpace.HeineCantor
public import Mathlib.Data.Rat.Cast.Order

@[expose] public section

/-!
# The Darboux cap bridge (lane D, package D2)

For a function `G` continuous on `[-r0, 0]` (the restriction of the atomic potential `g` to the real
axis) and a cap integral lower bound `Scap ≤ ∫ min(G - m', 0)`, there is, for every debit `η > 0`, a
finite rational partition of `[-r0, 0]` with rational lower values `segG` (`segG i ≤ G` on the cell)
such that `Scap - η ≤ ∑ len_i · min(segG i - m', 0)`.  This is the `segG` recipe: values near the
midpoint value minus a modulus, rounded; the debit is `length · (2ω + rounding)`.
-/

namespace CatalanCore.Uniform.Decay.Spline

open Finset intervalIntegral Set

theorem exists_seg_cover {G : ℝ → ℝ} {r0 : ℚ} (hr0 : 0 < r0)
    (hG : ContinuousOn G (Set.Icc (-(r0 : ℝ)) 0)) (mp Scap : ℝ)
    (hS : Scap ≤ ∫ x in (-(r0 : ℝ))..0, min (G x - mp) 0) {η : ℝ} (hη : 0 < η) :
    ∃ (nSeg : ℕ) (segA segB segG : Fin nSeg → ℚ),
      (∀ i, segA i ≤ segB i) ∧
      (∀ i (x : ℝ), (segA i : ℝ) ≤ x → x ≤ segB i → (segG i : ℝ) ≤ G x) ∧
      (∀ x : ℝ, -(r0 : ℝ) ≤ x → x ≤ 0 → ∃ i, (segA i : ℝ) ≤ x ∧ x ≤ segB i) ∧
      Scap - η ≤ ∑ i, ((segB i : ℝ) - segA i) * min ((segG i : ℝ) - mp) 0 := by
  classical
  set r : ℝ := (r0 : ℝ) with hrdef
  have hr : 0 < r := by rw [hrdef]; exact_mod_cast hr0
  set ω : ℝ := η / (3 * r) with hω
  have hω0 : 0 < ω := by positivity
  obtain ⟨δ, hδ, hunif⟩ := Metric.uniformContinuousOn_iff.1
    (isCompact_Icc.uniformContinuousOn_of_continuous hG) ω hω0
  obtain ⟨N, hN⟩ := exists_nat_gt (r / δ)
  have hr_d : r / δ > 0 := by positivity
  have hNpos : 0 < N := by
    have : (0 : ℝ) < N := lt_trans hr_d hN
    exact_mod_cast this
  have hN' : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hcell : r / N < δ := by
    rw [div_lt_iff₀ hN']; rw [div_lt_iff₀ hδ] at hN; linarith
  set h : ℝ → ℝ := fun x => min (G x - mp) 0 with hh
  have hhc : ContinuousOn h (Set.Icc (-r) 0) := continuous_min.comp_continuousOn ((hG.sub continuousOn_const).prodMk continuousOn_const)
  -- cell endpoints
  let aQ : ℕ → ℚ := fun k => -r0 + (k : ℚ) * (r0 / N)
  have haR : ∀ k : ℕ, (aQ k : ℝ) = -r + k * (r / N) := by intro k; simp [aQ, hrdef]
  have ha0 : (aQ 0 : ℝ) = -r := by rw [haR]; simp
  have haN : (aQ N : ℝ) = 0 := by rw [haR]; field_simp; ring
  have hacc : ∀ k : ℕ, k ≤ N → -r ≤ (aQ k : ℝ) ∧ (aQ k : ℝ) ≤ 0 := by
    intro k hk
    rw [haR]
    have : (k : ℝ) ≤ N := by exact_mod_cast hk
    have h1 : (k : ℝ) * (r / N) ≤ N * (r / N) := mul_le_mul_of_nonneg_right this (by positivity)
    have h2 : (N : ℝ) * (r / N) = r := by field_simp
    constructor
    · have : 0 ≤ (k : ℝ) * (r / N) := by positivity
      linarith
    · linarith
  have hstep : ∀ k : ℕ, (aQ (k + 1) : ℝ) - aQ k = r / N := by
    intro k; rw [haR, haR]; push_cast; ring
  -- lower values
  have hex : ∀ i : Fin N, ∃ q : ℚ, G ((aQ i : ℝ) + r / (2 * N)) - ω - ω < q ∧
      (q : ℝ) < G ((aQ i : ℝ) + r / (2 * N)) - ω := by
    intro i; exact exists_rat_btwn (by linarith)
  choose q hq1 hq2 using hex
  have hmid : ∀ i : Fin N, (aQ i : ℝ) + r / (2 * N) ∈ Set.Icc (-r) 0 := by
    intro i
    have h1 := hacc i (by omega)
    have h2 := hacc (i + 1) (by omega)
    have h3 := hstep i
    have h4 : r / (2 * N) = (r / N) / 2 := by field_simp
    constructor <;> linarith [h1.1, h2.2, h4]
  have hcellG : ∀ (i : Fin N) (x : ℝ), (aQ i : ℝ) ≤ x → x ≤ (aQ (i + 1) : ℝ) →
      x ∈ Set.Icc (-r) 0 ∧ |G x - G ((aQ i : ℝ) + r / (2 * N))| < ω := by
    intro i x hx1 hx2
    have h1 := hacc i (by omega)
    have h2 := hacc (i + 1) (by omega)
    have h3 := hstep i
    have hxm : x ∈ Set.Icc (-r) 0 := ⟨by linarith [h1.1], by linarith [h2.2]⟩
    refine ⟨hxm, ?_⟩
    have := hunif x hxm _ (hmid i) (by
      rw [Real.dist_eq, abs_lt]
      have h4 : r / (2 * N) = (r / N) / 2 := by field_simp
      constructor <;> linarith)
    simpa [Real.dist_eq] using this
  refine ⟨N, fun i => aQ i, fun i => aQ (i + 1), q, ?_, ?_, ?_, ?_⟩
  · intro i
    have := hstep i
    have : (aQ (i : ℕ) : ℝ) ≤ aQ ((i : ℕ) + 1) := by
      have h5 : 0 < r / N := by positivity
      linarith
    exact_mod_cast this
  · intro i x hx1 hx2
    obtain ⟨_, hd⟩ := hcellG i x hx1 hx2
    have := (abs_lt.1 hd).1
    have := hq2 i
    linarith
  · intro x hx1 hx2
    -- locate the cell: largest k with aQ k ≤ x
    have hex2 : ∃ k : ℕ, k < N ∧ (aQ k : ℝ) ≤ x ∧ x ≤ (aQ (k + 1) : ℝ) := by
      by_contra hcon
      push Not at hcon
      -- induction: aQ k ≤ x for k ≤ ... derive x > 0
      have key : ∀ k : ℕ, k ≤ N → (aQ k : ℝ) ≤ x := by
        intro k
        induction k with
        | zero => intro _; rw [ha0]; exact hx1
        | succ k ih =>
          intro hk
          have := hcon k (by omega) (ih (by omega))
          exact this.le
      have := key N le_rfl
      rw [haN] at this
      -- then x = 0 is in the last cell
      have hx0 : x = 0 := le_antisymm hx2 this
      have hlast := hcon (N - 1) (by omega) (key _ (by omega))
      have e : N - 1 + 1 = N := by omega
      rw [e, haN] at hlast
      linarith
    obtain ⟨k, hk, h1, h2⟩ := hex2
    exact ⟨⟨k, hk⟩, h1, h2⟩
  · -- the Darboux sum
    have hle : ∀ k : ℕ, (aQ k : ℝ) ≤ aQ (k + 1) := by
      intro k
      have := hstep k; have h5 : 0 < r / N := by positivity
      linarith
    have hint : ∀ k : ℕ, k < N → IntervalIntegrable h MeasureTheory.volume (aQ k : ℝ) (aQ (k + 1) : ℝ) := by
      intro k hk
      have h1 := hacc k (by omega)
      have h2 := hacc (k + 1) (by omega)
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le (hle k)]
      exact hhc.mono (fun x hx => ⟨by linarith [h1.1, hx.1], by linarith [h2.2, hx.2]⟩)
    have hsum := intervalIntegral.sum_integral_adjacent_intervals
      (f := h) (μ := MeasureTheory.volume) (a := fun k : ℕ => (aQ k : ℝ)) (n := N) (fun k hk => hint k hk)
    rw [ha0, haN] at hsum
    have hcellb : ∀ i : Fin N, ∫ x in (aQ i : ℝ)..(aQ (i + 1) : ℝ), h x
        ≤ ((aQ (i + 1) : ℝ) - aQ i) * (min ((q i : ℝ) - mp) 0 + 3 * ω) := by
      intro i
      have hI := hint i i.2
      have := intervalIntegral.integral_mono_on (hle i) hI (intervalIntegrable_const (c := min ((q i : ℝ) - mp) 0 + 3 * ω))
        (fun x hx => by
          obtain ⟨_, hd⟩ := hcellG i x hx.1 hx.2
          have h1 := (abs_lt.1 hd).2
          have h2 := hq1 i
          have : G x - mp ≤ ((q i : ℝ) - mp) + 3 * ω := by linarith
          show min (G x - mp) 0 ≤ _
          rcases le_total ((q i : ℝ) - mp) 0 with h3 | h3
          · rw [min_eq_left h3]; exact (min_le_left _ _).trans this
          · rw [min_eq_right h3]; linarith [min_le_right (G x - mp) 0])
      simp only [intervalIntegral.integral_const, smul_eq_mul] at this
      exact this.trans_eq (by ring)
    have hlen : ∑ i : Fin N, ((aQ (i + 1) : ℝ) - aQ i) = r := by
      have := Finset.sum_range_sub (fun k : ℕ => (aQ k : ℝ)) N
      rw [haN, ha0] at this
      rw [Fin.sum_univ_eq_sum_range (fun k => (aQ (k + 1) : ℝ) - aQ k) N]
      linarith
    have h1 : ∑ i : Fin N, ∫ x in (aQ i : ℝ)..(aQ (i + 1) : ℝ), h x
        = ∫ x in (-r)..0, h x := by
      rw [Fin.sum_univ_eq_sum_range (fun k => ∫ x in (aQ k : ℝ)..(aQ (k + 1) : ℝ), h x) N]
      exact hsum
    have h2 := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin N))) => hcellb i)
    have h3 : ∑ i : Fin N, ((aQ (i + 1) : ℝ) - aQ i) * (min ((q i : ℝ) - mp) 0 + 3 * ω)
        = ∑ i : Fin N, ((aQ (i + 1) : ℝ) - aQ i) * min ((q i : ℝ) - mp) 0 + 3 * ω * r := by
      rw [← hlen, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    have h4 : 3 * ω * r = η := by rw [hω]; field_simp
    have hS' : Scap ≤ ∫ x in (-r)..0, h x := hS
    rw [h1] at h2
    linarith

end CatalanCore.Uniform.Decay.Spline
