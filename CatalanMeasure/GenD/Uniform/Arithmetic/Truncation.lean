module
public import CatalanMeasure.GenD.Uniform.Arithmetic.PriceGrowth
public import Mathlib.Analysis.Normed.Group.Bounded
@[expose] public section
namespace CatalanMeasure.GenD.Uniform.Arithmetic
open Filter CatalanMeasure.Parametric
open scoped Topology BigOperators
noncomputable section

/-- A continuous profile loses arbitrarily little area when its zero endpoint
is replaced by a positive endpoint. This is an actual bounded-integral proof. -/
theorem exists_positive_truncation {F : ℝ→ℝ} {b c : ℝ} (hb : 0<b)
    (hF : ContinuousOn F (Set.Icc 0 b)) (hc : c<∫x in (0:ℝ)..b,F x) :
    ∃a:ℝ,0<a ∧ a<b ∧ c<∫x in a..b,F x := by
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hF
  let M : ℝ := max C 1
  have hM : 0<M := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  let A : ℝ := ∫x in (0:ℝ)..b,F x
  let a : ℝ := min (b/2) ((A-c)/(2*M))
  have ha : 0<a := lt_min (by positivity) (by positivity)
  have hab : a<b := (min_le_left _ _).trans_lt (by linarith)
  have hmul : a*M≤(A-c)/2 := by
    have h := (le_div_iff₀ (by positivity : 0<2*M)).mp (min_le_right (b/2) ((A-c)/(2*M)))
    change a*(2*M)≤A-c at h
    linarith
  have hsub0 : Set.Icc 0 a⊆Set.Icc 0 b := Set.Icc_subset_Icc le_rfl hab.le
  have hsub1 : Set.Icc a b⊆Set.Icc 0 b := Set.Icc_subset_Icc ha.le le_rfl
  have hi0 := (hF.mono hsub0).intervalIntegrable_of_Icc ha.le
  have hi1 := (hF.mono hsub1).intervalIntegrable_of_Icc hab.le
  have hsmall : (∫x in (0:ℝ)..a,F x)≤a*M := by
    have h := intervalIntegral.integral_mono_on ha.le hi0
      (continuous_const.intervalIntegrable 0 a) (fun x hx =>
        (le_abs_self (F x)).trans ((hC x (hsub0 hx)).trans (le_max_left C 1)))
    simpa only [intervalIntegral.integral_const,sub_zero,smul_eq_mul] using h
  have hadd := intervalIntegral.integral_add_adjacent_intervals hi0 hi1
  refine ⟨a,ha,hab,?_⟩
  change (∫x in (0:ℝ)..a,F x)+(∫x in a..b,F x)=A at hadd
  linarith

/-- Full zero-start saving area on the actual large-odd-prime branch.
Small primes are omitted only after choosing a fixed positive truncation;
the integral lemma then recovers the entire area. -/
theorem zero_start_odd_growth (P : Parameters) {F : ℝ→ℝ} {b : ℝ}
    (hb : 0<b) (hbH : b≤(P.H 1:ℝ)) (hF : ContinuousOn F (Set.Icc 0 b))
    (e : ℕ→ℕ→ℕ)
    (he : ∀ᶠ N:ℕ in atTop,∀p:ℕ,p.Prime→p≠2→P.H N<p^2→p≤P.H N→
      (p:ℝ)≤b*N→(N:ℝ)*F ((p:ℝ)/N)-1≤e N p)
    {c : ℝ} (hc : c<∫x in (0:ℝ)..b,F x) :
    ∀ᶠ N:ℕ in atTop,c*(N:ℝ)^2≤∑p∈oddBranch P N,(e N p:ℝ)*Real.log p := by
  obtain ⟨a,ha,hab,harea⟩ := exists_positive_truncation hb hF hc
  have hvalid := window_in_oddBranch_eventually P ha hbH
  have hbound := WindowGrowth.single_growth_eventually ha hab
    (hF.mono (Set.Icc_subset_Icc ha.le le_rfl)) e (by
      filter_upwards [he,hvalid] with N heN hvN
      intro p hp hpa hpb
      obtain ⟨hp2,hsq,hpH⟩ := hvN p hp hpa hpb
      exact heN p hp hp2 hsq hpH hpb) harea
  filter_upwards [hbound,hvalid] with N hbound hvN
  refine hbound.trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_)
  · intro p hp
    have hh := (PrimeGrowth.mem_winPrimes ha.le hab.le).mp hp
    obtain ⟨hp2,hsq,hpH⟩ := hvN p hh.2.2 hh.1 hh.2.1
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
      ⟨Finset.mem_Ioc.mpr ⟨hh.2.2.pos,hpH⟩,hh.2.2⟩,hp2,not_le.mpr hsq⟩
  · intro p hp _
    exact mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg p)

/-- Explicit compact-band errors can be sent to zero after the arithmetic
prime-sum estimate, without assuming any source growth conclusion. -/
theorem absorb_lowBand_error (D : ℕ→ℕ) (G K : ℝ) (hK : 0≤K)
    (h : ∀a:ℝ,0<a→∀δ:ℝ,0<δ→∀ᶠ N:ℕ in atTop,
      Real.log (D N:ℝ)≤(G+K*a+δ)*(N:ℝ)^2) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ N:ℕ in atTop,Real.log (D N:ℝ)≤(G+ε)*(N:ℝ)^2 := by
  let a : ℝ := ε/(2*(K+1))
  have ha : 0<a := by dsimp [a]; positivity
  have hKa : K*a≤ε/2 := by
    have he : a*(2*(K+1))=ε := by dsimp [a]; field_simp
    nlinarith only [he,ha]
  filter_upwards [h a ha (ε/2) (by positivity)] with N hN
  exact hN.trans (mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _))
end
end CatalanMeasure.GenD.Uniform.Arithmetic
