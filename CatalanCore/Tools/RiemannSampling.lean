module
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Topology.UniformSpace.HeineCantor
public import Mathlib.Analysis.SpecificLimits.Basic
@[expose] public section
set_option Elab.async false
open MeasureTheory Set Filter
open scoped Topology BigOperators
namespace CatalanCore.Tools.RiemannSampling
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem mesh_error (f : ℝ → E) (hf : Continuous f) (R ε δ : ℝ)
    (hε : 0 ≤ ε) (hδ : 0 < δ)
    (hu : ∀ x ∈ Icc (0:ℝ) R, ∀ y ∈ Icc (0:ℝ) R,
      dist x y < δ → ‖f x-f y‖ ≤ ε)
    (n m : ℕ) (hn : 0 < n) (hm : (m:ℝ)/n ≤ R) (hstep : 1/(n:ℝ) < δ) :
    ‖(n:ℝ)⁻¹ • (∑ k ∈ Finset.range m, f (((k+1:ℕ):ℝ)/n))-
      ∫ x in (0:ℝ)..((m:ℝ)/n), f x‖ ≤ ε*((m:ℝ)/n) := by
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  have hstepEq (k : ℕ) : ((k+1:ℕ):ℝ)/n-(k:ℝ)/n=(n:ℝ)⁻¹ := by push_cast; ring
  have hadj : (∑ k ∈ Finset.range m, ∫ t in ((k:ℝ)/n)..(((k+1:ℕ):ℝ)/n), f t)=
      ∫ t in (0:ℝ)..((m:ℝ)/n), f t := by
    simpa only [Nat.cast_zero,zero_div] using intervalIntegral.sum_integral_adjacent_intervals
      (a := fun k : ℕ => (k:ℝ)/n) (n := m) (fun k hk => hf.intervalIntegrable _ _)
  have he : (n:ℝ)⁻¹ • (∑ k ∈ Finset.range m, f (((k+1:ℕ):ℝ)/n))-
      (∫ t in (0:ℝ)..((m:ℝ)/n), f t)=
      ∑ k ∈ Finset.range m, ∫ t in ((k:ℝ)/n)..(((k+1:ℕ):ℝ)/n),
        (f (((k+1:ℕ):ℝ)/n)-f t) := by
    rw [← hadj,Finset.smul_sum,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    rw [intervalIntegral.integral_sub intervalIntegrable_const (hf.intervalIntegrable _ _),
      intervalIntegral.integral_const,hstepEq]
  rw [he]
  calc
    _ ≤ ∑ k ∈ Finset.range m, ‖∫ t in ((k:ℝ)/n)..(((k+1:ℕ):ℝ)/n),
        (f (((k+1:ℕ):ℝ)/n)-f t)‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range m, ε*(n:ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro k hk
      have hkm : k+1 ≤ m := Finset.mem_range.mp hk
      have hkmR : ((k+1:ℕ):ℝ) ≤ (m:ℝ) := by exact_mod_cast hkm
      have hright : ((k+1:ℕ):ℝ)/n ≤ R := (div_le_div_of_nonneg_right hkmR hnR.le).trans hm
      have hleft : 0 ≤ (k:ℝ)/n := by positivity
      have horder : (k:ℝ)/n ≤ ((k+1:ℕ):ℝ)/n := by gcongr; exact_mod_cast (Nat.le_succ k)
      have hh := intervalIntegral.norm_integral_le_of_norm_le_const (C := ε)
        (f := fun t : ℝ => f (((k+1:ℕ):ℝ)/n)-f t) (a := (k:ℝ)/n) (b := ((k+1:ℕ):ℝ)/n) (by
          intro t ht
          rw [uIoc_of_le horder] at ht
          apply hu _ ⟨by positivity,hright⟩ t ⟨by linarith [ht.1],ht.2.trans hright⟩
          rw [Real.dist_eq,abs_of_nonneg (by linarith [ht.2])]
          have hdiff : ((k+1:ℕ):ℝ)/n-t ≤ (n:ℝ)⁻¹ := by rw [← hstepEq k]; linarith [ht.1]
          exact hdiff.trans_lt (by simpa only [one_div] using hstep))
      simpa only [hstepEq,abs_of_pos (inv_pos.mpr hnR)] using hh
    _ = _ := by simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]; rw [div_eq_mul_inv]; ring

theorem right_sum_limit (f : ℝ → E) (hf : Continuous f) (c : ℝ) (hc : 0 ≤ c) :
    Tendsto (fun n : ℕ => (n:ℝ)⁻¹ •
      ∑ k ∈ Finset.range (Nat.floor (c*n)), f (((k+1:ℕ):ℝ)/n))
      atTop (nhds (∫ x in (0:ℝ)..c, f x)) := by
  let S : ℕ → E := fun n => (n:ℝ)⁻¹ • ∑ k ∈ Finset.range (Nat.floor (c*n)), f (((k+1:ℕ):ℝ)/n)
  let J : ℕ → E := fun n => ∫ x in (0:ℝ)..((Nat.floor (c*n):ℝ)/n), f x
  have hJ : Tendsto J atTop (nhds (∫ x in (0:ℝ)..c, f x)) :=
    ((intervalIntegral.continuous_primitive (fun a b => hf.intervalIntegrable a b) 0).tendsto c).comp
      ((tendsto_nat_floor_mul_div_atTop hc).comp tendsto_natCast_atTop_atTop)
  have hdiff : Tendsto (fun n => S n-J n) atTop (nhds 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    let η := ε/(2*(c+1))
    have hη : 0 < η := by dsimp [η]; positivity
    obtain ⟨δ,hδ,hunif⟩ := Metric.uniformContinuousOn_iff.mp
      (isCompact_Icc.uniformContinuousOn_of_continuous hf.continuousOn) η hη
    obtain ⟨N,hN⟩ := exists_nat_gt (max 1 (1/δ))
    filter_upwards [eventually_ge_atTop N] with n hn
    have hncast : (N:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
    have hnR : 0 < (n:ℝ) := by have hh := le_max_left (1:ℝ) (1/δ); linarith
    have hn0 : 0 < n := by exact_mod_cast hnR
    have hstep : 1/(n:ℝ) < δ := by
      apply (div_lt_iff₀ hnR).mpr
      have hh := le_max_right (1:ℝ) (1/δ)
      have hh' : 1/δ < (n:ℝ) := by linarith
      exact (div_lt_iff₀ hδ).mp hh' |>.trans_eq (mul_comm _ _)
    have hm : (Nat.floor (c*n):ℝ)/n ≤ c := by
      apply (div_le_iff₀ hnR).mpr
      exact Nat.floor_le (by positivity)
    have herr := mesh_error f hf c η δ hη.le hδ (fun x hx y hy hxy =>
      (by simpa only [dist_eq_norm] using (hunif x hx y hy hxy).le)) n (Nat.floor (c*n)) hn0 hm hstep
    change dist (S n-J n) 0 < ε
    rw [dist_zero_right]
    apply herr.trans_lt
    have hh := mul_le_mul_of_nonneg_left hm hη.le
    have he : η*(c+1)=ε/2 := by dsimp [η]; field_simp <;> ring
    have hx : η*c ≤ ε/2 := by nlinarith
    linarith
  have hh := hdiff.add hJ
  simpa only [sub_add_cancel,zero_add] using hh
theorem interval_right_sum_limit (f : ℝ → E) (hf : Continuous f) (a b : ℝ)
    (ha : 0 ≤ a) (hab : a ≤ b) :
    Tendsto (fun n : ℕ => (n:ℝ)⁻¹ •
      ∑ k ∈ Finset.Icc (Nat.floor (a*n)+1) (Nat.floor (b*n)), f ((k:ℝ)/n))
      atTop (nhds (∫ x in a..b, f x)) := by
  have ht := (right_sum_limit f hf b (ha.trans hab)).sub (right_sum_limit f hf a ha)
  rw [intervalIntegral.integral_interval_sub_left (hf.intervalIntegrable 0 b) (hf.intervalIntegrable 0 a)] at ht
  apply ht.congr'
  apply Filter.Eventually.of_forall
  intro n
  dsimp only
  have hfloor : Nat.floor (a*n) ≤ Nat.floor (b*n) :=
    Nat.floor_mono (mul_le_mul_of_nonneg_right hab (Nat.cast_nonneg n (α := ℝ)))
  have he : Finset.Ico (Nat.floor (a*n)+1) (Nat.floor (b*n)+1)=
      Finset.Icc (Nat.floor (a*n)+1) (Nat.floor (b*n)) := by
    ext k
    simp only [Finset.mem_Ico,Finset.mem_Icc]
    omega
  rw [← he,← Finset.sum_Ico_add' (fun k : ℕ => f ((k:ℝ)/n)) (Nat.floor (a*n)) (Nat.floor (b*n)) 1,
    Finset.sum_Ico_eq_sub _ hfloor,smul_sub]

theorem compact_tsum_eq_sum (f : ℝ → E) (R : ℝ) (hR : 0 ≤ R)
    (hz : ∀ x : ℝ, R < x → f x=0) (n : ℕ) (hn : 0 < n) :
    (∑' k : ℕ, f (((k+1:ℕ):ℝ)/n))=
      ∑ k ∈ Finset.range (Nat.floor (R*n)), f (((k+1:ℕ):ℝ)/n) := by
  classical
  apply tsum_eq_sum
  intro k hk
  apply hz
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  apply (lt_div_iff₀ hnR).mpr
  have hfk : Nat.floor (R*n) ≤ k := by simpa only [Finset.mem_range,not_lt] using hk
  have hh := Nat.lt_floor_add_one (R*n)
  have hkk : (Nat.floor (R*n):ℝ)+1 ≤ ((k+1:ℕ):ℝ) := by exact_mod_cast (Nat.add_le_add_right hfk 1)
  exact hh.trans_le hkk

theorem compact_right_tsum_limit (f : ℝ → E) (hf : Continuous f) (R : ℝ) (hR : 0 ≤ R)
    (hz : ∀ x : ℝ, R < x → f x=0) :
    Tendsto (fun n : ℕ => (n:ℝ)⁻¹ • ∑' k : ℕ, f (((k+1:ℕ):ℝ)/n))
      atTop (nhds (∫ x in Ici (0:ℝ), f x)) := by
  have ht := right_sum_limit f hf R hR
  have he : (∫ x in Ici (0:ℝ), f x)=(∫ x in (0:ℝ)..R, f x) := by
    rw [intervalIntegral.integral_of_le hR,← integral_Icc_eq_integral_Ioc]
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ici Icc_subset_Ici_self
    intro x hx
    apply hz
    by_contra hn
    exact hx.2 ⟨hx.1,le_of_not_gt hn⟩
  rw [he]
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
  rw [compact_tsum_eq_sum f R hR hz n (by omega)]
theorem cut_tsum_eq_sum (f : ℝ → E) (c : ℝ) (hc : 0 ≤ c) (n : ℕ) (hn : 0 < n) :
    (∑' k : ℕ, if (((k+1:ℕ):ℝ)/n) ∈ Icc (0:ℝ) c then f (((k+1:ℕ):ℝ)/n) else 0)=
      ∑ k ∈ Finset.range (Nat.floor (c*n)), f (((k+1:ℕ):ℝ)/n) := by
  classical
  have hz : ∀ x : ℝ, c < x → (if x ∈ Icc (0:ℝ) c then f x else 0)=0 := by
    intro x hx
    apply if_neg
    intro h
    linarith [h.2]
  rw [compact_tsum_eq_sum (fun x => if x ∈ Icc (0:ℝ) c then f x else 0) c hc hz n hn]
  apply Finset.sum_congr rfl
  intro k hk
  apply if_pos
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  constructor
  · positivity
  · apply (div_le_iff₀ hnR).mpr
    have hkm : k+1 ≤ Nat.floor (c*n) := Finset.mem_range.mp hk
    have hkmR : ((k+1:ℕ):ℝ) ≤ (Nat.floor (c*n):ℝ) := by exact_mod_cast hkm
    exact hkmR.trans (Nat.floor_le (by positivity))

theorem cut_right_tsum_limit (f : ℝ → E) (hf : Continuous f) (c : ℝ) (hc : 0 ≤ c) :
    Tendsto (fun n : ℕ => (n:ℝ)⁻¹ • ∑' k : ℕ,
      if (((k+1:ℕ):ℝ)/n) ∈ Icc (0:ℝ) c then f (((k+1:ℕ):ℝ)/n) else 0)
      atTop (nhds (∫ x in Icc (0:ℝ) c, f x)) := by
  have ht := right_sum_limit f hf c hc
  rw [intervalIntegral.integral_of_le hc,← integral_Icc_eq_integral_Ioc] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
  rw [cut_tsum_eq_sum f c hc n (by omega)]
end CatalanCore.Tools.RiemannSampling
#print axioms CatalanCore.Tools.RiemannSampling.right_sum_limit
#print axioms CatalanCore.Tools.RiemannSampling.interval_right_sum_limit
#print axioms CatalanCore.Tools.RiemannSampling.compact_right_tsum_limit
#print axioms CatalanCore.Tools.RiemannSampling.cut_right_tsum_limit
