module
public import CatalanCore.Li2.DecayCert.Segment
public import Mathlib.Analysis.Analytic.OfScalars
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Tactic.Linarith
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
@[expose] public section
set_option Elab.async false
open Filter Topology
open scoped NNReal ENNReal BigOperators
namespace CatalanCore.Li2.DecayCert

theorem HasTaylorSeriesAt.hasFPowerSeriesAt {f : ℂ → ℂ} {b : ℕ → ℂ} {x : ℂ}
    (hb : HasTaylorSeriesAt f b x) :
    HasFPowerSeriesAt f (FormalMultilinearSeries.ofScalars ℂ b) x := by
  rcases hb with ⟨r,hr,hb⟩
  apply hasFPowerSeriesAt_iff.mpr
  filter_upwards [Metric.ball_mem_nhds (0:ℂ) hr] with y hy
  have hy' : ‖y‖ < r := by simpa only [Metric.mem_ball,dist_zero_right] using hy
  simpa only [FormalMultilinearSeries.coeff_ofScalars,smul_eq_mul,mul_comm] using hb y hy'

theorem HasTaylorSeriesAt.zero {f : ℂ → ℂ} {b : ℕ → ℂ} {x : ℂ}
    (hb : HasTaylorSeriesAt f b x) : b 0=f x := by
  rcases hb with ⟨r,hr,hb⟩
  have hh := (hb 0 (by simpa using hr)).tsum_eq
  rw [tsum_eq_single 0 (fun n hn => by simp [zero_pow hn])] at hh
  simpa using hh

theorem HasTaylorSeriesAt.unique {f : ℂ → ℂ} {b c : ℕ → ℂ} {x : ℂ}
    (hb : HasTaylorSeriesAt f b x) (hc : HasTaylorSeriesAt f c x) : b=c := by
  have hh := hb.hasFPowerSeriesAt.eq_formalMultilinearSeries hc.hasFPowerSeriesAt
  funext n
  have := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p n (fun _ => 1)) hh
  simpa only [FormalMultilinearSeries.ofScalars_apply_eq,smul_eq_mul,one_pow,mul_one] using this
theorem hasTaylorSeriesAt_of_hasFPowerSeriesAt {f : ℂ → ℂ}
    {p : FormalMultilinearSeries ℂ ℂ ℂ} {x : ℂ} (hp : HasFPowerSeriesAt f p x) :
    HasTaylorSeriesAt f (fun n => p.coeff n) x := by
  rcases Metric.eventually_nhds_iff.mp (hasFPowerSeriesAt_iff.mp hp) with ⟨r,hr,hp⟩
  refine ⟨r,hr,?_⟩
  intro y hy
  simpa only [smul_eq_mul,mul_comm] using hp (by simpa only [dist_zero_right] using hy)

theorem HasTaylorSeriesAt.deriv {f : ℂ → ℂ} {b : ℕ → ℂ} {x : ℂ}
    (hb : HasTaylorSeriesAt f b x) :
    HasTaylorSeriesAt (_root_.deriv f) (fun n => (n+1:ℕ)*b (n+1)) x := by
  rcases hb.hasFPowerSeriesAt with ⟨r,hp⟩
  have hd : HasFPowerSeriesOnBall (_root_.deriv f)
      (FormalMultilinearSeries.ofScalars ℂ (fun n => (n+1:ℕ)*b (n+1))) x r := by
    convert! (ContinuousLinearMap.apply ℂ ℂ (1:ℂ)).comp_hasFPowerSeriesOnBall hp.fderiv using 1
    ext n
    simp
  have hh := hasTaylorSeriesAt_of_hasFPowerSeriesAt hd.hasFPowerSeriesAt
  simpa only [FormalMultilinearSeries.coeff_ofScalars] using hh

theorem HasTaylorSeriesAt.congr {f g : ℂ → ℂ} {b : ℕ → ℂ} {x : ℂ}
    (hb : HasTaylorSeriesAt f b x) (he : ∀ᶠ z in nhds x, f z=g z) :
    HasTaylorSeriesAt g b x := by
  have h := hasTaylorSeriesAt_of_hasFPowerSeriesAt (hb.hasFPowerSeriesAt.congr he)
  simpa only [FormalMultilinearSeries.coeff_ofScalars] using h

theorem HasTaylorSeriesAt.mul {f g : ℂ → ℂ} {b c : ℕ → ℂ} {x : ℂ}
    (hb : HasTaylorSeriesAt f b x) (hc : HasTaylorSeriesAt g c x) :
    HasTaylorSeriesAt (fun z => f z*g z)
      (fun n => ∑ k ∈ Finset.range (n+1), b k*c (n-k)) x := by
  rcases hb.hasFPowerSeriesAt with ⟨r,hp⟩
  rcases hc.hasFPowerSeriesAt with ⟨s,hq⟩
  have hh : HasFPowerSeriesAt (fun z => f z*g z)
      (FormalMultilinearSeries.ofScalars ℂ (fun n => ∑ k ∈ Finset.range (n+1), b k*c (n-k))) x := by
    apply hasFPowerSeriesAt_iff.mpr
    filter_upwards [Metric.eball_mem_nhds (0:ℂ) hp.r_pos,
      Metric.eball_mem_nhds (0:ℂ) hq.r_pos] with y hy hy'
    have hyP := Metric.eball_subset_eball hp.r_le hy
    have hyQ := Metric.eball_subset_eball hq.r_le hy'
    have hnP : Summable (fun n => ‖b n*y^n‖) := by
      simpa only [FormalMultilinearSeries.ofScalars_apply_eq,smul_eq_mul] using
        (FormalMultilinearSeries.ofScalars ℂ b).summable_norm_apply hyP
    have hnQ : Summable (fun n => ‖c n*y^n‖) := by
      simpa only [FormalMultilinearSeries.ofScalars_apply_eq,smul_eq_mul] using
        (FormalMultilinearSeries.ofScalars ℂ c).summable_norm_apply hyQ
    have hm := hasSum_sum_range_mul_of_summable_norm hnP hnQ
    have hf : (∑' n, b n*y^n)=f (x+y) := by
      simpa only [FormalMultilinearSeries.ofScalars_apply_eq,smul_eq_mul] using (hp.hasSum hy).tsum_eq
    have hg : (∑' n, c n*y^n)=g (x+y) := by
      simpa only [FormalMultilinearSeries.ofScalars_apply_eq,smul_eq_mul] using (hq.hasSum hy').tsum_eq
    rw [hf,hg] at hm
    convert hm using 1
    funext n
    simp only [FormalMultilinearSeries.coeff_ofScalars,smul_eq_mul]
    rw [mul_comm,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k hk
    have hkn : k+(n-k)=n := Nat.add_sub_of_le (Nat.le_of_lt_succ (Finset.mem_range.mp hk))
    have hypow : y^n=y^k*y^(n-k) := by rw [← pow_add,hkn]
    rw [hypow]
    ring
  have h := hasTaylorSeriesAt_of_hasFPowerSeriesAt hh
  simpa only [FormalMultilinearSeries.coeff_ofScalars] using h

theorem HasTaylorSeriesAt.add {f g : ℂ → ℂ} {b c : ℕ → ℂ} {x : ℂ}
    (hb : HasTaylorSeriesAt f b x) (hc : HasTaylorSeriesAt g c x) :
    HasTaylorSeriesAt (fun z => f z+g z) (fun n => b n+c n) x := by
  rcases hb with ⟨r,hr,hb⟩
  rcases hc with ⟨s,hs,hc⟩
  refine ⟨min r s,lt_min hr hs,?_⟩
  intro y hy
  convert (hb y (hy.trans_le (min_le_left _ _))).add (hc y (hy.trans_le (min_le_right _ _))) using 1
  funext n
  ring

theorem HasTaylorSeriesAt.sub {f g : ℂ → ℂ} {b c : ℕ → ℂ} {x : ℂ}
    (hb : HasTaylorSeriesAt f b x) (hc : HasTaylorSeriesAt g c x) :
    HasTaylorSeriesAt (fun z => f z-g z) (fun n => b n-c n) x := by
  rcases hb with ⟨r,hr,hb⟩
  rcases hc with ⟨s,hs,hc⟩
  refine ⟨min r s,lt_min hr hs,?_⟩
  intro y hy
  convert (hb y (hy.trans_le (min_le_left _ _))).sub (hc y (hy.trans_le (min_le_right _ _))) using 1
  funext n
  ring

theorem HasTaylorSeriesAt.const_mul {f : ℂ → ℂ} {b : ℕ → ℂ} {x : ℂ}
    (hb : HasTaylorSeriesAt f b x) (t : ℂ) :
    HasTaylorSeriesAt (fun z => t*f z) (fun n => t*b n) x := by
  rcases hb with ⟨r,hr,hb⟩
  refine ⟨r,hr,?_⟩
  intro y hy
  convert (hb y hy).mul_left t using 1
  funext n
  ring

theorem hasTaylorSeriesAt_const (t x : ℂ) :
    HasTaylorSeriesAt (fun _ => t) (fun n => if n=0 then t else 0) x := by
  refine ⟨1,by norm_num,?_⟩
  intro y hy
  convert (hasSum_single 0 (f:=fun n : ℕ => (if n=0 then t else 0)*y^n)
    (fun n hn => by simp [hn])) using 1 <;> simp

theorem hasTaylorSeriesAt_id_zero :
    HasTaylorSeriesAt (fun z : ℂ => z) (fun n => if n=1 then 1 else 0) 0 := by
  refine ⟨1,by norm_num,?_⟩
  intro y hy
  convert (hasSum_single 1 (f:=fun n : ℕ => (if n=1 then 1 else 0)*y^n)
    (fun n hn => by simp [hn])) using 1 <;> simp

theorem hasTaylorSeriesAt_monomial_zero (a : ℂ) (k : ℕ) :
    HasTaylorSeriesAt (fun z : ℂ => a*z^k) (fun n => if n=k then a else 0) 0 := by
  refine ⟨1,by norm_num,?_⟩
  intro y hy
  convert (hasSum_single k (f:=fun n : ℕ => (if n=k then a else 0)*y^n)
    (fun n hn => by simp [hn])) using 1 <;> simp

#print axioms HasTaylorSeriesAt.hasFPowerSeriesAt
#print axioms HasTaylorSeriesAt.zero
#print axioms HasTaylorSeriesAt.unique
#print axioms HasTaylorSeriesAt.deriv
#print axioms HasTaylorSeriesAt.mul
#print axioms HasTaylorSeriesAt.add
#print axioms HasTaylorSeriesAt.sub
#print axioms HasTaylorSeriesAt.const_mul
#print axioms hasTaylorSeriesAt_const
#print axioms hasTaylorSeriesAt_id_zero
#print axioms hasTaylorSeriesAt_monomial_zero
end CatalanCore.Li2.DecayCert
