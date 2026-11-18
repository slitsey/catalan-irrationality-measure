module
public import CatalanCore.Li2.DecayCert.Source.Sound
public import CatalanCore.Li2.DecayCert.Moments
public import CatalanCore.Lai.DecayTowerV
public import CatalanCore.Li2.DecayCert.PolynomialList
@[expose] public section
set_option Elab.async false
open MeasureTheory Set Filter Topology Polynomial
open scoped BigOperators
open CatalanCore.Zeta5.Potential CatalanCore.Tools.Joukowski
namespace CatalanCore.Li2.DecayCert
inductive ArcPoint
  | minusOne | plusOne
  | tangent : ℚ → ArcPoint
def ArcPoint.x : ArcPoint → ℚ
  | .minusOne => -1 | .plusOne => 1 | .tangent t => (1-t^2)/(1+t^2)
def ArcPoint.sin : ArcPoint → ℚ
  | .minusOne => 0 | .plusOne => 0 | .tangent t => 2*t/(1+t^2)
def ArcPoint.angle (terms : ℕ) : ArcPoint → SE
  | .minusOne => .pi | .plusOne => .rat 0 | .tangent t => seScale 2 (.arg terms (1,t))
def ArcPoint.valid : ArcPoint → Bool
  | .minusOne | .plusOne => true | .tangent t => decide (0 ≤ t)

theorem tangent_arg_value (t : ℚ) :
    Complex.arg (cqReal (1,t)) = Real.arctan (t:ℝ) := by
  rw [Complex.arg_of_re_nonneg (by norm_num [cqReal]),Real.arctan_eq_arcsin]
  simp [cqReal,Complex.norm_def,Complex.normSq_apply,add_comm,pow_two]

theorem tangent_angle_exact (terms : ℕ) (t : ℚ) :
    (seScale 2 (.arg terms (1,t))).value = 2*Real.arctan (t:ℝ) := by
  change (2:ℚ)*Complex.arg (cqReal (1,t))=2*Real.arctan (t:ℝ)
  rw [tangent_arg_value]
  norm_num

theorem atan_one_rejected : (ScalarExpr.atan 8 1).check = none := by decide +kernel
theorem arg_one_one_accepted : (ScalarExpr.arg 8 (1,1)).check.isSome = true := by decide +kernel


private theorem cos_integral_nat (k : ℕ) (a b : ℝ) :
    (∫ θ in a..b, Real.cos ((k+1:ℕ)*θ)) =
      (Real.sin ((k+1:ℕ)*b)-Real.sin ((k+1:ℕ)*a))/(k+1:ℕ) := by
  rw [intervalIntegral.integral_comp_mul_left Real.cos (by positivity : ((k+1:ℕ):ℝ) ≠ 0),
    integral_cos]
  simp only [smul_eq_mul, div_eq_mul_inv]
  ring

theorem cheb_interval_integral (c : ℕ → ℝ) (N : ℕ) (a b : ℝ) :
    (∫ θ in a..b, chebF c N (Real.cos θ)) =
      c 0*(b-a) + ∑ k ∈ Finset.range N, c (k+1)*
        (Real.sin ((k+1:ℕ)*b)-Real.sin ((k+1:ℕ)*a))/(k+1:ℕ) := by
  have he : (fun θ => chebF c N (Real.cos θ)) =
      fun θ => c 0 + ∑ k ∈ Finset.range N, c (k+1)*Real.cos ((k+1:ℕ)*θ) := by
    funext θ
    rw [chebF_cos, Finset.sum_range_succ']
    simp [add_comm]
  rw [he, intervalIntegral.integral_add (intervalIntegrable_const)
    ((continuous_finsetSum _ (fun k _ => by fun_prop)).intervalIntegrable _ _),
    intervalIntegral.integral_const, intervalIntegral.integral_finsetSum
      (fun k _ => (by fun_prop : Continuous (fun θ => c (k+1)*Real.cos ((k+1:ℕ)*θ))).intervalIntegrable _ _)]
  simp only [intervalIntegral.integral_const_mul, cos_integral_nat, smul_eq_mul, ← mul_div_assoc]
  ring

theorem arc_interval_integral (g : ℝ → ℝ) (a b : ℝ)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ Real.pi) :
    (∫ θ, (Icc a b).indicator g θ ∂arc) =
      (1/Real.pi)*(∫ θ in a..b, g θ) := by
  rw [integral_arc, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_of_le Real.pi_pos.le, ← integral_Icc_eq_integral_Ioc,
    integral_indicator measurableSet_Icc, Measure.restrict_restrict measurableSet_Icc]
  have hs : Icc a b ∩ Icc 0 Real.pi = Icc a b :=
    inter_eq_left.mpr (Icc_subset_Icc ha hb)
  rw [hs, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]

private theorem cos_interval_mem (x0 x1 θ : ℝ)
    (hx : -1 ≤ x0 ∧ x0 ≤ x1 ∧ x1 ≤ 1) (hθ : θ ∈ Icc 0 Real.pi) :
    Real.cos θ ∈ Icc x0 x1 ↔ θ ∈ Icc (Real.arccos x1) (Real.arccos x0) := by
  have h0 := Real.strictAntiOn_cos.le_iff_ge
    (show Real.arccos x0 ∈ Icc 0 Real.pi from ⟨Real.arccos_nonneg _,Real.arccos_le_pi _⟩) hθ
  have h1 := Real.strictAntiOn_cos.le_iff_ge hθ
    (show Real.arccos x1 ∈ Icc 0 Real.pi from ⟨Real.arccos_nonneg _,Real.arccos_le_pi _⟩)
  rw [Real.cos_arccos hx.1 (hx.2.1.trans hx.2.2)] at h0
  rw [Real.cos_arccos (hx.1.trans hx.2.1) hx.2.2] at h1
  exact ⟨fun h => ⟨h1.mp h.2,h0.mp h.1⟩, fun h => ⟨h0.mpr h.2,h1.mpr h.1⟩⟩


private theorem affine_interval_mem (d : SegmentData) (x0 x1 t : ℝ) :
    d.M+d.h*(t:ℂ) ∈ (fun x : ℝ => d.M+d.h*(x:ℂ)) '' Icc x0 x1 ↔
      t ∈ Icc x0 x1 := by
  constructor
  · rintro ⟨x,hx,he⟩
    have h := mul_left_cancel₀ d.h_ne (add_left_cancel he)
    have ht : x=t := Complex.ofReal_inj.mp h
    simpa only [ht] using hx
  · intro ht
    exact ⟨t,ht,rfl⟩

theorem sigmaCell_mass (d : SegmentData) (hpos : d.densityNonneg)
    (x0 x1 : ℝ) (hx : -1 ≤ x0 ∧ x0 ≤ x1 ∧ x1 ≤ 1) :
    d.ν ((fun x : ℝ => d.M+d.h*(x:ℂ)) '' Icc x0 x1) = ENNReal.ofReal
      ((d.c 0*(Real.arccos x0-Real.arccos x1) +
        ∑ k ∈ Finset.range d.N, d.c (k+1)*
          (Real.sin ((k+1:ℕ)*Real.arccos x0)-
            Real.sin ((k+1:ℕ)*Real.arccos x1))/(k+1:ℕ))/Real.pi) := by
  let S : Set ℂ := (fun x : ℝ => d.M+d.h*(x:ℂ)) '' Icc x0 x1
  have hS : MeasurableSet S := (isCompact_Icc.image
    (show Continuous (fun x : ℝ => d.M+d.h*(x:ℂ)) by fun_prop)).measurableSet
  haveI : IsFiniteMeasure d.ν := CatalanCore.Lai.DecayEnergy.isFiniteMeasure_seg hpos
  have hind : (∫ s, S.indicator (fun _ : ℂ => (1:ℝ)) s ∂d.ν) = d.ν.real S := by
    rw [integral_indicator hS, integral_const]
    simp only [smul_eq_mul, mul_one, Measure.real,
      Measure.restrict_apply MeasurableSet.univ, univ_inter]
  have hg : Measurable (S.indicator (fun _ : ℂ => (1:ℝ))) := measurable_const.indicator hS
  have hangle : (∫ s, S.indicator (fun _ : ℂ => (1:ℝ)) s ∂d.ν) =
      ∫ θ, (Icc (Real.arccos x1) (Real.arccos x0)).indicator
        (fun θ => chebF d.c d.N (Real.cos θ)) θ ∂arc := by
    rw [show d.ν = segMeasure d.M d.h d.c d.N from rfl,
      integral_segMeasure hpos hg]
    apply integral_congr_ae
    filter_upwards [CatalanMeasure.Signed.ae_mem_Icc_denMeasure (fun _ => 0) 0] with θ hθ
    have hm := (affine_interval_mem d x0 x1 (Real.cos θ)).trans (cos_interval_mem x0 x1 θ hx hθ)
    change (d.M+d.h*(Real.cos θ:ℂ) ∈ S ↔ _) at hm
    by_cases h : θ ∈ Icc (Real.arccos x1) (Real.arccos x0)
    · rw [Set.indicator_of_mem (hm.mpr h), Set.indicator_of_mem h, mul_one]
    · rw [Set.indicator_of_notMem (fun hm' => h (hm.mp hm')), Set.indicator_of_notMem h, mul_zero]
  change d.ν S = _
  rw [← ENNReal.ofReal_toReal (measure_ne_top d.ν S)]
  change ENNReal.ofReal (d.ν.real S) = _
  rw [← hind, hangle,
    arc_interval_integral _ _ _ (Real.arccos_nonneg _) (Real.arccos_le_arccos hx.2.1)
      (Real.arccos_le_pi _), cheb_interval_integral]
  congr 1
  ring


theorem sigmaCell_polynomial_integral (d : SegmentData) (hpos : d.densityNonneg)
    (p : ℝ[X]) (x0 x1 : ℝ) (hx : -1 ≤ x0 ∧ x0 ≤ x1 ∧ x1 ≤ 1) :
    (∫ s in ((fun x : ℝ => d.M+d.h*(x:ℂ)) '' Icc x0 x1),
      p.eval (((s-d.M)/d.h).re) ∂d.ν) =
      (1/Real.pi) * ∫ θ in Real.arccos x1..Real.arccos x0,
        p.eval (Real.cos θ) * chebF d.c d.N (Real.cos θ) := by
  let S : Set ℂ := (fun x : ℝ => d.M+d.h*(x:ℂ)) '' Icc x0 x1
  have hS : MeasurableSet S := (isCompact_Icc.image
    (show Continuous (fun x : ℝ => d.M+d.h*(x:ℂ)) by fun_prop)).measurableSet
  have hg : Measurable (S.indicator (fun s : ℂ => p.eval (((s-d.M)/d.h).re))) := by
    apply Measurable.indicator _ hS
    exact (p.continuous.comp (by fun_prop)).measurable
  rw [← integral_indicator hS]
  change (∫ s, S.indicator (fun s => p.eval (((s-d.M)/d.h).re)) s ∂d.ν) = _
  rw [show d.ν = segMeasure d.M d.h d.c d.N from rfl, integral_segMeasure hpos hg]
  have he : (∫ θ, chebF d.c d.N (Real.cos θ) *
      S.indicator (fun s => p.eval (((s-d.M)/d.h).re))
        (d.M+d.h*(Real.cos θ:ℂ)) ∂arc) =
      ∫ θ, (Icc (Real.arccos x1) (Real.arccos x0)).indicator
        (fun θ => p.eval (Real.cos θ)*chebF d.c d.N (Real.cos θ)) θ ∂arc := by
    apply integral_congr_ae
    filter_upwards [CatalanMeasure.Signed.ae_mem_Icc_denMeasure (fun _ => 0) 0] with θ hθ
    have hm := (affine_interval_mem d x0 x1 (Real.cos θ)).trans (cos_interval_mem x0 x1 θ hx hθ)
    change (d.M+d.h*(Real.cos θ:ℂ) ∈ S ↔ _) at hm
    have hpar : ((d.M+d.h*(Real.cos θ:ℂ)-d.M)/d.h).re = Real.cos θ := by
      have ht : (d.M+d.h*(Real.cos θ:ℂ)-d.M)/d.h = (Real.cos θ:ℂ) := by
        field_simp [d.h_ne]
        ring
      rw [ht, Complex.ofReal_re]
    by_cases h : θ ∈ Icc (Real.arccos x1) (Real.arccos x0)
    · rw [Set.indicator_of_mem (hm.mpr h), Set.indicator_of_mem h, hpar]
      ring
    · rw [Set.indicator_of_notMem (fun hm' => h (hm.mp hm')), Set.indicator_of_notMem h, mul_zero]
  rw [he, arc_interval_integral _ _ _ (Real.arccos_nonneg _)
    (Real.arccos_le_arccos hx.2.1) (Real.arccos_le_pi _)]

theorem ArcPoint.bounds (a : ArcPoint) : -1 ≤ (a.x:ℝ) ∧ (a.x:ℝ) ≤ 1 := by
  cases a with
  | minusOne => norm_num [ArcPoint.x]
  | plusOne => norm_num [ArcPoint.x]
  | tangent t =>
    simp only [ArcPoint.x, Rat.cast_div, Rat.cast_sub, Rat.cast_add, Rat.cast_one, Rat.cast_pow]
    have hp : 0 < 1+(t:ℝ)^2 := by positivity
    constructor
    · apply (le_div_iff₀ hp).mpr
      nlinarith [sq_nonneg (t:ℝ)]
    · apply (div_le_iff₀ hp).mpr
      nlinarith [sq_nonneg (t:ℝ)]

theorem ArcPoint.angle_value (a : ArcPoint) (terms : ℕ) (ha : a.valid=true) :
    (a.angle terms).value = Real.arccos (a.x:ℝ) := by
  cases a with
  | minusOne => simp [ArcPoint.x, ArcPoint.angle, ScalarExpr.value]
  | plusOne => simp [ArcPoint.x, ArcPoint.angle, ScalarExpr.value]
  | tangent t =>
    have ht : 0 ≤ (t:ℝ) := by
      have hq : 0 ≤ t := of_decide_eq_true ha
      exact_mod_cast hq
    change (seScale 2 (.arg terms (1,t))).value = _
    rw [tangent_angle_exact]
    simp only [ArcPoint.x, Rat.cast_div, Rat.cast_sub, Rat.cast_add, Rat.cast_one, Rat.cast_pow]
    rw [← (CatalanCore.Lai.DecayTowerV.trig_two_arctan (t:ℝ)).1]
    exact (Real.arccos_cos (by positivity : 0 ≤ 2*Real.arctan (t:ℝ))
      (by linarith [Real.arctan_lt_pi_div_two (t:ℝ)])).symm

theorem ArcPoint.sin_value (a : ArcPoint) (ha : a.valid=true) :
    Real.sin (Real.arccos (a.x:ℝ)) = (a.sin:ℝ) := by
  rw [← a.angle_value 0 ha]
  cases a with
  | minusOne => simp [ArcPoint.angle, ArcPoint.sin, ScalarExpr.value]
  | plusOne => simp [ArcPoint.angle, ArcPoint.sin, ScalarExpr.value]
  | tangent t =>
    change Real.sin ((seScale 2 (.arg 0 (1,t))).value) = _
    rw [tangent_angle_exact]
    simp only [ArcPoint.sin, Rat.cast_div, Rat.cast_mul, Rat.cast_add, Rat.cast_ofNat,
      Rat.cast_one, Rat.cast_pow]
    exact (CatalanCore.Lai.DecayTowerV.trig_two_arctan (t:ℝ)).2

def qEval (p : List ℚ) (x : ℚ) : ℚ := p.foldr (fun c v => c+x*v) 0
private theorem qListPoly_cons (a : ℚ) (p : List ℚ) :
    qListPoly (a::p)=Polynomial.C a+Polynomial.X*qListPoly p := by
  ext j
  cases j with
  | zero => simp [qListPoly_coeff, coeffQ]
  | succ j =>
    rw [Polynomial.coeff_add, Polynomial.coeff_X_mul, qListPoly_coeff, qListPoly_coeff]
    simp [coeffQ]
theorem qEval_correct (p : List ℚ) (x : ℚ) : qEval p x=(qListPoly p).eval x := by
  induction p with
  | nil => simp [qEval, qListPoly]
  | cons a p ih =>
    change a+x*qEval p x = _
    rw [qListPoly_cons, Polynomial.eval_add, Polynomial.eval_C,
      Polynomial.eval_mul, Polynomial.eval_X, ih]
theorem qEval_chebU (k : ℕ) (x : ℚ) :
    qEval (qChebU k) x=(Polynomial.Chebyshev.U ℚ (k:ℤ)).eval x := by
  rw [qEval_correct, qChebU_spec]

def arcMassExpr (terms : ℕ) (d : QSegment) (a b : ArcPoint) : SE :=
  seMul (.inv .pi) (seAdd (seScale (d.c 0) (seSub (a.angle terms) (b.angle terms)))
    (seRat (((List.range (d.coeff.length-1)).map (fun k : ℕ =>
      d.c (k+1)/(k+1:ℚ) *
        (a.sin*qEval (qChebU k) a.x - b.sin*qEval (qChebU k) b.x))).sum)))

theorem arcMassExpr_eq_polynomial (terms : ℕ) (d : QSegment) (a b : ArcPoint) :
    arcMassExpr terms d a b =
      seMul (.inv .pi) (seAdd (seScale (d.c 0) (seSub (a.angle terms) (b.angle terms)))
        (seRat (((List.range (d.coeff.length-1)).map (fun k =>
          d.c (k+1)/(k+1:ℚ) *
            (a.sin*(Polynomial.Chebyshev.U ℚ (k:ℤ)).eval a.x -
              b.sin*(Polynomial.Chebyshev.U ℚ (k:ℤ)).eval b.x))).sum))) := by
  unfold arcMassExpr
  simp only [qEval_chebU]

private theorem cast_eval_chebU (k : ℕ) (x : ℚ) :
    (((Polynomial.Chebyshev.U ℚ (k:ℤ)).eval x:ℚ):ℝ) =
      (Polynomial.Chebyshev.U ℝ (k:ℤ)).eval (x:ℝ) := by
  have h := Polynomial.eval₂_at_apply (p := Polynomial.Chebyshev.U ℚ (k:ℤ))
    (algebraMap ℚ ℝ) x
  rw [← Polynomial.eval_map, Polynomial.Chebyshev.map_U] at h
  exact h.symm

theorem ArcPoint.sin_mul_U (a : ArcPoint) (ha : a.valid=true) (k : ℕ) :
    (a.sin:ℝ)*(((Polynomial.Chebyshev.U ℚ (k:ℤ)).eval a.x:ℚ):ℝ) =
      Real.sin ((k+1:ℕ)*Real.arccos (a.x:ℝ)) := by
  rw [cast_eval_chebU, ← a.sin_value ha]
  have hb := a.bounds
  have h := Polynomial.Chebyshev.U_real_cos (Real.arccos (a.x:ℝ)) (k:ℤ)
  rw [Real.cos_arccos hb.1 hb.2] at h
  simp only [Int.cast_add, Int.cast_natCast, Int.cast_one] at h
  rw [mul_comm]
  simpa only [Nat.cast_add, Nat.cast_one, Real.cos_arccos hb.1 hb.2] using h

private theorem list_range_sum {A : Type*} [AddCommMonoid A] (f : ℕ → A) (n : ℕ) :
    ((List.range n).map f).sum=∑ k ∈ Finset.range n, f k := by
  induction n with
  | zero => simp
  | succ n ih => simp only [List.range_succ, List.map_append, List.sum_append,
      List.map_singleton, List.sum_singleton, Finset.sum_range_succ, ih]

theorem arcMassExpr_value (terms : ℕ) (d : QSegment) (a b : ArcPoint)
    (ha : a.valid=true) (hb : b.valid=true) :
    (arcMassExpr terms d a b).value =
      (((d.c 0:ℝ)*(Real.arccos (a.x:ℝ)-Real.arccos (b.x:ℝ)) +
        ∑ k ∈ Finset.range (d.coeff.length-1), (d.c (k+1):ℝ)*
          (Real.sin ((k+1:ℕ)*Real.arccos (a.x:ℝ))-
            Real.sin ((k+1:ℕ)*Real.arccos (b.x:ℝ)))/(k+1:ℕ))/Real.pi) := by
  rw [arcMassExpr_eq_polynomial]
  change Real.pi⁻¹ * (((d.c 0:ℝ)*((a.angle terms).value-(b.angle terms).value)) +
    ((((List.range (d.coeff.length-1)).map (fun k =>
      d.c (k+1)/(k+1:ℚ) *
        (a.sin*(Polynomial.Chebyshev.U ℚ (k:ℤ)).eval a.x -
          b.sin*(Polynomial.Chebyshev.U ℚ (k:ℤ)).eval b.x))).sum:ℚ):ℝ)) = _
  rw [a.angle_value terms ha, b.angle_value terms hb, list_range_sum]
  push_cast
  have hsum : (∑ k ∈ Finset.range (d.coeff.length-1),
      (d.c (k+1):ℝ)/(k+1:ℕ) *
        ((a.sin:ℝ)*(((Polynomial.Chebyshev.U ℚ (k:ℤ)).eval a.x:ℚ):ℝ) -
          (b.sin:ℝ)*(((Polynomial.Chebyshev.U ℚ (k:ℤ)).eval b.x:ℚ):ℝ))) =
      ∑ k ∈ Finset.range (d.coeff.length-1), (d.c (k+1):ℝ)*
        (Real.sin ((k+1:ℕ)*Real.arccos (a.x:ℝ))-
          Real.sin ((k+1:ℕ)*Real.arccos (b.x:ℝ)))/(k+1:ℕ) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [a.sin_mul_U ha k, b.sin_mul_U hb k]
    ring
  simp only [Nat.cast_add, Nat.cast_one] at hsum
  rw [hsum]
  ring

noncomputable def QSegment.segmentData (d : QSegment) (hh : cqReal d.half ≠ 0) : SegmentData where
  M := cqReal d.mid
  h := cqReal d.half
  h_ne := hh
  N := d.coeff.length-1
  c := fun k => (d.c k:ℝ)
  finite_coeff := by
    intro k hk
    simp [QSegment.c, List.getElem?_eq_none (by omega : d.coeff.length ≤ k)]

theorem arcMassExpr_measure (terms : ℕ) (d : QSegment) (a b : ArcPoint)
    (hh : cqReal d.half ≠ 0)
    (hpos : ∀ x ∈ Icc (-1:ℝ) 1, 0 ≤ chebF (fun k => (d.c k:ℝ)) (d.coeff.length-1) x)
    (ha : a.valid=true) (hb : b.valid=true) (hab : a.x ≤ b.x) :
    d.measure ((fun x : ℝ => cqReal d.mid+cqReal d.half*(x:ℂ)) '' Icc (a.x:ℝ) (b.x:ℝ)) =
      ENNReal.ofReal (arcMassExpr terms d a b).value := by
  rw [arcMassExpr_value terms d a b ha hb]
  exact sigmaCell_mass (d.segmentData hh) hpos (a.x:ℝ) (b.x:ℝ)
    ⟨a.bounds.1, by exact_mod_cast hab, b.bounds.2⟩

theorem arcMassExpr_nonneg (terms : ℕ) (d : QSegment) (a b : ArcPoint)
    (hpos : ∀ x ∈ Icc (-1:ℝ) 1, 0 ≤ chebF (fun k => (d.c k:ℝ)) (d.coeff.length-1) x)
    (ha : a.valid=true) (hb : b.valid=true) (hab : a.x ≤ b.x) :
    0 ≤ (arcMassExpr terms d a b).value := by
  have habR : (a.x:ℝ) ≤ (b.x:ℝ) := by exact_mod_cast hab
  have hi := intervalIntegral.integral_nonneg_of_forall (μ := volume)
    (f := fun θ => chebF (fun k => (d.c k:ℝ)) (d.coeff.length-1) (Real.cos θ))
    (Real.arccos_le_arccos habR) (fun θ => hpos _ (cos_mem θ))
  rw [cheb_interval_integral] at hi
  rw [arcMassExpr_value terms d a b ha hb]
  exact div_nonneg hi Real.pi_pos.le

theorem arcMassExpr_real (terms : ℕ) (d : QSegment) (a b : ArcPoint)
    (hh : cqReal d.half ≠ 0)
    (hpos : ∀ x ∈ Icc (-1:ℝ) 1, 0 ≤ chebF (fun k => (d.c k:ℝ)) (d.coeff.length-1) x)
    (ha : a.valid=true) (hb : b.valid=true) (hab : a.x ≤ b.x) :
    d.measure.real ((fun x : ℝ => cqReal d.mid+cqReal d.half*(x:ℂ)) '' Icc (a.x:ℝ) (b.x:ℝ)) =
      (arcMassExpr terms d a b).value := by
  change (d.measure _).toReal = _
  rw [arcMassExpr_measure terms d a b hh hpos ha hb hab,
    ENNReal.toReal_ofReal (arcMassExpr_nonneg terms d a b hpos ha hb hab)]

theorem arcMassExpr_sound (terms : ℕ) (d : QSegment) (a b : ArcPoint)
    (hh : cqReal d.half ≠ 0)
    (hpos : ∀ x ∈ Icc (-1:ℝ) 1, 0 ≤ chebF (fun k => (d.c k:ℝ)) (d.coeff.length-1) x)
    (ha : a.valid=true) (hb : b.valid=true) (hab : a.x ≤ b.x)
    (box : QBox) (hc : (arcMassExpr terms d a b).check=some box) :
    d.measure.real ((fun x : ℝ => cqReal d.mid+cqReal d.half*(x:ℂ)) '' Icc (a.x:ℝ) (b.x:ℝ)) ∈
      Icc (box.1:ℝ) (box.2:ℝ) := by
  rw [arcMassExpr_real terms d a b hh hpos ha hb hab]
  exact scalarCheck_sound _ box hc

#print axioms tangent_angle_exact
#print axioms cheb_interval_integral
#print axioms arc_interval_integral
#print axioms cos_interval_mem
#print axioms sigmaCell_mass
#print axioms sigmaCell_polynomial_integral
#print axioms ArcPoint.angle_value
#print axioms ArcPoint.sin_value
#print axioms qEval_correct
#print axioms arcMassExpr_eq_polynomial
#print axioms ArcPoint.sin_mul_U
#print axioms arcMassExpr_value
#print axioms arcMassExpr_measure
#print axioms arcMassExpr_nonneg
#print axioms arcMassExpr_real
#print axioms arcMassExpr_sound
end CatalanCore.Li2.DecayCert
