module
public import CatalanCore.Li2.DecayCert.Source
public import CatalanCore.Li2.DecayCert.Disc
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
@[expose] public section
set_option Elab.async false
open Polynomial MeasureTheory Set
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert
open CatalanCore.Li2.Decay
noncomputable def evalModel (a : List ℝ) (u : ℝ) : ℝ :=
  ∑ j ∈ Finset.range a.length, a[j]! * u^j

def Models (f : ℝ → ℝ) (a : List ℝ) (r e : ℝ) : Prop :=
  0 ≤ r ∧ 0 ≤ e ∧ ∀ u : ℝ, |u| ≤ r → |f u-evalModel a u| ≤ e

def ModelsOn (f : ℝ → ℝ) (a : List ℝ) (l r e : ℝ) : Prop :=
  l ≤ r ∧ 0 ≤ e ∧ ∀ u ∈ Icc l r, |f u-evalModel a u| ≤ e

theorem polynomial_truncation_bound (p : ℝ[X]) (J : ℕ) (l r u : ℝ) (hu : u ∈ Icc l r) :
    |p.eval u-∑ j ∈ Finset.range (J+1),p.coeff j*u^j| ≤
      ∑ j ∈ Finset.Icc (J+1) p.natDegree, |p.coeff j| *(max |l| |r|)^j := by
  have huabs : |u| ≤ max |l| |r| := by
    exact abs_le.mpr ⟨by have := le_max_left |l| |r|; have := neg_abs_le l; linarith [hu.1],
      by have := le_max_right |l| |r|; have := le_abs_self r; linarith [hu.2]⟩
  have hsum : p.eval u-(∑ j ∈ Finset.range (J+1),p.coeff j*u^j)=
      ∑ j ∈ Finset.Icc (J+1) p.natDegree,p.coeff j*u^j := by
    have hi : Finset.Icc (J+1) p.natDegree=Finset.Ico (J+1) (p.natDegree+1) := by
      ext k; simp only [Finset.mem_Icc,Finset.mem_Ico]; omega
    rw [hi]
    by_cases hJ : J+1 ≤ p.natDegree+1
    · have hs := Finset.sum_range_add_sum_Ico (fun j => p.coeff j*u^j) hJ
      rw [← Polynomial.eval_eq_sum_range] at hs
      linarith
    · have hdeg : p.natDegree < J+1 := by omega
      rw [Finset.Ico_eq_empty (by omega),Finset.sum_empty,p.eval_eq_sum_range' hdeg]
      ring
  rw [hsum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro j hj
  rw [abs_mul,abs_pow]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg u) huabs j) (abs_nonneg _)

theorem ownPoly_cell (d : SegmentData) (hpos : d.densityNonneg)
    (a b l r : ℝ) (hab : ∀ u ∈ Icc l r, a+b*u ∈ Icc (-1:ℝ) 1)
    (Jord : ℕ) (p : Polynomial ℝ) (hp : p=d.ownPolynomial.comp
      (Polynomial.C a+Polynomial.C b*Polynomial.X)) :
  ∀ u ∈ Icc l r,
    |P d.ν (d.M+d.h*(a+b*u:ℂ))-
      ∑ j ∈ Finset.range (Jord+1), p.coeff j*u^j| ≤
        ∑ j ∈ Finset.Icc (Jord+1) p.natDegree,
          |p.coeff j| *(max |l| |r|)^j := by
  intro u hu
  have he : P d.ν (d.M+d.h*(a+b*u:ℂ))=p.eval u := by
    have heval := segPot_closed_own d hpos _ (hab u hu)
    push_cast at heval
    rw [heval,hp,Polynomial.eval_comp]
    simp only [SegmentData.ownPolynomial,Polynomial.eval_sub,Polynomial.eval_C,
      Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_X,Polynomial.eval_finsetSum,
      T]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    push_cast
    ring
  rw [he]
  exact polynomial_truncation_bound p Jord l r u hu

def quadCandidates (a b l r : ℚ) : List ℚ :=
  [a*l+b*l^2,a*r+b*r^2] ++
    (if b ≠ 0 ∧ l ≤ -a/(2*b) ∧ -a/(2*b) ≤ r
      then [a*(-a/(2*b))+b*(-a/(2*b))^2] else [])
def polyUBQ (a : List ℚ) (l r : ℚ) : ℚ :=
  coeffQ a 0 + (quadCandidates (coeffQ a 1) (coeffQ a 2) l r).foldl max
    ((coeffQ a 1)*l+(coeffQ a 2)*l^2) +
      ∑ j ∈ Finset.range a.length, if 3 ≤ j then |coeffQ a j| *(max |l| |r|)^j else 0
def polyLBQ (a : List ℚ) (l r : ℚ) : ℚ := -polyUBQ (a.map Neg.neg) l r

theorem foldl_max_ge_init (xs : List ℚ) (q : ℚ) : q ≤ xs.foldl max q := by
  induction xs generalizing q with
  | nil => exact le_rfl
  | cons x xs ih => exact (le_max_left q x).trans (ih _)

theorem foldl_max_ge_mem (xs : List ℚ) (q x : ℚ) (hx : x ∈ xs) : x ≤ xs.foldl max q := by
  induction xs generalizing q with
  | nil => simp at hx
  | cons y ys ih =>
    rcases List.mem_cons.mp hx with rfl | hx
    · exact (le_max_right q x).trans (foldl_max_ge_init ys _)
    · exact ih _ hx

theorem quadratic_endpoint_or_vertex (a b l r u : ℝ) (hu : u ∈ Icc l r) :
    a*u+b*u^2 ≤ max (a*l+b*l^2) (a*r+b*r^2) ∨
      (b ≠ 0 ∧ l ≤ -a/(2*b) ∧ -a/(2*b) ≤ r ∧
        a*u+b*u^2 ≤ a*(-a/(2*b))+b*(-a/(2*b))^2) := by
  by_cases hb : 0 ≤ b
  · left
    by_cases hl : a+b*(u+l) ≤ 0
    · apply le_trans _ (le_max_left _ _)
      nlinarith [mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hu.1) hl]
    · have hr : 0 ≤ a+b*(u+r) := by nlinarith [mul_nonneg hb (sub_nonneg.mpr (hu.1.trans hu.2))]
      apply le_trans _ (le_max_right _ _)
      nlinarith [mul_nonneg (sub_nonneg.mpr hu.2) hr]
  · have hbneg : b < 0 := lt_of_not_ge hb
    let v := -a/(2*b)
    have hv : a+2*b*v=0 := by dsimp [v]; field_simp [hbneg.ne]; ring
    by_cases hvl : l ≤ v
    · by_cases hvr : v ≤ r
      · right
        refine ⟨hbneg.ne,hvl,hvr,?_⟩
        change a*u+b*u^2 ≤ a*v+b*v^2
        have he : a*u+b*u^2=a*v+b*v^2+b*(u-v)^2 := by
          linear_combination (u-v)*hv
        rw [he]
        linarith [mul_nonpos_of_nonpos_of_nonneg hbneg.le (sq_nonneg (u-v))]
      · left
        apply le_trans _ (le_max_right _ _)
        have hr : a+b*(u+r) ≥ 0 := by nlinarith [mul_nonpos_of_nonpos_of_nonneg hbneg.le (sub_nonneg.mpr hu.2)]
        nlinarith [mul_nonneg (sub_nonneg.mpr hu.2) hr]
    · left
      apply le_trans _ (le_max_left _ _)
      have hl : a+b*(u+l) ≤ 0 := by nlinarith [mul_nonpos_of_nonpos_of_nonneg hbneg.le (sub_nonneg.mpr hu.1)]
      nlinarith [mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hu.1) hl]

theorem quadCandidates_bound (a b l r : ℚ) (u : ℝ) (hu : u ∈ Icc (l:ℝ) (r:ℝ)) :
    (a:ℝ)*u+(b:ℝ)*u^2 ≤
      (((quadCandidates a b l r).foldl max (a*l+b*l^2):ℚ):ℝ) := by
  let xs := quadCandidates a b l r
  have hl : ((a*l+b*l^2:ℚ):ℝ) ≤ ((xs.foldl max (a*l+b*l^2):ℚ):ℝ) := by
    exact Rat.cast_le.mpr (foldl_max_ge_mem xs (a*l+b*l^2) (a*l+b*l^2) (by simp [xs,quadCandidates]))
  have hr : ((a*r+b*r^2:ℚ):ℝ) ≤ ((xs.foldl max (a*l+b*l^2):ℚ):ℝ) := by
    exact Rat.cast_le.mpr (foldl_max_ge_mem xs (a*l+b*l^2) (a*r+b*r^2) (by simp [xs,quadCandidates]))
  rcases quadratic_endpoint_or_vertex (a:ℝ) (b:ℝ) l r u hu with hh | hh
  · exact hh.trans (max_le (by simpa only [Rat.cast_add,Rat.cast_mul,Rat.cast_pow] using hl) (by simpa only [Rat.cast_add,Rat.cast_mul,Rat.cast_pow] using hr))
  · have hv : b ≠ 0 ∧ l ≤ -a/(2*b) ∧ -a/(2*b) ≤ r := by
      exact_mod_cast (show (b:ℝ) ≠ 0 ∧ (l:ℝ) ≤ -(a:ℝ)/(2*(b:ℝ)) ∧
        -(a:ℝ)/(2*(b:ℝ)) ≤ (r:ℝ) from ⟨hh.1,hh.2.1,hh.2.2.1⟩)
    have hvbound : ((a*(-a/(2*b))+b*(-a/(2*b))^2:ℚ):ℝ) ≤
        ((xs.foldl max (a*l+b*l^2):ℚ):ℝ) := by
      exact Rat.cast_le.mpr (foldl_max_ge_mem xs (a*l+b*l^2) (a*(-a/(2*b))+b*(-a/(2*b))^2) (by simp [xs,quadCandidates,hv]))
    exact hh.2.2.2.trans (by simpa only [Rat.cast_add,Rat.cast_mul,Rat.cast_pow,Rat.cast_neg,Rat.cast_div,Rat.cast_ofNat] using hvbound)

theorem sum_range_three_tail (n : ℕ) (f : ℕ → ℝ) (hz : ∀ j, n ≤ j → f j=0) :
    ∑ j ∈ Finset.range n,f j = f 0+f 1+f 2+
      ∑ j ∈ Finset.range n,if 3 ≤ j then f j else 0 := by
  by_cases hn : 3 ≤ n
  · have he : (∑ j ∈ Finset.range n,if 3 ≤ j then f j else 0)=
        ∑ j ∈ Finset.Ico 3 n,f j := by
      rw [← Finset.sum_filter]
      congr 1
      ext j
      simp only [Finset.mem_filter,Finset.mem_range,Finset.mem_Ico]
      omega
    rw [he,← Finset.sum_range_add_sum_Ico f hn]
    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]
  · have hn' : n ≤ 2 := by omega
    interval_cases n <;> simp_all [Finset.sum_range_succ]

theorem coeffQ_eq_zero_of_ge (a : List ℚ) (j : ℕ) (hj : a.length ≤ j) : coeffQ a j=0 := by
  simp [coeffQ,List.getElem?_eq_none hj]

theorem evalModel_map_rat (a : List ℚ) (u : ℝ) :
    evalModel (a.map (fun q : ℚ => (q:ℝ))) u = ∑ j ∈ Finset.range a.length,(coeffQ a j:ℝ)*u^j := by
  unfold evalModel
  simp only [List.length_map]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : j < a.length := Finset.mem_range.mp hj
  simp [List.getElem!_eq_getElem?_getD,coeffQ,List.getElem?_eq_getElem hj']

theorem polyUBQ_bound (a : List ℚ) (l r : ℚ) (u : ℝ) (hu : u ∈ Icc (l:ℝ) (r:ℝ)) :
    evalModel (a.map (fun q : ℚ => (q:ℝ))) u ≤ (polyUBQ a l r:ℝ) := by
  have he : (polyUBQ a l r:ℝ) = (coeffQ a 0:ℝ)+
      (((quadCandidates (coeffQ a 1) (coeffQ a 2) l r).foldl max
        ((coeffQ a 1)*l+(coeffQ a 2)*l^2):ℚ):ℝ)+
      ∑ j ∈ Finset.range a.length, if 3 ≤ j then |(coeffQ a j:ℝ)| *(max |(l:ℝ)| |(r:ℝ)|)^j else 0 := by
    rw [polyUBQ,Rat.cast_add,Rat.cast_add,Rat.cast_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    split_ifs <;> push_cast <;> rfl
  rw [he,evalModel_map_rat,sum_range_three_tail a.length (fun j => (coeffQ a j:ℝ)*u^j)
    (by intro j hj; rw [coeffQ_eq_zero_of_ge a j hj]; simp)]
  simp only [pow_zero,mul_one,pow_one]
  have huabs : |u| ≤ max |(l:ℝ)| |(r:ℝ)| := abs_le.mpr
    ⟨by have := le_max_left |(l:ℝ)| |(r:ℝ)|; have := neg_abs_le (l:ℝ); linarith [hu.1],
      by have := le_max_right |(l:ℝ)| |(r:ℝ)|; have := le_abs_self (r:ℝ); linarith [hu.2]⟩
  have ht : (∑ j ∈ Finset.range a.length,if 3 ≤ j then (coeffQ a j:ℝ)*u^j else 0) ≤
      ∑ j ∈ Finset.range a.length,if 3 ≤ j then |(coeffQ a j:ℝ)| *(max |(l:ℝ)| |(r:ℝ)|)^j else 0 := by
    apply Finset.sum_le_sum
    intro j hj
    split_ifs
    · calc
        _ ≤ |(coeffQ a j:ℝ)*u^j| := le_abs_self _
        _ = |(coeffQ a j:ℝ)| *|u|^j := by rw [abs_mul,abs_pow]
        _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg u) huabs j) (abs_nonneg _)
    · exact le_rfl
  have hq := quadCandidates_bound (coeffQ a 1) (coeffQ a 2) l r u hu
  linarith

theorem coeffQ_map_neg (a : List ℚ) (j : ℕ) : coeffQ (a.map Neg.neg) j= -coeffQ a j := by
  by_cases hj : j < a.length
  · simp [coeffQ,List.getElem?_eq_getElem hj]
  · simp [coeffQ_eq_zero_of_ge a j (by omega),
      coeffQ_eq_zero_of_ge (a.map Neg.neg) j (by simpa using (show a.length ≤ j by omega))]

theorem evalModel_map_neg_rat (a : List ℚ) (u : ℝ) :
    evalModel ((a.map Neg.neg).map (fun q : ℚ => (q:ℝ))) u =
      -evalModel (a.map (fun q : ℚ => (q:ℝ))) u := by
  rw [evalModel_map_rat,evalModel_map_rat,List.length_map,← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  rw [coeffQ_map_neg,Rat.cast_neg,neg_mul]

theorem cell_ub_lb (f : ℝ → ℝ) (a : List ℚ) (l r err : ℚ)
    (hm : ModelsOn f (a.map (fun x : ℚ => (x:ℝ))) l r err) :
  ∀ u ∈ Icc (l:ℝ) (r:ℝ),
    ((polyLBQ a l r-err:ℚ):ℝ) ≤ f u ∧ f u ≤ ((polyUBQ a l r+err:ℚ):ℝ) := by
  intro u hu
  have he := abs_le.mp (hm.2.2 u hu)
  have hub := polyUBQ_bound a l r u hu
  have hlb := polyUBQ_bound (a.map Neg.neg) l r u hu
  rw [evalModel_map_neg_rat] at hlb
  constructor
  · simp only [Rat.cast_sub,polyLBQ,Rat.cast_neg]
    linarith
  · rw [Rat.cast_add]
    linarith

theorem HasTaylorSeriesAt.comp_mul {f : ℂ → ℂ} {b : ℕ → ℂ}
    (hb : HasTaylorSeriesAt f b 0) (γ : ℂ) :
    HasTaylorSeriesAt (fun u => f (γ*u)) (fun n => b n*γ^n) 0 := by
  rcases hb with ⟨r,hr,hb⟩
  have hm : 0 < max 1 ‖γ‖ := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  refine ⟨r/max 1 ‖γ‖,div_pos hr hm,?_⟩
  intro u hu
  have hgu : ‖γ*u‖ < r := by
    rw [norm_mul]
    calc
      _ ≤ max 1 ‖γ‖*‖u‖ := mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)
      _ < r := by simpa only [mul_comm] using (lt_div_iff₀ hm).mp hu
  have hh := hb (γ*u) hgu
  simp only [zero_add] at hh ⊢
  convert! hh using 1
  funext n
  rw [mul_pow]
  ring

noncomputable def logUnitCoeff (n : ℕ) : ℂ := -(-1:ℂ)^n/(n:ℂ)
noncomputable def freUnitCoeff (n : ℕ) : ℂ :=
  if n < 2 then 0 else (-1:ℂ)^n/((n:ℂ)*((n:ℂ)-1))

theorem hasTaylorSeriesAt_logUnit :
    HasTaylorSeriesAt (fun u : ℂ => Complex.log (1+u)) logUnitCoeff 0 := by
  change HasTaylorSeriesAt (fun u : ℂ => Complex.log (1+u)) (fun n => -(-1:ℂ)^n/(n:ℂ)) 0
  simpa only [FormalMultilinearSeries.coeff_ofScalars] using
    hasTaylorSeriesAt_of_hasFPowerSeriesAt hasFPowerSeriesAt_clog_one_add

theorem freUnit_coeff (n : ℕ) :
    logUnitCoeff n+(if 1 ≤ n then logUnitCoeff (n-1) else 0)-(if n=1 then 1 else 0)=
      freUnitCoeff n := by
  rcases n with _|n
  · simp [logUnitCoeff,freUnitCoeff]
  rcases n with _|n
  · norm_num [logUnitCoeff,freUnitCoeff]
  have hn : n+1+1 ≠ 1 := by omega
  simp only [show ¬n+1+1<2 by omega,show 1 ≤ n+1+1 by omega,hn,
    freUnitCoeff,logUnitCoeff,ite_false,ite_true,sub_zero,Nat.add_sub_cancel]
  push_cast
  rw [pow_succ]
  have h₁ : (n:ℂ)+1 ≠ 0 := by exact_mod_cast (show n+1 ≠ 0 by omega)
  have h₂ : (n:ℂ)+1+1 ≠ 0 := by exact_mod_cast (show n+1+1 ≠ 0 by omega)
  simp only [add_sub_cancel_right]
  field_simp [h₁,h₂] <;> ring

theorem hasTaylorSeriesAt_freUnit :
    HasTaylorSeriesAt (fun u : ℂ => (1+u)*Complex.log (1+u)-u) freUnitCoeff 0 := by
  have hh := (hasTaylorSeriesAt_logUnit.add (hasTaylorSeriesAt_logUnit.monomial_mul 1 1)).sub
    hasTaylorSeriesAt_id_zero
  have hc : (fun n => logUnitCoeff n+(if 1 ≤ n then (1:ℂ)*logUnitCoeff (n-1) else 0)-
      if n=1 then (1:ℂ) else 0)=freUnitCoeff := by
    funext n
    simpa only [one_mul] using freUnit_coeff n
  rw [hc] at hh
  convert! hh using 1
  funext u
  ring

theorem log_affine_split (a v : ℂ) (ha : 0 ≤ a.re) (ha0 : a ≠ 0) (hv : ‖v‖ < 1) :
    Complex.log (a*(1+v))=Complex.log a+Complex.log (1+v) := by
  have hre : 0 < (1+v).re := by
    have hh := (Complex.abs_re_le_norm v).trans_lt hv
    simp only [Complex.add_re,Complex.one_re]
    linarith [neg_abs_le v.re]
  have hargA := abs_le.mp (Complex.abs_arg_le_pi_div_two_iff.mpr ha)
  have hargV := abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hre))
  apply Complex.log_mul ha0 (Complex.slitPlane_ne_zero (Complex.mem_slitPlane_iff.mpr (Or.inl hre)))
  constructor <;> linarith

theorem freUnit_differentiable : DifferentiableOn ℂ
    (fun u : ℂ => (1+u)*Complex.log (1+u)-u) (Metric.ball 0 1) := by
  intro u hu
  have hu' : ‖u‖ < 1 := by simpa only [Metric.mem_ball,dist_zero_right] using hu
  have hlog := (Complex.hasDerivAt_log (Complex.mem_slitPlane_of_norm_lt_one hu')).comp
    u (h:=fun z : ℂ => 1+z) ((hasDerivAt_id u).const_add 1)
  exact ((((hasDerivAt_id u).const_add 1).mul hlog).sub (hasDerivAt_id u)).differentiableAt.differentiableWithinAt

theorem norm_freUnitCoeff (n : ℕ) (hn : 2 ≤ n) :
    ‖freUnitCoeff n‖ = 1/((n:ℝ)*((n:ℝ)-1)) := by
  have hn' : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have he : (n:ℂ)*((n:ℂ)-1)=(((n:ℝ)*((n:ℝ)-1):ℝ):ℂ) := by push_cast; rfl
  rw [freUnitCoeff,ite_eq_right (by omega),norm_div,he,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (Nat.cast_nonneg n) (by linarith : 0 ≤ (n:ℝ)-1))]
  simp

theorem freUnit_remainder (z : ℂ) (t : ℝ) (ht : 0 ≤ t ∧ t < 1) (hz : ‖z‖ ≤ t)
    (J : ℕ) (hJ : 2 ≤ J) :
    ‖(1+z)*Complex.log (1+z)-z-(∑ n ∈ Finset.range (J+1),freUnitCoeff n*z^n)‖ ≤
      t^(J+1)/(((J+1:ℕ):ℝ)*(J:ℝ)*(1-t)) := by
  have hs := hasTaylorSeriesAt_freUnit.hasSum_ball freUnit_differentiable (hz.trans_lt ht.2)
  have htail := (hasSum_nat_add_iff' (J+1)).mpr hs
  let C : ℝ := t^(J+1)/(((J+1:ℕ):ℝ)*(J:ℝ))
  have hden : 0 < ((J+1:ℕ):ℝ)*(J:ℝ) := by
    have : (0:ℝ)<(J:ℝ) := by exact_mod_cast (show 0<J by omega)
    positivity
  have hbound (n : ℕ) : ‖freUnitCoeff (n+(J+1))*z^(n+(J+1))‖ ≤ C*t^n := by
    have hm : 2 ≤ n+(J+1) := by omega
    have hj : (2:ℝ) ≤ (J:ℝ) := by exact_mod_cast hJ
    have hnr : (0:ℝ) ≤ (n:ℝ) := by positivity
    have hden' : ((J+1:ℕ):ℝ)*(J:ℝ) ≤ ((n+(J+1):ℕ):ℝ)*(((n+(J+1):ℕ):ℝ)-1) := by
      push_cast
      nlinarith
    rw [norm_mul,norm_pow,norm_freUnitCoeff _ hm]
    calc
      _ ≤ (1/(((J+1:ℕ):ℝ)*(J:ℝ)))*t^(n+(J+1)) :=
        mul_le_mul (div_le_div_of_nonneg_left (by norm_num) hden hden')
          (pow_le_pow_left₀ (norm_nonneg z) hz _) (by positivity) (by positivity)
      _ = _ := by dsimp [C]; rw [pow_add]; ring
  have hh := norm_sub_le_of_geometric_bound_of_hasSum ht.2 hbound htail 0
  simpa only [Finset.range_zero,Finset.sum_empty,zero_sub,norm_neg,pow_zero,mul_one,
    C,div_div,mul_assoc] using hh

noncomputable def freComplexCoeff (a b : ℂ) (j : ℕ) : ℂ :=
  if j=0 then a*Complex.log a-a
  else if j=1 then b*Complex.log a
  else ((-1:ℂ)^j*b^j)/((j:ℂ)*((j:ℂ)-1)*a^(j-1))
noncomputable def freCoeff (a b : ℂ) (j : ℕ) : ℝ :=
  if j=0 then (a*Complex.log a-a).re
  else if j=1 then (b*Complex.log a).re
  else (((-1:ℂ)^j*b^j)/((j:ℂ)*(j-1)*a^(j-1))).re

theorem freCoeff_eq_re (a b : ℂ) (j : ℕ) : freCoeff a b j=(freComplexCoeff a b j).re := by
  unfold freCoeff freComplexCoeff
  split_ifs <;> rfl

theorem freComplexCoeff_term (a b u : ℂ) (ha : a ≠ 0) (n : ℕ) :
    freComplexCoeff a b n*u^n =
      (if n=0 then a*Complex.log a-a else 0)+
      (if n=1 then b*u*Complex.log a else 0)+a*freUnitCoeff n*((b/a)*u)^n := by
  rcases n with _|n
  · simp [freComplexCoeff,freUnitCoeff]
  rcases n with _|n
  · simp [freComplexCoeff,freUnitCoeff]; ring
  have hn0 : n+1+1 ≠ 0 := by omega
  have hn1 : n+1+1 ≠ 1 := by omega
  simp only [freComplexCoeff,hn0,hn1,ite_false,freUnitCoeff,show ¬n+1+1<2 by omega,
    zero_add,Nat.add_sub_cancel]
  have hc1 : (n:ℂ)+1+1 ≠ 0 := by exact_mod_cast (show n+1+1 ≠ 0 by omega)
  have hc2 : (n:ℂ)+1 ≠ 0 := by exact_mod_cast (show n+1 ≠ 0 by omega)
  rw [mul_pow,div_pow,pow_succ a (n+1)]
  push_cast
  simp only [add_sub_cancel_right]
  field_simp [ha,hc1,hc2] <;> ring

theorem freComplex_sum (a b u : ℂ) (ha : a ≠ 0) (J : ℕ) (hJ : 2 ≤ J) :
    (∑ n ∈ Finset.range (J+1),freComplexCoeff a b n*u^n) =
      a*Complex.log a-a+b*u*Complex.log a+
        a*(∑ n ∈ Finset.range (J+1),freUnitCoeff n*((b/a)*u)^n) := by
  simp_rw [freComplexCoeff_term a b u ha]
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib]
  simp_rw [mul_assoc a]
  rw [← Finset.mul_sum]
  simp only [Finset.sum_ite_eq',Finset.mem_range,show 0<J+1 by omega,
    show 1<J+1 by omega,ite_true]

theorem evalModel_freCoeff (a b : ℂ) (J : ℕ) (u : ℝ) :
    evalModel ((List.range (J+1)).map (freCoeff a b)) u =
      (∑ n ∈ Finset.range (J+1),freComplexCoeff a b n*(u:ℂ)^n).re := by
  unfold evalModel
  simp only [List.length_map,List.length_range,Complex.re_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hn' : n < J+1 := Finset.mem_range.mp hn
  simp [List.getElem!_eq_getElem?_getD,List.getElem?_range hn',
    freCoeff_eq_re,Complex.mul_re,← Complex.ofReal_pow]

theorem fre_affine_remainder_complex (a b : ℂ) (r : ℝ) (ha : 0 ≤ a.re)
    (hr : 0 ≤ r) (hsep : ‖b‖*r < ‖a‖) (J : ℕ) (hJ : 2 ≤ J)
    (u : ℝ) (hu : |u| ≤ r) :
    ‖(a+b*(u:ℂ))*Complex.log (a+b*(u:ℂ))-(a+b*(u:ℂ))-
      (∑ n ∈ Finset.range (J+1),freComplexCoeff a b n*(u:ℂ)^n)‖ ≤
      ‖a‖*(‖b‖*r/‖a‖)^(J+1)/(((J+1:ℕ):ℝ)*(J:ℝ)*(1-‖b‖*r/‖a‖)) := by
  have haPos : 0 < ‖a‖ := lt_of_le_of_lt (mul_nonneg (norm_nonneg b) hr) hsep
  have ha0 : a ≠ 0 := norm_pos_iff.mp haPos
  let t := ‖b‖*r/‖a‖
  let v := (b/a)*(u:ℂ)
  have ht : 0 ≤ t ∧ t < 1 := ⟨div_nonneg (mul_nonneg (norm_nonneg b) hr) haPos.le,
    (div_lt_one haPos).mpr hsep⟩
  have hv : ‖v‖ ≤ t := by
    dsimp [v,t]
    rw [norm_mul,norm_div,Complex.norm_real,Real.norm_eq_abs]
    calc
      _ ≤ (‖b‖/‖a‖)*r := mul_le_mul_of_nonneg_left hu (by positivity)
      _ = _ := by ring
  have hlog := log_affine_split a v ha ha0 (hv.trans_lt ht.2)
  have he : a*(1+v)=a+b*(u:ℂ) := by dsimp [v]; field_simp
  rw [he] at hlog
  have hsum := freComplex_sum a b (u:ℂ) ha0 J hJ
  change (∑ n ∈ Finset.range (J+1),freComplexCoeff a b n*(u:ℂ)^n)=
    a*Complex.log a-a+b*(u:ℂ)*Complex.log a+
      a*(∑ n ∈ Finset.range (J+1),freUnitCoeff n*v^n) at hsum
  have hav : a*v=b*(u:ℂ) := by dsimp [v]; field_simp
  have hid : (a+b*(u:ℂ))*Complex.log (a+b*(u:ℂ))-(a+b*(u:ℂ))-
      (∑ n ∈ Finset.range (J+1),freComplexCoeff a b n*(u:ℂ)^n)=
        a*((1+v)*Complex.log (1+v)-v-
          (∑ n ∈ Finset.range (J+1),freUnitCoeff n*v^n)) := by
    rw [hlog,hsum,← he,← hav]
    ring
  rw [hid,norm_mul]
  have hh := mul_le_mul_of_nonneg_left (freUnit_remainder v t ht hv J hJ) (norm_nonneg a)
  dsimp only [t] at hh
  simpa only [mul_div_assoc] using hh

theorem fre_taylor_remainder (a b : ℂ) (r : ℝ) (ha : 0 ≤ a.re)
    (hr : 0 ≤ r) (hsep : ‖b‖*r < ‖a‖) (Jord : ℕ) (hJ : 2 ≤ Jord) :
  Models (fun u => ((a+b*(u:ℂ))*Complex.log (a+b*(u:ℂ))-(a+b*(u:ℂ))).re)
    ((List.range (Jord+1)).map (freCoeff a b)) r
      (‖a‖*(‖b‖*r/‖a‖)^(Jord+1)/((Jord+1:ℕ)*Jord*(1-‖b‖*r/‖a‖))) := by
  have haPos : 0 < ‖a‖ := lt_of_le_of_lt (mul_nonneg (norm_nonneg b) hr) hsep
  refine ⟨hr,?_,?_⟩
  · have ht : ‖b‖*r/‖a‖ < 1 := (div_lt_one haPos).mpr hsep
    positivity
  · intro u hu
    rw [evalModel_freCoeff]
    have hh := fre_affine_remainder_complex a b r ha hr hsep Jord hJ u hu
    have hre := Complex.abs_re_le_norm
      ((a+b*(u:ℂ))*Complex.log (a+b*(u:ℂ))-(a+b*(u:ℂ))-
        (∑ n ∈ Finset.range (Jord+1),freComplexCoeff a b n*(u:ℂ)^n))
    rw [Complex.sub_re] at hre
    exact hre.trans hh

noncomputable def xtower (x : ℝ) (j : ℕ) : ℝ :=
  if j=0 then xlog x else if j=1 then Real.log x+1
  else (-1:ℝ)^j / ((j:ℝ)*(j-1)*x^(j-1))

theorem xtower_freCoeff (x : ℝ) (n : ℕ) :
    xtower x n=freCoeff (x:ℂ) 1 n+(if n=0 then x else if n=1 then 1 else 0) := by
  by_cases hn0 : n=0
  · subst n
    simp [xtower,freCoeff,xlog,Complex.mul_re,Complex.log_ofReal_re]
  by_cases hn1 : n=1
  · subst n
    simp [xtower,freCoeff,Complex.log_ofReal_re]
  simp only [xtower,freCoeff,hn0,hn1,ite_false,add_zero,one_pow,mul_one]
  have he : (-1:ℂ)^n/((n:ℂ)*((n:ℂ)-1)*(x:ℂ)^(n-1))=
      (((-1:ℝ)^n/((n:ℝ)*((n:ℝ)-1)*x^(n-1)):ℝ):ℂ) := by push_cast; rfl
  rw [he,Complex.ofReal_re]

theorem evalModel_map_range (f : ℕ → ℝ) (J : ℕ) (u : ℝ) :
    evalModel ((List.range (J+1)).map f) u=∑ n ∈ Finset.range (J+1),f n*u^n := by
  unfold evalModel
  simp only [List.length_map,List.length_range]
  apply Finset.sum_congr rfl
  intro n hn
  simp [List.getElem!_eq_getElem?_getD,List.getElem?_range (Finset.mem_range.mp hn)]

theorem evalModel_xtower (x u : ℝ) (J : ℕ) (hJ : 2 ≤ J) :
    evalModel ((List.range (J+1)).map (xtower x)) u=
      evalModel ((List.range (J+1)).map (freCoeff (x:ℂ) 1)) u+x+u := by
  rw [evalModel_map_range,evalModel_map_range]
  simp_rw [xtower_freCoeff,add_mul,Finset.sum_add_distrib]
  have hc (n : ℕ) : (if n=0 then x else if n=1 then 1 else 0)*u^n=
      (if n=0 then x else 0)+(if n=1 then u else 0) := by
    by_cases h0 : n=0
    · subst n; simp
    · by_cases h1 : n=1
      · subst n; simp
      · simp [h0,h1]
  simp_rw [hc,Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq',Finset.mem_range,show 0<J+1 by omega,
    show 1<J+1 by omega,ite_true]
  ring

theorem xlog_taylor_remainder (x r : ℝ) (hx : 0 < r ∧ r < x) (J : ℕ) (hJ : 2 ≤ J) :
  Models (fun u => xlog (x+u)) ((List.range (J+1)).map (xtower x)) r
    (x*(r/x)^(J+1)/((J+1:ℕ)*(J:ℕ)*(1-r/x))) := by
  have hxpos : 0 < x := hx.1.trans hx.2
  have hh := fre_taylor_remainder (x:ℂ) 1 r (by simpa using hxpos.le) hx.1.le
    (by simpa only [norm_one,one_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hxpos] using hx.2) J hJ
  simp only [norm_one,one_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hxpos] at hh
  refine ⟨hx.1.le,hh.2.1,?_⟩
  intro u hu
  have hmodel := hh.2.2 u hu
  rw [evalModel_xtower x u J hJ]
  dsimp only at hmodel
  have hfun : ((x:ℂ)+(u:ℂ))*Complex.log ((x:ℂ)+(u:ℂ))-((x:ℂ)+(u:ℂ))=
      ((x+u:ℝ):ℂ)*Complex.log ((x+u:ℝ):ℂ)-((x+u:ℝ):ℂ) := by push_cast; simp
  rw [hfun] at hmodel
  simp only [Complex.sub_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    Complex.log_ofReal_re,zero_mul,sub_zero] at hmodel
  unfold xlog
  convert! hmodel using 1 <;> congr 1 <;> ring

#print axioms ownPoly_cell
#print axioms cell_ub_lb
#print axioms fre_taylor_remainder
#print axioms xlog_taylor_remainder
end CatalanCore.Li2.DecayCert
