module
public import CatalanCore.Tools.VerticalResidues
public import CatalanCore.Uniform.Decay.Polygon.Deform
public import CatalanCore.Li2.Decay.Kernel
public import CatalanCore.Li2.Decay.Series
public import Mathlib.Analysis.Complex.RemovableSingularity
@[expose] public section
set_option Elab.async false
open MeasureTheory Set Filter
open scoped Topology BigOperators
namespace CatalanCore.Li2.Decay.ContourGeometry

noncomputable def sineQuotient (m : ℕ) : ℂ → ℂ :=
  dslope (fun u : ℂ => Complex.sin ((Real.pi:ℂ)*u)) (m:ℂ)

theorem sineQuotient_differentiable (m : ℕ) : Differentiable ℂ (sineQuotient m) := by
  have hs : Differentiable ℂ (fun u : ℂ => Complex.sin ((Real.pi:ℂ)*u)) := by fun_prop
  unfold sineQuotient
  rw [← differentiableOn_univ]
  exact (Complex.differentiableOn_dslope (show (univ : Set ℂ) ∈ nhds (m:ℂ) by simp)).mpr hs.differentiableOn

theorem sin_integer (m : ℕ) : Complex.sin ((Real.pi:ℂ)*(m:ℂ))=0 := by
  have he : (Real.pi:ℂ)*(m:ℂ)=(((m:ℝ)*Real.pi:ℝ):ℂ) := by push_cast; ring
  rw [he,← Complex.ofReal_sin,Real.sin_nat_mul_pi,Complex.ofReal_zero]

theorem sineQuotient_value (m : ℕ) : sineQuotient m (m:ℂ)=(Real.pi:ℂ)*(-1:ℂ)^m := by
  have hd : HasDerivAt (fun u : ℂ => Complex.sin ((Real.pi:ℂ)*u))
      (Complex.cos ((Real.pi:ℂ)*(m:ℂ))*(Real.pi:ℂ)) (m:ℂ) := by
    simpa only [Function.comp_def,id_eq,mul_one] using
      (Complex.hasDerivAt_sin ((Real.pi:ℂ)*(m:ℂ))).comp (m:ℂ) ((hasDerivAt_id (m:ℂ)).const_mul (Real.pi:ℂ))
  rw [sineQuotient,dslope_same,hd.deriv]
  have he : (Real.pi:ℂ)*(m:ℂ)=(((m:ℝ)*Real.pi:ℝ):ℂ) := by push_cast; ring
  rw [he,← Complex.ofReal_cos,Real.cos_nat_mul_pi]
  push_cast
  ring

theorem sineQuotient_mul (m : ℕ) (u : ℂ) :
    (u-(m:ℂ))*sineQuotient m u=Complex.sin ((Real.pi:ℂ)*u) := by
  have hh := sub_smul_dslope (fun u : ℂ => Complex.sin ((Real.pi:ℂ)*u)) (m:ℂ) u
  simpa only [sineQuotient,smul_eq_mul,sin_integer m,sub_zero] using hh

def poleStrip (m : ℕ) : Set ℂ := {u | (m:ℝ)-3/4 < u.re ∧ u.re < (m:ℝ)+3/4}

theorem sineQuotient_ne_zero (m : ℕ) (u : ℂ) (hu : u ∈ poleStrip m) : sineQuotient m u ≠ 0 := by
  by_cases he : u=(m:ℂ)
  · rw [he,sineQuotient_value]
    exact mul_ne_zero (by exact_mod_cast Real.pi_ne_zero) (pow_ne_zero _ (by norm_num))
  intro hq
  have hsin : Complex.sin ((Real.pi:ℂ)*u)=0 := by
    have hh := sineQuotient_mul m u
    rw [hq,mul_zero] at hh
    exact hh.symm
  obtain ⟨k,hk⟩ := Complex.sin_eq_zero_iff.mp hsin
  have hpi : (Real.pi:ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have huk : u=(k:ℂ) := by
    apply mul_left_cancel₀ hpi
    rw [hk]
    ring
  have hreal : (m:ℝ)-3/4 < (k:ℝ) ∧ (k:ℝ) < (m:ℝ)+3/4 := by
    simpa only [poleStrip,mem_setOf_eq,huk,Complex.intCast_re] using hu
  have hlo : -1 < k-(m:ℤ) := by exact_mod_cast (show (-1:ℝ) < (k:ℝ)-(m:ℝ) by linarith)
  have hhi : k-(m:ℤ) < 1 := by exact_mod_cast (show (k:ℝ)-(m:ℝ) < (1:ℝ) by linarith)
  have hkm : k=(m:ℤ) := by omega
  apply he
  rw [huk,hkm,Int.cast_natCast]
end CatalanCore.Li2.Decay.ContourGeometry
#print axioms CatalanCore.Li2.Decay.ContourGeometry.sineQuotient_ne_zero


namespace CatalanCore.Li2.Decay.ContourGeometry

noncomputable def poleAmplitude (negative : Bool) (m : ℕ) (u : ℂ) : ℂ :=
  if negative then (Real.pi:ℂ)/sineQuotient m u else
    (Real.pi:ℂ)*Complex.cos ((Real.pi:ℂ)*u)/sineQuotient m u

theorem poleStrip_open (m : ℕ) : IsOpen (poleStrip m) :=
  (isOpen_lt continuous_const Complex.continuous_re).inter (isOpen_lt Complex.continuous_re continuous_const)

theorem poleAmplitude_differentiableOn (negative : Bool) (m : ℕ) :
    DifferentiableOn ℂ (poleAmplitude negative m) (poleStrip m) := by
  intro u hu
  apply DifferentiableAt.differentiableWithinAt
  have hq := (sineQuotient_differentiable m u)
  have hqne := sineQuotient_ne_zero m u hu
  cases negative
  · change DifferentiableAt ℂ (fun u : ℂ => (Real.pi:ℂ)*Complex.cos ((Real.pi:ℂ)*u)/sineQuotient m u) u
    exact ((by fun_prop : DifferentiableAt ℂ (fun u : ℂ => (Real.pi:ℂ)*Complex.cos ((Real.pi:ℂ)*u)) u).div hq hqne)
  · change DifferentiableAt ℂ (fun u : ℂ => (Real.pi:ℂ)/sineQuotient m u) u
    exact (hasDerivAt_const u (Real.pi:ℂ)).differentiableAt.div hq hqne

theorem poleAmplitude_value (negative : Bool) (m : ℕ) :
    poleAmplitude negative m (m:ℂ)=if negative then (-1:ℂ)^m else 1 := by
  have hπ : (Real.pi:ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hs : (-1:ℂ)^m ≠ 0 := pow_ne_zero _ (by norm_num)
  have hs2 : (-1:ℂ)^m*(-1:ℂ)^m=1 := by rw [← mul_pow]; norm_num
  have he : (Real.pi:ℂ)*(m:ℂ)=(((m:ℝ)*Real.pi:ℝ):ℂ) := by push_cast; ring
  cases negative
  · simp only [poleAmplitude,Bool.false_eq_true,↓reduceIte,sineQuotient_value]
    rw [he,← Complex.ofReal_cos,Real.cos_nat_mul_pi]
    push_cast
    exact div_self (mul_ne_zero hπ hs)
  · simp only [poleAmplitude,↓reduceIte,sineQuotient_value]
    apply (div_eq_iff (mul_ne_zero hπ hs)).mpr
    calc
      _ = (Real.pi:ℂ)*((-1:ℂ)^m*(-1:ℂ)^m) := by rw [hs2,mul_one]
      _ = _ := by ring

theorem poleAmplitude_split (negative : Bool) (m : ℕ) (u : ℂ) :
    (if negative then (Real.pi:ℂ)/Complex.sin ((Real.pi:ℂ)*u) else
      (Real.pi:ℂ)*Complex.cos ((Real.pi:ℂ)*u)/Complex.sin ((Real.pi:ℂ)*u))=
        poleAmplitude negative m u/(u-(m:ℂ)) := by
  cases negative <;> simp only [poleAmplitude,Bool.false_eq_true,↓reduceIte,div_div]
  all_goals rw [mul_comm (sineQuotient m u) (u-(m:ℂ)),sineQuotient_mul]
end CatalanCore.Li2.Decay.ContourGeometry
#print axioms CatalanCore.Li2.Decay.ContourGeometry.poleAmplitude_differentiableOn
#print axioms CatalanCore.Li2.Decay.ContourGeometry.poleAmplitude_value

namespace CatalanCore.Li2.Decay.ContourGeometry
open Polynomial

noncomputable def unshiftedKernel (negative : Bool) (u : ℂ) : ℂ :=
  if negative then (Real.pi:ℂ)/Complex.sin ((Real.pi:ℂ)*u) else
    (Real.pi:ℂ)*Complex.cos ((Real.pi:ℂ)*u)/Complex.sin ((Real.pi:ℂ)*u)
noncomputable def unshiftedKernelPrime (negative : Bool) (u : ℂ) : ℂ :=
  if negative then -(Real.pi:ℂ)^2*Complex.cos ((Real.pi:ℂ)*u)/Complex.sin ((Real.pi:ℂ)*u)^2 else
    -(Real.pi:ℂ)^2/Complex.sin ((Real.pi:ℂ)*u)^2

theorem unshiftedKernel_hasDerivAt (negative : Bool) (u : ℂ)
    (hsin : Complex.sin ((Real.pi:ℂ)*u) ≠ 0) :
    HasDerivAt (unshiftedKernel negative) (unshiftedKernelPrime negative u) u := by
  have hs : HasDerivAt (fun w : ℂ => Complex.sin ((Real.pi:ℂ)*w))
      (Complex.cos ((Real.pi:ℂ)*u)*(Real.pi:ℂ)) u := by
    simpa only [Function.comp_def,id_eq,mul_one] using
      (Complex.hasDerivAt_sin ((Real.pi:ℂ)*u)).comp u ((hasDerivAt_id u).const_mul (Real.pi:ℂ))
  have hc : HasDerivAt (fun w : ℂ => (Real.pi:ℂ)*Complex.cos ((Real.pi:ℂ)*w))
      ((Real.pi:ℂ)*(-Complex.sin ((Real.pi:ℂ)*u)*(Real.pi:ℂ))) u := by
    simpa only [Function.comp_def,id_eq,mul_one] using
      (((Complex.hasDerivAt_cos ((Real.pi:ℂ)*u)).comp u ((hasDerivAt_id u).const_mul (Real.pi:ℂ))).const_mul (Real.pi:ℂ))
  cases negative
  · convert hc.div hs hsin using 1
    · funext w
      rfl
    · simp only [unshiftedKernelPrime,Bool.false_eq_true,↓reduceIte]
      field_simp
      linear_combination (Complex.sin_sq_add_cos_sq ((Real.pi:ℂ)*u))
  · convert (hasDerivAt_const u (Real.pi:ℂ)).div hs hsin using 1
    · funext w
      rfl
    · simp only [unshiftedKernelPrime,↓reduceIte,zero_mul,zero_sub]
      ring

noncomputable def rationalCore (n : ℕ) (T : ℂ[X]) (u : ℂ) : ℂ := u*weight n u*T.eval u

theorem rationalCore_differentiableOn (n m : ℕ) (T : ℂ[X]) :
    DifferentiableOn ℂ (rationalCore n T) (poleStrip m) := by
  have hD (k : ℕ) : Differentiable ℂ (Dprod k) := by unfold Dprod; fun_prop
  intro u hu
  have hden : Dprod (4*n) u ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    intro he
    have hh := congrArg Complex.re he
    simp only [Complex.add_re,Complex.natCast_re,Complex.zero_re] at hh
    have hjR : (1:ℝ) ≤ j := by exact_mod_cast (Finset.mem_Icc.mp hj).1
    have hmR : (0:ℝ) ≤ m := Nat.cast_nonneg _
    have huR := hu.1
    linarith
  have hw : DifferentiableAt ℂ (weight n) u := by
    unfold weight
    exact ((hD n u).pow 3).div (hD (4*n) u) hden
  exact ((((hasDerivAt_id u).differentiableAt.mul hw).mul (T.hasDerivAt u).differentiableAt)).differentiableWithinAt

theorem poleNumerator_differentiableOn (negative : Bool) (n m : ℕ) (T : ℂ[X]) (L : ℂ) :
    DifferentiableOn ℂ
      (CatalanCore.Tools.VerticalResidues.exponentialPoleNumerator (rationalCore n T)
        (poleAmplitude negative m) L (m:ℂ)) (poleStrip m) := by
  have hR := rationalCore_differentiableOn n m T
  have hA := poleAmplitude_differentiableOn negative m
  have hdA := hA.deriv (poleStrip_open m)
  have hh : DifferentiableOn ℂ (fun u : ℂ => u-(m:ℂ)) (poleStrip m) := by fun_prop
  have he : DifferentiableOn ℂ (fun u : ℂ => Complex.exp (L*u)) (poleStrip m) := by fun_prop
  exact (hR.mul he).mul ((hA.sub (hh.mul hdA)).sub ((hh.const_mul L).mul hA))

theorem poleNumerator_deriv (negative : Bool) (n m : ℕ) (T : ℂ[X]) (L : ℂ) :
    deriv (CatalanCore.Tools.VerticalResidues.exponentialPoleNumerator (rationalCore n T)
      (poleAmplitude negative m) L (m:ℂ)) (m:ℂ)=
        (if negative then (-1:ℂ)^m else 1)*Complex.exp (L*(m:ℂ))*deriv (rationalCore n T) (m:ℂ) := by
  have hmS : (m:ℂ) ∈ poleStrip m := by
    change (m:ℝ)-3/4 < (m:ℂ).re ∧ (m:ℂ).re < (m:ℝ)+3/4
    simp only [Complex.natCast_re]
    constructor <;> linarith
  have hn := (poleStrip_open m).mem_nhds hmS
  rw [CatalanCore.Tools.VerticalResidues.exponentialPoleNumerator_deriv _ _ _ _
    ((rationalCore_differentiableOn n m T).differentiableAt hn)
    ((poleAmplitude_differentiableOn negative m).differentiableAt hn)
    (((poleAmplitude_differentiableOn negative m).deriv (poleStrip_open m)).differentiableAt hn),
    poleAmplitude_value]
end CatalanCore.Li2.Decay.ContourGeometry
#print axioms CatalanCore.Li2.Decay.ContourGeometry.poleNumerator_deriv


namespace CatalanCore.Li2.Decay.ContourGeometry
open Polynomial

theorem rationalCore_polynomial_bound (n : ℕ) (T : ℂ[X]) :
    ∃ B : ℝ, 0 < B ∧ ∀ u : ℂ, -(1/4:ℝ) ≤ u.re →
      ‖rationalCore n T u‖ ≤ B*(1+‖u‖)^(3*n+1+T.natDegree) := by
  classical
  let CT : ℝ := ∑ k ∈ T.support, ‖T.coeff k‖
  have hCT : 0 ≤ CT := Finset.sum_nonneg fun k hk => norm_nonneg _
  let B : ℝ := (n+1:ℝ)^(3*n)/((3/4:ℝ)^(4*n))*(CT+1)
  refine ⟨B,by dsimp only [B]; positivity,?_⟩
  intro u hu
  have hr : 0 ≤ ‖u‖ := norm_nonneg _
  have hr1 : 1 ≤ 1+‖u‖ := by linarith
  have hT : ‖T.eval u‖ ≤ CT*(1+‖u‖)^T.natDegree := by
    rw [Polynomial.eval_eq_sum]
    unfold Polynomial.sum
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ k ∈ T.support, ‖T.coeff k‖*(1+‖u‖)^T.natDegree := by
        apply Finset.sum_le_sum
        intro k hk
        rw [norm_mul,norm_pow]
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        apply (pow_le_pow_left₀ hr (by linarith : ‖u‖ ≤ 1+‖u‖) k).trans
        exact pow_le_pow_right₀ hr1 (T.le_natDegree_of_ne_zero (Polynomial.mem_support_iff.mp hk))
      _ = _ := by dsimp only [CT]; rw [Finset.sum_mul]
  have hnum : ‖Dprod n u‖ ≤ ((n+1:ℝ)*(1+‖u‖))^n := by
    unfold Dprod
    rw [norm_prod]
    calc
      _ ≤ ∏ j ∈ Finset.Icc 1 n, ((n+1:ℝ)*(1+‖u‖)) := by
        apply Finset.prod_le_prod₀ (fun j hj => norm_nonneg _)
        intro j hj
        have hjR : (j:ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hj).2
        have hh := norm_add_le u (j:ℂ)
        rw [Complex.norm_natCast] at hh
        have hnR : (0:ℝ) ≤ n := Nat.cast_nonneg _
        nlinarith
      _ = _ := by simp
  have hden : (3/4:ℝ)^(4*n) ≤ ‖Dprod (4*n) u‖ := by
    unfold Dprod
    rw [norm_prod]
    calc
      _ = ∏ j ∈ Finset.Icc 1 (4*n), (3/4:ℝ) := by simp [div_pow]
      _ ≤ _ := by
        apply Finset.prod_le_prod₀ (fun j hj => by norm_num)
        intro j hj
        have hjR : (1:ℝ) ≤ j := by exact_mod_cast (Finset.mem_Icc.mp hj).1
        have hh := (le_abs_self (u+(j:ℂ)).re).trans (Complex.abs_re_le_norm (u+(j:ℂ)))
        simp only [Complex.add_re,Complex.natCast_re] at hh
        linarith
  have hinv : ‖Dprod (4*n) u‖⁻¹ ≤ ((3/4:ℝ)^(4*n))⁻¹ :=
    by simpa only [one_div] using one_div_le_one_div_of_le (by positivity : 0 < (3/4:ℝ)^(4*n)) hden
  have hraw : ‖rationalCore n T u‖ ≤ (1+‖u‖)*(((n+1:ℝ)*(1+‖u‖))^n)^3*
      ((3/4:ℝ)^(4*n))⁻¹*(CT*(1+‖u‖)^T.natDegree) := by
    unfold rationalCore weight
    rw [norm_mul,norm_mul,norm_div,norm_pow,div_eq_mul_inv]
    have hcube := pow_le_pow_left₀ (norm_nonneg _) hnum 3
    have h1 := mul_le_mul (show ‖u‖ ≤ 1+‖u‖ by linarith) hcube
      (pow_nonneg (norm_nonneg _) 3) (by positivity : 0 ≤ 1+‖u‖)
    have h2 := mul_le_mul h1 hinv (inv_nonneg.mpr (norm_nonneg _)) (by positivity)
    have h3 := mul_le_mul h2 hT (norm_nonneg _) (by positivity)
    convert h3 using 1 <;> ring
  have he : (1+‖u‖)*(((n+1:ℝ)*(1+‖u‖))^n)^3*
      ((3/4:ℝ)^(4*n))⁻¹*(CT*(1+‖u‖)^T.natDegree)=
      ((n+1:ℝ)^(3*n)/((3/4:ℝ)^(4*n))*CT)*(1+‖u‖)^(3*n+1+T.natDegree) := by
    simp only [mul_pow,← pow_mul]
    simp only [pow_add,pow_one,div_eq_mul_inv]
    have hmul : n*3=3*n := by omega
    rw [hmul]
    ring
  rw [he] at hraw
  apply hraw.trans
  dsimp only [B]
  gcongr
  linarith
end CatalanCore.Li2.Decay.ContourGeometry
#print axioms CatalanCore.Li2.Decay.ContourGeometry.rationalCore_polynomial_bound


namespace CatalanCore.Li2.Decay.ContourGeometry
open Polynomial
open CatalanCore.Tools.VerticalResidues

noncomputable def branchDensity (negative upper : Bool) (n : ℕ) (T : ℂ[X]) (L u : ℂ) : ℂ :=
  rationalCore n T u*Complex.exp (L*u)*
    (-unshiftedKernelPrime negative u-L*(unshiftedKernel negative u+
      (if negative then 0 else if upper then (Real.pi:ℂ)*Complex.I else -(Real.pi:ℂ)*Complex.I)))

theorem unshifted_density_representation (negative : Bool) (n m : ℕ) (T : ℂ[X]) (L u : ℂ)
    (hu : u ∈ poleStrip m) (hne : u ≠ (m:ℂ)) :
    rationalCore n T u*Complex.exp (L*u)*
      (-unshiftedKernelPrime negative u-L*unshiftedKernel negative u)=
        exponentialPoleNumerator (rationalCore n T) (poleAmplitude negative m) L (m:ℂ) u/(u-(m:ℂ))^2 := by
  have hsin : Complex.sin ((Real.pi:ℂ)*u) ≠ 0 := by
    rw [← sineQuotient_mul m u]
    exact mul_ne_zero (sub_ne_zero.mpr hne) (sineQuotient_ne_zero m u hu)
  have hfun : (fun w : ℂ => poleAmplitude negative m w/(w-(m:ℂ)))=unshiftedKernel negative := by
    funext w
    exact (poleAmplitude_split negative m w).symm
  have hh := exponentialPoleNumerator_split (rationalCore n T) (poleAmplitude negative m) L (m:ℂ) u
    ((poleAmplitude_differentiableOn negative m).differentiableAt ((poleStrip_open m).mem_nhds hu)) hne
  rw [hfun,(unshiftedKernel_hasDerivAt negative u hsin).deriv] at hh
  have hpoint := congrFun hfun u
  rw [hpoint] at hh
  exact hh

theorem branchDensity_representation (negative upper : Bool) (n m : ℕ) (T : ℂ[X]) (L u : ℂ)
    (hu : u ∈ poleStrip m) (hne : u ≠ (m:ℂ)) :
    branchDensity negative upper n T L u=
      exponentialPoleNumerator (rationalCore n T) (poleAmplitude negative m) L (m:ℂ) u/(u-(m:ℂ))^2+
        (if negative then 0 else if upper then -L*(Real.pi:ℂ)*Complex.I else L*(Real.pi:ℂ)*Complex.I)*
          (rationalCore n T u*Complex.exp (L*u)) := by
  rw [← unshifted_density_representation negative n m T L u hu hne]
  cases negative <;> cases upper <;> simp only [branchDensity,Bool.false_eq_true,↓reduceIte] <;> ring

theorem pole_coefficient (z : ℝ) (hz : ValidZ z) (m : ℕ) :
    (if z < 0 then (-1:ℂ)^m else 1)*Complex.exp ((Real.log |z|:ℂ)*(m:ℂ))=(z:ℂ)^m := by
  have he : Complex.exp ((Real.log |z|:ℂ)*(m:ℂ))=((|z|:ℝ):ℂ)^m := by
    rw [mul_comm,Complex.exp_nat_mul,← Complex.ofReal_exp,Real.exp_log hz.1]
  rw [he]
  by_cases hneg : z < 0
  · rw [if_pos hneg,abs_of_neg hneg]
    push_cast
    rw [← mul_pow]
    congr 1
    ring
  · rw [if_neg hneg,one_mul,abs_of_nonneg (le_of_not_gt hneg)]
end CatalanCore.Li2.Decay.ContourGeometry
#print axioms CatalanCore.Li2.Decay.ContourGeometry.branchDensity_representation
#print axioms CatalanCore.Li2.Decay.ContourGeometry.pole_coefficient


namespace CatalanCore.Li2.Decay.ContourGeometry
open Polynomial

noncomputable def densityCore (z : ℝ) (n : ℕ) (T : ℂ[X]) (u : ℂ) : ℂ :=
  rationalCore n T u*Complex.exp ((Real.log |z|:ℂ)*u)*kernel z u

theorem branchDensity_negative (z : ℝ) (hz : z < 0) (upper : Bool) (n : ℕ) (T : ℂ[X]) (u : ℂ) :
    branchDensity true upper n T (Real.log |z|:ℂ) u=densityCore z n T u := by
  simp only [branchDensity,densityCore,unshiftedKernel,unshiftedKernelPrime,kernel,
    basicKernel,basicKernelPrime,if_pos hz,↓reduceIte,add_zero]

theorem branchDensity_physical (z : ℝ) (upper : Bool) (n : ℕ) (T : ℂ[X]) (u : ℂ)
    (hside : if upper then 0 ≤ u.im else u.im < 0) :
    branchDensity (decide (z<0)) upper n T (Real.log |z|:ℂ) u=densityCore z n T u := by
  cases upper with
  | false =>
    have hi : ¬0 ≤ u.im := not_le.mpr hside
    by_cases hz : z<0 <;> simp [branchDensity,densityCore,unshiftedKernel,unshiftedKernelPrime,
      kernel,basicKernel,basicKernelPrime,hz,hi] <;> ring
  | true =>
    have hi : 0 ≤ u.im := hside
    by_cases hz : z<0 <;> simp [branchDensity,densityCore,unshiftedKernel,unshiftedKernelPrime,
      kernel,basicKernel,basicKernelPrime,hz,hi] <;> ring

theorem densityCore_radial_bound (z : ℝ) (hz : ValidZ z) (n : ℕ) (T : ℂ[X]) :
    ∃ M a : ℝ, 0 < M ∧ 0 < a ∧ ∀ u : ℂ, -(1/4:ℝ) ≤ u.re →
      ((∃ N : ℕ, u.re=(N:ℝ)+1/2) ∨ 1 ≤ |u.im|) →
      ‖densityCore z n T u‖ ≤ M*Real.exp (-a*‖u‖) := by
  obtain ⟨B,hB,hR⟩ := rationalCore_polynomial_bound n T
  obtain ⟨C,hC,hK⟩ := kernel_bound
  let L := Real.log |z|
  have hL : L < 0 := Real.log_neg hz.1 hz.2
  have hκ : 0 < kappaRate z := by unfold kappaRate; split_ifs <;> positivity
  let a := min (-L) (kappaRate z)
  have ha : 0 < a := lt_min (by linarith) hκ
  have haL : a ≤ -L := min_le_left _ _
  have haκ : a ≤ kappaRate z := min_le_right _ _
  obtain ⟨D,hD,hpow⟩ := CatalanCore.Decay.CurveFamily.pow_one_add_le_exp (3*n+1+T.natDegree)
    (show 0 < a/2 by positivity)
  let c0 := (a-L)/4
  let M := B*C*(1+|L|)*(D+1)*Real.exp c0
  refine ⟨M,a/2,by dsimp only [M]; positivity,by positivity,?_⟩
  intro u hu hguard
  have hr : 0 ≤ ‖u‖ := norm_nonneg _
  have hx : 0 ≤ u.re+1/4 := by linarith
  have habs : |u.re| ≤ u.re+1/2 := abs_le.mpr ⟨by linarith,by linarith⟩
  have hnorm : ‖u‖ ≤ u.re+1/2+|u.im| := by
    have hh := Complex.norm_le_abs_re_add_abs_im u
    linarith
  have hlin : L*u.re-kappaRate z*|u.im| ≤ c0-a*‖u‖ := by
    have h1 := mul_le_mul_of_nonneg_right haL hx
    have h2 := mul_le_mul_of_nonneg_right haκ (abs_nonneg u.im)
    have h3 := mul_le_mul_of_nonneg_left hnorm ha.le
    dsimp only [c0]
    nlinarith
  have hraw : ‖densityCore z n T u‖ ≤
      B*C*(1+|L|)*(1+‖u‖)^(3*n+1+T.natDegree)*Real.exp (L*u.re-kappaRate z*|u.im|) := by
    unfold densityCore
    rw [norm_mul,norm_mul,Complex.norm_exp]
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    calc
      _ ≤ (B*(1+‖u‖)^(3*n+1+T.natDegree))*Real.exp (L*u.re)*
        (C*(1+|L|)*Real.exp (-kappaRate z*|u.im|)) := by
          exact mul_le_mul (mul_le_mul_of_nonneg_right (hR u hu) (Real.exp_pos _).le)
            (hK z hz u hguard) (norm_nonneg _) (by positivity)
      _ = _ := by rw [sub_eq_add_neg,Real.exp_add]; ring
  have he : Real.exp ((a/2)*‖u‖)*Real.exp (-a*‖u‖)=Real.exp (-(a/2)*‖u‖) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ ≤ B*C*(1+|L|)*(1+‖u‖)^(3*n+1+T.natDegree)*Real.exp (c0-a*‖u‖) := by
      apply hraw.trans
      gcongr
    _ = (B*C*(1+|L|)*Real.exp c0)*((1+‖u‖)^(3*n+1+T.natDegree)*Real.exp (-a*‖u‖)) := by
      rw [sub_eq_add_neg,Real.exp_add]
      ring
    _ ≤ (B*C*(1+|L|)*Real.exp c0)*((D*Real.exp ((a/2)*‖u‖))*Real.exp (-a*‖u‖)) := by
      gcongr
      exact hpow ‖u‖ hr
    _ = (B*C*(1+|L|)*D*Real.exp c0)*Real.exp (-(a/2)*‖u‖) := by
      calc
        _ = (B*C*(1+|L|)*D*Real.exp c0)*(Real.exp ((a/2)*‖u‖)*Real.exp (-a*‖u‖)) := by ring
        _ = _ := by rw [he]
    _ ≤ _ := by dsimp only [M]; gcongr; linarith
end CatalanCore.Li2.Decay.ContourGeometry
#print axioms CatalanCore.Li2.Decay.ContourGeometry.densityCore_radial_bound


namespace CatalanCore.Li2.Decay.ContourGeometry
open Polynomial

theorem densityCore_measurable (z : ℝ) (n : ℕ) (T : ℂ[X]) : Measurable (densityCore z n T) := by
  have hT : Measurable (fun u : ℂ => T.eval u) := T.continuous.measurable
  have hshift : Measurable (fun u : ℂ => if 0 ≤ u.im then (Real.pi:ℂ)*Complex.I else -(Real.pi:ℂ)*Complex.I) :=
    Measurable.ite (isClosed_le continuous_const Complex.continuous_im).measurableSet measurable_const measurable_const
  unfold densityCore rationalCore kernel basicKernelPrime basicKernel weight Dprod
  by_cases hz : z<0
  · simp only [if_pos hz]
    fun_prop
  · simp only [if_neg hz]
    fun_prop

noncomputable def upLine (z : ℝ) (n : ℕ) (T : ℂ[X]) (N : ℕ) (y : ℝ) : ℂ :=
  Complex.I*densityCore z n T ((((N:ℝ)+1/2:ℝ):ℂ)+(y:ℂ)*Complex.I)

theorem upLine_geometric_bound (z : ℝ) (hz : ValidZ z) (n : ℕ) (T : ℂ[X]) :
    ∃ C q : ℝ, 0 < C ∧ 0 < q ∧ q < 1 ∧ ∀ N : ℕ,
      Integrable (upLine z n T N) ∧ ‖∫ y : ℝ, upLine z n T N y‖ ≤ C*q^N := by
  obtain ⟨M,a,hM,ha,hbound⟩ := densityCore_radial_bound z hz n T
  obtain ⟨D,hD,hpow⟩ := CatalanCore.Decay.CurveFamily.pow_one_add_le_exp 2
    (show 0 < a/2 by positivity)
  let J : ℝ := ∫ y : ℝ, (1+y^2)⁻¹
  have hJ : 0 ≤ J := integral_nonneg fun y => by positivity
  let q := Real.exp (-a/2)
  have hq : 0 < q := Real.exp_pos _
  have hq1 : q < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  let C := M*(D+1)*(J+1)
  refine ⟨C,q,by dsimp only [C]; positivity,hq,hq1,?_⟩
  intro N
  let v : ℝ := (N:ℝ)+1/2
  have hv : 0 ≤ v := by dsimp only [v]; positivity
  have hscalar : 0 ≤ M*D*Real.exp (-(a/2)*v) := by positivity
  have hpoint (y : ℝ) : ‖upLine z n T N y‖ ≤
      (M*D*Real.exp (-(a/2)*v))*(1+y^2)⁻¹ := by
    let u : ℂ := (v:ℂ)+(y:ℂ)*Complex.I
    have huRe : u.re=v := by simp only [u,Complex.add_re,Complex.ofReal_re,Complex.mul_I_re,Complex.ofReal_im,neg_zero,add_zero]
    have huIm : u.im=y := by simp only [u,Complex.add_im,Complex.ofReal_im,Complex.mul_I_im,Complex.ofReal_re,zero_add]
    have hre : -(1/4:ℝ) ≤ u.re := by rw [huRe]; linarith
    have hguard : (∃ k : ℕ, u.re=(k:ℝ)+1/2) ∨ 1 ≤ |u.im| := Or.inl ⟨N,huRe⟩
    have hh := hbound u hre hguard
    have hgap : v+|y| ≤ 2*‖u‖ := by
      have h1 := Complex.abs_re_le_norm u
      have h2 := Complex.abs_im_le_norm u
      rw [huRe,abs_of_nonneg hv] at h1
      rw [huIm] at h2
      linarith
    have hcauchy : Real.exp (-(a/2)*|y|) ≤ D*(1+y^2)⁻¹ := by
      have hs : 1+y^2 ≤ (1+|y|)^2 := by nlinarith [sq_abs y,abs_nonneg y]
      have hp := hpow |y| (abs_nonneg y)
      have hm := mul_le_mul_of_nonneg_left (hs.trans hp) (Real.exp_pos (-(a/2)*|y|)).le
      have he : Real.exp (-(a/2)*|y|)*(D*Real.exp ((a/2)*|y|))=D := by
        rw [show -(a/2)*|y|= -((a/2)*|y|) by ring,Real.exp_neg]
        field_simp
      rw [he] at hm
      have hh' := (le_div_iff₀ (by positivity : 0 < 1+y^2)).mpr hm
      simpa only [div_eq_mul_inv] using hh'
    change ‖Complex.I*densityCore z n T u‖ ≤ _
    rw [norm_mul,Complex.norm_I,one_mul]
    calc
      _ ≤ M*Real.exp (-a*‖u‖) := hh
      _ ≤ M*Real.exp (-(a/2)*v)*Real.exp (-(a/2)*|y|) := by
        rw [mul_assoc,← Real.exp_add]
        gcongr
        nlinarith
      _ ≤ M*Real.exp (-(a/2)*v)*(D*(1+y^2)⁻¹) :=
        mul_le_mul_of_nonneg_left hcauchy (by positivity)
      _ = _ := by ring
  have hmeas : AEStronglyMeasurable (upLine z n T N) := by
    apply Measurable.aestronglyMeasurable
    exact measurable_const.mul ((densityCore_measurable z n T).comp (by fun_prop))
  have hdom : Integrable (fun y : ℝ => (M*D*Real.exp (-(a/2)*v))*(1+y^2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul _
  have hi : Integrable (upLine z n T N) := hdom.mono' hmeas (Eventually.of_forall hpoint)
  refine ⟨hi,?_⟩
  have hnorm : ‖∫ y : ℝ, upLine z n T N y‖ ≤ (M*D*Real.exp (-(a/2)*v))*J := by
    apply (norm_integral_le_integral_norm _).trans
    have hh := integral_mono hi.norm hdom hpoint
    rw [integral_const_mul] at hh
    exact hh
  have heq : Real.exp (-(a/2)*v)=Real.exp (-a/4)*q^N := by
    dsimp only [v,q]
    rw [← Real.exp_nat_mul,← Real.exp_add]
    congr 1
    ring
  have hexp : Real.exp (-a/4) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  rw [heq] at hnorm
  have hcoef : M*D*J ≤ C := by
    dsimp only [C]
    gcongr <;> linarith
  apply hnorm.trans
  calc
    _ = (M*D*J)*Real.exp (-a/4)*q^N := by ring
    _ ≤ C*1*q^N := mul_le_mul_of_nonneg_right
      (mul_le_mul hcoef hexp (Real.exp_pos _).le (by dsimp only [C]; positivity)) (pow_nonneg hq.le N)
    _ = _ := by rw [mul_one]
end CatalanCore.Li2.Decay.ContourGeometry
#print axioms CatalanCore.Li2.Decay.ContourGeometry.upLine_geometric_bound


namespace CatalanCore.Li2.Decay.ContourGeometry
open Polynomial

theorem poleNumerator_residue (z : ℝ) (hz : ValidZ z) (n m : ℕ) (T : ℂ[X]) :
    deriv (CatalanCore.Tools.VerticalResidues.exponentialPoleNumerator (rationalCore n T)
      (poleAmplitude (decide (z<0)) m) (Real.log |z|:ℂ) (m:ℂ)) (m:ℂ)=
        (z:ℂ)^m*deriv (rationalCore n T) (m:ℂ) := by
  rw [poleNumerator_deriv]
  have he : (if decide (z<0) then (-1:ℂ)^m else 1)=(if z<0 then (-1:ℂ)^m else 1) := by
    by_cases hh : z<0 <;> simp [hh]
  rw [he,pole_coefficient z hz m]

theorem branch_horizontal_bound (z : ℝ) (hz : ValidZ z) (n : ℕ) (T : ℂ[X]) :
    ∃ C : ℝ, 0 < C ∧ ∀ H : ℝ, 1 ≤ H → ∀ x : ℝ, 0 ≤ x →
      ‖branchDensity (decide (z<0)) false n T (Real.log |z|:ℂ) ((x:ℂ)-(H:ℂ)*Complex.I)‖ ≤ C/H ∧
      ‖branchDensity (decide (z<0)) true n T (Real.log |z|:ℂ) ((x:ℂ)+(H:ℂ)*Complex.I)‖ ≤ C/H := by
  obtain ⟨M,a,hM,ha,hbound⟩ := densityCore_radial_bound z hz n T
  obtain ⟨D,hD,hpow⟩ := CatalanCore.Decay.CurveFamily.pow_one_add_le_exp 1 ha
  let C := M*(D+1)
  refine ⟨C,by dsimp only [C]; positivity,?_⟩
  intro H hH x hx
  have hH0 : 0 < H := by linarith
  have he : Real.exp (-a*H) ≤ (D+1)/H := by
    have hp := hpow H hH0.le
    simp only [pow_one] at hp
    have hm := mul_le_mul_of_nonneg_right (show H ≤ D*Real.exp (a*H) by linarith) (Real.exp_pos (-a*H)).le
    have hcancel : D*Real.exp (a*H)*Real.exp (-a*H)=D := by
      rw [mul_assoc, ← Real.exp_add]
      have hh : a*H + -a*H = 0 := by ring
      rw [hh, Real.exp_zero, mul_one]
    rw [hcancel] at hm
    apply (le_div_iff₀ hH0).mpr
    nlinarith
  have hcommon (u : ℂ) (huRe : u.re=x) (huIm : |u.im|=H) : ‖densityCore z n T u‖ ≤ C/H := by
    have hh := hbound u (by rw [huRe]; linarith) (Or.inr (by rw [huIm]; exact hH))
    have hnorm : H ≤ ‖u‖ := by rw [← huIm]; exact Complex.abs_im_le_norm u
    calc
      _ ≤ M*Real.exp (-a*‖u‖) := hh
      _ ≤ M*Real.exp (-a*H) := mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hnorm (neg_nonpos.mpr ha.le))) hM.le
      _ ≤ M*((D+1)/H) := mul_le_mul_of_nonneg_left he hM.le
      _ = _ := by dsimp only [C]; ring
  constructor
  · rw [branchDensity_physical z false n T _ (by
      change ((x:ℂ)-(H:ℂ)*Complex.I).im < 0
      simp only [Complex.sub_im,Complex.ofReal_im,Complex.mul_I_im,Complex.ofReal_re,zero_sub]
      linarith)]
    apply hcommon
    · simp
    · simp [abs_of_pos hH0]
  · rw [branchDensity_physical z true n T _ (by
      change 0 ≤ ((x:ℂ)+(H:ℂ)*Complex.I).im
      simp only [Complex.add_im,Complex.ofReal_im,Complex.mul_I_im,Complex.ofReal_re,zero_add]
      linarith)]
    apply hcommon
    · simp
    · simp [abs_of_pos hH0]
end CatalanCore.Li2.Decay.ContourGeometry
#print axioms CatalanCore.Li2.Decay.ContourGeometry.branch_horizontal_bound

namespace CatalanCore.Li2.Decay.ContourGeometry
open Polynomial
open CatalanCore.Tools.VerticalResidues

theorem closed_strip_mem (N : ℕ) (u : ℂ)
    (hu : u.re ∈ Icc ((N:ℝ)+1/2) (((N+1:ℕ):ℝ)+1/2)) : u ∈ poleStrip (N+1) := by
  change ((N+1:ℕ):ℝ)-3/4 < u.re ∧ u.re < ((N+1:ℕ):ℝ)+3/4
  simp only [Nat.cast_add,Nat.cast_one] at hu ⊢
  constructor <;> linarith [hu.1,hu.2]

theorem negative_unit_strip (z : ℝ) (hz : ValidZ z) (hneg : z < 0)
    (n N : ℕ) (T : ℂ[X]) :
    (∫ y : ℝ, upLine z n T N y)-(∫ y : ℝ, upLine z n T (N+1) y)=
      -((2*Real.pi:ℂ)*Complex.I)*(z:ℂ)^(N+1)*deriv (rationalCore n T) (((N+1:ℕ):ℂ)) := by
  let a : ℝ := (N:ℝ)+1/2
  let b : ℝ := ((N+1:ℕ):ℝ)+1/2
  let m : ℕ := N+1
  let L : ℂ := (Real.log |z|:ℂ)
  let g := exponentialPoleNumerator (rationalCore n T) (poleAmplitude true m) L (m:ℂ)
  obtain ⟨C,hC,hhor⟩ := branch_horizontal_bound z hz n T
  obtain ⟨CL,q,hCL,hq,hq1,hline⟩ := upLine_geometric_bound z hz n T
  have hap : a < (m:ℝ) := by dsimp only [a,m]; push_cast; linarith
  have hpb : (m:ℝ) < b := by dsimp only [b,m]; linarith
  have hstrip : ∀ u : ℂ, u.re ∈ Icc a b → u ∈ poleStrip m := closed_strip_mem N
  have hF : ∀ u ∈ poleStrip m, u ≠ ((m:ℝ):ℂ) →
      densityCore z n T u=g u/(u-((m:ℝ):ℂ))^2 := by
    intro u hu hne
    have hh := branchDensity_representation true true n m T L u hu (by simpa only [Complex.ofReal_natCast] using hne)
    rw [branchDensity_negative z hneg true n T u] at hh
    simpa only [↓reduceIte,zero_mul,add_zero,Complex.ofReal_natCast,g,L] using hh
  have hdec : ∀ H : ℝ, 1 ≤ H → ∀ x ∈ Icc a b,
      ‖densityCore z n T ((x:ℂ)-(H:ℂ)*Complex.I)‖ ≤ C/H ∧
      ‖densityCore z n T ((x:ℂ)+(H:ℂ)*Complex.I)‖ ≤ C/H := by
    intro H hH x hx
    have hx0 : 0 ≤ x := by have hnR := Nat.cast_nonneg N (α := ℝ); have hh := hx.1; dsimp only [a] at hh; linarith
    have hh := hhor H hH x hx0
    have hbool : decide (z<0)=true := by simp [hneg]
    simpa only [hbool,branchDensity_negative z hneg] using hh
  have hia : Integrable (fun y : ℝ => Complex.I*densityCore z n T ((a:ℂ)+(y:ℂ)*Complex.I)) :=
    (hline N).1
  have hib : Integrable (fun y : ℝ => Complex.I*densityCore z n T ((b:ℂ)+(y:ℂ)*Complex.I)) :=
    (hline (N+1)).1
  have hh := vertical_double_pole (densityCore z n T) g (poleStrip m) a b (m:ℝ) C hap hpb
    (poleStrip_open m) hstrip (poleNumerator_differentiableOn true n m T L) hF hia hib hdec
  simp only [Complex.ofReal_natCast] at hh
  have hres : deriv g (m:ℂ)=(z:ℂ)^m*deriv (rationalCore n T) (m:ℂ) := by
    have hg := poleNumerator_residue z hz n m T
    have hbool : decide (z<0)=true := by simp [hneg]
    simpa only [hbool,g,L] using hg
  rw [hres] at hh
  simpa only [upLine,a,b,m,mul_assoc] using hh
end CatalanCore.Li2.Decay.ContourGeometry
#print axioms CatalanCore.Li2.Decay.ContourGeometry.negative_unit_strip

namespace CatalanCore.Li2.Decay.ContourGeometry
open Polynomial
noncomputable def branchLine (z : ℝ) (upper : Bool) (n : ℕ) (T : ℂ[X]) (N : ℕ) (y : ℝ) : ℂ :=
  Complex.I*branchDensity (decide (z<0)) upper n T (Real.log |z|:ℂ)
    (((((N:ℝ)+1/2):ℝ):ℂ)+(y:ℂ)*Complex.I)

theorem branchLine_upper_ae (z : ℝ) (n : ℕ) (T : ℂ[X]) (N : ℕ) :
    branchLine z true n T N =ᵐ[volume.restrict (Ioi (0:ℝ))] upLine z n T N := by
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  dsimp only [branchLine,upLine]
  rw [branchDensity_physical z true n T _ (by simpa using hy.le)]

theorem branchLine_lower_ae (z : ℝ) (n : ℕ) (T : ℂ[X]) (N : ℕ) :
    branchLine z false n T N =ᵐ[volume.restrict (Iic (0:ℝ))] upLine z n T N := by
  have hn : ∀ᵐ y : ℝ, y ≠ 0 := by simp [ae_iff]
  filter_upwards [ae_restrict_mem measurableSet_Iic,ae_restrict_of_ae hn] with y hy hne
  dsimp only [branchLine,upLine]
  rw [branchDensity_physical z false n T _ (by
    have hlt : y < 0 := lt_of_le_of_ne hy hne
    simpa using hlt)]

theorem branchLine_integrable (z : ℝ) (hz : ValidZ z) (n : ℕ) (T : ℂ[X]) (N : ℕ) :
    IntegrableOn (branchLine z true n T N) (Ioi 0) ∧
    IntegrableOn (branchLine z false n T N) (Iic 0) := by
  obtain ⟨C,q,hC,hq,hq1,hh⟩ := upLine_geometric_bound z hz n T
  exact ⟨(hh N).1.integrableOn.congr (branchLine_upper_ae z n T N).symm,
    (hh N).1.integrableOn.congr (branchLine_lower_ae z n T N).symm⟩

theorem branchLine_integral (z : ℝ) (hz : ValidZ z) (n : ℕ) (T : ℂ[X]) (N : ℕ) :
    (∫ y in Ioi (0:ℝ), branchLine z true n T N y)+
    (∫ y in Iic (0:ℝ), branchLine z false n T N y)=∫ y : ℝ, upLine z n T N y := by
  rw [integral_congr_ae (branchLine_upper_ae z n T N),
    integral_congr_ae (branchLine_lower_ae z n T N),add_comm]
  obtain ⟨C,q,hC,hq,hq1,hh⟩ := upLine_geometric_bound z hz n T
  exact intervalIntegral.integral_Iic_add_Ioi (hh N).1.integrableOn (hh N).1.integrableOn
end CatalanCore.Li2.Decay.ContourGeometry
#print axioms CatalanCore.Li2.Decay.ContourGeometry.branchLine_integral

namespace CatalanCore.Li2.Decay.ContourGeometry
open Polynomial CatalanCore.Tools.VerticalResidues

theorem positive_unit_strip (z : ℝ) (hz : ValidZ z) (hpos : 0 < z)
    (n N : ℕ) (T : ℂ[X]) :
    (∫ y : ℝ, upLine z n T N y)-(∫ y : ℝ, upLine z n T (N+1) y)=
      -((2*Real.pi:ℂ)*Complex.I)*((z:ℂ)^(N+1)*deriv (rationalCore n T) (((N+1:ℕ):ℂ))+
        (Real.log |z|:ℂ)*(∫ x in ((N:ℝ)+1/2)..(((N+1:ℕ):ℝ)+1/2),
          rationalCore n T (x:ℂ)*Complex.exp ((Real.log |z|:ℂ)*(x:ℂ)))) := by
  let a : ℝ := (N:ℝ)+1/2
  let b : ℝ := ((N+1:ℕ):ℝ)+1/2
  let m : ℕ := N+1
  let L : ℂ := (Real.log |z|:ℂ)
  let Q : ℂ → ℂ := fun u => rationalCore n T u*Complex.exp (L*u)
  let g := exponentialPoleNumerator (rationalCore n T) (poleAmplitude false m) L (m:ℂ)
  let Fp := branchDensity false true n T L
  let Fm := branchDensity false false n T L
  let c : ℂ := -L*(Real.pi:ℂ)*Complex.I
  have hbool : decide (z<0)=false := by simp [not_lt.mpr hpos.le]
  obtain ⟨C,hC,hhor⟩ := branch_horizontal_bound z hz n T
  have hap : a < (m:ℝ) := by dsimp only [a,m]; push_cast; linarith
  have hpb : (m:ℝ) < b := by dsimp only [b,m]; linarith
  have hQ : DifferentiableOn ℂ Q (poleStrip m) :=
    (rationalCore_differentiableOn n m T).mul (by fun_prop)
  have hFp : ∀ u ∈ poleStrip m, u ≠ ((m:ℝ):ℂ) → Fp u=g u/(u-((m:ℝ):ℂ))^2+c*Q u := by
    intro u hu hne
    simpa only [Fp,g,c,Q,Complex.ofReal_natCast,Bool.false_eq_true,↓reduceIte] using
      branchDensity_representation false true n m T L u hu (by simpa using hne)
  have hFm : ∀ u ∈ poleStrip m, u ≠ ((m:ℝ):ℂ) → Fm u=g u/(u-((m:ℝ):ℂ))^2-c*Q u := by
    intro u hu hne
    have hh := branchDensity_representation false false n m T L u hu (by simpa using hne)
    simp only [Bool.false_eq_true,↓reduceIte] at hh
    simpa only [Fm,g,c,Q,Complex.ofReal_natCast,neg_mul,sub_neg_eq_add] using hh
  have hipN := (branchLine_integrable z hz n T N).1
  have hipB := (branchLine_integrable z hz n T (N+1)).1
  have himN := (branchLine_integrable z hz n T N).2
  have himB := (branchLine_integrable z hz n T (N+1)).2
  have hip : IntegrableOn (fun y : ℝ => Complex.I*Fp ((a:ℂ)+(y:ℂ)*Complex.I)-Complex.I*Fp ((b:ℂ)+(y:ℂ)*Complex.I)) (Ioi 0) := by
    have hh := hipN.sub hipB
    change IntegrableOn (fun y => branchLine z true n T N y-branchLine z true n T (N+1) y) (Ioi 0) at hh
    simpa only [branchLine,hbool,Fp,a,b,L] using hh
  have him : IntegrableOn (fun y : ℝ => Complex.I*Fm ((a:ℂ)+(y:ℂ)*Complex.I)-Complex.I*Fm ((b:ℂ)+(y:ℂ)*Complex.I)) (Iic 0) := by
    have hh := himN.sub himB
    change IntegrableOn (fun y => branchLine z false n T N y-branchLine z false n T (N+1) y) (Iic 0) at hh
    simpa only [branchLine,hbool,Fm,a,b,L] using hh
  have hdec : ∀ H : ℝ, 1 ≤ H → ∀ x ∈ Icc a b,
      ‖Fm ((x:ℂ)-(H:ℂ)*Complex.I)‖ ≤ C/H ∧ ‖Fp ((x:ℂ)+(H:ℂ)*Complex.I)‖ ≤ C/H := by
    intro H hH x hx
    have hx0 : 0 ≤ x := by
      have hnR := Nat.cast_nonneg N (α := ℝ)
      have hh := hx.1
      dsimp only [a] at hh
      linarith
    simpa only [hbool,Fm,Fp,L] using hhor H hH x hx0
  have hh := vertical_double_pole_jump Fp Fm g Q (poleStrip m) a b (m:ℝ) C c hap hpb
    (poleStrip_open m) (closed_strip_mem N) (poleNumerator_differentiableOn false n m T L) hQ hFp hFm hip him hdec
  have hres : deriv g ((m:ℝ):ℂ)=(z:ℂ)^m*deriv (rationalCore n T) (m:ℂ) := by
    simpa only [hbool,g,L,Complex.ofReal_natCast] using poleNumerator_residue z hz n m T
  rw [hres] at hh
  have hpSub : (∫ y in Ioi (0:ℝ), branchLine z true n T N y-branchLine z true n T (N+1) y)=
      (∫ y in Ioi (0:ℝ), branchLine z true n T N y)-(∫ y in Ioi (0:ℝ), branchLine z true n T (N+1) y) := integral_sub hipN hipB
  have hmSub : (∫ y in Iic (0:ℝ), branchLine z false n T N y-branchLine z false n T (N+1) y)=
      (∫ y in Iic (0:ℝ), branchLine z false n T N y)-(∫ y in Iic (0:ℝ), branchLine z false n T (N+1) y) := integral_sub himN himB
  have hh2 : (∫ y in Ioi (0:ℝ), branchLine z true n T N y-branchLine z true n T (N+1) y)+
    (∫ y in Iic (0:ℝ), branchLine z false n T N y-branchLine z false n T (N+1) y)=
      -((2*Real.pi:ℂ)*Complex.I)*((z:ℂ)^m*deriv (rationalCore n T) (m:ℂ))+(2*c)*(∫ x in a..b, Q (x:ℂ)) := by
    simpa only [branchLine,hbool,Fp,Fm,a,b,L] using hh
  rw [hpSub,hmSub] at hh2
  have hadd : ∀ A B C D : ℂ, (A-B)+(C-D)=(A+C)-(B+D) := by intros; ring
  rw [hadd,branchLine_integral z hz n T N,branchLine_integral z hz n T (N+1)] at hh2
  rw [hh2]
  dsimp only [c,Q,L,a,b,m]
  ring
end CatalanCore.Li2.Decay.ContourGeometry
#print axioms CatalanCore.Li2.Decay.ContourGeometry.positive_unit_strip

namespace CatalanCore.Li2.Decay.ContourGeometry
open Polynomial
noncomputable def realDensity (z : ℝ) (n : ℕ) (T : ℂ[X]) (x : ℝ) : ℂ :=
  rationalCore n T (x:ℂ)*Complex.exp ((Real.log |z|:ℂ)*(x:ℂ))

theorem realDensity_bound (z : ℝ) (hz : ValidZ z) (n : ℕ) (T : ℂ[X]) :
    ∃ M b : ℝ, 0 < M ∧ 0 < b ∧ ∀ x : ℝ, 0 ≤ x → ‖realDensity z n T x‖ ≤ M*Real.exp (-b*x) := by
  obtain ⟨B,hB,hR⟩ := rationalCore_polynomial_bound n T
  let L := Real.log |z|
  have hL : L < 0 := Real.log_neg hz.1 hz.2
  let b := -L/2
  have hb : 0 < b := by dsimp only [b]; linarith
  obtain ⟨D,hD,hpow⟩ := CatalanCore.Decay.CurveFamily.pow_one_add_le_exp (3*n+1+T.natDegree) hb
  refine ⟨B*(D+1),b,by positivity,hb,?_⟩
  intro x hx
  have hr := hR (x:ℂ) (by simpa using (show -(1/4:ℝ) ≤ x by linarith))
  simp only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hx] at hr
  have hnorm : ‖realDensity z n T x‖=‖rationalCore n T (x:ℂ)‖*Real.exp (L*x) := by
    simp [realDensity,norm_mul,Complex.norm_exp,L]
  rw [hnorm]
  calc
    _ ≤ (B*(1+x)^(3*n+1+T.natDegree))*Real.exp (L*x) := mul_le_mul_of_nonneg_right hr (Real.exp_pos _).le
    _ ≤ (B*(D*Real.exp (b*x)))*Real.exp (L*x) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hpow x hx) hB.le) (Real.exp_pos _).le
    _ = B*D*Real.exp (-b*x) := by
      calc
        _ = B*D*(Real.exp (b*x)*Real.exp (L*x)) := by ring
        _ = _ := by
          rw [← Real.exp_add]
          congr 2
          dsimp only [b]
          ring
    _ ≤ B*(D+1)*Real.exp (-b*x) := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by linarith : D ≤ D+1) hB.le) (Real.exp_pos _).le

theorem realDensity_measurable (z : ℝ) (n : ℕ) (T : ℂ[X]) : Measurable (realDensity z n T) := by
  have hT := T.continuous.measurable
  unfold realDensity rationalCore weight Dprod
  fun_prop

noncomputable def realTail (z : ℝ) (n : ℕ) (T : ℂ[X]) (N : ℕ) : ℂ :=
  ∫ x in Ici ((N:ℝ)+1/2), realDensity z n T x

theorem realTail_geometric_bound (z : ℝ) (hz : ValidZ z) (n : ℕ) (T : ℂ[X]) :
    ∃ C q : ℝ, 0 < C ∧ 0 < q ∧ q < 1 ∧ ∀ N : ℕ,
      IntegrableOn (realDensity z n T) (Ici ((N:ℝ)+1/2)) ∧ ‖realTail z n T N‖ ≤ C*q^N := by
  obtain ⟨M,b,hM,hb,hbound⟩ := realDensity_bound z hz n T
  let q := Real.exp (-b)
  let C := M/b
  have hq : 0 < q := Real.exp_pos _
  refine ⟨C,q,by dsimp only [C]; positivity,hq,by dsimp only [q]; simpa only [Real.exp_lt_one_iff,neg_lt_zero] using hb,?_⟩
  intro N
  let v : ℝ := (N:ℝ)+1/2
  have hv : 0 ≤ v := by dsimp only [v]; positivity
  have hmajor : IntegrableOn (fun x : ℝ => M*Real.exp (-b*x)) (Ioi v) :=
    (integrableOn_exp_mul_Ioi (by linarith : -b<0) v).const_mul M
  have hi : IntegrableOn (realDensity z n T) (Ioi v) := by
    apply hmajor.mono' (realDensity_measurable z n T).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact hbound x (hv.trans hx.le)
  have hiC : IntegrableOn (realDensity z n T) (Ici v) := Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi hi
  refine ⟨hiC,?_⟩
  have hh : ‖realTail z n T N‖ ≤ ∫ x in Ioi v, M*Real.exp (-b*x) := by
    change ‖∫ x in Ici v, realDensity z n T x‖ ≤ _
    rw [integral_Ici_eq_integral_Ioi]
    apply norm_integral_le_of_norm_le hmajor
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact hbound x (hv.trans hx.le)
  rw [integral_const_mul,integral_exp_mul_Ioi (by linarith : -b<0) v] at hh
  apply hh.trans
  have he : Real.exp (-b*v) ≤ q^N := by
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    dsimp only [v]
    nlinarith
  calc
    M*(-Real.exp (-b*v)/(-b)) = C*Real.exp (-b*v) := by dsimp only [C]; ring
    _ ≤ C*q^N := mul_le_mul_of_nonneg_left he (by dsimp only [C]; positivity)

theorem realTail_sub (z : ℝ) (hz : ValidZ z) (n : ℕ) (T : ℂ[X]) (N : ℕ) :
    realTail z n T N-realTail z n T (N+1)=
      ∫ x in ((N:ℝ)+1/2)..(((N+1:ℕ):ℝ)+1/2), realDensity z n T x := by
  obtain ⟨C,q,hC,hq,hq1,hh⟩ := realTail_geometric_bound z hz n T
  exact intervalIntegral.integral_Ici_sub_Ici' (hh N).1 (hh (N+1)).1
end CatalanCore.Li2.Decay.ContourGeometry
#print axioms CatalanCore.Li2.Decay.ContourGeometry.realTail_sub


namespace CatalanCore.Li2.Decay.ContourGeometry
open Polynomial
noncomputable def correctedLine (z : ℝ) (n : ℕ) (T : ℂ[X]) (N : ℕ) : ℂ :=
  -(((2*Real.pi:ℂ)*Complex.I)⁻¹)*(∫ y : ℝ, upLine z n T N y)+
    if 0 < z then -(Real.log |z|:ℂ)*realTail z n T N else 0

theorem correctedLine_sub (z : ℝ) (hz : ValidZ z) (n N : ℕ) (T : ℂ[X]) :
    correctedLine z n T N-correctedLine z n T (N+1)=
      (z:ℂ)^(N+1)*deriv (rationalCore n T) (((N+1:ℕ):ℂ)) := by
  have hπ : (2*Real.pi:ℂ)*Complex.I ≠ 0 := by
    apply mul_ne_zero _ Complex.I_ne_zero
    exact_mod_cast (ne_of_gt (mul_pos (by norm_num : (0:ℝ)<2) Real.pi_pos))
  by_cases hpos : 0 < z
  · have hh := positive_unit_strip z hz hpos n N T
    unfold correctedLine
    rw [if_pos hpos,if_pos hpos]
    have halg : ∀ A B C D E : ℂ, -E*A+C-(-E*B+D) = -E*(A-B)+(C-D) := by intros; ring
    rw [halg,hh]
    have htail : -(Real.log |z|:ℂ)*realTail z n T N-
        (-(Real.log |z|:ℂ)*realTail z n T (N+1))=
        -(Real.log |z|:ℂ)*(∫ x in ((N:ℝ)+1/2)..(((N+1:ℕ):ℝ)+1/2), realDensity z n T x) := by
      rw [← mul_sub,realTail_sub z hz n T N]
    rw [htail]
    unfold realDensity
    field_simp
    <;> ring
  · have hz0 : z ≠ 0 := by intro he; simpa [he] using hz.1
    have hneg : z < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hz0
    have hh := negative_unit_strip z hz hneg n N T
    unfold correctedLine
    rw [if_neg hpos,if_neg hpos,add_zero,add_zero,← mul_sub,hh]
    field_simp
    <;> ring

theorem correctedLine_summable (z : ℝ) (hz : ValidZ z) (n : ℕ) (T : ℂ[X]) :
    Summable (correctedLine z n T) := by
  obtain ⟨C,q,hC,hq,hq1,hline⟩ := upLine_geometric_bound z hz n T
  have hsLine : Summable (fun N : ℕ => ∫ y : ℝ, upLine z n T N y) :=
    Summable.of_norm_bounded ((summable_geometric_of_lt_one hq.le hq1).mul_left C)
      (fun N => (hline N).2)
  obtain ⟨D,r,hD,hr,hr1,htail⟩ := realTail_geometric_bound z hz n T
  have hsTail : Summable (realTail z n T) :=
    Summable.of_norm_bounded ((summable_geometric_of_lt_one hr.le hr1).mul_left D)
      (fun N => (htail N).2)
  unfold correctedLine
  by_cases hpos : 0 < z
  · simp only [if_pos hpos]
    exact (hsLine.mul_left _).add (hsTail.mul_left _)
  · simp only [if_neg hpos,add_zero]
    exact hsLine.mul_left _

theorem latticeTail_eq_correctedLine (z : ℝ) (hz : ValidZ z) (n N : ℕ) (T : ℂ[X]) :
    latticeTail z n N T=correctedLine z n T N := by
  have hs := correctedLine_summable z hz n T
  have hsN : Summable (fun k : ℕ => correctedLine z n T (N+k)) := by
    simpa only [Nat.add_comm] using (summable_nat_add_iff N).mpr hs
  have hsB : Summable (fun k : ℕ => correctedLine z n T (N+(k+1))) := by
    simpa only [Nat.add_comm] using (summable_nat_add_iff 1).mpr hsN
  have hterm (k : ℕ) : (z:ℂ)^(N+1+k)*deriv (fun u : ℂ => u*weight n u*T.eval u) ((N+1+k:ℕ):ℂ)=
      correctedLine z n T (N+k)-correctedLine z n T (N+(k+1)) := by
    rw [show N+(k+1)=(N+k)+1 by omega,correctedLine_sub z hz n (N+k) T]
    have hfun : rationalCore n T=(fun u : ℂ => u*weight n u*T.eval u) := funext fun _ => rfl
    rw [hfun,show N+1+k=N+k+1 by omega]
  unfold latticeTail
  simp_rw [hterm]
  rw [hsN.tsum_sub hsB]
  have hh := hsN.tsum_eq_zero_add
  simp only [Nat.add_zero] at hh
  linear_combination hh
end CatalanCore.Li2.Decay.ContourGeometry
#print axioms CatalanCore.Li2.Decay.ContourGeometry.latticeTail_eq_correctedLine

namespace CatalanCore.Li2.Decay.ContourGeometry
open Polynomial
noncomputable def rightDomain : Set ℂ := {u | -(1/4:ℝ)<u.re}

theorem rightDomain_open : IsOpen rightDomain := isOpen_lt continuous_const Complex.continuous_re

theorem rationalCore_differentiableAt_right (n : ℕ) (T : ℂ[X]) (u : ℂ) (hu : u ∈ rightDomain) :
    DifferentiableAt ℂ (rationalCore n T) u := by
  have hD (k : ℕ) : Differentiable ℂ (Dprod k) := by unfold Dprod; fun_prop
  have hden : Dprod (4*n) u ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj he
    have hh := congrArg Complex.re he
    simp only [Complex.add_re,Complex.natCast_re,Complex.zero_re] at hh
    have hjR : (1:ℝ) ≤ j := by exact_mod_cast (Finset.mem_Icc.mp hj).1
    change -(1/4:ℝ)<u.re at hu
    linarith
  have hw : DifferentiableAt ℂ (weight n) u := by
    unfold weight
    exact ((hD n u).pow 3).div (hD (4*n) u) hden
  exact ((hasDerivAt_id u).differentiableAt.mul hw).mul (T.hasDerivAt u).differentiableAt

theorem sin_ne_zero_of_im (u : ℂ) (hu : u.im ≠ 0) : Complex.sin ((Real.pi:ℂ)*u) ≠ 0 := by
  intro he
  obtain ⟨k,hk⟩ := Complex.sin_eq_zero_iff.mp he
  have hh := congrArg Complex.im hk
  simp only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,zero_add,
    Complex.intCast_im,Complex.intCast_re,mul_zero,add_zero] at hh
  exact hu ((mul_eq_zero.mp hh).resolve_left Real.pi_ne_zero)

theorem sin_ne_zero_near_half (N : ℕ) (u : ℂ)
    (hu : u ∈ Metric.ball (((N:ℝ)+1/2:ℝ):ℂ) (1/4)) :
    Complex.sin ((Real.pi:ℂ)*u) ≠ 0 := by
  intro he
  obtain ⟨k,hk⟩ := Complex.sin_eq_zero_iff.mp he
  have huEq : u=(k:ℂ) := by
    apply mul_left_cancel₀ (show (Real.pi:ℂ) ≠ 0 by exact_mod_cast Real.pi_ne_zero)
    simpa only [mul_comm] using hk
  have hdist := Metric.mem_ball.mp hu
  rw [dist_eq_norm,huEq] at hdist
  have hr := Complex.abs_re_le_norm ((k:ℂ)-(((N:ℝ)+1/2:ℝ):ℂ))
  simp only [Complex.sub_re,Complex.intCast_re,Complex.ofReal_re] at hr
  have hab : |(k:ℝ)-((N:ℝ)+1/2)| < 1/4 := hr.trans_lt hdist
  have hl : (N:ℝ) < (k:ℝ) := by linarith [(abs_lt.mp hab).1]
  have hh : (k:ℝ) < ((N+1:ℕ):ℝ) := by push_cast; linarith [(abs_lt.mp hab).2]
  have hlI : (N:ℤ)<k := by exact_mod_cast hl
  have hhI : k<(N:ℤ)+1 := by exact_mod_cast hh
  omega

theorem branchDensity_differentiableAt (negative upper : Bool) (n : ℕ) (T : ℂ[X]) (L u : ℂ)
    (hu : u ∈ rightDomain) (hs : Complex.sin ((Real.pi:ℂ)*u) ≠ 0) :
    DifferentiableAt ℂ (branchDensity negative upper n T L) u := by
  have hR := rationalCore_differentiableAt_right n T u hu
  have hsin : DifferentiableAt ℂ (fun u : ℂ => Complex.sin ((Real.pi:ℂ)*u)) u := by fun_prop
  have hcos : DifferentiableAt ℂ (fun u : ℂ => Complex.cos ((Real.pi:ℂ)*u)) u := by fun_prop
  have hB := (unshiftedKernel_hasDerivAt negative u hs).differentiableAt
  have hP : DifferentiableAt ℂ (unshiftedKernelPrime negative) u := by
    have he : unshiftedKernelPrime negative=(fun w : ℂ => if negative then
      -(Real.pi:ℂ)^2*Complex.cos ((Real.pi:ℂ)*w)/Complex.sin ((Real.pi:ℂ)*w)^2 else
      -(Real.pi:ℂ)^2/Complex.sin ((Real.pi:ℂ)*w)^2) := funext fun _ => rfl
    rw [he]
    have hs2 : Complex.sin ((Real.pi:ℂ)*u)^2 ≠ 0 := pow_ne_zero 2 hs
    cases negative <;> simp only [Bool.false_eq_true,↓reduceIte] <;> fun_prop
  unfold branchDensity
  fun_prop
end CatalanCore.Li2.Decay.ContourGeometry
#print axioms CatalanCore.Li2.Decay.ContourGeometry.branchDensity_differentiableAt


namespace CatalanCore.Li2.Decay.ContourGeometry
open CatalanCore.Uniform.Decay.Polygon Topology
variable {f : ℂ → ℂ} {σ δ : ℝ} {v : ℂ}

theorem diffAt_convex {S : Set ℂ} (hSo : IsOpen S) (hδ : 0 < δ)
    (hfH : DifferentiableOn ℂ f (S ∩ halfP σ))
    (hfB : DifferentiableOn ℂ f (Metric.ball v δ)) {z : ℂ} (hzS : z ∈ S)
    (hz : z ∈ Metric.ball v δ ∨ z ∈ halfP σ) : DifferentiableAt ℂ f z := by
  rcases hz with h | h
  · exact hfB.differentiableAt (Metric.isOpen_ball.mem_nhds h)
  · exact hfH.differentiableAt ((hSo.inter (isOpen_halfP σ)).mem_nhds ⟨hzS,h⟩)

theorem chain_close_convex {S : Set ℂ} (hS : Convex ℝ S) (hSo : IsOpen S)
    (hvS : v ∈ S) (hv : v.im=0) (hδ : 0 < δ)
    (hfH : DifferentiableOn ℂ f (S ∩ halfP σ))
    (hfB : DifferentiableOn ℂ f (Metric.ball v δ)) (w1 : ℂ) (rest : List ℂ)
    (hl : ∀ z ∈ w1 :: rest, z ∈ S ∧ 0 < σ*z.im) {Q : ℂ}
    (hQ : Q ∈ S ∧ 0 < σ*Q.im) :
    chainI f (v :: w1 :: rest)+segI f ((w1 :: rest).getLast (List.cons_ne_nil _ _)) Q=segI f v Q := by
  have hw1 := hl w1 (by simp)
  obtain ⟨e1,he1s,he1b,he1h⟩ := exists_near (σ := σ) hv hδ hw1.2
  obtain ⟨e2,he2s,he2b,he2h⟩ := exists_near (σ := σ) hv hδ hQ.2
  have he1S := hS.segment_subset hvS hw1.1 he1s
  have he2S := hS.segment_subset hvS hQ.1 he2s
  set L := (w1 :: rest).getLast (List.cons_ne_nil _ _) with hL
  have hLm := hl L (List.getLast_mem _)
  have hrest : ∀ z ∈ rest, z ∈ S ∩ halfP σ := fun z hz => hl z (by simp [hz])
  have hHS := hS.inter (convex_halfP σ)
  have s1 := segI_split he1s (fun z hz => diffAt_convex hSo hδ hfH hfB
    (hS.segment_subset hvS hw1.1 hz) (segment_sub hv hδ hw1.2 z hz))
  have c1 := chainI_eq hHS hfH rest w1 hw1 hrest
  have a1 := segI_add hHS hfH (a := e1) (b := w1) (c := L) ⟨he1S,he1h⟩ hw1 hLm
  have a2 := segI_add hHS hfH (a := e1) (b := L) (c := Q) ⟨he1S,he1h⟩ hLm hQ
  have a3 := segI_add hHS hfH (a := e1) (b := e2) (c := Q) ⟨he1S,he1h⟩ ⟨he2S,he2h⟩ hQ
  have b1 := segI_add (convex_ball v δ) hfB (a := v) (b := e1) (c := e2)
    (Metric.mem_ball_self hδ) he1b he2b
  have s2 := segI_split he2s (fun z hz => diffAt_convex hSo hδ hfH hfB
    (hS.segment_subset hvS hQ.1 hz) (segment_sub hv hδ hQ.2 z hz))
  rw [chainI_cons_cons,c1]
  rw [← hL]
  linear_combination -s1+a1+a2-a3+b1+s2

theorem integrableOn_ray_convex {S : Set ℂ} {p d : ℂ}
    (hstay : ∀ u : ℝ, 0 ≤ u → p+(u:ℂ)*d ∈ S) (hp : 0 ≤ σ * p.im) (hd : 0 < σ * d.im) {K : ℝ}
    (hK : 0 ≤ K) (hdec : ∀ z : ℂ, z ∈ S → 1 ≤ σ * z.im → ‖f z‖ ≤ K / (σ * z.im) ^ 2)
    (hc : ∀ u : ℝ, 0 ≤ u → ContinuousAt f (p + (u : ℂ) * d)) :
    IntegrableOn (fun u : ℝ => f (p + (u : ℂ) * d) * d) (Ioi 0) := by
  set U : ℝ := 1 / (σ * d.im) with hU
  have hU0 : 0 < U := by positivity
  have hcont : ContinuousOn (fun u : ℝ => f (p + (u : ℂ) * d) * d) (Ici 0) := by
    intro u hu
    refine ContinuousAt.continuousWithinAt ?_
    refine ContinuousAt.mul ?_ continuousAt_const
    exact (hc u hu).comp (f := fun u : ℝ => p + (u : ℂ) * d) (by fun_prop)
  have h1 : IntegrableOn (fun u : ℝ => f (p + (u : ℂ) * d) * d) (Ioc 0 U) :=
    ((hcont.mono Icc_subset_Ici_self).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have h2 : IntegrableOn (fun u : ℝ => f (p + (u : ℂ) * d) * d) (Ioi U) := by
    have hb : IntegrableOn (fun u : ℝ => (K * ‖d‖ / (σ * d.im) ^ 2) * u ^ (-2 : ℝ)) (Ioi U) :=
      (integrableOn_Ioi_rpow_of_lt (by norm_num) hU0).const_mul _
    refine hb.mono' ((hcont.mono (Ioi_subset_Ici hU0.le)).aestronglyMeasurable measurableSet_Ioi) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u hu => ?_)
    have hu : U < u := hu
    have hu0 : 0 < u := hU0.trans hu
    have hh : u * (σ * d.im) ≤ σ * (p + (u : ℂ) * d).im := by
      rw [im_ray]; nlinarith
    have h1le : 1 ≤ u * (σ * d.im) := by
      rw [hU] at hu
      have := (div_lt_iff₀ hd).1 hu
      linarith
    have hz := hdec _ (hstay u hu0.le) (h1le.trans hh)
    rw [norm_mul]
    have hpos : 0 < u * (σ * d.im) := by positivity
    have hsq : K / (σ * (p + (u : ℂ) * d).im) ^ 2 ≤ K / (u * (σ * d.im)) ^ 2 :=
      div_le_div_of_nonneg_left hK (by positivity) (pow_le_pow_left₀ hpos.le hh 2)
    have hr : u ^ (-2 : ℝ) = 1 / u ^ 2 := by
      rw [Real.rpow_neg hu0.le, one_div]; norm_cast
    rw [hr]
    calc ‖f (p + (u : ℂ) * d)‖ * ‖d‖ ≤ K / (u * (σ * d.im)) ^ 2 * ‖d‖ :=
          mul_le_mul_of_nonneg_right (hz.trans hsq) (norm_nonneg _)
      _ = K * ‖d‖ / (σ * d.im) ^ 2 * (1 / u ^ 2) := by field_simp
  have := h1.union h2
  rwa [Ioc_union_Ioi_eq_Ioi hU0.le] at this

theorem connector_convex {S : Set ℂ} (hS : Convex ℝ S) {p v d D : ℂ}
    (hpS : ∀ u : ℝ, 0 ≤ u → p+(u:ℂ)*d ∈ S)
    (hvS : ∀ u : ℝ, 0 ≤ u → v+(u:ℂ)*D ∈ S) (hp : 0 ≤ σ * p.im) (hv : 0 ≤ σ * v.im)
    (hd : 0 < σ * d.im) (hD : 0 < σ * D.im) {K : ℝ} (hK : 0 ≤ K)
    (hdec : ∀ z : ℂ, z ∈ S → 1 ≤ σ * z.im → ‖f z‖ ≤ K / (σ * z.im) ^ 2) :
    Tendsto (fun T : ℝ => segI f (p + (T : ℂ) * d) (v + (T : ℂ) * D)) atTop (𝓝 0) := by
  set c : ℝ := min (σ * d.im) (σ * D.im) with hc
  have hc0 : 0 < c := lt_min hd hD
  set α : ℝ := ‖v - p‖
  set β : ℝ := ‖D - d‖
  have hbound : ∀ᶠ T : ℝ in atTop, ‖segI f (p + (T : ℂ) * d) (v + (T : ℂ) * D)‖
      ≤ K / c ^ 2 * (α * (T⁻¹) ^ 2 + β * T⁻¹) := by
    filter_upwards [eventually_ge_atTop (1 / c), eventually_gt_atTop (0 : ℝ)] with T hT hT0
    have hcT : 1 ≤ c * T := by
      have := (div_le_iff₀ hc0).1 hT; linarith
    have hA : c * T ≤ σ * (p + (T : ℂ) * d).im := by
      rw [im_ray]; have := min_le_left (σ * d.im) (σ * D.im); nlinarith
    have hB : c * T ≤ σ * (v + (T : ℂ) * D).im := by
      rw [im_ray]; have := min_le_right (σ * d.im) (σ * D.im); nlinarith
    have hseg : ∀ z ∈ segment ℝ (p + (T : ℂ) * d) (v + (T : ℂ) * D),
        ‖f z‖ ≤ K / (c * T) ^ 2 := by
      intro z hz
      have hm := height_segment_ge hA hB hz
      refine (hdec z (hS.segment_subset (hpS T hT0.le) (hvS T hT0.le) hz) (hcT.trans hm)).trans ?_
      exact div_le_div_of_nonneg_left hK (by positivity) (pow_le_pow_left₀ (by positivity) hm 2)
    refine (norm_segI_le hseg).trans ?_
    have hlen : ‖(v + (T : ℂ) * D) - (p + (T : ℂ) * d)‖ ≤ α + T * β := by
      have e : (v + (T : ℂ) * D) - (p + (T : ℂ) * d) = (v - p) + (T : ℂ) * (D - d) := by ring
      rw [e]
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hT0.le]
    calc K / (c * T) ^ 2 * ‖(v + (T : ℂ) * D) - (p + (T : ℂ) * d)‖
        ≤ K / (c * T) ^ 2 * (α + T * β) :=
          mul_le_mul_of_nonneg_left hlen (by positivity)
      _ = K / c ^ 2 * (α * (T⁻¹) ^ 2 + β * T⁻¹) := by field_simp
  have hlim : Tendsto (fun T : ℝ => K / c ^ 2 * (α * (T⁻¹) ^ 2 + β * T⁻¹)) atTop (𝓝 0) := by
    have h0 := tendsto_inv_atTop_zero (𝕜 := ℝ)
    have := ((h0.pow 2).const_mul α).add (h0.const_mul β)
    have := this.const_mul (K / c ^ 2)
    simpa using this
  exact squeeze_zero_norm' hbound hlim
theorem deform_convex {S : Set ℂ} (hS : Convex ℝ S) (hSo : IsOpen S) (hvS : v ∈ S) (hv : v.im = 0) (hδ : 0 < δ) (hfH : DifferentiableOn ℂ f (S ∩ halfP σ))
    (hfB : DifferentiableOn ℂ f (Metric.ball v δ)) (pts : List ℂ)
    (hpts : ∀ z ∈ pts, z ∈ S ∧ 0 < σ * z.im) {d D : ℂ} (hd : 0 < σ * d.im) (hD : 0 < σ * D.im)
    (hray : ∀ p ∈ v :: pts, ∀ u : ℝ, 0 ≤ u → p+(u:ℂ)*d ∈ S)
    (href : ∀ u : ℝ, 0 ≤ u → v+(u:ℂ)*D ∈ S)
    {K : ℝ} (hK : 0 ≤ K) (hdec : ∀ z : ℂ, z ∈ S → 1 ≤ σ * z.im → ‖f z‖ ≤ K / (σ * z.im) ^ 2) :
    polyI f v pts d = rayInt f v D := by
  have hptsH : ∀ z ∈ pts, 0 < σ*z.im := fun z hz => (hpts z hz).2
  set L := (v :: pts).getLast (List.cons_ne_nil v pts) with hL
  have hLm : L = v ∨ 0 < σ * L.im := mem_or_half pts hptsH L (List.getLast_mem _)
  have hLmS : L ∈ S := by
    have hmem : L ∈ v :: pts := List.getLast_mem _
    rcases List.mem_cons.mp hmem with h | h
    · rw [h]; exact hvS
    · exact (hpts L h).1
  have hstay : ∀ u : ℝ, 0 ≤ u → L+(u:ℂ)*d ∈ S := hray L (List.getLast_mem _) 
  have hL0 : 0 ≤ σ * L.im := by
    rcases hLm with h | h
    · rw [h, hv, mul_zero]
    · exact h.le
  have hv0 : 0 ≤ σ * v.im := by rw [hv, mul_zero]
  have hdiff : ∀ z, z ∈ S → (z ∈ Metric.ball v δ ∨ z ∈ halfP σ) → DifferentiableAt ℂ f z :=
    fun z hzS hz => diffAt_convex hSo hδ hfH hfB hzS hz
  have hiT := integrableOn_ray_convex hstay hL0 hd hK hdec
    (fun u hu => (hdiff _ (hstay u hu) (ray_mem hδ hLm hd hv hu)).continuousAt)
  have hiR := integrableOn_ray_convex href hv0 hD hK hdec
    (fun u hu => (hdiff _ (href u hu) (ray_mem hδ (Or.inl rfl) hD hv hu)).continuousAt)
  -- the truncated identity, for every `T > 0`
  have htr : ∀ T : ℝ, 0 < T → chainI f (v :: pts) + segI f L (L + (T : ℂ) * d)
      + segI f (L + (T : ℂ) * d) (v + (T : ℂ) * D) = segI f v (v + (T : ℂ) * D) := by
    intro T hT
    have hend : 0 < σ * (L + (T : ℂ) * d).im := by rw [im_ray]; nlinarith
    have hQ : 0 < σ * (v + (T : ℂ) * D).im := by rw [im_ray]; nlinarith
    have happ := chainI_append_singleton f (L + (T : ℂ) * d) pts v
    obtain ⟨w1, rest, hwr⟩ : ∃ w1 rest, pts ++ [L + (T : ℂ) * d] = w1 :: rest := by
      cases pts with
      | nil => exact ⟨_, [], rfl⟩
      | cons a l => exact ⟨a, l ++ [L + (T : ℂ) * d], rfl⟩
    have hl : ∀ z ∈ w1 :: rest, z ∈ S ∧ 0 < σ * z.im := by
      rw [← hwr]; intro z hz
      rcases List.mem_append.1 hz with h | h
      · exact hpts z h
      · rw [List.mem_singleton.1 h]; exact ⟨hstay T hT.le,hend⟩
    have hcl := chain_close_convex hS hSo hvS hv hδ hfH hfB w1 rest hl ⟨href T hT.le,hQ⟩ (f := f)
    have hlast : (w1 :: rest).getLast (List.cons_ne_nil _ _) = L + (T : ℂ) * d := by
      simp only [← hwr, List.getLast_append_singleton]
    rw [hlast] at hcl
    have e : v :: pts ++ [L + (T : ℂ) * d] = v :: w1 :: rest := by
      rw [List.cons_append, hwr]
    rw [e] at happ
    rw [← hL] at happ
    rw [← happ]; exact hcl
  -- pass to the limit `T → ∞`
  have hT1 : Tendsto (fun T : ℝ => segI f L (L + (T : ℂ) * d)) atTop
      (𝓝 (rayInt f L d)) := by
    have := intervalIntegral_tendsto_integral_Ioi 0 hiT tendsto_id
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    rw [segI_ray f L d hT]; rfl
  have hT2 : Tendsto (fun T : ℝ => segI f v (v + (T : ℂ) * D)) atTop
      (𝓝 (rayInt f v D)) := by
    have := intervalIntegral_tendsto_integral_Ioi 0 hiR tendsto_id
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    rw [segI_ray f v D hT]; rfl
  have hT3 := connector_convex (f := f) hS hstay href hL0 hv0 hd hD hK hdec (p := L) (v := v)
  have hsum := (tendsto_const_nhds (x := chainI f (v :: pts))).add hT1 |>.add hT3
  have hsum' : Tendsto (fun T : ℝ => segI f v (v + (T : ℂ) * D)) atTop
      (𝓝 (chainI f (v :: pts) + rayInt f L d + 0)) := by
    refine hsum.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    exact htr T hT
  have := tendsto_nhds_unique hsum' hT2
  rw [add_zero] at this
  unfold polyI
  rw [← hL]; exact this

end CatalanCore.Li2.Decay.ContourGeometry
#print axioms CatalanCore.Li2.Decay.ContourGeometry.deform_convex


namespace CatalanCore.Li2.Decay.ContourGeometry
open Polynomial CatalanCore.Uniform.Decay.Polygon

def sideSign (upper : Bool) : ℝ := if upper then 1 else -1
noncomputable def sideDirection (upper : Bool) : ℂ := if upper then Complex.I else -Complex.I

theorem rightDomain_convex : Convex ℝ rightDomain := by
  have hl : IsLinearMap ℝ (fun z : ℂ => z.re) :=
    ⟨fun x y => by simp,fun c x => by simp⟩
  exact convex_halfSpace_gt hl (-(1/4:ℝ))

theorem branchDensity_halfplane (z : ℝ) (upper : Bool) (n : ℕ) (T : ℂ[X]) :
    DifferentiableOn ℂ (branchDensity (decide (z<0)) upper n T (Real.log |z|:ℂ))
      (rightDomain ∩ halfP (sideSign upper)) := by
  intro u hu
  apply (branchDensity_differentiableAt _ _ n T _ u hu.1 (sin_ne_zero_of_im u ?_)).differentiableWithinAt
  intro he
  have hh := hu.2
  change 0 < sideSign upper*u.im at hh
  rw [he,mul_zero] at hh
  exact (lt_irrefl 0) hh

theorem branchDensity_ball (z : ℝ) (upper : Bool) (n N : ℕ) (T : ℂ[X]) :
    DifferentiableOn ℂ (branchDensity (decide (z<0)) upper n T (Real.log |z|:ℂ))
      (Metric.ball (((N:ℝ)+1/2:ℝ):ℂ) (1/4)) := by
  intro u hu
  have hh := Metric.mem_ball.mp hu
  rw [dist_eq_norm] at hh
  have hr := Complex.abs_re_le_norm (u-(((N:ℝ)+1/2:ℝ):ℂ))
  simp only [Complex.sub_re,Complex.ofReal_re] at hr
  have hl := (abs_lt.mp (hr.trans_lt hh)).1
  have huR : u ∈ rightDomain := by
    change -(1/4:ℝ)<u.re
    have hn := Nat.cast_nonneg N (α := ℝ)
    linarith
  exact (branchDensity_differentiableAt _ _ n T _ u huR (sin_ne_zero_near_half N u hu)).differentiableWithinAt

theorem branchDensity_height_bound (z : ℝ) (hz : ValidZ z) (upper : Bool) (n : ℕ) (T : ℂ[X]) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ u : ℂ, u ∈ rightDomain → 1 ≤ sideSign upper*u.im →
      ‖branchDensity (decide (z<0)) upper n T (Real.log |z|:ℂ) u‖ ≤ K/(sideSign upper*u.im)^2 := by
  obtain ⟨M,a,hM,ha,hbound⟩ := densityCore_radial_bound z hz n T
  obtain ⟨D,hD,hpow⟩ := CatalanCore.Decay.CurveFamily.pow_one_add_le_exp 2 ha
  refine ⟨M*(D+1),by positivity,?_⟩
  intro u hu hh
  let t := sideSign upper*u.im
  have ht : 0 < t := by dsimp only [t]; linarith
  have him : |u.im|=t := by cases upper <;> simp_all [sideSign,t,abs_of_nonneg,abs_of_nonpos] <;> linarith
  have hside : if upper then 0 ≤ u.im else u.im<0 := by
    cases upper <;> simp_all [sideSign] <;> linarith
  rw [branchDensity_physical z upper n T u hside]
  have hnorm : t ≤ ‖u‖ := by rw [← him]; exact Complex.abs_im_le_norm u
  have hp := hpow t ht.le
  have he : t^2*Real.exp (-a*t) ≤ D := by
    have ht2 : t^2 ≤ D*Real.exp (a*t) := by nlinarith
    have hm := mul_le_mul_of_nonneg_right ht2 (Real.exp_pos (-a*t)).le
    have hc : D*Real.exp (a*t)*Real.exp (-a*t)=D := by
      rw [mul_assoc,← Real.exp_add,show a*t+-a*t=0 by ring,Real.exp_zero,mul_one]
    rwa [hc] at hm
  apply (le_div_iff₀ (pow_pos ht 2)).mpr
  have hn := hbound u (le_of_lt hu) (Or.inr (by rw [him]; exact hh))
  calc
    _ ≤ (M*Real.exp (-a*‖u‖))*t^2 := mul_le_mul_of_nonneg_right hn (sq_nonneg _)
    _ ≤ (M*Real.exp (-a*t))*t^2 := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hnorm (by linarith))) hM.le) (sq_nonneg _)
    _ = M*(t^2*Real.exp (-a*t)) := by ring
    _ ≤ M*D := mul_le_mul_of_nonneg_left he hM.le
    _ ≤ M*(D+1) := by nlinarith

theorem branch_polygon_deform (z : ℝ) (hz : ValidZ z) (upper : Bool) (n N : ℕ) (T : ℂ[X])
    (pts : List ℂ) (hpts : ∀ u ∈ pts, 0 ≤ u.re ∧ 0 < sideSign upper*u.im) :
    polyI (branchDensity (decide (z<0)) upper n T (Real.log |z|:ℂ))
      (((N:ℝ)+1/2:ℝ):ℂ) pts (sideDirection upper)=
    rayInt (branchDensity (decide (z<0)) upper n T (Real.log |z|:ℂ))
      (((N:ℝ)+1/2:ℝ):ℂ) (sideDirection upper) := by
  obtain ⟨K,hK,hdec⟩ := branchDensity_height_bound z hz upper n T
  have hd : 0 < sideSign upper*(sideDirection upper).im := by cases upper <;> norm_num [sideSign,sideDirection]
  have hv : 0 ≤ (((N:ℝ)+1/2:ℝ):ℂ).re := by simp; positivity
  have hre : (sideDirection upper).re=0 := by cases upper <;> simp [sideDirection]
  apply deform_convex (S := rightDomain) rightDomain_convex rightDomain_open
    (by change -(1/4:ℝ)<_; simpa using (show -(1/4:ℝ)<(N:ℝ)+1/2 by have hnR := Nat.cast_nonneg N (α := ℝ); linarith))
    (by simp) (by norm_num : (0:ℝ)<1/4)
    (branchDensity_halfplane z upper n T) (branchDensity_ball z upper n N T) pts
    (fun u hu => ⟨by change -(1/4:ℝ)<u.re; linarith [(hpts u hu).1],(hpts u hu).2⟩) hd hd
    (fun p hp u hu => ?_) (fun u hu => ?_) hK hdec
  · change -(1/4:ℝ)<(p+(u:ℂ)*sideDirection upper).re
    have hpR : 0 ≤ p.re := by
      rcases List.mem_cons.mp hp with he|he
      · rw [he]; exact hv
      · exact (hpts p he).1
    simp only [Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,hre,mul_zero,zero_mul,sub_zero,add_zero]
    linarith
  · change -(1/4:ℝ)<((((N:ℝ)+1/2:ℝ):ℂ)+(u:ℂ)*sideDirection upper).re
    simp only [Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,hre,mul_zero,zero_mul,sub_zero,add_zero]
    have hn := Nat.cast_nonneg N (α := ℝ)
    linarith
end CatalanCore.Li2.Decay.ContourGeometry
#print axioms CatalanCore.Li2.Decay.ContourGeometry.branch_polygon_deform


namespace CatalanCore.Li2.Decay.ContourGeometry
open Polynomial CatalanCore.Li2.Uniform CatalanCore.Decay.CurveFamily CatalanCore.Uniform.Decay.Polygon

noncomputable def modifiedVertices (p : PolygonFrame) (n : ℕ) : List ℂ :=
  [(crossing p n:ℂ)+Complex.I,firstAtOne p n] ++
    (List.range p.edges).map (fun j => (n:ℂ)*p.vertex (j+1))

theorem vertex_one_im_pos (p : PolygonFrame) : 0 < (p.vertex 1).im := by
  have hh := p.imag_strict 0 1 (by omega) p.edges_pos
  simpa only [p.initial,Complex.ofReal_im] using hh

theorem modifiedVertices_upper (p : PolygonFrame) (n : ℕ) (hn : 0 < n)
    (hheight : 1 ≤ (n:ℝ)*(p.vertex 1).im) :
    ∀ u ∈ modifiedVertices p n, 0 ≤ u.re ∧ 0 < u.im := by
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  have hy := vertex_one_im_pos p
  have hx := p.real_pos 1 (by omega) p.edges_pos
  have hfirst : 0 ≤ (firstAtOne p n).re := by
    simp only [firstAtOne,← Complex.ofReal_mul,← Complex.ofReal_sub,← Complex.ofReal_div,← Complex.ofReal_add,Complex.add_re,Complex.ofReal_re,Complex.I_re,add_zero,Complex.add_im,Complex.ofReal_im,Complex.I_im,zero_add]
    change 0 ≤ (n:ℝ)*p.cut+((p.vertex 1).re-p.cut)/(p.vertex 1).im
    have hmul : 0 ≤ p.cut*((n:ℝ)*(p.vertex 1).im-1)+(p.vertex 1).re :=
      add_nonneg (mul_nonneg p.nonneg (by linarith)) hx.le
    have he : ((n:ℝ)*p.cut+((p.vertex 1).re-p.cut)/(p.vertex 1).im)*(p.vertex 1).im=
        p.cut*((n:ℝ)*(p.vertex 1).im-1)+(p.vertex 1).re := by
      field_simp
      <;> ring
    exact nonneg_of_mul_nonneg_right (by rw [mul_comm,he]; exact hmul) hy
  intro u hu
  rcases List.mem_append.mp hu with hu|hu
  · simp only [List.mem_cons,List.mem_nil_iff,or_false] at hu
    rcases hu with rfl|rfl
    · constructor
      · simp only [Complex.add_re,Complex.ofReal_re,Complex.I_re,add_zero]
        unfold crossing
        positivity
      · simp
    · exact ⟨hfirst,by simp only [firstAtOne,← Complex.ofReal_mul,← Complex.ofReal_sub,← Complex.ofReal_div,← Complex.ofReal_add,Complex.add_re,Complex.ofReal_re,Complex.I_re,add_zero,Complex.add_im,Complex.ofReal_im,Complex.I_im,zero_add]; norm_num⟩
  · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hu
    have hjE : j+1 ≤ p.edges := by have hh := List.mem_range.mp hj; omega
    have hxj := p.real_pos (j+1) (by omega) hjE
    have hyj : 0 < (p.vertex (j+1)).im := by
      have hh := p.imag_strict 0 (j+1) (by omega) hjE
      simpa only [p.initial,Complex.ofReal_im] using hh
    simp only [Complex.mul_re,Complex.mul_im,Complex.natCast_re,Complex.natCast_im,
      zero_mul,sub_zero,zero_add,add_zero]
    exact ⟨(mul_pos hnR hxj).le,mul_pos hnR hyj⟩

theorem modifiedVertices_last (p : PolygonFrame) (n : ℕ) :
    ((crossing p n:ℂ)::modifiedVertices p n).getLast (List.cons_ne_nil _ _)=(n:ℂ)*p.vertex p.edges := by
  obtain ⟨e,he⟩ := Nat.exists_eq_succ_of_ne_zero p.edges_pos.ne'
  unfold modifiedVertices
  rw [he,List.range_succ,List.map_append]
  simp only [List.map_cons,List.map_nil]
  simp only [← List.cons_append,← List.append_assoc,List.getLast_append_singleton]

theorem upperModified_eq_polyPieces (p : PolygonFrame) (n : ℕ) :
    upperModified p n=polyPieces ((crossing p n:ℂ)::modifiedVertices p n) (List.cons_ne_nil _ _) Complex.I := by
  unfold upperModified polyPieces
  rw [modifiedVertices_last]
  rfl

theorem upperModified_sum_eq_polyI (p : PolygonFrame) (n : ℕ) (f : ℂ → ℂ) :
    ((upperModified p n).map (fun q => pieceIntegral q f)).sum=
      polyI f (crossing p n:ℂ) (modifiedVertices p n) Complex.I := by
  rw [polyI_eq_sum,upperModified_eq_polyPieces]
  rfl
end CatalanCore.Li2.Decay.ContourGeometry
#print axioms CatalanCore.Li2.Decay.ContourGeometry.upperModified_sum_eq_polyI


namespace CatalanCore.Li2.Decay.ContourGeometry
open Polynomial CatalanCore.Li2.Uniform CatalanCore.Decay.CurveFamily CatalanCore.Uniform.Decay.Polygon

theorem chainPieces_height_ae (σ : ℝ) (v : ℂ) (pts : List ℂ) (hv : 0 ≤ σ*v.im)
    (hpts : ∀ u ∈ pts, 0 < σ*u.im) :
    ∀ q ∈ chainPieces (v::pts), ∀ᵐ t : ℝ ∂q.nu, 0 < σ*(q.zeta t).im := by
  induction pts generalizing v with
  | nil => simp [chainPieces]
  | cons w rest ih =>
    intro q hq
    simp only [chainPieces,List.mem_cons] at hq
    rcases hq with rfl|hq
    · change ∀ᵐ t : ℝ ∂volume.restrict (Ioc (0:ℝ) 1), _
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      have hw := hpts w (by simp)
      have h1 := mul_nonneg (sub_nonneg.mpr ht.2) hv
      have h2 := mul_pos ht.1 hw
      simp only [Piece.zeta,Complex.add_im,Complex.mul_im,Complex.ofReal_re,
        Complex.ofReal_im,zero_mul,zero_add,Complex.sub_im]
      nlinarith
    · exact ih w (hpts w (by simp)).le (fun u hu => hpts u (by simp [hu])) q hq

theorem upperModified_height_ae (p : PolygonFrame) (n : ℕ) (hn : 0 < n)
    (hheight : 1 ≤ (n:ℝ)*(p.vertex 1).im) :
    ∀ q ∈ upperModified p n, ∀ᵐ t : ℝ ∂q.nu, 0 < (q.zeta t).im := by
  intro q hq
  have hh := modifiedVertices_upper p n hn hheight
  rw [upperModified_eq_polyPieces] at hq
  simp only [polyPieces,List.mem_append,List.mem_singleton] at hq
  rcases hq with hq|rfl
  · simpa only [one_mul] using chainPieces_height_ae 1 (crossing p n:ℂ) (modifiedVertices p n)
      (by simp) (fun u hu => by simpa using (hh u hu).2) q hq
  · rw [modifiedVertices_last]
    change ∀ᵐ t : ℝ ∂volume.restrict (Ioi (0:ℝ)), _
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hy : 0 < (p.vertex p.edges).im := by
      have he := p.imag_strict 0 p.edges p.edges_pos (le_refl _)
      simpa only [p.initial,Complex.ofReal_im] using he
    have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
    simp only [Piece.zeta,Complex.add_im,Complex.mul_im,Complex.natCast_re,
      Complex.natCast_im,Complex.ofReal_im,Complex.ofReal_re,Complex.I_re,Complex.I_im,
      zero_mul,mul_zero,zero_add,add_zero,mul_one]
    exact add_pos (mul_pos hnR hy) ht

theorem upperModified_branch_integral (z : ℝ) (p : PolygonFrame) (n : ℕ) (T : ℂ[X])
    (hn : 0 < n) (hheight : 1 ≤ (n:ℝ)*(p.vertex 1).im) :
    ((upperModified p n).map (fun q => pieceIntegral q (densityCore z n T))).sum=
    polyI (branchDensity (decide (z<0)) true n T (Real.log |z|:ℂ))
      (crossing p n:ℂ) (modifiedVertices p n) Complex.I := by
  rw [← upperModified_sum_eq_polyI]
  apply congrArg List.sum
  apply List.map_congr_left
  intro q hq
  apply integral_congr_ae
  filter_upwards [upperModified_height_ae p n hn hheight q hq] with t ht
  rw [branchDensity_physical z true n T (q.zeta t) ht.le]

theorem lowerModified_branch_integral (z : ℝ) (p : PolygonFrame) (n : ℕ) (T : ℂ[X])
    (hn : 0 < n) (hheight : 1 ≤ (n:ℝ)*(p.vertex 1).im) :
    (((upperModified p n).map Piece.conj).map (fun q => pieceIntegral q (densityCore z n T))).sum=
    (((upperModified p n).map Piece.conj).map
      (fun q => pieceIntegral q (branchDensity (decide (z<0)) false n T (Real.log |z|:ℂ)))).sum := by
  apply congrArg List.sum
  apply List.map_congr_left
  intro q hq
  obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hq
  apply integral_congr_ae
  have hh : ∀ᵐ t : ℝ ∂r.conj.nu, 0 < (r.zeta t).im := by
    have hnu : r.conj.nu=r.nu := by rfl
    rw [hnu]
    exact upperModified_height_ae p n hn hheight r hr
  filter_upwards [hh] with t ht
  rw [branchDensity_physical z false n T (r.conj.zeta t) (by
    rw [Piece.zeta_conj]
    simpa using (show -(r.zeta t).im<0 by linarith))]

theorem upper_reference_eq (z : ℝ) (n N : ℕ) (T : ℂ[X]) :
    rayInt (branchDensity (decide (z<0)) true n T (Real.log |z|:ℂ))
      (((N:ℝ)+1/2:ℝ):ℂ) Complex.I=∫ y in Ioi (0:ℝ), upLine z n T N y := by
  unfold rayInt
  rw [← integral_congr_ae (branchLine_upper_ae z n T N)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y => by dsimp only [branchLine]; ring

theorem lower_reference_eq (z : ℝ) (n N : ℕ) (T : ℂ[X]) :
    rayInt (branchDensity (decide (z<0)) false n T (Real.log |z|:ℂ))
      (((N:ℝ)+1/2:ℝ):ℂ) (-Complex.I)=-(∫ y in Iic (0:ℝ), upLine z n T N y) := by
  unfold rayInt
  have he : (fun y : ℝ => branchDensity (decide (z<0)) false n T (Real.log |z|:ℂ)
      (((((N:ℝ)+1/2:ℝ):ℂ))+(y:ℂ)*(-Complex.I))*(-Complex.I))=
      (fun y : ℝ => -branchLine z false n T N (-y)) := by
    funext y
    simp only [branchLine,Complex.ofReal_neg]
    have harg : (((N:ℝ)+1/2:ℝ):ℂ)+(y:ℂ)*(-Complex.I)=
      (((N:ℝ)+1/2:ℝ):ℂ)+(-(y:ℂ))*Complex.I := by ring
    rw [harg]
    ring
  rw [he,integral_neg,integral_comp_neg_Ioi]
  simp only [neg_zero]
  rw [integral_congr_ae (branchLine_lower_ae z n T N)]
end CatalanCore.Li2.Decay.ContourGeometry
#print axioms CatalanCore.Li2.Decay.ContourGeometry.lower_reference_eq


namespace CatalanCore.Li2.Decay.ContourGeometry
open Polynomial CatalanCore.Li2.Uniform CatalanCore.Decay.CurveFamily CatalanCore.Uniform.Decay.Polygon

theorem chainPieces_conj (vs : List ℂ) :
    chainPieces (vs.map (starRingEnd ℂ))=(chainPieces vs).map Piece.conj := by
  induction vs using List.twoStepInduction with
  | nil => simp [chainPieces]
  | singleton a => simp [chainPieces]
  | cons_cons a b rest ihrest ih =>
    have hb := ih b
    simp only [List.map_cons] at hb
    simp only [List.map_cons,chainPieces]
    rw [hb]
    congr 1
    simp [Piece.conj,map_sub]

theorem polyPieces_conj (v : ℂ) (pts : List ℂ) (d : ℂ) :
    (polyPieces (v::pts) (List.cons_ne_nil _ _) d).map Piece.conj=
      polyPieces ((starRingEnd ℂ v)::pts.map (starRingEnd ℂ)) (List.cons_ne_nil _ _) (starRingEnd ℂ d) := by
  unfold polyPieces
  rw [List.map_append]
  have hc := chainPieces_conj (v::pts)
  simp only [List.map_cons] at hc
  rw [← hc]
  congr 1
  simp only [List.map_cons,List.map_nil,List.cons.injEq,Piece.conj, true_and]
  simp only [← List.map_cons,List.getLast_map]
  simp

theorem lowerModified_sum_eq_polyI (p : PolygonFrame) (n : ℕ) (f : ℂ → ℂ) :
    (((upperModified p n).map Piece.conj).map (fun q => pieceIntegral q f)).sum=
      polyI f (crossing p n:ℂ) ((modifiedVertices p n).map (starRingEnd ℂ)) (-Complex.I) := by
  rw [upperModified_eq_polyPieces,polyPieces_conj]
  have hv : starRingEnd ℂ (crossing p n:ℂ)=(crossing p n:ℂ) := by simp
  rw [hv]
  simpa only [map_neg,Complex.conj_I,pieceIntegral] using
    (polyI_eq_sum f (crossing p n:ℂ) ((modifiedVertices p n).map (starRingEnd ℂ)) (-Complex.I)).symm

theorem upperModified_straight (z : ℝ) (hz : ValidZ z) (p : PolygonFrame) (n : ℕ) (T : ℂ[X])
    (hn : 0 < n) (hheight : 1 ≤ (n:ℝ)*(p.vertex 1).im) :
    ((upperModified p n).map (fun q => pieceIntegral q (densityCore z n T))).sum=
      ∫ y in Ioi (0:ℝ), upLine z n T (Nat.floor (p.cut*n)) y := by
  rw [upperModified_branch_integral z p n T hn hheight]
  have hh := branch_polygon_deform z hz true n (Nat.floor (p.cut*n)) T (modifiedVertices p n)
    (by simpa only [sideSign,↓reduceIte,one_mul] using modifiedVertices_upper p n hn hheight)
  simp only [sideDirection,↓reduceIte] at hh
  simp only [crossing]
  rw [hh,upper_reference_eq]

theorem lowerModified_straight (z : ℝ) (hz : ValidZ z) (p : PolygonFrame) (n : ℕ) (T : ℂ[X])
    (hn : 0 < n) (hheight : 1 ≤ (n:ℝ)*(p.vertex 1).im) :
    (((upperModified p n).map Piece.conj).map (fun q => pieceIntegral q (densityCore z n T))).sum=
      -(∫ y in Iic (0:ℝ), upLine z n T (Nat.floor (p.cut*n)) y) := by
  rw [lowerModified_branch_integral z p n T hn hheight,lowerModified_sum_eq_polyI]
  have hpts : ∀ u ∈ (modifiedVertices p n).map (starRingEnd ℂ),
      0 ≤ u.re ∧ 0 < sideSign false*u.im := by
    intro u hu
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hu
    have hh := modifiedVertices_upper p n hn hheight v hv
    simpa [sideSign] using hh
  have hh := branch_polygon_deform z hz false n (Nat.floor (p.cut*n)) T
    ((modifiedVertices p n).map (starRingEnd ℂ)) hpts
  simp only [sideDirection,Bool.false_eq_true,↓reduceIte] at hh
  simp only [crossing]
  rw [hh,lower_reference_eq]

theorem polygon_line_straight (z : ℝ) (hz : ValidZ z) (p : PolygonFrame) (n : ℕ) (T : ℂ[X])
    (hn : 0 < n) (hheight : 1 ≤ (n:ℝ)*(p.vertex 1).im) :
    -((upperModified p n).map (fun q => pieceIntegral q (densityCore z n T))).sum+
      (((upperModified p n).map Piece.conj).map (fun q => pieceIntegral q (densityCore z n T))).sum=
        -(∫ y : ℝ, upLine z n T (Nat.floor (p.cut*n)) y) := by
  rw [upperModified_straight z hz p n T hn hheight,lowerModified_straight z hz p n T hn hheight]
  obtain ⟨C,q,hC,hq,hq1,hh⟩ := upLine_geometric_bound z hz n T
  have hi := (hh (Nat.floor (p.cut*n))).1
  have he := intervalIntegral.integral_Iic_add_Ioi (hi.integrableOn (s := Iic (0:ℝ))) (hi.integrableOn (s := Ioi (0:ℝ)))
  linear_combination -he
end CatalanCore.Li2.Decay.ContourGeometry
#print axioms CatalanCore.Li2.Decay.ContourGeometry.polygon_line_straight


namespace CatalanCore.Li2.Decay.ContourGeometry
open Polynomial CatalanCore.Li2.Uniform

theorem lineIntegral_const_mul (F : DualFrame) (g : FrameGeometry F) (n : ℕ) (c : ℂ) (f : ℂ → ℂ) :
    lineIntegral g n (fun u => c*f u)=c*lineIntegral g n f := by
  have hs (ps : List CatalanCore.Decay.CurveFamily.Piece) :
      (ps.map (fun q => pieceIntegral q (fun u => c*f u))).sum=
        c*(ps.map (fun q => pieceIntegral q f)).sum := by
    induction ps with
    | nil => simp
    | cons q ps ih =>
      simp only [List.map_cons,List.sum_cons,ih]
      have hi : pieceIntegral q (fun u => c*f u)=c*pieceIntegral q f := by
        simp only [pieceIntegral,mul_assoc,integral_const_mul]
      rw [hi]
      ring
  cases g with
  | pure hp hl hf => simp [lineIntegral]
  | polygon p hp hl hf =>
    simp only [lineIntegral,hs]
    ring

theorem contourDensity_eq (z : ℝ) (n : ℕ) (T : ℂ[X]) :
    contourDensity z n T=(fun u => (((2*Real.pi:ℂ)*Complex.I)⁻¹)*densityCore z n T u) := by
  funext u
  unfold contourDensity densityCore rationalCore
  ring

theorem eventual_height (p : PolygonFrame) :
    ∀ᶠ n : ℕ in atTop, 1 ≤ (n:ℝ)*(p.vertex 1).im := by
  have hy := vertex_one_im_pos p
  filter_upwards [tendsto_natCast_atTop_atTop.eventually
    (eventually_ge_atTop (1/(p.vertex 1).im))] with n hn
  exact (div_le_iff₀ hy).mp hn
end CatalanCore.Li2.Decay.ContourGeometry

namespace CatalanCore.Li2.Decay
open Polynomial CatalanCore.Li2.Uniform ContourGeometry

theorem negative_contour (z : ℝ) (hz : ValidZ z) (hneg : z < 0)
    (F : Frame) (g : FrameGeometry F) (c : ℝ) (hc : frameCut g=some c) (T : ℂ[X]) :
  ∀ᶠ n : ℕ in atTop,
    latticeTail z n (Nat.floor (c*n)) T =
      lineIntegral g n (fun u => ((2*Real.pi:ℂ)*Complex.I)⁻¹*u*weight n u*T.eval u*
        Complex.exp ((Real.log |z|:ℂ)*u)*kernel z u) := by
  cases g with
  | pure hp hl hf => simp [frameCut] at hc
  | polygon p hp hl hf =>
    have hc' : p.cut=c := Option.some.inj hc
    subst c
    filter_upwards [eventual_height p,eventually_ge_atTop (1:ℕ)] with n hh hn
    have hn0 : 0 < n := by omega
    have he := polygon_line_straight z hz p n T hn0 hh
    have hfactor : (fun u => ((2*Real.pi:ℂ)*Complex.I)⁻¹*u*weight n u*T.eval u*
        Complex.exp ((Real.log |z|:ℂ)*u)*kernel z u)=
        fun u => ((2*Real.pi:ℂ)*Complex.I)⁻¹*densityCore z n T u := by
      funext u
      unfold densityCore rationalCore
      ring
    rw [hfactor,lineIntegral_const_mul]
    change latticeTail z n (Nat.floor (p.cut*n)) T=
      ((2*Real.pi:ℂ)*Complex.I)⁻¹*(-((upperModified p n).map (fun q => pieceIntegral q (densityCore z n T))).sum+
        (((upperModified p n).map CatalanCore.Decay.CurveFamily.Piece.conj).map (fun q => pieceIntegral q (densityCore z n T))).sum)
    rw [he,latticeTail_eq_correctedLine z hz]
    simp only [correctedLine,if_neg (not_lt.mpr hneg.le),add_zero]
    ring

theorem positive_contour_ray (z : ℝ) (hz : ValidZ z) (hpos : 0 < z)
    (F : Frame) (g : FrameGeometry F) (c : ℝ) (hc : frameCut g=some c) (T : ℂ[X]) :
  ∀ᶠ n : ℕ in atTop,
    latticeTail z n (Nat.floor (c*n)) T =
      lineIntegral g n (contourDensity z n T)+
        ∫ x in Ici ((Nat.floor (c*n):ℝ)+1/2),
          (-Real.log |z|:ℂ)*(x:ℂ)*weight n (x:ℂ)*T.eval (x:ℂ)*Complex.exp ((Real.log |z| *x:ℝ):ℂ) := by
  cases g with
  | pure hp hl hf => simp [frameCut] at hc
  | polygon p hp hl hf =>
    have hc' : p.cut=c := Option.some.inj hc
    subst c
    filter_upwards [eventual_height p,eventually_ge_atTop (1:ℕ)] with n hh hn
    have hn0 : 0 < n := by omega
    have he := polygon_line_straight z hz p n T hn0 hh
    have hray : (∫ x in Ici ((Nat.floor (p.cut*n):ℝ)+1/2),
          (-Real.log |z|:ℂ)*(x:ℂ)*weight n (x:ℂ)*T.eval (x:ℂ)*Complex.exp ((Real.log |z| *x:ℝ):ℂ))=
        -(Real.log |z|:ℂ)*realTail z n T (Nat.floor (p.cut*n)) := by
      unfold realTail
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        unfold realDensity rationalCore
        simp only [Complex.ofReal_mul,Complex.ofReal_neg]
        ring
    rw [hray,contourDensity_eq,lineIntegral_const_mul,latticeTail_eq_correctedLine z hz]
    change correctedLine z n T (Nat.floor (p.cut*n))=
      ((2*Real.pi:ℂ)*Complex.I)⁻¹*(-((upperModified p n).map (fun q => pieceIntegral q (densityCore z n T))).sum+
        (((upperModified p n).map CatalanCore.Decay.CurveFamily.Piece.conj).map (fun q => pieceIntegral q (densityCore z n T))).sum)+
          -(Real.log |z|:ℂ)*realTail z n T (Nat.floor (p.cut*n))
    rw [he]
    simp only [correctedLine,if_pos hpos]
    ring
end CatalanCore.Li2.Decay
#print axioms CatalanCore.Li2.Decay.negative_contour
#print axioms CatalanCore.Li2.Decay.positive_contour_ray
