module
public import CatalanCore.Tools.JoukowskiLog
@[expose] public section
set_option Elab.async false
open MeasureTheory Set Complex Filter Topology
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert
open CatalanCore.Tools.Joukowski

theorem log_product_of_phase_bound (A B : ℂ) (hA : A ≠ 0) (hB : B ≠ 0) (k : ℤ)
    (hp : |Complex.arg (A*B)-Complex.arg A-Complex.arg B-2*Real.pi*(k:ℝ)| < Real.pi) :
    Complex.log (A*B)=Complex.log A+Complex.log B+2*Real.pi*Complex.I*(k:ℂ) := by
  let D : ℂ := Complex.log (A*B)-Complex.log A-Complex.log B-2*Real.pi*Complex.I*(k:ℂ)
  have hk : Complex.exp (2*Real.pi*Complex.I*(k:ℂ))=1 :=
    Complex.exp_eq_one_iff.mpr ⟨k,by ring⟩
  have he : Complex.exp D=1 := by
    simp only [D,Complex.exp_sub,Complex.exp_log (mul_ne_zero hA hB),
      Complex.exp_log hA,Complex.exp_log hB,hk]
    field_simp
  have him : D.im=Complex.arg (A*B)-Complex.arg A-Complex.arg B-2*Real.pi*(k:ℝ) := by
    simp only [D,Complex.sub_im,Complex.log_im,Complex.mul_im,Complex.mul_re,
      Complex.ofReal_re,Complex.ofReal_im,Complex.intCast_re,Complex.intCast_im,
      Complex.I_re,Complex.I_im,mul_zero,zero_mul,mul_one,one_mul,sub_zero,zero_add,add_zero]
    norm_num <;> ring
  have hbounds := abs_lt.mp hp
  have hzero : D=0 := Complex.exp_inj_of_neg_pi_lt_of_le_pi
    (by rw [him]; exact hbounds.1) (by rw [him]; exact hbounds.2.le)
    (by simp; exact Real.pi_pos) (by simp; exact Real.pi_pos.le) (by simpa using he)
  dsimp only [D] at hzero
  linear_combination hzero

theorem log_affine_of_center_nonreal (A H η : ℂ) (hH : H ≠ 0) (hη : η.im ≠ 0)
    (hfac : A=(-H)*η)
    (hslit : ∀ y : ℝ, |y| ≤ 1 → A+H*(y:ℂ) ∈ Complex.slitPlane)
    (x : ℝ) (hx : x ∈ Icc (-1:ℝ) 1) :
    Complex.log (A+H*(x:ℂ))-Complex.log (η-(x:ℂ))=Complex.log A-Complex.log η := by
  have hp : 0 < |η.im| := abs_pos.mpr hη
  have hnorm : 0 < ‖H‖ := norm_pos_iff.mpr hH
  have hf (y : ℝ) : A+H*(y:ℂ)=(-H)*(η-(y:ℂ)) := by rw [hfac]; ring
  have ha (y : ℝ) (hy : |y| ≤ 1) : A-(-H)*(y:ℂ) ∈ Complex.slitPlane := by
    convert hslit y hy using 1 <;> ring
  have ha' (y : ℝ) (_ : |y| ≤ 1) : η-1*(y:ℂ) ∈ Complex.slitPlane := by
    right
    simpa using hη
  have hm' (y : ℝ) (_ : |y| ≤ 1) : |η.im| ≤ ‖η-1*(y:ℂ)‖ := by
    simpa using Complex.abs_im_le_norm (η-(y:ℂ))
  have hm (y : ℝ) (hy : |y| ≤ 1) : ‖H‖*|η.im| ≤ ‖A-(-H)*(y:ℂ)‖ := by
    have he : A-(-H)*(y:ℂ)=(-H)*(η-(y:ℂ)) := by rw [hfac]; ring
    rw [he,norm_mul,norm_neg]
    exact mul_le_mul_of_nonneg_left (by simpa using hm' y hy) (norm_nonneg H)
  have hd := CatalanMeasure.GenD.Cert.LogSeriesBand.log_affine_drift A (-H) η 1
    (‖H‖*|η.im|) |η.im| (mul_pos hnorm hp) hp ha ha' hm hm' (abs_le.mpr hx)
  have hn : 1*A-(-H)*η=0 := by rw [hfac]; ring
  rw [hn,norm_zero,zero_div,zero_mul] at hd
  have he := norm_le_zero_iff.mp hd
  have hterm : A-(-H)*(x:ℂ)=A+H*(x:ℂ) := by ring
  rw [hterm,one_mul] at he
  exact sub_eq_zero.mp he

theorem log_affine_of_center_real (A H η : ℂ) (hH : H ≠ 0) (hη : η.im=0)
    (hoff : 1 < |η.re|) (hfac : A=(-H)*η) (x : ℝ) (hx : x ∈ Icc (-1:ℝ) 1) :
    Complex.log (A+H*(x:ℂ))-Complex.log (η-(x:ℂ))=Complex.log A-Complex.log η := by
  have hηR : η=(η.re:ℂ) := by apply Complex.ext <;> simp [hη]
  have hη0 : η.re ≠ 0 := by intro hz; simp [hz] at hoff; linarith
  have hηne : η ≠ 0 := by intro hz; exact hη0 (by rw [hz]; rfl)
  have hA : A ≠ 0 := by rw [hfac]; exact mul_ne_zero (neg_ne_zero.mpr hH) hηne
  let r : ℝ := (η.re-x)/η.re
  have hr : 0 < r := by
    dsimp only [r]
    by_cases hp : 0 < η.re
    · rw [abs_of_pos hp] at hoff
      exact div_pos (by linarith [hx.2]) hp
    · have hn : η.re < 0 := lt_of_le_of_ne (le_of_not_gt hp) hη0
      rw [abs_of_neg hn] at hoff
      exact div_pos_of_neg_of_neg (by linarith [hx.1]) hn
  have heη : η-(x:ℂ)=η*(r:ℂ) := by
    rw [hηR]
    dsimp only [r]
    push_cast
    field_simp [hη0]
    <;> ring
  have heA : A+H*(x:ℂ)=A*(r:ℂ) := by
    calc
      _ = (-H)*(η-(x:ℂ)) := by rw [hfac]; ring
      _ = _ := by rw [heη,hfac]; ring
  rw [heA,heη,Complex.log_mul_ofReal r hr A hA,Complex.log_mul_ofReal r hr η hηne]
  ring

theorem log_affine_of_center (A H η : ℂ) (hH : H ≠ 0) (hoff : 1 < jc η)
    (hfac : A=(-H)*η)
    (hslit : ∀ y : ℝ, |y| ≤ 1 → A+H*(y:ℂ) ∈ Complex.slitPlane)
    (x : ℝ) (hx : x ∈ Icc (-1:ℝ) 1) :
    Complex.log (A+H*(x:ℂ))-Complex.log (η-(x:ℂ))=Complex.log A-Complex.log η := by
  by_cases him : η.im=0
  · have hηR : η=(η.re:ℂ) := by apply Complex.ext <;> simp [him]
    have hηoff : 1 < |η.re| := by
      by_contra hh
      have hx : η.re ∈ Icc (-1:ℝ) 1 := abs_le.mp (le_of_not_gt hh)
      have hc := jc_ofReal hx
      rw [← hηR] at hc
      linarith
    exact log_affine_of_center_real A H η hH him hηoff hfac x hx
  · exact log_affine_of_center_nonreal A H η hH him hfac hslit x hx

theorem affine_slit_of_quadrant (A H η : ℂ) (hH : H ≠ 0) (hoff : 1 < jc η)
    (hfac : A=(-H)*η)
    (hquad : ∀ y : ℝ, |y| ≤ 1 → 0 ≤ (A+H*(y:ℂ)).re ∧ 0 ≤ (A+H*(y:ℂ)).im) :
    ∀ y : ℝ, |y| ≤ 1 → A+H*(y:ℂ) ∈ Complex.slitPlane := by
  intro y hy
  have hf : A+H*(y:ℂ)=(-H)*(η-(y:ℂ)) := by rw [hfac]; ring
  have hn : A+H*(y:ℂ) ≠ 0 := by
    rw [hf]
    exact mul_ne_zero (neg_ne_zero.mpr hH) (sub_ofReal_ne_zero hoff (abs_le.mp hy))
  by_cases him : (A+H*(y:ℂ)).im=0
  · left
    have hre : (A+H*(y:ℂ)).re ≠ 0 := by
      intro hz
      apply hn
      apply Complex.ext <;> simp [hz,him]
    exact lt_of_le_of_ne (hquad y hy).1 (Ne.symm hre)
  · exact Or.inr him

theorem log_affine_branch (A H η : ℂ) (hH : H ≠ 0) (hoff : 1 < jc η)
    (hfac : A=(-H)*η) (k : ℤ)
    (hquad : ∀ y : ℝ, |y| ≤ 1 → 0 ≤ (A+H*(y:ℂ)).re ∧ 0 ≤ (A+H*(y:ℂ)).im)
    (hcenter : |Complex.arg A-Complex.arg (-H)-Complex.arg η-2*Real.pi*(k:ℝ)| < Real.pi)
    (x : ℝ) (hx : x ∈ Icc (-1:ℝ) 1) :
    Complex.log (A+H*(x:ℂ)) = Complex.log (-H)+Complex.log (η-(x:ℂ))+2*Real.pi*Complex.I*(k:ℂ) := by
  have hη0 : η ≠ 0 := by
    have hh := sub_ofReal_ne_zero hoff (show (0:ℝ) ∈ Icc (-1:ℝ) 1 by constructor <;> norm_num)
    simpa using hh
  have hp : |Complex.arg ((-H)*η)-Complex.arg (-H)-Complex.arg η-2*Real.pi*(k:ℝ)| < Real.pi := by
    rwa [← hfac]
  have hc := log_product_of_phase_bound (-H) η (neg_ne_zero.mpr hH) hη0 k hp
  rw [← hfac] at hc
  have hd := log_affine_of_center A H η hH hoff hfac (affine_slit_of_quadrant A H η hH hoff hfac hquad) x hx
  linear_combination hd+hc

#print axioms log_affine_of_center_real
#print axioms log_affine_of_center
#print axioms affine_slit_of_quadrant
#print axioms log_affine_branch

#print axioms log_product_of_phase_bound
#print axioms log_affine_of_center_nonreal
end CatalanCore.Li2.DecayCert
