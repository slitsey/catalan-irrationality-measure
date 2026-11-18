module
public import CatalanCore.Decay.ContourIdentity
public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
@[expose] public section
set_option Elab.async false
open MeasureTheory Set Filter
open scoped Topology
namespace CatalanCore.Tools.VerticalResidues

noncomputable def regularPart (g : ℂ → ℂ) (p : ℂ) : ℂ → ℂ := dslope (dslope g p) p

theorem regularPart_differentiableOn (g : ℂ → ℂ) (S : Set ℂ) (p : ℂ)
    (hp : S ∈ nhds p) (hg : DifferentiableOn ℂ g S) : DifferentiableOn ℂ (regularPart g p) S := by
  exact (Complex.differentiableOn_dslope hp).mpr ((Complex.differentiableOn_dslope hp).mpr hg)

theorem regularPart_eq (g : ℂ → ℂ) (p u : ℂ) (hu : u ≠ p) :
    regularPart g p u=g u/(u-p)^2-g p/(u-p)^2-deriv g p/(u-p) := by
  rw [regularPart,dslope_of_ne _ hu,slope_def_field,dslope_of_ne _ hu,slope_def_field,dslope_same]
  field_simp
  <;> ring

theorem vertical_rectangle (H : ℂ → ℂ) (a b T : ℝ) (hab : a ≤ b)
    (hH : ∀ u : ℂ, u.re ∈ Icc a b → DifferentiableAt ℂ H u) :
    (∫ y in -T..T, (Complex.I*H ((a:ℂ)+(y:ℂ)*Complex.I)-
      Complex.I*H ((b:ℂ)+(y:ℂ)*Complex.I)))=
      (∫ x in a..b, H ((x:ℂ)-(T:ℂ)*Complex.I))-
        (∫ x in a..b, H ((x:ℂ)+(T:ℂ)*Complex.I)) := by
  have hline (c : ℝ) (hc : c ∈ Icc a b) : Continuous (fun y : ℝ => H ((c:ℂ)+(y:ℂ)*Complex.I)) := by
    apply continuous_iff_continuousAt.mpr
    intro y
    apply ((hH _ (by simpa only [Complex.add_re,Complex.ofReal_re,Complex.mul_I_re,
      Complex.ofReal_im,neg_zero,add_zero] using hc)).continuousAt).comp
    fun_prop
  have hA := (hline a ⟨le_refl _,hab⟩).intervalIntegrable (μ := volume) (-T) T
  have hB := (hline b ⟨hab,le_refl _⟩).intervalIntegrable (μ := volume) (-T) T
  have hh := Complex.integral_boundary_rect_eq_zero_of_differentiableOn H
    ((a:ℂ)-(T:ℂ)*Complex.I) ((b:ℂ)+(T:ℂ)*Complex.I) (by
      intro u hu
      apply (hH u _).differentiableWithinAt
      have hc := hu.1
      simpa only [Complex.sub_re,Complex.add_re,Complex.ofReal_re,Complex.mul_I_re,
        Complex.ofReal_im,neg_zero,sub_zero,add_zero,uIcc_of_le hab,Set.mem_preimage] using hc)
  simp only [Complex.sub_re,Complex.add_re,Complex.ofReal_re,Complex.mul_I_re,
    Complex.ofReal_im,Complex.sub_im,Complex.add_im,Complex.mul_I_im,neg_zero,sub_zero,
    add_zero,zero_sub,zero_add,smul_eq_mul] at hh
  rw [intervalIntegral.integral_sub (hA.const_mul Complex.I) (hB.const_mul Complex.I),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul]
  have hneg : (fun x : ℝ => H ((x:ℂ)+((-T:ℝ):ℂ)*Complex.I))=
      (fun x : ℝ => H ((x:ℂ)-(T:ℂ)*Complex.I)) := by
    funext x
    congr 1
    push_cast
    ring
  rw [hneg] at hh
  linear_combination -hh

theorem horizontal_zero (H : ℂ → ℂ) (a b s C : ℝ) (hab : a ≤ b)
    (hdec : ∀ T : ℝ, 1 ≤ T → ∀ x ∈ Icc a b,
      ‖H ((x:ℂ)+((s*T:ℝ):ℂ)*Complex.I)‖ ≤ C/T) :
    Tendsto (fun T : ℝ => ∫ x in a..b, H ((x:ℂ)+((s*T:ℝ):ℂ)*Complex.I)) atTop (nhds 0) := by
  have hbound : ∀ᶠ T : ℝ in atTop,
      ‖∫ x in a..b, H ((x:ℂ)+((s*T:ℝ):ℂ)*Complex.I)‖ ≤ (C*(b-a))/T := by
    filter_upwards [eventually_ge_atTop (1:ℝ)] with T hT
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b)
      (fun x hx => hdec T hT x (by
        rw [uIoc_of_le hab] at hx
        exact ⟨hx.1.le,hx.2⟩))
    rw [abs_of_nonneg (sub_nonneg.mpr hab)] at hh
    convert hh using 1 <;> ring
  have hlim : Tendsto (fun T : ℝ => (C*(b-a))/T) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  exact squeeze_zero_norm' hbound hlim

theorem vertical_difference_zero (H : ℂ → ℂ) (a b C : ℝ) (hab : a ≤ b)
    (hH : ∀ u : ℂ, u.re ∈ Icc a b → DifferentiableAt ℂ H u)
    (hi : Integrable (fun y : ℝ => Complex.I*H ((a:ℂ)+(y:ℂ)*Complex.I)-
      Complex.I*H ((b:ℂ)+(y:ℂ)*Complex.I)))
    (hdec : ∀ T : ℝ, 1 ≤ T → ∀ x ∈ Icc a b,
      ‖H ((x:ℂ)-(T:ℂ)*Complex.I)‖ ≤ C/T ∧ ‖H ((x:ℂ)+(T:ℂ)*Complex.I)‖ ≤ C/T) :
    (∫ y : ℝ, (Complex.I*H ((a:ℂ)+(y:ℂ)*Complex.I)-
      Complex.I*H ((b:ℂ)+(y:ℂ)*Complex.I)))=0 := by
  have hplus := horizontal_zero H a b 1 C hab (by
    intro T hT x hx
    simpa only [one_mul] using (hdec T hT x hx).2)
  have hminus := horizontal_zero H a b (-1) C hab (by
    intro T hT x hx
    simpa only [neg_one_mul,Complex.ofReal_neg,neg_mul,one_mul,sub_eq_add_neg] using (hdec T hT x hx).1)
  have ht := hminus.sub hplus
  simp only [sub_zero] at ht
  have ht' : Tendsto (fun T : ℝ => ∫ y in -T..T,
      (Complex.I*H ((a:ℂ)+(y:ℂ)*Complex.I)-Complex.I*H ((b:ℂ)+(y:ℂ)*Complex.I)))
      atTop (nhds 0) := by
    apply ht.congr'
    apply Eventually.of_forall
    intro T
    simpa only [one_mul,neg_one_mul,Complex.ofReal_neg,neg_mul,sub_eq_add_neg] using
      (vertical_rectangle H a b T hab hH).symm
  exact tendsto_nhds_unique (intervalIntegral_tendsto_integral hi tendsto_neg_atTop_atBot tendsto_id) ht'
end CatalanCore.Tools.VerticalResidues
#print axioms CatalanCore.Tools.VerticalResidues.regularPart_differentiableOn
#print axioms CatalanCore.Tools.VerticalResidues.regularPart_eq
#print axioms CatalanCore.Tools.VerticalResidues.vertical_rectangle

#print axioms CatalanCore.Tools.VerticalResidues.vertical_difference_zero



namespace CatalanCore.Tools.VerticalResidues
open Complex
open CatalanCore.Decay.LineInt

theorem remainder_bound (f B A p u : ℂ) (C T : ℝ) (hT : 1 ≤ T)
    (hgap : T ≤ ‖u-p‖) (hbound : ‖f‖ ≤ C/T) :
    ‖f-B/(u-p)^2-A/(u-p)‖ ≤ (C+‖B‖+‖A‖)/T := by
  have hT0 : 0 < T := by linarith
  have hsq : T ≤ ‖u-p‖^2 := by nlinarith
  have h1 : ‖B‖/‖u-p‖^2 ≤ ‖B‖/T := div_le_div_of_nonneg_left (norm_nonneg _) hT0 hsq
  have h2 : ‖A‖/‖u-p‖ ≤ ‖A‖/T := div_le_div_of_nonneg_left (norm_nonneg _) hT0 hgap
  have hh := (norm_sub_le (f-B/(u-p)^2) (A/(u-p))).trans
    (add_le_add (norm_sub_le f (B/(u-p)^2)) (le_refl ‖A/(u-p)‖))
  simp only [norm_div,norm_pow] at hh
  calc
    _ ≤ C/T+‖B‖/T+‖A‖/T := by linarith
    _ = _ := by ring

theorem regularPart_bound (F g : ℂ → ℂ) (p u : ℂ) (C T : ℝ) (hT : 1 ≤ T)
    (hgap : T ≤ ‖u-p‖) (hF : F u=g u/(u-p)^2) (hbound : ‖F u‖ ≤ C/T) :
    ‖regularPart g p u‖ ≤ (C+‖g p‖+‖deriv g p‖)/T := by
  have hu : u ≠ p := by intro he; simp only [he,sub_self,norm_zero] at hgap; linarith
  rw [regularPart_eq g p u hu,← hF]
  exact remainder_bound (F u) (g p) (deriv g p) p u C T hT hgap hbound

theorem vertical_double_pole (F g : ℂ → ℂ) (S : Set ℂ) (a b p C : ℝ)
    (hap : a < p) (hpb : p < b) (hS : IsOpen S)
    (hstrip : ∀ u : ℂ, u.re ∈ Icc a b → u ∈ S) (hg : DifferentiableOn ℂ g S)
    (hF : ∀ u ∈ S, u ≠ (p:ℂ) → F u=g u/(u-(p:ℂ))^2)
    (hia : Integrable (fun y : ℝ => I*F ((a:ℂ)+(y:ℂ)*I)))
    (hib : Integrable (fun y : ℝ => I*F ((b:ℂ)+(y:ℂ)*I)))
    (hdec : ∀ T : ℝ, 1 ≤ T → ∀ x ∈ Icc a b,
      ‖F ((x:ℂ)-(T:ℂ)*I)‖ ≤ C/T ∧ ‖F ((x:ℂ)+(T:ℂ)*I)‖ ≤ C/T) :
    (∫ y : ℝ, I*F ((a:ℂ)+(y:ℂ)*I))-(∫ y : ℝ, I*F ((b:ℂ)+(y:ℂ)*I))=
      -((2*Real.pi:ℂ)*I)*deriv g (p:ℂ) := by
  have hab : a ≤ b := hap.le.trans hpb.le
  have hpS : (p:ℂ) ∈ S := hstrip _ (by simpa only [ofReal_re] using ⟨hap.le,hpb.le⟩)
  let H := regularPart g (p:ℂ)
  let B := g (p:ℂ)
  let A := deriv g (p:ℂ)
  let V : ℝ → ℂ := fun y => I*F ((a:ℂ)+(y:ℂ)*I)-I*F ((b:ℂ)+(y:ℂ)*I)
  let D : ℝ → ℂ := fun y => I*(1/(lz (a-p) y)^2)-I*(1/(lz (b-p) y)^2)
  let P : ℝ → ℂ := fun y => I*(1/lz (a-p) y)-I*(1/lz (b-p) y)
  have ha : a-p ≠ 0 := by linarith
  have hb : b-p ≠ 0 := by linarith
  have hV : Integrable V := hia.sub hib
  have hD : Integrable D := ((integrable_inv_pow_lz ha (by norm_num : 2 ≤ (2:ℕ))).const_mul I).sub
    ((integrable_inv_pow_lz hb (by norm_num : 2 ≤ (2:ℕ))).const_mul I)
  have hP : Integrable P := integrable_diff_simple ha hb
  have hpoint (c : ℝ) (hc : c ∈ Icc a b) (hcp : c ≠ p) (y : ℝ) :
      H ((c:ℂ)+(y:ℂ)*I)=F ((c:ℂ)+(y:ℂ)*I)-B/(lz (c-p) y)^2-A/lz (c-p) y := by
    have huS : (c:ℂ)+(y:ℂ)*I ∈ S := hstrip _ (by
      simpa only [add_re,ofReal_re,mul_I_re,ofReal_im,neg_zero,add_zero] using hc)
    have hne : (c:ℂ)+(y:ℂ)*I ≠ (p:ℂ) := by
      intro he
      have hh := congrArg Complex.re he
      simp only [add_re,ofReal_re,mul_I_re,ofReal_im,neg_zero,add_zero] at hh
      exact hcp hh
    have he : ((c:ℂ)+(y:ℂ)*I)-(p:ℂ)=lz (c-p) y := by unfold lz; push_cast; ring
    dsimp only [H,B,A]
    rw [regularPart_eq g (p:ℂ) _ hne,← hF _ huS hne,he]
  have hrel (y : ℝ) : I*H ((a:ℂ)+(y:ℂ)*I)-I*H ((b:ℂ)+(y:ℂ)*I)=
      V y-B*D y-A*P y := by
    rw [hpoint a ⟨le_refl _,hab⟩ (by linarith),hpoint b ⟨hab,le_refl _⟩ (by linarith)]
    dsimp only [V,D,P]
    ring
  have hiH : Integrable (fun y : ℝ => I*H ((a:ℂ)+(y:ℂ)*I)-I*H ((b:ℂ)+(y:ℂ)*I)) :=
    ((hV.sub (hD.const_mul B)).sub (hP.const_mul A)).congr (Eventually.of_forall fun y => (hrel y).symm)
  have hHd : ∀ u : ℂ, u.re ∈ Icc a b → DifferentiableAt ℂ H u := by
    intro u hu
    exact (regularPart_differentiableOn g S (p:ℂ) (hS.mem_nhds hpS) hg).differentiableAt
      (hS.mem_nhds (hstrip u hu))
  have hHdec : ∀ T : ℝ, 1 ≤ T → ∀ x ∈ Icc a b,
      ‖H ((x:ℂ)-(T:ℂ)*I)‖ ≤ (C+‖B‖+‖A‖)/T ∧
      ‖H ((x:ℂ)+(T:ℂ)*I)‖ ≤ (C+‖B‖+‖A‖)/T := by
    intro T hT x hx
    have hxminus : ((x:ℂ)-(T:ℂ)*I).re ∈ Icc a b := by
      simpa only [sub_re,ofReal_re,mul_I_re,ofReal_im,neg_zero,sub_zero] using hx
    have hxplus : ((x:ℂ)+(T:ℂ)*I).re ∈ Icc a b := by
      simpa only [add_re,ofReal_re,mul_I_re,ofReal_im,neg_zero,add_zero] using hx
    have hgapminus : T ≤ ‖((x:ℂ)-(T:ℂ)*I)-(p:ℂ)‖ := by
      have hh := Complex.abs_im_le_norm (((x:ℂ)-(T:ℂ)*I)-(p:ℂ))
      simpa only [sub_im,ofReal_im,mul_I_im,ofReal_re,zero_sub,sub_zero,abs_neg,
        abs_of_nonneg (by linarith : 0 ≤ T)] using hh
    have hgapplus : T ≤ ‖((x:ℂ)+(T:ℂ)*I)-(p:ℂ)‖ := by
      have hh := Complex.abs_im_le_norm (((x:ℂ)+(T:ℂ)*I)-(p:ℂ))
      simpa only [sub_im,add_im,ofReal_im,mul_I_im,ofReal_re,zero_add,sub_zero,
        abs_of_nonneg (by linarith : 0 ≤ T)] using hh
    have hnminus : (x:ℂ)-(T:ℂ)*I ≠ (p:ℂ) := by
      intro he
      simp only [he,sub_self,norm_zero] at hgapminus
      linarith
    have hnplus : (x:ℂ)+(T:ℂ)*I ≠ (p:ℂ) := by
      intro he
      simp only [he,sub_self,norm_zero] at hgapplus
      linarith
    exact ⟨regularPart_bound F g (p:ℂ) _ C T hT hgapminus (hF _ (hstrip _ hxminus) hnminus) (hdec T hT x hx).1,
      regularPart_bound F g (p:ℂ) _ C T hT hgapplus (hF _ (hstrip _ hxplus) hnplus) (hdec T hT x hx).2⟩
  have hzero := vertical_difference_zero H a b (C+‖B‖+‖A‖) hab hHd hiH hHdec
  have hDi : (∫ y : ℝ, D y)=0 := by
    rw [show D=(fun y : ℝ => I*(1/(lz (a-p) y)^2)-I*(1/(lz (b-p) y)^2)) from rfl,
      integral_sub ((integrable_inv_pow_lz ha (by norm_num : 2 ≤ (2:ℕ))).const_mul I)
        ((integrable_inv_pow_lz hb (by norm_num : 2 ≤ (2:ℕ))).const_mul I),
      integral_pow_inv ha (by norm_num : 2 ≤ (2:ℕ)),integral_pow_inv hb (by norm_num : 2 ≤ (2:ℕ)),sub_self]
  have hPi : (∫ y : ℝ, P y)=(-2*(Real.pi:ℂ))*I := by
    rw [show P=(fun y : ℝ => I*(1/lz (a-p) y)-I*(1/lz (b-p) y)) from rfl,
      integral_diff_simple ha hb]
    simp only [sg,if_neg (show ¬0 < a-p by linarith),if_pos (show 0 < b-p by linarith)]
    push_cast
    ring
  have hval : (∫ y : ℝ, I*H ((a:ℂ)+(y:ℂ)*I)-I*H ((b:ℂ)+(y:ℂ)*I))=
      (∫ y : ℝ, V y)-B*(∫ y : ℝ, D y)-A*(∫ y : ℝ, P y) := by
    rw [integral_congr_ae (Eventually.of_forall hrel)]
    have hsub2 := integral_sub (hV.sub (hD.const_mul B)) (hP.const_mul A)
    have hsub1 := integral_sub hV (hD.const_mul B)
    simp only [Pi.sub_apply] at hsub2 hsub1
    rw [hsub2,hsub1,integral_const_mul,integral_const_mul]
  rw [hDi,hPi] at hval
  have hVi : (∫ y : ℝ, V y)=(∫ y : ℝ, I*F ((a:ℂ)+(y:ℂ)*I))-
      (∫ y : ℝ, I*F ((b:ℂ)+(y:ℂ)*I)) := integral_sub hia hib
  rw [hVi,hzero] at hval
  dsimp only [A] at hval
  linear_combination -hval
end CatalanCore.Tools.VerticalResidues
#print axioms CatalanCore.Tools.VerticalResidues.vertical_double_pole


namespace CatalanCore.Tools.VerticalResidues
open Complex

theorem vertical_levels (H : ℂ → ℂ) (a b s t : ℝ) (hab : a ≤ b)
    (hH : ∀ u : ℂ, u.re ∈ Icc a b → DifferentiableAt ℂ H u) :
    (∫ y in s..t, (I*H ((a:ℂ)+(y:ℂ)*I)-I*H ((b:ℂ)+(y:ℂ)*I)))=
      (∫ x in a..b, H ((x:ℂ)+(s:ℂ)*I))-(∫ x in a..b, H ((x:ℂ)+(t:ℂ)*I)) := by
  have hline (c : ℝ) (hc : c ∈ Icc a b) : Continuous (fun y : ℝ => H ((c:ℂ)+(y:ℂ)*I)) := by
    apply continuous_iff_continuousAt.mpr
    intro y
    apply ((hH _ (by simpa only [add_re,ofReal_re,mul_I_re,ofReal_im,neg_zero,add_zero] using hc)).continuousAt).comp
    fun_prop
  have hA := (hline a ⟨le_refl _,hab⟩).intervalIntegrable (μ := volume) s t
  have hB := (hline b ⟨hab,le_refl _⟩).intervalIntegrable (μ := volume) s t
  have hh := Complex.integral_boundary_rect_eq_zero_of_differentiableOn H
    ((a:ℂ)+(s:ℂ)*I) ((b:ℂ)+(t:ℂ)*I) (by
      intro u hu
      apply (hH u _).differentiableWithinAt
      have hc := hu.1
      simpa only [add_re,ofReal_re,mul_I_re,ofReal_im,neg_zero,add_zero,uIcc_of_le hab,mem_preimage] using hc)
  simp only [add_re,ofReal_re,mul_I_re,ofReal_im,add_im,mul_I_im,neg_zero,add_zero,zero_add,smul_eq_mul] at hh
  rw [intervalIntegral.integral_sub (hA.const_mul I) (hB.const_mul I),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul]
  linear_combination -hh

theorem vertical_difference_jump (Hp Hm : ℂ → ℂ) (a b C : ℝ) (hab : a ≤ b)
    (hHp : ∀ u : ℂ, u.re ∈ Icc a b → DifferentiableAt ℂ Hp u)
    (hHm : ∀ u : ℂ, u.re ∈ Icc a b → DifferentiableAt ℂ Hm u)
    (hip : IntegrableOn (fun y : ℝ => I*Hp ((a:ℂ)+(y:ℂ)*I)-I*Hp ((b:ℂ)+(y:ℂ)*I)) (Ioi 0))
    (him : IntegrableOn (fun y : ℝ => I*Hm ((a:ℂ)+(y:ℂ)*I)-I*Hm ((b:ℂ)+(y:ℂ)*I)) (Iic 0))
    (hdec : ∀ T : ℝ, 1 ≤ T → ∀ x ∈ Icc a b,
      ‖Hm ((x:ℂ)-(T:ℂ)*I)‖ ≤ C/T ∧ ‖Hp ((x:ℂ)+(T:ℂ)*I)‖ ≤ C/T) :
    (∫ y in Ioi (0:ℝ), I*Hp ((a:ℂ)+(y:ℂ)*I)-I*Hp ((b:ℂ)+(y:ℂ)*I))+
      (∫ y in Iic (0:ℝ), I*Hm ((a:ℂ)+(y:ℂ)*I)-I*Hm ((b:ℂ)+(y:ℂ)*I))=
        (∫ x in a..b, Hp (x:ℂ))-(∫ x in a..b, Hm (x:ℂ)) := by
  have hplus := horizontal_zero Hp a b 1 C hab (by
    intro T hT x hx
    simpa only [one_mul] using (hdec T hT x hx).2)
  have hminus := horizontal_zero Hm a b (-1) C hab (by
    intro T hT x hx
    simpa only [neg_one_mul,Complex.ofReal_neg,neg_mul,one_mul,sub_eq_add_neg] using (hdec T hT x hx).1)
  have hstep (T : ℝ) :
      (∫ y in (0:ℝ)..T, I*Hp ((a:ℂ)+(y:ℂ)*I)-I*Hp ((b:ℂ)+(y:ℂ)*I))+
        (∫ y in -T..(0:ℝ), I*Hm ((a:ℂ)+(y:ℂ)*I)-I*Hm ((b:ℂ)+(y:ℂ)*I))=
          ((∫ x in a..b, Hp (x:ℂ))-(∫ x in a..b, Hm (x:ℂ)))+
            (∫ x in a..b, Hm ((x:ℂ)+((-1*T:ℝ):ℂ)*I))-
            (∫ x in a..b, Hp ((x:ℂ)+((1*T:ℝ):ℂ)*I)) := by
    rw [vertical_levels Hp a b 0 T hab hHp,vertical_levels Hm a b (-T) 0 hab hHm]
    simp only [ofReal_zero,zero_mul,add_zero,neg_one_mul,one_mul]
    ring
  have hL := (intervalIntegral_tendsto_integral_Ioi (0:ℝ) hip tendsto_id).add
    (intervalIntegral_tendsto_integral_Iic (0:ℝ) him tendsto_neg_atTop_atBot)
  have hR := ((tendsto_const_nhds (x := (∫ x in a..b, Hp (x:ℂ))-(∫ x in a..b, Hm (x:ℂ)))).add hminus).sub hplus
  simp only [add_zero,sub_zero] at hR
  apply tendsto_nhds_unique hL
  exact hR.congr' (Eventually.of_forall (fun T => (hstep T).symm))
end CatalanCore.Tools.VerticalResidues
#print axioms CatalanCore.Tools.VerticalResidues.vertical_difference_jump

namespace CatalanCore.Tools.VerticalResidues
open Complex
open CatalanCore.Decay.LineInt

noncomputable def principalDifference (a b p : ℝ) (B A : ℂ) (y : ℝ) : ℂ :=
  B*(I*(1/(lz (a-p) y)^2)-I*(1/(lz (b-p) y)^2))+
    A*(I*(1/lz (a-p) y)-I*(1/lz (b-p) y))

theorem principalDifference_integral (a b p : ℝ) (hap : a < p) (hpb : p < b) (B A : ℂ) :
    Integrable (principalDifference a b p B A) ∧
      (∫ y : ℝ, principalDifference a b p B A y)=-((2*Real.pi:ℂ)*I)*A := by
  have ha : a-p ≠ 0 := by linarith
  have hb : b-p ≠ 0 := by linarith
  have hD : Integrable (fun y : ℝ => I*(1/(lz (a-p) y)^2)-I*(1/(lz (b-p) y)^2)) := ((integrable_inv_pow_lz ha (by norm_num : 2 ≤ (2:ℕ))).const_mul I).sub
    ((integrable_inv_pow_lz hb (by norm_num : 2 ≤ (2:ℕ))).const_mul I)
  have hP := integrable_diff_simple ha hb
  refine ⟨(hD.const_mul B).add (hP.const_mul A),?_⟩
  unfold principalDifference
  rw [integral_add (hD.const_mul B) (hP.const_mul A),integral_const_mul,integral_const_mul,
    integral_sub ((integrable_inv_pow_lz ha (by norm_num : 2 ≤ (2:ℕ))).const_mul I)
      ((integrable_inv_pow_lz hb (by norm_num : 2 ≤ (2:ℕ))).const_mul I),
    integral_pow_inv ha (by norm_num : 2 ≤ (2:ℕ)),integral_pow_inv hb (by norm_num : 2 ≤ (2:ℕ)),
    integral_diff_simple ha hb]
  simp only [sg,if_neg (show ¬0 < a-p by linarith),if_pos (show 0 < b-p by linarith)]
  push_cast
  ring

theorem vertical_double_pole_jump (Fp Fm g Q : ℂ → ℂ) (S : Set ℂ) (a b p C : ℝ) (c : ℂ)
    (hap : a < p) (hpb : p < b) (hS : IsOpen S)
    (hstrip : ∀ u : ℂ, u.re ∈ Icc a b → u ∈ S)
    (hg : DifferentiableOn ℂ g S) (hQ : DifferentiableOn ℂ Q S)
    (hFp : ∀ u ∈ S, u ≠ (p:ℂ) → Fp u=g u/(u-(p:ℂ))^2+c*Q u)
    (hFm : ∀ u ∈ S, u ≠ (p:ℂ) → Fm u=g u/(u-(p:ℂ))^2-c*Q u)
    (hip : IntegrableOn (fun y : ℝ => I*Fp ((a:ℂ)+(y:ℂ)*I)-I*Fp ((b:ℂ)+(y:ℂ)*I)) (Ioi 0))
    (him : IntegrableOn (fun y : ℝ => I*Fm ((a:ℂ)+(y:ℂ)*I)-I*Fm ((b:ℂ)+(y:ℂ)*I)) (Iic 0))
    (hdec : ∀ T : ℝ, 1 ≤ T → ∀ x ∈ Icc a b,
      ‖Fm ((x:ℂ)-(T:ℂ)*I)‖ ≤ C/T ∧ ‖Fp ((x:ℂ)+(T:ℂ)*I)‖ ≤ C/T) :
    (∫ y in Ioi (0:ℝ), I*Fp ((a:ℂ)+(y:ℂ)*I)-I*Fp ((b:ℂ)+(y:ℂ)*I))+
      (∫ y in Iic (0:ℝ), I*Fm ((a:ℂ)+(y:ℂ)*I)-I*Fm ((b:ℂ)+(y:ℂ)*I))=
        -((2*Real.pi:ℂ)*I)*deriv g (p:ℂ)+(2*c)*(∫ x in a..b, Q (x:ℂ)) := by
  have hab : a ≤ b := hap.le.trans hpb.le
  have hpS : (p:ℂ) ∈ S := hstrip _ (by simpa only [ofReal_re] using ⟨hap.le,hpb.le⟩)
  let B := g (p:ℂ)
  let A := deriv g (p:ℂ)
  let Hp : ℂ → ℂ := fun u => regularPart g (p:ℂ) u+c*Q u
  let Hm : ℂ → ℂ := fun u => regularPart g (p:ℂ) u-c*Q u
  let Vp : ℝ → ℂ := fun y => I*Fp ((a:ℂ)+(y:ℂ)*I)-I*Fp ((b:ℂ)+(y:ℂ)*I)
  let Vm : ℝ → ℂ := fun y => I*Fm ((a:ℂ)+(y:ℂ)*I)-I*Fm ((b:ℂ)+(y:ℂ)*I)
  let D := principalDifference a b p B A
  have hD := (principalDifference_integral a b p hap hpb B A).1
  have hDi := (principalDifference_integral a b p hap hpb B A).2
  have hremp (u : ℂ) (hu : u ∈ S) (hne : u ≠ (p:ℂ)) :
      Hp u=Fp u-B/(u-(p:ℂ))^2-A/(u-(p:ℂ)) := by
    dsimp only [Hp,B,A]
    rw [regularPart_eq g (p:ℂ) u hne,hFp u hu hne]
    ring
  have hremm (u : ℂ) (hu : u ∈ S) (hne : u ≠ (p:ℂ)) :
      Hm u=Fm u-B/(u-(p:ℂ))^2-A/(u-(p:ℂ)) := by
    dsimp only [Hm,B,A]
    rw [regularPart_eq g (p:ℂ) u hne,hFm u hu hne]
    ring
  have hline (x : ℝ) (hx : x ∈ Icc a b) (hxp : x ≠ p) (y : ℝ) :
      ((x:ℂ)+(y:ℂ)*I) ∈ S ∧ ((x:ℂ)+(y:ℂ)*I) ≠ (p:ℂ) ∧
      ((x:ℂ)+(y:ℂ)*I)-(p:ℂ)=lz (x-p) y := by
    refine ⟨hstrip _ (by simpa only [add_re,ofReal_re,mul_I_re,ofReal_im,neg_zero,add_zero] using hx),?_,?_⟩
    · intro he
      have hh := congrArg Complex.re he
      simp only [add_re,ofReal_re,mul_I_re,ofReal_im,neg_zero,add_zero] at hh
      exact hxp hh
    · unfold lz
      push_cast
      ring
  have hrelp (y : ℝ) : I*Hp ((a:ℂ)+(y:ℂ)*I)-I*Hp ((b:ℂ)+(y:ℂ)*I)=Vp y-D y := by
    have ha := hline a ⟨le_refl _,hab⟩ (by linarith) y
    have hb := hline b ⟨hab,le_refl _⟩ (by linarith) y
    rw [hremp _ ha.1 ha.2.1,hremp _ hb.1 hb.2.1,ha.2.2,hb.2.2]
    dsimp only [Vp,D,principalDifference]
    ring
  have hrelm (y : ℝ) : I*Hm ((a:ℂ)+(y:ℂ)*I)-I*Hm ((b:ℂ)+(y:ℂ)*I)=Vm y-D y := by
    have ha := hline a ⟨le_refl _,hab⟩ (by linarith) y
    have hb := hline b ⟨hab,le_refl _⟩ (by linarith) y
    rw [hremm _ ha.1 ha.2.1,hremm _ hb.1 hb.2.1,ha.2.2,hb.2.2]
    dsimp only [Vm,D,principalDifference]
    ring
  have hreg := regularPart_differentiableOn g S (p:ℂ) (hS.mem_nhds hpS) hg
  have hHpd : ∀ u : ℂ, u.re ∈ Icc a b → DifferentiableAt ℂ Hp u := by
    intro u hu
    exact (hreg.add (hQ.const_mul c)).differentiableAt (hS.mem_nhds (hstrip u hu))
  have hHmd : ∀ u : ℂ, u.re ∈ Icc a b → DifferentiableAt ℂ Hm u := by
    intro u hu
    exact (hreg.sub (hQ.const_mul c)).differentiableAt (hS.mem_nhds (hstrip u hu))
  have hipH : IntegrableOn (fun y : ℝ => I*Hp ((a:ℂ)+(y:ℂ)*I)-I*Hp ((b:ℂ)+(y:ℂ)*I)) (Ioi 0) :=
    (hip.sub hD.integrableOn).congr (Eventually.of_forall fun y => (hrelp y).symm)
  have himH : IntegrableOn (fun y : ℝ => I*Hm ((a:ℂ)+(y:ℂ)*I)-I*Hm ((b:ℂ)+(y:ℂ)*I)) (Iic 0) :=
    (him.sub hD.integrableOn).congr (Eventually.of_forall fun y => (hrelm y).symm)
  have hHdec : ∀ T : ℝ, 1 ≤ T → ∀ x ∈ Icc a b,
      ‖Hm ((x:ℂ)-(T:ℂ)*I)‖ ≤ (C+‖B‖+‖A‖)/T ∧
      ‖Hp ((x:ℂ)+(T:ℂ)*I)‖ ≤ (C+‖B‖+‖A‖)/T := by
    intro T hT x hx
    have hgapm : T ≤ ‖((x:ℂ)-(T:ℂ)*I)-(p:ℂ)‖ := by
      have hh := Complex.abs_im_le_norm (((x:ℂ)-(T:ℂ)*I)-(p:ℂ))
      simpa only [sub_im,ofReal_im,mul_I_im,ofReal_re,zero_sub,sub_zero,abs_neg,abs_of_nonneg (by linarith : 0 ≤ T)] using hh
    have hgapp : T ≤ ‖((x:ℂ)+(T:ℂ)*I)-(p:ℂ)‖ := by
      have hh := Complex.abs_im_le_norm (((x:ℂ)+(T:ℂ)*I)-(p:ℂ))
      simpa only [sub_im,add_im,ofReal_im,mul_I_im,ofReal_re,zero_add,sub_zero,abs_of_nonneg (by linarith : 0 ≤ T)] using hh
    have hmS := hstrip ((x:ℂ)-(T:ℂ)*I) (by simpa using hx)
    have hpS' := hstrip ((x:ℂ)+(T:ℂ)*I) (by simpa using hx)
    have hmn : (x:ℂ)-(T:ℂ)*I ≠ (p:ℂ) := by intro he; simp only [he,sub_self,norm_zero] at hgapm; linarith
    have hpn : (x:ℂ)+(T:ℂ)*I ≠ (p:ℂ) := by intro he; simp only [he,sub_self,norm_zero] at hgapp; linarith
    rw [hremm _ hmS hmn,hremp _ hpS' hpn]
    exact ⟨remainder_bound (Fm ((x:ℂ)-(T:ℂ)*I)) B A (p:ℂ) _ C T hT hgapm (hdec T hT x hx).1,
      remainder_bound (Fp ((x:ℂ)+(T:ℂ)*I)) B A (p:ℂ) _ C T hT hgapp (hdec T hT x hx).2⟩
  have hjump := vertical_difference_jump Hp Hm a b (C+‖B‖+‖A‖) hab hHpd hHmd hipH himH hHdec
  have hreal : (∫ x in a..b, Hp (x:ℂ))-(∫ x in a..b, Hm (x:ℂ))=
      (2*c)*(∫ x in a..b, Q (x:ℂ)) := by
    have hpi : IntervalIntegrable (fun x : ℝ => Hp (x:ℂ)) volume a b := by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le hab]
      intro x hx
      have hf : ContinuousAt Hp (x:ℂ) := (hHpd (x:ℂ) (by simpa only [ofReal_re] using hx)).continuousAt
      exact (hf.comp (show ContinuousAt (fun y : ℝ => (y:ℂ)) x by fun_prop)).continuousWithinAt
    have hmi : IntervalIntegrable (fun x : ℝ => Hm (x:ℂ)) volume a b := by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le hab]
      intro x hx
      have hf : ContinuousAt Hm (x:ℂ) := (hHmd (x:ℂ) (by simpa only [ofReal_re] using hx)).continuousAt
      exact (hf.comp (show ContinuousAt (fun y : ℝ => (y:ℂ)) x by fun_prop)).continuousWithinAt
    have hsub := intervalIntegral.integral_sub hpi hmi
    rw [← hsub,← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x hx
    dsimp only [Hp,Hm]
    ring
  have hVp : (∫ y in Ioi (0:ℝ), I*Hp ((a:ℂ)+(y:ℂ)*I)-I*Hp ((b:ℂ)+(y:ℂ)*I))=
      (∫ y in Ioi (0:ℝ), Vp y)-(∫ y in Ioi (0:ℝ), D y) := by
    rw [integral_congr_ae (Eventually.of_forall hrelp)]
    have hh := integral_sub hip (hD.integrableOn (s := Ioi (0:ℝ)))
    simpa only [Pi.sub_apply] using hh
  have hVm : (∫ y in Iic (0:ℝ), I*Hm ((a:ℂ)+(y:ℂ)*I)-I*Hm ((b:ℂ)+(y:ℂ)*I))=
      (∫ y in Iic (0:ℝ), Vm y)-(∫ y in Iic (0:ℝ), D y) := by
    rw [integral_congr_ae (Eventually.of_forall hrelm)]
    have hh := integral_sub him (hD.integrableOn (s := Iic (0:ℝ)))
    simpa only [Pi.sub_apply] using hh
  rw [hVp,hVm,hreal] at hjump
  have hDi' : (∫ y in Ioi (0:ℝ), D y)+(∫ y in Iic (0:ℝ), D y)=
      -((2*Real.pi:ℂ)*I)*A := by
    rw [add_comm,intervalIntegral.integral_Iic_add_Ioi hD.integrableOn hD.integrableOn]
    exact hDi
  dsimp only [A] at hDi'
  change (∫ y in Ioi (0:ℝ), Vp y)+(∫ y in Iic (0:ℝ), Vm y)= _
  linear_combination hjump+hDi'
end CatalanCore.Tools.VerticalResidues
#print axioms CatalanCore.Tools.VerticalResidues.vertical_double_pole_jump


namespace CatalanCore.Tools.VerticalResidues

noncomputable def exponentialPoleNumerator (R A : ℂ → ℂ) (L p u : ℂ) : ℂ :=
  R u*Complex.exp (L*u)*(A u-(u-p)*deriv A u-L*(u-p)*A u)

theorem exponentialPoleNumerator_value (R A : ℂ → ℂ) (L p : ℂ) :
    exponentialPoleNumerator R A L p p=R p*Complex.exp (L*p)*A p := by
  simp only [exponentialPoleNumerator,sub_self,zero_mul,mul_zero,sub_zero]

theorem exponentialPoleNumerator_deriv (R A : ℂ → ℂ) (L p : ℂ)
    (hR : DifferentiableAt ℂ R p) (hA : DifferentiableAt ℂ A p)
    (hdA : DifferentiableAt ℂ (deriv A) p) :
    deriv (exponentialPoleNumerator R A L p) p=A p*Complex.exp (L*p)*deriv R p := by
  let h : ℂ → ℂ := fun u => u-p
  have hh : HasDerivAt h 1 p := (hasDerivAt_id p).sub_const p
  have he : HasDerivAt (fun u : ℂ => Complex.exp (L*u)) (Complex.exp (L*p)*L) p := by
    simpa only [Function.comp_def,id_eq,mul_one] using
      (Complex.hasDerivAt_exp (L*p)).comp p ((hasDerivAt_id p).const_mul L)
  have hinner := (hA.hasDerivAt.sub (hh.mul hdA.hasDerivAt)).sub ((hh.const_mul L).mul hA.hasDerivAt)
  have hd := (hR.hasDerivAt.mul he).mul hinner
  have hfinal : HasDerivAt (exponentialPoleNumerator R A L p)
      (A p*Complex.exp (L*p)*deriv R p) p := by
    convert hd using 1
    · funext u
      rfl
    · dsimp only [h]
      simp only [Pi.mul_apply,Pi.sub_apply,id_eq,sub_self,mul_zero,zero_mul,sub_zero,add_zero,one_mul,mul_one]
      ring
  exact hfinal.deriv

theorem exponentialPoleNumerator_split (R A : ℂ → ℂ) (L p u : ℂ)
    (hA : DifferentiableAt ℂ A u) (hu : u ≠ p) :
    R u*Complex.exp (L*u)*(-deriv (fun w : ℂ => A w/(w-p)) u-L*(A u/(u-p)))=
      exponentialPoleNumerator R A L p u/(u-p)^2 := by
  have hne : u-p ≠ 0 := sub_ne_zero.mpr hu
  have hb : HasDerivAt (fun w : ℂ => A w/(w-p))
      ((deriv A u*(u-p)-A u)/(u-p)^2) u := by
    convert hA.hasDerivAt.div ((hasDerivAt_id u).sub_const p) hne using 1
    · funext w
      rfl
    · simp only [mul_one,id_eq]
  rw [hb.deriv]
  unfold exponentialPoleNumerator
  field_simp
  <;> ring
end CatalanCore.Tools.VerticalResidues
#print axioms CatalanCore.Tools.VerticalResidues.exponentialPoleNumerator_deriv
#print axioms CatalanCore.Tools.VerticalResidues.exponentialPoleNumerator_split

