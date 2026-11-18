module
public import CatalanCore.Li2.DecayCert.Compile.Basic
@[expose] public section
set_option Elab.async false
open Polynomial MeasureTheory Set Filter Topology
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert
open CatalanCore.Li2.Decay CatalanCore.Tools.Joukowski
noncomputable section
theorem logUnit_remainder (z : ℂ) (t : ℝ) (ht : 0 ≤ t ∧ t < 1) (hz : ‖z‖ ≤ t) (J : ℕ) :
    ‖Complex.log (1+z)-(∑ n ∈ Finset.range (J+1),logUnitCoeff n*z^n)‖ ≤
      t^(J+1)/(((J+1:ℕ):ℝ)*(1-t)) := by
  have he : (∑ n ∈ Finset.range (J+1),logUnitCoeff n*z^n)=Complex.logTaylor (J+1) z := by
    unfold Complex.logTaylor
    apply Finset.sum_congr rfl
    intro n hn
    dsimp [logUnitCoeff]
    rw [pow_succ]
    ring
  rw [he]
  have hh := Complex.norm_log_sub_logTaylor_le J (hz.trans_lt ht.2)
  calc
    _ ≤ ‖z‖^(J+1)/((J+1:ℕ):ℝ)/(1-‖z‖) := by convert! hh using 1 <;> push_cast <;> ring
    _ ≤ t^(J+1)/((J+1:ℕ):ℝ)/(1-‖z‖) :=
      div_le_div_of_nonneg_right (div_le_div_of_nonneg_right
        (pow_le_pow_left₀ (norm_nonneg z) hz _) (by positivity)) (by linarith [hz.trans_lt ht.2])
    _ ≤ t^(J+1)/((J+1:ℕ):ℝ)/(1-t) :=
      div_le_div_of_nonneg_left (div_nonneg (pow_nonneg ht.1 _) (Nat.cast_nonneg _)) (sub_pos.mpr ht.2) (by linarith)
    _ = _ := by rw [div_div]

noncomputable def logAffineCoeff (a b : ℂ) (n : ℕ) : ℝ :=
  if n=0 then Real.log ‖a‖ else (logUnitCoeff n*(b/a)^n).re

theorem logAffine_model_eval (a b : ℂ) (J : ℕ) (u : ℝ) :
    evalModel ((List.range (J+1)).map (logAffineCoeff a b)) u=
      Real.log ‖a‖+(∑ n ∈ Finset.range (J+1),logUnitCoeff n*((b/a)*(u:ℂ))^n).re := by
  rw [evalModel_map_range]
  have hc (n : ℕ) : logAffineCoeff a b n*u^n=
      (if n=0 then Real.log ‖a‖ else 0)+(logUnitCoeff n*((b/a)*(u:ℂ))^n).re := by
    by_cases hn : n=0
    · subst n; simp [logAffineCoeff,logUnitCoeff]
    · simp only [logAffineCoeff,hn,ite_false,zero_add]
      have he : logUnitCoeff n*((b/a)*(u:ℂ))^n=(logUnitCoeff n*(b/a)^n)*(u:ℂ)^n := by rw [mul_pow]; ring
      rw [he,← Complex.ofReal_pow]
      simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
  simp_rw [hc,Finset.sum_add_distrib]
  rw [← Complex.re_sum]
  simp only [Finset.sum_ite_eq',Finset.mem_range,Nat.zero_lt_succ,ite_true]

theorem logAffine_taylor_remainder (a b : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hsep : ‖b‖*r < ‖a‖) (J : ℕ) :
    Models (fun u => Real.log ‖a+b*(u:ℂ)‖)
      ((List.range (J+1)).map (logAffineCoeff a b)) r
      ((‖b‖*r/‖a‖)^(J+1)/(((J+1:ℕ):ℝ)*(1-‖b‖*r/‖a‖))) := by
  have haPos : 0 < ‖a‖ := lt_of_le_of_lt (mul_nonneg (norm_nonneg b) hr) hsep
  have ha0 : a ≠ 0 := norm_pos_iff.mp haPos
  let t := ‖b‖*r/‖a‖
  have ht : 0 ≤ t ∧ t < 1 := ⟨div_nonneg (mul_nonneg (norm_nonneg b) hr) haPos.le,
    (div_lt_one haPos).mpr hsep⟩
  refine ⟨hr,div_nonneg (pow_nonneg ht.1 _)
    (mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr ht.2.le)),?_⟩
  intro u hu
  let v := (b/a)*(u:ℂ)
  have hv : ‖v‖ ≤ t := by
    dsimp [v,t]
    rw [norm_mul,norm_div,Complex.norm_real,Real.norm_eq_abs]
    calc
      _ ≤ (‖b‖/‖a‖)*r := mul_le_mul_of_nonneg_left hu (by positivity)
      _ = _ := by ring
  have hv0 : 1+v ≠ 0 := Complex.slitPlane_ne_zero (Complex.mem_slitPlane_of_norm_lt_one (hv.trans_lt ht.2))
  have he : a*(1+v)=a+b*(u:ℂ) := by dsimp [v]; field_simp
  have hfun : Real.log ‖a+b*(u:ℂ)‖=Real.log ‖a‖+(Complex.log (1+v)).re := by
    rw [← he,norm_mul,Real.log_mul haPos.ne' (norm_ne_zero_iff.mpr hv0),Complex.log_re]
  change |Real.log ‖a+b*(u:ℂ)‖-evalModel ((List.range (J+1)).map (logAffineCoeff a b)) u| ≤ _
  rw [hfun,logAffine_model_eval]
  have hre := Complex.abs_re_le_norm (Complex.log (1+v)-
    (∑ n ∈ Finset.range (J+1),logUnitCoeff n*v^n))
  rw [Complex.sub_re] at hre
  have hh := hre.trans (logUnit_remainder v t ht hv J)
  convert! hh using 1 <;> congr 1 <;> ring

noncomputable def invUnitCoeff (k n : ℕ) : ℂ :=
  (-1:ℂ)^n*((k+n-1).choose n:ℂ)

noncomputable def invAffineCoeff (a b : ℂ) (k n : ℕ) : ℂ :=
  (-1:ℂ)^n*((k+n-1).choose n:ℂ)*b^n/a^(k+n)

theorem hasTaylorSeriesAt_invUnit (k : ℕ) (hk : 0 < k) :
    HasTaylorSeriesAt (fun u : ℂ => (1+u)^(-(k:ℤ))) (invUnitCoeff k) 0 := by
  rcases k with _|k
  · omega
  refine ⟨1,by norm_num,?_⟩
  intro u hu
  have hs := hasSum_choose_mul_geometric_of_norm_lt_one k (r:=-u) (by simpa using hu)
  have hfun : 1/(1-(-u))^(k+1)=(1+u)^(-((k+1:ℕ):ℤ)) := by
    simp only [sub_neg_eq_add,zpow_neg,zpow_natCast,one_div]
  rw [hfun] at hs
  simp only [zero_add]
  convert! hs using 1
  funext n
  have hidx : k+1+n-1=n+k := by omega
  have hch : (n+k).choose k=(n+k).choose n := Nat.choose_symm_add.symm
  rw [neg_pow u n]
  simp only [invUnitCoeff,hidx]
  rw [hch]
  ring

theorem hasTaylorSeriesAt_invAffine (a b : ℂ) (ha : a ≠ 0) (k : ℕ) (hk : 0 < k) :
    HasTaylorSeriesAt (fun u : ℂ => (a+b*u)^(-(k:ℤ))) (invAffineCoeff a b k) 0 := by
  have hh := ((hasTaylorSeriesAt_invUnit k hk).comp_mul (b/a)).const_mul (a^(-(k:ℤ)))
  have hc : (fun n => a^(-(k:ℤ))*(invUnitCoeff k n*(b/a)^n))=invAffineCoeff a b k := by
    funext n
    simp only [invUnitCoeff,invAffineCoeff,zpow_neg,zpow_natCast,div_pow,pow_add,mul_inv_rev,div_eq_mul_inv]
    ring
  rw [hc] at hh
  convert! hh using 1
  funext u
  rw [← mul_zpow]
  have he : a*(1+b/a*u)=a+b*u := by field_simp
  rw [he]

theorem evalModel_complex_re (c : ℕ → ℂ) (J : ℕ) (u : ℝ) :
    evalModel ((List.range (J+1)).map (fun n => (c n).re)) u=
      (∑ n ∈ Finset.range (J+1),c n*(u:ℂ)^n).re := by
  rw [evalModel_map_range,Complex.re_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [← Complex.ofReal_pow]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]

theorem invAffine_taylor_remainder (a b : ℂ) (k : ℕ) (hk : 0 < k)
    (R rt : ℝ) (hrt : 0 ≤ rt ∧ rt < R) (hsep : ‖b‖*R < ‖a‖) (J : ℕ) :
    Models (fun u => ((a+b*(u:ℂ))^(-(k:ℤ))).re)
      ((List.range (J+1)).map (fun n => (invAffineCoeff a b k n).re)) rt
      ((‖a‖-‖b‖*R)^(-(k:ℤ))*(rt/R)^(J+1)/(1-rt/R)) := by
  have hR : 0 < R := hrt.1.trans_lt hrt.2
  have haPos : 0 < ‖a‖ := lt_of_le_of_lt (mul_nonneg (norm_nonneg b) hR.le) hsep
  have ha0 : a ≠ 0 := norm_pos_iff.mp haPos
  let m := ‖a‖-‖b‖*R
  have hm : 0 < m := sub_pos.mpr hsep
  have hlower (z : ℂ) (hz : z ∈ Metric.ball 0 R) : m ≤ ‖a+b*z‖ := by
    have hz' : ‖z‖ < R := by simpa only [Metric.mem_ball,dist_zero_right] using hz
    have hmul : ‖b*z‖ ≤ ‖b‖*R := by rw [norm_mul]; exact mul_le_mul_of_nonneg_left hz'.le (norm_nonneg _)
    have hh := norm_sub_norm_le a (-(b*z))
    rw [norm_neg,sub_neg_eq_add] at hh
    dsimp only [m]
    linarith
  have hne : ∀ z ∈ Metric.ball (0:ℂ) R,a+b*z ≠ 0 := by
    intro z hz hzero
    have hh := hlower z hz
    rw [hzero,norm_zero] at hh
    linarith
  have hAff : Differentiable ℂ (fun z : ℂ => a+b*z) := by
    intro z
    exact (((hasDerivAt_id z).const_mul b).const_add a).differentiableAt
  have hf : DifferentiableOn ℂ (fun z : ℂ => (a+b*z)^(-(k:ℤ))) (Metric.ball 0 R) :=
    hAff.differentiableOn.zpow (Or.inl hne)
  have hM : ∀ z ∈ Metric.ball (0:ℂ) R,‖(a+b*z)^(-(k:ℤ))‖ ≤ m^(-(k:ℤ)) := by
    intro z hz
    simp only [zpow_neg,zpow_natCast,norm_inv,norm_pow]
    simpa only [one_div] using div_le_div_of_nonneg_left (by norm_num : (0:ℝ)≤1) (pow_pos hm k)
      (pow_le_pow_left₀ hm.le (hlower z hz) k)
  have hb := hasTaylorSeriesAt_invAffine a b ha0 k hk
  have hrat : 0 ≤ rt/R ∧ rt/R < 1 := ⟨div_nonneg hrt.1 hR.le,(div_lt_one hR).mpr hrt.2⟩
  refine ⟨hrt.1,div_nonneg (mul_nonneg (by positivity) (pow_nonneg hrat.1 _))
    (sub_nonneg.mpr hrat.2.le),?_⟩
  intro u hu
  rw [evalModel_complex_re]
  have hh := taylor_remainder_bound hb R rt (m^(-(k:ℤ))) hR hrt hf hM (u:ℂ)
    (by simpa only [Complex.norm_real,Real.norm_eq_abs] using hu) (J+1)
  have hre := Complex.abs_re_le_norm ((a+b*(u:ℂ))^(-(k:ℤ))-
    (∑ n ∈ Finset.range (J+1),invAffineCoeff a b k n*(u:ℂ)^n))
  rw [Complex.sub_re] at hre
  exact hre.trans hh

theorem regularOK_sound (a b : CQ) (rt : ℚ) (w : RegularWitness)
    (hc : regularOK a b rt w=true) :
    2 ≤ w.order ∧ 0 < (w.normLo:ℝ) ∧ (w.normLo:ℝ) ≤ ‖cqReal a‖ ∧
      ‖cqReal a‖ ≤ (w.normHi:ℝ) ∧ 0 ≤ (w.directionHi:ℝ) ∧
      ‖cqReal b‖ ≤ (w.directionHi:ℝ) ∧ 0 ≤ (rt:ℝ) ∧
      (w.directionHi:ℝ)*(rt:ℝ) < (w.normLo:ℝ) := by
  have hh := of_decide_eq_true hc
  rcases hh with ⟨hord,hlo,hlohi,hAsqlo,hAsqhi,hdir,hBsq,hrt,hsep⟩
  have hLo : (0:ℝ)<(w.normLo:ℝ) := by exact_mod_cast hlo
  have hLH : (w.normLo:ℝ) ≤ (w.normHi:ℝ) := by exact_mod_cast hlohi
  have hAl : (w.normLo:ℝ)^2 ≤ ‖cqReal a‖^2 := by rw [← cqSq_eq_norm_sq]; exact_mod_cast hAsqlo
  have hAh : ‖cqReal a‖^2 ≤ (w.normHi:ℝ)^2 := by rw [← cqSq_eq_norm_sq]; exact_mod_cast hAsqhi
  have hD : (0:ℝ) ≤ (w.directionHi:ℝ) := by exact_mod_cast hdir
  have hB : ‖cqReal b‖^2 ≤ (w.directionHi:ℝ)^2 := by rw [← cqSq_eq_norm_sq]; exact_mod_cast hBsq
  refine ⟨hord,hLo,?_,?_,hD,?_,?_,?_⟩
  · nlinarith [norm_nonneg (cqReal a)]
  · nlinarith [norm_nonneg (cqReal a)]
  · nlinarith [norm_nonneg (cqReal b)]
  · exact_mod_cast hrt
  · exact_mod_cast hsep

def freScalarCoeff (a b : CQ) (terms j : ℕ) : SE :=
  if j=0 then seSub (seReMulLog terms a a) (seRat a.1)
  else if j=1 then seReMulLog terms b a
  else seRat (cqScale ((-1:ℚ)^j/((j:ℚ)*(j-1)))
    (cqDiv (cqPow b j) (cqPow a (j-1)))).1

theorem freScalarCoeff_value (a b : CQ) (terms j : ℕ) :
    (freScalarCoeff a b terms j).value=freCoeff (cqReal a) (cqReal b) j := by
  by_cases h0 : j=0
  · subst j
    simp [freScalarCoeff,freCoeff,seSub_value,seReMulLog_value,seRat_value,cqReal_re,Complex.sub_re]
  by_cases h1 : j=1
  · subst j
    simp [freScalarCoeff,freCoeff,seReMulLog_value]
  simp only [freScalarCoeff,freCoeff,h0,h1,ite_false]
  rw [seRat_value,← cqReal_re,cqReal_scale,cqReal_div,cqReal_pow,cqReal_pow]
  push_cast
  congr 1
  simp only [div_eq_mul_inv,mul_inv_rev,inv_pow]
  ring

theorem geometric_error_mono (m M u v D : ℝ) (N : ℕ)
    (hm : 0 ≤ m) (hmM : m ≤ M) (hu : 0 ≤ u) (huv : u ≤ v) (hv : v < 1) (hD : 0 ≤ D) :
    m*u^N/(D*(1-u)) ≤ M*v^N/(D*(1-v)) := by
  have hv0 : 0 ≤ v := hu.trans huv
  have hgeo : u^N/(1-u) ≤ v^N/(1-v) := by
    calc
      _ ≤ v^N/(1-u) := div_le_div_of_nonneg_right (pow_le_pow_left₀ hu huv _) (by linarith)
      _ ≤ _ := div_le_div_of_nonneg_left (pow_nonneg hv0 _) (sub_pos.mpr hv) (by linarith)
  have hmul := mul_le_mul hmM hgeo (div_nonneg (pow_nonneg hu _) (by linarith)) (hm.trans hmM)
  have hh := div_le_div_of_nonneg_right hmul hD
  convert! hh using 1 <;> simp only [div_eq_mul_inv,mul_inv_rev] <;> ring

theorem Models.onIcc {f : ℝ → ℝ} {a : List ℝ} {R err : ℝ}
    (hm : Models f a R err) (l r : ℝ) (hlr : l ≤ r)
    (hbound : ∀ u ∈ Icc l r,|u| ≤ R) : ModelsOn f a l r err :=
  ⟨hlr,hm.2.1,fun u hu => hm.2.2 u (hbound u hu)⟩

theorem ModelsOn.error_mono {f : ℝ → ℝ} {a : List ℝ} {l r err err' : ℝ}
    (hm : ModelsOn f a l r err) (he : err ≤ err') : ModelsOn f a l r err' :=
  ⟨hm.1,hm.2.1.trans he,fun u hu => (hm.2.2 u hu).trans he⟩

theorem regularCompile_fre_shape (a b : CQ) (lo hi : ℚ) (w : RegularWitness)
    (m : CompiledModel) (hc : regularCompile (.fre a b) lo hi w=some m) :
    regularOK a b (max |lo| |hi|) w=true ∧ 0 ≤ a.1 ∧
      m.coeff=(List.range (w.order+1)).map (freScalarCoeff a b w.terms) ∧
      m.error=seRat (w.normHi*(w.directionHi*(max |lo| |hi|)/w.normLo)^(w.order+1)/
        ((w.order+1:ℚ)*w.order*(1-w.directionHi*(max |lo| |hi|)/w.normLo))) := by
  dsimp only [regularCompile] at hc
  split_ifs at hc with hgate
  have he := Option.some.inj hc
  cases he
  simp only [Bool.and_eq_true,decide_eq_true_eq] at hgate
  exact ⟨hgate.1,hgate.2,rfl,rfl⟩

theorem regularCompile_fre_sound (a b : CQ) (lo hi : ℚ) (w : RegularWitness)
    (m : CompiledModel) (hdom : lo ≤ hi) (hc : regularCompile (.fre a b) lo hi w=some m) :
    ModelsOn (CellExpr.fre a b).value (m.coeff.map ScalarExpr.value) lo hi m.error.value := by
  rcases regularCompile_fre_shape a b lo hi w m hc with ⟨hcheck,haq,hcoeff,herror⟩
  let rtQ := max |lo| |hi|
  let rt : ℝ := (rtQ:ℝ)
  rcases regularOK_sound a b rtQ w hcheck with ⟨hJ,hlo,hloa,hahi,hdir,hbn,hrt,hsep⟩
  have ha : 0 ≤ (cqReal a).re := by rw [cqReal_re]; exact_mod_cast haq
  have hmulp : ‖cqReal b‖*rt ≤ (w.directionHi:ℝ)*rt := mul_le_mul_of_nonneg_right hbn hrt
  have hsepA : ‖cqReal b‖*rt < ‖cqReal a‖ := hmulp.trans_lt (hsep.trans_le hloa)
  have hFM := fre_taylor_remainder (cqReal a) (cqReal b) rt ha hrt hsepA w.order hJ
  have hratio : ‖cqReal b‖*rt/‖cqReal a‖ ≤ (w.directionHi:ℝ)*rt/(w.normLo:ℝ) := by
    calc
      _ ≤ (w.directionHi:ℝ)*rt/‖cqReal a‖ := div_le_div_of_nonneg_right hmulp (norm_nonneg _)
      _ ≤ _ := div_le_div_of_nonneg_left (mul_nonneg hdir hrt) hlo hloa
  have hproxylt : (w.directionHi:ℝ)*rt/(w.normLo:ℝ) < 1 := (div_lt_one hlo).mpr hsep
  have hErr := geometric_error_mono ‖cqReal a‖ (w.normHi:ℝ)
    (‖cqReal b‖*rt/‖cqReal a‖) ((w.directionHi:ℝ)*rt/(w.normLo:ℝ))
    (((w.order+1:ℕ):ℝ)*(w.order:ℝ)) (w.order+1) (norm_nonneg _) hahi
    (div_nonneg (mul_nonneg (norm_nonneg _) hrt) (norm_nonneg _)) hratio hproxylt (by positivity)
  have herr : ‖cqReal a‖*(‖cqReal b‖*rt/‖cqReal a‖)^(w.order+1)/
      (((w.order+1:ℕ):ℝ)*(w.order:ℝ)*(1-‖cqReal b‖*rt/‖cqReal a‖)) ≤ m.error.value := by
    rw [herror,seRat_value]
    push_cast
    push_cast at hErr
    simpa only [rt,rtQ,Rat.cast_max,Rat.cast_abs] using hErr
  have hco : m.coeff.map ScalarExpr.value=
      (List.range (w.order+1)).map (freCoeff (cqReal a) (cqReal b)) := by
    rw [hcoeff,List.map_map]
    simp only [Function.comp_def,freScalarCoeff_value]
  change ModelsOn (fun u => ((cqReal a+cqReal b*(u:ℂ))*Complex.log (cqReal a+cqReal b*(u:ℂ))-
    (cqReal a+cqReal b*(u:ℂ))).re) (m.coeff.map ScalarExpr.value) lo hi m.error.value
  rw [hco]
  apply (hFM.onIcc lo hi (by exact_mod_cast hdom) ?_).error_mono herr
  intro u hu
  change |u| ≤ ((max |lo| |hi|:ℚ):ℝ)
  rw [Rat.cast_max,Rat.cast_abs,Rat.cast_abs]
  exact abs_le.mpr
    ⟨by have := le_max_left |(lo:ℝ)| |(hi:ℝ)|; have := neg_abs_le (lo:ℝ); linarith [hu.1],
      by have := le_max_right |(lo:ℝ)| |(hi:ℝ)|; have := le_abs_self (hi:ℝ); linarith [hu.2]⟩

def logScalarCoeff (a b : CQ) (terms j : ℕ) : SE :=
  if j=0 then seLogNorm terms a
  else seRat (cqScale ((-1:ℚ)^(j+1)/(j:ℚ)) (cqPow (cqDiv b a) j)).1

theorem logScalarCoeff_value (a b : CQ) (terms j : ℕ) :
    (logScalarCoeff a b terms j).value=logAffineCoeff (cqReal a) (cqReal b) j := by
  by_cases h0 : j=0
  · subst j
    simp [logScalarCoeff,logAffineCoeff,seLogNorm_value]
  simp only [logScalarCoeff,logAffineCoeff,h0,ite_false]
  rw [seRat_value,← cqReal_re,cqReal_scale,cqReal_pow,cqReal_div]
  push_cast
  congr 1
  simp only [logUnitCoeff,div_eq_mul_inv,pow_succ]
  ring

theorem regularCompile_log_shape (a b : CQ) (lo hi : ℚ) (w : RegularWitness)
    (m : CompiledModel) (hc : regularCompile (.logAffine a b) lo hi w=some m) :
    regularOK a b (max |lo| |hi|) w=true ∧
      m.coeff=(List.range (w.order+1)).map (logScalarCoeff a b w.terms) ∧
      m.error=seRat ((w.directionHi*(max |lo| |hi|)/w.normLo)^(w.order+1)/
        ((w.order+1:ℚ)*(1-w.directionHi*(max |lo| |hi|)/w.normLo))) := by
  dsimp only [regularCompile] at hc
  split_ifs at hc with hgate
  have he := Option.some.inj hc
  cases he
  exact ⟨hgate,rfl,rfl⟩

theorem regularCompile_log_sound (a b : CQ) (lo hi : ℚ) (w : RegularWitness)
    (m : CompiledModel) (hdom : lo ≤ hi) (hc : regularCompile (.logAffine a b) lo hi w=some m) :
    ModelsOn (CellExpr.logAffine a b).value (m.coeff.map ScalarExpr.value) lo hi m.error.value := by
  rcases regularCompile_log_shape a b lo hi w m hc with ⟨hcheck,hcoeff,herror⟩
  let rtQ := max |lo| |hi|
  let rt : ℝ := (rtQ:ℝ)
  rcases regularOK_sound a b rtQ w hcheck with ⟨hJ,hlo,hloa,hahi,hdir,hbn,hrt,hsep⟩
  have hmulp : ‖cqReal b‖*rt ≤ (w.directionHi:ℝ)*rt := mul_le_mul_of_nonneg_right hbn hrt
  have hsepA : ‖cqReal b‖*rt < ‖cqReal a‖ := hmulp.trans_lt (hsep.trans_le hloa)
  have hFM := logAffine_taylor_remainder (cqReal a) (cqReal b) rt hrt hsepA w.order
  have hratio : ‖cqReal b‖*rt/‖cqReal a‖ ≤ (w.directionHi:ℝ)*rt/(w.normLo:ℝ) := by
    calc
      _ ≤ (w.directionHi:ℝ)*rt/‖cqReal a‖ := div_le_div_of_nonneg_right hmulp (norm_nonneg _)
      _ ≤ _ := div_le_div_of_nonneg_left (mul_nonneg hdir hrt) hlo hloa
  have hproxylt : (w.directionHi:ℝ)*rt/(w.normLo:ℝ) < 1 := (div_lt_one hlo).mpr hsep
  have hErr := geometric_error_mono 1 1
    (‖cqReal b‖*rt/‖cqReal a‖) ((w.directionHi:ℝ)*rt/(w.normLo:ℝ))
    ((w.order+1:ℕ):ℝ) (w.order+1) (by norm_num) le_rfl
    (div_nonneg (mul_nonneg (norm_nonneg _) hrt) (norm_nonneg _)) hratio hproxylt (by positivity)
  have herr : (‖cqReal b‖*rt/‖cqReal a‖)^(w.order+1)/
      (((w.order+1:ℕ):ℝ)*(1-‖cqReal b‖*rt/‖cqReal a‖)) ≤ m.error.value := by
    rw [herror,seRat_value]
    push_cast
    push_cast at hErr
    simpa only [one_mul,rt,rtQ,Rat.cast_max,Rat.cast_abs] using hErr
  have hco : m.coeff.map ScalarExpr.value=
      (List.range (w.order+1)).map (logAffineCoeff (cqReal a) (cqReal b)) := by
    rw [hcoeff,List.map_map]
    simp only [Function.comp_def,logScalarCoeff_value]
  change ModelsOn (fun u => Real.log ‖cqReal a+cqReal b*(u:ℂ)‖)
    (m.coeff.map ScalarExpr.value) lo hi m.error.value
  rw [hco]
  apply (hFM.onIcc lo hi (by exact_mod_cast hdom) ?_).error_mono herr
  intro u hu
  change |u| ≤ ((max |lo| |hi|:ℚ):ℝ)
  rw [Rat.cast_max,Rat.cast_abs,Rat.cast_abs]
  exact abs_le.mpr
    ⟨by have := le_max_left |(lo:ℝ)| |(hi:ℝ)|; have := neg_abs_le (lo:ℝ); linarith [hu.1],
      by have := le_max_right |(lo:ℝ)| |(hi:ℝ)|; have := le_abs_self (hi:ℝ); linarith [hu.2]⟩

def invScalarCoeff (a b : CQ) (k j : ℕ) : SE := seRat
  (cqScale ((-1:ℚ)^j*((k+j-1).choose j:ℚ))
    (cqDiv (cqPow b j) (cqPow a (k+j)))).1

theorem invScalarCoeff_value (a b : CQ) (k j : ℕ) :
    (invScalarCoeff a b k j).value=(invAffineCoeff (cqReal a) (cqReal b) k j).re := by
  rw [invScalarCoeff,seRat_value,← cqReal_re,cqReal_scale,cqReal_div,cqReal_pow,cqReal_pow]
  push_cast
  congr 1
  simp only [invAffineCoeff,div_eq_mul_inv]
  ring

theorem regularCompile_inv_shape (a b : CQ) (k : ℕ) (hk : 0 < k)
    (lo hi : ℚ) (w : RegularWitness) (m : CompiledModel)
    (hc : regularCompile (.invPow a b k) lo hi w=some m) :
    regularOK a b (max |lo| |hi|) w=true ∧
      max |lo| |hi| < w.radius ∧ w.directionHi*w.radius < w.normLo ∧
      m.coeff=(List.range (w.order+1)).map (invScalarCoeff a b k) ∧
      m.error=seRat ((w.normLo-w.directionHi*w.radius)^(-(k:ℤ))*
        ((max |lo| |hi|)/w.radius)^(w.order+1)/(1-(max |lo| |hi|)/w.radius)) := by
  dsimp only [regularCompile] at hc
  simp only [show k ≠ 0 by omega,ite_false] at hc
  split_ifs at hc with hgate
  have he := Option.some.inj hc
  cases he
  simp only [Bool.and_eq_true,decide_eq_true_eq] at hgate
  exact ⟨hgate.1,hgate.2.1,hgate.2.2,rfl,rfl⟩

theorem regularCompile_inv_positive_sound (a b : CQ) (k : ℕ) (hk : 0 < k)
    (lo hi : ℚ) (w : RegularWitness) (m : CompiledModel) (hdom : lo ≤ hi)
    (hc : regularCompile (.invPow a b k) lo hi w=some m) :
    ModelsOn (CellExpr.invPow a b k).value (m.coeff.map ScalarExpr.value) lo hi m.error.value := by
  rcases regularCompile_inv_shape a b k hk lo hi w m hc with ⟨hcheck,hR,hsepR,hcoeff,herror⟩
  let rtQ := max |lo| |hi|
  let rt : ℝ := (rtQ:ℝ)
  rcases regularOK_sound a b rtQ w hcheck with ⟨hJ,hlo,hloa,hahi,hdir,hbn,hrt,hsep⟩
  have hrtR : rt < (w.radius:ℝ) := by
    simpa only [rt,rtQ] using (Rat.cast_lt.mpr hR : ((max |lo| |hi|:ℚ):ℝ) < (w.radius:ℝ))
  have hRpos : 0 < (w.radius:ℝ) := hrt.trans_lt hrtR
  have hproxysep : (w.directionHi:ℝ)*(w.radius:ℝ) < (w.normLo:ℝ) := by exact_mod_cast hsepR
  have hmul : ‖cqReal b‖*(w.radius:ℝ) ≤ (w.directionHi:ℝ)*(w.radius:ℝ) :=
    mul_le_mul_of_nonneg_right hbn hRpos.le
  have hsepA : ‖cqReal b‖*(w.radius:ℝ) < ‖cqReal a‖ := hmul.trans_lt (hproxysep.trans_le hloa)
  have hFM := invAffine_taylor_remainder (cqReal a) (cqReal b) k hk (w.radius:ℝ) rt
    ⟨hrt,hrtR⟩ hsepA w.order
  have hp : 0 < (w.normLo:ℝ)-(w.directionHi:ℝ)*(w.radius:ℝ) := sub_pos.mpr hproxysep
  have hpm : (w.normLo:ℝ)-(w.directionHi:ℝ)*(w.radius:ℝ) ≤
      ‖cqReal a‖-‖cqReal b‖*(w.radius:ℝ) := sub_le_sub hloa hmul
  have hmajor : (‖cqReal a‖-‖cqReal b‖*(w.radius:ℝ))^(-(k:ℤ)) ≤
      ((w.normLo:ℝ)-(w.directionHi:ℝ)*(w.radius:ℝ))^(-(k:ℤ)) := by
    simp only [zpow_neg,zpow_natCast]
    simpa only [one_div] using div_le_div_of_nonneg_left (by norm_num : (0:ℝ)≤1)
      (pow_pos hp k) (pow_le_pow_left₀ hp.le hpm k)
  have hrat : 0 ≤ rt/(w.radius:ℝ) := div_nonneg hrt hRpos.le
  have hratlt : rt/(w.radius:ℝ) < 1 := (div_lt_one hRpos).mpr hrtR
  have hErr := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hmajor (pow_nonneg hrat (w.order+1))) (by linarith : 0 ≤ 1-rt/(w.radius:ℝ))
  have herr : (‖cqReal a‖-‖cqReal b‖*(w.radius:ℝ))^(-(k:ℤ))*
      (rt/(w.radius:ℝ))^(w.order+1)/(1-rt/(w.radius:ℝ)) ≤ m.error.value := by
    rw [herror,seRat_value]
    push_cast
    simpa only [rt,rtQ,Rat.cast_max,Rat.cast_abs] using hErr
  have hco : m.coeff.map ScalarExpr.value=
      (List.range (w.order+1)).map (fun j => (invAffineCoeff (cqReal a) (cqReal b) k j).re) := by
    rw [hcoeff,List.map_map]
    simp only [Function.comp_def,invScalarCoeff_value]
  change ModelsOn (fun u => ((cqReal a+cqReal b*(u:ℂ))^(-(k:ℤ))).re)
    (m.coeff.map ScalarExpr.value) lo hi m.error.value
  rw [hco]
  apply (hFM.onIcc lo hi (by exact_mod_cast hdom) ?_).error_mono herr
  intro u hu
  change |u| ≤ ((max |lo| |hi|:ℚ):ℝ)
  rw [Rat.cast_max,Rat.cast_abs,Rat.cast_abs]
  exact abs_le.mpr
    ⟨by have := le_max_left |(lo:ℝ)| |(hi:ℝ)|; have := neg_abs_le (lo:ℝ); linarith [hu.1],
      by have := le_max_right |(lo:ℝ)| |(hi:ℝ)|; have := le_abs_self (hi:ℝ); linarith [hu.2]⟩

theorem regularCompile_inv_sound (a b : CQ) (k : ℕ)
    (lo hi : ℚ) (w : RegularWitness) (m : CompiledModel) (hdom : lo ≤ hi)
    (hc : regularCompile (.invPow a b k) lo hi w=some m) :
    ModelsOn (CellExpr.invPow a b k).value (m.coeff.map ScalarExpr.value) lo hi m.error.value := by
  by_cases hk : k=0
  · subst k
    have he : some (⟨[seRat 1],seRat 0⟩ : CompiledModel)=some m := hc
    cases Option.some.inj he
    refine ⟨by exact_mod_cast hdom,by simp [seRat_value],?_⟩
    intro u hu
    simp [CellExpr.value,evalModel,seRat_value,ScalarExpr.value,Finset.sum_range_succ]
  · exact regularCompile_inv_positive_sound a b k (by omega) lo hi w m hdom hc

theorem evalModel_pair (a b u : ℝ) : evalModel [a,b] u=a+b*u := by
  simp [evalModel,Finset.sum_range_succ]

theorem cqPow_pure (a : ℚ) (j : ℕ) : cqPow (a,0) j=(a^j,0) := by
  induction j with
  | zero => simp [cqPow]
  | succ j ih => simp [cqPow,ih,cqMul,pow_succ,mul_comm]

theorem cqDiv_pure (a b : ℚ) : cqDiv (a,0) (b,0)=(a/b,0) := by
  by_cases hb : b=0
  · subst b; simp [cqDiv,cqInv,cqMul,cqSq]
  · ext <;> simp [cqDiv,cqInv,cqMul,cqSq,pow_two]
    field_simp

def xlogScalarCoeff (a b : ℚ) (terms j : ℕ) : SE :=
  if j=0 then seScale a (.log terms a)
  else if j=1 then seScale b (seAdd (.log terms a) (seRat 1))
  else seRat ((-1:ℚ)^j*b^j/((j:ℚ)*(j-1)*a^(j-1)))

theorem xlogScalarCoeff_vs_fre (a b : ℚ) (terms j : ℕ) :
    (xlogScalarCoeff a b terms j).value=(freScalarCoeff (a,0) (b,0) terms j).value+
      (if j=0 then (a:ℝ) else 0)+(if j=1 then (b:ℝ) else 0) := by
  by_cases h0 : j=0
  · subst j
    simp [xlogScalarCoeff,freScalarCoeff,seScale_value,seSub_value,seReMulLog_value,
      seRat_value,ScalarExpr.value,cqReal,Complex.mul_re,Complex.sub_re,Complex.log_re,
      Complex.norm_real,Real.norm_eq_abs,Real.log_abs]
  by_cases h1 : j=1
  · subst j
    simp [xlogScalarCoeff,freScalarCoeff,seScale_value,seAdd_value,seReMulLog_value,
      seRat_value,ScalarExpr.value,cqReal,Complex.mul_re,Complex.log_re,
      Complex.norm_real,Real.norm_eq_abs,Real.log_abs]
    ring
  simp only [xlogScalarCoeff,freScalarCoeff,h0,h1,ite_false,add_zero]
  rw [cqPow_pure,cqPow_pure,cqDiv_pure,seRat_value,seRat_value]
  simp only [cqScale]
  push_cast
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

theorem fre_real_value (a b : ℚ) (u : ℝ) :
    (CellExpr.fre (a,0) (b,0)).value u=xlog ((a:ℝ)+(b:ℝ)*u)-((a:ℝ)+(b:ℝ)*u) := by
  have hw : cqReal (a,0)+cqReal (b,0)*(u:ℂ)=(((a:ℝ)+(b:ℝ)*u:ℝ):ℂ) := by
    simp [cqReal]
  change ((cqReal (a,0)+cqReal (b,0)*(u:ℂ))*Complex.log (cqReal (a,0)+cqReal (b,0)*(u:ℂ))-
    (cqReal (a,0)+cqReal (b,0)*(u:ℂ))).re=_
  rw [hw]
  simp only [Complex.sub_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,zero_mul,sub_zero,
    Complex.log_re,Complex.norm_real,Real.norm_eq_abs,Real.log_abs,xlog]

theorem evalModel_xlog_fre (a b : ℚ) (terms J : ℕ) (hJ : 2 ≤ J) (u : ℝ) :
    evalModel (((List.range (J+1)).map (xlogScalarCoeff a b terms)).map ScalarExpr.value) u=
      evalModel (((List.range (J+1)).map (freScalarCoeff (a,0) (b,0) terms)).map ScalarExpr.value) u+
        (a:ℝ)+(b:ℝ)*u := by
  simp only [List.map_map,Function.comp_def]
  rw [evalModel_map_range,evalModel_map_range]
  simp_rw [xlogScalarCoeff_vs_fre,add_mul,ite_mul,zero_mul]
  simp only [Finset.sum_add_distrib]
  have h1 : 1 < J+1 := by omega
  simp [Finset.sum_ite_eq',h1,add_assoc]

theorem regularCompile_xlog_shape (a b lo hi : ℚ) (w : RegularWitness)
    (m : CompiledModel) (hc : regularCompile (.xlog a b) lo hi w=some m) :
    2 ≤ w.order ∧ 0 < a ∧ lo ≤ hi ∧ |b| *(max |lo| |hi|) < a ∧
      m.coeff=(List.range (w.order+1)).map (xlogScalarCoeff a b w.terms) ∧
      m.error=seRat (a*(|b| *(max |lo| |hi|)/a)^(w.order+1)/
        ((w.order+1:ℚ)*w.order*(1-|b| *(max |lo| |hi|)/a))) := by
  dsimp only [regularCompile] at hc
  split_ifs at hc with hgate
  have he := Option.some.inj hc
  cases he
  rcases hgate with ⟨hJ,ha,hd,hs⟩
  exact ⟨hJ,ha,hd,hs,rfl,rfl⟩

theorem abs_le_rat_radius (lo hi : ℚ) (u : ℝ) (hu : u ∈ Icc (lo:ℝ) (hi:ℝ)) :
    |u| ≤ ((max |lo| |hi|:ℚ):ℝ) := by
  rw [Rat.cast_max,Rat.cast_abs,Rat.cast_abs]
  exact abs_le.mpr
    ⟨by have := le_max_left |(lo:ℝ)| |(hi:ℝ)|; have := neg_abs_le (lo:ℝ); linarith [hu.1],
      by have := le_max_right |(lo:ℝ)| |(hi:ℝ)|; have := le_abs_self (hi:ℝ); linarith [hu.2]⟩

theorem regularCompile_xlog_sound (a b lo hi : ℚ) (w : RegularWitness)
    (m : CompiledModel) (hc : regularCompile (.xlog a b) lo hi w=some m) :
    ModelsOn (CellExpr.xlog a b).value (m.coeff.map ScalarExpr.value) lo hi m.error.value := by
  rcases regularCompile_xlog_shape a b lo hi w m hc with ⟨hJ,ha,hd,hsep,hcoeff,herror⟩
  let rtQ := max |lo| |hi|
  let rt : ℝ := (rtQ:ℝ)
  have haR : 0 < (a:ℝ) := by exact_mod_cast ha
  have hrtQ : 0 ≤ rtQ := (abs_nonneg lo).trans (le_max_left _ _)
  have hrt : 0 ≤ rt := by
    change (0:ℝ) ≤ (rtQ:ℝ)
    exact_mod_cast hrtQ
  have hna : ‖cqReal (a,0)‖=(a:ℝ) := by simp [cqReal,abs_of_pos haR]
  have hnb : ‖cqReal (b,0)‖=|(b:ℝ)| := by simp [cqReal]
  have hsepR : |(b:ℝ)| *rt < (a:ℝ) := by
    simpa only [rt,rtQ,Rat.cast_mul,Rat.cast_abs] using
      (Rat.cast_lt.mpr hsep : ((|b| *(max |lo| |hi|):ℚ):ℝ) < (a:ℝ))
  have hFM := fre_taylor_remainder (cqReal (a,0)) (cqReal (b,0)) rt
    (by simpa only [cqReal_re] using haR.le) hrt (by rwa [hna,hnb]) w.order hJ
  rw [hna,hnb] at hFM
  have heError : m.error.value=(a:ℝ)*(|(b:ℝ)| *rt/(a:ℝ))^(w.order+1)/
      (((w.order+1:ℕ):ℝ)*(w.order:ℝ)*(1-|(b:ℝ)| *rt/(a:ℝ))) := by
    rw [herror,seRat_value]
    dsimp only [rt,rtQ]
    push_cast
    rfl
  refine ⟨by exact_mod_cast hd,?_,?_⟩
  · rw [heError]
    exact hFM.2.1
  · intro u hu
    have hh := hFM.2.2 u (abs_le_rat_radius lo hi u hu)
    change |(CellExpr.fre (a,0) (b,0)).value u-
      evalModel ((List.range (w.order+1)).map (freCoeff (cqReal (a,0)) (cqReal (b,0)))) u| ≤ _ at hh
    have hco : ((List.range (w.order+1)).map (freScalarCoeff (a,0) (b,0) w.terms)).map ScalarExpr.value=
        (List.range (w.order+1)).map (freCoeff (cqReal (a,0)) (cqReal (b,0))) := by
      simp only [List.map_map,Function.comp_def,freScalarCoeff_value]
    rw [fre_real_value,← hco] at hh
    change |xlog ((a:ℝ)+(b:ℝ)*u)-evalModel (m.coeff.map ScalarExpr.value) u| ≤ m.error.value
    rw [hcoeff,evalModel_xlog_fre a b w.terms w.order hJ u,heError]
    convert! hh using 1 <;> congr 1 <;> ring

theorem ulogCompile_tight_sound (hi : ℚ) (hhi : 0 < hi) (terms : ℕ) :
    ModelsOn CatalanCore.Li2.DecayCert.xlog
      ((ulogCompile hi terms).coeff.map ScalarExpr.value) 0 hi ((hi:ℝ)/4) := by
  let R : ℝ := (hi:ℝ)
  let t : ℝ := R/2
  have hR : 0 < R := by
    simpa only [R,Rat.cast_zero] using (Rat.cast_lt.mpr hhi : ((0:ℚ):ℝ) < (hi:ℝ))
  have ht : 0 < t := by dsimp [t]; positivity
  have hlogs : Real.log R-Real.log t ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (div_pos hR ht)
    rw [Real.log_div hR.ne' ht.ne'] at hh
    have hdiv : R/t=2 := by dsimp [t]; field_simp
    rw [hdiv] at hh
    linarith
  refine ⟨by exact_mod_cast hhi.le,?_,?_⟩
  · change 0 ≤ (hi:ℝ)/4
    positivity
  · intro u hu
    have hupper := mul_log_le_chord u R hu.1 hR hu.2
    have hlower := mul_log_le_tangent u t hu.1 ht
    have hgap := mul_nonpos_of_nonneg_of_nonpos hu.1
      (show Real.log R-Real.log t-1 ≤ 0 by linarith)
    have he : evalModel ((ulogCompile hi terms).coeff.map ScalarExpr.value) u=
        -t/2+((Real.log t+1+Real.log R)/2)*u := by
      simp only [ulogCompile,List.map_cons,List.map_nil,seRat_value,seScale_value,seAdd_value,ScalarExpr.value]
      rw [evalModel_pair]
      push_cast
      dsimp only [t,R]
      ring
    rw [he]
    change |xlog u-(-t/2+(Real.log t+1+Real.log R)/2*u)| ≤ ((hi:ℝ)/4)
    rw [abs_le]
    change -(R/4) ≤ xlog u-(-t/2+(Real.log t+1+Real.log R)/2*u) ∧
      xlog u-(-t/2+(Real.log t+1+Real.log R)/2*u) ≤ R/4
    constructor <;> dsimp only [t] at * <;> nlinarith

theorem ulogCompile_sound (hi : ℚ) (hhi : 0 < hi) (terms : ℕ) :
    ModelsOn CatalanCore.Li2.DecayCert.xlog
      ((ulogCompile hi terms).coeff.map ScalarExpr.value) 0 hi (ulogCompile hi terms).error.value := by
  have he : (ulogCompile hi terms).error.value=(hi:ℝ)/4 := by
    change ((hi/4:ℚ):ℝ)=(hi:ℝ)/4
    push_cast
    rfl
  rw [he]
  exact ulogCompile_tight_sound hi hhi terms


#print axioms logUnit_remainder
#print axioms logAffine_model_eval
#print axioms logAffine_taylor_remainder
#print axioms hasTaylorSeriesAt_invUnit
#print axioms hasTaylorSeriesAt_invAffine
#print axioms evalModel_complex_re
#print axioms invAffine_taylor_remainder
#print axioms regularOK_sound
#print axioms freScalarCoeff_value
#print axioms geometric_error_mono
#print axioms Models.onIcc
#print axioms ModelsOn.error_mono
#print axioms regularCompile_fre_shape
#print axioms regularCompile_fre_sound
#print axioms logScalarCoeff_value
#print axioms regularCompile_log_shape
#print axioms regularCompile_log_sound
#print axioms invScalarCoeff_value
#print axioms regularCompile_inv_shape
#print axioms regularCompile_inv_positive_sound
#print axioms regularCompile_inv_sound
#print axioms evalModel_pair
#print axioms cqPow_pure
#print axioms cqDiv_pure
#print axioms xlogScalarCoeff_vs_fre
#print axioms fre_real_value
#print axioms evalModel_xlog_fre
#print axioms regularCompile_xlog_shape
#print axioms abs_le_rat_radius
#print axioms regularCompile_xlog_sound
#print axioms ulogCompile_tight_sound
#print axioms ulogCompile_sound
end
end CatalanCore.Li2.DecayCert
