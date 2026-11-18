module
public import CatalanCore.Li2.DecayCert.FieldIntegral.Analytic
public import CatalanCore.Li2.DecayCert.SlitDistance
public import CatalanCore.Tools.JoukowskiLog
@[expose] public section
set_option Elab.async false
open MeasureTheory Set Complex Polynomial Filter Topology
open scoped BigOperators
open CatalanCore.Zeta5.Potential CatalanCore.Tools.Joukowski
namespace CatalanCore.Li2.DecayCert
abbrev CE := SE×SE
def ceRat (q : CQ) : CE := (.rat q.1,.rat q.2)
def ceAdd (a b : CE) : CE := (seAdd a.1 b.1,seAdd a.2 b.2)
def ceNeg (a : CE) : CE := (seNeg a.1,seNeg a.2)
def ceSub (a b : CE) : CE := ceAdd a (ceNeg b)
def ceMul (a b : CE) : CE :=
  (seSub (seMul a.1 b.1) (seMul a.2 b.2),seAdd (seMul a.1 b.2) (seMul a.2 b.1))
def ceScale (q : ℚ) (a : CE) : CE := (seScale q a.1,seScale q a.2)
def ceNormSq (a : CE) : SE := seAdd (seMul a.1 a.1) (seMul a.2 a.2)
def ceInv (a : CE) : CE :=
  (seMul a.1 (.inv (ceNormSq a)),seNeg (seMul a.2 (.inv (ceNormSq a))))
def cePow (a : CE) : ℕ → CE | 0 => ceRat (1,0) | n+1 => ceMul a (cePow a n)
def ceLog (terms : ℕ) (a : CE) : CE :=
  (seScale (1/2) (.logE terms (ceNormSq a)),.argE terms a.1 a.2)
structure RootWitness where
  normLo : ℚ
  normHi : ℚ
  reLo : ℚ
  reHi : ℚ
  imLo : ℚ
  imHi : ℚ
def sqrtCQExpr (a : CQ) (w : RootWitness) : CE :=
  let nr : SE := .sqrt (.rat (cqSq a)) w.normLo w.normHi
  (.sqrt (seScale (1/2) (seAdd nr (.rat a.1))) w.reLo w.reHi,
    seScale (if a.2 < 0 then -1 else 1)
      (.sqrt (seScale (1/2) (seSub nr (.rat a.1))) w.imLo w.imHi))
structure VSeed where
  terms : ℕ
  branch : ℤ
  rootMinus : RootWitness
  rootPlus : RootWitness

def qWeightedCheb (d : QSegment) (a : ℚ) (k : ℕ) : CQ :=
  let β := cqAdd d.mid (a,0)
  if k=0 then cqAdd (cqScale (d.c 0) β) (cqScale (d.c 1/2) d.half)
  else if k=1 then cqAdd (cqScale (d.c 1) β) (cqScale (d.c 0+d.c 2/2) d.half)
  else cqAdd (cqScale (d.c k) β) (cqScale ((d.c (k-1)+d.c (k+1))/2) d.half)
def phiExpr (η : CQ) (w : VSeed) : CE :=
  ceAdd (ceRat η) (ceMul (sqrtCQExpr (cqSub η (1,0)) w.rootMinus)
    (sqrtCQExpr (cqAdd η (1,0)) w.rootPlus))
def ceSum (xs : List CE) : CE := xs.foldl ceAdd (ceRat (0,0))
def vintExpr (d : QSegment) (a : ℚ) (w : VSeed) : SE :=
  let β := cqAdd d.mid (a,0)
  let w0 := ceRat (qWeightedCheb d a 0)
  let tail (ψ : CE) := ceSum ((List.range d.coeff.length).map (fun j : ℕ =>
    ceScale (1/(j+1:ℚ)) (ceMul (ceRat (qWeightedCheb d a (j+1))) (cePow ψ (j+1)))))
  if β=d.half then
    (ceSub (ceSub (ceMul (ceSub (ceLog w.terms (ceRat d.half))
      (.log w.terms 2,.rat 0)) w0) (tail (ceRat (-1,0)))) w0).1
  else if β=cqNeg d.half then
    (ceSub (ceSub (ceMul (ceSub (ceLog w.terms (ceRat (cqNeg d.half)))
      (.log w.terms 2,.rat 0)) w0) (tail (ceRat (1,0)))) w0).1
  else
    let η := cqNeg (cqDiv β d.half)
    let φ := phiExpr η w
    let value := ceSub (ceSub (ceMul w0 (ceLog w.terms (ceScale (1/2) φ)))
      (tail (ceInv φ))) w0
    if d.mid.2=0 ∧ d.half.2=0 then
      seAdd value.1 (seScale (qWeightedCheb d a 0).1 (seLogNorm w.terms d.half))
    else
      (ceAdd value (ceMul w0 (ceAdd (ceLog w.terms (ceRat (cqNeg d.half)))
        (.rat 0,seScale (2*w.branch) .pi)))).1

def vintGeometryCheck (d : QSegment) (a : ℚ) (w : VSeed) : Bool :=
  let β := cqAdd d.mid (a,0)
  let η := cqNeg (cqDiv β d.half)
  if cqSq d.half=0 then false
  else if β=d.half ∨ β=cqNeg d.half then true
  else if d.mid.2=0 ∧ d.half.2=0 then decide (1 ≤ |η.1|)
  else
    let delta := seSub (seSub (seSub (.arg w.terms β)
      (.arg w.terms (cqNeg d.half))) (.arg w.terms η)) (seScale (2*w.branch) .pi)
    decide (0 < slitDistSq η ∧
      0 ≤ (cqSub d.mid d.half).1+a ∧ 0 ≤ (cqAdd d.mid d.half).1+a ∧
      0 ≤ (cqSub d.mid d.half).2 ∧ 0 ≤ (cqAdd d.mid d.half).2) &&
      match delta.check,ScalarExpr.pi.check with
      | some b,some piBox => decide (max |b.1| |b.2| < piBox.1)
      | _,_ => false


noncomputable def ceValue (a : CE) : ℂ := (a.1.value:ℂ)+(a.2.value:ℂ)*Complex.I

theorem ceValue_re (a : CE) : (ceValue a).re=a.1.value := by simp [ceValue]
theorem ceValue_im (a : CE) : (ceValue a).im=a.2.value := by simp [ceValue]
theorem ceValue_rat (q : CQ) : ceValue (ceRat q)=cqReal q := by
  rfl
theorem ceValue_add (a b : CE) : ceValue (ceAdd a b)=ceValue a+ceValue b := by
  simp only [ceValue, ceAdd, seAdd, ScalarExpr.value, Complex.ofReal_add]
  ring
theorem ceValue_neg (a : CE) : ceValue (ceNeg a)= -ceValue a := by
  simp only [ceValue, ceNeg, seNeg, ScalarExpr.value, Complex.ofReal_neg]
  ring
theorem ceValue_sub (a b : CE) : ceValue (ceSub a b)=ceValue a-ceValue b := by
  rw [ceSub, ceValue_add, ceValue_neg]
  ring
theorem ceValue_mul (a b : CE) : ceValue (ceMul a b)=ceValue a*ceValue b := by
  simp only [ceValue, ceMul, seSub, seMul, seAdd, seNeg, ScalarExpr.value,
    Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_neg]
  ring_nf
  simp only [Complex.I_sq]
  ring
theorem ceValue_scale (q : ℚ) (a : CE) : ceValue (ceScale q a)=(q:ℂ)*ceValue a := by
  simp only [ceValue, ceScale, seScale, seMul, seRat, ScalarExpr.value, Complex.ofReal_mul,
    Complex.ofReal_ratCast]
  ring
theorem ceNormSq_value (a : CE) : (ceNormSq a).value=Complex.normSq (ceValue a) := by
  simp [ceNormSq, ceValue, seAdd, seMul, ScalarExpr.value, Complex.normSq_apply]
theorem ceValue_inv (a : CE) : ceValue (ceInv a)=(ceValue a)⁻¹ := by
  apply Complex.ext <;> simp [ceValue, ceInv, ceNormSq, seMul, seAdd, seNeg,
    ScalarExpr.value, Complex.inv_re, Complex.inv_im, Complex.normSq_apply] <;> ring

theorem ceValue_pow (a : CE) (n : ℕ) : ceValue (cePow a n)=(ceValue a)^n := by
  induction n with
  | zero => simp [cePow,ceValue_rat,cqReal]
  | succ n ih => rw [cePow,ceValue_mul,ih,pow_succ'];

theorem ceValue_log (terms : ℕ) (a : CE) : ceValue (ceLog terms a)=Complex.log (ceValue a) := by
  apply Complex.ext
  · rw [ceValue_re, Complex.log_re]
    change (((1/2:ℚ):ℝ)*Real.log (ceNormSq a).value) = Real.log ‖ceValue a‖
    rw [ceNormSq_value,Complex.normSq_eq_norm_sq,Real.log_pow]
    norm_num <;> ring
  · rw [ceValue_im, Complex.log_im]
    rfl

theorem qWeightedCheb_value (d : QSegment) (hh : cqReal d.half ≠ 0) (a : ℚ) (k : ℕ) :
    cqReal (qWeightedCheb d a k)=weightedCheb (d.segmentData hh) (a:ℝ) k := by
  unfold qWeightedCheb weightedCheb
  dsimp only [QSegment.segmentData]
  split_ifs <;> simp [cqReal,cqAdd,cqScale] <;> push_cast <;> ring

private noncomputable def croot (z : ℂ) : ℂ :=
  ⟨Real.sqrt ((‖z‖+z.re)/2),
    (if z.im < 0 then -1 else 1)*Real.sqrt ((‖z‖-z.re)/2)⟩

private theorem croot_sq (z : ℂ) : croot z^2=z := by
  let u := Real.sqrt ((‖z‖+z.re)/2)
  let v := Real.sqrt ((‖z‖-z.re)/2)
  have hp : 0 ≤ (‖z‖+z.re)/2 := by linarith [Complex.abs_re_le_norm z, neg_le_abs z.re]
  have hm : 0 ≤ (‖z‖-z.re)/2 := by linarith [Complex.re_le_norm z]
  have hu : u^2=(‖z‖+z.re)/2 := Real.sq_sqrt hp
  have hv : v^2=(‖z‖-z.re)/2 := Real.sq_sqrt hm
  have hun : 0 ≤ u := Real.sqrt_nonneg _
  have hvn : 0 ≤ v := Real.sqrt_nonneg _
  have hprod : (2*u*v)^2=z.im^2 := by
    calc
      _ = 4*u^2*v^2 := by ring
      _ = (‖z‖+z.re)*(‖z‖-z.re) := by rw [hu,hv]; ring
      _ = z.im^2 := by nlinarith [sq_norm_eq z]
  have huv : 2*u*v=|z.im| := by
    nlinarith [mul_nonneg hun hvn,abs_nonneg z.im,sq_abs z.im]
  apply Complex.ext
  · rw [pow_two,Complex.mul_re]
    change u*u-((if z.im < 0 then -1 else 1)*v)*((if z.im < 0 then -1 else 1)*v)=z.re
    split_ifs <;> nlinarith [hu,hv]
  · rw [pow_two,Complex.mul_im]
    change u*((if z.im < 0 then -1 else 1)*v)+((if z.im < 0 then -1 else 1)*v)*u=z.im
    split_ifs with hi
    · rw [abs_of_neg hi] at huv
      nlinarith
    · rw [abs_of_nonneg (le_of_not_gt hi)] at huv
      nlinarith

private theorem ceValue_sqrtCQExpr (a : CQ) (w : RootWitness) :
    ceValue (sqrtCQExpr a w)=croot (cqReal a) := by
  have him : (cqReal a).im=(a.2:ℝ) := by norm_num [cqReal]
  have hre : (cqReal a).re=(a.1:ℝ) := by norm_num [cqReal]
  have hn : Real.sqrt (cqSq a:ℝ)=‖cqReal a‖ := by
    rw [Complex.norm_def]
    congr 1
    simp [cqSq,cqReal,Complex.normSq_apply]
    push_cast
    ring
  have hiff : a.2 < 0 ↔ (cqReal a).im < 0 := by rw [him]; exact_mod_cast Iff.rfl
  apply Complex.ext
  · rw [ceValue_re]
    change Real.sqrt (((1/2:ℚ):ℝ)*(Real.sqrt (cqSq a:ℝ)+(a.1:ℝ))) = _
    change _ = Real.sqrt ((‖cqReal a‖+(cqReal a).re)/2)
    rw [hn,hre]
    congr 1
    norm_num <;> ring
  · rw [ceValue_im]
    change ((if a.2 < 0 then -1 else 1:ℚ):ℝ)*
      Real.sqrt (((1/2:ℚ):ℝ)*(Real.sqrt (cqSq a:ℝ)-(a.1:ℝ))) = _
    change _ = (if (cqReal a).im < 0 then -1 else 1)*Real.sqrt ((‖cqReal a‖-(cqReal a).re)/2)
    rw [hn,hre]
    have hf : (((1/2:ℚ):ℝ)*(‖cqReal a‖-(a.1:ℝ))) = (‖cqReal a‖-(a.1:ℝ))/2 := by
      norm_num <;> ring
    rw [hf]
    simp only [hiff]
    split_ifs <;> norm_num only [Rat.cast_neg,Rat.cast_one]

private noncomputable def rootPair (z : ℂ) : ℂ := croot (z-1)*croot (z+1)
private theorem rootPair_sq (z : ℂ) : rootPair z^2=z^2-1 := by
  rw [rootPair,mul_pow,croot_sq,croot_sq]
  ring
private theorem croot_re_nonneg (z : ℂ) : 0 ≤ (croot z).re := Real.sqrt_nonneg _
private theorem croot_re_pos {z : ℂ} (hi : z.im ≠ 0) : 0 < (croot z).re := by
  apply Real.sqrt_pos.mpr
  have hh := Complex.abs_re_lt_norm.mpr hi
  have hn := neg_le_abs z.re
  linarith
private theorem croot_im_pos {z : ℂ} (hi : 0 < z.im) : 0 < (croot z).im := by
  have hh := Complex.abs_re_lt_norm.mpr hi.ne'
  have hp : 0 < (‖z‖-z.re)/2 := by linarith [le_abs_self z.re]
  change 0 < (if z.im < 0 then -1 else 1)*Real.sqrt ((‖z‖-z.re)/2)
  rw [if_neg (not_lt.mpr hi.le),one_mul]
  exact Real.sqrt_pos.mpr hp
private theorem croot_im_neg {z : ℂ} (hi : z.im < 0) : (croot z).im < 0 := by
  have hh := Complex.abs_re_lt_norm.mpr hi.ne
  have hp : 0 < (‖z‖-z.re)/2 := by linarith [le_abs_self z.re]
  change (if z.im < 0 then -1 else 1)*Real.sqrt ((‖z‖-z.re)/2) < 0
  rw [if_pos hi,neg_one_mul]
  exact neg_neg_of_pos (Real.sqrt_pos.mpr hp)
private theorem rootPair_im_pos {z : ℂ} (hi : 0 < z.im) : 0 < (rootPair z).im := by
  have hp : 0 < (z-1).im := by simpa using hi
  have hm : 0 < (z+1).im := by simpa using hi
  rw [rootPair,Complex.mul_im]
  exact add_pos (mul_pos (croot_re_pos hp.ne') (croot_im_pos hm))
    (mul_pos (croot_im_pos hp) (croot_re_pos hm.ne'))
private theorem rootPair_im_neg {z : ℂ} (hi : z.im < 0) : (rootPair z).im < 0 := by
  have hp : (z-1).im < 0 := by simpa using hi
  have hm : (z+1).im < 0 := by simpa using hi
  rw [rootPair,Complex.mul_im]
  exact add_neg (mul_neg_of_pos_of_neg (croot_re_pos hp.ne) (croot_im_neg hm))
    (mul_neg_of_neg_of_pos (croot_im_neg hp) (croot_re_pos hm.ne))

private theorem jq_re_factor (z : ℂ) :
    (jq z).re=(jphi z).re*(1-(Complex.normSq (jphi z))⁻¹)/2 := by
  simp only [jq,Complex.div_ofNat_re,Complex.sub_re,Complex.inv_re]
  ring
private theorem jq_im_factor (z : ℂ) :
    (jq z).im=(jphi z).im*(1+(Complex.normSq (jphi z))⁻¹)/2 := by
  simp only [jq,Complex.div_ofNat_im,Complex.sub_im,Complex.inv_im]
  ring
private theorem jq_im_pos {z : ℂ} (h : 1 < jc z) (hi : 0 < z.im) : 0 < (jq z).im := by
  have hR := one_lt_jR h
  have hr : (jR z)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hR
  have hr0 : 0 ≤ (jR z)⁻¹ := inv_nonneg.mpr (by linarith)
  have hd : 0 < 1-(jR z)⁻¹^2 := by nlinarith
  have hp : 0 < (jphi z).im := div_pos (by linarith) hd
  rw [jq_im_factor]
  have hf : 0 < 1+(Complex.normSq (jphi z))⁻¹ := by
    have hn := inv_nonneg.mpr (Complex.normSq_nonneg (jphi z))
    linarith
  exact div_pos (mul_pos hp hf) (by norm_num)
private theorem jq_im_neg {z : ℂ} (h : 1 < jc z) (hi : z.im < 0) : (jq z).im < 0 := by
  have hR := one_lt_jR h
  have hr : (jR z)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hR
  have hr0 : 0 ≤ (jR z)⁻¹ := inv_nonneg.mpr (by linarith)
  have hd : 0 < 1-(jR z)⁻¹^2 := by nlinarith
  have hp : (jphi z).im < 0 := div_neg_of_neg_of_pos (by linarith) hd
  rw [jq_im_factor]
  have hf : 0 < 1+(Complex.normSq (jphi z))⁻¹ := by
    have hn := inv_nonneg.mpr (Complex.normSq_nonneg (jphi z))
    linarith
  exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hp hf) (by norm_num)

private theorem croot_ofReal_nonneg (r : ℝ) (hr : 0 ≤ r) : croot (r:ℂ)=(Real.sqrt r:ℂ) := by
  have he : (r+r)/2=r := by ring
  apply Complex.ext <;> simp [croot,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hr,he]
private theorem croot_ofReal_neg (r : ℝ) (hr : r < 0) : croot (r:ℂ)=(Real.sqrt (-r):ℂ)*Complex.I := by
  have he : (-r-r)/2= -r := by ring
  apply Complex.ext <;> simp [croot,Complex.norm_real,Real.norm_eq_abs,abs_of_neg hr,he]

private theorem jq_re_pos_real (r : ℝ) (h : 1 < jc (r:ℂ)) (hr : 1 < r) : 0 < (jq (r:ℂ)).re := by
  have hd : jd (r:ℂ)=1 := by
    unfold jd
    rw [← Complex.ofReal_one,← Complex.ofReal_add,← Complex.ofReal_sub,
      Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs,
      abs_of_pos (by linarith),abs_of_pos (by linarith)]
    ring
  have hn : 1 < Complex.normSq (jphi (r:ℂ)) := by
    rw [← Complex.sq_norm]
    nlinarith [(jphi_spec h).1, norm_nonneg (jphi (r:ℂ))]
  have hp : 0 < (jphi (r:ℂ)).re := by change 0 < jR (r:ℂ)*jd (r:ℂ); rw [hd,mul_one]; linarith [one_lt_jR h]
  rw [jq_re_factor]
  exact div_pos (mul_pos hp (sub_pos.mpr (inv_lt_one_of_one_lt₀ hn))) (by norm_num)
private theorem jq_re_neg_real (r : ℝ) (h : 1 < jc (r:ℂ)) (hr : r < -1) : (jq (r:ℂ)).re < 0 := by
  have hd : jd (r:ℂ)= -1 := by
    unfold jd
    rw [← Complex.ofReal_one,← Complex.ofReal_add,← Complex.ofReal_sub,
      Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs,
      abs_of_neg (by linarith),abs_of_neg (by linarith)]
    ring
  have hn : 1 < Complex.normSq (jphi (r:ℂ)) := by
    rw [← Complex.sq_norm]
    nlinarith [(jphi_spec h).1, norm_nonneg (jphi (r:ℂ))]
  have hp : (jphi (r:ℂ)).re < 0 := by change jR (r:ℂ)*jd (r:ℂ) < 0; rw [hd,mul_neg_one]; linarith [one_lt_jR h]
  rw [jq_re_factor]
  exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hp (sub_pos.mpr (inv_lt_one_of_one_lt₀ hn))) (by norm_num)

private theorem rootPair_eq_jq {z : ℂ} (h : 1 < jc z) : rootPair z=jq z := by
  have hs : rootPair z^2=jq z^2 := by rw [rootPair_sq,jq_sq h]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with he | he
  · exact he
  · exfalso
    by_cases hi : z.im=0
    · have hz : z=(z.re:ℂ) := by apply Complex.ext <;> simp [hi]
      have hout : z.re < -1 ∨ 1 < z.re := by
        by_contra hn
        push_neg at hn
        have hc := jc_ofReal hn
        rw [← hz] at hc
        linarith
      rcases hout with hr | hr
      · have hq := jq_re_neg_real z.re (by rw [← hz]; exact h) hr
        have hroot : (rootPair z).re < 0 := by
          rw [hz]
          have hm : (z.re-1:ℝ) < 0 := by linarith
          have hp : (z.re+1:ℝ) < 0 := by linarith
          rw [rootPair,← Complex.ofReal_one,← Complex.ofReal_sub,← Complex.ofReal_add,
            croot_ofReal_neg _ hm,croot_ofReal_neg _ hp]
          simp only [Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
            Complex.I_re,Complex.I_im,mul_zero,mul_one,zero_mul,sub_zero,zero_add]
          nlinarith [Real.sqrt_pos.mpr (neg_pos.mpr hm),Real.sqrt_pos.mpr (neg_pos.mpr hp)]
        have hhe := congrArg Complex.re he
        rw [hz] at hhe hroot
        simp only [Complex.neg_re] at hhe
        linarith
      · have hq := jq_re_pos_real z.re (by rw [← hz]; exact h) hr
        have hroot : 0 < (rootPair z).re := by
          rw [hz]
          have hm : 0 ≤ z.re-1 := by linarith
          have hp : 0 ≤ z.re+1 := by linarith
          rw [rootPair,← Complex.ofReal_one,← Complex.ofReal_sub,← Complex.ofReal_add,
            croot_ofReal_nonneg _ hm,croot_ofReal_nonneg _ hp]
          simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
          exact mul_pos (Real.sqrt_pos.mpr (by linarith)) (Real.sqrt_pos.mpr (by linarith))
        have hhe := congrArg Complex.re he
        rw [hz] at hhe hroot
        simp only [Complex.neg_re] at hhe
        linarith
    · rcases lt_or_gt_of_ne hi with him | him
      · have hq := jq_im_neg h him
        have hr := rootPair_im_neg him
        have hh := congrArg Complex.im he
        simp only [Complex.neg_im] at hh
        linarith
      · have hq := jq_im_pos h him
        have hr := rootPair_im_pos him
        have hh := congrArg Complex.im he
        simp only [Complex.neg_im] at hh
        linarith

theorem phiExpr_value (η : CQ) (w : VSeed) (hη : 1 < jc (cqReal η)) :
    ceValue (phiExpr η w)=jphi (cqReal η) := by
  rw [phiExpr,ceValue_add,ceValue_rat,ceValue_mul,ceValue_sqrtCQExpr,ceValue_sqrtCQExpr,
    cqReal_sub,cqReal_add]
  have hone : cqReal (1,0)=1 := by norm_num [cqReal]
  rw [hone]
  change cqReal η+rootPair (cqReal η)=jphi (cqReal η)
  rw [rootPair_eq_jq hη,← jphi_eq_add_jq hη]

theorem ceValue_sum (xs : List CE) : ceValue (ceSum xs)=(xs.map ceValue).sum := by
  have hh : ∀ (xs : List CE) (base : CE), ceValue (xs.foldl ceAdd base)=ceValue base+(xs.map ceValue).sum := by
    intro xs
    induction xs with
    | nil => intro base; simp
    | cons x xs ih =>
      intro base
      simp only [List.foldl_cons,List.map_cons,List.sum_cons]
      rw [ih,ceValue_add]
      ring
  simpa only [ceSum,ceValue_rat,cqReal,Rat.cast_zero,zero_mul,zero_add] using hh xs (ceRat (0,0))

private theorem cList_range_sum (f : ℕ → ℂ) (n : ℕ) :
    ((List.range n).map f).sum=∑ k ∈ Finset.range n, f k := by
  induction n with
  | zero => simp
  | succ n ih => simp only [List.range_succ,List.map_append,List.sum_append,
      List.map_singleton,List.sum_singleton,Finset.sum_range_succ,ih]

private def vtail (d : QSegment) (a : ℚ) (ψ : CE) : CE :=
  ceSum ((List.range d.coeff.length).map (fun j : ℕ =>
    ceScale (1/(j+1:ℚ)) (ceMul (ceRat (qWeightedCheb d a (j+1))) (cePow ψ (j+1)))))
private theorem vtail_value (d : QSegment) (hh : cqReal d.half ≠ 0) (a : ℚ) (ψ : CE) :
    ceValue (vtail d a ψ)=∑ j ∈ Finset.range d.coeff.length,
      weightedCheb (d.segmentData hh) (a:ℝ) (j+1)*(ceValue ψ)^(j+1)/(j+1:ℕ) := by
  rw [vtail,ceValue_sum,List.map_map,cList_range_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Function.comp_apply,ceValue_scale,ceValue_mul,ceValue_rat,ceValue_pow,qWeightedCheb_value d hh a]
  push_cast
  ring

theorem logNorm_value (n : ℕ) (q : CQ) : (seLogNorm n q).value=Real.log ‖cqReal q‖ := by
  have hs : (cqSq q:ℝ)=‖cqReal q‖^2 := by
    rw [Complex.sq_norm,Complex.normSq_apply]
    norm_num [cqSq,cqReal]
    push_cast
    ring
  change (((1/2:ℚ):ℝ)*Real.log (cqSq q:ℝ))=Real.log ‖cqReal q‖
  rw [hs,Real.log_pow]
  norm_num <;> ring

theorem vintExpr_value_left (d : QSegment) (hh : cqReal d.half ≠ 0) (a : ℚ) (w : VSeed)
    (hβ : cqAdd d.mid (a,0)=d.half) :
    (vintExpr d a w).value =
      ((Complex.log (cqReal d.half)-(Real.log 2:ℂ))*weightedCheb (d.segmentData hh) (a:ℝ) 0 -
        (∑ j ∈ Finset.range d.coeff.length,
          (-1:ℂ)^(j+1)*weightedCheb (d.segmentData hh) (a:ℝ) (j+1)/(j+1:ℕ)) -
        weightedCheb (d.segmentData hh) (a:ℝ) 0).re := by
  have hlog2 : ceValue (.log w.terms 2,.rat 0)=(Real.log 2:ℂ) := by
    simp [ceValue,ScalarExpr.value]
  have hm1 : cqReal (-1,0)=(-1:ℂ) := by norm_num [cqReal]
  have hs : (∑ j ∈ Finset.range d.coeff.length,
      weightedCheb (d.segmentData hh) (a:ℝ) (j+1)*(-1:ℂ)^(j+1)/(j+1:ℕ)) =
      ∑ j ∈ Finset.range d.coeff.length,
        (-1:ℂ)^(j+1)*weightedCheb (d.segmentData hh) (a:ℝ) (j+1)/(j+1:ℕ) := by
    apply Finset.sum_congr rfl
    intro j hj
    ring
  simp only [vintExpr,hβ,ite_true]
  rw [← ceValue_re]
  change (ceValue (ceSub (ceSub (ceMul (ceSub (ceLog w.terms (ceRat d.half))
    (.log w.terms 2,.rat 0)) (ceRat (qWeightedCheb d a 0)))
    (vtail d a (ceRat (-1,0)))) (ceRat (qWeightedCheb d a 0)))).re = _
  · simp only [ceValue_sub,ceValue_mul,ceValue_log,ceValue_rat,hlog2,
      vtail_value d hh a,hm1,qWeightedCheb_value d hh a,hs]

theorem vintExpr_value_right (d : QSegment) (hh : cqReal d.half ≠ 0) (a : ℚ) (w : VSeed)
    (hβ : cqAdd d.mid (a,0)=cqNeg d.half) (hn : cqAdd d.mid (a,0) ≠ d.half) :
    (vintExpr d a w).value =
      ((Complex.log (-cqReal d.half)-(Real.log 2:ℂ))*weightedCheb (d.segmentData hh) (a:ℝ) 0 -
        (∑ j ∈ Finset.range d.coeff.length,
          weightedCheb (d.segmentData hh) (a:ℝ) (j+1)/(j+1:ℕ)) -
        weightedCheb (d.segmentData hh) (a:ℝ) 0).re := by
  have hlog2 : ceValue (.log w.terms 2,.rat 0)=(Real.log 2:ℂ) := by simp [ceValue,ScalarExpr.value]
  have hone : cqReal (1,0)=(1:ℂ) := by norm_num [cqReal]
  simp only [vintExpr]
  rw [if_neg hn,if_pos hβ]
  rw [← ceValue_re]
  change (ceValue (ceSub (ceSub (ceMul (ceSub (ceLog w.terms (ceRat (cqNeg d.half)))
    (.log w.terms 2,.rat 0)) (ceRat (qWeightedCheb d a 0)))
    (vtail d a (ceRat (1,0)))) (ceRat (qWeightedCheb d a 0)))).re = _
  simp only [ceValue_sub,ceValue_mul,ceValue_log,ceValue_rat,hlog2,
    vtail_value d hh a,hone,qWeightedCheb_value d hh a,cqReal_neg,one_pow,mul_one]

theorem vintExpr_value_generic (d : QSegment) (hh : cqReal d.half ≠ 0) (a : ℚ) (w : VSeed)
    (hnl : cqAdd d.mid (a,0) ≠ d.half) (hnr : cqAdd d.mid (a,0) ≠ cqNeg d.half)
    (hreal : ¬ (d.mid.2=0 ∧ d.half.2=0))
    (hoff : 1 < jc (cqReal (cqNeg (cqDiv (cqAdd d.mid (a,0)) d.half)))) :
    let η := cqReal (cqNeg (cqDiv (cqAdd d.mid (a,0)) d.half))
    (vintExpr d a w).value =
      ((Complex.log (-cqReal d.half)+2*Real.pi*Complex.I*(w.branch:ℂ))*
          weightedCheb (d.segmentData hh) (a:ℝ) 0 +
        weightedCheb (d.segmentData hh) (a:ℝ) 0*Complex.log (jphi η/2) -
        (∑ j ∈ Finset.range d.coeff.length,
          weightedCheb (d.segmentData hh) (a:ℝ) (j+1)*(jphi η)⁻¹^(j+1)/(j+1:ℕ)) -
        weightedCheb (d.segmentData hh) (a:ℝ) 0).re := by
  let ηq := cqNeg (cqDiv (cqAdd d.mid (a,0)) d.half)
  have hbranch : ceValue (.rat 0,seScale (2*w.branch) .pi)=2*Real.pi*Complex.I*(w.branch:ℂ) := by
    simp only [ceValue,seScale,seMul,seRat,ScalarExpr.value]
    push_cast
    ring
  have hhalf : (((1/2:ℚ):ℝ):ℂ)=(1/2:ℂ) := by norm_num
  simp only [vintExpr,hnl,hnr,hreal,ite_false]
  rw [← ceValue_re]
  change (ceValue (ceAdd (ceSub (ceSub (ceMul (ceRat (qWeightedCheb d a 0))
    (ceLog w.terms (ceScale (1/2) (phiExpr ηq w))))
    (vtail d a (ceInv (phiExpr ηq w)))) (ceRat (qWeightedCheb d a 0)))
    (ceMul (ceRat (qWeightedCheb d a 0)) (ceAdd (ceLog w.terms (ceRat (cqNeg d.half)))
      (.rat 0,seScale (2*w.branch) .pi))))).re = _
  simp only [ceValue_add,ceValue_sub,ceValue_mul,ceValue_log,ceValue_scale,ceValue_rat,
    ceValue_inv,phiExpr_value ηq w hoff,vtail_value d hh a,qWeightedCheb_value d hh a,
    cqReal_neg,hbranch,hhalf]
  dsimp only [ηq]
  simp only [cqReal_neg]
  congr 1
  ring_nf
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem vintExpr_value_real (d : QSegment) (hh : cqReal d.half ≠ 0) (a : ℚ) (w : VSeed)
    (hnl : cqAdd d.mid (a,0) ≠ d.half) (hnr : cqAdd d.mid (a,0) ≠ cqNeg d.half)
    (hreal : d.mid.2=0 ∧ d.half.2=0)
    (hoff : 1 < jc (cqReal (cqNeg (cqDiv (cqAdd d.mid (a,0)) d.half)))) :
    let η := cqReal (cqNeg (cqDiv (cqAdd d.mid (a,0)) d.half))
    (vintExpr d a w).value =
      (weightedCheb (d.segmentData hh) (a:ℝ) 0*Complex.log (jphi η/2) -
        (∑ j ∈ Finset.range d.coeff.length,
          weightedCheb (d.segmentData hh) (a:ℝ) (j+1)*(jphi η)⁻¹^(j+1)/(j+1:ℕ)) -
        weightedCheb (d.segmentData hh) (a:ℝ) 0).re +
      (weightedCheb (d.segmentData hh) (a:ℝ) 0).re*Real.log ‖cqReal d.half‖ := by
  let ηq := cqNeg (cqDiv (cqAdd d.mid (a,0)) d.half)
  have hw0 : ((qWeightedCheb d a 0).1:ℝ)=(weightedCheb (d.segmentData hh) (a:ℝ) 0).re := by
    rw [← qWeightedCheb_value d hh a 0]
    simp [cqReal]
  have hhalf : (((1/2:ℚ):ℝ):ℂ)=(1/2:ℂ) := by norm_num
  simp only [vintExpr]
  rw [if_neg hnl,if_neg hnr,if_pos hreal]
  simp only [seAdd,seScale,seMul,seRat,ScalarExpr.value]
  rw [← ceValue_re]
  change (ceValue (ceSub (ceSub (ceMul (ceRat (qWeightedCheb d a 0))
    (ceLog w.terms (ceScale (1/2) (phiExpr ηq w))))
    (vtail d a (ceInv (phiExpr ηq w)))) (ceRat (qWeightedCheb d a 0)))).re +
      ((qWeightedCheb d a 0).1:ℝ)*(seLogNorm w.terms d.half).value = _
  simp only [ceValue_sub,ceValue_mul,ceValue_log,ceValue_scale,ceValue_rat,
    ceValue_inv,phiExpr_value ηq w hoff,vtail_value d hh a,qWeightedCheb_value d hh a,
    hhalf,hw0,logNorm_value]
  dsimp only [ηq]
  norm_num only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] <;> congr 2 <;> ring_nf
  all_goals
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    ring

#print axioms vintExpr_value_real

#print axioms vintExpr_value_right
#print axioms vintExpr_value_generic

#print axioms ceValue_sum
#print axioms vtail_value
#print axioms logNorm_value
#print axioms vintExpr_value_left
#print axioms jq_im_pos
#print axioms jq_im_neg
#print axioms croot_ofReal_nonneg
#print axioms croot_ofReal_neg
#print axioms rootPair_eq_jq
#print axioms phiExpr_value
#print axioms croot_sq
#print axioms ceValue_sqrtCQExpr
#print axioms rootPair_sq
#print axioms rootPair_im_pos
#print axioms rootPair_im_neg
#print axioms ceValue_mul
#print axioms ceValue_inv
#print axioms ceValue_log
#print axioms qWeightedCheb_value
end CatalanCore.Li2.DecayCert
