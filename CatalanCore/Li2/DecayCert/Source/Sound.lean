module
public import CatalanCore.Li2.DecayCert.Source
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
@[expose] public section
set_option Elab.async false
open Set
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert

theorem cqReal_add (a b : CQ) : cqReal (cqAdd a b)=cqReal a+cqReal b := by
  simp [cqReal,cqAdd]; ring

theorem cqReal_neg (a : CQ) : cqReal (cqNeg a) = -cqReal a := by
  simp [cqReal,cqNeg]; ring

theorem cqReal_sub (a b : CQ) : cqReal (cqSub a b)=cqReal a-cqReal b := by
  simp [cqSub,cqReal_add,cqReal_neg,sub_eq_add_neg]

theorem cqReal_mul (a b : CQ) : cqReal (cqMul a b)=cqReal a*cqReal b := by
  simp only [cqReal,cqMul]
  push_cast
  linear_combination -(a.2:ℂ)*(b.2:ℂ)*Complex.I_sq

theorem cqReal_scale (q : ℚ) (a : CQ) : cqReal (cqScale q a)=(q:ℂ)*cqReal a := by
  simp [cqReal,cqScale]; ring

theorem cqReal_pow (a : CQ) (n : ℕ) : cqReal (cqPow a n)=(cqReal a)^n := by
  induction n with
  | zero => simp [cqPow,cqReal]
  | succ n ih => rw [cqPow,cqReal_mul,ih,pow_succ]; ring

theorem cqReal_mk (a : CQ) : cqReal a=⟨(a.1:ℝ),(a.2:ℝ)⟩ := by
  apply Complex.ext <;> simp [cqReal]

theorem cqReal_inv (a : CQ) : cqReal (cqInv a)=(cqReal a)⁻¹ := by
  rw [cqReal_mk,cqReal_mk]
  apply Complex.ext <;> simp [cqInv,cqSq,Complex.inv_re,Complex.inv_im,Complex.normSq_apply,pow_two]

theorem cqReal_div (a b : CQ) : cqReal (cqDiv a b)=cqReal a/cqReal b := by
  simp [cqDiv,cqReal_mul,cqReal_inv,div_eq_mul_inv]

def BoxContains (b : QBox) (x : ℝ) : Prop := x ∈ Icc (b.1:ℝ) (b.2:ℝ)

theorem boxSingleton_sound (q : ℚ) : BoxContains (boxSingleton q) (q:ℝ) := ⟨le_rfl,le_rfl⟩

theorem boxAdd_sound (a b : QBox) (x y : ℝ) (hx : BoxContains a x) (hy : BoxContains b y) :
    BoxContains (boxAdd a b) (x+y) := by
  rcases hx with ⟨hx0,hx1⟩
  rcases hy with ⟨hy0,hy1⟩
  constructor <;> simp only [boxAdd,Rat.cast_add] <;> linarith

theorem boxNeg_sound (a : QBox) (x : ℝ) (hx : BoxContains a x) :
    BoxContains (boxNeg a) (-x) := by
  rcases hx with ⟨hx0,hx1⟩
  constructor <;> simp only [boxNeg,Rat.cast_neg] <;> linarith

theorem rectangle_mul_upper (a b c d x y M : ℝ) (hx : x ∈ Icc a b) (hy : y ∈ Icc c d)
    (hac : a*c ≤ M) (had : a*d ≤ M) (hbc : b*c ≤ M) (hbd : b*d ≤ M) : x*y ≤ M := by
  by_cases hy0 : 0 ≤ y
  · apply (mul_le_mul_of_nonneg_right hx.2 hy0).trans
    by_cases hb0 : 0 ≤ b
    · exact (mul_le_mul_of_nonneg_left hy.2 hb0).trans hbd
    · exact (mul_le_mul_of_nonpos_left hy.1 (le_of_not_ge hb0)).trans hbc
  · apply (mul_le_mul_of_nonpos_right hx.1 (le_of_not_ge hy0)).trans
    by_cases ha0 : 0 ≤ a
    · exact (mul_le_mul_of_nonneg_left hy.2 ha0).trans had
    · exact (mul_le_mul_of_nonpos_left hy.1 (le_of_not_ge ha0)).trans hac

theorem rectangle_mul_lower (a b c d x y m : ℝ) (hx : x ∈ Icc a b) (hy : y ∈ Icc c d)
    (hac : m ≤ a*c) (had : m ≤ a*d) (hbc : m ≤ b*c) (hbd : m ≤ b*d) : m ≤ x*y := by
  have hn : -x ∈ Icc (-b) (-a) := ⟨neg_le_neg hx.2,neg_le_neg hx.1⟩
  have hh := rectangle_mul_upper (-b) (-a) c d (-x) y (-m) hn hy
    (by nlinarith) (by nlinarith) (by nlinarith) (by nlinarith)
  nlinarith

theorem boxMul_sound (a b : QBox) (x y : ℝ) (hx : BoxContains a x) (hy : BoxContains b y) :
    BoxContains (boxMul a b) (x*y) := by
  constructor
  · apply rectangle_mul_lower (a.1:ℝ) a.2 b.1 b.2 x y _ hx hy
    all_goals dsimp [boxMul]; push_cast; aesop
  · apply rectangle_mul_upper (a.1:ℝ) a.2 b.1 b.2 x y _ hx hy
    all_goals dsimp [boxMul]; push_cast; aesop

theorem boxEnc_sound (v e : ℚ) (b : QBox) (x : ℝ)
    (hb : boxEnc v e=some b) (hx : |x-(v:ℝ)| ≤ (e:ℝ)) : BoxContains b x := by
  unfold boxEnc at hb
  split_ifs at hb with he
  · cases hb
    have hh := abs_le.mp hx
    constructor <;> dsimp <;> push_cast <;> linarith

theorem boxInv_sound (a b : QBox) (x : ℝ) (hx : BoxContains a x)
    (hb : boxInv a=some b) : BoxContains b x⁻¹ := by
  unfold boxInv at hb
  split_ifs at hb with ha
  cases hb
  rcases hx with ⟨hx0,hx1⟩
  change ((a.2⁻¹:ℚ):ℝ) ≤ x⁻¹ ∧ x⁻¹ ≤ ((a.1⁻¹:ℚ):ℝ)
  push_cast
  rcases ha with ha | ha
  · have haR : (0:ℝ)<(a.1:ℝ) := by exact_mod_cast ha
    have hxp : 0 < x := haR.trans_le hx0
    exact ⟨inv_anti₀ hxp hx1,inv_anti₀ haR hx0⟩
  · have haR : (a.2:ℝ)<(0:ℝ) := by exact_mod_cast ha
    have hxn : x < 0 := hx1.trans_lt haR
    have h₁ := inv_anti₀ (neg_pos.mpr haR) (neg_le_neg hx1)
    have h₂ := inv_anti₀ (neg_pos.mpr hxn) (neg_le_neg hx0)
    simp only [inv_neg] at h₁ h₂
    exact ⟨by linarith,by linarith⟩

theorem boxAbs_sound (a : QBox) (x : ℝ) (hx : BoxContains a x) :
    BoxContains (boxAbs a) |x| := by
  rcases hx with ⟨hx0,hx1⟩
  have hupper : |x| ≤ max |(a.1:ℝ)| |(a.2:ℝ)| := by
    apply abs_le.mpr
    constructor
    · have h := le_max_left |(a.1:ℝ)| |(a.2:ℝ)|
      linarith [neg_abs_le (a.1:ℝ)]
    · have h := le_max_right |(a.1:ℝ)| |(a.2:ℝ)|
      linarith [le_abs_self (a.2:ℝ)]
  constructor
  · dsimp [boxAbs]
    split_ifs with ha
    · simpa only [Rat.cast_zero] using abs_nonneg x
    · push_cast
      have hcross : ¬((a.1:ℝ) ≤ 0 ∧ 0 ≤ (a.2:ℝ)) := by exact_mod_cast ha
      rcases lt_or_ge (0:ℝ) (a.1:ℝ) with ha0 | ha0
      · have hxp : 0 ≤ x := ha0.le.trans hx0
        rw [abs_of_nonneg hxp]
        exact (min_le_left _ _).trans (by simpa [abs_of_pos ha0] using hx0)
      · have han : (a.2:ℝ)<0 := lt_of_not_ge (fun h => hcross ⟨ha0,h⟩)
        have hxn : x ≤ 0 := hx1.trans han.le
        rw [abs_of_nonpos hxn]
        exact (min_le_right _ _).trans (by simpa [abs_of_neg han] using neg_le_neg hx1)
  · simpa [boxAbs] using hupper

open OAI.InternalCatalan

theorem source_arg_of_re_pos (a b : ℝ) (ha : 0 < a) :
    Complex.arg (⟨a,b⟩:ℂ)=Real.arctan (b/a) := barrierComplexArg_of_re_pos ha

theorem source_arg_of_im_pos (a b : ℝ) (hb : 0 < b) :
    Complex.arg (⟨a,b⟩:ℂ)=Real.pi/2-Real.arctan (a/b) := by
  have hrot : barrierOctantRotate 2 (⟨a,b⟩:ℂ)=⟨2*b,-2*a⟩ := by
    apply Complex.ext <;> norm_num [barrierOctantRotate,barrierOctantMultiplier,pow_two,
      Complex.mul_re,Complex.mul_im] <;> ring
  have ht : -a/b=(-2*a)/(2*b) := by field_simp <;> ring
  have hrange : (2:ℝ)*(Real.pi/4)+Real.arctan (-a/b) ∈ Ioc (-Real.pi) Real.pi := by
    have hh := Real.arctan_mem_Ioo (-a/b)
    constructor <;> linarith [Real.pi_pos,hh.1,hh.2]
  have h := barrierComplexArg_octant_of_eq 2 (⟨a,b⟩:ℂ) (2*b) (-2*a) (-a/b)
    hrot (by linarith) ht (by simpa only [Int.cast_neg,Int.cast_ofNat] using hrange)
  rw [h,neg_div,Real.arctan_neg]
  ring

theorem source_arg_of_im_neg (a b : ℝ) (hb : b < 0) :
    Complex.arg (⟨a,b⟩:ℂ)= -(Real.pi/2)-Real.arctan (a/b) := by
  have hrot : barrierOctantRotate (-2) (⟨a,b⟩:ℂ)=⟨-2*b,2*a⟩ := by
    apply Complex.ext <;> norm_num [barrierOctantRotate,barrierOctantMultiplier,pow_two,
      Complex.mul_re,Complex.mul_im] <;> ring
  have ht : -a/b=(2*a)/(-2*b) := by field_simp <;> ring
  have hrange : (-2:ℝ)*(Real.pi/4)+Real.arctan (-a/b) ∈ Ioc (-Real.pi) Real.pi := by
    have hh := Real.arctan_mem_Ioo (-a/b)
    constructor <;> linarith [Real.pi_pos,hh.1,hh.2]
  have h := barrierComplexArg_octant_of_eq (-2) (⟨a,b⟩:ℂ) (-2*b) (2*a) (-a/b)
    hrot (by linarith) ht (by simpa only [Int.cast_neg,Int.cast_ofNat] using hrange)
  rw [h,neg_div,Real.arctan_neg]
  ring

theorem real_inv_interval (c d y : ℝ) (hy : y ∈ Icc c d) (hs : 0 < c ∨ d < 0) :
    y⁻¹ ∈ Icc d⁻¹ c⁻¹ := by
  rcases hs with h | h
  · exact ⟨inv_anti₀ (h.trans_le hy.1) hy.2,inv_anti₀ h hy.1⟩
  · have h₁ := inv_anti₀ (neg_pos.mpr h) (neg_le_neg hy.2)
    have h₂ := inv_anti₀ (neg_pos.mpr (hy.2.trans_lt h)) (neg_le_neg hy.1)
    simp only [inv_neg] at h₁ h₂
    exact ⟨by linarith,by linarith⟩

theorem monotone_ratio_interval (f : ℝ → ℝ) (hf : Monotone f)
    (a b c d x y L U : ℝ) (hx : x ∈ Icc a b) (hy : y ∈ Icc c d)
    (hs : 0 < c ∨ d < 0)
    (h00 : f (a/c) ∈ Icc L U) (h01 : f (a/d) ∈ Icc L U)
    (h10 : f (b/c) ∈ Icc L U) (h11 : f (b/d) ∈ Icc L U) : f (x/y) ∈ Icc L U := by
  have hi := real_inv_interval c d y hy hs
  have hr : x/y ∈ Icc (min (min (a*d⁻¹) (a*c⁻¹)) (min (b*d⁻¹) (b*c⁻¹)))
      (max (max (a*d⁻¹) (a*c⁻¹)) (max (b*d⁻¹) (b*c⁻¹))) := by
    rw [div_eq_mul_inv]
    constructor
    · apply rectangle_mul_lower a b d⁻¹ c⁻¹ x y⁻¹ _ hx hi <;> aesop
    · apply rectangle_mul_upper a b d⁻¹ c⁻¹ x y⁻¹ _ hx hi <;> aesop
  simp only [div_eq_mul_inv] at h00 h01 h10 h11
  have hl : L ≤ f (min (min (a*d⁻¹) (a*c⁻¹)) (min (b*d⁻¹) (b*c⁻¹))) := by
    simp only [hf.map_min]
    exact le_min (le_min h01.1 h00.1) (le_min h11.1 h10.1)
  have hu : f (max (max (a*d⁻¹) (a*c⁻¹)) (max (b*d⁻¹) (b*c⁻¹))) ≤ U := by
    simp only [hf.map_max]
    exact max_le (max_le h01.2 h00.2) (max_le h11.2 h10.2)
  exact ⟨hl.trans (hf hr.1),(hf hr.2).trans hu⟩

theorem sub_interval_iff (K z L U : ℝ) : K-z ∈ Icc L U ↔ z ∈ Icc (K-U) (K-L) := by
  constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]

theorem arg_rectangle_interval (a b c d x y L U : ℝ)
    (hx : x ∈ Icc a b) (hy : y ∈ Icc c d) (hs : 0 < a ∨ 0 < c ∨ d < 0)
    (h00 : Complex.arg (⟨a,c⟩:ℂ) ∈ Icc L U) (h01 : Complex.arg (⟨a,d⟩:ℂ) ∈ Icc L U)
    (h10 : Complex.arg (⟨b,c⟩:ℂ) ∈ Icc L U) (h11 : Complex.arg (⟨b,d⟩:ℂ) ∈ Icc L U) :
    Complex.arg (⟨x,y⟩:ℂ) ∈ Icc L U := by
  rcases hs with ha | hc | hd
  · have hb : 0 < b := ha.trans_le (hx.1.trans hx.2)
    rw [source_arg_of_re_pos a c ha] at h00
    rw [source_arg_of_re_pos a d ha] at h01
    rw [source_arg_of_re_pos b c hb] at h10
    rw [source_arg_of_re_pos b d hb] at h11
    rw [source_arg_of_re_pos x y (ha.trans_le hx.1)]
    exact monotone_ratio_interval Real.arctan Real.arctan_strictMono.monotone
      c d a b y x L U hy hx (Or.inl ha) h00 h10 h01 h11
  · have hd : 0 < d := hc.trans_le (hy.1.trans hy.2)
    rw [source_arg_of_im_pos a c hc,sub_interval_iff] at h00
    rw [source_arg_of_im_pos a d hd,sub_interval_iff] at h01
    rw [source_arg_of_im_pos b c hc,sub_interval_iff] at h10
    rw [source_arg_of_im_pos b d hd,sub_interval_iff] at h11
    rw [source_arg_of_im_pos x y (hc.trans_le hy.1),sub_interval_iff]
    exact monotone_ratio_interval Real.arctan Real.arctan_strictMono.monotone
      a b c d x y _ _ hx hy (Or.inl hc) h00 h01 h10 h11
  · have hc : c < 0 := (hy.1.trans hy.2).trans_lt hd
    rw [source_arg_of_im_neg a c hc,sub_interval_iff] at h00
    rw [source_arg_of_im_neg a d hd,sub_interval_iff] at h01
    rw [source_arg_of_im_neg b c hc,sub_interval_iff] at h10
    rw [source_arg_of_im_neg b d hd,sub_interval_iff] at h11
    rw [source_arg_of_im_neg x y (hy.2.trans_lt hd),sub_interval_iff]
    exact monotone_ratio_interval Real.arctan Real.arctan_strictMono.monotone
      a b c d x y _ _ hx hy (Or.inr hd) h00 h01 h10 h11

def argPointEnc (n : ℕ) (p : CQ) : Option QBox := do
  let (v,e) ← CatalanMeasure.GenD.Signed.LogEval.argQ n p.1 p.2
  boxEnc v e

theorem argPointEnc_sound (n : ℕ) (p : CQ) (b : QBox) (h : argPointEnc n p=some b) :
    BoxContains b (Complex.arg (⟨(p.1:ℝ),(p.2:ℝ)⟩:ℂ)) := by
  unfold argPointEnc at h
  cases he : CatalanMeasure.GenD.Signed.LogEval.argQ n p.1 p.2 with
  | none => simp [he] at h
  | some ve =>
    have hb : boxEnc ve.1 ve.2=some b := by simpa [he] using h
    exact boxEnc_sound ve.1 ve.2 b _ hb (CatalanMeasure.GenD.Signed.LogEval.argQ_spec he)

theorem pi_enclosure :
    |Real.pi-((4*CatalanMeasure.GenD.Signed.LogEval.PI4:ℚ):ℝ)| ≤
      ((4*CatalanMeasure.GenD.Signed.LogEval.PI4E:ℚ):ℝ) := by
  calc
    _ = |(4:ℝ)*(Real.pi/4-(CatalanMeasure.GenD.Signed.LogEval.PI4:ℝ))| := by
      congr 1; push_cast; ring
    _ = 4*|Real.pi/4-(CatalanMeasure.GenD.Signed.LogEval.PI4:ℝ)| := by rw [abs_mul]; norm_num
    _ ≤ 4*(CatalanMeasure.GenD.Signed.LogEval.PI4E:ℝ) :=
      mul_le_mul_of_nonneg_left CatalanMeasure.GenD.Signed.LogEval.pi4_spec (by norm_num)
    _ = _ := by push_cast; ring

def hull4 (a b c d : QBox) : QBox :=
  (([a,b,c,d].map Prod.fst).foldl min a.1,([a,b,c,d].map Prod.snd).foldl max a.2)

theorem hull4_sound (a b c d : QBox) (x : ℝ)
    (h : BoxContains a x ∨ BoxContains b x ∨ BoxContains c x ∨ BoxContains d x) :
    BoxContains (hull4 a b c d) x := by
  rcases h with h | h | h | h
  all_goals rcases h with ⟨h0,h1⟩
  all_goals constructor <;> dsimp [hull4] <;> push_cast <;> aesop

theorem argBox_sound (n : ℕ) (A B out : QBox) (x y : ℝ)
    (hx : BoxContains A x) (hy : BoxContains B y) (h : argBox n A B=some out) :
    BoxContains out (Complex.arg (⟨x,y⟩:ℂ)) := by
  unfold argBox at h
  split_ifs at h with hneg hgood
  · have hy0 : y=0 := by
      rcases hy with ⟨hy0,hy1⟩
      rcases hneg with ⟨hB0,hB1,hA⟩
      simp only [hB0,hB1,Rat.cast_zero] at hy0 hy1
      linarith
    have hxn : x<0 := hx.2.trans_lt (by exact_mod_cast hneg.2.2)
    have harg : Complex.arg (⟨x,y⟩:ℂ)=Real.pi := Complex.arg_eq_pi_iff.mpr ⟨hxn,hy0⟩
    rw [harg]
    exact boxEnc_sound _ _ out Real.pi h pi_enclosure
  · let f := argPointEnc n
    change (do
      let bounds ← [(A.1,B.1),(A.1,B.2),(A.2,B.1),(A.2,B.2)].mapM f
      pure ((bounds.map Prod.fst).foldl min ((bounds.headD (0,0)).1),
        (bounds.map Prod.snd).foldl max ((bounds.headD (0,0)).2)))=some out at h
    rcases h00 : f (A.1,B.1) with _ | b00
    · simp [h00] at h
    rcases h01 : f (A.1,B.2) with _ | b01
    · simp [h00,h01] at h
    rcases h10 : f (A.2,B.1) with _ | b10
    · simp [h00,h01,h10] at h
    rcases h11 : f (A.2,B.2) with _ | b11
    · simp [h00,h01,h10,h11] at h
    have hout : hull4 b00 b01 b10 b11=out := by simpa [hull4,h00,h01,h10,h11] using h
    rw [← hout]
    have hc00 := argPointEnc_sound n (A.1,B.1) b00 h00
    have hc01 := argPointEnc_sound n (A.1,B.2) b01 h01
    have hc10 := argPointEnc_sound n (A.2,B.1) b10 h10
    have hc11 := argPointEnc_sound n (A.2,B.2) b11 h11
    apply arg_rectangle_interval (A.1:ℝ) A.2 B.1 B.2 x y _ _ hx hy
    · exact_mod_cast hgood
    · exact hull4_sound _ _ _ _ _ (Or.inl hc00)
    · exact hull4_sound _ _ _ _ _ (Or.inr (Or.inl hc01))
    · exact hull4_sound _ _ _ _ _ (Or.inr (Or.inr (Or.inl hc10)))
    · exact hull4_sound _ _ _ _ _ (Or.inr (Or.inr (Or.inr hc11)))

theorem scalarCheck_sound (e : ScalarExpr) (b : QBox) (h : e.check=some b) :
    e.value ∈ Icc (b.1:ℝ) (b.2:ℝ) := by
  change BoxContains b e.value
  induction e generalizing b with
  | rat q =>
    simp only [ScalarExpr.check] at h
    cases Option.some.inj h
    exact ⟨le_rfl,le_rfl⟩
  | add a c ihA ihC =>
    change (a.check.bind (fun A => c.check.bind (fun B => some (boxAdd A B))))=some b at h
    simp only [Option.bind_eq_some_iff] at h
    obtain ⟨A,hA,B,hB,hout⟩ := h
    cases Option.some.inj hout
    exact boxAdd_sound A B a.value c.value (ihA A hA) (ihC B hB)
  | neg a ihA =>
    change (a.check.bind (fun A => some (boxNeg A)))=some b at h
    simp only [Option.bind_eq_some_iff] at h
    obtain ⟨A,hA,hout⟩ := h
    cases Option.some.inj hout
    exact boxNeg_sound A a.value (ihA A hA)
  | mul a c ihA ihC =>
    change (a.check.bind (fun A => c.check.bind (fun B => some (boxMul A B))))=some b at h
    simp only [Option.bind_eq_some_iff] at h
    obtain ⟨A,hA,B,hB,hout⟩ := h
    cases Option.some.inj hout
    exact boxMul_sound A B a.value c.value (ihA A hA) (ihC B hB)
  | inv a ihA =>
    change (a.check.bind boxInv)=some b at h
    simp only [Option.bind_eq_some_iff] at h
    obtain ⟨A,hA,hout⟩ := h
    exact boxInv_sound A b a.value (ihA A hA) hout
  | abs a ihA =>
    change (a.check.bind (fun A => some (boxAbs A)))=some b at h
    simp only [Option.bind_eq_some_iff] at h
    obtain ⟨A,hA,hout⟩ := h
    cases Option.some.inj hout
    exact boxAbs_sound A a.value (ihA A hA)
  | log n q =>
    change ((CatalanMeasure.GenD.Signed.LogEval.logQ n q).bind (fun ve => boxEnc ve.1 ve.2))=some b at h
    simp only [Option.bind_eq_some_iff] at h
    obtain ⟨⟨v,err⟩,hv,henc⟩ := h
    exact boxEnc_sound v err b _ henc (CatalanMeasure.GenD.Signed.LogEval.logQ_spec hv).2
  | arg n q =>
    change (if cqSq q=0 then none else
      (CatalanMeasure.GenD.Signed.LogEval.argQ n q.1 q.2).bind (fun ve => boxEnc ve.1 ve.2))=some b at h
    split_ifs at h with hzero
    simp only [Option.bind_eq_some_iff] at h
    obtain ⟨⟨v,err⟩,hv,henc⟩ := h
    apply boxEnc_sound v err b _ henc
    simpa only [ScalarExpr.value,cqReal_mk] using CatalanMeasure.GenD.Signed.LogEval.argQ_spec hv
  | pi => exact boxEnc_sound _ _ b _ h pi_enclosure
  | atan n q =>
    change ((CatalanMeasure.GenD.Signed.LogEval.atanQ n q).bind (fun ve => boxEnc ve.1 ve.2))=some b at h
    simp only [Option.bind_eq_some_iff] at h
    obtain ⟨⟨v,err⟩,hv,henc⟩ := h
    exact boxEnc_sound v err b _ henc (CatalanMeasure.GenD.Signed.LogEval.atanQ_spec hv)
  | logE n a ihA =>
    change (a.check.bind (fun A => if 0 < A.1 then
      (CatalanMeasure.GenD.Signed.LogEval.logQ n A.1).bind (fun ve =>
        (CatalanMeasure.GenD.Signed.LogEval.logQ n A.2).bind (fun we => some (ve.1-ve.2,we.1+we.2)))
      else none))=some b at h
    simp only [Option.bind_eq_some_iff] at h
    obtain ⟨A,hA,hrest⟩ := h
    split_ifs at hrest with hpos
    simp only [Option.bind_eq_some_iff] at hrest
    obtain ⟨⟨vl,el⟩,hlogL,⟨vr,er⟩,hlogR,hout⟩ := hrest
    cases Option.some.inj hout
    have hsem := ihA A hA
    have hlo : (0:ℝ)<(A.1:ℝ) := by exact_mod_cast hpos
    have hxp : 0 < a.value := hlo.trans_le hsem.1
    have hleft := Real.log_le_log hlo hsem.1
    have hright := Real.log_le_log hxp hsem.2
    have hEL : |Real.log (A.1:ℝ)-(vl:ℝ)| ≤ (el:ℝ) :=
      (CatalanMeasure.GenD.Signed.LogEval.logQ_spec hlogL).2
    have hER : |Real.log (A.2:ℝ)-(vr:ℝ)| ≤ (er:ℝ) :=
      (CatalanMeasure.GenD.Signed.LogEval.logQ_spec hlogR).2
    have hEL' := abs_le.mp hEL
    have hER' := abs_le.mp hER
    simp only [ScalarExpr.value]
    constructor <;> dsimp <;> push_cast <;> linarith [hEL'.1,hEL'.2,hER'.1,hER'.2]
  | argE n a c ihA ihC =>
    change (a.check.bind (fun A => c.check.bind (fun B => argBox n A B)))=some b at h
    simp only [Option.bind_eq_some_iff] at h
    obtain ⟨A,hA,B,hB,hout⟩ := h
    have hh := argBox_sound n A B b a.value c.value (ihA A hA) (ihC B hB) hout
    have heq : (a.value:ℂ)+(c.value:ℂ)*Complex.I=(⟨a.value,c.value⟩:ℂ) := by
      apply Complex.ext <;> simp
    simpa only [ScalarExpr.value,heq] using hh
  | sqrt a lo hi ihA =>
    change (a.check.bind (fun A => if 0 ≤ lo ∧ lo ≤ hi ∧ 0 ≤ A.1 ∧ lo^2 ≤ A.1 ∧ A.2 ≤ hi^2
      then some (lo,hi) else none))=some b at h
    simp only [Option.bind_eq_some_iff] at h
    obtain ⟨A,hA,hrest⟩ := h
    split_ifs at hrest with hg
    cases Option.some.inj hrest
    rcases hg with ⟨hlo,hlh,hA0,hLow,hHigh⟩
    have hsem := ihA A hA
    have hloR : (0:ℝ) ≤ (lo:ℝ) := by exact_mod_cast hlo
    have hhiR : (lo:ℝ) ≤ (hi:ℝ) := by exact_mod_cast hlh
    have hA0R : (0:ℝ) ≤ (A.1:ℝ) := by exact_mod_cast hA0
    have hLowR : (lo:ℝ)^2 ≤ (A.1:ℝ) := by exact_mod_cast hLow
    have hHighR : (A.2:ℝ) ≤ (hi:ℝ)^2 := by exact_mod_cast hHigh
    have hnonneg : 0 ≤ a.value := hA0R.trans hsem.1
    have hsq := Real.sq_sqrt hnonneg
    have hn := Real.sqrt_nonneg a.value
    simp only [ScalarExpr.value]
    constructor <;> dsimp <;> nlinarith [hsem.1,hsem.2]

#print axioms scalarCheck_sound
#print axioms argBox_sound
end CatalanCore.Li2.DecayCert
