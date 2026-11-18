module
public import CatalanCore.Li2.DecayCert.Arithmetic
@[expose] public section
set_option Elab.async false
namespace CatalanCore.Li2.DecayCert.Simple
abbrev FBox := ℤ×ℤ
def absI (a : ℤ) : ℤ := max a (-a)
def S : ℤ := 2^120
def floorDiv (a b : ℤ) : ℤ := if 0≤b then a/b else (-a)/(-b)
def ceilDiv (a b : ℤ) : ℤ := -(floorDiv (-a) b)
def boxZero : FBox := (0,0)
def boxOne : FBox := (S,S)
def boxOfQ (q : ℚ) : FBox := (q.num*S/(q.den:ℤ),ceilDiv (q.num*S) q.den)
def boxAddF (a b : FBox) : FBox := (a.1+b.1,a.2+b.2)
def boxNegF (a : FBox) : FBox := (-a.2,-a.1)
def boxSubF (a b : FBox) : FBox := boxAddF a (boxNegF b)
def boxScaleF (k : ℤ) (a : FBox) : FBox :=
  if 0≤k then (k*a.1,k*a.2) else (k*a.2,k*a.1)
def min4 (a b c d : ℤ) : ℤ := min (min a b) (min c d)
def max4 (a b c d : ℤ) : ℤ := max (max a b) (max c d)
def boxMulF (a b : FBox) : FBox :=
  (min4 (a.1*b.1) (a.1*b.2) (a.2*b.1) (a.2*b.2)/S,
   ceilDiv (max4 (a.1*b.1) (a.1*b.2) (a.2*b.1) (a.2*b.2)) S)
def boxDivF (a b : FBox) : Option FBox :=
  if 0<b.1 ∨ b.2<0 then
    some (min4 (floorDiv (a.1*S) b.1) (floorDiv (a.1*S) b.2) (floorDiv (a.2*S) b.1) (floorDiv (a.2*S) b.2),
      max4 (ceilDiv (a.1*S) b.1) (ceilDiv (a.1*S) b.2)
        (ceilDiv (a.2*S) b.1) (ceilDiv (a.2*S) b.2))
  else none
def boxDivNatF (n : ℕ) (a : FBox) : FBox := (a.1/(n:ℤ),ceilDiv a.2 n)
def boxAbsF (a : FBox) : FBox :=
  if 0≤a.1 then a else if a.2≤0 then boxNegF a else (0,max (-a.1) a.2)
def boxPowF (a : FBox) : ℕ → FBox
  | 0 => boxOne
  | n+1 => boxMulF (boxPowF a n) a

noncomputable section
 theorem S_pos : (0:ℤ)<S := by unfold S; positivity
 theorem S_real_pos : (0:ℝ)<(S:ℝ) := by exact_mod_cast S_pos
 def Contains (a : FBox) (x : ℝ) : Prop := dec S a.1≤x ∧ x≤dec S a.2
 theorem ediv_le_real (a b : ℤ) (hb : 0<b) : ((a/b:ℤ):ℝ)≤(a:ℝ)/(b:ℝ) := by
  have hbR : (0:ℝ)<(b:ℝ) := by exact_mod_cast hb
  apply (le_div_iff₀ hbR).2
  have hr : (0:ℝ)≤((a%b:ℤ):ℝ) := by exact_mod_cast Int.emod_nonneg a hb.ne'
  have he : ((a%b:ℤ):ℝ)+((a/b:ℤ):ℝ)*(b:ℝ)=(a:ℝ) := by
   exact_mod_cast Int.emod_add_ediv_mul a b
  linarith
 theorem floorDiv_le (a b : ℤ) (hb : b≠0) : (floorDiv a b:ℝ)≤(a:ℝ)/(b:ℝ) := by
  unfold floorDiv
  split_ifs with h
  · exact ediv_le_real a b (lt_of_le_of_ne h (Ne.symm hb))
  · have hh:=ediv_le_real (-a) (-b) (by omega)
    simpa only [Int.cast_neg, neg_div_neg_eq] using hh
 theorem ceilDiv_ge (a b : ℤ) (hb : b≠0) : (a:ℝ)/(b:ℝ)≤(ceilDiv a b:ℝ) := by
  have hh:=floorDiv_le (-a) b hb
  simp only [ceilDiv, Int.cast_neg, neg_div] at *
  linarith
 theorem boxZero_sound : Contains boxZero 0 := by simp [Contains,boxZero,dec]
 theorem boxOne_sound : Contains boxOne 1 := by
  simp [Contains,boxOne,dec, ne_of_gt S_real_pos]
 theorem boxAddF_sound (a b : FBox) (x y : ℝ) (hx : Contains a x) (hy : Contains b y) :
    Contains (boxAddF a b) (x+y) := by
  simpa only [Contains,boxAddF,dec_add] using And.intro (add_le_add hx.1 hy.1) (add_le_add hx.2 hy.2)
 theorem boxNegF_sound (a : FBox) (x : ℝ) (hx : Contains a x) : Contains (boxNegF a) (-x) := by
  simpa only [Contains,boxNegF,dec,Int.cast_neg,neg_div,neg_le_neg_iff] using And.intro hx.2 hx.1
 theorem boxSubF_sound (a b : FBox) (x y : ℝ) (hx : Contains a x) (hy : Contains b y) :
    Contains (boxSubF a b) (x-y) := by
  exact boxAddF_sound a (boxNegF b) x (-y) hx (boxNegF_sound b y hy)
 theorem between_mul (a b x c : ℝ) (hx : a≤x ∧ x≤b) :
    min (a*c) (b*c)≤x*c ∧ x*c≤max (a*c) (b*c) := by
  rcases le_total 0 c with hc|hc
  · exact ⟨(min_le_left _ _).trans (mul_le_mul_of_nonneg_right hx.1 hc),
      (mul_le_mul_of_nonneg_right hx.2 hc).trans (le_max_right _ _)⟩
  · exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_right hx.2 hc),
      (mul_le_mul_of_nonpos_right hx.1 hc).trans (le_max_left _ _)⟩
 theorem product_corners (a b c d x y : ℝ) (hx : a≤x ∧ x≤b) (hy : c≤y ∧ y≤d) :
    min (min (a*c) (a*d)) (min (b*c) (b*d))≤x*y ∧
    x*y≤max (max (a*c) (a*d)) (max (b*c) (b*d)) := by
  have h:=between_mul a b x y hx
  have ha:=between_mul c d y a hy
  have hb:=between_mul c d y b hy
  simp only [mul_comm _ a] at ha
  simp only [mul_comm _ b] at hb
  exact ⟨(min_le_min ha.1 hb.1).trans h.1,h.2.trans (max_le_max ha.2 hb.2)⟩

theorem contains_iff (a : FBox) (x : ℝ) :
    Contains a x ↔ (a.1:ℝ)≤(S:ℝ)*x ∧ (S:ℝ)*x≤(a.2:ℝ) := by
  simp only [Contains,dec,div_le_iff₀ S_real_pos,le_div_iff₀ S_real_pos,mul_comm x]
 theorem boxMulF_sound (a b : FBox) (x y : ℝ) (hx : Contains a x) (hy : Contains b y) :
    Contains (boxMulF a b) (x*y) := by
  have h:=product_corners (a.1:ℝ) a.2 b.1 b.2 ((S:ℝ)*x) ((S:ℝ)*y)
    ((contains_iff a x).mp hx) ((contains_iff b y).mp hy)
  let lo:=min4 (a.1*b.1) (a.1*b.2) (a.2*b.1) (a.2*b.2)
  let hi:=max4 (a.1*b.1) (a.1*b.2) (a.2*b.1) (a.2*b.2)
  have hl : (lo:ℝ)≤((S:ℝ)*x)*((S:ℝ)*y) := by
    simpa only [lo,min4,Int.cast_min,Int.cast_mul] using h.1
  have hh : ((S:ℝ)*x)*((S:ℝ)*y)≤(hi:ℝ) := by
    simpa only [hi,max4,Int.cast_max,Int.cast_mul] using h.2
  have hfl:=(le_div_iff₀ S_real_pos).mp (ediv_le_real lo S S_pos)
  have hce:=(div_le_iff₀ S_real_pos).mp (ceilDiv_ge hi S S_pos.ne')
  apply (contains_iff _ _).2
  change ((lo/S:ℤ):ℝ)≤(S:ℝ)*(x*y) ∧ (S:ℝ)*(x*y)≤(ceilDiv hi S:ℝ)
  constructor <;> nlinarith [S_real_pos]
 theorem boxPowF_sound (a : FBox) (x : ℝ) (hx : Contains a x) (n : ℕ) :
    Contains (boxPowF a n) (x^n) := by
  induction n with
  | zero => simpa only [boxPowF,pow_zero] using boxOne_sound
  | succ n ih => simpa only [boxPowF,pow_succ] using boxMulF_sound (boxPowF a n) a (x^n) x ih hx
 theorem boxScaleF_sound (k : ℤ) (a : FBox) (x : ℝ) (hx : Contains a x) :
    Contains (boxScaleF k a) ((k:ℝ)*x) := by
  have h:= (contains_iff a x).mp hx
  apply (contains_iff _ _).2
  unfold boxScaleF
  split_ifs with hk
  · have hkR : (0:ℝ)≤(k:ℝ) := by exact_mod_cast hk
    simp only [Int.cast_mul]
    constructor <;> nlinarith [mul_le_mul_of_nonneg_left h.1 hkR,mul_le_mul_of_nonneg_left h.2 hkR]
  · have hkR : (k:ℝ)≤0 := by exact_mod_cast (le_of_lt (lt_of_not_ge hk))
    simp only [Int.cast_mul]
    constructor <;> nlinarith [mul_le_mul_of_nonpos_left h.1 hkR,mul_le_mul_of_nonpos_left h.2 hkR]
 theorem boxOfQ_sound (q : ℚ) : Contains (boxOfQ q) (q:ℝ) := by
  have hd : (0:ℤ)<(q.den:ℤ) := by exact_mod_cast q.pos
  have hlo:=(ediv_le_real (q.num*S) q.den hd)
  have hhi:=(ceilDiv_ge (q.num*S) q.den hd.ne')
  apply (contains_iff _ _).2
  change ((q.num*S/(q.den:ℤ):ℤ):ℝ)≤(S:ℝ)*(q:ℝ) ∧
    (S:ℝ)*(q:ℝ)≤(ceilDiv (q.num*S) q.den:ℝ)
  have he : ((q.num*S:ℤ):ℝ)/(q.den:ℝ)=(S:ℝ)*(q:ℝ) := by
    rw [Rat.cast_def]
    push_cast
    ring
  exact ⟨hlo.trans_eq he,he.symm.trans_le hhi⟩

theorem boxDivNatF_sound (n : ℕ) (hn : 0<n) (a : FBox) (x : ℝ) (hx : Contains a x) :
    Contains (boxDivNatF n a) (x/(n:ℝ)) := by
  have hnI : (0:ℤ)<(n:ℤ) := by exact_mod_cast hn
  have hnR : (0:ℝ)<(n:ℝ) := by exact_mod_cast hn
  have h:=(contains_iff a x).mp hx
  apply (contains_iff _ _).2
  have hl:=(ediv_le_real a.1 n hnI).trans (div_le_div_of_nonneg_right h.1 hnR.le)
  have hh:=(div_le_div_of_nonneg_right h.2 hnR.le).trans (ceilDiv_ge a.2 n hnI.ne')
  simpa only [boxDivNatF,mul_div_assoc,Int.cast_natCast] using And.intro hl hh
 theorem boxAbsF_sound (a : FBox) (x : ℝ) (hx : Contains a x) : Contains (boxAbsF a) |x| := by
  unfold boxAbsF
  split_ifs with hpos hneg
  · have hp : (0:ℝ)≤(a.1:ℝ) := by exact_mod_cast hpos
    have ha : (0:ℝ)≤dec S a.1 := div_nonneg hp S_real_pos.le
    have h : 0≤x := ha.trans hx.1
    simpa only [abs_of_nonneg h] using hx
  · have h : x≤0 := hx.2.trans (div_nonpos_of_nonpos_of_nonneg (Int.cast_nonpos.mpr hneg) S_real_pos.le)
    simpa only [abs_of_nonpos h] using boxNegF_sound a x hx
  · apply (contains_iff _ _).2
    constructor
    · simpa using mul_nonneg S_real_pos.le (abs_nonneg x)
    · have h:=(contains_iff a x).mp hx
      rw [Int.cast_max,Int.cast_neg]
      rcases le_total 0 x with hx0|hx0
      · rw [abs_of_nonneg hx0]; exact h.2.trans (le_max_right _ _)
      · rw [abs_of_nonpos hx0]; have h':=neg_le_neg h.1
        nlinarith [le_max_left (-(a.1:ℝ)) (a.2:ℝ)]
 theorem inverse_interval (a b y : ℝ) (hy : a≤y ∧ y≤b) (hdom : 0<a ∨ b<0) :
    1/b≤1/y ∧ 1/y≤1/a := by
  rcases hdom with h|h
  · exact ⟨one_div_le_one_div_of_le (h.trans_le hy.1) hy.2,one_div_le_one_div_of_le h hy.1⟩
  · exact ⟨one_div_le_one_div_of_neg_of_le h hy.2,one_div_le_one_div_of_neg_of_le (hy.2.trans_lt h) hy.1⟩
 theorem quotient_corners (a b c d x y : ℝ) (hx : a≤x ∧ x≤b) (hy : c≤y ∧ y≤d)
    (hdom : 0<c ∨ d<0) :
    min (min (a/c) (a/d)) (min (b/c) (b/d))≤x/y ∧
    x/y≤max (max (a/c) (a/d)) (max (b/c) (b/d)) := by
  have h:=product_corners a b (1/d) (1/c) x (1/y) hx (inverse_interval c d y hy hdom)
  simpa only [←div_eq_mul_one_div,min_comm (a/d),min_comm (b/d),max_comm (a/d),max_comm (b/d)] using h
 theorem round_quotient (a b : ℤ) (hb : b≠0) :
    (floorDiv (a*S) b:ℝ)≤(S:ℝ)*((a:ℝ)/(b:ℝ)) ∧
    (S:ℝ)*((a:ℝ)/(b:ℝ))≤(ceilDiv (a*S) b:ℝ) := by
  have he : ((a*S:ℤ):ℝ)/(b:ℝ)=(S:ℝ)*((a:ℝ)/(b:ℝ)) := by push_cast; ring
  exact ⟨(floorDiv_le (a*S) b hb).trans_eq he,he.symm.trans_le (ceilDiv_ge (a*S) b hb)⟩

theorem boxDivF_sound (a b c : FBox) (x y : ℝ) (hx : Contains a x) (hy : Contains b y)
    (hc : boxDivF a b=some c) : Contains c (x/y) := by
  unfold boxDivF at hc
  split_ifs at hc with hdom
  · cases hc
    have hy':=(contains_iff b y).mp hy
    have hdomR : (0:ℝ)<(b.1:ℝ) ∨ (b.2:ℝ)<0 := by exact_mod_cast hdom
    have hb1 : b.1≠0 := by
      apply Int.cast_ne_zero.mp (show (b.1:ℝ)≠0 from ?_)
      intro hz
      rcases hdomR with h|h <;> linarith
    have hb2 : b.2≠0 := by
      apply Int.cast_ne_zero.mp (show (b.2:ℝ)≠0 from ?_)
      intro hz
      rcases hdomR with h|h <;> linarith
    have h:=quotient_corners (a.1:ℝ) a.2 b.1 b.2 ((S:ℝ)*x) ((S:ℝ)*y)
      ((contains_iff a x).mp hx) hy' hdomR
    rw [mul_div_mul_left _ _ (ne_of_gt S_real_pos)] at h
    have h11:=round_quotient a.1 b.1 hb1
    have h12:=round_quotient a.1 b.2 hb2
    have h21:=round_quotient a.2 b.1 hb1
    have h22:=round_quotient a.2 b.2 hb2
    have hl:=mul_le_mul_of_nonneg_left h.1 S_real_pos.le
    have hh:=mul_le_mul_of_nonneg_left h.2 S_real_pos.le
    simp only [mul_min_of_nonneg _ _ S_real_pos.le,mul_max_of_nonneg _ _ S_real_pos.le] at hl hh
    apply (contains_iff _ _).2
    simp only [min4,max4,Int.cast_min,Int.cast_max]
    exact ⟨(min_le_min (min_le_min h11.1 h12.1) (min_le_min h21.1 h22.1)).trans hl,
      hh.trans (max_le_max (max_le_max h11.2 h12.2) (max_le_max h21.2 h22.2))⟩

#print axioms floorDiv_le
#print axioms ceilDiv_ge
#print axioms boxMulF_sound
#print axioms boxPowF_sound
#print axioms boxScaleF_sound
#print axioms boxOfQ_sound
#print axioms boxDivNatF_sound
#print axioms boxAbsF_sound
#print axioms boxDivF_sound
end
end CatalanCore.Li2.DecayCert.Simple
