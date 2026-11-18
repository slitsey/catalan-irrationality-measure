module
public import CatalanCore.Li2.DecayCert.Compile.DiscModel
public import CatalanCore.Linalg.PackedMatrix
/-! Generic ball arithmetic over Gaussian rationals, Kronecker-packed polynomial shifts, integer
upper bounds, and the integer model of one segment copy (`ballCopyJ`, `ballCopyJ_model`).
Shared by the bent and lattice certificates. -/
@[expose] public section
set_option Elab.async false
namespace CatalanCore.Li2.DecayCert.Seg
open CatalanCore.Li2.DecayCert Polynomial
open CatalanCore.Linalg.PackedMatrix

/-- Gaussian ball: midpoint `(re,im)` and ℓ¹ radius, all in units `1/S`. -/
abbrev CB := (ℤ×ℤ)×ℤ

def cbVal (S : ℤ) (b : CB) : CQ := ((b.1.1:ℚ)/S,(b.1.2:ℚ)/S)
/-- `b` encloses the exact Gaussian rational `x`. -/
def Encl (S : ℤ) (b : CB) (x : CQ) : Prop := cqL1 (cqSub x (cbVal S b)) ≤ (b.2:ℚ)/S

def cbZero : CB := ((0,0),0)
def cdiv (n S : ℤ) : ℤ := (n+S-1)/S
def iabs (a : ℤ) : ℤ := if a < 0 then -a else a
def cbMag (b : CB) : ℤ := iabs b.1.1+iabs b.1.2
def cbOfQ (S : ℤ) (x : CQ) : CB := ((x.1.num*S/(x.1.den:ℤ),x.2.num*S/(x.2.den:ℤ)),2)
def cbAdd (a b : CB) : CB := ((a.1.1+b.1.1,a.1.2+b.1.2),a.2+b.2)
def cbSub (a b : CB) : CB := ((a.1.1-b.1.1,a.1.2-b.1.2),a.2+b.2)
def cbMul (S : ℤ) (a b : CB) : CB :=
  (((a.1.1*b.1.1)/S-(a.1.2*b.1.2)/S,(a.1.1*b.1.2)/S+(a.1.2*b.1.1)/S),
    cdiv (cbMag a*b.2+cbMag b*a.2+a.2*b.2) S+4)
def cbScaleQ (c : ℚ) (a : CB) : CB :=
  ((c.num*a.1.1/(c.den:ℤ),c.num*a.1.2/(c.den:ℤ)),cdiv (iabs c.num*a.2) c.den+2)

/-! ### Integer division facts -/

theorem iabs_eq (a : ℤ) : iabs a=|a| := by
  unfold iabs; split_ifs with h
  · rw [abs_of_neg h]
  · rw [abs_of_nonneg (not_lt.mp h)]

theorem ediv_bounds (a d : ℤ) (hd : 0 < d) :
    ((a/d:ℤ):ℚ) ≤ (a:ℚ)/d ∧ (a:ℚ)/d < ((a/d:ℤ):ℚ)+1 := by
  have hdq : (0:ℚ) < d := by exact_mod_cast hd
  have h1 : a/d*d ≤ a := Int.ediv_mul_le a hd.ne'
  have h2 : a < (a/d+1)*d := by
    have := Int.lt_ediv_add_one_mul_self a hd; linarith
  constructor
  · rw [le_div_iff₀ hdq]; exact_mod_cast h1
  · rw [div_lt_iff₀ hdq]; exact_mod_cast h2

theorem cdiv_ge (n S : ℤ) (hS : 0 < S) : (n:ℚ)/S ≤ (cdiv n S:ℚ) := by
  have hSq : (0:ℚ) < S := by exact_mod_cast hS
  have h2 : n+S-1 < ((n+S-1)/S+1)*S := by
    have := Int.lt_ediv_add_one_mul_self (n+S-1) hS; linarith
  have h3 : n ≤ (n+S-1)/S*S := by nlinarith
  rw [div_le_iff₀ hSq]; unfold cdiv; exact_mod_cast h3

/-- Floor of `x*S` written as `num*S/den`. -/
theorem floor_scale (x : ℚ) (S : ℤ) :
    ((x.num*S/(x.den:ℤ):ℤ):ℚ) ≤ x*S ∧ x*S < ((x.num*S/(x.den:ℤ):ℤ):ℚ)+1 := by
  have hd : (0:ℤ) < (x.den:ℤ) := by exact_mod_cast x.den_pos
  have he : x*S=((x.num*S:ℤ):ℚ)/((x.den:ℤ):ℚ) := by
    rw [Int.cast_mul,Int.cast_natCast]
    nth_rewrite 1 [← Rat.num_div_den x]
    field_simp
  rw [he]; exact ediv_bounds _ _ hd

/-! ### ℓ¹ algebra on CQ -/

theorem cqL1_nonneg (a : CQ) : 0 ≤ cqL1 a := by
  unfold cqL1; positivity

theorem cqL1_add_le (a b : CQ) : cqL1 (cqAdd a b) ≤ cqL1 a+cqL1 b := by
  unfold cqL1 cqAdd
  linarith [abs_add_le a.1 b.1,abs_add_le a.2 b.2]

theorem cqL1_mul_le (a b : CQ) : cqL1 (cqMul a b) ≤ cqL1 a*cqL1 b := by
  unfold cqL1 cqMul
  have h1 : |a.1*b.1-a.2*b.2| ≤ |a.1| * |b.1|+|a.2| * |b.2| := by
    rw [← abs_mul,← abs_mul]; exact abs_sub _ _
  have h2 : |a.1*b.2+a.2*b.1| ≤ |a.1| * |b.2|+|a.2| * |b.1| := by
    rw [← abs_mul,← abs_mul]; exact abs_add_le _ _
  nlinarith [abs_nonneg a.1,abs_nonneg a.2,abs_nonneg b.1,abs_nonneg b.2]

theorem cqL1_scale (c : ℚ) (a : CQ) : cqL1 (cqScale c a)=|c| * cqL1 a := by
  unfold cqL1 cqScale; rw [abs_mul,abs_mul]; ring

theorem cqL1_val (S : ℤ) (hS : 0 < S) (b : CB) : cqL1 (cbVal S b)=(cbMag b:ℚ)/S := by
  have hSq : (0:ℚ) < S := by exact_mod_cast hS
  unfold cqL1 cbVal cbMag
  rw [abs_div,abs_div,abs_of_pos hSq,iabs_eq,iabs_eq]; push_cast; ring

theorem cqL1_le_of_encl (S : ℤ) (hS : 0 < S) (b : CB) (x : CQ) (h : Encl S b x) :
    cqL1 x ≤ ((cbMag b+b.2:ℤ):ℚ)/S := by
  have he : x=cqAdd (cqSub x (cbVal S b)) (cbVal S b) := by
    unfold cqSub cqAdd cqNeg; ext <;> simp
  have := cqL1_add_le (cqSub x (cbVal S b)) (cbVal S b)
  rw [← he,cqL1_val S hS] at this
  unfold Encl at h
  push_cast; rw [add_div]; linarith

/-! ### Enclosure lemmas -/

theorem encl_zero (S : ℤ) (hS : 0 < S) : Encl S cbZero (0,0) := by
  unfold Encl cbZero cbVal cqSub cqAdd cqNeg cqL1; simp

theorem encl_ofQ (S : ℤ) (hS : 0 < S) (x : CQ) : Encl S (cbOfQ S x) x := by
  have hSq : (0:ℚ) < S := by exact_mod_cast hS
  obtain ⟨a1,a2⟩ := floor_scale x.1 S
  obtain ⟨b1,b2⟩ := floor_scale x.2 S
  unfold Encl cbOfQ cbVal cqSub cqAdd cqNeg cqL1
  simp only
  have e1 : x.1+-(((x.1.num*S/(x.1.den:ℤ):ℤ):ℚ)/S)=(x.1*S-((x.1.num*S/(x.1.den:ℤ):ℤ):ℚ))/S := by
    field_simp; ring
  have e2 : x.2+-(((x.2.num*S/(x.2.den:ℤ):ℤ):ℚ)/S)=(x.2*S-((x.2.num*S/(x.2.den:ℤ):ℤ):ℚ))/S := by
    field_simp; ring
  rw [e1,e2,abs_div,abs_div,abs_of_pos hSq,abs_of_nonneg (by linarith),abs_of_nonneg (by linarith),
    ← add_div]
  apply div_le_div_of_nonneg_right _ hSq.le
  push_cast; linarith

theorem encl_add (S : ℤ) (a b : CB) (x y : CQ) (ha : Encl S a x) (hb : Encl S b y) :
    Encl S (cbAdd a b) (cqAdd x y) := by
  unfold Encl at *
  have he : cqSub (cqAdd x y) (cbVal S (cbAdd a b))=cqAdd (cqSub x (cbVal S a)) (cqSub y (cbVal S b)) := by
    unfold cqSub cqAdd cqNeg cbVal cbAdd; ext <;> simp <;> push_cast <;> ring
  rw [he]
  calc _ ≤ _ := cqL1_add_le _ _
    _ ≤ (a.2:ℚ)/S+(b.2:ℚ)/S := add_le_add ha hb
    _ = _ := by unfold cbAdd; push_cast; ring

theorem encl_sub (S : ℤ) (a b : CB) (x y : CQ) (ha : Encl S a x) (hb : Encl S b y) :
    Encl S (cbSub a b) (cqSub x y) := by
  unfold Encl at *
  have he : cqSub (cqSub x y) (cbVal S (cbSub a b))=cqAdd (cqSub x (cbVal S a)) (cqNeg (cqSub y (cbVal S b))) := by
    unfold cqSub cqAdd cqNeg cbVal cbSub; ext <;> simp <;> push_cast <;> ring
  have hn : ∀ v : CQ,cqL1 (cqNeg v)=cqL1 v := by intro v; unfold cqL1 cqNeg; simp
  rw [he]
  calc _ ≤ _ := cqL1_add_le _ _
    _ ≤ (a.2:ℚ)/S+(b.2:ℚ)/S := by rw [hn]; exact add_le_add ha hb
    _ = _ := by unfold cbSub; push_cast; ring

/-- Rounding error of the fixed-point complex product. -/
theorem cbMul_round (S : ℤ) (hS : 0 < S) (a b : CB) :
    cqL1 (cqSub (cqMul (cbVal S a) (cbVal S b)) (cbVal S (cbMul S a b))) ≤ 4/(S:ℚ) := by
  have hSq : (0:ℚ) < S := by exact_mod_cast hS
  have r (u v : ℤ) : |(u:ℚ)*v/S/S-((u*v/S:ℤ):ℚ)/S| ≤ 1/S := by
    obtain ⟨h1,h2⟩ := ediv_bounds (u*v) S hS
    have e : (u:ℚ)*v/S/S-((u*v/S:ℤ):ℚ)/S=(((u*v:ℤ):ℚ)/S-((u*v/S:ℤ):ℚ))/S := by push_cast; ring
    rw [e,abs_div,abs_of_pos hSq]
    apply div_le_div_of_nonneg_right _ hSq.le
    rw [abs_of_nonneg (by linarith)]; linarith
  unfold cqSub cqAdd cqNeg cqMul cbVal cbMul cqL1
  simp only
  have e1 : (a.1.1:ℚ)/S*((b.1.1:ℚ)/S)-(a.1.2:ℚ)/S*((b.1.2:ℚ)/S)+
      -(((a.1.1*b.1.1/S-a.1.2*b.1.2/S:ℤ):ℚ)/S)=
      ((a.1.1:ℚ)*b.1.1/S/S-((a.1.1*b.1.1/S:ℤ):ℚ)/S)-((a.1.2:ℚ)*b.1.2/S/S-((a.1.2*b.1.2/S:ℤ):ℚ)/S) := by
    push_cast; ring
  have e2 : (a.1.1:ℚ)/S*((b.1.2:ℚ)/S)+(a.1.2:ℚ)/S*((b.1.1:ℚ)/S)+
      -(((a.1.1*b.1.2/S+a.1.2*b.1.1/S:ℤ):ℚ)/S)=
      ((a.1.1:ℚ)*b.1.2/S/S-((a.1.1*b.1.2/S:ℤ):ℚ)/S)+((a.1.2:ℚ)*b.1.1/S/S-((a.1.2*b.1.1/S:ℤ):ℚ)/S) := by
    push_cast; ring
  rw [e1,e2]
  have := r a.1.1 b.1.1; have := r a.1.2 b.1.2; have := r a.1.1 b.1.2; have := r a.1.2 b.1.1
  have := abs_sub ((a.1.1:ℚ)*b.1.1/S/S-((a.1.1*b.1.1/S:ℤ):ℚ)/S) ((a.1.2:ℚ)*b.1.2/S/S-((a.1.2*b.1.2/S:ℤ):ℚ)/S)
  have := abs_add_le ((a.1.1:ℚ)*b.1.2/S/S-((a.1.1*b.1.2/S:ℤ):ℚ)/S) ((a.1.2:ℚ)*b.1.1/S/S-((a.1.2*b.1.1/S:ℤ):ℚ)/S)
  have h4 : (4:ℚ)/S=1/S+1/S+1/S+1/S := by ring
  linarith

theorem encl_mul (S : ℤ) (hS : 0 < S) (a b : CB) (x y : CQ) (ha : Encl S a x) (hb : Encl S b y) :
    Encl S (cbMul S a b) (cqMul x y) := by
  have hSq : (0:ℚ) < S := by exact_mod_cast hS
  set A := cbVal S a
  set B := cbVal S b
  set dx := cqSub x A
  set dy := cqSub y B
  have hx : x=cqAdd A dx := by simp only [dx,cqSub,cqAdd,cqNeg]; ext <;> simp
  have hy : y=cqAdd B dy := by simp only [dy,cqSub,cqAdd,cqNeg]; ext <;> simp
  have he : cqSub (cqMul x y) (cbVal S (cbMul S a b))=
      cqAdd (cqAdd (cqMul A dy) (cqMul dx B)) (cqAdd (cqMul dx dy)
        (cqSub (cqMul A B) (cbVal S (cbMul S a b)))) := by
    rw [hx,hy]; unfold cqSub cqAdd cqNeg cqMul; ext <;> simp <;> ring
  have hA := cqL1_val S hS a
  have hB := cqL1_val S hS b
  have hdx : cqL1 dx ≤ (a.2:ℚ)/S := ha
  have hdy : cqL1 dy ≤ (b.2:ℚ)/S := hb
  have hm1 := cqL1_mul_le A dy
  have hm2 := cqL1_mul_le dx B
  have hm3 := cqL1_mul_le dx dy
  have hr := cbMul_round S hS a b
  have t1 := cqL1_add_le (cqAdd (cqMul A dy) (cqMul dx B)) (cqAdd (cqMul dx dy) (cqSub (cqMul A B) (cbVal S (cbMul S a b))))
  have t2 := cqL1_add_le (cqMul A dy) (cqMul dx B)
  have t3 := cqL1_add_le (cqMul dx dy) (cqSub (cqMul A B) (cbVal S (cbMul S a b)))
  have hAn : 0 ≤ cqL1 A := cqL1_nonneg A
  have hBn : 0 ≤ cqL1 B := cqL1_nonneg B
  have hdxn : 0 ≤ cqL1 dx := cqL1_nonneg dx
  have hdyn : 0 ≤ cqL1 dy := cqL1_nonneg dy
  have p1 : cqL1 A*cqL1 dy ≤ cqL1 A*((b.2:ℚ)/S) := mul_le_mul_of_nonneg_left hdy hAn
  have p2 : cqL1 dx*cqL1 B ≤ ((a.2:ℚ)/S)*cqL1 B := mul_le_mul_of_nonneg_right hdx hBn
  have p3 : cqL1 dx*cqL1 dy ≤ ((a.2:ℚ)/S)*((b.2:ℚ)/S) :=
    mul_le_mul hdx hdy hdyn ((cqL1_nonneg dx).trans hdx)
  have hc := cdiv_ge (cbMag a*b.2+cbMag b*a.2+a.2*b.2) S hS
  unfold Encl; rw [he]
  have hgoal : cqL1 A*((b.2:ℚ)/S)+((a.2:ℚ)/S)*cqL1 B+((a.2:ℚ)/S)*((b.2:ℚ)/S)+4/S ≤
      ((cbMul S a b).2:ℚ)/S := by
    rw [hA,hB]
    have e : ((cbMul S a b).2:ℚ)=(cdiv (cbMag a*b.2+cbMag b*a.2+a.2*b.2) S:ℚ)+4 := by
      unfold cbMul; push_cast; ring
    rw [e,add_div]
    have : (cbMag a:ℚ)/S*((b.2:ℚ)/S)+(a.2:ℚ)/S*((cbMag b:ℚ)/S)+(a.2:ℚ)/S*((b.2:ℚ)/S)=
        (((cbMag a*b.2+cbMag b*a.2+a.2*b.2:ℤ):ℚ)/S)/S := by push_cast; field_simp
    rw [this]
    have : (((cbMag a*b.2+cbMag b*a.2+a.2*b.2:ℤ):ℚ)/S)/S ≤ (cdiv (cbMag a*b.2+cbMag b*a.2+a.2*b.2) S:ℚ)/S :=
      div_le_div_of_nonneg_right hc hSq.le
    linarith
  linarith

theorem encl_scaleQ (S : ℤ) (hS : 0 < S) (c : ℚ) (a : CB) (x : CQ) (ha : Encl S a x) :
    Encl S (cbScaleQ c a) (cqScale c x) := by
  have hSq : (0:ℚ) < S := by exact_mod_cast hS
  have hd : (0:ℤ) < (c.den:ℤ) := by exact_mod_cast c.den_pos
  have hdq : (0:ℚ) < ((c.den:ℤ):ℚ) := by exact_mod_cast hd
  have hmd : c*((c.den:ℤ):ℚ)=(c.num:ℚ) := by rw [Int.cast_natCast]; exact Rat.mul_den_eq_num c
  have r (u : ℤ) : |c*((u:ℚ)/S)-((c.num*u/(c.den:ℤ):ℤ):ℚ)/S| ≤ 1/S := by
    obtain ⟨h1,h2⟩ := ediv_bounds (c.num*u) c.den hd
    have hcu : ((c.num*u:ℤ):ℚ)/((c.den:ℤ):ℚ)=c*u := by
      rw [Int.cast_mul,← hmd]; field_simp
    have e : c*((u:ℚ)/S)-((c.num*u/(c.den:ℤ):ℤ):ℚ)/S=
        (((c.num*u:ℤ):ℚ)/((c.den:ℤ):ℚ)-((c.num*u/(c.den:ℤ):ℤ):ℚ))/S := by
      rw [hcu]; ring
    rw [e,abs_div,abs_of_pos hSq]
    apply div_le_div_of_nonneg_right _ hSq.le
    rw [abs_of_nonneg (by linarith)]; linarith
  set A := cbVal S a
  have he : cqSub (cqScale c x) (cbVal S (cbScaleQ c a))=
      cqAdd (cqScale c (cqSub x A)) (cqSub (cqScale c A) (cbVal S (cbScaleQ c a))) := by
    unfold cqSub cqAdd cqNeg cqScale; ext <;> simp <;> ring
  have hround : cqL1 (cqSub (cqScale c A) (cbVal S (cbScaleQ c a))) ≤ 2/S := by
    unfold cqSub cqAdd cqNeg cqScale cqL1 cbScaleQ
    simp only [A,cbVal]
    have := r a.1.1; have := r a.1.2
    have h2 : (2:ℚ)/S=1/S+1/S := by ring
    rw [← sub_eq_add_neg,← sub_eq_add_neg]; linarith
  have hsc : cqL1 (cqScale c (cqSub x A)) ≤ |c| * ((a.2:ℚ)/S) := by
    rw [cqL1_scale]; exact mul_le_mul_of_nonneg_left ha (abs_nonneg c)
  have hcd := cdiv_ge (iabs c.num*a.2) c.den hd
  have habs : |c|=((iabs c.num:ℤ):ℚ)/((c.den:ℤ):ℚ) := by
    rw [iabs_eq,Int.cast_abs,← hmd,abs_mul,abs_of_pos hdq]; field_simp
  unfold Encl; rw [he]
  have t := cqL1_add_le (cqScale c (cqSub x A)) (cqSub (cqScale c A) (cbVal S (cbScaleQ c a)))
  have e2 : ((cbScaleQ c a).2:ℚ)/S=(cdiv (iabs c.num*a.2) c.den:ℚ)/S+2/S := by
    unfold cbScaleQ; push_cast; ring
  rw [e2]
  have : |c| * ((a.2:ℚ)/S) ≤ (cdiv (iabs c.num*a.2) c.den:ℚ)/S := by
    rw [habs]
    have : ((iabs c.num:ℤ):ℚ)/((c.den:ℤ):ℚ)*((a.2:ℚ)/S)=(((iabs c.num*a.2:ℤ):ℚ)/((c.den:ℤ):ℚ))/S := by
      push_cast; ring
    rw [this]; exact div_le_div_of_nonneg_right (by exact_mod_cast hcd) hSq.le
  linarith

/-! ### Ball sums -/

def cbSum (xs : List CB) : CB := xs.foldl cbAdd cbZero

theorem encl_sum (S : ℤ) (hS : 0 < S) (bs : List CB) (xs : List CQ)
    (h : List.Forall₂ (Encl S) bs xs) : Encl S (cbSum bs) (cqSum xs) := by
  unfold cbSum cqSum
  have hh : ∀ (bs : List CB) (xs : List CQ),List.Forall₂ (Encl S) bs xs →
      ∀ a x,Encl S a x → Encl S (bs.foldl cbAdd a) (xs.foldl cqAdd x) := by
    intro bs xs h
    induction h with
    | nil => intro a x hx; exact hx
    | cons hb _ ih => intro a x hx; exact ih _ _ (encl_add S _ _ _ _ hx hb)
  exact hh bs xs h _ _ (encl_zero S hS)

/-! ### The y recurrence of a segment copy -/

/-- One ball step of `yPair`: inputs `B = 2ζγ`, `C = γ²`, `iA = 1/q²`. -/
def cbYStep (S : ℤ) (Bb Cb iAb : CB) (n : ℕ) (v : CB×CB) : CB×CB :=
  (v.2,cbScaleQ (-(1/((n:ℚ)+1))) (cbMul S (cbAdd (cbScaleQ ((n:ℚ)+1/2) (cbMul S Bb v.2))
    (cbScaleQ (n:ℚ) (cbMul S Cb v.1))) iAb))
def cbYPair (S : ℤ) (Bb Cb iAb y0 : CB) : ℕ → CB×CB
  | 0 => (cbZero,y0)
  | n+1 => cbYStep S Bb Cb iAb n (cbYPair S Bb Cb iAb y0 n)

theorem encl_yPair (S : ℤ) (hS : 0 < S) (ζ γ q : CQ) (Bb Cb iAb y0 : CB)
    (hB : Encl S Bb (cqScale 2 (cqMul ζ γ))) (hC : Encl S Cb (cqMul γ γ))
    (hA : Encl S iAb (cqInv (cqMul q q))) (h0 : Encl S y0 (cqInv q)) (n : ℕ) :
    Encl S (cbYPair S Bb Cb iAb y0 n).1 (yPair ζ γ q n).1 ∧
      Encl S (cbYPair S Bb Cb iAb y0 n).2 (yPair ζ γ q n).2 := by
  induction n with
  | zero => exact ⟨encl_zero S hS,h0⟩
  | succ n ih =>
    refine ⟨ih.2,?_⟩
    simp only [cbYPair,cbYStep,yPair,cqDiv]
    have hn : ((n+1:ℕ):ℚ)=(n:ℚ)+1 := by push_cast; ring
    apply encl_scaleQ S hS
    apply encl_mul S hS _ _ _ _ _ hA
    apply encl_add
    · exact encl_scaleQ S hS _ _ _ (encl_mul S hS _ _ _ _ hB ih.2)
    · exact encl_scaleQ S hS _ _ _ (encl_mul S hS _ _ _ _ hC ih.1)

/-- The list `y_0,…,y_{k-1}` in one pass. -/
def cbYAux (S : ℤ) (Bb Cb iAb : CB) : ℕ → ℕ → CB×CB → List CB
  | 0,_,_ => []
  | k+1,n,v => v.2::cbYAux S Bb Cb iAb k (n+1) (cbYStep S Bb Cb iAb n v)
def cbYList (S : ℤ) (Bb Cb iAb y0 : CB) (k : ℕ) : List CB := cbYAux S Bb Cb iAb k 0 (cbZero,y0)

theorem cbYAux_eq (S : ℤ) (Bb Cb iAb y0 : CB) (k n : ℕ) :
    cbYAux S Bb Cb iAb k n (cbYPair S Bb Cb iAb y0 n)=
      (List.range k).map (fun i => (cbYPair S Bb Cb iAb y0 (n+i)).2) := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
    rw [List.range_succ_eq_map,List.map_cons,cbYAux]
    have h1 : cbYStep S Bb Cb iAb n (cbYPair S Bb Cb iAb y0 n)=cbYPair S Bb Cb iAb y0 (n+1) := rfl
    rw [h1,ih (n+1),List.map_map]
    congr 1
    apply List.map_congr_left
    intro i _; simp only [Function.comp_apply]; congr 2; omega

theorem cbYList_eq (S : ℤ) (Bb Cb iAb y0 : CB) (k : ℕ) :
    cbYList S Bb Cb iAb y0 k=(List.range k).map (fun i => (cbYPair S Bb Cb iAb y0 i).2) := by
  have := cbYAux_eq S Bb Cb iAb y0 k 0
  simp only [zero_add] at this
  exact this

/-! ### Copy coefficients -/

def cbGet (l : List CB) (i : ℕ) : CB := l.getD i cbZero

theorem cbGet_cbYList (S : ℤ) (Bb Cb iAb y0 : CB) (k i : ℕ) :
    cbGet (cbYList S Bb Cb iAb y0 k) i=if i < k then (cbYPair S Bb Cb iAb y0 i).2 else cbZero := by
  rw [cbGet,cbYList_eq]
  split_ifs with h
  · rw [List.getD_eq_getElem _ _ (by simpa using h)]; simp
  · rw [List.getD_eq_default _ _ (by simpa using h)]

def cbConv (S : ℤ) (F Y : List CB) (n : ℕ) : CB :=
  cbSum ((List.range (n+1)).map (fun i => cbMul S (cbGet F i) (cbGet Y (n-i))))
/-- Ball form of `segCoeff` for `j = n+1`. -/
def cbSegCoeff (S : ℤ) (γb : CB) (F Q Y : List CB) (n : ℕ) : CB :=
  cbScaleQ (1/((n+1:ℕ):ℚ)) (cbMul S γb (cbSub (cbConv S F Y n) (cbGet Q n)))

theorem encl_segCoeff (S : ℤ) (hS : 0 < S) (d : QSegment) (φ e : CQ) (γb : CB)
    (F Q Y : List CB) (n : ℕ)
    (hγ : Encl S γb (cqDiv e d.half))
    (hF : ∀ i ≤ n,Encl S (cbGet F i) (qShiftCoeff d.density
      (cqScale (1/2) (cqAdd φ (cqInv φ))) (cqDiv e d.half) i))
    (hQ : Encl S (cbGet Q n) (qShiftCoeff d.quotDensity
      (cqScale (1/2) (cqAdd φ (cqInv φ))) (cqDiv e d.half) n))
    (hY : ∀ i ≤ n,Encl S (cbGet Y i) (yPair (cqScale (1/2) (cqAdd φ (cqInv φ))) (cqDiv e d.half)
      (cqScale (1/2) (cqSub φ (cqInv φ))) i).2) :
    Encl S (cbSegCoeff S γb F Q Y n) (segCoeff d φ e (n+1)) := by
  simp only [segCoeff,cbSegCoeff,Nat.add_one_ne_zero,if_false,Nat.add_sub_cancel]
  apply encl_scaleQ S hS
  apply encl_mul S hS _ _ _ _ hγ
  apply encl_sub _ _ _ _ _ _ hQ
  unfold cbConv
  apply encl_sum S hS
  rw [List.forall₂_map_left_iff,List.forall₂_map_right_iff]
  apply List.forall₂_same.mpr
  intro i hi
  have hi' : i ≤ n := Nat.lt_succ_iff.mp (List.mem_range.mp hi)
  exact encl_mul S hS _ _ _ _ (hF i hi') (hY (n-i) (Nat.sub_le n i))



abbrev GI := ℤ×ℤ
def giMul (a b : GI) : GI := (a.1*b.1-a.2*b.2,a.1*b.2+a.2*b.1)
def giAdd (a b : GI) : GI := (a.1+b.1,a.2+b.2)
noncomputable def giC (a : GI) : ℂ := (a.1:ℂ)+(a.2:ℂ)*Complex.I

theorem giC_mul (a b : GI) : giC (giMul a b)=giC a*giC b := by
  simp only [giC,giMul]; push_cast; linear_combination (-(a.2:ℂ)*b.2)*Complex.I_sq
theorem giC_add (a b : GI) : giC (giAdd a b)=giC a+giC b := by
  simp only [giC,giAdd]; push_cast; ring

/-- Exact ascending update for `(C+E*u)*p+a`. -/
def shiftStepG (C E : GI) : GI → List GI → List GI
  | a,[] => [a]
  | a,b::bs => giAdd (giMul C b) a::shiftStepG C E (giMul E b) bs
/-- Homogeneous shift of the integer polynomial with descending coefficients `ds` by `(C+E u)/den`. -/
def shiftMidG (C E : GI) (den : ℤ) (ds : List ℤ) : List GI×ℤ :=
  ds.foldl (fun st a => let d := den*st.2; (shiftStepG C E (a*d,0) st.1,d)) ([],1)

/-! ### Polynomial semantics -/

noncomputable def giPoly : List GI → ℂ[X]
  | [] => 0
  | a::l => C (giC a)+X*giPoly l
noncomputable def intPolyC : List ℤ → ℂ[X]
  | [] => 0
  | a::l => C (a:ℂ)+X*intPolyC l

theorem giPoly_coeff : ∀ (l : List GI) (j : ℕ),(giPoly l).coeff j=giC (l.getD j (0,0))
  | [],j => by simp [giPoly,giC]
  | a::l,0 => by simp [giPoly]
  | a::l,j+1 => by simp [giPoly,giPoly_coeff l j]

theorem intPolyC_coeff : ∀ (l : List ℤ) (j : ℕ),(intPolyC l).coeff j=((l.getD j 0:ℤ):ℂ)
  | [],j => by simp [intPolyC]
  | a::l,0 => by simp [intPolyC]
  | a::l,j+1 => by
    simp only [intPolyC,Polynomial.coeff_add,Polynomial.coeff_C_succ,Polynomial.coeff_X_mul,
      intPolyC_coeff l j,zero_add,List.getD_cons_succ]

theorem giPoly_step (C E : GI) : ∀ (l : List GI) (a : GI),
    giPoly (shiftStepG C E a l)=(Polynomial.C (giC C)+Polynomial.C (giC E)*X)*giPoly l+Polynomial.C (giC a)
  | [],a => by simp [shiftStepG,giPoly]
  | b::bs,a => by
    simp only [shiftStepG,giPoly,giPoly_step C E bs,giC_add,giC_mul,Polynomial.C_add,Polynomial.C_mul]
    ring

theorem shiftMidG_fold (C E : GI) (den : ℤ) (hden : den ≠ 0) (ds : List ℤ) :
    ∀ (xs : List GI) (pw : ℤ) (v : ℂ[X]),giPoly xs=Polynomial.C (pw:ℂ)*v →
      giPoly (ds.foldl (fun st a => let d := den*st.2; (shiftStepG C E (a*d,0) st.1,d)) (xs,pw)).1=
        Polynomial.C ((ds.foldl (fun st a => let d := den*st.2; (shiftStepG C E (a*d,0) st.1,d)) (xs,pw)).2:ℂ)*
        ds.foldl (fun acc (a:ℤ) => (Polynomial.C (1/(den:ℂ))*(Polynomial.C (giC C)+Polynomial.C (giC E)*X))*acc+
          Polynomial.C (a:ℂ)) v := by
  induction ds with
  | nil => intro xs pw v h; exact h
  | cons a ds ih =>
    intro xs pw v h
    simp only [List.foldl_cons]
    apply ih
    rw [giPoly_step,h]
    have hd : (den:ℂ) ≠ 0 := by exact_mod_cast hden
    have hk : Polynomial.C ((den*pw:ℤ):ℂ)*Polynomial.C (1/(den:ℂ))=Polynomial.C (pw:ℂ) := by
      rw [← Polynomial.C_mul]; congr 1; push_cast; field_simp
    have ha : giC (a*(den*pw),0)=((den*pw:ℤ):ℂ)*(a:ℂ) := by simp [giC]; push_cast; ring
    rw [ha,Polynomial.C_mul]
    linear_combination (-(Polynomial.C (giC C)+Polynomial.C (giC E)*X)*v)*hk

theorem shiftMidG_snd (C E : GI) (den : ℤ) (ds : List ℤ) :
    ∀ (xs : List GI) (pw : ℤ),
      (ds.foldl (fun st a => let d := den*st.2; (shiftStepG C E (a*d,0) st.1,d)) (xs,pw)).2=pw*den^ds.length := by
  induction ds with
  | nil => intro xs pw; simp
  | cons a ds ih => intro xs pw; simp only [List.foldl_cons,ih,List.length_cons]; ring

/-- Horner on the reversed list is composition. -/
theorem horner_reverse (y : ℂ[X]) (l : List ℤ) :
    l.reverse.foldl (fun acc (a:ℤ) => y*acc+Polynomial.C (a:ℂ)) 0=(intPolyC l).comp y := by
  rw [List.foldl_reverse]
  induction l with
  | nil => simp [intPolyC]
  | cons a l ih => simp only [List.foldr_cons,ih,intPolyC,Polynomial.add_comp,Polynomial.C_comp,
      Polynomial.mul_comp,Polynomial.X_comp]; ring

theorem shiftMidG_poly (C E : GI) (den : ℤ) (hden : den ≠ 0) (a : List ℤ) :
    giPoly (shiftMidG C E den a.reverse).1=Polynomial.C ((shiftMidG C E den a.reverse).2:ℂ)*
      (intPolyC a).comp (Polynomial.C (giC C/den)+Polynomial.C (giC E/den)*X) := by
  have h := shiftMidG_fold C E den hden a.reverse [] 1 0 (by simp [giPoly])
  have hh := horner_reverse (Polynomial.C (1/(den:ℂ))*(Polynomial.C (giC C)+Polynomial.C (giC E)*X)) a
  rw [hh] at h
  unfold shiftMidG
  rw [h]; congr 2
  rw [show (1/(den:ℂ))=(den:ℂ)⁻¹ by ring,div_eq_mul_inv,div_eq_mul_inv,Polynomial.C_mul,Polynomial.C_mul]
  ring

/-! ### Identification with `qShiftCoeff` -/

theorem qListPoly_map_div (a : List ℤ) (dd : ℤ) :
    (qListPoly (a.map (fun x : ℤ => (x:ℚ)/dd))).map (Rat.castHom ℂ)=Polynomial.C (1/(dd:ℂ))*intPolyC a := by
  ext j
  rw [Polynomial.coeff_map,qListPoly_coeff,Polynomial.coeff_C_mul,intPolyC_coeff]
  simp only [coeffQ,List.getElem?_map]
  by_cases hj : j < a.length
  · rw [List.getElem?_eq_getElem hj,List.getD_eq_getElem _ _ hj]; simp; ring
  · rw [List.getElem?_eq_none (by omega),List.getD_eq_default _ _ (by omega)]; simp

/-- The exact shift reproduces `qShiftCoeff` once the table and the centre are matched. -/
theorem shiftMidG_qShiftCoeff (C E : GI) (den dd : ℤ) (hden : den ≠ 0) (hdd : dd ≠ 0)
    (a : List ℤ) (ζ γ : CQ) (hζ : ζ=((C.1:ℚ)/den,(C.2:ℚ)/den)) (hγ : γ=((E.1:ℚ)/den,(E.2:ℚ)/den))
    (j : ℕ) :
    cqReal (qShiftCoeff (qListPoly (a.map (fun x : ℤ => (x:ℚ)/dd))) ζ γ j)=
      giC (((shiftMidG C E den a.reverse).1).getD j (0,0))/(dd*(shiftMidG C E den a.reverse).2) := by
  have hpw : ((shiftMidG C E den a.reverse).2:ℂ) ≠ 0 := by
    unfold shiftMidG; rw [shiftMidG_snd]; push_cast; exact mul_ne_zero one_ne_zero (pow_ne_zero _ (by exact_mod_cast hden))
  rw [qShiftCoeff_spec,qListPoly_map_div,Polynomial.mul_comp,Polynomial.C_comp,Polynomial.coeff_C_mul]
  have hc : cqReal ζ=giC C/den := by rw [hζ]; simp [cqReal,giC]; ring
  have he : cqReal γ=giC E/den := by rw [hγ]; simp [cqReal,giC]; ring
  rw [hc,he,← giPoly_coeff,shiftMidG_poly C E den hden a,Polynomial.coeff_C_mul]
  have hddc : (dd:ℂ) ≠ 0 := by exact_mod_cast hdd
  field_simp

/-! ### Kronecker form: one Horner pass at `u = R`, then balanced digits of both parts -/

def absI (a : ℤ) : ℤ := max a (-a)
theorem absI_eq (a : ℤ) : absI a=|a| := by simp [absI,abs_eq_max_neg]

def n1i : List ℤ → ℤ
  | [] => 0
  | a::l => absI a+n1i l
def gn1 : List GI → ℤ
  | [] => 0
  | a::l => |a.1|+|a.2|+gn1 l

def packG (R : ℤ) (l : List GI) : GI := (signedPack R (l.map Prod.fst),signedPack R (l.map Prod.snd))
def kronAccG (R : ℤ) (C E : GI) (den : ℤ) (ds : List ℤ) : GI×ℤ :=
  ds.foldl (fun st a => let d := den*st.2;
    (giAdd (giMul st.1 (giAdd C (E.1*R,E.2*R))) (a*d,0),d)) ((0,0),1)
def kronShiftG (R H : ℤ) (C E : GI) (den : ℤ) (ds : List ℤ) : List GI×ℤ :=
  let st := kronAccG R C E den ds
  (((signedUnpack R H ds.length st.1.1).1).zip ((signedUnpack R H ds.length st.1.2).1),st.2)
def kronOKG (R H : ℤ) (C E : GI) (den : ℤ) (ds : List ℤ) : Bool :=
  decide (0<R ∧ 0≤H ∧ 2*H≤R ∧
    n1i ds*(absI C.1+absI C.2+absI E.1+absI E.2+absI den+1)^ds.length<H)

theorem n1i_nonneg : ∀ l : List ℤ,0 ≤ n1i l
  | [] => le_rfl
  | a::l => by simp only [n1i,absI_eq]; linarith [abs_nonneg a,n1i_nonneg l]
theorem gn1_nonneg : ∀ l : List GI,0 ≤ gn1 l
  | [] => le_rfl
  | a::l => by simp only [gn1]; linarith [abs_nonneg a.1,abs_nonneg a.2,gn1_nonneg l]

theorem le_gn1 : ∀ (l : List GI) (x : GI),x ∈ l → |x.1|+|x.2| ≤ gn1 l
  | [],x,h => by simp at h
  | a::l,x,h => by
    simp only [gn1]
    rcases List.mem_cons.mp h with rfl | h
    · linarith [gn1_nonneg l]
    · linarith [le_gn1 l x h,abs_nonneg a.1,abs_nonneg a.2]

theorem giMul_l1 (a b : GI) : |(giMul a b).1|+|(giMul a b).2| ≤ (|a.1|+|a.2|)*(|b.1|+|b.2|) := by
  simp only [giMul]
  have h1 : |a.1*b.1-a.2*b.2| ≤ |a.1| * |b.1|+|a.2| * |b.2| := by
    rw [← abs_mul,← abs_mul]; exact abs_sub _ _
  have h2 : |a.1*b.2+a.2*b.1| ≤ |a.1| * |b.2|+|a.2| * |b.1| := by
    rw [← abs_mul,← abs_mul]; exact abs_add_le _ _
  nlinarith [abs_nonneg a.1,abs_nonneg a.2,abs_nonneg b.1,abs_nonneg b.2]

theorem packG_step (R : ℤ) (C E : GI) : ∀ (l : List GI) (a : GI),
    packG R (shiftStepG C E a l)=giAdd (giMul (giAdd C (E.1*R,E.2*R)) (packG R l)) a
  | [],a => by simp only [shiftStepG,packG,List.map,signedPack,giAdd,giMul]; ext <;> simp
  | b::bs,a => by
    have ih := packG_step R C E bs (giMul E b)
    simp only [shiftStepG,packG,List.map,signedPack] at ih ⊢
    simp only [Prod.ext_iff,giAdd,giMul] at ih ⊢
    constructor
    · rw [ih.1]; ring
    · rw [ih.2]; ring

theorem length_stepG (C E : GI) : ∀ (l : List GI) (a : GI),(shiftStepG C E a l).length=l.length+1
  | [],a => by simp [shiftStepG]
  | b::bs,a => by simp [shiftStepG,length_stepG C E bs]

theorem gn1_step (C E : GI) : ∀ (l : List GI) (a : GI),
    gn1 (shiftStepG C E a l) ≤ |a.1|+|a.2|+(|C.1|+|C.2|+(|E.1|+|E.2|))*gn1 l
  | [],a => by simp [shiftStepG,gn1]
  | b::bs,a => by
    simp only [shiftStepG,gn1]
    have h := gn1_step C E bs (giMul E b)
    have hC := giMul_l1 C b
    have hE := giMul_l1 E b
    have h1 : |(giAdd (giMul C b) a).1|+|(giAdd (giMul C b) a).2| ≤
        |(giMul C b).1|+|(giMul C b).2|+(|a.1|+|a.2|) := by
      simp only [giAdd]; linarith [abs_add_le (giMul C b).1 a.1,abs_add_le (giMul C b).2 a.2]
    nlinarith [abs_nonneg C.1,abs_nonneg C.2,abs_nonneg E.1,abs_nonneg E.2,abs_nonneg b.1,
      abs_nonneg b.2,gn1_nonneg bs]

theorem fold_invG (R : ℤ) (C E : GI) (den M : ℤ) (hM1 : 1 ≤ M) (hden : |den| ≤ M)
    (hCE : |C.1|+|C.2|+(|E.1|+|E.2|) ≤ M) :
    ∀ (ds : List ℤ) (l : List GI) (v : GI) (d A : ℤ) (k : ℕ),
      v=packG R l → |d| ≤ M^k → gn1 l ≤ A*M^k → 0 ≤ A →
      (ds.foldl (fun st a => let d := den*st.2;
          (giAdd (giMul st.1 (giAdd C (E.1*R,E.2*R))) (a*d,0),d)) (v,d)).1=
        packG R (ds.foldl (fun st a => let d := den*st.2; (shiftStepG C E (a*d,0) st.1,d)) (l,d)).1 ∧
      (ds.foldl (fun st a => let d := den*st.2;
          (giAdd (giMul st.1 (giAdd C (E.1*R,E.2*R))) (a*d,0),d)) (v,d)).2=
        (ds.foldl (fun st a => let d := den*st.2; (shiftStepG C E (a*d,0) st.1,d)) (l,d)).2 ∧
      (ds.foldl (fun st a => let d := den*st.2; (shiftStepG C E (a*d,0) st.1,d)) (l,d)).1.length=
        l.length+ds.length ∧
      gn1 (ds.foldl (fun st a => let d := den*st.2; (shiftStepG C E (a*d,0) st.1,d)) (l,d)).1 ≤
        (A+n1i ds)*M^(k+ds.length)
  | [],l,v,d,A,k,hv,hd,hl,hA => by
    simp only [List.foldl_nil,List.length_nil,add_zero,n1i]
    exact ⟨hv,trivial,trivial,hl⟩
  | a::ds,l,v,d,A,k,hv,hd,hl,hA => by
    simp only [List.foldl_cons]
    have hpk : 0 ≤ M^k := pow_nonneg (by linarith) k
    have hd' : |den*d| ≤ M^(k+1) := by
      rw [abs_mul,pow_succ]
      calc |den| * |d| ≤ M*M^k := mul_le_mul hden hd (abs_nonneg _) (by linarith)
        _ = M^k*M := by ring
    have hl' : gn1 (shiftStepG C E (a*(den*d),0) l) ≤ (A+|a|)*M^(k+1) := by
      have h := gn1_step C E l (a*(den*d),0)
      have hx : |a*(den*d)|+|(0:ℤ)| ≤ |a| * M^(k+1) := by
        rw [abs_zero,add_zero,abs_mul]; exact mul_le_mul_of_nonneg_left hd' (abs_nonneg a)
      have hy : (|C.1|+|C.2|+(|E.1|+|E.2|))*gn1 l ≤ M*(A*M^k) :=
        mul_le_mul hCE hl (gn1_nonneg l) (by linarith)
      have hz : M*(A*M^k) ≤ A*M^(k+1) := by rw [pow_succ]; nlinarith
      simp only at h hx
      nlinarith
    obtain ⟨h1,h2,h3,h4⟩ := fold_invG R C E den M hM1 hden hCE ds (shiftStepG C E (a*(den*d),0) l)
      (giAdd (giMul v (giAdd C (E.1*R,E.2*R))) (a*(den*d),0)) (den*d) (A+|a|) (k+1)
      (by rw [packG_step,hv]; simp only [giAdd,giMul]; ext <;> simp <;> ring) hd' hl'
      (by linarith [abs_nonneg a])
    refine ⟨h1,h2,?_,?_⟩
    · rw [h3,length_stepG]; simp only [List.length_cons]; omega
    · have e1 : A+|a|+n1i ds=A+n1i (a::ds) := by simp only [n1i,absI_eq]; ring
      have e2 : k+1+ds.length=k+(a::ds).length := by simp only [List.length_cons]; omega
      rw [e1,e2] at h4; exact h4

theorem unpack_pack (R H : ℤ) (hR : 0 < R) : ∀ (q : List ℤ),
    (∀ x ∈ q,DigitRange R H x) → signedUnpack R H q.length (signedPack R q)=(q,0)
  | [],_ => by simp [signedUnpack,signedPack]
  | a::q,h => by
    have ha := h a (by simp)
    have hq := unpack_pack R H hR q (fun x hx => h x (by simp [hx]))
    dsimp [DigitRange] at ha
    have hd : (a+R*signedPack R q+H)%R-H=a := by
      have : (a+R*signedPack R q+H)%R=(a+H)%R := by
        rw [show a+R*signedPack R q+H=(a+H)+R*signedPack R q by ring,Int.add_mul_emod_self_left]
      rw [this,Int.emod_eq_of_lt (by omega) (by omega)]; ring
    have hq' : (a+R*signedPack R q-a)/R=signedPack R q := by
      rw [show a+R*signedPack R q-a=R*signedPack R q by ring,Int.mul_ediv_cancel_left _ hR.ne']
    simp only [signedUnpack,signedPack,List.length_cons,hd,hq',hq]

theorem zip_fst_snd : ∀ l : List GI,(l.map Prod.fst).zip (l.map Prod.snd)=l
  | [] => rfl
  | a::l => by simp [zip_fst_snd l]

theorem kronShiftG_eq (R H : ℤ) (C E : GI) (den : ℤ) (ds : List ℤ)
    (hok : kronOKG R H C E den ds=true) : kronShiftG R H C E den ds=shiftMidG C E den ds := by
  simp only [kronOKG,decide_eq_true_eq,absI_eq] at hok
  obtain ⟨hR,hH,h2H,hA⟩ := hok
  set M := |C.1|+|C.2|+|E.1|+|E.2|+|den|+1
  have hM1 : (1:ℤ) ≤ M := by
    simp only [M]; linarith [abs_nonneg C.1,abs_nonneg C.2,abs_nonneg E.1,abs_nonneg E.2,abs_nonneg den]
  obtain ⟨h1,h2,h3,h4⟩ := fold_invG R C E den M hM1
    (by simp only [M]; linarith [abs_nonneg C.1,abs_nonneg C.2,abs_nonneg E.1,abs_nonneg E.2])
    (by simp only [M]; linarith [abs_nonneg den])
    ds [] (0,0) 1 0 0 (by simp [packG,signedPack]) (by simp) (by simp [gn1]) le_rfl
  simp only [zero_add,List.length_nil] at h3 h4
  have hn : n1i ds=n1i ds := rfl
  have hrange : ∀ x ∈ (shiftMidG C E den ds).1,DigitRange R H x.1 ∧ DigitRange R H x.2 := by
    intro x hx
    have hx' := le_gn1 _ x hx
    unfold shiftMidG at hx'
    have hb : gn1 (ds.foldl (fun st a => let d := den*st.2; (shiftStepG C E (a*d,0) st.1,d)) ([],1)).1 < H := by
      have : n1i ds*M^ds.length < H := by
        simpa only [M,absI_eq,add_assoc] using hA
      linarith
    dsimp [DigitRange]
    refine ⟨⟨?_,?_⟩,⟨?_,?_⟩⟩ <;> linarith [neg_abs_le x.1,le_abs_self x.1,neg_abs_le x.2,le_abs_self x.2,
      abs_nonneg x.1,abs_nonneg x.2]
  unfold kronShiftG kronAccG
  unfold shiftMidG at hrange ⊢
  dsimp only
  rw [h1,h2]
  have hlen : ds.length=(ds.foldl (fun st a => let d := den*st.2; (shiftStepG C E (a*d,0) st.1,d)) ([],1)).1.length := h3.symm
  set out := (ds.foldl (fun st a => let d := den*st.2; (shiftStepG C E (a*d,0) st.1,d)) ([],1)).1
  have hu1 := unpack_pack R H hR (out.map Prod.fst) (by
    intro y hy; rcases List.mem_map.mp hy with ⟨x,hx,rfl⟩; exact (hrange x hx).1)
  have hu2 := unpack_pack R H hR (out.map Prod.snd) (by
    intro y hy; rcases List.mem_map.mp hy with ⟨x,hx,rfl⟩; exact (hrange x hx).2)
  rw [List.length_map] at hu1 hu2
  simp only [packG]
  rw [hlen,hu1,hu2]
  simp only [zip_fst_snd]
  rfl



/-- Powers of two through `Nat.pow`, which the kernel evaluates natively. -/
def pow2 (n : ℕ) : ℤ := ((2^n : ℕ) : ℤ)

@[simp] theorem pow2_eq (n : ℕ) : pow2 n=2^n := by simp [pow2]

/-! ### Rounding an exact Gaussian ratio -/

def cbRound (S M : ℤ) (g : GI) : CB := ((g.1*S/M,g.2*S/M),2)

theorem encl_round (S M : ℤ) (hS : 0 < S) (hM : 0 < M) (g : GI) (x : CQ)
    (hx : x=((g.1:ℚ)/M,(g.2:ℚ)/M)) : Encl S (cbRound S M g) x := by
  have hSq : (0:ℚ) < S := by exact_mod_cast hS
  have hMq : (0:ℚ) < M := by exact_mod_cast hM
  obtain ⟨a1,a2⟩ := ediv_bounds (g.1*S) M hM
  obtain ⟨b1,b2⟩ := ediv_bounds (g.2*S) M hM
  subst hx
  unfold Encl cbRound cbVal cqSub cqAdd cqNeg cqL1
  simp only
  have e1 : (g.1:ℚ)/M+-(((g.1*S/M:ℤ):ℚ)/S)=(((g.1*S:ℤ):ℚ)/M-((g.1*S/M:ℤ):ℚ))/S := by
    push_cast; field_simp; ring
  have e2 : (g.2:ℚ)/M+-(((g.2*S/M:ℤ):ℚ)/S)=(((g.2*S:ℤ):ℚ)/M-((g.2*S/M:ℤ):ℚ))/S := by
    push_cast; field_simp; ring
  rw [e1,e2,abs_div,abs_div,abs_of_pos hSq,abs_of_nonneg (by linarith),abs_of_nonneg (by linarith),
    ← add_div]
  apply div_le_div_of_nonneg_right _ hSq.le
  push_cast at a1 a2 b1 b2 ⊢; linarith


/-- Ball list of the shifted coefficients of `(a/dd)(ζ+γu)`, `ζ=C/den`, `γ=E/den`. -/
def cbShift (S : ℤ) (L : ℕ) (C E : GI) (den dd : ℤ) (a : List ℤ) : List CB :=
  let r := if kronOKG (pow2 L) (pow2 (L-1)) C E den a.reverse then kronShiftG (pow2 L) (pow2 (L-1)) C E den a.reverse
    else shiftMidG C E den a.reverse
  r.1.map (cbRound S (dd*r.2))

theorem cbShift_eq (S : ℤ) (L : ℕ) (C E : GI) (den dd : ℤ) (a : List ℤ) :
    cbShift S L C E den dd a=(shiftMidG C E den a.reverse).1.map
      (cbRound S (dd*(shiftMidG C E den a.reverse).2)) := by
  unfold cbShift; split_ifs with h
  · rw [kronShiftG_eq _ _ _ _ _ _ h]
  · rfl

theorem encl_cbShift (S : ℤ) (hS : 0 < S) (L : ℕ) (C E : GI) (den dd : ℤ) (hden : 0 < den)
    (hdd : 0 < dd) (a : List ℤ) (ζ γ : CQ) (hζ : ζ=((C.1:ℚ)/den,(C.2:ℚ)/den))
    (hγ : γ=((E.1:ℚ)/den,(E.2:ℚ)/den)) (i : ℕ) :
    Encl S (cbGet (cbShift S L C E den dd a) i)
      (qShiftCoeff (qListPoly (a.map (fun x : ℤ => (x:ℚ)/dd))) ζ γ i) := by
  rw [cbShift_eq]
  set out := shiftMidG C E den a.reverse
  have hpw : out.2=den^a.length := by
    simp only [out,shiftMidG]; rw [shiftMidG_snd]; simp
  have hM : 0 < dd*out.2 := by rw [hpw]; positivity
  have hx := shiftMidG_qShiftCoeff C E den dd hden.ne' hdd.ne' a ζ γ hζ hγ i
  set x := qShiftCoeff (qListPoly (a.map (fun x : ℤ => (x:ℚ)/dd))) ζ γ i
  have hre := congrArg Complex.re hx
  have him := congrArg Complex.im hx
  rw [cqReal_re] at hre; rw [cqReal_im] at him
  have hMc : ((dd:ℂ)*(out.2:ℂ))=(((dd*out.2:ℤ):ℝ):ℂ) := by push_cast; ring
  rw [hMc] at hre him
  simp only [giC,Complex.div_ofReal_re,Complex.div_ofReal_im,Complex.add_re,Complex.add_im,
    Complex.mul_re,Complex.mul_im,Complex.intCast_re,Complex.intCast_im,Complex.I_re,Complex.I_im,
    mul_zero,mul_one,sub_zero,add_zero,zero_add] at hre him
  have hx' : x=(((out.1.getD i (0,0)).1:ℚ)/(dd*out.2:ℤ),((out.1.getD i (0,0)).2:ℚ)/(dd*out.2:ℤ)) := by
    ext
    · exact_mod_cast hre
    · exact_mod_cast him
  unfold cbGet
  by_cases hi : i < out.1.length
  · rw [List.getD_eq_getElem _ _ (by simpa using hi),List.getElem_map]
    rw [List.getD_eq_getElem _ _ hi] at hx'
    exact encl_round S _ hS hM _ x hx'
  · rw [List.getD_eq_default _ _ (by simpa using hi)]
    rw [List.getD_eq_default _ _ (by omega)] at hx'
    rw [hx']; simpa using encl_zero S hS

/-! ### Per-segment table, checked once -/

structure SegTable where
  dn : List ℤ
  dd : ℤ
  qn : List ℤ
  qd : ℤ

def SegTable.ok (d : QSegment) (t : SegTable) : Bool :=
  decide (0 < t.dd ∧ 0 < t.qd ∧ t.dn.map (fun x : ℤ => (x:ℚ)/t.dd)=qDensityCoeffs d ∧
    t.qn.map (fun x : ℤ => (x:ℚ)/t.qd)=qQuotDensityCoeffs d)

/-- Common integer form of two Gaussian rationals. -/
def cqCommon (ζ γ : CQ) : GI×GI×ℤ :=
  let D : ℕ := (ζ.1.den.lcm ζ.2.den).lcm (γ.1.den.lcm γ.2.den)
  ((ζ.1.num*((D/ζ.1.den:ℕ):ℤ),ζ.2.num*((D/ζ.2.den:ℕ):ℤ)),
    (γ.1.num*((D/γ.1.den:ℕ):ℤ),γ.2.num*((D/γ.2.den:ℕ):ℤ)),(D:ℤ))

def commonOK (ζ γ : CQ) (c : GI×GI×ℤ) : Bool :=
  decide (0 < c.2.2 ∧ ζ=((c.1.1:ℚ)/c.2.2,(c.1.2:ℚ)/c.2.2) ∧ γ=((c.2.1.1:ℚ)/c.2.2,(c.2.1.2:ℚ)/c.2.2))

/-! ### One segment copy -/

/-- Per-copy witness: the disc witness and the Kronecker exponent. -/
structure CopyW where
  disc : SegDiscWitness
  L : ℕ

def ballCopyCoeffs (S : ℤ) (t : SegTable) (d : QSegment) (e : CQ) (w : CopyW) : Option (List CB) :=
  let φ := w.disc.phi
  let ζ := cqScale (1/2) (cqAdd φ (cqInv φ))
  let q := cqScale (1/2) (cqSub φ (cqInv φ))
  let γ := cqDiv e d.half
  let c := cqCommon ζ γ
  if commonOK ζ γ c then
    let F := cbShift S w.L c.1 c.2.1 c.2.2 t.dd t.dn
    let Q := cbShift S w.L c.1 c.2.1 c.2.2 t.qd t.qn
    let Y := cbYList S (cbOfQ S (cqScale 2 (cqMul ζ γ))) (cbOfQ S (cqMul γ γ))
      (cbOfQ S (cqInv (cqMul q q))) (cbOfQ S (cqInv q)) w.disc.order
    some ((List.range w.disc.order).map (cbSegCoeff S (cbOfQ S γ) F Q Y))
  else none

theorem encl_ballCopyCoeffs (S : ℤ) (hS : 0 < S) (t : SegTable) (d : QSegment) (ht : t.ok d=true)
    (e : CQ) (w : CopyW) (cs : List CB) (h : ballCopyCoeffs S t d e w=some cs) :
    cs.length=w.disc.order ∧ ∀ n < w.disc.order,Encl S (cbGet cs n) (segCoeff d w.disc.phi e (n+1)) := by
  simp only [SegTable.ok,decide_eq_true_eq] at ht
  obtain ⟨hdd,hqd,hdn,hqn⟩ := ht
  unfold ballCopyCoeffs at h
  dsimp only at h
  split_ifs at h with hc
  simp only [commonOK,decide_eq_true_eq] at hc
  obtain ⟨hD,hζ,hγ⟩ := hc
  cases Option.some.inj h
  refine ⟨by simp,?_⟩
  intro n hn
  unfold cbGet
  rw [List.getD_eq_getElem _ _ (by simpa using hn),List.getElem_map,List.getElem_range]
  apply encl_segCoeff S hS
  · exact encl_ofQ S hS _
  · intro i _
    have := encl_cbShift S hS w.L _ _ _ _ hD hdd t.dn _ _ hζ hγ i
    rwa [hdn,qDensityCoeffs_spec] at this
  · have := encl_cbShift S hS w.L _ _ _ _ hD hqd t.qn _ _ hζ hγ n
    rwa [hqn,qQuotDensityCoeffs_spec] at this
  · intro i hi
    rw [cbGet_cbYList,if_pos (by omega)]
    exact (encl_yPair S hS _ _ _ _ _ _ _ (encl_ofQ S hS _) (encl_ofQ S hS _) (encl_ofQ S hS _)
      (encl_ofQ S hS _) i).2

/-! ### Perturbing a model's coefficients -/

theorem models_perturb (f : ℝ → ℝ) (g g' c : ℕ → ℝ) (n : ℕ) (r e e' : ℝ)
    (h : Models f ((List.range n).map g) r e) (hc : ∀ j < n,|g j-g' j| ≤ c j)
    (he : e+∑ j ∈ Finset.range n,c j*r^j ≤ e') : Models f ((List.range n).map g') r e' := by
  obtain ⟨hr,he0,hm⟩ := h
  have hc0 : ∀ j ∈ Finset.range n,0 ≤ c j*r^j := fun j hj =>
    mul_nonneg ((abs_nonneg _).trans (hc j (Finset.mem_range.mp hj))) (pow_nonneg hr _)
  refine ⟨hr,(add_nonneg he0 (Finset.sum_nonneg hc0)).trans he,?_⟩
  intro u hu
  have h1 := hm u hu
  rw [evalModel_range] at h1 ⊢
  have hd : |∑ j ∈ Finset.range n,g j*u^j-∑ j ∈ Finset.range n,g' j*u^j| ≤
      ∑ j ∈ Finset.range n,c j*r^j := by
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j hj => ?_)
    rw [← sub_mul,abs_mul,abs_pow]
    exact mul_le_mul (hc j (Finset.mem_range.mp hj)) (pow_le_pow_left₀ (abs_nonneg u) hu j)
      (pow_nonneg (abs_nonneg u) _) ((abs_nonneg _).trans (hc j (Finset.mem_range.mp hj)))
  calc |f u-∑ j ∈ Finset.range n,g' j*u^j|
      = |(f u-∑ j ∈ Finset.range n,g j*u^j)+(∑ j ∈ Finset.range n,g j*u^j-
          ∑ j ∈ Finset.range n,g' j*u^j)| := by congr 1; ring
    _ ≤ _ := abs_add_le _ _
    _ ≤ e+∑ j ∈ Finset.range n,c j*r^j := add_le_add h1 hd
    _ ≤ e' := he

/-! ### The ball copy as a compiled model -/

/-- Upper bound for `cqL1` of the enclosed value. -/
def cbL1Hi (S : ℤ) (b : CB) : ℚ := ((cbMag b+b.2:ℤ):ℚ)/S

def ballCopyCompile (S : ℤ) (t : SegTable) (d : QSegment) (p e : CQ) (rt : ℚ) (w : CopyW) :
    Option CompiledModel :=
  if segDiscOK d p e rt w.disc then
    match ballCopyCoeffs S t d e w with
    | none => none
    | some cs =>
      let wd := w.disc
      let ζ := cqScale (1/2) (cqAdd wd.phi (cqInv wd.phi))
      let center := cqAdd d.mid (cqMul d.half ζ)
      let δ := cqL1 (cqDiv (cqSub p center) e)
      let ρ := (rt+δ)/wd.radius
      let displacement := δ*((List.range wd.order).map (fun k : ℕ =>
        (k+1:ℚ)*cbL1Hi S (cbGet cs k)*(rt+δ)^k)).sum
      let ballErr := ((List.range wd.order).map (fun k : ℕ =>
        ((cbGet cs k).2:ℚ)/S*rt^(k+1))).sum
      some ⟨(List.range (wd.order+1)).map (fun j : ℕ =>
          if j=0 then segConstant wd.terms d wd.phi else seRat (cbVal S (cbGet cs (j-1))).1),
        seAdd (seAdd (seScale (ρ^(wd.order+1)/(1-ρ)) (segDiscMajorantExpr d wd)) (seRat displacement))
          (seRat ballErr)⟩
  else none

theorem abs_fst_le_cqL1 (x : CQ) : |x.1| ≤ cqL1 x := by
  unfold cqL1; linarith [abs_nonneg x.2]

theorem ballCopyCompile_model (S : ℤ) (hS : 0 < S) (t : SegTable) (d : QSegment) (ht : t.ok d=true)
    (p e : CQ) (rt : ℚ) (w : CopyW) (m : CompiledModel)
    (hpos : ∀ x ∈ Set.Icc (-1:ℝ) 1,0 ≤ CatalanCore.Zeta5.Potential.chebF
      (fun k => (d.c k:ℝ)) (d.coeff.length-1) x)
    (hc : ballCopyCompile S t d p e rt w=some m) :
    Models (CellExpr.segment d p e).value (m.coeff.map ScalarExpr.value) rt m.error.value := by
  have hSq : (0:ℚ) < S := by exact_mod_cast hS
  unfold ballCopyCompile at hc
  split_ifs at hc with hg
  split at hc
  · contradiction
  rename_i cs hcs
  obtain ⟨hlen,henc⟩ := encl_ballCopyCoeffs S hS t d ht e w cs hcs
  cases Option.some.inj hc
  set wd := w.disc
  set n := wd.order
  -- the exact model
  cases h0 : segDiscCompile d p e rt wd with
  | none => simp [segDiscCompile,hg] at h0
  | some m0 =>
  have hm0 := segDiscCompile_model d p e rt wd m0 hpos h0
  simp only [segDiscCompile,hg,ite_true] at h0
  cases Option.some.inj h0
  set δ := cqL1 (cqDiv (cqSub p (cqAdd d.mid (cqMul d.half (cqScale (1/2) (cqAdd wd.phi (cqInv wd.phi)))))) e)
  rw [List.map_map] at hm0 ⊢
  have hrt : (0:ℝ) ≤ rt := hm0.1
  have hδ : 0 ≤ δ := by
    simp only [δ,cqL1]; positivity
  apply models_perturb _ _ _ (fun j => (((if j=0 then 0 else ((cbGet cs (j-1)).2:ℚ)/S):ℚ):ℝ))
    (n+1) _ _ _ hm0
  · intro j hj
    rcases j with _ | k
    · simp
    · simp only [Function.comp_apply,Nat.succ_ne_zero,ite_false,seRat_value,Nat.add_sub_cancel]
      have hk := henc k (by omega)
      unfold Encl at hk
      have h3 : |(segCoeff d wd.phi e (k+1)).1-(cbVal S (cbGet cs k)).1| ≤ ((cbGet cs k).2:ℚ)/S := by
        have e3 : (segCoeff d wd.phi e (k+1)).1-(cbVal S (cbGet cs k)).1=
            (cqSub (segCoeff d wd.phi e (k+1)) (cbVal S (cbGet cs k))).1 := by
          simp only [cqSub,cqAdd,cqNeg,sub_eq_add_neg]
        rw [e3]; exact (abs_fst_le_cqL1 _).trans hk
      rw [← Rat.cast_sub,← Rat.cast_abs]
      exact Rat.cast_le.mpr h3
  · simp only [segDiscMajorantExpr,seAdd_value,seScale_value,seRat_value,list_sum_map_range]
    rw [Finset.sum_range_succ']
    simp only [Nat.succ_ne_zero,ite_false,Nat.add_sub_cancel,ite_true]
    push_cast
    have hD : ∑ k ∈ Finset.range n,((k:ℝ)+1)*((cqL1 (segCoeff d wd.phi e (k+1)):ℚ):ℝ)*((rt:ℝ)+(δ:ℝ))^k ≤
        ∑ k ∈ Finset.range n,((k:ℝ)+1)*((cbL1Hi S (cbGet cs k):ℚ):ℝ)*((rt:ℝ)+(δ:ℝ))^k := by
      apply Finset.sum_le_sum
      intro k hk
      have hk' := cqL1_le_of_encl S hS _ _ (henc k (Finset.mem_range.mp hk))
      have hk2 : cqL1 (segCoeff d wd.phi e (k+1)) ≤ cbL1Hi S (cbGet cs k) := hk'
      have : ((cqL1 (segCoeff d wd.phi e (k+1)):ℚ):ℝ) ≤ ((cbL1Hi S (cbGet cs k):ℚ):ℝ) :=
        Rat.cast_le.mpr hk2
      have hδr : (0:ℝ) ≤ (δ:ℝ) := by exact_mod_cast hδ
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this (by positivity))
        (pow_nonneg (add_nonneg hrt hδr) _)
    have hδr : (0:ℝ) ≤ (δ:ℝ) := by exact_mod_cast hδ
    have hsum : ∑ k ∈ Finset.range n,(((cbGet cs k).2:ℝ)/(S:ℝ))*(rt:ℝ)^(k+1) =
        ∑ k ∈ Finset.range n,(((cbGet cs k).2:ℝ)/(S:ℝ))*(rt:ℝ)^(k+1) := rfl
    nlinarith [mul_le_mul_of_nonneg_left hD hδr]

/-! ### Ball sum of integer multiples of powers (the constant's ψ-sum) -/

def cbOne (S : ℤ) : CB := ((S,0),0)
def cbScaleI (m : ℤ) (a : CB) : CB := ((m*a.1.1,m*a.1.2),iabs m*a.2)

theorem encl_one (S : ℤ) (hS : 0 < S) : Encl S (cbOne S) (1,0) := by
  have hSq : (S:ℚ) ≠ 0 := by exact_mod_cast hS.ne'
  unfold Encl cbOne cbVal cqSub cqAdd cqNeg cqL1
  simp [hSq]

theorem encl_scaleI (S : ℤ) (m : ℤ) (a : CB) (x : CQ) (ha : Encl S a x) :
    Encl S (cbScaleI m a) (cqScale (m:ℚ) x) := by
  unfold Encl at ha ⊢
  have he : cqSub (cqScale (m:ℚ) x) (cbVal S (cbScaleI m a))=cqScale (m:ℚ) (cqSub x (cbVal S a)) := by
    unfold cqSub cqAdd cqNeg cqScale cbVal cbScaleI
    refine Prod.ext ?_ ?_ <;> simp only <;> push_cast <;> ring
  rw [he,cqL1_scale]
  unfold cbScaleI
  simp only
  rw [iabs_eq]
  push_cast
  rw [mul_div_assoc]
  exact mul_le_mul_of_nonneg_left ha (abs_nonneg _)

def cbDotAux (S : ℤ) (z : CB) : List ℤ → CB → CB → CB
  | [],_,s => s
  | m::ms,p,s => let q := cbMul S z p; cbDotAux S z ms q (cbAdd s (cbScaleI m q))

def cqDotAux (x : CQ) : List ℤ → CQ → CQ → CQ
  | [],_,s => s
  | m::ms,p,s => cqDotAux x ms (cqMul x p) (cqAdd s (cqScale (m:ℚ) (cqMul x p)))

theorem encl_dotAux (S : ℤ) (hS : 0 < S) (z : CB) (x : CQ) (hz : Encl S z x) :
    ∀ (pc : List ℤ) (p : CB) (y : CQ) (s : CB) (t : CQ),Encl S p y → Encl S s t →
      Encl S (cbDotAux S z pc p s) (cqDotAux x pc y t)
  | [],_,_,_,_,_,hs => hs
  | m::ms,p,y,s,t,hp,hs => by
    simp only [cbDotAux,cqDotAux]
    have hq := encl_mul S hS z p x y hz hp
    exact encl_dotAux S hS z x hz ms _ _ _ _ hq (encl_add S _ _ _ _ hs (encl_scaleI S m _ _ hq))

theorem cqDotAux_real (x : CQ) : ∀ (pc : List ℤ) (p s : CQ),
    cqReal (cqDotAux x pc p s)=cqReal s+
      ∑ k ∈ Finset.range pc.length,((pc.getD k 0:ℤ):ℂ)*cqReal x^(k+1)*cqReal p
  | [],p,s => by simp [cqDotAux]
  | m::ms,p,s => by
    simp only [cqDotAux]
    rw [cqDotAux_real x ms,cqReal_add,cqReal_scale,cqReal_mul,List.length_cons,Finset.sum_range_succ']
    simp only [List.getD_cons_succ,List.getD_cons_zero,pow_one]
    have hs : ∑ k ∈ Finset.range ms.length,((ms.getD k 0:ℤ):ℂ)*cqReal x^(k+1)*(cqReal x*cqReal p)=
        ∑ k ∈ Finset.range ms.length,((ms.getD k 0:ℤ):ℂ)*cqReal x^(k+1+1)*cqReal p :=
      Finset.sum_congr rfl (fun k _ => by ring)
    rw [hs]; push_cast; ring

theorem polysum_eq (d : QSegment) (φ : CQ) (pc : List ℤ) (pd : ℤ) (hpd : 0 < pd)
    (h : pc.map (fun x : ℤ => (x:ℚ)/pd)=(List.range (d.coeff.length-1)).map
      (fun k : ℕ => d.c (k+1)/(k+1:ℚ))) :
    ((((List.range (d.coeff.length-1)).map (fun k : ℕ =>
        d.c (k+1)*(cqPow (cqInv φ) (k+1)).1/(k+1:ℚ))).sum:ℚ):ℝ)=
      (cqReal (cqDotAux (cqInv φ) pc (1,0) (0,0))).re/pd := by
  have hl : pc.length=d.coeff.length-1 := by simpa using congrArg List.length h
  have hk : ∀ k < d.coeff.length-1,((pc.getD k 0:ℤ):ℚ)/pd=d.c (k+1)/(k+1:ℚ) := by
    intro k hk
    have h2 := congrArg (fun l : List ℚ => l.getD k 0) h
    rw [List.getD_eq_getElem _ _ (by simpa [hl] using hk),List.getElem_map,
      List.getD_eq_getElem _ _ (by simpa using hk),List.getElem_map,List.getElem_range] at h2
    rw [List.getD_eq_getElem _ _ (by rw [hl]; exact hk)]
    exact h2
  rw [cqDotAux_real,list_sum_map_range]
  have h0 : cqReal ((0,0):CQ)=0 := by simp [cqReal]
  have h1 : cqReal ((1,0):CQ)=1 := by simp [cqReal]
  rw [h0,h1,zero_add,Complex.re_sum,hl,Finset.sum_div]
  push_cast
  apply Finset.sum_congr rfl
  intro k hkr
  have hkk := hk k (Finset.mem_range.mp hkr)
  have hpdr : (pd:ℝ) ≠ 0 := by exact_mod_cast hpd.ne'
  have hq : ((d.c (k+1)/(k+1:ℚ):ℚ):ℝ)=(((pc.getD k 0:ℤ):ℚ)/pd:ℚ) := by rw [hkk]
  push_cast at hq
  rw [← cqReal_pow,mul_one]
  simp only [Complex.mul_re,Complex.intCast_re,Complex.intCast_im,zero_mul,sub_zero,cqReal_re]
  rw [div_eq_mul_inv ((d.c (k+1):ℝ)*_),mul_assoc,mul_comm (((cqPow (cqInv φ) (k+1)).1:ℚ):ℝ),← mul_assoc,
    ← div_eq_mul_inv,hq]
  ring

/-! ### Per-segment shared record, checked once -/

structure SegShared where
  tab : SegTable
  terms : ℕ
  phiHi : ℚ
  fraction : ℚ
  mcHi : ℚ
  kLo : ℚ
  kHi : ℚ
  pc : List ℤ
  pd : ℤ

/-- The majorant depends only on the segment and three witness fields. -/
def mcExpr (d : QSegment) (sh : SegShared) : SE :=
  segDiscMajorantExpr d ⟨(0,0),0,sh.terms,0,0,0,0,sh.phiHi,sh.fraction⟩

/-- The part of the constant that does not depend on the copy. -/
def kExpr (d : QSegment) (terms : ℕ) : SE :=
  seScale (d.c 0) (seSub (seLogNorm terms d.half) (.log terms 2))

def SegShared.ok (d : QSegment) (sh : SegShared) : Bool :=
  sh.tab.ok d && decide (0 < sh.pd ∧ sh.pc.map (fun x : ℤ => (x:ℚ)/sh.pd)=
      (List.range (d.coeff.length-1)).map (fun k : ℕ => d.c (k+1)/(k+1:ℚ))) &&
    (match (mcExpr d sh).check with | some b => decide (b.2 ≤ sh.mcHi) | none => false) &&
    (match (kExpr d sh.terms).check with | some b => decide (sh.kLo ≤ b.1 ∧ b.2 ≤ sh.kHi) | none => false)

theorem segShared_spec (d : QSegment) (sh : SegShared) (h : sh.ok d=true) :
    sh.tab.ok d=true ∧ 0 < sh.pd ∧ sh.pc.map (fun x : ℤ => (x:ℚ)/sh.pd)=
      (List.range (d.coeff.length-1)).map (fun k : ℕ => d.c (k+1)/(k+1:ℚ)) ∧
    (mcExpr d sh).value ≤ sh.mcHi ∧
    (sh.kLo:ℝ) ≤ (kExpr d sh.terms).value ∧ (kExpr d sh.terms).value ≤ sh.kHi := by
  unfold SegShared.ok at h
  simp only [Bool.and_eq_true,decide_eq_true_eq] at h
  obtain ⟨⟨⟨ht,hpd,hpc⟩,hm⟩,hk⟩ := h
  refine ⟨ht,hpd,hpc,?_,?_⟩
  · split at hm
    · rename_i b hb
      have := (scalarCheck_sound _ b hb).2
      simp only [decide_eq_true_eq] at hm
      exact this.trans (by exact_mod_cast hm)
    · contradiction
  · split at hk
    · rename_i b hb
      have := scalarCheck_sound _ b hb
      simp only [decide_eq_true_eq] at hk
      exact ⟨(by exact_mod_cast hk.1 : (sh.kLo:ℝ) ≤ b.1).trans this.1,
        this.2.trans (by exact_mod_cast hk.2)⟩
    · contradiction

/-! ### One copy as a rational model -/

def ballCopyQ (S : ℤ) (sh : SegShared) (d : QSegment) (p e : CQ) (rt : ℚ) (w : CopyW) :
    Option CompiledModel :=
  let wd := w.disc
  if segDiscOK d p e rt wd && wd.terms == sh.terms && wd.phiHi == sh.phiHi &&
      wd.fraction == sh.fraction then
    match ballCopyCoeffs S sh.tab d e w,(seScale (d.c 0) (seLogNorm wd.terms wd.phi)).check with
    | some cs,some lb =>
      let ψb := cbDotAux S (cbOfQ S (cqInv wd.phi)) sh.pc (cbOne S) cbZero
      let pm := (ψb.1.1:ℚ)/(S*sh.pd)
      let pr := (ψb.2:ℚ)/(S*sh.pd)
      let lo := sh.kLo+lb.1-(pm+pr)
      let hi := sh.kHi+lb.2-(pm-pr)
      let ζ := cqScale (1/2) (cqAdd wd.phi (cqInv wd.phi))
      let center := cqAdd d.mid (cqMul d.half ζ)
      let δ := cqL1 (cqDiv (cqSub p center) e)
      let ρ := (rt+δ)/wd.radius
      let displacement := δ*((List.range wd.order).map (fun k : ℕ =>
        (k+1:ℚ)*cbL1Hi S (cbGet cs k)*(rt+δ)^k)).sum
      let ballErr := ((List.range wd.order).map (fun k : ℕ =>
        ((cbGet cs k).2:ℚ)/S*rt^(k+1))).sum
      some ⟨(List.range (wd.order+1)).map (fun j : ℕ =>
          if j=0 then seRat ((lo+hi)/2) else seRat (cbVal S (cbGet cs (j-1))).1),
        seRat (ρ^(wd.order+1)/(1-ρ)*sh.mcHi+displacement+ballErr+(hi-lo)/2)⟩
    | _,_ => none
  else none

theorem segConstant_split (terms : ℕ) (d : QSegment) (φ : CQ) :
    (segConstant terms d φ).value=(kExpr d terms).value+(seScale (d.c 0) (seLogNorm terms φ)).value-
      ((((List.range (d.coeff.length-1)).map (fun k : ℕ =>
        d.c (k+1)*(cqPow (cqInv φ) (k+1)).1/(k+1:ℚ))).sum:ℚ):ℝ) := by
  simp only [segConstant,kExpr,seSub_value,seAdd_value,seScale_value,seRat_value]
  ring

theorem ballCopyQ_model (S : ℤ) (hS : 0 < S) (sh : SegShared) (d : QSegment) (hsh : sh.ok d=true)
    (p e : CQ) (rt : ℚ) (w : CopyW) (m : CompiledModel)
    (hpos : ∀ x ∈ Set.Icc (-1:ℝ) 1,0 ≤ CatalanCore.Zeta5.Potential.chebF
      (fun k => (d.c k:ℝ)) (d.coeff.length-1) x)
    (hc : ballCopyQ S sh d p e rt w=some m) :
    Models (CellExpr.segment d p e).value (m.coeff.map ScalarExpr.value) rt m.error.value := by
  have hSq : (0:ℚ) < S := by exact_mod_cast hS
  obtain ⟨ht,hpd,hpc,hmc,hk1,hk2⟩ := segShared_spec d sh hsh
  unfold ballCopyQ at hc
  dsimp only at hc
  split_ifs at hc with hg
  simp only [Bool.and_eq_true,beq_iff_eq] at hg
  obtain ⟨⟨⟨hg,hterms⟩,hphiHi⟩,hfrac⟩ := hg
  split at hc
  rotate_left
  · contradiction
  rename_i cs lb hcs hlb
  obtain ⟨hlen,henc⟩ := encl_ballCopyCoeffs S hS sh.tab d ht e w cs hcs
  cases Option.some.inj hc
  set wd := w.disc
  set n := wd.order
  -- the ψ-sum enclosure
  set ψb := cbDotAux S (cbOfQ S (cqInv wd.phi)) sh.pc (cbOne S) cbZero
  have hψ := encl_dotAux S hS _ _ (encl_ofQ S hS (cqInv wd.phi)) sh.pc _ _ _ _ (encl_one S hS)
    (encl_zero S hS)
  have hψ1 := (abs_fst_le_cqL1 _).trans hψ
  have hpoly := polysum_eq d wd.phi sh.pc sh.pd hpd hpc
  have hsplit := segConstant_split wd.terms d wd.phi
  set PS := (((List.range (d.coeff.length-1)).map (fun k : ℕ =>
        d.c (k+1)*(cqPow (cqInv wd.phi) (k+1)).1/(k+1:ℚ))).sum:ℚ)
  set X := cqDotAux (cqInv wd.phi) sh.pc (1,0) (0,0)
  have hpsq : PS=X.1/sh.pd := by
    have := hpoly; rw [cqReal_re] at this; exact_mod_cast this
  have hpdq : (0:ℚ) < sh.pd := by exact_mod_cast hpd
  have hPS : |PS-(ψb.1.1:ℚ)/(S*sh.pd)| ≤ (ψb.2:ℚ)/(S*sh.pd) := by
    have e1 : PS-(ψb.1.1:ℚ)/(S*sh.pd)=(cqSub X (cbVal S ψb)).1/sh.pd := by
      rw [hpsq]; simp only [cqSub,cqAdd,cqNeg,cbVal]; field_simp; ring
    rw [e1,abs_div,abs_of_pos hpdq,div_le_div_iff₀ hpdq (by positivity)]
    have := mul_le_mul_of_nonneg_right hψ1 hpdq.le
    rw [div_mul_eq_mul_div] at this
    calc |(cqSub X (cbVal S ψb)).1| * (S*sh.pd) = (|(cqSub X (cbVal S ψb)).1| * sh.pd)*S := by ring
      _ ≤ ((ψb.2:ℚ)*sh.pd/S)*S := mul_le_mul_of_nonneg_right this hSq.le
      _ = (ψb.2:ℚ)*sh.pd := by field_simp
  have hL := scalarCheck_sound _ lb hlb
  -- the exact model
  set δ := cqL1 (cqDiv (cqSub p (cqAdd d.mid (cqMul d.half (cqScale (1/2) (cqAdd wd.phi (cqInv wd.phi)))))) e)
  cases h0 : segDiscCompile d p e rt wd with
  | none => simp [segDiscCompile,hg] at h0
  | some m0 =>
  have hm0 := segDiscCompile_model d p e rt wd m0 hpos h0
  have hshape : m0.coeff=(List.range (wd.order+1)).map (fun j : ℕ =>
        if j=0 then segConstant wd.terms d wd.phi else seRat (segCoeff d wd.phi e j).1) ∧
      m0.error=seAdd (seScale (((rt+δ)/wd.radius)^(wd.order+1)/(1-(rt+δ)/wd.radius))
        (segDiscMajorantExpr d wd)) (seRat (δ*((List.range wd.order).map (fun k : ℕ =>
          (k+1:ℚ)*cqL1 (segCoeff d wd.phi e (k+1))*(rt+δ)^k)).sum)) := by
    simp only [segDiscCompile,hg,ite_true] at h0
    cases Option.some.inj h0
    exact ⟨rfl,rfl⟩
  rw [hshape.1,hshape.2] at hm0
  rw [List.map_map] at hm0 ⊢
  have hrt : (0:ℝ) ≤ rt := hm0.1
  have hδ : 0 ≤ δ := by simp only [δ,cqL1]; positivity
  have hδr : (0:ℝ) ≤ (δ:ℝ) := by exact_mod_cast hδ
  -- the gate gives 0 ≤ ρ < 1
  have hgate := of_decide_eq_true hg
  obtain ⟨-,-,-,-,-,-,-,-,-,hR,-,-,-,-,hdr,-⟩ := hgate
  have hRr : (0:ℝ) < wd.radius := by exact_mod_cast hR
  have hρ0 : (0:ℝ) ≤ ((rt:ℝ)+δ)/wd.radius := div_nonneg (add_nonneg hrt hδr) hRr.le
  have hρ1 : ((rt:ℝ)+δ)/wd.radius < 1 := by
    rw [div_lt_one hRr]; exact_mod_cast hdr
  set lo := sh.kLo+lb.1-((ψb.1.1:ℚ)/(S*sh.pd)+(ψb.2:ℚ)/(S*sh.pd))
  set hi := sh.kHi+lb.2-((ψb.1.1:ℚ)/(S*sh.pd)-(ψb.2:ℚ)/(S*sh.pd))
  have hconst : (lo:ℝ) ≤ (segConstant wd.terms d wd.phi).value ∧
      (segConstant wd.terms d wd.phi).value ≤ hi := by
    rw [hsplit]
    rw [← hterms] at hk1 hk2
    have h1 := abs_le.mp hPS
    have h1r : ((PS-(ψb.1.1:ℚ)/(S*sh.pd):ℚ):ℝ) ≤ (((ψb.2:ℚ)/(S*sh.pd):ℚ):ℝ) := by exact_mod_cast h1.2
    have h2r' : (((-((ψb.2:ℚ)/(S*sh.pd))):ℚ):ℝ) ≤ ((PS-(ψb.1.1:ℚ)/(S*sh.pd):ℚ):ℝ) := by
      exact_mod_cast h1.1
    simp only [lo,hi]
    push_cast at h1r h2r' ⊢
    constructor <;> linarith [hL.1,hL.2]
  apply models_perturb _ _ _
    (fun j => (((if j=0 then (hi-lo)/2 else ((cbGet cs (j-1)).2:ℚ)/S):ℚ):ℝ)) (n+1) _ _ _ hm0
  · intro j hj
    rcases j with _ | k
    · simp only [Function.comp_apply,ite_true,seRat_value]
      rw [abs_le]
      push_cast
      constructor <;> linarith [hconst.1,hconst.2]
    · simp only [Function.comp_apply,Nat.succ_ne_zero,ite_false,seRat_value,Nat.add_sub_cancel]
      have hk := henc k (by omega)
      unfold Encl at hk
      have h3 : |(segCoeff d wd.phi e (k+1)).1-(cbVal S (cbGet cs k)).1| ≤ ((cbGet cs k).2:ℚ)/S := by
        have e3 : (segCoeff d wd.phi e (k+1)).1-(cbVal S (cbGet cs k)).1=
            (cqSub (segCoeff d wd.phi e (k+1)) (cbVal S (cbGet cs k))).1 := by
          simp only [cqSub,cqAdd,cqNeg,sub_eq_add_neg]
        rw [e3]; exact (abs_fst_le_cqL1 _).trans hk
      rw [← Rat.cast_sub,← Rat.cast_abs]
      exact Rat.cast_le.mpr h3
  · simp only [seAdd_value,seScale_value,seRat_value,list_sum_map_range]
    rw [Finset.sum_range_succ']
    simp only [Nat.succ_ne_zero,ite_false,Nat.add_sub_cancel,ite_true]
    have hmc' : (segDiscMajorantExpr d wd).value ≤ sh.mcHi := by
      have : segDiscMajorantExpr d wd=mcExpr d sh := by
        unfold mcExpr segDiscMajorantExpr; rw [hterms,hphiHi,hfrac]
      rw [this]; exact hmc
    have hD : ∑ k ∈ Finset.range n,((k:ℝ)+1)*((cqL1 (segCoeff d wd.phi e (k+1)):ℚ):ℝ)*((rt:ℝ)+(δ:ℝ))^k ≤
        ∑ k ∈ Finset.range n,((k:ℝ)+1)*((cbL1Hi S (cbGet cs k):ℚ):ℝ)*((rt:ℝ)+(δ:ℝ))^k := by
      apply Finset.sum_le_sum
      intro k hk
      have hk' := cqL1_le_of_encl S hS _ _ (henc k (Finset.mem_range.mp hk))
      have hk2 : cqL1 (segCoeff d wd.phi e (k+1)) ≤ cbL1Hi S (cbGet cs k) := hk'
      have : ((cqL1 (segCoeff d wd.phi e (k+1)):ℚ):ℝ) ≤ ((cbL1Hi S (cbGet cs k):ℚ):ℝ) :=
        Rat.cast_le.mpr hk2
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this (by positivity))
        (pow_nonneg (add_nonneg hrt hδr) _)
    have hfac : (0:ℝ) ≤ (((rt:ℝ)+δ)/wd.radius)^(n+1)/(1-((rt:ℝ)+δ)/wd.radius) :=
      div_nonneg (pow_nonneg hρ0 _) (by linarith)
    have hM := mul_le_mul_of_nonneg_left hmc' hfac
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left hD hδr]

/-! ### Exact Gaussian fractions over the integers -/

/-- `((x₁,x₂),D)` stands for `(x₁+x₂ i)/D`. -/
abbrev GF := GI×ℤ

def gfQ (x : GF) : CQ := ((x.1.1:ℚ)/x.2,(x.1.2:ℚ)/x.2)
def gfMul (x y : GF) : GF := (giMul x.1 y.1,x.2*y.2)
def gfAdd (x y : GF) : GF := ((x.1.1*y.2+y.1.1*x.2,x.1.2*y.2+y.1.2*x.2),x.2*y.2)
def gfSub (x y : GF) : GF := ((x.1.1*y.2-y.1.1*x.2,x.1.2*y.2-y.1.2*x.2),x.2*y.2)
def gfInv (x : GF) : GF := ((x.2*x.1.1,-(x.2*x.1.2)),x.1.1^2+x.1.2^2)
def gfScaleN (c : ℤ) (x : GF) : GF := ((c*x.1.1,c*x.1.2),x.2)
def gfHalf (x : GF) : GF := (x.1,2*x.2)

theorem gfQ_mul (x y : GF) : gfQ (gfMul x y)=cqMul (gfQ x) (gfQ y) := by
  unfold gfQ gfMul cqMul giMul
  refine Prod.ext ?_ ?_ <;> simp only <;> push_cast <;> ring

theorem gfQ_add (x y : GF) (hx : x.2 ≠ 0) (hy : y.2 ≠ 0) : gfQ (gfAdd x y)=cqAdd (gfQ x) (gfQ y) := by
  have hx' : (x.2:ℚ) ≠ 0 := by exact_mod_cast hx
  have hy' : (y.2:ℚ) ≠ 0 := by exact_mod_cast hy
  unfold gfQ gfAdd cqAdd
  refine Prod.ext ?_ ?_ <;> simp only <;> push_cast <;> field_simp <;> ring

theorem gfQ_sub (x y : GF) (hx : x.2 ≠ 0) (hy : y.2 ≠ 0) : gfQ (gfSub x y)=cqSub (gfQ x) (gfQ y) := by
  have hx' : (x.2:ℚ) ≠ 0 := by exact_mod_cast hx
  have hy' : (y.2:ℚ) ≠ 0 := by exact_mod_cast hy
  unfold gfQ gfSub cqSub cqAdd cqNeg
  refine Prod.ext ?_ ?_ <;> simp only <;> push_cast <;> field_simp <;> ring

theorem gfQ_inv (x : GF) (hx : x.2 ≠ 0) : gfQ (gfInv x)=cqInv (gfQ x) := by
  have hx' : (x.2:ℚ) ≠ 0 := by exact_mod_cast hx
  unfold gfQ gfInv cqInv cqSq
  by_cases hz : (x.1.1:ℚ)^2+(x.1.2:ℚ)^2=0
  · have h1 : (x.1.1:ℚ)=0 := by nlinarith [sq_nonneg (x.1.1:ℚ),sq_nonneg (x.1.2:ℚ)]
    have h2 : (x.1.2:ℚ)=0 := by nlinarith [sq_nonneg (x.1.1:ℚ),sq_nonneg (x.1.2:ℚ)]
    refine Prod.ext ?_ ?_ <;> simp only <;> push_cast <;> simp [h1,h2]
  · have hz' : ((x.1.1:ℚ)/x.2)^2+((x.1.2:ℚ)/x.2)^2 ≠ 0 := by
      rw [div_pow,div_pow,← add_div]; exact div_ne_zero hz (pow_ne_zero _ hx')
    refine Prod.ext ?_ ?_ <;> simp only <;> push_cast <;> field_simp <;> ring

theorem gfQ_half (x : GF) : gfQ (gfHalf x)=cqScale (1/2) (gfQ x) := by
  unfold gfQ gfHalf cqScale
  refine Prod.ext ?_ ?_ <;> simp only <;> push_cast <;> ring

theorem gfQ_scaleN (c : ℤ) (x : GF) : gfQ (gfScaleN c x)=cqScale (c:ℚ) (gfQ x) := by
  unfold gfQ gfScaleN cqScale
  refine Prod.ext ?_ ?_ <;> simp only <;> push_cast <;> ring

theorem gfQ_rebase (x : GF) (c : ℤ) (hc : c ≠ 0) :
    gfQ ((x.1.1*c,x.1.2*c),x.2*c)=gfQ x := by
  have hc' : (c:ℚ) ≠ 0 := by exact_mod_cast hc
  unfold gfQ
  refine Prod.ext ?_ ?_ <;> simp only <;> push_cast <;> rw [mul_div_mul_right _ _ hc']

theorem cqDiv_mul_cancel (h g : CQ) (hh : cqSq h ≠ 0) : cqDiv (cqMul h g) h=g := by
  unfold cqDiv cqMul cqInv cqSq at *
  refine Prod.ext ?_ ?_ <;> simp only <;> field_simp <;> ring

/-- Ball of an exact Gaussian fraction with positive denominator. -/
def cbOfGF (S : ℤ) (x : GF) : CB := cbRound S x.2 x.1

theorem encl_ofGF (S : ℤ) (hS : 0 < S) (x : GF) (hx : 0 < x.2) : Encl S (cbOfGF S x) (gfQ x) :=
  encl_round S x.2 hS hx x.1 _ rfl

/-! ### Exact Horner sums `Σ c_k z^(k+1)` -/

def gHorner (z : GF) : List ℤ → GF
  | [] => ((0,0),1)
  | c::cs => gfMul z (gfAdd ((c,0),1) (gHorner z cs))

def cqHorner (x : CQ) : List ℤ → CQ
  | [] => (0,0)
  | c::cs => cqMul x (cqAdd ((c:ℚ),0) (cqHorner x cs))

theorem cqDotAux_horner (x : CQ) : ∀ (pc : List ℤ) (p s : CQ),
    cqDotAux x pc p s=cqAdd s (cqMul p (cqHorner x pc))
  | [],p,s => by
    simp only [cqDotAux,cqHorner,cqAdd,cqMul]; refine Prod.ext ?_ ?_ <;> simp
  | m::ms,p,s => by
    rw [cqDotAux,cqDotAux_horner x ms,cqHorner]
    unfold cqAdd cqMul cqScale
    refine Prod.ext ?_ ?_ <;> simp only <;> ring

theorem gHorner_den (z : GF) (hz : 0 < z.2) : ∀ pc : List ℤ,0 < (gHorner z pc).2
  | [] => by simp [gHorner]
  | c::cs => by
    simp only [gHorner,gfMul,gfAdd]
    have := gHorner_den z hz cs
    positivity

theorem gfQ_gHorner (z : GF) (hz : 0 < z.2) : ∀ pc : List ℤ,gfQ (gHorner z pc)=cqHorner (gfQ z) pc
  | [] => by simp [gHorner,cqHorner,gfQ]
  | c::cs => by
    rw [gHorner,cqHorner,gfQ_mul,gfQ_add _ _ one_ne_zero (gHorner_den z hz cs).ne',gfQ_gHorner z hz cs]
    congr 2
    simp [gfQ]

/-! ### Integer front end of one copy -/

/-- φ = (a+bi)/2^k and γ = (g₁+g₂i)/2^m. -/
structure IFront where
  a : ℤ
  b : ℤ
  k : ℕ
  g1 : ℤ
  g2 : ℤ
  m : ℕ

def IFront.phiF (f : IFront) : GF := ((f.a,f.b),pow2 f.k)
def IFront.gamF (f : IFront) : GF := ((f.g1,f.g2),pow2 f.m)
def IFront.psiF (f : IFront) : GF := gfInv f.phiF
def IFront.zetaF (f : IFront) : GF := gfHalf (gfAdd f.phiF f.psiF)
def IFront.qF (f : IFront) : GF := gfHalf (gfSub f.phiF f.psiF)

/-- Positivity of every denominator used, checked per copy. -/
def IFront.ok (f : IFront) : Bool :=
  decide (0 < f.psiF.2 ∧ 0 < (gfInv f.qF).2 ∧ 0 < (gfInv (gfMul f.qF f.qF)).2)

def ballCopyCoeffsI (S : ℤ) (t : SegTable) (f : IFront) (order L : ℕ) : List CB :=
  let ζ := f.zetaF
  let γ := f.gamF
  let q := f.qF
  let C : GI := (ζ.1.1*γ.2,ζ.1.2*γ.2)
  let E : GI := (γ.1.1*ζ.2,γ.1.2*ζ.2)
  let D := ζ.2*γ.2
  let F := cbShift S L C E D t.dd t.dn
  let Q := cbShift S L C E D t.qd t.qn
  let Y := cbYList S (cbOfGF S (gfScaleN 2 (gfMul ζ γ))) (cbOfGF S (gfMul γ γ))
    (cbOfGF S (gfInv (gfMul q q))) (cbOfGF S (gfInv q)) order
  (List.range order).map (cbSegCoeff S (cbOfGF S γ) F Q Y)

theorem encl_ballCopyCoeffsI (S : ℤ) (hS : 0 < S) (t : SegTable) (d : QSegment) (ht : t.ok d=true)
    (hh : cqSq d.half ≠ 0) (f : IFront) (hf : f.ok=true) (e : CQ) (he : e=cqMul d.half (gfQ f.gamF))
    (order L : ℕ) (n : ℕ) (hn : n < order) :
    Encl S (cbGet (ballCopyCoeffsI S t f order L) n) (segCoeff d (gfQ f.phiF) e (n+1)) := by
  simp only [SegTable.ok,decide_eq_true_eq] at ht
  obtain ⟨hdd,hqd,hdn,hqn⟩ := ht
  simp only [IFront.ok,decide_eq_true_eq] at hf
  obtain ⟨hψ0,hy0,hiA0⟩ := hf
  have hk : (0:ℤ) < 2^f.k := by positivity
  have hm : (0:ℤ) < 2^f.m := by positivity
  have hφ0 : f.phiF.2 ≠ 0 := by simp only [IFront.phiF,pow2_eq]; positivity
  have hψ0' : f.psiF.2 ≠ 0 := hψ0.ne'
  have hγ0 : 0 < f.gamF.2 := by simp only [IFront.gamF,pow2_eq]; positivity
  have hζ0 : 0 < f.zetaF.2 := by
    simp only [IFront.zetaF,gfHalf,gfAdd,IFront.phiF,pow2_eq]; simp only [IFront.psiF] at hψ0; positivity
  have hq0 : 0 < f.qF.2 := by
    simp only [IFront.qF,gfHalf,gfSub,IFront.phiF,pow2_eq]; simp only [IFront.psiF] at hψ0; positivity
  -- the rational quantities
  have hψ : gfQ f.psiF=cqInv (gfQ f.phiF) := gfQ_inv _ hφ0
  have hζ : gfQ f.zetaF=cqScale (1/2) (cqAdd (gfQ f.phiF) (cqInv (gfQ f.phiF))) := by
    rw [IFront.zetaF,gfQ_half,gfQ_add _ _ hφ0 hψ0',hψ]
  have hq : gfQ f.qF=cqScale (1/2) (cqSub (gfQ f.phiF) (cqInv (gfQ f.phiF))) := by
    rw [IFront.qF,gfQ_half,gfQ_sub _ _ hφ0 hψ0',hψ]
  have hγ : cqDiv e d.half=gfQ f.gamF := by rw [he]; exact cqDiv_mul_cancel _ _ hh
  have hC : (cqScale (1/2) (cqAdd (gfQ f.phiF) (cqInv (gfQ f.phiF))))=
      ((((f.zetaF.1.1*f.gamF.2:ℤ):ℚ)/(f.zetaF.2*f.gamF.2:ℤ)),(((f.zetaF.1.2*f.gamF.2:ℤ):ℚ)/(f.zetaF.2*f.gamF.2:ℤ))) := by
    rw [← hζ,← gfQ_rebase f.zetaF f.gamF.2 hγ0.ne']; rfl
  have hE : cqDiv e d.half=
      ((((f.gamF.1.1*f.zetaF.2:ℤ):ℚ)/(f.zetaF.2*f.gamF.2:ℤ)),(((f.gamF.1.2*f.zetaF.2:ℤ):ℚ)/(f.zetaF.2*f.gamF.2:ℤ))) := by
    rw [hγ,← gfQ_rebase f.gamF f.zetaF.2 hζ0.ne',mul_comm f.gamF.2]; rfl
  have hD : 0 < f.zetaF.2*f.gamF.2 := mul_pos hζ0 hγ0
  unfold ballCopyCoeffsI cbGet
  rw [List.getD_eq_getElem _ _ (by simpa using hn),List.getElem_map,List.getElem_range]
  apply encl_segCoeff S hS
  · rw [hγ]; exact encl_ofGF S hS _ hγ0
  · intro i _
    have := encl_cbShift S hS L (f.zetaF.1.1*f.gamF.2,f.zetaF.1.2*f.gamF.2)
      (f.gamF.1.1*f.zetaF.2,f.gamF.1.2*f.zetaF.2) _ _ hD hdd t.dn _ _ hC hE i
    rwa [hdn,qDensityCoeffs_spec] at this
  · have := encl_cbShift S hS L (f.zetaF.1.1*f.gamF.2,f.zetaF.1.2*f.gamF.2)
      (f.gamF.1.1*f.zetaF.2,f.gamF.1.2*f.zetaF.2) _ _ hD hqd t.qn _ _ hC hE n
    rwa [hqn,qQuotDensityCoeffs_spec] at this
  · intro i hi
    rw [cbGet_cbYList,if_pos (by omega)]
    have hqq : 0 < (gfMul f.qF f.qF).2 := by simp only [gfMul]; positivity
    refine (encl_yPair S hS _ _ _ _ _ _ _ ?_ ?_ ?_ ?_ i).2
    · rw [hγ,← hζ,← gfQ_mul]
      have := encl_ofGF S hS (gfScaleN 2 (gfMul f.zetaF f.gamF)) (by simp only [gfScaleN,gfMul]; positivity)
      rwa [gfQ_scaleN,Int.cast_ofNat] at this
    · rw [hγ,← gfQ_mul]
      exact encl_ofGF S hS _ (by simp only [gfMul]; positivity)
    · rw [← hq,← gfQ_mul,← gfQ_inv _ hqq.ne']
      exact encl_ofGF S hS _ hiA0
    · rw [← hq,← gfQ_inv _ hq0.ne']
      exact encl_ofGF S hS _ hy0

/-! ### Assembling a copy model from checked pieces -/

/-- The rational model of one copy from ball coefficients `cs`, a constant interval `[lo,hi]`,
an upper bound `δ` for the centre displacement and a majorant bound `mcHi`. -/
def assemble (S : ℤ) (cs : List CB) (lo hi δ rt : ℚ) (wd : SegDiscWitness) (mcHi : ℚ) : CompiledModel :=
  let ρ := (rt+δ)/wd.radius
  let displacement := δ*((List.range wd.order).map (fun k : ℕ =>
    (k+1:ℚ)*cbL1Hi S (cbGet cs k)*(rt+δ)^k)).sum
  let ballErr := ((List.range wd.order).map (fun k : ℕ => ((cbGet cs k).2:ℚ)/S*rt^(k+1))).sum
  ⟨(List.range (wd.order+1)).map (fun j : ℕ =>
      if j=0 then seRat ((lo+hi)/2) else seRat (cbVal S (cbGet cs (j-1))).1),
    seRat (ρ^(wd.order+1)/(1-ρ)*mcHi+displacement+ballErr+(hi-lo)/2)⟩

theorem assemble_model (S : ℤ) (hS : 0 < S) (d : QSegment) (p e : CQ) (rt : ℚ) (wd : SegDiscWitness)
    (cs : List CB) (lo hi δ mcHi : ℚ)
    (hpos : ∀ x ∈ Set.Icc (-1:ℝ) 1,0 ≤ CatalanCore.Zeta5.Potential.chebF
      (fun k => (d.c k:ℝ)) (d.coeff.length-1) x)
    (hg : segDiscOK d p e rt wd=true)
    (henc : ∀ n < wd.order,Encl S (cbGet cs n) (segCoeff d wd.phi e (n+1)))
    (hlo : (lo:ℝ) ≤ (segConstant wd.terms d wd.phi).value)
    (hhi : (segConstant wd.terms d wd.phi).value ≤ hi)
    (hδ : cqL1 (cqDiv (cqSub p (cqAdd d.mid (cqMul d.half
      (cqScale (1/2) (cqAdd wd.phi (cqInv wd.phi)))))) e) ≤ δ)
    (hδR : rt+δ < wd.radius)
    (hmc : (segDiscMajorantExpr d wd).value ≤ mcHi) :
    Models (CellExpr.segment d p e).value ((assemble S cs lo hi δ rt wd mcHi).coeff.map ScalarExpr.value)
      rt (assemble S cs lo hi δ rt wd mcHi).error.value := by
  have hSq : (0:ℚ) < S := by exact_mod_cast hS
  set n := wd.order
  set δe := cqL1 (cqDiv (cqSub p (cqAdd d.mid (cqMul d.half (cqScale (1/2) (cqAdd wd.phi (cqInv wd.phi)))))) e)
  cases h0 : segDiscCompile d p e rt wd with
  | none => simp [segDiscCompile,hg] at h0
  | some m0 =>
  have hm0 := segDiscCompile_model d p e rt wd m0 hpos h0
  have hshape : m0.coeff=(List.range (wd.order+1)).map (fun j : ℕ =>
        if j=0 then segConstant wd.terms d wd.phi else seRat (segCoeff d wd.phi e j).1) ∧
      m0.error=seAdd (seScale (((rt+δe)/wd.radius)^(wd.order+1)/(1-(rt+δe)/wd.radius))
        (segDiscMajorantExpr d wd)) (seRat (δe*((List.range wd.order).map (fun k : ℕ =>
          (k+1:ℚ)*cqL1 (segCoeff d wd.phi e (k+1))*(rt+δe)^k)).sum)) := by
    simp only [segDiscCompile,hg,ite_true] at h0
    cases Option.some.inj h0
    exact ⟨rfl,rfl⟩
  rw [hshape.1,hshape.2] at hm0
  unfold assemble
  rw [List.map_map] at hm0 ⊢
  have hrt : (0:ℝ) ≤ rt := hm0.1
  have hδe : 0 ≤ δe := by simp only [δe,cqL1]; positivity
  have hδer : (0:ℝ) ≤ (δe:ℝ) := by exact_mod_cast hδe
  have hδr : (δe:ℝ) ≤ (δ:ℝ) := by exact_mod_cast hδ
  have hgate := of_decide_eq_true hg
  obtain ⟨-,-,-,-,-,-,-,-,-,hR,hf0,hf1,-,-,-,hH1,-⟩ := hgate
  have hRr : (0:ℝ) < wd.radius := by exact_mod_cast hR
  have hδRr : (rt:ℝ)+δ < wd.radius := by exact_mod_cast hδR
  have hρ0 : (0:ℝ) ≤ ((rt:ℝ)+δe)/wd.radius := div_nonneg (add_nonneg hrt hδer) hRr.le
  have hρ1 : ((rt:ℝ)+δ)/wd.radius < 1 := by rw [div_lt_one hRr]; exact hδRr
  have hρle : ((rt:ℝ)+δe)/wd.radius ≤ ((rt:ℝ)+δ)/wd.radius :=
    div_le_div_of_nonneg_right (by linarith) hRr.le
  apply models_perturb _ _ _
    (fun j => (((if j=0 then (hi-lo)/2 else ((cbGet cs (j-1)).2:ℚ)/S):ℚ):ℝ)) (n+1) _ _ _ hm0
  · intro j hj
    rcases j with _ | k
    · simp only [Function.comp_apply,ite_true,seRat_value]
      rw [abs_le]
      push_cast
      constructor <;> linarith
    · simp only [Function.comp_apply,Nat.succ_ne_zero,ite_false,seRat_value,Nat.add_sub_cancel]
      have hk := henc k (by omega)
      unfold Encl at hk
      have h3 : |(segCoeff d wd.phi e (k+1)).1-(cbVal S (cbGet cs k)).1| ≤ ((cbGet cs k).2:ℚ)/S := by
        have e3 : (segCoeff d wd.phi e (k+1)).1-(cbVal S (cbGet cs k)).1=
            (cqSub (segCoeff d wd.phi e (k+1)) (cbVal S (cbGet cs k))).1 := by
          simp only [cqSub,cqAdd,cqNeg,sub_eq_add_neg]
        rw [e3]; exact (abs_fst_le_cqL1 _).trans hk
      rw [← Rat.cast_sub,← Rat.cast_abs]
      exact Rat.cast_le.mpr h3
  · simp only [seAdd_value,seScale_value,seRat_value,list_sum_map_range]
    rw [Finset.sum_range_succ']
    simp only [Nat.succ_ne_zero,ite_false,Nat.add_sub_cancel,ite_true]
    have hD : ∑ k ∈ Finset.range n,((k:ℝ)+1)*((cqL1 (segCoeff d wd.phi e (k+1)):ℚ):ℝ)*((rt:ℝ)+(δe:ℝ))^k ≤
        ∑ k ∈ Finset.range n,((k:ℝ)+1)*((cbL1Hi S (cbGet cs k):ℚ):ℝ)*((rt:ℝ)+(δ:ℝ))^k := by
      apply Finset.sum_le_sum
      intro k hk
      have hk' := cqL1_le_of_encl S hS _ _ (henc k (Finset.mem_range.mp hk))
      have hk2 : cqL1 (segCoeff d wd.phi e (k+1)) ≤ cbL1Hi S (cbGet cs k) := hk'
      have h4 : ((cqL1 (segCoeff d wd.phi e (k+1)):ℚ):ℝ) ≤ ((cbL1Hi S (cbGet cs k):ℚ):ℝ) :=
        Rat.cast_le.mpr hk2
      have h5 : (0:ℝ) ≤ ((cqL1 (segCoeff d wd.phi e (k+1)):ℚ):ℝ) := by
        exact_mod_cast cqL1_nonneg _
      have h6 : ((rt:ℝ)+δe)^k ≤ ((rt:ℝ)+δ)^k := pow_le_pow_left₀ (add_nonneg hrt hδer) (by linarith) k
      apply mul_le_mul (mul_le_mul_of_nonneg_left h4 (by positivity)) h6 (by positivity)
        (mul_nonneg (by positivity) (h5.trans h4))
    have hDs : (0:ℝ) ≤ ∑ k ∈ Finset.range n,((k:ℝ)+1)*((cqL1 (segCoeff d wd.phi e (k+1)):ℚ):ℝ)*((rt:ℝ)+(δe:ℝ))^k := by
      apply Finset.sum_nonneg; intro k _
      have h5 : (0:ℝ) ≤ ((cqL1 (segCoeff d wd.phi e (k+1)):ℚ):ℝ) := by exact_mod_cast cqL1_nonneg _
      positivity
    have hdisp := mul_le_mul hδr hD hDs (hδer.trans hδr)
    have hM0 : (0:ℝ) ≤ (segDiscMajorantExpr d wd).value := by
      rw [segDiscMajorantExpr_value]
      have hH : (1:ℝ) ≤ wd.phiHi := by exact_mod_cast hH1
      have hf1r : (wd.fraction:ℝ) < 1 := by exact_mod_cast hf1
      have hf0r : (0:ℝ) < wd.fraction := by exact_mod_cast hf0
      have l1 := Real.log_nonneg hH
      have l2 : Real.log (1-(wd.fraction:ℝ)) ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
      have l3 := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2)
      have := Real.pi_pos
      apply add_nonneg
      · apply mul_nonneg (abs_nonneg _); linarith
      · apply Finset.sum_nonneg; intro k _; positivity
    have hfac1 : (((rt:ℝ)+δe)/wd.radius)^(n+1)/(1-((rt:ℝ)+δe)/wd.radius) ≤
        (((rt:ℝ)+δ)/wd.radius)^(n+1)/(1-((rt:ℝ)+δ)/wd.radius) := by
      apply div_le_div₀ (pow_nonneg (hρ0.trans hρle) _) (pow_le_pow_left₀ hρ0 hρle _) (by linarith)
        (by linarith)
    have hfac0 : (0:ℝ) ≤ (((rt:ℝ)+δe)/wd.radius)^(n+1)/(1-((rt:ℝ)+δe)/wd.radius) :=
      div_nonneg (pow_nonneg hρ0 _) (by linarith)
    have hM := mul_le_mul hfac1 hmc hM0 (hfac0.trans hfac1)
    push_cast
    nlinarith

/-! ### Integer gate implying `segDiscOK` -/

def gfOfCQ (x : CQ) : GF := ((x.1.num*(x.2.den:ℤ),x.2.num*(x.1.den:ℤ)),(x.1.den:ℤ)*(x.2.den:ℤ))

theorem gfOfCQ_den (x : CQ) : 0 < (gfOfCQ x).2 := by
  unfold gfOfCQ; simp only; have := x.1.den_pos; have := x.2.den_pos; positivity

theorem gfQ_ofCQ (x : CQ) : gfQ (gfOfCQ x)=x := by
  have h1 : ((x.1.den:ℤ):ℚ) ≠ 0 := by exact_mod_cast x.1.den_pos.ne'
  have h2 : ((x.2.den:ℤ):ℚ) ≠ 0 := by exact_mod_cast x.2.den_pos.ne'
  unfold gfQ gfOfCQ
  refine Prod.ext ?_ ?_ <;> simp only <;> push_cast
  · rw [mul_div_mul_right _ _ (by exact_mod_cast x.2.den_pos.ne'),Rat.num_div_den]
  · rw [mul_comm ((x.1.den:ℚ)),mul_div_mul_right _ _ (by exact_mod_cast x.1.den_pos.ne'),Rat.num_div_den]

/-- Integer slit distance numerator: `slitDistSq (X/D) = sdI X D / D²` for `D > 0`. -/
def sdI (X : GI) (D : ℤ) : ℤ :=
  if X.1 < -D then (X.1+D)^2+X.2^2 else if D < X.1 then (X.1-D)^2+X.2^2 else X.2^2

theorem slitDistSq_gf (x : GF) (hD : 0 < x.2) : slitDistSq (gfQ x)=(sdI x.1 x.2:ℚ)/(x.2:ℚ)^2 := by
  have hDq : (0:ℚ) < x.2 := by exact_mod_cast hD
  unfold slitDistSq sdI gfQ
  simp only
  have c1 : ((x.1.1:ℚ)/x.2 < -1) ↔ x.1.1 < -x.2 := by
    rw [div_lt_iff₀ hDq,neg_one_mul]; constructor <;> intro h <;> exact_mod_cast h
  have c2 : (1 < (x.1.1:ℚ)/x.2) ↔ x.2 < x.1.1 := by
    rw [lt_div_iff₀ hDq,one_mul]; constructor <;> intro h <;> exact_mod_cast h
  by_cases h1 : x.1.1 < -x.2
  · rw [if_pos (c1.mpr h1),if_pos h1]; push_cast; field_simp
  · rw [if_neg (fun h => h1 (c1.mp h)),if_neg h1]
    by_cases h2 : x.2 < x.1.1
    · rw [if_pos (c2.mpr h2),if_pos h2]; push_cast; field_simp
    · rw [if_neg (fun h => h2 (c2.mp h)),if_neg h2]; push_cast; field_simp

theorem cqSq_gf (x : GF) (hD : x.2 ≠ 0) : cqSq (gfQ x)=((x.1.1^2+x.1.2^2:ℤ):ℚ)/(x.2:ℚ)^2 := by
  have hDq : (x.2:ℚ) ≠ 0 := by exact_mod_cast hD
  unfold cqSq gfQ; simp only; push_cast; field_simp

theorem cqL1_gf (x : GF) (hD : 0 < x.2) : cqL1 (gfQ x)=((|x.1.1|+|x.1.2|:ℤ):ℚ)/(x.2:ℚ) := by
  have hDq : (0:ℚ) < x.2 := by exact_mod_cast hD
  unfold cqL1 gfQ; simp only; push_cast
  rw [abs_div,abs_div,abs_of_pos hDq,add_div]

/-- `q²·n ≤ m` style comparison for a rational bound `r = r.num/r.den`: `X ≤ r² D²`. -/
def leSqI (X : ℤ) (r : ℚ) (D : ℤ) : Bool := decide (X*(r.den:ℤ)^2 ≤ r.num^2*D^2)

theorem leSqI_spec (X : ℤ) (r : ℚ) (D : ℤ) (hD : D ≠ 0) (h : leSqI X r D=true) :
    (X:ℚ)/(D:ℚ)^2 ≤ r^2 := by
  unfold leSqI at h
  have h' : (X:ℚ)*((r.den:ℤ):ℚ)^2 ≤ (r.num:ℚ)^2*(D:ℚ)^2 := by exact_mod_cast of_decide_eq_true h
  have hD' : (D:ℚ) ≠ 0 := by exact_mod_cast hD
  have hDq : (0:ℚ) < (D:ℚ)^2 := by positivity
  have hd : (0:ℚ) < ((r.den:ℤ):ℚ)^2 := by have := r.den_pos; positivity
  rw [div_le_iff₀ hDq]
  have hr : r=(r.num:ℚ)/((r.den:ℤ):ℚ) := by push_cast; exact (Rat.num_div_den r).symm
  rw [hr,div_pow]
  rw [div_mul_eq_mul_div,le_div_iff₀ hd]
  linarith

/-- The same with the inequality reversed: `r² D² ≤ X`. -/
def geSqI (X : ℤ) (r : ℚ) (D : ℤ) : Bool := decide (r.num^2*D^2 ≤ X*(r.den:ℤ)^2)

theorem geSqI_spec (X : ℤ) (r : ℚ) (D : ℤ) (hD : D ≠ 0) (h : geSqI X r D=true) :
    r^2 ≤ (X:ℚ)/(D:ℚ)^2 := by
  unfold geSqI at h
  have h' : (r.num:ℚ)^2*(D:ℚ)^2 ≤ (X:ℚ)*((r.den:ℤ):ℚ)^2 := by exact_mod_cast of_decide_eq_true h
  have hD' : (D:ℚ) ≠ 0 := by exact_mod_cast hD
  have hDq : (0:ℚ) < (D:ℚ)^2 := by positivity
  have hd : (0:ℚ) < ((r.den:ℤ):ℚ)^2 := by have := r.den_pos; positivity
  rw [le_div_iff₀ hDq]
  have hr : r=(r.num:ℚ)/((r.den:ℤ):ℚ) := by push_cast; exact (Rat.num_div_den r).symm
  rw [hr,div_pow,div_mul_eq_mul_div,div_le_iff₀ hd]
  linarith

/-- Displacement of the cell point from the expansion centre, as an exact Gaussian fraction. -/
def deltaF (d : QSegment) (p : CQ) (f : IFront) : GF :=
  gfMul (gfSub (gfOfCQ p) (gfAdd (gfOfCQ d.mid) (gfMul (gfOfCQ d.half) f.zetaF)))
    (gfInv (gfMul (gfOfCQ d.half) f.gamF))

/-- The integer gate. `wd.phi` is required to be `gfQ f.phiF`; `dHi` bounds the displacement. -/
def gateI (d : QSegment) (p e : CQ) (rt : ℚ) (wd : SegDiscWitness) (f : IFront) (dHi : ℚ) : Bool :=
  let ζ := f.zetaF
  let δ := deltaF d p f
  decide (cqSq d.half ≠ 0 ∧ e=cqMul d.half (gfQ f.gamF) ∧ f.g1^2+f.g2^2 ≠ 0 ∧ 0 < ζ.2 ∧ 0 < δ.2 ∧
    pow2 (2*f.k) < f.a^2+f.b^2 ∧
    0 < wd.distanceLo) && geSqI (sdI ζ.1 ζ.2) wd.distanceLo ζ.2 &&
  decide (0 ≤ wd.gammaHi) && leSqI (f.g1^2+f.g2^2) wd.gammaHi (pow2 f.m) &&
  decide (0 ≤ wd.zetaHi) && leSqI (ζ.1.1^2+ζ.1.2^2) wd.zetaHi ζ.2 &&
  decide (0 < wd.radius ∧ 0 < wd.fraction ∧ wd.fraction < 1 ∧
    wd.gammaHi*wd.radius ≤ wd.fraction*wd.distanceLo ∧
    0 ≤ rt ∧ rt+dHi < wd.radius ∧
    1 ≤ wd.phiHi ∧ wd.zetaHi+wd.gammaHi*wd.radius ≤ wd.phiHi ∧
    (wd.zetaHi+wd.gammaHi*wd.radius)^2+1 ≤ (wd.phiHi-(wd.zetaHi+wd.gammaHi*wd.radius))^2 ∧
    (|δ.1.1|+|δ.1.2|)*(dHi.den:ℤ) ≤ dHi.num*δ.2)

theorem gateI_spec (d : QSegment) (p e : CQ) (rt : ℚ) (wd : SegDiscWitness) (f : IFront) (dHi : ℚ)
    (hphi : wd.phi=gfQ f.phiF) (hf : f.ok=true) (h : gateI d p e rt wd f dHi=true) :
    segDiscOK d p e rt wd=true ∧
    cqL1 (cqDiv (cqSub p (cqAdd d.mid (cqMul d.half (cqScale (1/2) (cqAdd wd.phi (cqInv wd.phi))))))
      e) ≤ dHi ∧ e=cqMul d.half (gfQ f.gamF) ∧ cqSq d.half ≠ 0 ∧ rt+dHi < wd.radius := by
  unfold gateI at h
  simp only [Bool.and_eq_true,decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hh,he,hg,hζ0,hδ0,hφ,hd0⟩,hdsq⟩,hg0⟩,hgsq⟩,hz0⟩,hzsq⟩,
    hR,hf0,hf1,hgR,hrt,hdr,hH1,hZH,hHsq,hδ⟩ := h
  simp only [IFront.ok,decide_eq_true_eq] at hf
  obtain ⟨hψ0,-,-⟩ := hf
  have hk : (0:ℤ) < 2^f.k := by positivity
  have hm : (0:ℤ) < 2^f.m := by positivity
  have hφ0 : f.phiF.2 ≠ 0 := by simp only [IFront.phiF,pow2_eq]; positivity
  have hψ : gfQ f.psiF=cqInv (gfQ f.phiF) := gfQ_inv _ hφ0
  have hζ : gfQ f.zetaF=cqScale (1/2) (cqAdd wd.phi (cqInv wd.phi)) := by
    rw [hphi,IFront.zetaF,gfQ_half,gfQ_add _ _ hφ0 hψ0.ne',hψ]
  have hγ : cqDiv e d.half=gfQ f.gamF := by rw [he]; exact cqDiv_mul_cancel _ _ hh
  -- displacement
  have hhalf0 := gfOfCQ_den d.half
  have hδq : cqDiv (cqSub p (cqAdd d.mid (cqMul d.half (cqScale (1/2) (cqAdd wd.phi (cqInv wd.phi)))))) e=
      gfQ (deltaF d p f) := by
    have hmid0 := gfOfCQ_den d.mid
    have hp0 := gfOfCQ_den p
    have hhz : (gfMul (gfOfCQ d.half) f.zetaF).2 ≠ 0 := by simp only [gfMul]; positivity
    have hc0 : (gfAdd (gfOfCQ d.mid) (gfMul (gfOfCQ d.half) f.zetaF)).2 ≠ 0 := by
      simp only [gfAdd,gfMul]; positivity
    have he0 : (gfMul (gfOfCQ d.half) f.gamF).2 ≠ 0 := by simp only [gfMul,IFront.gamF,pow2_eq]; positivity
    unfold deltaF cqDiv
    rw [gfQ_mul,gfQ_inv _ he0,gfQ_sub _ _ hp0.ne' hc0,gfQ_add _ _ hmid0.ne' hhz,gfQ_mul,gfQ_mul,
      gfQ_ofCQ,gfQ_ofCQ,gfQ_ofCQ,hζ,he]
  have hδle : cqL1 (cqDiv (cqSub p (cqAdd d.mid (cqMul d.half (cqScale (1/2) (cqAdd wd.phi (cqInv wd.phi))))))
      e) ≤ dHi := by
    rw [hδq,cqL1_gf _ hδ0]
    have hDq : (0:ℚ) < (deltaF d p f).2 := by exact_mod_cast hδ0
    have hdd : (0:ℚ) < ((dHi.den:ℤ):ℚ) := by have := dHi.den_pos; positivity
    rw [div_le_iff₀ hDq]
    have h' : (((|(deltaF d p f).1.1|+|(deltaF d p f).1.2|:ℤ)):ℚ)*((dHi.den:ℤ):ℚ) ≤
        (dHi.num:ℚ)*(deltaF d p f).2 := by exact_mod_cast hδ
    calc _ ≤ (dHi.num:ℚ)*(deltaF d p f).2/((dHi.den:ℤ):ℚ) := by rw [le_div_iff₀ hdd]; exact h'
      _ = _ := by push_cast; rw [mul_div_right_comm,Rat.num_div_den]
  refine ⟨?_,hδle,he,hh,hdr⟩
  unfold segDiscOK
  simp only [decide_eq_true_eq]
  have he2 : cqSq e ≠ 0 := by
    intro h0
    have hgq : cqSq (gfQ f.gamF)=0 := by
      have : cqSq (cqDiv e d.half)=0 := by
        unfold cqDiv cqInv cqMul cqSq at *; simp only at *
        have h1 : e.1=0 := by nlinarith [sq_nonneg e.1,sq_nonneg e.2]
        have h2 : e.2=0 := by nlinarith [sq_nonneg e.1,sq_nonneg e.2]
        simp [h1,h2]
      rwa [hγ] at this
    rw [cqSq_gf _ (by simp only [IFront.gamF,pow2_eq]; positivity)] at hgq
    have hm2 : ((2^f.m:ℤ):ℚ) ≠ 0 := by positivity
    simp only [IFront.gamF,pow2_eq] at hgq
    rw [div_eq_zero_iff] at hgq
    rcases hgq with hgq | hgq
    · exact hg (by exact_mod_cast hgq)
    · exact hm2 (pow_eq_zero_iff (by norm_num) |>.mp hgq)
  have hφs : 1 < cqSq wd.phi := by
    rw [hphi,cqSq_gf _ hφ0]
    simp only [IFront.phiF,pow2_eq]
    have hkq : (0:ℚ) < ((2^f.k:ℤ):ℚ)^2 := by positivity
    rw [lt_div_iff₀ hkq,one_mul]
    rw [pow2_eq] at hφ
    have : ((2^(2*f.k):ℤ):ℚ) < ((f.a^2+f.b^2:ℤ):ℚ) := by exact_mod_cast hφ
    calc ((2^f.k:ℤ):ℚ)^2=((2^(2*f.k):ℤ):ℚ) := by push_cast; rw [← pow_mul,mul_comm]
      _ < _ := this
  refine ⟨hh,he2,hφs,hd0,?_,hg0,?_,hz0,?_,hR,hf0,hf1,hgR,hrt,?_,hH1,hZH,hHsq⟩
  · rw [← hζ,slitDistSq_gf _ hζ0]; exact geSqI_spec _ _ _ hζ0.ne' hdsq
  · rw [hγ,cqSq_gf _ (by simp only [IFront.gamF,pow2_eq]; positivity)]
    simp only [IFront.gamF,pow2_eq]
    exact leSqI_spec _ _ _ (by positivity) hgsq
  · rw [← hζ,cqSq_gf _ hζ0.ne']; exact leSqI_spec _ _ _ hζ0.ne' hzsq
  · linarith

/-! ### One copy, integer front end -/

structure CopyI where
  f : IFront
  disc : SegDiscWitness
  L : ℕ
  dHi : ℚ

/-- The disc witness with its expansion point taken from the integer front end. -/
def CopyI.wd (w : CopyI) : SegDiscWitness := {w.disc with phi := gfQ w.f.phiF}

def ballCopyI (S : ℤ) (sh : SegShared) (d : QSegment) (p e : CQ) (rt : ℚ) (w : CopyI) :
    Option CompiledModel :=
  let wd := w.wd
  if w.f.ok && gateI d p e rt wd w.f w.dHi && wd.terms == sh.terms && wd.phiHi == sh.phiHi &&
      wd.fraction == sh.fraction then
    match (ScalarExpr.log wd.terms (cqSq wd.phi)).check with
    | some lb =>
      let cs := ballCopyCoeffsI S sh.tab w.f wd.order w.L
      let ψb := cbOfGF S (gHorner w.f.psiF sh.pc)
      let pm := (ψb.1.1:ℚ)/(S*sh.pd)
      let pr := (ψb.2:ℚ)/(S*sh.pd)
      let c0 := d.c 0
      let ll := if 0 ≤ c0 then c0*lb.1/2 else c0*lb.2/2
      let lh := if 0 ≤ c0 then c0*lb.2/2 else c0*lb.1/2
      some (assemble S cs (sh.kLo+ll-(pm+pr)) (sh.kHi+lh-(pm-pr)) w.dHi rt wd sh.mcHi)
    | none => none
  else none

theorem ballCopyI_model (S : ℤ) (hS : 0 < S) (sh : SegShared) (d : QSegment) (hsh : sh.ok d=true)
    (p e : CQ) (rt : ℚ) (w : CopyI) (m : CompiledModel)
    (hpos : ∀ x ∈ Set.Icc (-1:ℝ) 1,0 ≤ CatalanCore.Zeta5.Potential.chebF
      (fun k => (d.c k:ℝ)) (d.coeff.length-1) x)
    (hc : ballCopyI S sh d p e rt w=some m) :
    Models (CellExpr.segment d p e).value (m.coeff.map ScalarExpr.value) rt m.error.value := by
  have hSq : (0:ℚ) < S := by exact_mod_cast hS
  obtain ⟨ht,hpd,hpc,hmc,hk1,hk2⟩ := segShared_spec d sh hsh
  unfold ballCopyI at hc
  dsimp only at hc
  split at hc
  rotate_left
  · contradiction
  rename_i hg
  simp only [Bool.and_eq_true,beq_iff_eq] at hg
  obtain ⟨⟨⟨⟨hfok,hgate⟩,hterms⟩,hphiHi⟩,hfrac⟩ := hg
  split at hc
  rotate_left
  · contradiction
  rename_i lb hlb
  cases Option.some.inj hc
  set wd := w.wd
  obtain ⟨hok,hδ,he,hh,hδR⟩ := gateI_spec d p e rt wd w.f w.dHi rfl hfok hgate
  -- the ψ-sum enclosure
  set ψb := cbOfGF S (gHorner w.f.psiF sh.pc)
  have hφ0 : w.f.phiF.2 ≠ 0 := by simp only [IFront.phiF,pow2_eq]; positivity
  have hψq : gfQ w.f.psiF=cqInv wd.phi := gfQ_inv _ hφ0
  have hψ0 : 0 < w.f.psiF.2 := by
    simp only [IFront.ok,decide_eq_true_eq] at hfok; exact hfok.1
  have hψ : Encl S ψb (cqDotAux (cqInv wd.phi) sh.pc (1,0) (0,0)) := by
    have h := encl_ofGF S hS _ (gHorner_den _ hψ0 sh.pc)
    rw [gfQ_gHorner _ hψ0,hψq] at h
    rw [cqDotAux_horner]
    have e : cqAdd ((0:ℚ),(0:ℚ)) (cqMul ((1:ℚ),(0:ℚ)) (cqHorner (cqInv wd.phi) sh.pc))=
        cqHorner (cqInv wd.phi) sh.pc := by
      unfold cqAdd cqMul; refine Prod.ext ?_ ?_ <;> simp
    rw [e]; exact h
  have hψ1 := (abs_fst_le_cqL1 _).trans hψ
  have hpoly := polysum_eq d wd.phi sh.pc sh.pd hpd hpc
  have hsplit := segConstant_split wd.terms d wd.phi
  set PS := (((List.range (d.coeff.length-1)).map (fun k : ℕ =>
        d.c (k+1)*(cqPow (cqInv wd.phi) (k+1)).1/(k+1:ℚ))).sum:ℚ)
  set X := cqDotAux (cqInv wd.phi) sh.pc (1,0) (0,0)
  have hpsq : PS=X.1/sh.pd := by
    have := hpoly; rw [cqReal_re] at this; exact_mod_cast this
  have hpdq : (0:ℚ) < sh.pd := by exact_mod_cast hpd
  have hPS : |PS-(ψb.1.1:ℚ)/(S*sh.pd)| ≤ (ψb.2:ℚ)/(S*sh.pd) := by
    have e1 : PS-(ψb.1.1:ℚ)/(S*sh.pd)=(cqSub X (cbVal S ψb)).1/sh.pd := by
      rw [hpsq]; simp only [cqSub,cqAdd,cqNeg,cbVal]; field_simp; ring
    rw [e1,abs_div,abs_of_pos hpdq,div_le_div_iff₀ hpdq (by positivity)]
    have := mul_le_mul_of_nonneg_right hψ1 hpdq.le
    rw [div_mul_eq_mul_div] at this
    calc |(cqSub X (cbVal S ψb)).1| * (S*sh.pd) = (|(cqSub X (cbVal S ψb)).1| * sh.pd)*S := by ring
      _ ≤ ((ψb.2:ℚ)*sh.pd/S)*S := mul_le_mul_of_nonneg_right this hSq.le
      _ = (ψb.2:ℚ)*sh.pd := by field_simp
  -- the log enclosure
  have hL := scalarCheck_sound _ lb hlb
  have hLv : (seScale (d.c 0) (seLogNorm wd.terms wd.phi)).value=
      (d.c 0:ℝ)*(ScalarExpr.log wd.terms (cqSq wd.phi)).value/2 := by
    simp only [seScale_value,seLogNorm]; push_cast; ring
  set ll := if 0 ≤ d.c 0 then d.c 0*lb.1/2 else d.c 0*lb.2/2
  set lh := if 0 ≤ d.c 0 then d.c 0*lb.2/2 else d.c 0*lb.1/2
  have hLl : (ll:ℝ) ≤ (seScale (d.c 0) (seLogNorm wd.terms wd.phi)).value ∧
      (seScale (d.c 0) (seLogNorm wd.terms wd.phi)).value ≤ lh := by
    rw [hLv]
    obtain ⟨h1,h2⟩ := hL
    by_cases hc0 : 0 ≤ d.c 0
    · have hc0r : (0:ℝ) ≤ d.c 0 := by exact_mod_cast hc0
      simp only [ll,lh,if_pos hc0]; push_cast
      constructor
      · have := mul_le_mul_of_nonneg_left h1 hc0r; linarith
      · have := mul_le_mul_of_nonneg_left h2 hc0r; linarith
    · have hc0r : (d.c 0:ℝ) ≤ 0 := by exact_mod_cast (le_of_lt (not_le.mp hc0))
      simp only [ll,lh,if_neg hc0]; push_cast
      constructor
      · have := mul_le_mul_of_nonpos_left h2 hc0r; linarith
      · have := mul_le_mul_of_nonpos_left h1 hc0r; linarith
  rw [← hterms] at hk1 hk2
  have h1 := abs_le.mp hPS
  have h1r : ((PS-(ψb.1.1:ℚ)/(S*sh.pd):ℚ):ℝ) ≤ (((ψb.2:ℚ)/(S*sh.pd):ℚ):ℝ) := by exact_mod_cast h1.2
  have h2r : (((-((ψb.2:ℚ)/(S*sh.pd))):ℚ):ℝ) ≤ ((PS-(ψb.1.1:ℚ)/(S*sh.pd):ℚ):ℝ) := by
    exact_mod_cast h1.1
  push_cast at h1r h2r
  apply assemble_model S hS d p e rt wd _ _ _ _ _ hpos hok
  · intro n hn
    exact encl_ballCopyCoeffsI S hS sh.tab d ht hh w.f hfok e he wd.order w.L n hn
  · rw [hsplit]; push_cast; linarith [hLl.1]
  · rw [hsplit]; push_cast; linarith [hLl.2]
  · exact hδ
  · exact hδR
  · have : segDiscMajorantExpr d wd=mcExpr d sh := by
      unfold mcExpr segDiscMajorantExpr; rw [hterms,hphiHi,hfrac]
    rw [this]; exact hmc

/-! ### Integer upper bounds at scale `S` -/

def mulUp (S a b : ℤ) : ℤ := cdiv (a*b) S
def powUp (S x : ℤ) : ℕ → ℤ
  | 0 => S
  | k+1 => mulUp S (powUp S x k) x
def divUp (S a b : ℤ) : ℤ := cdiv (a*S) b

theorem cdiv_nonneg (n S : ℤ) (hS : 0 < S) (hn : 0 ≤ n) : 0 ≤ cdiv n S := by
  unfold cdiv; exact Int.ediv_nonneg (by linarith) hS.le

theorem mulUp_spec (S a b : ℤ) (hS : 0 < S) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ mulUp S a b ∧ (a:ℚ)/S*((b:ℚ)/S) ≤ (mulUp S a b:ℚ)/S := by
  have hSq : (0:ℚ) < S := by exact_mod_cast hS
  refine ⟨cdiv_nonneg _ _ hS (mul_nonneg ha hb),?_⟩
  have h := cdiv_ge (a*b) S hS
  have e : (a:ℚ)/S*((b:ℚ)/S)=((a*b:ℤ):ℚ)/S/S := by push_cast; field_simp
  rw [e]; exact div_le_div_of_nonneg_right h hSq.le

theorem powUp_spec (S x : ℤ) (hS : 0 < S) (hx : 0 ≤ x) : ∀ k : ℕ,
    0 ≤ powUp S x k ∧ ((x:ℚ)/S)^k ≤ (powUp S x k:ℚ)/S
  | 0 => by
    have hSq : (S:ℚ) ≠ 0 := by exact_mod_cast hS.ne'
    refine ⟨hS.le,?_⟩
    simp only [powUp,pow_zero]; rw [div_self hSq]
  | k+1 => by
    obtain ⟨h0,h1⟩ := powUp_spec S x hS hx k
    obtain ⟨m0,m1⟩ := mulUp_spec S _ _ hS h0 hx
    refine ⟨m0,?_⟩
    rw [pow_succ]; simp only [powUp]
    have hxq : (0:ℚ) ≤ (x:ℚ)/S := by
      have : (0:ℚ) ≤ x := by exact_mod_cast hx
      have : (0:ℚ) < S := by exact_mod_cast hS
      positivity
    exact (mul_le_mul_of_nonneg_right h1 hxq).trans m1

theorem divUp_spec (S a b : ℤ) (hS : 0 < S) (ha : 0 ≤ a) (hb : 0 < b) :
    0 ≤ divUp S a b ∧ (a:ℚ)/b ≤ (divUp S a b:ℚ)/S := by
  have hSq : (0:ℚ) < S := by exact_mod_cast hS
  refine ⟨cdiv_nonneg _ _ hb (mul_nonneg ha hS.le),?_⟩
  have h := cdiv_ge (a*S) b hb
  rw [le_div_iff₀ hSq]
  calc (a:ℚ)/b*S=((a*S:ℤ):ℚ)/b := by push_cast; ring
    _ ≤ _ := h

theorem cdiv_scale_ge (x : ℚ) (S : ℤ) (hS : 0 < S) : x ≤ (cdiv (x.num*S) (x.den:ℤ):ℚ)/S := by
  have hSq : (0:ℚ) < S := by exact_mod_cast hS
  have hd : (0:ℤ) < (x.den:ℤ) := by exact_mod_cast x.den_pos
  have h := cdiv_ge (x.num*S) (x.den:ℤ) hd
  rw [le_div_iff₀ hSq]
  have e : x*S=((x.num*S:ℤ):ℚ)/((x.den:ℤ):ℚ) := by
    rw [Int.cast_mul,Int.cast_natCast]
    nth_rewrite 1 [← Rat.num_div_den x]
    field_simp
  rw [e]; exact h

theorem floor_scale_le (x : ℚ) (S : ℤ) (hS : 0 < S) : ((x.num*S/(x.den:ℤ):ℤ):ℚ)/S ≤ x := by
  have hSq : (0:ℚ) < S := by exact_mod_cast hS
  rw [div_le_iff₀ hSq]; exact (floor_scale x S).1

/-! ### The copy error in integers -/

def cbL1I (b : CB) : ℤ := cbMag b+b.2

def asmErrI (S : ℤ) (cs : List CB) (H δI rtI RI MI : ℤ) (J : ℕ) : ℤ :=
  let ρI := divUp S (rtI+δI) RI
  divUp S (mulUp S (powUp S ρI (J+1)) MI) (S-ρI) +
  mulUp S δI (((List.range J).map (fun k : ℕ =>
    ((k:ℤ)+1)*mulUp S (cbL1I (cbGet cs k)) (powUp S (rtI+δI) k))).sum) +
  ((List.range J).map (fun k : ℕ => mulUp S (cbGet cs k).2 (powUp S rtI (k+1)))).sum + H

theorem cbMag_nonneg (b : CB) : 0 ≤ cbMag b := by
  unfold cbMag; rw [iabs_eq,iabs_eq]; positivity

theorem asmErr_le (S : ℤ) (hS : 0 < S) (cs : List CB) (lo hi δ rt : ℚ) (wd : SegDiscWitness) (mcHi : ℚ)
    (H δI rtI RI MI : ℤ)
    (hrt0 : 0 ≤ rt) (hrt : rt ≤ (rtI:ℚ)/S) (hδ0 : 0 ≤ δ) (hδ : δ ≤ (δI:ℚ)/S)
    (hRI : 0 < RI) (hR : (RI:ℚ)/S ≤ wd.radius) (hρ : divUp S (rtI+δI) RI < S)
    (hMI : 0 ≤ MI) (hmc : mcHi ≤ (MI:ℚ)/S) (hH : (hi-lo)/2 ≤ (H:ℚ)/S)
    (hcs : ∀ k < wd.order,0 ≤ (cbGet cs k).2) :
    (((rt+δ)/wd.radius)^(wd.order+1)/(1-(rt+δ)/wd.radius)*mcHi+
      δ*((List.range wd.order).map (fun k : ℕ => (k+1:ℚ)*cbL1Hi S (cbGet cs k)*(rt+δ)^k)).sum+
      ((List.range wd.order).map (fun k : ℕ => ((cbGet cs k).2:ℚ)/S*rt^(k+1))).sum+(hi-lo)/2) ≤
      (asmErrI S cs H δI rtI RI MI wd.order:ℚ)/S := by
  have hSq : (0:ℚ) < S := by exact_mod_cast hS
  set J := wd.order
  have hrtI : 0 ≤ rtI := by
    have : (0:ℚ) ≤ (rtI:ℚ)/S := hrt0.trans hrt
    have := (div_nonneg_iff.mp this)
    rcases this with h | h
    · exact_mod_cast h.1
    · exact absurd h.2 (not_le.mpr hSq)
  have hδI : 0 ≤ δI := by
    have : (0:ℚ) ≤ (δI:ℚ)/S := hδ0.trans hδ
    rcases div_nonneg_iff.mp this with h | h
    · exact_mod_cast h.1
    · exact absurd h.2 (not_le.mpr hSq)
  have hRIq : (0:ℚ) < (RI:ℚ)/S := div_pos (by exact_mod_cast hRI) hSq
  have hRpos : 0 < wd.radius := hRIq.trans_le hR
  set ρI := divUp S (rtI+δI) RI
  obtain ⟨hρI0,hρI⟩ := divUp_spec S (rtI+δI) RI hS (by linarith) hRI
  -- ρ ≤ ρI/S < 1
  set ρ := (rt+δ)/wd.radius
  have hρ0 : 0 ≤ ρ := div_nonneg (by linarith) hRpos.le
  have hρle : ρ ≤ (ρI:ℚ)/S := by
    calc ρ ≤ ((rtI+δI:ℤ):ℚ)/S/wd.radius := by
            apply div_le_div_of_nonneg_right _ hRpos.le; push_cast; rw [add_div]; linarith
      _ ≤ ((rtI+δI:ℤ):ℚ)/S/((RI:ℚ)/S) := by
            apply div_le_div_of_nonneg_left _ hRIq hR
            have : (0:ℚ) ≤ ((rtI+δI:ℤ):ℚ) := by exact_mod_cast (by linarith : (0:ℤ) ≤ rtI+δI)
            positivity
      _ = ((rtI+δI:ℤ):ℚ)/RI := by field_simp
      _ ≤ _ := hρI
  have hρI1 : (ρI:ℚ)/S < 1 := by rw [div_lt_one hSq]; exact_mod_cast hρ
  have hSρ : 0 < S-ρI := by linarith
  have hSρq : (0:ℚ) < ((S-ρI:ℤ):ℚ)/S := div_pos (by exact_mod_cast hSρ) hSq
  -- tail term
  obtain ⟨hp0,hp1⟩ := powUp_spec S ρI hS hρI0 (J+1)
  obtain ⟨hm0,hm1⟩ := mulUp_spec S _ _ hS hp0 hMI
  obtain ⟨-,hd1⟩ := divUp_spec S (mulUp S (powUp S ρI (J+1)) MI) (S-ρI) hS hm0 hSρ
  have hT : ρ^(J+1)/(1-ρ)*mcHi ≤ (divUp S (mulUp S (powUp S ρI (J+1)) MI) (S-ρI):ℚ)/S := by
    have h1ρ : ((S-ρI:ℤ):ℚ)/S ≤ 1-ρ := by push_cast; rw [sub_div,div_self hSq.ne']; linarith
    have hf0 : 0 ≤ ρ^(J+1)/(1-ρ) := div_nonneg (pow_nonneg hρ0 _) (by linarith)
    have hMIq : (0:ℚ) ≤ (MI:ℚ)/S := div_nonneg (by exact_mod_cast hMI) hSq.le
    calc ρ^(J+1)/(1-ρ)*mcHi ≤ ρ^(J+1)/(1-ρ)*((MI:ℚ)/S) := mul_le_mul_of_nonneg_left hmc hf0
      _ ≤ ((ρI:ℚ)/S)^(J+1)/(((S-ρI:ℤ):ℚ)/S)*((MI:ℚ)/S) := by
            apply mul_le_mul_of_nonneg_right _ hMIq
            exact div_le_div₀ (pow_nonneg (hρ0.trans hρle) _) (pow_le_pow_left₀ hρ0 hρle _) hSρq h1ρ
      _ ≤ (powUp S ρI (J+1):ℚ)/S/(((S-ρI:ℤ):ℚ)/S)*((MI:ℚ)/S) := by
            apply mul_le_mul_of_nonneg_right _ hMIq
            exact div_le_div_of_nonneg_right hp1 hSρq.le
      _ = (powUp S ρI (J+1):ℚ)/S*((MI:ℚ)/S)/(((S-ρI:ℤ):ℚ)/S) := by ring
      _ ≤ (mulUp S (powUp S ρI (J+1)) MI:ℚ)/S/(((S-ρI:ℤ):ℚ)/S) :=
            div_le_div_of_nonneg_right hm1 hSρq.le
      _ = ((mulUp S (powUp S ρI (J+1)) MI:ℤ):ℚ)/((S-ρI:ℤ):ℚ) := by field_simp
      _ ≤ _ := hd1
  -- displacement term
  have hx0 : 0 ≤ rtI+δI := by linarith
  have hk : ∀ k ∈ Finset.range J,(k+1:ℚ)*cbL1Hi S (cbGet cs k)*(rt+δ)^k ≤
      (((k:ℤ)+1)*mulUp S (cbL1I (cbGet cs k)) (powUp S (rtI+δI) k):ℤ)/S := by
    intro k hkJ
    have hL0 : 0 ≤ cbL1I (cbGet cs k) := add_nonneg (cbMag_nonneg _) (hcs k (Finset.mem_range.mp hkJ))
    obtain ⟨hq0,hq1⟩ := powUp_spec S (rtI+δI) hS hx0 k
    obtain ⟨-,hu1⟩ := mulUp_spec S _ _ hS hL0 hq0
    have hxk : (rt+δ)^k ≤ (powUp S (rtI+δI) k:ℚ)/S := by
      refine (pow_le_pow_left₀ (by linarith) ?_ k).trans hq1
      push_cast; rw [add_div]; linarith
    have hLq : (0:ℚ) ≤ cbL1Hi S (cbGet cs k) := by
      unfold cbL1Hi; have : (0:ℚ) ≤ ((cbMag (cbGet cs k)+(cbGet cs k).2:ℤ):ℚ) := by exact_mod_cast hL0
      positivity
    have hk1 : (0:ℚ) ≤ (k+1:ℚ) := by positivity
    calc (k+1:ℚ)*cbL1Hi S (cbGet cs k)*(rt+δ)^k
        ≤ (k+1:ℚ)*(cbL1Hi S (cbGet cs k)*((powUp S (rtI+δI) k:ℚ)/S)) := by
          rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hxk hLq) hk1
      _ ≤ (k+1:ℚ)*((mulUp S (cbL1I (cbGet cs k)) (powUp S (rtI+δI) k):ℚ)/S) := by
          apply mul_le_mul_of_nonneg_left _ hk1
          simpa only [cbL1Hi,cbL1I] using hu1
      _ = _ := by push_cast; ring
  have hsd0 : 0 ≤ ((List.range J).map (fun k : ℕ =>
      ((k:ℤ)+1)*mulUp S (cbL1I (cbGet cs k)) (powUp S (rtI+δI) k))).sum := by
    rw [list_sum_map_range]; apply Finset.sum_nonneg; intro k hkJ
    have hL0 : 0 ≤ cbL1I (cbGet cs k) := add_nonneg (cbMag_nonneg _) (hcs k (Finset.mem_range.mp hkJ))
    have := (mulUp_spec S _ _ hS hL0 (powUp_spec S (rtI+δI) hS hx0 k).1).1
    positivity
  set sd := ((List.range J).map (fun k : ℕ =>
    ((k:ℤ)+1)*mulUp S (cbL1I (cbGet cs k)) (powUp S (rtI+δI) k))).sum
  have hDsum : ((List.range J).map (fun k : ℕ => (k+1:ℚ)*cbL1Hi S (cbGet cs k)*(rt+δ)^k)).sum ≤ (sd:ℚ)/S := by
    rw [list_sum_map_range]
    simp only [sd]; rw [list_sum_map_range]; push_cast; rw [Finset.sum_div]
    apply Finset.sum_le_sum; intro k hkJ; have := hk k hkJ; push_cast at this; exact this
  obtain ⟨-,hδm⟩ := mulUp_spec S δI sd hS hδI hsd0
  have hD : δ*((List.range J).map (fun k : ℕ => (k+1:ℚ)*cbL1Hi S (cbGet cs k)*(rt+δ)^k)).sum ≤
      (mulUp S δI sd:ℚ)/S := by
    have hs0 : 0 ≤ ((List.range J).map (fun k : ℕ => (k+1:ℚ)*cbL1Hi S (cbGet cs k)*(rt+δ)^k)).sum := by
      rw [list_sum_map_range]; apply Finset.sum_nonneg; intro k hkJ
      have hL0 : 0 ≤ cbL1I (cbGet cs k) := add_nonneg (cbMag_nonneg _) (hcs k (Finset.mem_range.mp hkJ))
      have : (0:ℚ) ≤ cbL1Hi S (cbGet cs k) := by
        unfold cbL1Hi; have : (0:ℚ) ≤ ((cbMag (cbGet cs k)+(cbGet cs k).2:ℤ):ℚ) := by exact_mod_cast hL0
        positivity
      have : (0:ℚ) ≤ rt+δ := by linarith
      positivity
    have hsq2 : (0:ℚ) ≤ (sd:ℚ)/S := div_nonneg (by exact_mod_cast hsd0) hSq.le
    calc _ ≤ ((δI:ℚ)/S)*((sd:ℚ)/S) := mul_le_mul hδ hDsum hs0 (hδ0.trans hδ)
      _ ≤ _ := hδm
  -- ball term
  have hB : ((List.range J).map (fun k : ℕ => ((cbGet cs k).2:ℚ)/S*rt^(k+1))).sum ≤
      ((((List.range J).map (fun k : ℕ => mulUp S (cbGet cs k).2 (powUp S rtI (k+1)))).sum:ℤ):ℚ)/S := by
    rw [list_sum_map_range,list_sum_map_range]; push_cast; rw [Finset.sum_div]
    apply Finset.sum_le_sum; intro k hkJ
    have hr0 := hcs k (Finset.mem_range.mp hkJ)
    obtain ⟨hq0,hq1⟩ := powUp_spec S rtI hS hrtI (k+1)
    obtain ⟨-,hu1⟩ := mulUp_spec S _ _ hS hr0 hq0
    have hrq : (0:ℚ) ≤ ((cbGet cs k).2:ℚ)/S := div_nonneg (by exact_mod_cast hr0) hSq.le
    calc ((cbGet cs k).2:ℚ)/S*rt^(k+1) ≤ ((cbGet cs k).2:ℚ)/S*((powUp S rtI (k+1):ℚ)/S) :=
          mul_le_mul_of_nonneg_left ((pow_le_pow_left₀ hrt0 hrt _).trans hq1) hrq
      _ ≤ _ := hu1
  unfold asmErrI
  simp only []
  push_cast
  rw [add_div,add_div,add_div]
  push_cast at hT hD hB
  linarith

/-! ### One copy with integer output -/

structure SegSharedI where
  sh : SegShared
  kLoI : ℤ
  kHiI : ℤ
  MI : ℤ

def SegSharedI.ok (S : ℤ) (d : QSegment) (s : SegSharedI) : Bool :=
  s.sh.ok d && decide ((s.kLoI:ℚ)/S ≤ s.sh.kLo ∧ s.sh.kHi ≤ (s.kHiI:ℚ)/S ∧
    s.sh.mcHi ≤ (s.MI:ℚ)/S ∧ 0 ≤ s.MI)

/-- Constant-term interval, centre and copy error, all at scale `S`. -/
def copyTailI (S : ℤ) (s : SegSharedI) (d : QSegment) (lb : ℚ×ℚ) (ψb : CB) (cs : List CB)
    (rt dHi radius : ℚ) (J : ℕ) : Option (List ℤ×ℤ) :=
  let pmLo := (ψb.1.1-ψb.2)/s.sh.pd
  let pmHi := cdiv (ψb.1.1+ψb.2) s.sh.pd
  let c0 := d.c 0
  let ll := min (c0*lb.1/2) (c0*lb.2/2)
  let lh := max (c0*lb.1/2) (c0*lb.2/2)
  let loI := s.kLoI+ll.num*S/(ll.den:ℤ)-pmHi
  let hiI := s.kHiI+cdiv (lh.num*S) (lh.den:ℤ)-pmLo
  let c0I := (loI+hiI)/2
  let rtI := cdiv (rt.num*S) (rt.den:ℤ)
  let δI := cdiv (dHi.num*S) (dHi.den:ℤ)
  let RI := radius.num*S/(radius.den:ℤ)
  if 0 < RI ∧ divUp S (rtI+δI) RI < S ∧ loI ≤ hiI then
    some (c0I::(List.range J).map (fun k : ℕ => (cbGet cs k).1.1),
      asmErrI S cs (hiI-c0I) δI rtI RI s.MI J)
  else none

def ballCopyJ (S : ℤ) (s : SegSharedI) (d : QSegment) (p e : CQ) (rt : ℚ) (w : CopyI) :
    Option (List ℤ×ℤ) :=
  let sh := s.sh
  let wd := w.wd
  if w.f.ok && gateI d p e rt wd w.f w.dHi && wd.terms == sh.terms && wd.phiHi == sh.phiHi &&
      wd.fraction == sh.fraction then
    match (ScalarExpr.log wd.terms (cqSq wd.phi)).check with
    | some lb =>
      copyTailI S s d lb (cbOfGF S (gHorner w.f.psiF sh.pc)) (ballCopyCoeffsI S sh.tab w.f wd.order w.L)
        rt w.dHi wd.radius wd.order
    | none => none
  else none

theorem models_mono_err (f : ℝ → ℝ) (a : List ℝ) (r e e' : ℝ) (h : Models f a r e) (he : e ≤ e') :
    Models f a r e' :=
  ⟨h.1,h.2.1.trans he,fun u hu => (h.2.2 u hu).trans he⟩

theorem encl_rad_nonneg (S : ℤ) (hS : 0 < S) (b : CB) (x : CQ) (h : Encl S b x) : 0 ≤ b.2 := by
  have hSq : (0:ℚ) < S := by exact_mod_cast hS
  have h1 : (0:ℚ) ≤ (b.2:ℚ)/S := (cqL1_nonneg _).trans h
  rcases div_nonneg_iff.mp h1 with h2 | h2
  · exact_mod_cast h2.1
  · exact absurd h2.2 (not_le.mpr hSq)

theorem ballCopyJ_model (S : ℤ) (hS : 0 < S) (s : SegSharedI) (d : QSegment) (hsh : s.ok S d=true)
    (p e : CQ) (rt : ℚ) (w : CopyI) (out : List ℤ×ℤ)
    (hpos : ∀ x ∈ Set.Icc (-1:ℝ) 1,0 ≤ CatalanCore.Zeta5.Potential.chebF
      (fun k => (d.c k:ℝ)) (d.coeff.length-1) x)
    (hc : ballCopyJ S s d p e rt w=some out) :
    Models (CellExpr.segment d p e).value (out.1.map (fun c : ℤ => (((c:ℚ)/S:ℚ):ℝ))) rt
      (((out.2:ℚ)/S:ℚ):ℝ) := by
  have hSq : (0:ℚ) < S := by exact_mod_cast hS
  unfold SegSharedI.ok at hsh
  simp only [Bool.and_eq_true,decide_eq_true_eq] at hsh
  obtain ⟨hsh0,hkLo,hkHi,hmcI,hMI⟩ := hsh
  set sh := s.sh
  obtain ⟨ht,hpd,hpc,hmc,hk1,hk2⟩ := segShared_spec d sh hsh0
  unfold ballCopyJ at hc
  dsimp only at hc
  split_ifs at hc with hg
  simp only [Bool.and_eq_true,beq_iff_eq] at hg
  obtain ⟨⟨⟨⟨hfok,hgate⟩,hterms⟩,hphiHi⟩,hfrac⟩ := hg
  split at hc
  rotate_left
  · contradiction
  rename_i lb hlb
  set wd := w.wd
  obtain ⟨hok,hδ,he,hh,hδR⟩ := gateI_spec d p e rt wd w.f w.dHi rfl hfok hgate
  -- the ψ-sum enclosure
  set ψb := cbOfGF S (gHorner w.f.psiF sh.pc)
  have hφ0 : w.f.phiF.2 ≠ 0 := by simp only [IFront.phiF,pow2_eq]; positivity
  have hψq : gfQ w.f.psiF=cqInv wd.phi := gfQ_inv _ hφ0
  have hψ0 : 0 < w.f.psiF.2 := by
    simp only [IFront.ok,decide_eq_true_eq] at hfok; exact hfok.1
  have hψ : Encl S ψb (cqDotAux (cqInv wd.phi) sh.pc (1,0) (0,0)) := by
    have h := encl_ofGF S hS _ (gHorner_den _ hψ0 sh.pc)
    rw [gfQ_gHorner _ hψ0,hψq] at h
    rw [cqDotAux_horner]
    have e : cqAdd ((0:ℚ),(0:ℚ)) (cqMul ((1:ℚ),(0:ℚ)) (cqHorner (cqInv wd.phi) sh.pc))=
        cqHorner (cqInv wd.phi) sh.pc := by
      unfold cqAdd cqMul; refine Prod.ext ?_ ?_ <;> simp
    rw [e]; exact h
  have hψ1 := (abs_fst_le_cqL1 _).trans hψ
  have hpoly := polysum_eq d wd.phi sh.pc sh.pd hpd hpc
  have hsplit := segConstant_split wd.terms d wd.phi
  set PS := (((List.range (d.coeff.length-1)).map (fun k : ℕ =>
        d.c (k+1)*(cqPow (cqInv wd.phi) (k+1)).1/(k+1:ℚ))).sum:ℚ)
  set X := cqDotAux (cqInv wd.phi) sh.pc (1,0) (0,0)
  have hpsq : PS=X.1/sh.pd := by
    have := hpoly; rw [cqReal_re] at this; exact_mod_cast this
  have hpdq : (0:ℚ) < sh.pd := by exact_mod_cast hpd
  -- PS ∈ [pmLo/S, pmHi/S]
  have hX1 : |X.1-(ψb.1.1:ℚ)/S| ≤ (ψb.2:ℚ)/S := by
    have e1 : X.1-(ψb.1.1:ℚ)/S=(cqSub X (cbVal S ψb)).1 := by
      simp only [cqSub,cqAdd,cqNeg,cbVal,sub_eq_add_neg]
    rw [e1]; exact hψ1
  have hPSlo : (((ψb.1.1-ψb.2)/sh.pd:ℤ):ℚ)/S ≤ PS := by
    obtain ⟨a1,-⟩ := ediv_bounds (ψb.1.1-ψb.2) sh.pd hpd
    rw [hpsq,div_le_iff₀ hSq]
    have h2 : ((ψb.1.1-ψb.2:ℤ):ℚ)/sh.pd ≤ X.1/sh.pd*S := by
      rw [div_mul_eq_mul_div,div_le_div_iff_of_pos_right hpdq]
      have := (abs_le.mp hX1).1
      push_cast
      have h3 : ((ψb.1.1:ℚ)-ψb.2)/S ≤ X.1 := by rw [sub_div]; linarith
      rw [div_le_iff₀ hSq] at h3; linarith
    linarith
  have hPShi : PS ≤ (cdiv (ψb.1.1+ψb.2) sh.pd:ℚ)/S := by
    have a1 := cdiv_ge (ψb.1.1+ψb.2) sh.pd hpd
    rw [hpsq,le_div_iff₀ hSq]
    have h2 : X.1/sh.pd*S ≤ ((ψb.1.1+ψb.2:ℤ):ℚ)/sh.pd := by
      rw [div_mul_eq_mul_div,div_le_div_iff_of_pos_right hpdq]
      have := (abs_le.mp hX1).2
      push_cast
      have h3 : X.1 ≤ ((ψb.1.1:ℚ)+ψb.2)/S := by rw [add_div]; linarith
      rw [le_div_iff₀ hSq] at h3; linarith
    linarith
  -- the log enclosure
  have hL := scalarCheck_sound _ lb hlb
  have hLv : (seScale (d.c 0) (seLogNorm wd.terms wd.phi)).value=
      (d.c 0:ℝ)*(ScalarExpr.log wd.terms (cqSq wd.phi)).value/2 := by
    simp only [seScale_value,seLogNorm]; push_cast; ring
  set ll := min (d.c 0*lb.1/2) (d.c 0*lb.2/2)
  set lh := max (d.c 0*lb.1/2) (d.c 0*lb.2/2)
  have hLl : (ll:ℝ) ≤ (seScale (d.c 0) (seLogNorm wd.terms wd.phi)).value ∧
      (seScale (d.c 0) (seLogNorm wd.terms wd.phi)).value ≤ lh := by
    rw [hLv]
    obtain ⟨h1,h2⟩ := hL
    simp only [ll,lh]; push_cast
    by_cases hc0 : 0 ≤ d.c 0
    · have hc0r : (0:ℝ) ≤ d.c 0 := by exact_mod_cast hc0
      have a1 := mul_le_mul_of_nonneg_left h1 hc0r
      have a2 := mul_le_mul_of_nonneg_left h2 hc0r
      constructor
      · exact (min_le_left _ _).trans (by linarith)
      · exact le_trans (by linarith) (le_max_right _ _)
    · have hc0r : (d.c 0:ℝ) ≤ 0 := by exact_mod_cast (le_of_lt (not_le.mp hc0))
      have a1 := mul_le_mul_of_nonpos_left h1 hc0r
      have a2 := mul_le_mul_of_nonpos_left h2 hc0r
      constructor
      · exact (min_le_right _ _).trans (by linarith)
      · exact le_trans (by linarith) (le_max_left _ _)
  rw [← hterms] at hk1 hk2
  -- integer constant interval
  have hllI := floor_scale_le ll S hS
  have hlhI := cdiv_scale_ge lh S hS
  unfold copyTailI at hc
  dsimp only at hc
  split_ifs at hc with hcond
  obtain ⟨hRI,hρ,hlohi⟩ := hcond
  have hout := (Option.some.inj hc).symm
  subst hout
  set loI := s.kLoI+ll.num*S/(ll.den:ℤ)-cdiv (ψb.1.1+ψb.2) sh.pd
  set hiI := s.kHiI+cdiv (lh.num*S) (lh.den:ℤ)-(ψb.1.1-ψb.2)/sh.pd
  set c0I := (loI+hiI)/2
  have hval : (segConstant wd.terms d wd.phi).value=(kExpr d wd.terms).value+
      (seScale (d.c 0) (seLogNorm wd.terms wd.phi)).value-PS := by
    rw [hsplit]; all_goals (push_cast; try ring)
  have hlo : (((loI:ℚ)/S:ℚ):ℝ) ≤ (segConstant wd.terms d wd.phi).value := by
    rw [hval]
    have e1 : ((loI:ℚ)/S)=(s.kLoI:ℚ)/S+((ll.num*S/(ll.den:ℤ):ℤ):ℚ)/S-
        (cdiv (ψb.1.1+ψb.2) sh.pd:ℚ)/S := by simp only [loI]; push_cast; ring
    rw [e1]; push_cast
    have a1 : ((s.kLoI:ℚ)/S:ℝ) ≤ (sh.kLo:ℝ) := by exact_mod_cast hkLo
    have a2 : ((((ll.num*S/(ll.den:ℤ):ℤ):ℚ)/S:ℚ):ℝ) ≤ (ll:ℝ) := by exact_mod_cast hllI
    have a3 : (PS:ℝ) ≤ (((cdiv (ψb.1.1+ψb.2) sh.pd:ℚ)/S:ℚ):ℝ) := by exact_mod_cast hPShi
    push_cast at a1 a2 a3
    linarith [hLl.1]
  have hhi : (segConstant wd.terms d wd.phi).value ≤ (((hiI:ℚ)/S:ℚ):ℝ) := by
    rw [hval]
    have e1 : ((hiI:ℚ)/S)=(s.kHiI:ℚ)/S+(cdiv (lh.num*S) (lh.den:ℤ):ℚ)/S-
        (((ψb.1.1-ψb.2)/sh.pd:ℤ):ℚ)/S := by simp only [hiI]; push_cast; ring
    rw [e1]; push_cast
    have a1 : (sh.kHi:ℝ) ≤ ((s.kHiI:ℚ)/S:ℝ) := by exact_mod_cast hkHi
    have a2 : (lh:ℝ) ≤ (((cdiv (lh.num*S) (lh.den:ℤ):ℚ)/S:ℚ):ℝ) := by exact_mod_cast hlhI
    have a3 : ((((((ψb.1.1-ψb.2)/sh.pd:ℤ):ℚ)/S):ℚ):ℝ) ≤ (PS:ℝ) := by exact_mod_cast hPSlo
    push_cast at a1 a2 a3
    linarith [hLl.2]
  -- the rational model with lo' = (c0I-H)/S, hi' = hiI/S
  have hc0lo : 2*c0I ≤ loI+hiI := by
    have := Int.ediv_mul_le (loI+hiI) (two_ne_zero); simp only [c0I]; linarith
  have hlo' : ((((c0I-(hiI-c0I):ℤ):ℚ)/S:ℚ):ℝ) ≤ (segConstant wd.terms d wd.phi).value := by
    refine le_trans ?_ hlo
    have : ((c0I-(hiI-c0I):ℤ):ℚ)/S ≤ (loI:ℚ)/S :=
      div_le_div_of_nonneg_right (by exact_mod_cast (by linarith : c0I-(hiI-c0I) ≤ loI)) hSq.le
    exact_mod_cast this
  have hhi' : (segConstant wd.terms d wd.phi).value ≤ ((((c0I+(hiI-c0I):ℤ):ℚ)/S:ℚ):ℝ) := by
    have e : c0I+(hiI-c0I)=hiI := by ring
    rw [e]; exact hhi
  have henc : ∀ n < wd.order,Encl S (cbGet (ballCopyCoeffsI S sh.tab w.f wd.order w.L) n)
      (segCoeff d wd.phi e (n+1)) := fun n hn =>
    encl_ballCopyCoeffsI S hS sh.tab d ht hh w.f hfok e he wd.order w.L n hn
  have hmajor : (segDiscMajorantExpr d wd).value ≤ sh.mcHi := by
    have : segDiscMajorantExpr d wd=mcExpr d sh := by
      unfold mcExpr segDiscMajorantExpr; rw [hterms,hphiHi,hfrac]
    rw [this]; exact hmc
  have hA := assemble_model S hS d p e rt wd (ballCopyCoeffsI S sh.tab w.f wd.order w.L)
    (((c0I-(hiI-c0I):ℤ):ℚ)/S) (((c0I+(hiI-c0I):ℤ):ℚ)/S) w.dHi sh.mcHi hpos hok henc
    (by exact_mod_cast hlo') (by exact_mod_cast hhi') hδ hδR hmajor
  have hrt0 : 0 ≤ rt := by exact_mod_cast hA.1
  have hδ0 : 0 ≤ w.dHi := (cqL1_nonneg _).trans hδ
  -- coefficients agree
  have hco : (assemble S (ballCopyCoeffsI S sh.tab w.f wd.order w.L)
      (((c0I-(hiI-c0I):ℤ):ℚ)/S) (((c0I+(hiI-c0I):ℤ):ℚ)/S) w.dHi rt wd sh.mcHi).coeff.map
        ScalarExpr.value=(c0I::(List.range wd.order).map (fun k : ℕ =>
          (cbGet (ballCopyCoeffsI S sh.tab w.f wd.order w.L) k).1.1)).map
            (fun c : ℤ => (((c:ℚ)/S:ℚ):ℝ)) := by
    simp only [assemble,List.range_succ_eq_map,List.map_cons,List.map_map]
    congr 1
    · simp only [ite_true,seRat_value]
      congr 1
      push_cast; field_simp; ring
  rw [← hco]
  apply models_mono_err _ _ _ _ _ hA
  simp only [assemble,seRat_value]
  have hle := asmErr_le S hS (ballCopyCoeffsI S sh.tab w.f wd.order w.L)
    (((c0I-(hiI-c0I):ℤ):ℚ)/S) (((c0I+(hiI-c0I):ℤ):ℚ)/S) w.dHi rt wd sh.mcHi (hiI-c0I)
    (cdiv (w.dHi.num*S) (w.dHi.den:ℤ)) (cdiv (rt.num*S) (rt.den:ℤ)) (wd.radius.num*S/(wd.radius.den:ℤ))
    s.MI hrt0 (cdiv_scale_ge rt S hS) hδ0 (cdiv_scale_ge w.dHi S hS) hRI (floor_scale_le _ S hS) hρ hMI hmcI
    (le_of_eq (by push_cast; ring))
    (fun k hk => encl_rad_nonneg S hS _ _ (henc k hk))
  exact Rat.cast_le.mpr hle

end CatalanCore.Li2.DecayCert.Seg
