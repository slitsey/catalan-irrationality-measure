module
public import CatalanCore.Li2.DecayCert.PolynomialList
public import CatalanCore.Li2.DecayCert.Source.Sound
public import CatalanCore.Li2.DecayCert.Compile.Defs
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 600000
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert.Rounded

/-- Rational L1 errors; no field or potential bound is supplied by a certificate. -/
def Close (a b : CQ) (e : ℚ) : Prop := cqL1 (cqSub a b) ≤ e

theorem l1_nonneg (a : CQ) : 0 ≤ cqL1 a := add_nonneg (abs_nonneg _) (abs_nonneg _)
theorem l1_add (a b : CQ) : cqL1 (cqAdd a b) ≤ cqL1 a+cqL1 b := by
  have h0 := abs_add_le a.1 b.1
  have h1 := abs_add_le a.2 b.2
  dsimp [cqL1,cqAdd]
  linarith

theorem l1_neg (a : CQ) : cqL1 (cqNeg a)=cqL1 a := by
  simp [cqL1,cqNeg]

theorem l1_mul (a b : CQ) : cqL1 (cqMul a b) ≤ cqL1 a*cqL1 b := by
  have h0 : |a.1*b.1-a.2*b.2| ≤ |a.1*b.1|+|a.2*b.2| := by
    simpa only [sub_eq_add_neg,abs_neg] using abs_add_le (a.1*b.1) (-(a.2*b.2))
  have h1 := abs_add_le (a.1*b.2) (a.2*b.1)
  simp only [abs_mul] at h0 h1
  dsimp [cqL1,cqMul]
  nlinarith

theorem close_nonneg {a b : CQ} {e : ℚ} (h : Close a b e) : 0 ≤ e :=
  (l1_nonneg _).trans h

theorem close_add {a b ah bh : CQ} {ea eb : ℚ}
    (ha : Close a ah ea) (hb : Close b bh eb) :
    Close (cqAdd a b) (cqAdd ah bh) (ea+eb) := by
  unfold Close at *
  have heq : cqSub (cqAdd a b) (cqAdd ah bh)=cqAdd (cqSub a ah) (cqSub b bh) := by
    apply Prod.ext <;> simp [cqSub,cqAdd,cqNeg] <;> ring
  rw [heq]
  exact (l1_add _ _).trans (add_le_add ha hb)

theorem close_neg {a ah : CQ} {ea : ℚ} (ha : Close a ah ea) :
    Close (cqNeg a) (cqNeg ah) ea := by
  unfold Close at *
  have heq : cqSub (cqNeg a) (cqNeg ah)=cqNeg (cqSub a ah) := by
    apply Prod.ext <;> simp [cqSub,cqAdd,cqNeg] <;> ring
  rw [heq,l1_neg]
  exact ha

theorem close_sub {a b ah bh : CQ} {ea eb : ℚ}
    (ha : Close a ah ea) (hb : Close b bh eb) :
    Close (cqSub a b) (cqSub ah bh) (ea+eb) :=
  close_add ha (close_neg hb)

theorem close_mul {a b ah bh : CQ} {ea eb : ℚ}
    (ha : Close a ah ea) (hb : Close b bh eb) :
    Close (cqMul a b) (cqMul ah bh)
      (cqL1 ah*eb+cqL1 bh*ea+ea*eb) := by
  have hea := close_nonneg ha
  have heb := close_nonneg hb
  unfold Close at *
  have heq : cqSub (cqMul a b) (cqMul ah bh)=
      cqAdd (cqAdd (cqMul ah (cqSub b bh)) (cqMul (cqSub a ah) bh))
        (cqMul (cqSub a ah) (cqSub b bh)) := by
    apply Prod.ext <;> simp [cqSub,cqAdd,cqNeg,cqMul] <;> ring
  rw [heq]
  have h0 := l1_mul ah (cqSub b bh)
  have h1 := l1_mul (cqSub a ah) bh
  have h2 := l1_mul (cqSub a ah) (cqSub b bh)
  have h3 := l1_add (cqMul ah (cqSub b bh)) (cqMul (cqSub a ah) bh)
  have h4 := l1_add (cqAdd (cqMul ah (cqSub b bh)) (cqMul (cqSub a ah) bh))
      (cqMul (cqSub a ah) (cqSub b bh))
  have m0 := mul_le_mul_of_nonneg_left hb (l1_nonneg ah)
  have m1 := mul_le_mul_of_nonneg_right ha (l1_nonneg bh)
  have m2 := mul_le_mul ha hb (l1_nonneg _) hea
  nlinarith

theorem close_scale {a ah : CQ} {ea : ℚ} (q : ℚ) (ha : Close a ah ea) :
    Close (cqScale q a) (cqScale q ah) (|q| *ea) := by
  unfold Close at *
  have heq : cqSub (cqScale q a) (cqScale q ah)=cqScale q (cqSub a ah) := by
    apply Prod.ext <;> dsimp [cqSub,cqAdd,cqNeg,cqScale] <;> ring
  rw [heq]
  have hscale : cqL1 (cqScale q (cqSub a ah))=|q| *cqL1 (cqSub a ah) := by
    dsimp [cqL1,cqScale]
    rw [abs_mul,abs_mul,mul_add]
  rw [hscale]
  exact mul_le_mul_of_nonneg_left ha (abs_nonneg _)

theorem close_trans {a b c : CQ} {ea eb : ℚ}
    (ha : Close a b ea) (hb : Close b c eb) : Close a c (ea+eb) := by
  unfold Close at *
  have heq : cqSub a c=cqAdd (cqSub a b) (cqSub b c) := by
    apply Prod.ext <;> simp [cqSub,cqAdd,cqNeg] <;> ring
  rw [heq]
  exact (l1_add _ _).trans (add_le_add ha hb)

theorem close_re {a b : CQ} {e : ℚ} (h : Close a b e) : |a.1-b.1| ≤ e := by
  have hn := abs_nonneg (a.2-b.2)
  have hh : |a.1-b.1|+|a.2-b.2| ≤ e := by
    simpa only [Close,cqL1,cqSub,cqAdd,cqNeg,sub_eq_add_neg] using h
  linarith

theorem close_l1 {a b : CQ} {e : ℚ} (h : Close a b e) : cqL1 a ≤ cqL1 b+e := by
  have heq : a=cqAdd b (cqSub a b) := by
    apply Prod.ext <;> dsimp [cqSub,cqAdd,cqNeg] <;> ring
  calc
    cqL1 a = cqL1 (cqAdd b (cqSub a b)) := congrArg cqL1 heq
    _ ≤ cqL1 b+cqL1 (cqSub a b) := l1_add _ _
    _ ≤ cqL1 b+e := add_le_add le_rfl h

def decode (S : ℤ) (a : ℤ×ℤ) : CQ := ((a.1:ℚ)/(S:ℚ),(a.2:ℚ)/(S:ℚ))
def iadd (a b : ℤ×ℤ) : ℤ×ℤ := (a.1+b.1,a.2+b.2)
def imul (a b : ℤ×ℤ) : ℤ×ℤ := (a.1*b.1-a.2*b.2,a.1*b.2+a.2*b.1)

theorem decode_add (S : ℤ) (a b : ℤ×ℤ) :
    decode S (iadd a b)=cqAdd (decode S a) (decode S b) := by
  apply Prod.ext <;> simp [decode,iadd,cqAdd,add_div]

theorem decode_mul (S : ℤ) (a b : ℤ×ℤ) :
    decode (S*S) (imul a b)=cqMul (decode S a) (decode S b) := by
  apply Prod.ext <;> simp [decode,imul,cqMul] <;> ring

theorem cqAdd_eq_add (a b : CQ) : cqAdd a b = a+b := rfl

theorem close_sum (xs : List ℕ) (a b : ℕ → CQ) (e : ℕ → ℚ)
    (h : ∀ i ∈ xs, Close (a i) (b i) (e i)) :
    Close (cqSum (xs.map a)) (cqSum (xs.map b)) (xs.map e).sum := by
  induction xs with
  | nil => simp [Close,cqSum,cqSub,cqAdd,cqNeg,cqL1]
  | cons i xs ih =>
      have hi := h i (by simp)
      have hs := ih (fun j hj => h j (by simp [hj]))
      have hc := close_add hi hs
      rw [cqAdd_eq_add,cqAdd_eq_add] at hc
      simpa only [cqSum_eq_sum,List.map_cons,List.sum_cons] using hc

def isum : List (ℤ×ℤ) → ℤ×ℤ
  | [] => (0,0)
  | a::as => iadd a (isum as)

theorem decode_sum (S : ℤ) (xs : List (ℤ×ℤ)) :
    decode S (isum xs)=cqSum (xs.map (decode S)) := by
  induction xs with
  | nil => simp [isum,decode,cqSum_eq_sum]
  | cons a xs ih =>
      rw [isum,decode_add,ih]
      simp only [cqSum_eq_sum,List.map_cons,List.sum_cons]
      rfl

theorem ediv_error_Q (a b : ℤ) (hb : b ≠ 0) :
    |((a/b:ℤ):ℚ)-(a:ℚ)/(b:ℚ)| ≤ 1 := by
  have h := ediv_real_error a b hb
  have hh : |((a/b:ℤ):ℚ)-(a:ℚ)/(b:ℚ)| < 1 := by exact_mod_cast h
  exact hh.le

theorem grid_ediv_close (S D : ℤ) (raw : ℤ×ℤ) (hS : 0 < S) (hD : D ≠ 0) :
    Close (cqScale (1/(S:ℚ)) (decode D raw))
      (decode S (raw.1/D,raw.2/D)) (2/(S:ℚ)) := by
  have hs : (0:ℚ)<(S:ℚ) := by exact_mod_cast hS
  have h0 := ediv_error_Q raw.1 D hD
  have h1 := ediv_error_Q raw.2 D hD
  have t0 : |(raw.1:ℚ)/(D:ℚ)-((raw.1/D:ℤ):ℚ)| ≤ 1 := by simpa only [abs_sub_comm] using h0
  have t1 : |(raw.2:ℚ)/(D:ℚ)-((raw.2/D:ℤ):ℚ)| ≤ 1 := by simpa only [abs_sub_comm] using h1
  unfold Close
  have heq : cqSub (cqScale (1/(S:ℚ)) (decode D raw))
      (decode S (raw.1/D,raw.2/D))=
      cqScale (1/(S:ℚ)) (((raw.1:ℚ)/(D:ℚ)-((raw.1/D:ℤ):ℚ)),
        ((raw.2:ℚ)/(D:ℚ)-((raw.2/D:ℤ):ℚ))) := by
    apply Prod.ext <;> dsimp [cqSub,cqAdd,cqNeg,cqScale,decode] <;> ring
  rw [heq]
  dsimp [cqL1,cqScale]
  rw [abs_mul,abs_mul,abs_of_pos (one_div_pos.mpr hs),← mul_add]
  calc
    (1/(S:ℚ))*(|(raw.1:ℚ)/(D:ℚ)-((raw.1/D:ℤ):ℚ)|+
        |(raw.2:ℚ)/(D:ℚ)-((raw.2/D:ℤ):ℚ)|) ≤ (1/(S:ℚ))*(1+1) :=
      mul_le_mul_of_nonneg_left (add_le_add t0 t1) (le_of_lt (one_div_pos.mpr hs))
    _ = 2/(S:ℚ) := by ring

def il1 (a : ℤ×ℤ) : ℤ := |a.1|+|a.2|

theorem l1_decode (S : ℤ) (a : ℤ×ℤ) (hS : 0 < S) :
    cqL1 (decode S a)=(il1 a:ℚ)/(S:ℚ) := by
  have hs : (0:ℚ)<(S:ℚ) := by exact_mod_cast hS
  simp only [cqL1,decode,abs_div,abs_of_pos hs,il1,Int.cast_add,Int.cast_abs]
  ring

theorem sum_cast_div (xs : List ℤ) (D : ℚ) :
    ((xs.sum:ℤ):ℚ)/D=(xs.map (fun (a : ℤ) => (a:ℚ)/D)).sum := by
  induction xs with
  | nil => simp
  | cons a xs ih => simp only [List.sum_cons,List.map_cons,Int.cast_add,add_div,ih]

def iconv (xs : List ℕ) (a b : ℕ → ℤ×ℤ) : ℤ×ℤ :=
  isum (xs.map (fun i => imul (a i) (b i)))

theorem decode_iconv (S : ℤ) (xs : List ℕ) (a b : ℕ → ℤ×ℤ) :
    decode (S*S) (iconv xs a b)=
      cqSum (xs.map (fun i => cqMul (decode S (a i)) (decode S (b i)))) := by
  rw [iconv,decode_sum]
  simp only [List.map_map,Function.comp_def,decode_mul]

theorem decode_mul_mixed (S T : ℤ) (a b : ℤ×ℤ) :
    decode (S*T) (imul a b)=cqMul (decode S a) (decode T b) := by
  apply Prod.ext <;> simp [decode,imul,cqMul] <;> ring

/-- Upper-bound one weighted positive term before summing on a shared grid. -/
theorem rounded_term_sum (xs : List ℕ) (t : ℕ → ℚ) (a : ℕ → ℤ) (S : ℤ)
    (h : ∀ i ∈ xs, t i ≤ (a i:ℚ)/(S:ℚ)) :
    (xs.map t).sum ≤ (((xs.map a).sum:ℤ):ℚ)/(S:ℚ) := by
  rw [sum_cast_div,List.map_map]
  exact List.sum_le_sum (fun i hi => h i hi)

def iconvError (xs : List ℕ) (a b : ℕ → ℤ×ℤ) (ea eb : ℕ → ℤ) : ℤ :=
  (xs.map (fun i : ℕ => il1 (a i)*eb i+il1 (b i)*ea i+ea i*eb i)).sum

theorem iconv_close (S : ℤ) (hS : 0 < S) (xs : List ℕ)
    (A B : ℕ → CQ) (a b : ℕ → ℤ×ℤ) (ea eb : ℕ → ℤ)
    (ha : ∀ i ∈ xs, Close (A i) (decode S (a i)) ((ea i:ℚ)/(S:ℚ)))
    (hb : ∀ i ∈ xs, Close (B i) (decode S (b i)) ((eb i:ℚ)/(S:ℚ))) :
    Close (cqSum (xs.map (fun i : ℕ => cqMul (A i) (B i))))
      (decode (S*S) (iconv xs a b)) ((iconvError xs a b ea eb:ℚ)/((S*S:ℤ):ℚ)) := by
  have hs : (S:ℚ) ≠ 0 := by exact_mod_cast hS.ne'
  have h := close_sum xs (fun i : ℕ => cqMul (A i) (B i))
    (fun i : ℕ => cqMul (decode S (a i)) (decode S (b i)))
    (fun i : ℕ => cqL1 (decode S (a i))*((eb i:ℚ)/(S:ℚ))+
      cqL1 (decode S (b i))*((ea i:ℚ)/(S:ℚ))+((ea i:ℚ)/(S:ℚ))*((eb i:ℚ)/(S:ℚ)))
    (fun i hi => close_mul (ha i hi) (hb i hi))
  rw [← decode_iconv] at h
  have he : (xs.map (fun i : ℕ => cqL1 (decode S (a i))*((eb i:ℚ)/(S:ℚ))+
      cqL1 (decode S (b i))*((ea i:ℚ)/(S:ℚ))+((ea i:ℚ)/(S:ℚ))*((eb i:ℚ)/(S:ℚ)))).sum=
      ((iconvError xs a b ea eb:ℤ):ℚ)/((S*S:ℤ):ℚ) := by
    unfold iconvError
    rw [sum_cast_div,List.map_map]
    apply congrArg List.sum
    apply List.map_congr_left
    intro i hi
    dsimp only [Function.comp_def]
    rw [l1_decode S (a i) hS,l1_decode S (b i) hS]
    push_cast
    field_simp [hs]
    <;> ring
  rw [he] at h
  exact h

def isub (a b : ℤ×ℤ) : ℤ×ℤ := (a.1-b.1,a.2-b.2)
def ilift (S : ℤ) (a : ℤ×ℤ) : ℤ×ℤ := (a.1*S,a.2*S)

theorem decode_sub (S : ℤ) (a b : ℤ×ℤ) :
    decode S (isub a b)=cqSub (decode S a) (decode S b) := by
  apply Prod.ext <;> dsimp [decode,isub,cqSub,cqAdd,cqNeg] <;> push_cast <;> ring

theorem decode_lift (S : ℤ) (a : ℤ×ℤ) (hs : S ≠ 0) :
    decode (S*S) (ilift S a)=decode S a := by
  have hsq : (S:ℚ) ≠ 0 := by exact_mod_cast hs
  apply Prod.ext <;> dsimp [decode,ilift] <;> push_cast <;> field_simp <;> ring

theorem iconv_sub_close (S : ℤ) (hS : 0 < S) (xs : List ℕ)
    (A B : ℕ → CQ) (a b : ℕ → ℤ×ℤ) (ea eb : ℕ → ℤ) (R : CQ) (r : ℤ×ℤ) (er : ℤ)
    (ha : ∀ i ∈ xs, Close (A i) (decode S (a i)) ((ea i:ℚ)/(S:ℚ)))
    (hb : ∀ i ∈ xs, Close (B i) (decode S (b i)) ((eb i:ℚ)/(S:ℚ)))
    (hr : Close R (decode S r) ((er:ℚ)/(S:ℚ))) :
    Close (cqSub (cqSum (xs.map (fun i : ℕ => cqMul (A i) (B i)))) R)
      (decode (S*S) (isub (iconv xs a b) (ilift S r)))
      (((iconvError xs a b ea eb+er*S:ℤ):ℚ)/((S*S:ℤ):ℚ)) := by
  have h := close_sub (iconv_close S hS xs A B a b ea eb ha hb) hr
  rw [← decode_lift S r hS.ne',← decode_sub] at h
  have hs : (S:ℚ) ≠ 0 := by exact_mod_cast hS.ne'
  convert h using 1
  push_cast
  field_simp
  <;> ring

theorem close_self (a : CQ) : Close a a 0 := by
  simp [Close,cqL1,cqSub,cqAdd,cqNeg]

theorem close_mul_left (g : CQ) {a b : CQ} {e : ℚ} (h : Close a b e) :
    Close (cqMul g a) (cqMul g b) (cqL1 g*e) := by
  simpa only [mul_zero,zero_mul,add_zero] using close_mul (close_self g) h

theorem close_mono {a b : CQ} {e f : ℚ} (h : Close a b e) (hef : e ≤ f) : Close a b f :=
  h.trans hef

theorem scaled_decode (S G j : ℤ) (g a : ℤ×ℤ) :
    cqScale (1/(j:ℚ)) (cqMul (decode G g) (decode (S*S) a))=
      cqScale (1/(S:ℚ)) (decode (j*S*G) (imul g a)) := by
  apply Prod.ext <;> simp [decode,imul,cqMul,cqScale] <;> ring

theorem scaled_error_bound (S G j E En : ℤ) (g : ℤ×ℤ)
    (hS : 0 < S) (hG : 0 < G) (hj : 0 < j)
    (hb : il1 g*En ≤ (E-2)*j*S*G) :
    |1/(j:ℚ)| *(cqL1 (decode G g)*((En:ℚ)/((S*S:ℤ):ℚ)))+2/(S:ℚ) ≤ (E:ℚ)/(S:ℚ) := by
  have hs : (0:ℚ)<(S:ℚ) := by exact_mod_cast hS
  have hg : (0:ℚ)<(G:ℚ) := by exact_mod_cast hG
  have hjq : (0:ℚ)<(j:ℚ) := by exact_mod_cast hj
  have hd := mul_pos (mul_pos hjq hs) hg
  have hbq : (il1 g:ℚ)*(En:ℚ) ≤ ((E:ℚ)-2)*(j:ℚ)*(S:ℚ)*(G:ℚ) := by exact_mod_cast hb
  have hc : ((il1 g:ℚ)*(En:ℚ))/((j:ℚ)*(S:ℚ)*(G:ℚ)) ≤ (E:ℚ)-2 := by
    apply (div_le_iff₀ hd).2
    nlinarith only [hbq]
  have hdiv := div_le_div_of_nonneg_right hc hs.le
  have heq : |1/(j:ℚ)| *(cqL1 (decode G g)*((En:ℚ)/((S*S:ℤ):ℚ)))=
      (((il1 g:ℚ)*(En:ℚ))/((j:ℚ)*(S:ℚ)*(G:ℚ)))/(S:ℚ) := by
    rw [abs_of_pos (one_div_pos.mpr hjq),l1_decode G g hG]
    push_cast
    field_simp [hs.ne',hg.ne',hjq.ne']
    <;> ring
  rw [heq]
  calc
    (((il1 g:ℚ)*(En:ℚ))/((j:ℚ)*(S:ℚ)*(G:ℚ)))/(S:ℚ)+2/(S:ℚ)
        ≤ ((E:ℚ)-2)/(S:ℚ)+2/(S:ℚ) := add_le_add hdiv le_rfl
    _ = (E:ℚ)/(S:ℚ) := by ring

theorem rounded_scaled_close (S G j E En : ℤ) (g a : ℤ×ℤ) (A : CQ)
    (hS : 0 < S) (hG : 0 < G) (hj : 0 < j)
    (ha : Close A (decode (S*S) a) ((En:ℚ)/((S*S:ℤ):ℚ)))
    (hb : il1 g*En ≤ (E-2)*j*S*G) :
    Close (cqScale (1/(j:ℚ)) (cqMul (decode G g) A))
      (decode S ((imul g a).1/(j*S*G),(imul g a).2/(j*S*G))) ((E:ℚ)/(S:ℚ)) := by
  have hd : j*S*G ≠ 0 := ne_of_gt (mul_pos (mul_pos hj hS) hG)
  have h0 := close_scale (1/(j:ℚ)) (close_mul_left (decode G g) ha)
  rw [scaled_decode] at h0
  have h1 := grid_ediv_close S (j*S*G) (imul g a) hS hd
  exact close_mono (close_trans h0 h1) (scaled_error_bound S G j E En g hS hG hj hb)

#print axioms rounded_scaled_close
#print axioms iconv_close
#print axioms iconv_sub_close
#print axioms close_sum
#print axioms close_mul
#print axioms close_scale
#print axioms close_re
#print axioms l1_decode
#print axioms decode_iconv
#print axioms rounded_term_sum
#print axioms decode_mul
#print axioms decode_sum
#print axioms grid_ediv_close
theorem coeffEnclosed_of_close (S a e : ℤ) (q : CQ) (im : ℤ) (hS : 0<S)
    (h : Close q (decode S (a,im)) ((e:ℚ)/(S:ℚ))) :
    coeffEnclosed S a e (q.1,q.1)=true := by
  have hs : (0:ℚ)<(S:ℚ) := by exact_mod_cast hS
  have hn := close_nonneg h
  have heq : (0:ℚ)≤(e:ℚ) := by
    have hh := mul_nonneg hn hs.le
    simpa only [div_mul_cancel₀ _ hs.ne'] using hh
  have he : (0:ℤ)≤e := by exact_mod_cast heq
  have hr := close_re h
  change |q.1-(a:ℚ)/(S:ℚ)|≤(e:ℚ)/(S:ℚ) at hr
  have hb := abs_le.mp hr
  simp only [coeffEnclosed,decide_eq_true_eq]
  refine ⟨he,?_,?_⟩ <;> push_cast <;> simp only [sub_div,add_div] <;> linarith

theorem coefficientCheck_of_rounded (S : ℤ) (m : CompiledModel) (w : CellWitness)
    (hS : 0<S) (hl : m.coeff.length=w.coeff.length)
    (he : w.error.length=w.coeff.length) (q : ℕ→CQ)
    (hcheck : ∀ j<m.coeff.length,
      (seGet m.coeff j).check=some ((q j).1,(q j).1))
    (hr : ∀ j<m.coeff.length,
      Close (q j) (decode S (getI w.coeff j,0)) ((getI w.error j:ℚ)/(S:ℚ))) :
    coefficientCheck S m w=true := by
  simp only [coefficientCheck,Bool.and_eq_true,decide_eq_true_eq]
  refine ⟨⟨hS,hl,he⟩,?_⟩
  apply List.all_eq_true.mpr
  intro j hj
  have hj' := List.mem_range.mp hj
  rw [hcheck j hj']
  exact coeffEnclosed_of_close S (getI w.coeff j) (getI w.error j) (q j) 0 hS (hr j hj')

#print axioms coeffEnclosed_of_close
#print axioms coefficientCheck_of_rounded
/-- Input rounding and short integer convolution bound the original frozen coefficient. -/
theorem segCoeff_close (d : QSegment) (φ e : CQ) (j : ℕ) (hj : 0<j)
    (S G E : ℤ) (hS : 0<S) (hG : 0<G) (g : ℤ×ℤ)
    (a b : ℕ→ℤ×ℤ) (ea eb : ℕ→ℤ) (r : ℤ×ℤ) (er : ℤ)
    (hg : decode G g=cqDiv e d.half)
    (ha : ∀ i∈List.range j, Close
      (qShiftCoeff d.density (cqScale (1/2) (cqAdd φ (cqInv φ))) (cqDiv e d.half) i)
      (decode S (a i)) ((ea i:ℚ)/(S:ℚ)))
    (hb : ∀ i∈List.range j, Close
      (yPair (cqScale (1/2) (cqAdd φ (cqInv φ))) (cqDiv e d.half)
        (cqScale (1/2) (cqSub φ (cqInv φ))) (j-1-i)).2
      (decode S (b i)) ((eb i:ℚ)/(S:ℚ)))
    (hr : Close
      (qShiftCoeff d.quotDensity (cqScale (1/2) (cqAdd φ (cqInv φ))) (cqDiv e d.half) (j-1))
      (decode S r) ((er:ℚ)/(S:ℚ)))
    (herr : il1 g*(iconvError (List.range j) a b ea eb+er*S)≤(E-2)*(j:ℤ)*S*G) :
    let acc := isub (iconv (List.range j) a b) (ilift S r)
    Close (segCoeff d φ e j)
      (decode S ((imul g acc).1/((j:ℤ)*S*G),(imul g acc).2/((j:ℤ)*S*G)))
      ((E:ℚ)/(S:ℚ)) := by
  let ζ := cqScale (1/2) (cqAdd φ (cqInv φ))
  let γ := cqDiv e d.half
  let q := cqScale (1/2) (cqSub φ (cqInv φ))
  have h := iconv_sub_close S hS (List.range j)
    (fun i => qShiftCoeff d.density ζ γ i)
    (fun i => (yPair ζ γ q (j-1-i)).2) a b ea eb
    (qShiftCoeff d.quotDensity ζ γ (j-1)) r er ha hb hr
  have hjz : (0:ℤ)<(j:ℤ) := by exact_mod_cast hj
  have hh := rounded_scaled_close S G (j:ℤ) E
    (iconvError (List.range j) a b ea eb+er*S) g
    (isub (iconv (List.range j) a b) (ilift S r)) _ hS hG hjz h herr
  rw [hg] at hh
  have hlen : j-1+1=j := Nat.sub_add_cancel hj
  simpa only [segCoeff,if_neg (ne_of_gt hj),hlen,ζ,γ,q,Int.cast_natCast] using hh

#print axioms segCoeff_close
theorem coefficientCheck_of_rounded_tail (S : ℤ) (m : CompiledModel) (w : CellWitness)
    (hS : 0<S) (hl : m.coeff.length=w.coeff.length)
    (he : w.error.length=w.coeff.length) (q : ℕ→CQ) (im : ℕ→ℤ)
    (hzero : (match (seGet m.coeff 0).check with
      | none => false | some b => coeffEnclosed S (getI w.coeff 0) (getI w.error 0) b)=true)
    (hcheck : ∀ j<m.coeff.length, 0<j →
      (seGet m.coeff j).check=some ((q j).1,(q j).1))
    (hr : ∀ j<m.coeff.length, 0<j →
      Close (q j) (decode S (getI w.coeff j,im j)) ((getI w.error j:ℚ)/(S:ℚ))) :
    coefficientCheck S m w=true := by
  simp only [coefficientCheck,Bool.and_eq_true,decide_eq_true_eq]
  refine ⟨⟨hS,hl,he⟩,?_⟩
  apply List.all_eq_true.mpr
  intro j hj
  have hj' := List.mem_range.mp hj
  by_cases hz : j=0
  · subst j; exact hzero
  · have hp : 0<j := Nat.pos_of_ne_zero hz
    rw [hcheck j hj' hp]
    exact coeffEnclosed_of_close S (getI w.coeff j) (getI w.error j) (q j) (im j) hS (hr j hj' hp)

#print axioms coefficientCheck_of_rounded_tail
/-- Direct transfer for the unchanged coefficient vector emitted by segDiscCompile. -/
theorem segDisc_coefficientCheck (d : QSegment) (φ e : CQ) (J terms : ℕ)
    (S : ℤ) (m : CompiledModel) (w : CellWitness) (im : ℕ→ℤ)
    (hS : 0<S) (hl : w.coeff.length=J+1) (he : w.error.length=J+1)
    (hm : m.coeff=(List.range (J+1)).map (fun j : ℕ =>
      if j=0 then segConstant terms d φ else seRat (segCoeff d φ e j).1))
    (hseed : (match (segConstant terms d φ).check with
      | none => false | some b => coeffEnclosed S (getI w.coeff 0) (getI w.error 0) b)=true)
    (hround : ∀ j, 0<j → j≤J →
      Close (segCoeff d φ e j) (decode S (getI w.coeff j,im j))
        ((getI w.error j:ℚ)/(S:ℚ))) : coefficientCheck S m w=true := by
  have hmLen : m.coeff.length=J+1 := by simp only [hm,List.length_map,List.length_range]
  apply coefficientCheck_of_rounded_tail S m w hS (hmLen.trans hl.symm) (he.trans hl.symm)
    (fun j => segCoeff d φ e j) im
  · simpa [hm,seGet] using hseed
  · intro j hj hp
    have hlt : j<J+1 := by simpa only [hmLen] using hj
    simp [hm,seGet,hlt,ne_of_gt hp,seRat,ScalarExpr.check]
  · intro j hj hp
    exact hround j hp (by omega)

#print axioms segDisc_coefficientCheck
theorem weighted_l1_bound (xs : List ℕ) (weight : ℕ→ℚ) (A : ℕ→CQ)
    (B : ℕ→CQ) (err : ℕ→ℚ)
    (hw : ∀ i∈xs, 0≤weight i) (hc : ∀ i∈xs, Close (A i) (B i) (err i)) :
    (xs.map (fun i => weight i*cqL1 (A i))).sum≤
      (xs.map (fun i => weight i*(cqL1 (B i)+err i))).sum := by
  induction xs with
  | nil => simp
  | cons i xs ih =>
    have hi := mul_le_mul_of_nonneg_left (close_l1 (hc i (by simp))) (hw i (by simp))
    have ht := ih (fun j hj => hw j (by simp [hj])) (fun j hj => hc j (by simp [hj]))
    simpa only [List.map_cons,List.sum_cons] using add_le_add hi ht

theorem weighted_l1_nonneg (xs : List ℕ) (weight : ℕ→ℚ) (A : ℕ→CQ)
    (hw : ∀ i∈xs, 0≤weight i) :
    0≤(xs.map (fun i => weight i*cqL1 (A i))).sum := by
  induction xs with
  | nil => simp
  | cons i xs ih =>
    have hi := mul_nonneg (hw i (by simp)) (l1_nonneg (A i))
    have ht := ih (fun j hj => hw j (by simp [hj]))
    simpa only [List.map_cons,List.sum_cons] using add_nonneg hi ht

theorem boxMul_nonneg_scale (c : ℚ) (b : QBox) (hc : 0≤c) (hb : b.1≤b.2) :
    boxMul (c,c) b=(c*b.1,c*b.2) := by
  have hh := mul_le_mul_of_nonneg_left hb hc
  simp [boxMul,min_eq_left hh,max_eq_right hh,min_eq_right hh,max_eq_left hh]

/-- Rounding debits dominate the original displacement and original remainder Boolean. -/
theorem remainderCheck_of_rounded (S : ℤ) (rt : ℚ) (m : CompiledModel) (w : CellWitness)
    (Mc : SE) (b : QBox) (c δ : ℚ) (xs : List ℕ) (weight : ℕ→ℚ)
    (A B : ℕ→CQ) (err : ℕ→ℚ)
    (hMc : Mc.check=some b) (hb : b.1≤b.2) (hb0 : 0≤b.1)
    (hc : 0≤c) (hδ : 0≤δ) (hw : ∀ i∈xs, 0≤weight i)
    (hclose : ∀ i∈xs, Close (A i) (B i) (err i))
    (hm : m.error=seAdd (seScale c Mc)
      (seRat (δ*(xs.map (fun i => weight i*cqL1 (A i))).sum)))
    (hr : 0≤w.remainder)
    (hnum : c*b.2+δ*(xs.map (fun i => weight i*(cqL1 (B i)+err i))).sum+
      ((List.range w.error.length).map (fun j : ℕ =>
        (getI w.error j:ℚ)/(S:ℚ)*rt^j)).sum≤w.remainder) :
    remainderCheck S rt m w=true := by
  have hd := mul_le_mul_of_nonneg_left (weighted_l1_bound xs weight A B err hw hclose) hδ
  have hd0 := mul_nonneg hδ (weighted_l1_nonneg xs weight A hw)
  have hscale := boxMul_nonneg_scale c b hc hb
  have hcheck : m.error.check=some
      (c*b.1+δ*(xs.map (fun i => weight i*cqL1 (A i))).sum,
       c*b.2+δ*(xs.map (fun i => weight i*cqL1 (A i))).sum) := by
    simp only [hm,seAdd,seScale,seMul,seRat,ScalarExpr.check,hMc]
    simp [hscale,boxAdd]
  simp only [remainderCheck,hcheck,decide_eq_true_eq]
  exact ⟨add_nonneg (mul_nonneg hc hb0) hd0,hr,by linarith⟩

#print axioms weighted_l1_bound
#print axioms remainderCheck_of_rounded
end CatalanCore.Li2.DecayCert.Rounded
