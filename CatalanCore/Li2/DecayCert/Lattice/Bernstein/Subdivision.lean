module
public import CatalanCore.Li2.DecayCert.Lattice.Bernstein.Basis
public import CatalanCore.Li2.DecayCert.Lattice.Bernstein.Engine
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 600000
open scoped BigOperators
open CatalanCore.Uniform.Decay.Tools
namespace CatalanCore.Li2.DecayCert.BernsteinGrid

def bezier (n : ℕ) (b : ℕ→ℚ) (t : ℚ) : ℚ :=
  ∑ k ∈ Finset.range (n+1),b k*bw n k t

theorem bw_succ (n k : ℕ) (t : ℚ) :
    bw (n+1) k t=(1-t)*bw n k t+t*(if k=0 then 0 else bw n (k-1) t) := by
  cases k with
  | zero => simp [bw,pow_succ]; ring
  | succ k =>
    by_cases hk : k≤n
    · simp only [Nat.succ_ne_zero,ite_false,Nat.add_sub_cancel]
      unfold bw
      rw [Nat.choose_succ_succ,Nat.cast_add]
      by_cases he : k=n
      · subst k
        simp [pow_succ,mul_comm]
      · have hkn : k+1≤n := by omega
        rw [show n+1-(k+1)=n-(k+1)+1 by omega,pow_succ,
          show n-k=n-(k+1)+1 by omega,pow_succ]
        ring
    · have hkn : n<k := by omega
      simp [bw,Nat.choose_eq_zero_of_lt hkn,Nat.choose_eq_zero_of_lt (by omega : n<k+1),
        Nat.choose_eq_zero_of_lt (by omega : n+1<k+1)]

theorem bezier_rec (n : ℕ) (b : ℕ→ℚ) (t : ℚ) :
    bezier (n+1) b t=(1-t)*bezier n b t+t*bezier n (fun i=>b (i+1)) t := by
  unfold bezier
  simp_rw [bw_succ,mul_add]
  rw [Finset.sum_add_distrib]
  have hlo : (∑ k ∈ Finset.range (n+1+1),b k*((1-t)*bw n k t))=
      (1-t)*(∑ k ∈ Finset.range (n+1),b k*bw n k t) := by
    rw [Finset.sum_range_succ]
    simp only [bw,Nat.choose_succ_self,Nat.cast_zero,zero_mul,mul_zero,add_zero]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  have hhi : (∑ k ∈ Finset.range (n+1+1),b k*(t*(if k=0 then 0 else bw n (k-1) t)))=
      t*(∑ k ∈ Finset.range (n+1),b (k+1)*bw n k t) := by
    rw [Finset.sum_range_succ']
    simp only [Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,ite_false,Nat.add_sub_cancel,
      ite_true,mul_zero,add_zero]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [hlo,hhi]

def leftValue : ℕ→(ℕ→ℚ)→ℚ
  | 0,b => b 0
  | j+1,b => leftValue j (fun i=>(b i+b (i+1))/2)

theorem bezier_avg (n : ℕ) (b : ℕ→ℚ) (t : ℚ) :
    bezier n (fun i=>(b i+b (i+1))/2) t=
      (bezier n b t+bezier n (fun i=>b (i+1)) t)/2 := by
  unfold bezier
  rw [← Finset.sum_add_distrib,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k hk
  ring

theorem bezier_left (n : ℕ) (b : ℕ→ℚ) (t : ℚ) :
    bezier n (fun j=>leftValue j b) t=bezier n b (t/2) := by
  induction n generalizing b with
  | zero => simp [bezier,bw,leftValue]
  | succ n ih =>
    rw [bezier_rec,bezier_rec,ih]
    have hh : (fun i=>leftValue (i+1) b)=(fun i=>leftValue i (fun j=>(b j+b (j+1))/2)) := rfl
    rw [hh,ih,bezier_avg]
    ring

#print axioms bezier_rec
#print axioms bezier_left
def rightValue : ℕ→ℕ→(ℕ→ℚ)→ℚ
  | 0,k,b => b k
  | n+1,k,b => if k=n+1 then b k else rightValue n k (fun i=>(b i+b (i+1))/2)

theorem rightValue_shift (n k : ℕ) (hk : k≤n) (b : ℕ→ℚ) :
    rightValue (n+1) (k+1) b=rightValue n k (fun i=>b (i+1)) := by
  induction n generalizing k b with
  | zero =>
    have he : k=0 := by omega
    subst k
    simp [rightValue]
  | succ n ih =>
    by_cases he : k=n+1
    · subst k
      simp [rightValue]
    · have hkn : k≤n := by omega
      simp only [rightValue,show k+1≠n+1+1 by omega,show k≠n+1 by omega,ite_false]
      exact ih k hkn (fun i=>(b i+b (i+1))/2)

theorem bezier_right (n : ℕ) (b : ℕ→ℚ) (t : ℚ) :
    bezier n (fun j=>rightValue n j b) t=bezier n b ((1+t)/2) := by
  induction n generalizing b with
  | zero => simp [bezier,bw,rightValue]
  | succ n ih =>
    rw [bezier_rec,bezier_rec]
    have hp : bezier n (fun j=>rightValue (n+1) j b) t=
        bezier n (fun j=>rightValue n j (fun i=>(b i+b (i+1))/2)) t := by
      unfold bezier
      apply Finset.sum_congr rfl
      intro k hk
      dsimp only
      rw [rightValue,if_neg (by have := Finset.mem_range.mp hk;omega)]
    have ht : bezier n (fun j=>rightValue (n+1) (j+1) b) t=
        bezier n (fun j=>rightValue n j (fun i=>b (i+1))) t := by
      unfold bezier
      apply Finset.sum_congr rfl
      intro k hk
      dsimp only
      rw [rightValue_shift n k (by have := Finset.mem_range.mp hk;omega)]
    rw [hp,ht,ih,ih,bezier_avg]
    ring

theorem leftValue_congr (n : ℕ) (b c : ℕ→ℚ) (h : ∀i≤n,b i=c i) :
    leftValue n b=leftValue n c := by
  induction n generalizing b c with
  | zero => exact h 0 (by omega)
  | succ n ih =>
    apply ih
    intro i hi
    rw [h i (by omega),h (i+1) (by omega)]

theorem rightValue_congr (n k : ℕ) (hk : k≤n) (b c : ℕ→ℚ) (h : ∀i≤n,b i=c i) :
    rightValue n k b=rightValue n k c := by
  induction n generalizing b c with
  | zero => exact h k hk
  | succ n ih =>
    dsimp only [rightValue]
    split_ifs with he
    · exact h k hk
    · apply ih (by omega)
      intro i hi
      rw [h i (by omega),h (i+1) (by omega)]

theorem exactAvg_length (ys : List ℚ) : (exactAvg ys).length=ys.length-1 := by
  induction ys with
  | nil => rfl
  | cons a ys ih =>
    cases ys with
    | nil => rfl
    | cons b ys => simpa only [exactAvg,List.length_cons,Nat.succ_sub_one] using congrArg Nat.succ ih

theorem lget_exactAvg (ys : List ℚ) (i : ℕ) (hi : i+1<ys.length) :
    lget (exactAvg ys) i=(lget ys i+lget ys (i+1))/2 := by
  induction ys generalizing i with
  | nil => simp at hi
  | cons a ys ih =>
    cases ys with
    | nil => simp at hi
    | cons b ys =>
      cases i with
      | zero => rfl
      | succ i =>
        simpa only [exactAvg,lget,List.getElem?_cons_succ] using ih i (by simpa using hi)

theorem exactSplitFuel_length (n : ℕ) (ys : List ℚ) :
    (exactSplitFuel n ys).1.length=n ∧ (exactSplitFuel n ys).2.length=n := by
  induction n generalizing ys with
  | zero => exact ⟨rfl,rfl⟩
  | succ n ih =>
    have h := ih (exactAvg ys)
    dsimp only [exactSplitFuel]
    constructor
    · rw [List.length_cons,h.1]
    · rw [List.length_append,h.2]
      rfl

#print axioms bezier_right
#print axioms lget_exactAvg

theorem exactSplitFuel_left_get (n : ℕ) (ys : List ℚ) (hn : n≤ys.length)
    (k : ℕ) (hk : k<n) :
    lget (exactSplitFuel n ys).1 k=leftValue k (lget ys) := by
  induction n generalizing ys k with
  | zero => omega
  | succ n ih =>
    cases k with
    | zero => simpa only [exactSplitFuel,lget,List.getElem?_cons_zero,Option.getD_some,leftValue] using headD_eq_lget ys
    | succ k =>
      change lget (exactSplitFuel n (exactAvg ys)).1 k=leftValue k (fun i=>(lget ys i+lget ys (i+1))/2)
      rw [ih (exactAvg ys) (by rw [exactAvg_length];omega) k (by omega)]
      apply leftValue_congr
      intro i hi
      exact lget_exactAvg ys i (by omega)

theorem rightValue_diag (n : ℕ) (b : ℕ→ℚ) : rightValue n n b=b n := by
  cases n <;> simp [rightValue]

theorem lastD_eq_lget (ys : List ℚ) : ys.getLastD 0=lget ys (ys.length-1) := by
  simp only [List.getLastD_eq_getLast?,List.getLast?_eq_getElem?,lget]

theorem exactSplitFuel_right_get (n : ℕ) (ys : List ℚ) (hn : ys.length=n)
    (k : ℕ) (hk : k<n) :
    lget (exactSplitFuel n ys).2 k=rightValue (n-1) k (lget ys) := by
  induction n generalizing ys k with
  | zero => omega
  | succ n ih =>
    have hl := (exactSplitFuel_length n (exactAvg ys)).2
    by_cases he : k=n
    · subst k
      rw [Nat.add_sub_cancel,rightValue_diag]
      change ((exactSplitFuel n (exactAvg ys)).2++[ys.getLastD 0])[n]?.getD 0=lget ys n
      rw [List.getElem?_append_right (by omega),hl,Nat.sub_self,List.getElem?_cons_zero,Option.getD_some]
      simpa only [hn,Nat.add_sub_cancel] using lastD_eq_lget ys
    · have hk' : k<n := by omega
      change ((exactSplitFuel n (exactAvg ys)).2++[ys.getLastD 0])[k]?.getD 0=
        rightValue n k (lget ys)
      rw [List.getElem?_append_left (by omega)]
      change lget (exactSplitFuel n (exactAvg ys)).2 k=rightValue n k (lget ys)
      rw [ih (exactAvg ys) (by rw [exactAvg_length,hn];omega) k hk']
      cases n with
      | zero => omega
      | succ n =>
        rw [rightValue,if_neg he]
        apply rightValue_congr n k (by omega)
        intro i hi
        exact lget_exactAvg ys i (by omega)

theorem exactSplit_left_eval (n : ℕ) (ys : List ℚ) (hn : ys.length=n+1) (t : ℚ) :
    bezier n (lget (exactSplit ys).1) t=bezier n (lget ys) (t/2) := by
  rw [← bezier_left]
  unfold bezier
  apply Finset.sum_congr rfl
  intro k hk
  dsimp only
  rw [exactSplit,exactSplitFuel_left_get _ _ (by omega) k (by have := Finset.mem_range.mp hk;omega)]

theorem exactSplit_right_eval (n : ℕ) (ys : List ℚ) (hn : ys.length=n+1) (t : ℚ) :
    bezier n (lget (exactSplit ys).2) t=bezier n (lget ys) ((1+t)/2) := by
  rw [← bezier_right]
  unfold bezier
  apply Finset.sum_congr rfl
  intro k hk
  dsimp only
  rw [exactSplit,exactSplitFuel_right_get _ _ rfl k (by have := Finset.mem_range.mp hk;omega),hn,Nat.add_sub_cancel]

#print axioms exactSplit_left_eval
#print axioms exactSplit_right_eval

end CatalanCore.Li2.DecayCert.BernsteinGrid
