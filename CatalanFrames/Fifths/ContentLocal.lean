module
public import CatalanFrames.Fifths.RationalData
public import CatalanFrames.Fifths.RootArithmetic
public import CatalanCore.Arith.Growth
public import CatalanCore.Arith.Hybrid.SingLev
@[expose] public section
open Finset Classical CatalanCore CatalanCore.Arith CatalanCore.Basic
namespace CatalanFrames.Fifths
section Local
variable {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u)
include T in
lemma fifthsMn_lt {a b : ℕ} (hab : a < b) :
    Fr.Mn a b = (1/25 : ℚ)*(1/((b : ℚ)-a))*∑ k ∈ Ioc a b,Fr.Delta k := by
  unfold Frame.Mn
  rw [if_neg hab.ne,max_eq_right hab.le,min_eq_left hab.le,T.norm_eq]
  norm_num
include T in
lemma fifthsMn_diag (a : ℕ) : Fr.Mn a a = -((1/25 : ℚ)*∑ k ∈ Icc 1 a,Fr.Dsq k) := by
  unfold Frame.Mn
  rw [if_pos rfl,T.norm_eq]
  norm_num <;> ring
lemma fifthsMn_symm (a b : ℕ) : Fr.Mn a b = Fr.Mn b a := by
  unfold Frame.Mn
  by_cases h : a=b
  · subst h; rfl
  · rw [if_neg h,if_neg (Ne.symm h),max_comm,min_comm]
variable (p : ℕ) [Fact p.Prime]
lemma fifthsPower_mem {N n : ℕ} (hn : 0<n) (hv : n.factorization p ≤ N) :
    ((p : ℚ)^N/(n : ℚ)) ∈ LocRing p := by
  have h := div_mem_locRing (p := p) (n := n) (W := p^N) hn (Nat.pow_dvd_pow p hv)
  simpa using h
lemma fifthsPower_mem' {n h : ℕ} (hn : 0<n) (hnh : n ≤ 5*h) :
    ((p : ℚ)^Nat.log p (5*h)/(n : ℚ)) ∈ LocRing p :=
  fifthsPower_mem p hn (Nat.le_log_of_pow_le (Fact.out : p.Prime).one_lt
    (le_trans (Nat.ordProj_le p hn.ne') hnh))
lemma five_mem : (5 : ℚ) ∈ LocRing p := by
  exact_mod_cast int_mem_locRing (ℓ := p) (5 : ℤ)
include T in
lemma fifthsOff_mem {h a b : ℕ} (hab : a<b) (hbh : b<h) :
    ((p : ℚ)^Nat.log p (5*h))^2*(25*Fr.Mn a b) ∈ LocRing p := by
  set v : ℚ := (p : ℚ)^Nat.log p (5*h) with hv
  have hu := T.hu1
  have hs : ∑ k ∈ Ioc a b,Fr.Delta k =
      ∑ k ∈ Ioc a b,(1/(k : ℚ)-5/((5*k-u : ℕ) : ℚ)) := by
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk0 : 0<k := by have := (Finset.mem_Ioc.mp hk).1;omega
    exact T.delta k hk0
  have e1 : ∑ k ∈ Ioc a b,(v/(k : ℚ)-5*(v/((5*k-u : ℕ) : ℚ))) =
      v*∑ k ∈ Ioc a b,(1/(k : ℚ)-5/((5*k-u : ℕ) : ℚ)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have key : v^2*(25*Fr.Mn a b) =
      (v/((b-a : ℕ) : ℚ))*∑ k ∈ Ioc a b,(v/(k : ℚ)-5*(v/((5*k-u : ℕ) : ℚ))) := by
    rw [e1,fifthsMn_lt T hab,hs,Nat.cast_sub hab.le]
    ring
  rw [key]
  apply (LocRing p).mul_mem
  · exact fifthsPower_mem' p (by omega) (by omega)
  · refine Subring.sum_mem _ fun k hk => ?_
    have hk' := Finset.mem_Ioc.mp hk
    apply (LocRing p).sub_mem (fifthsPower_mem' p (by omega) (by omega))
    exact (LocRing p).mul_mem (five_mem p) (fifthsPower_mem' p (by omega) (by omega))
include T in
lemma fifthsDiag_mem {h a : ℕ} (ha : a<h) :
    ((p : ℚ)^Nat.log p (5*h))^2*(25*Fr.Mn a a) ∈ LocRing p := by
  set v : ℚ := (p : ℚ)^Nat.log p (5*h) with hv
  have hu := T.hu1
  have hs : ∑ k ∈ Icc 1 a,Fr.Dsq k =
      ∑ k ∈ Icc 1 a,(1/(k : ℚ)^2-25/((5*k-u : ℕ) : ℚ)^2) := by
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk0 : 0<k := by have := (Finset.mem_Icc.mp hk).1;omega
    simpa only [Nat.cast_ofNat,show (5 : ℚ)^2=25 by norm_num] using T.dsq k hk0
  have e1 : ∑ k ∈ Icc 1 a,((v/(k : ℚ))^2-25*(v/((5*k-u : ℕ) : ℚ))^2) =
      v^2*∑ k ∈ Icc 1 a,(1/(k : ℚ)^2-25/((5*k-u : ℕ) : ℚ)^2) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have key : v^2*(25*Fr.Mn a a) =
      -∑ k ∈ Icc 1 a,((v/(k : ℚ))^2-25*(v/((5*k-u : ℕ) : ℚ))^2) := by
    rw [e1,fifthsMn_diag T,hs]
    ring
  rw [key]
  apply (LocRing p).neg_mem
  refine Subring.sum_mem _ fun k hk => ?_
  have hk' := Finset.mem_Icc.mp hk
  have h25 : (25 : ℚ) ∈ LocRing p := by
    exact_mod_cast int_mem_locRing (ℓ := p) (25 : ℤ)
  apply (LocRing p).sub_mem ((LocRing p).pow_mem (fifthsPower_mem' p (by omega) (by omega)) 2)
  exact (LocRing p).mul_mem h25 ((LocRing p).pow_mem
    (fifthsPower_mem' p (by omega) (by omega)) 2)
include T in
lemma fifthsNorm_mem {h a b : ℕ} (ha : a<h) (hb : b<h) :
    ((p : ℚ)^Nat.log p (5*h))^2*(25*Fr.Mn a b) ∈ LocRing p := by
  rcases lt_trichotomy a b with hab|rfl|hba
  · exact fifthsOff_mem T p hab hb
  · exact fifthsDiag_mem T p ha
  · rw [fifthsMn_symm]
    exact fifthsOff_mem T p hba ha
end Local
lemma small5_pos (h : ℕ) : 0<small5 h := by unfold small5;positivity
/-- The complete bad-prime localization proof at all2,3,5, including the norm25 factor. -/
theorem small5_ok {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (p : ℕ) [Fact p.Prime]
    (hp : p ∈ badPrimes) (h a b : ℕ) (ha : a<h) (hb : b<h) :
    ((small5 h : ℕ) : ℚ)^2*Fr.Mn a b ∈ LocRing p := by
  have hdiv : 5*p^Nat.log p (5*h) ∣ small5 h := by
    simp only [badPrimes,Finset.mem_insert,Finset.mem_singleton] at hp
    rcases hp with rfl|rfl|rfl
    · refine ⟨3^Nat.log 3 (5*h)*5^Nat.log 5 (5*h),?_⟩
      unfold small5
      ring
    · refine ⟨2^Nat.log 2 (5*h)*5^Nat.log 5 (5*h),?_⟩
      unfold small5
      ring
    · refine ⟨2^Nat.log 2 (5*h)*3^Nat.log 3 (5*h),?_⟩
      unfold small5
      ring
  obtain ⟨d,hd⟩ := hdiv
  have he : ((small5 h : ℕ) : ℚ)^2*Fr.Mn a b =
      (d : ℚ)^2*(((p : ℚ)^Nat.log p (5*h))^2*(25*Fr.Mn a b)) := by
    rw [hd]
    push_cast
    ring
  rw [he]
  apply (LocRing p).mul_mem
  · apply (LocRing p).pow_mem
    exact_mod_cast int_mem_locRing (ℓ := p) (d : ℤ)
  · exact fifthsNorm_mem T p ha hb
end CatalanFrames.Fifths
set_option pp.fullNames true
#print axioms CatalanFrames.Fifths.small5_ok
#print axioms CatalanFrames.Fifths.fifthsNorm_mem
