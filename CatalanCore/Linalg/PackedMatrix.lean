module
public import Mathlib.Data.Nat.Digits.Lemmas
public import Mathlib.Data.List.GetD
public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public meta import Lean.Elab.Tactic.Omega

@[expose] public section
open scoped BigOperators
open Polynomial Finset
namespace CatalanCore.Linalg.PackedMatrix

/-- Strict normalization at kernel arithmetic boundaries. -/
def forceNat {α : Type} (n : ℕ) (k : ℕ→α) : α :=
  match n with | 0 => k 0 | m+1 => k (m+1)

theorem forceNat_eq {α : Type} (n : ℕ) (k : ℕ→α) : forceNat n k=k n := by
  cases n <;> rfl

def packNatAux (R : ℕ) : List ℕ→ℕ
  | [] => 0
  | x::xs => forceNat (packNatAux R xs) fun v => forceNat (R*v) fun w => x+w

def packNat (R : ℕ) (xs : List ℕ) : ℕ := forceNat R fun R => packNatAux R xs

theorem packNat_eq_ofDigits (R : ℕ) (xs : List ℕ) : packNat R xs=Nat.ofDigits R xs := by
  have h : ∀ xs, packNatAux R xs=Nat.ofDigits R xs := by
    intro xs
    induction xs with
    | nil => rfl
    | cons x xs ih => simp only [packNatAux,forceNat_eq,ih,Nat.ofDigits,Nat.cast_id]
  simp only [packNat,forceNat_eq,h]

def wordProductDigit (R D a b : ℕ) : ℕ :=
  forceNat R fun R => forceNat D fun D => forceNat a fun a => forceNat b fun b =>
    forceNat (a*b) fun p => forceNat (p/D) fun q => q%R

theorem wordProductDigit_eq (R D a b : ℕ) : wordProductDigit R D a b=(a*b)/D%R := by
  simp only [wordProductDigit,forceNat_eq]

private theorem head_drop_getD (xs : List ℕ) (i : ℕ) : (xs.drop i).head!=xs.getD i 0 := by
  induction xs generalizing i with
  | nil => simp
  | cons x xs ih => cases i <;> simp [ih]

private theorem ofDigits_digit (R : ℕ) (hR : 0<R) (xs : List ℕ)
    (hb : ∀ x∈xs,x<R) (i : ℕ) : Nat.ofDigits R xs/R^i%R=xs.getD i 0 := by
  rw [Nat.ofDigits_div_pow_eq_ofDigits_drop i hR xs hb,Nat.ofDigits_mod_eq_head!,head_drop_getD]
  apply Nat.mod_eq_of_lt
  by_cases hi : i<xs.length
  · rw [List.getD_eq_getElem xs 0 hi]
    exact hb _ (List.getElem_mem hi)
  · rw [List.getD_eq_default xs 0 (by omega)]
    exact hR

private noncomputable def digitsPoly (xs : List ℕ) : ℕ[X] := Nat.ofDigits (X : ℕ[X]) xs

private theorem digitsPoly_coeff (xs : List ℕ) (i : ℕ) :
    (digitsPoly xs).coeff i=xs.getD i 0 := by
  induction xs generalizing i with
  | nil => simp [digitsPoly,Nat.ofDigits]
  | cons x xs ih =>
    cases i with
    | zero => simp [digitsPoly,Nat.ofDigits]
    | succ i => simpa only [digitsPoly,Nat.ofDigits,Polynomial.coeff_add,
        Polynomial.coeff_natCast_ite,if_neg (by omega : i+1≠0),zero_add,Polynomial.coeff_X_mul,
        List.getD_cons_succ,Nat.cast_id] using ih i

private theorem digitsPoly_eval (R : ℕ) (xs : List ℕ) :
    (digitsPoly xs).eval R=Nat.ofDigits R xs := by
  induction xs with
  | nil => simp [digitsPoly,Nat.ofDigits]
  | cons x xs ih => simpa only [digitsPoly,Nat.ofDigits,Polynomial.eval_add,
      Polynomial.eval_natCast,Polynomial.eval_mul,Polynomial.eval_X,Nat.cast_id] using congrArg (fun v => x+R*v) ih

private theorem coeff_le_eval_one (p : ℕ[X]) (i : ℕ) : p.coeff i≤p.eval 1 := by
  by_cases hi : i≤p.natDegree
  · rw [Polynomial.eval_eq_sum_range]
    simp only [one_pow,mul_one]
    exact Finset.single_le_sum (fun j _ => Nat.zero_le (p.coeff j)) (Finset.mem_range.mpr (by omega))
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
    exact Nat.zero_le _

private theorem polynomial_digit (R : ℕ) (hR : 0<R) (p : ℕ[X])
    (hb : ∀ i,p.coeff i<R) (i : ℕ) : p.eval R/R^i%R=p.coeff i := by
  let N := p.natDegree+i+2
  let xs := (List.range N).map p.coeff
  have hcoeff (j : ℕ) : xs.getD j 0=p.coeff j := by
    by_cases hj : j<N
    · rw [List.getD_eq_getElem xs 0 (by simpa [xs] using hj)]
      simp only [xs,List.getElem_map,List.getElem_range]
    · rw [List.getD_eq_default xs 0 (by simp only [xs,List.length_map,List.length_range];omega)]
      exact (Polynomial.coeff_eq_zero_of_natDegree_lt (by dsimp [N] at hj;omega)).symm
  have hp : digitsPoly xs=p := by
    ext j
    rw [digitsPoly_coeff,hcoeff]
  have he : Nat.ofDigits R xs=p.eval R := by rw [← digitsPoly_eval R xs,hp]
  rw [← he,ofDigits_digit R hR xs ?_,hcoeff]
  intro x hx
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hx
  exact hb j

/-- A central coefficient of a packed product is the dot product, provided
its coefficient carry bound follows from the two checked l1 sums. -/
theorem packed_dot (R n : ℕ) (hR : 0<R) (hn : 0<n) (a b : List ℕ)
    (ha : a.length=n) (hb : b.length=n) (hcarry : a.sum*b.sum<R) :
    (packNat R a*packNat R b.reverse)/R^(n-1)%R =
      ∑ i∈Finset.range n,a.getD i 0*b.getD i 0 := by
  let p := digitsPoly a
  let q := digitsPoly b.reverse
  have hcoef (i : ℕ) : (p*q).coeff i<R := by
    apply lt_of_le_of_lt (coeff_le_eval_one (p*q) i)
    simpa only [Polynomial.eval_mul,p,q,digitsPoly_eval,Nat.ofDigits_one,List.sum_reverse] using hcarry
  have hd := polynomial_digit R hR (p*q) hcoef (n-1)
  rw [Polynomial.eval_mul,digitsPoly_eval,digitsPoly_eval] at hd
  rw [packNat_eq_ofDigits,packNat_eq_ofDigits,hd,Polynomial.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  have hn1 : n-1+1=n := by omega
  change (∑ k∈Finset.range (n-1+1),p.coeff k*q.coeff (n-1-k))= _
  rw [hn1]
  apply Finset.sum_congr rfl
  intro i hi
  rw [digitsPoly_coeff,digitsPoly_coeff]
  have hir : n-1-i<b.length := by have := Finset.mem_range.mp hi;omega
  rw [List.getD_reverse (n-1-i) hir]
  congr 1
  congr 1
  have := Finset.mem_range.mp hi
  omega

/-- Runtime words and their denominator are literals. Their shared semantic
bindings and carry bounds are consumed here, without recomputing packing. -/
theorem word_dot_of_bounds (R D n SU SV wa wb : ℕ) (a b : List ℕ)
    (hR : 0<R) (hn : 0<n) (ha : a.length=n) (hb : b.length=n)
    (hsa : a.sum≤SU) (hsb : b.sum≤SV) (hcarry : SU*SV<R)
    (hD : D=R^(n-1)) (hwa : packNat R a=wa) (hwb : packNat R b.reverse=wb) :
    wordProductDigit R D wa wb=∑ i∈Finset.range n,a.getD i 0*b.getD i 0 := by
  rw [wordProductDigit_eq,hD,← hwa,← hwb]
  exact packed_dot R n hR hn a b ha hb ((Nat.mul_le_mul hsa hsb).trans_lt hcarry)

theorem word_dot_mod (p R D n SU SV wa wb : ℕ) (a b : List ℕ)
    (hR : 0<R) (hn : 0<n) (ha : a.length=n) (hb : b.length=n)
    (hsa : a.sum≤SU) (hsb : b.sum≤SV) (hcarry : SU*SV<R)
    (hD : D=R^(n-1)) (hwa : packNat R a=wa) (hwb : packNat R b.reverse=wb) :
    (wordProductDigit R D wa wb : ZMod p)=
      ∑ i∈Finset.range n,(a.getD i 0:ZMod p)*(b.getD i 0:ZMod p) := by
  rw [word_dot_of_bounds R D n SU SV wa wb a b hR hn ha hb hsa hsb hcarry hD hwa hwb]
  simp only [Nat.cast_sum,Nat.cast_mul]

/-! Arbitrary-radix balanced signed pack/unpack. These are the odd-radix
versions of ColCert.Pack's two generic uniqueness/specification lemmas.
No analytic producer or data closure is imported. -/
def signedPack (R : ℤ) : List ℤ→ℤ
  | [] => 0
  | a::xs => a+R*signedPack R xs

def signedUnpack (R H : ℤ) : ℕ→ℤ→List ℤ×ℤ
  | 0,x => ([],x)
  | n+1,x =>
    let d := (x+H)%R-H
    let r := signedUnpack R H n ((x-d)/R)
    (d::r.1,r.2)

def DigitRange (R H a : ℤ) : Prop := -H≤a ∧ a<R-H

theorem signed_unpack_spec (R H : ℤ) (hR : 0<R) : ∀ (n : ℕ) (x : ℤ),
    x=signedPack R (signedUnpack R H n x).1+R^n*(signedUnpack R H n x).2 ∧
      ∀ a∈(signedUnpack R H n x).1,DigitRange R H a
  | 0,x => by simp [signedUnpack,signedPack]
  | n+1,x => by
    obtain ⟨h1,h2⟩ := signed_unpack_spec R H hR n ((x-((x+H)%R-H))/R)
    let d := (x+H)%R-H
    have hd : R∣x-d := by
      refine ⟨(x+H)/R,?_⟩
      dsimp [d]
      rw [Int.emod_def]
      ring
    have he : x-d=R*((x-d)/R) := (Int.mul_ediv_cancel' hd).symm
    refine ⟨?_,?_⟩
    · simp only [signedUnpack,signedPack]
      change x=d+R*signedPack R (signedUnpack R H n ((x-d)/R)).1+
        R^(n+1)*(signedUnpack R H n ((x-d)/R)).2
      rw [pow_succ']
      calc
        x=d+(x-d) := by ring
        _ = d+R*((x-d)/R) := by rw [← he]
        _ = _ := by
          conv_lhs => rw [h1]
          ring
    · intro a ha
      simp only [signedUnpack,List.mem_cons] at ha
      rcases ha with rfl | ha
      · have h0 := Int.emod_nonneg (x+H) hR.ne'
        have hlt := Int.emod_lt_of_pos (x+H) hR
        dsimp [DigitRange]
        omega
      · exact h2 a ha

theorem signed_pack_inj (R H : ℤ) (hR : 0<R) : ∀ (a b : List ℤ),
    (∀ x∈a,DigitRange R H x) → (∀ x∈b,DigitRange R H x) →
    a.length=b.length → signedPack R a=signedPack R b → a=b
  | [],[],_,_,_,_ => rfl
  | [],_::_,_,_,h,_ => by simp at h
  | _::_,[],_,_,h,_ => by simp at h
  | a::as,b::bs,ha,hb,hlen,hp => by
    have hA := ha a (by simp)
    have hB := hb b (by simp)
    simp only [signedPack] at hp
    have hdiv : R∣a-b := ⟨signedPack R bs-signedPack R as,by rw [mul_sub];linarith⟩
    have hab : |a-b|<R := by
      rw [abs_lt]
      dsimp [DigitRange] at hA hB
      constructor <;> omega
    have he := Int.eq_zero_of_abs_lt_dvd hdiv hab
    have heq : a=b := by omega
    subst b
    have ht : signedPack R as=signedPack R bs := by
      exact mul_left_cancel₀ hR.ne' (by linarith [hp])
    have htail := signed_pack_inj R H hR as bs
      (fun x hx => ha x (by simp [hx])) (fun x hx => hb x (by simp [hx]))
      (by simpa using hlen) ht
    rw [htail]

#print axioms word_dot_of_bounds
#print axioms word_dot_mod
#print axioms signed_unpack_spec
#print axioms signed_pack_inj
end CatalanCore.Linalg.PackedMatrix
