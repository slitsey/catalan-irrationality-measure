module
public import CatalanCore.Arith.Hybrid.RegularPoleSplit
public import CatalanCore.Arith.Hybrid.UniformEntries
@[expose] public section
open Finset CatalanCore
namespace CatalanCore.Arith.Hybrid
variable {p : ℕ} [Fact p.Prime]

lemma regularPrefix_eq_Icc (o : ℤ) (a : ℕ) :
    regularPrefix p o a=∑k∈Icc 1 a,regularDelta p o k := by
  have he : Icc 1 a=Ico 1 (a+1) := by ext k;simp only [mem_Icc,mem_Ico];omega
  rw [he,Finset.sum_Ico_eq_sum_range]
  simp [regularPrefix,add_comm]

lemma regularPrefix_sub (o : ℤ) {a b : ℕ} (hab : a≤b) :
    regularPrefix p o b-regularPrefix p o a=∑k∈Ioc a b,regularDelta p o k := by
  rw [regularPrefix_eq_Icc,regularPrefix_eq_Icc]
  have he (n : ℕ) : Icc 1 n=Ioc 0 n := by ext k;simp only [mem_Icc,mem_Ioc];omega
  rw [he,he,←Finset.sum_Ioc_consecutive _ (Nat.zero_le a) hab]
  ring

lemma good_regular_interval_zero (o : ℤ) (h4 : (4:ZMod p)≠0)
    {a b : ℕ} (hab : a≤b) (hc : a%p=b%p) :
    Good p (∑k∈Ioc a b,regularDelta p o k) 0 := by
  rw [←regularPrefix_sub o hab]
  exact good_regularPrefix_difference o h4 hc

noncomputable def regularLoewner (n : ℚ) (p : ℕ) (o : ℤ) (a b : ℕ) : ℚ :=
  if a=b then -(1/n)*∑k∈Icc 1 a,regularDsq p o k else
    (1/n)*(1/(((max a b:ℕ):ℚ)-((min a b:ℕ):ℚ)))*
      ∑k∈Ioc (min a b) (max a b),regularDelta p o k

lemma regularLoewner_symm (n : ℚ) (o : ℤ) (a b : ℕ) :
    regularLoewner n p o a b=regularLoewner n p o b a := by
  by_cases hab : a=b
  · subst b;rfl
  · simp only [regularLoewner,if_neg hab,if_neg (Ne.symm hab),min_comm,max_comm]

lemma good_scaled_regularLoewner_diagonal {n : ℚ} {nb : ZMod p}
    (hn : Good p n nb) (hnb : nb≠0) (o : ℤ) (a : ℕ) :
    Good p ((p:ℚ)*regularLoewner n p o a a) 0 := by
  have gs:=Good.sum (ℓ:=p) (Icc 1 a) (fun k=>regularDsq p o k)
    (fun k=>(((k:ZMod p)⁻¹)^2-16*((4*(k:ZMod p)-o)⁻¹)^2))
    (fun k _=>by simpa only [Int.cast_natCast] using good_regularDsq (p:=p) o (k:ℤ))
  have H:=((hn.inv hnb).neg.mul gs).ell_mul
  apply (H.congr' ?_)
  simp [regularLoewner,one_div]

lemma good_scaled_regularLoewner_ordered {n : ℚ} {nb : ZMod p}
    (hn : Good p n nb) (hnb : nb≠0) (o : ℤ) (h4 : (4:ZMod p)≠0)
    {a b : ℕ} (hab : a<b) (hb : b<p*p) (hc : a%p=b%p) :
    Good p ((p:ℚ)*regularLoewner n p o a b) 0 := by
  have gd:=good_scaled_inverse (p:=p) (n:=b-a) (by omega) (by omega)
  have gs:=good_regular_interval_zero o h4 hab.le hc
  have H:=((hn.inv hnb).mul gd).mul gs
  have H' : Good p (n⁻¹*((p:ℚ)/((b-a:ℕ):ℚ))*∑k∈Ioc a b,regularDelta p o k) 0 := by
    simpa only [mul_zero] using H
  apply (H'.congr' ?_)
  rw [regularLoewner,if_neg hab.ne,min_eq_left hab.le,max_eq_right hab.le]
  rw [Nat.cast_sub hab.le]
  simp only [div_eq_mul_inv]
  ring

/-- The same-residue regular part starts at order p^2 in the scaled core.
This is the stronger stationarity needed at the next determinant level. -/
theorem good_scaled_regularLoewner_same_class {n : ℚ} {nb : ZMod p}
    (hn : Good p n nb) (hnb : nb≠0) (o : ℤ) (h4 : (4:ZMod p)≠0)
    {a b : ℕ} (ha : a<p*p) (hb : b<p*p) (hc : a%p=b%p) :
    Good p ((p:ℚ)*regularLoewner n p o a b) 0 := by
  rcases lt_trichotomy a b with h|rfl|h
  · exact good_scaled_regularLoewner_ordered hn hnb o h4 h hb hc
  · exact good_scaled_regularLoewner_diagonal hn hnb o a
  · rw [regularLoewner_symm]
    exact good_scaled_regularLoewner_ordered hn hnb o h4 h ha hc.symm

end CatalanCore.Arith.Hybrid
