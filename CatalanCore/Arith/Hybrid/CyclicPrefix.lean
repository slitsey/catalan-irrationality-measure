module
public import CatalanCore.Arith.Hybrid.LemmaE.Harmonic
@[expose] public section
open Finset
namespace CatalanCore.Arith.Hybrid
variable {p : ℕ} [Fact p.Prime]

def cyclicPrefix (f : ZMod p→ZMod p) (a : ℕ) : ZMod p :=
  ∑k∈range a,f ((k+1:ℕ):ZMod p)

/-- A zero-mean residue function has a periodic discrete primitive. -/
theorem cyclicPrefix_add_period (f : ZMod p→ZMod p) (hf : (∑x:ZMod p,f x)=0) (a : ℕ) :
    cyclicPrefix f (a+p)=cyclicPrefix f a := by
  have hs : (∑k∈range p,f ((a+k+1:ℕ):ZMod p))=0 := by
    have H:=LemmaE.sum_range_cast p (fun x=>f (x+(a+1:ℕ)))
    have H':=Equiv.sum_comp (Equiv.addRight ((a+1:ℕ):ZMod p)) f
    simpa only [Nat.cast_add,Nat.cast_one,add_assoc,add_comm,add_left_comm] using H.trans (H'.trans hf)
  unfold cyclicPrefix
  rw [Finset.sum_range_add,hs,add_zero]

theorem cyclicPrefix_mod (f : ZMod p→ZMod p) (hf : (∑x:ZMod p,f x)=0) (a : ℕ) :
    cyclicPrefix f a=cyclicPrefix f (a%p) := by
  induction a using Nat.strong_induction_on with
  | h a ih =>
    by_cases ha : a<p
    · rw [Nat.mod_eq_of_lt ha]
    · have hp:=(Fact.out:p.Prime).pos
      have hpa : p≤a:=by omega
      calc
        cyclicPrefix f a=cyclicPrefix f ((a-p)+p) := by congr;omega
        _=cyclicPrefix f (a-p) := cyclicPrefix_add_period f hf _
        _=cyclicPrefix f ((a-p)%p) := ih _ (by omega)
        _=cyclicPrefix f (a%p) := by rw [←Nat.mod_eq_sub_mod hpa]

theorem cyclicPrefix_congr (f : ZMod p→ZMod p) (hf : (∑x:ZMod p,f x)=0)
    {a b : ℕ} (hab : a%p=b%p) : cyclicPrefix f a=cyclicPrefix f b := by
  rw [cyclicPrefix_mod f hf a,cyclicPrefix_mod f hf b,hab]

theorem reciprocal_difference_zero_mean (h : ZMod p) :
    (∑x:ZMod p,(x⁻¹-(x-h)⁻¹))=0 := by
  rw [Finset.sum_sub_distrib]
  have H:=Equiv.sum_comp (Equiv.subRight h) (fun x:ZMod p=>x⁻¹)
  change (∑x:ZMod p,(x-h)⁻¹)=∑x:ZMod p,x⁻¹ at H
  rw [H,sub_self]
end CatalanCore.Arith.Hybrid
