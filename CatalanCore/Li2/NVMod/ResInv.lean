module
public import CatalanCore.Li2.NVMod.Formula
@[expose] public section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace CatalanCore.Li2.NVMod

structure PrimeInverseTable where
  values : List ℕ

def inverseTableCheck (p : ℕ) (C : PrimeInverseTable) : Bool :=
  C.values.length == p && (List.range p).all (fun i=>
    let v := C.values.getD i 0
    decide (v<p) && if i=0 then v==0 else (i*v)%p==1)

def inverseNat (p : ℕ) (C : PrimeInverseTable) (x : ℕ) : ℕ := C.values.getD (x%p) 0

theorem inverseTable_value (p : ℕ) [Fact p.Prime] (C : PrimeInverseTable)
    (h : inverseTableCheck p C=true) (i : ℕ) (hi : i<p) :
    C.values.getD i 0<p ∧ (C.values.getD i 0:ZMod p)=(i:ZMod p)⁻¹ := by
  have hh : C.values.length=p ∧ ∀ j<p,
      C.values.getD j 0<p ∧ (if j=0 then C.values.getD j 0=0 else j*C.values.getD j 0%p=1) := by
    simpa [inverseTableCheck] using h
  have hb := hh.2 i hi
  refine ⟨hb.1,?_⟩
  by_cases hz : i=0
  · have hv : C.values.getD i 0=0 := by simpa only [hz,ite_true] using hb.2
    rw [hv,hz,Nat.cast_zero,inv_zero]
  · have hv : i*C.values.getD i 0%p=1 := by simpa only [if_neg hz] using hb.2
    have he := congrArg (fun n : ℕ=>(n:ZMod p)) hv
    have hpv : (i:ZMod p)≠0 := by
      intro heq
      have hh := congrArg ZMod.val heq
      rw [ZMod.val_natCast_of_lt hi,ZMod.val_zero] at hh
      exact hz hh
    have hm : (i:ZMod p)*(C.values.getD i 0:ZMod p)=1 := by
      simpa only [ZMod.natCast_mod,Nat.cast_mul,Nat.cast_one] using he
    exact eq_inv_of_mul_eq_one_right hm

theorem inverseNat_sound (p : ℕ) [Fact p.Prime] (C : PrimeInverseTable)
    (h : inverseTableCheck p C=true) (x : ℕ) :
    inverseNat p C x<p ∧ (inverseNat p C x:ZMod p)=(x:ZMod p)⁻¹ := by
  have hh := inverseTable_value p C h (x%p) (Nat.mod_lt _ (Fact.out : p.Prime).pos)
  simpa only [inverseNat,ZMod.natCast_mod] using hh

#print axioms inverseTable_value
#print axioms inverseNat_sound
end CatalanCore.Li2.NVMod
