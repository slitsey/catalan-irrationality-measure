module
public import CatalanMeasure.GenD.Uniform.Prefix.EndpointModes
public import CatalanMeasure.GenD.Uniform.Prefix.NativeSlots
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Tactic.Abel
@[expose] public section
set_option Elab.async false
namespace CatalanMeasure.GenD.Uniform.Prefix
open Polynomial Polynomial.Chebyshev
variable {K : Type*} [Field K]
noncomputable section

def nativeA (h : Nat) (a0 : K) (a : Fin h → K) : K[X] :=
  a0 • U K ((2*h : Nat) : Int)+∑ j : Fin h,
    a j • (U K (j.val : Int)+U K ((2*h-j.val-1 : Nat) : Int))
def nativeC (h : Nat) (c : Fin h → K) : K[X] :=
  ∑ j : Fin h, c j • (U K (j.val : Int)-U K ((2*h-j.val-1 : Nat) : Int))
def modeCoefficients {h : Nat} (c0 : K) (lo hi : Fin h → K) : EndpointModes h → K
  | none => c0
  | some (.inl j) => lo j
  | some (.inr j) => hi j

theorem mode_sum (h : Nat) (c0 : K) (lo hi : Fin h → K) :
    (∑ i, modeCoefficients c0 lo hi i • endpointMode (K := K) i)=
      c0 • U K ((2*h : Nat) : Int)+(∑ j,lo j • U K (j.val : Int))+
        ∑ j,hi j • U K ((2*h-j.val-1 : Nat) : Int) := by
  simp only [EndpointModes,Fintype.sum_option,Fintype.sum_sum_type,
    modeCoefficients,endpointMode,modeDegree,add_assoc]

theorem native_bottom_expansion (h : Nat) (a0 z : K) (a c : Fin h → K) :
    nativeA h a0 a-nativeC h c+z • U K ((2*h : Nat) : Int)=
      ∑ i,modeCoefficients (a0+z) (a-c) (a+c) i • endpointMode (K := K) i := by
  rw [mode_sum]
  simp only [nativeA,nativeC,smul_add,smul_sub,add_smul,sub_smul,
    Pi.sub_apply,Pi.add_apply,Finset.sum_add_distrib,Finset.sum_sub_distrib]
  abel

theorem native_top_expansion (h : Nat) (a0 : K) (a c : Fin h → K) :
    nativeA h a0 a+nativeC h c=
      ∑ i,modeCoefficients a0 (a+c) (a-c) i • endpointMode (K := K) i := by
  rw [mode_sum]
  simp only [nativeA,nativeC,smul_add,smul_sub,add_smul,sub_smul,
    Pi.sub_apply,Pi.add_apply,Finset.sum_add_distrib,Finset.sum_sub_distrib]
  abel

theorem native_bottom_cut [NeZero (2 : K)] (h r : Nat) (a0 z : K) (a c : Fin h → K) :
    (nativeA h a0 a-nativeC h c+z • U K ((2*h : Nat) : Int)).degree<(r : WithBot Nat) ↔
      (r ≤ 2*h → a0+z=0) ∧
      (∀ j : Fin h, r ≤ j.val → a j-c j=0) ∧
      (∀ j : Fin h, r ≤ 2*h-j.val-1 → a j+c j=0) := by
  rw [native_bottom_expansion,endpoint_modes_cut]
  simp only [EndpointModes,Option.forall,Sum.forall,modeCoefficients,modeDegree,
    Pi.sub_apply,Pi.add_apply]

theorem native_top_cut [NeZero (2 : K)] (h r : Nat) (a0 : K) (a c : Fin h → K) :
    (nativeA h a0 a+nativeC h c).degree<(r : WithBot Nat) ↔
      (r ≤ 2*h → a0=0) ∧
      (∀ j : Fin h, r ≤ j.val → a j+c j=0) ∧
      (∀ j : Fin h, r ≤ 2*h-j.val-1 → a j-c j=0) := by
  rw [native_top_expansion,endpoint_modes_cut]
  simp only [EndpointModes,Option.forall,Sum.forall,modeCoefficients,modeDegree,
    Pi.sub_apply,Pi.add_apply]

#print axioms native_bottom_cut
#print axioms native_top_cut
end
end CatalanMeasure.GenD.Uniform.Prefix
