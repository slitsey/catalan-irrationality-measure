module
public import CatalanCore.Li2.NVMod.PolynomialChecker
public import CatalanCore.Li2.NVMod.RationalRoot
public import CatalanCore.Li2.NVMod.PointValue
public import CatalanCore.Li2.NVMod.SpecialNonzero
@[expose] public section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
open Polynomial Finset
namespace CatalanCore.Li2.NVMod
noncomputable section

structure AllConstantsChecked (q0 : ℕ) where
  input : (A : TypeKey)→A∈needed q0→A∉specialKeys→EndpointInput
  key_eq : ∀ A hA hS,(input A hA hS).key=A
  prime : ∀ A hA hS,(input A hA hS).p.Prime
  endpoint0 : ∀ A hA hS,chk0 (input A hA hS)=true
  endpoint1 : ∀ A hA hS,chk1 (input A hA hS)=true
  endpointInf : ∀ A hA hS,chkInf (input A hA hS)=true
  interiorChecked : ∀ A hA hS,PolynomialCert.InteriorChecked (input A hA hS)

theorem constants_nonzero_of_checked (q0 : ℕ) (cert : AllConstantsChecked q0)
    (z : ℚ) (hz : Allowed z) : AllConstantsNonzero z q0 := by
  intro A hA
  by_cases hS : A∈specialKeys
  · exact special_constants_nonzero z hz A hS
  · let I := cert.input A hA hS
    have hp : I.p.Prime := cert.prime A hA hS
    letI : Fact I.p.Prime := ⟨hp⟩
    have he := endpoint_check_sound I (cert.endpoint0 A hA hS) (cert.endpoint1 A hA hS)
      (cert.endpointInf A hA hS)
    have hi := PolynomialCert.interior_sound I (cert.interiorChecked A hA hS)
    have hF := no_rational_root_of_residues I.F I.p I.v0 I.v1 he.1 he.2.1
      he.2.2.1 he.2.2.2.1 he.2.2.2.2 hi z hz.1 hz.2.1
    have hkey : I.key=A := cert.key_eq A hA hS
    rw [←hkey]
    intro hK
    apply hF
    rw [I.eval_clear z hz.1 hz.2.1,hK,mul_zero]

#print axioms constants_nonzero_of_checked
end
end CatalanCore.Li2.NVMod
