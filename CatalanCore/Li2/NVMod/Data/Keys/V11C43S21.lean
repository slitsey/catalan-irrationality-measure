module
public import CatalanCore.Li2.NVMod.Data.Regular.V11C43
public import CatalanCore.Li2.NVMod.Data.Polynomial.V11C43S21
public import CatalanCore.Li2.NVMod.DataSupport.PolynomialPackageSupport
public import CatalanCore.Li2.NVMod.DataSupport.PolynomialInfSource
public import CatalanCore.Li2.NVMod.DataSupport.Factorials
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option backward.isDefEq.respectTransparency false
open Polynomial Finset
namespace CatalanCore.Li2.NVMod.KeyData.V11C43S21
open CatalanCore.Li2.NVMod CatalanCore.Li2.NVMod.DataSupport
noncomputable section

-- kcost: 1 s estimated; closed endpoint orders and literal fields, shared factorial theorem
def input : EndpointInput where
  -- kcost: 1 s estimated; finite endpoint orders, checked literal fields
  key:=CatalanCore.Li2.NVMod.FamilySource.V11C43.key 21
  p:=53
  D:=26903333717223138781041508177533006458880000000
  clearZ:=42
  clearOne:=32
  v0:=231
  v1:=432
  D_pos:=by decide +kernel
  mz:=CatalanCore.Li2.NVMod.FamilySource.V11C43.mz
  moment_clear:=by
    intro i j
    apply CatalanCore.Li2.NVMod.FamilySource.V11C43.moment_source 21
    have hi:=i.isLt
    have hj:=j.isLt
    change i.val<21 at hi
    change j.val<21 at hj
    omega
  order_zero:=by decide +kernel
  order_one:=by
    change (432:ℤ)=(32:ℤ)*21+oneOrder (CatalanCore.Li2.NVMod.FamilySource.V11C43.key 21)
    rw [oneOrderWith_spec,CatalanCore.Li2.NVMod.RegularFamily.V11C43.h0_key]
    decide +kernel
  factorials:=allFactorials (CatalanCore.Li2.NVMod.FamilySource.V11C43.key 21)

theorem rho_source : ∀m∈poleSet (CatalanCore.Li2.NVMod.FamilySource.V11C43.key 21),CatalanCore.Li2.NVMod.FamilySource.V11C43.rho m=residue (CatalanCore.Li2.NVMod.FamilySource.V11C43.key 21) m := by
  intro m hm
  apply CatalanCore.Li2.NVMod.FamilySource.V11C43.rho_source 21 m
  rwa [(CatalanCore.Li2.NVMod.FamilySource.V11C43.indices_set 21).trans (poles_eq_poleSet _)]

-- kcost: 3 s estimated; original endpoint check via proved source equalities
set_option trace.profiler true in
theorem endpoint0 : chk0 input=true := by
  change ((topPoles (CatalanCore.Li2.NVMod.FamilySource.V11C43.key 21)).length == 21 && ratUnitCheck 53 ((26903333717223138781041508177533006458880000000:ℚ)^21*zeroLead (CatalanCore.Li2.NVMod.FamilySource.V11C43.key 21)))=true
  rw [zeroLead_with_residues (CatalanCore.Li2.NVMod.FamilySource.V11C43.key 21) CatalanCore.Li2.NVMod.FamilySource.V11C43.rho rho_source]
  decide +kernel
-- kcost: 3 s estimated; original endpoint check via proved source equalities
set_option trace.profiler true in
theorem endpoint1 : chk1 input=true := by
  unfold chk1
  change (match oneLead (CatalanCore.Li2.NVMod.FamilySource.V11C43.key 21) with | none=>false | some q=>ratUnitCheck 53 ((26903333717223138781041508177533006458880000000:ℚ)^21*q))=true
  rw [oneLeadWith_spec (CatalanCore.Li2.NVMod.FamilySource.V11C43.key 21) (10) CatalanCore.Li2.NVMod.RegularFamily.V11C43.regularValue (CatalanCore.Li2.NVMod.RegularFamily.V11C43.h0_key 21) (CatalanCore.Li2.NVMod.RegularFamily.V11C43.regular_source 21)]
  decide +kernel
-- kcost: 3 s estimated; original endpoint check via proved source equalities
set_option trace.profiler true in
theorem endpointInf : chkInf input=true := by
  change (decide (21≤(slots (CatalanCore.Li2.NVMod.FamilySource.V11C43.key 21)).length) && ratUnitCheck 53 ((26903333717223138781041508177533006458880000000:ℚ)^21*infLead (CatalanCore.Li2.NVMod.FamilySource.V11C43.key 21)))=true
  rw [infLeadNative_spec (CatalanCore.Li2.NVMod.FamilySource.V11C43.key 21) CatalanCore.Li2.NVMod.FamilySource.V11C43.num CatalanCore.Li2.NVMod.FamilySource.V11C43.den CatalanCore.Li2.NVMod.FamilySource.V11C43.indices CatalanCore.Li2.NVMod.FamilySource.V11C43.rho (CatalanCore.Li2.NVMod.FamilySource.V11C43.num_source 21) (CatalanCore.Li2.NVMod.FamilySource.V11C43.den_source 21) CatalanCore.Li2.NVMod.FamilySource.V11C43.indices_nodup ((CatalanCore.Li2.NVMod.FamilySource.V11C43.indices_set 21).trans (poles_eq_poleSet _)) rho_source]
  decide +kernel
-- kcost: 1 s estimated; coefficientwise integer remainder binding
set_option trace.profiler true in
theorem mod_ok : momentResidueCheck 53 21 CatalanCore.Li2.NVMod.FamilySource.V11C43.moments CatalanCore.Li2.NVMod.PolynomialData.V11C43S21.data.moments=true := by decide +kernel

-- kcost: 1 s estimated; existing arithmetic proofs and outer list length only
def interior : PolynomialCert.InteriorChecked input where
  data:=CatalanCore.Li2.NVMod.PolynomialData.V11C43S21.data.toCertificate
  bounds:=(PolynomialCompute.bounds_nat_transfer 21 53 CatalanCore.Li2.NVMod.PolynomialData.V11C43S21.data).symm.trans CatalanCore.Li2.NVMod.PolynomialData.V11C43S21.bounds_ok
  arithmetic:=(PolynomialCompute.arithmetic_transfer 21 53 CatalanCore.Li2.NVMod.PolynomialData.V11C43S21.data).symm.trans CatalanCore.Li2.NVMod.PolynomialData.V11C43S21.arithmetic_ok
  moments:=by
    intro e he
    exact momentResidueCheck_sound 53 21 CatalanCore.Li2.NVMod.FamilySource.V11C43.moments CatalanCore.Li2.NVMod.PolynomialData.V11C43S21.data.moments mod_ok (by decide +kernel) e he

def checked : KeyCertificate :=
  ⟨input,by decide +kernel,endpoint0,endpoint1,endpointInf,interior⟩
#print axioms checked
end
end CatalanCore.Li2.NVMod.KeyData.V11C43S21
