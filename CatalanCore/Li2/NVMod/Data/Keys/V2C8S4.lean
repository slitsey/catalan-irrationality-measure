module
public import CatalanCore.Li2.NVMod.Data.Regular.V2C8
public import CatalanCore.Li2.NVMod.Data.Polynomial.V2C8S4
public import CatalanCore.Li2.NVMod.DataSupport.PolynomialPackageSupport
public import CatalanCore.Li2.NVMod.DataSupport.PolynomialInfSource
public import CatalanCore.Li2.NVMod.DataSupport.Factorials
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option backward.isDefEq.respectTransparency false
open Polynomial Finset
namespace CatalanCore.Li2.NVMod.KeyData.V2C8S4
open CatalanCore.Li2.NVMod CatalanCore.Li2.NVMod.DataSupport
noncomputable section

-- kcost: 1 s estimated; closed endpoint orders and literal fields, shared factorial theorem
def input : EndpointInput where
  -- kcost: 1 s estimated; finite endpoint orders, checked literal fields
  key:=CatalanCore.Li2.NVMod.FamilySource.V2C8.key 4
  p:=31
  D:=108000
  clearZ:=7
  clearOne:=4
  v0:=10
  v1:=10
  D_pos:=by decide +kernel
  mz:=CatalanCore.Li2.NVMod.FamilySource.V2C8.mz
  moment_clear:=by
    intro i j
    apply CatalanCore.Li2.NVMod.FamilySource.V2C8.moment_source 4
    have hi:=i.isLt
    have hj:=j.isLt
    change i.val<4 at hi
    change j.val<4 at hj
    omega
  order_zero:=by decide +kernel
  order_one:=by
    change (10:ℤ)=(4:ℤ)*4+oneOrder (CatalanCore.Li2.NVMod.FamilySource.V2C8.key 4)
    rw [oneOrderWith_spec,CatalanCore.Li2.NVMod.RegularFamily.V2C8.h0_key]
    decide +kernel
  factorials:=allFactorials (CatalanCore.Li2.NVMod.FamilySource.V2C8.key 4)

theorem rho_source : ∀m∈poleSet (CatalanCore.Li2.NVMod.FamilySource.V2C8.key 4),CatalanCore.Li2.NVMod.FamilySource.V2C8.rho m=residue (CatalanCore.Li2.NVMod.FamilySource.V2C8.key 4) m := by
  intro m hm
  apply CatalanCore.Li2.NVMod.FamilySource.V2C8.rho_source 4 m
  rwa [(CatalanCore.Li2.NVMod.FamilySource.V2C8.indices_set 4).trans (poles_eq_poleSet _)]

-- kcost: 3 s estimated; original endpoint check via proved source equalities
set_option trace.profiler true in
theorem endpoint0 : chk0 input=true := by
  change ((topPoles (CatalanCore.Li2.NVMod.FamilySource.V2C8.key 4)).length == 4 && ratUnitCheck 31 ((108000:ℚ)^4*zeroLead (CatalanCore.Li2.NVMod.FamilySource.V2C8.key 4)))=true
  rw [zeroLead_with_residues (CatalanCore.Li2.NVMod.FamilySource.V2C8.key 4) CatalanCore.Li2.NVMod.FamilySource.V2C8.rho rho_source]
  decide +kernel
-- kcost: 3 s estimated; original endpoint check via proved source equalities
set_option trace.profiler true in
theorem endpoint1 : chk1 input=true := by
  unfold chk1
  change (match oneLead (CatalanCore.Li2.NVMod.FamilySource.V2C8.key 4) with | none=>false | some q=>ratUnitCheck 31 ((108000:ℚ)^4*q))=true
  rw [oneLeadWith_spec (CatalanCore.Li2.NVMod.FamilySource.V2C8.key 4) (2) CatalanCore.Li2.NVMod.RegularFamily.V2C8.regularValue (CatalanCore.Li2.NVMod.RegularFamily.V2C8.h0_key 4) (CatalanCore.Li2.NVMod.RegularFamily.V2C8.regular_source 4)]
  decide +kernel
-- kcost: 3 s estimated; original endpoint check via proved source equalities
set_option trace.profiler true in
theorem endpointInf : chkInf input=true := by
  change (decide (4≤(slots (CatalanCore.Li2.NVMod.FamilySource.V2C8.key 4)).length) && ratUnitCheck 31 ((108000:ℚ)^4*infLead (CatalanCore.Li2.NVMod.FamilySource.V2C8.key 4)))=true
  rw [infLeadNative_spec (CatalanCore.Li2.NVMod.FamilySource.V2C8.key 4) CatalanCore.Li2.NVMod.FamilySource.V2C8.num CatalanCore.Li2.NVMod.FamilySource.V2C8.den CatalanCore.Li2.NVMod.FamilySource.V2C8.indices CatalanCore.Li2.NVMod.FamilySource.V2C8.rho (CatalanCore.Li2.NVMod.FamilySource.V2C8.num_source 4) (CatalanCore.Li2.NVMod.FamilySource.V2C8.den_source 4) CatalanCore.Li2.NVMod.FamilySource.V2C8.indices_nodup ((CatalanCore.Li2.NVMod.FamilySource.V2C8.indices_set 4).trans (poles_eq_poleSet _)) rho_source]
  decide +kernel
-- kcost: 1 s estimated; coefficientwise integer remainder binding
set_option trace.profiler true in
theorem mod_ok : momentResidueCheck 31 4 CatalanCore.Li2.NVMod.FamilySource.V2C8.moments CatalanCore.Li2.NVMod.PolynomialData.V2C8S4.data.moments=true := by decide +kernel

-- kcost: 1 s estimated; existing arithmetic proofs and outer list length only
def interior : PolynomialCert.InteriorChecked input where
  data:=CatalanCore.Li2.NVMod.PolynomialData.V2C8S4.data.toCertificate
  bounds:=(PolynomialCompute.bounds_nat_transfer 4 31 CatalanCore.Li2.NVMod.PolynomialData.V2C8S4.data).symm.trans CatalanCore.Li2.NVMod.PolynomialData.V2C8S4.bounds_ok
  arithmetic:=(PolynomialCompute.arithmetic_transfer 4 31 CatalanCore.Li2.NVMod.PolynomialData.V2C8S4.data).symm.trans CatalanCore.Li2.NVMod.PolynomialData.V2C8S4.arithmetic_ok
  moments:=by
    intro e he
    exact momentResidueCheck_sound 31 4 CatalanCore.Li2.NVMod.FamilySource.V2C8.moments CatalanCore.Li2.NVMod.PolynomialData.V2C8S4.data.moments mod_ok (by decide +kernel) e he

def checked : KeyCertificate :=
  ⟨input,by decide +kernel,endpoint0,endpoint1,endpointInf,interior⟩
#print axioms checked
end
end CatalanCore.Li2.NVMod.KeyData.V2C8S4
