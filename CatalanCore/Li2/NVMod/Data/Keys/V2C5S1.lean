module
public import CatalanCore.Li2.NVMod.Data.Regular.V2C5
public import CatalanCore.Li2.NVMod.Data.Polynomial.V2C5S1
public import CatalanCore.Li2.NVMod.DataSupport.PolynomialPackageSupport
public import CatalanCore.Li2.NVMod.DataSupport.PolynomialInfSource
public import CatalanCore.Li2.NVMod.DataSupport.Factorials
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option backward.isDefEq.respectTransparency false
open Polynomial Finset
namespace CatalanCore.Li2.NVMod.KeyData.V2C5S1
open CatalanCore.Li2.NVMod CatalanCore.Li2.NVMod.DataSupport
noncomputable section

-- kcost: 1 s estimated; closed endpoint orders and literal fields, shared factorial theorem
def input : EndpointInput where
  -- kcost: 1 s estimated; finite endpoint orders, checked literal fields
  key:=CatalanCore.Li2.NVMod.FamilySource.V2C5.key 1
  p:=5
  D:=1
  clearZ:=4
  clearOne:=3
  v0:=1
  v1:=2
  D_pos:=by decide +kernel
  mz:=CatalanCore.Li2.NVMod.FamilySource.V2C5.mz
  moment_clear:=by
    intro i j
    apply CatalanCore.Li2.NVMod.FamilySource.V2C5.moment_source 1
    have hi:=i.isLt
    have hj:=j.isLt
    change i.val<1 at hi
    change j.val<1 at hj
    omega
  order_zero:=by decide +kernel
  order_one:=by
    change (2:ℤ)=(3:ℤ)*1+oneOrder (CatalanCore.Li2.NVMod.FamilySource.V2C5.key 1)
    rw [oneOrderWith_spec,CatalanCore.Li2.NVMod.RegularFamily.V2C5.h0_key]
    decide +kernel
  factorials:=allFactorials (CatalanCore.Li2.NVMod.FamilySource.V2C5.key 1)

theorem rho_source : ∀m∈poleSet (CatalanCore.Li2.NVMod.FamilySource.V2C5.key 1),CatalanCore.Li2.NVMod.FamilySource.V2C5.rho m=residue (CatalanCore.Li2.NVMod.FamilySource.V2C5.key 1) m := by
  intro m hm
  apply CatalanCore.Li2.NVMod.FamilySource.V2C5.rho_source 1 m
  rwa [(CatalanCore.Li2.NVMod.FamilySource.V2C5.indices_set 1).trans (poles_eq_poleSet _)]

-- kcost: 3 s estimated; original endpoint check via proved source equalities
set_option trace.profiler true in
theorem endpoint0 : chk0 input=true := by
  change ((topPoles (CatalanCore.Li2.NVMod.FamilySource.V2C5.key 1)).length == 1 && ratUnitCheck 5 ((1:ℚ)^1*zeroLead (CatalanCore.Li2.NVMod.FamilySource.V2C5.key 1)))=true
  rw [zeroLead_with_residues (CatalanCore.Li2.NVMod.FamilySource.V2C5.key 1) CatalanCore.Li2.NVMod.FamilySource.V2C5.rho rho_source]
  decide +kernel
-- kcost: 3 s estimated; original endpoint check via proved source equalities
set_option trace.profiler true in
theorem endpoint1 : chk1 input=true := by
  unfold chk1
  change (match oneLead (CatalanCore.Li2.NVMod.FamilySource.V2C5.key 1) with | none=>false | some q=>ratUnitCheck 5 ((1:ℚ)^1*q))=true
  rw [oneLeadWith_spec (CatalanCore.Li2.NVMod.FamilySource.V2C5.key 1) (-1) CatalanCore.Li2.NVMod.RegularFamily.V2C5.regularValue (CatalanCore.Li2.NVMod.RegularFamily.V2C5.h0_key 1) (CatalanCore.Li2.NVMod.RegularFamily.V2C5.regular_source 1)]
  decide +kernel
-- kcost: 3 s estimated; original endpoint check via proved source equalities
set_option trace.profiler true in
theorem endpointInf : chkInf input=true := by
  change (decide (1≤(slots (CatalanCore.Li2.NVMod.FamilySource.V2C5.key 1)).length) && ratUnitCheck 5 ((1:ℚ)^1*infLead (CatalanCore.Li2.NVMod.FamilySource.V2C5.key 1)))=true
  rw [infLeadNative_spec (CatalanCore.Li2.NVMod.FamilySource.V2C5.key 1) CatalanCore.Li2.NVMod.FamilySource.V2C5.num CatalanCore.Li2.NVMod.FamilySource.V2C5.den CatalanCore.Li2.NVMod.FamilySource.V2C5.indices CatalanCore.Li2.NVMod.FamilySource.V2C5.rho (CatalanCore.Li2.NVMod.FamilySource.V2C5.num_source 1) (CatalanCore.Li2.NVMod.FamilySource.V2C5.den_source 1) CatalanCore.Li2.NVMod.FamilySource.V2C5.indices_nodup ((CatalanCore.Li2.NVMod.FamilySource.V2C5.indices_set 1).trans (poles_eq_poleSet _)) rho_source]
  decide +kernel
-- kcost: 1 s estimated; coefficientwise integer remainder binding
set_option trace.profiler true in
theorem mod_ok : momentResidueCheck 5 1 CatalanCore.Li2.NVMod.FamilySource.V2C5.moments CatalanCore.Li2.NVMod.PolynomialData.V2C5S1.data.moments=true := by decide +kernel

-- kcost: 1 s estimated; existing arithmetic proofs and outer list length only
def interior : PolynomialCert.InteriorChecked input where
  data:=CatalanCore.Li2.NVMod.PolynomialData.V2C5S1.data.toCertificate
  bounds:=(PolynomialCompute.bounds_nat_transfer 1 5 CatalanCore.Li2.NVMod.PolynomialData.V2C5S1.data).symm.trans CatalanCore.Li2.NVMod.PolynomialData.V2C5S1.bounds_ok
  arithmetic:=(PolynomialCompute.arithmetic_transfer 1 5 CatalanCore.Li2.NVMod.PolynomialData.V2C5S1.data).symm.trans CatalanCore.Li2.NVMod.PolynomialData.V2C5S1.arithmetic_ok
  moments:=by
    intro e he
    exact momentResidueCheck_sound 5 1 CatalanCore.Li2.NVMod.FamilySource.V2C5.moments CatalanCore.Li2.NVMod.PolynomialData.V2C5S1.data.moments mod_ok (by decide +kernel) e he

def checked : KeyCertificate :=
  ⟨input,by decide +kernel,endpoint0,endpoint1,endpointInf,interior⟩
#print axioms checked
end
end CatalanCore.Li2.NVMod.KeyData.V2C5S1
