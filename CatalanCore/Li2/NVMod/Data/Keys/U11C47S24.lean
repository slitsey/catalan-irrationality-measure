module
public import CatalanCore.Li2.NVMod.Data.Regular.U11C47
public import CatalanCore.Li2.NVMod.Data.Polynomial.U11C47S24
public import CatalanCore.Li2.NVMod.DataSupport.PolynomialPackageSupport
public import CatalanCore.Li2.NVMod.DataSupport.PolynomialInfSource
public import CatalanCore.Li2.NVMod.DataSupport.Factorials
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option backward.isDefEq.respectTransparency false
open Polynomial Finset
namespace CatalanCore.Li2.NVMod.KeyData.U11C47S24
open CatalanCore.Li2.NVMod CatalanCore.Li2.NVMod.DataSupport
noncomputable section

-- kcost: 1 s estimated; closed endpoint orders and literal fields, shared factorial theorem
def input : EndpointInput where
  -- kcost: 1 s estimated; finite endpoint orders, checked literal fields
  key:=CatalanCore.Li2.NVMod.FamilySource.U11C47.key 24
  p:=73
  D:=1271103042686470436267506215496935883032675744421912589107200000000
  clearZ:=47
  clearOne:=35
  v0:=300
  v1:=551
  D_pos:=by decide +kernel
  mz:=CatalanCore.Li2.NVMod.FamilySource.U11C47.mz
  moment_clear:=by
    intro i j
    apply CatalanCore.Li2.NVMod.FamilySource.U11C47.moment_source 24
    have hi:=i.isLt
    have hj:=j.isLt
    change i.val<24 at hi
    change j.val<24 at hj
    omega
  order_zero:=by decide +kernel
  order_one:=by
    change (551:ℤ)=(35:ℤ)*24+oneOrder (CatalanCore.Li2.NVMod.FamilySource.U11C47.key 24)
    rw [oneOrderWith_spec,CatalanCore.Li2.NVMod.RegularFamily.U11C47.h0_key]
    decide +kernel
  factorials:=allFactorials (CatalanCore.Li2.NVMod.FamilySource.U11C47.key 24)

theorem rho_source : ∀m∈poleSet (CatalanCore.Li2.NVMod.FamilySource.U11C47.key 24),CatalanCore.Li2.NVMod.FamilySource.U11C47.rho m=residue (CatalanCore.Li2.NVMod.FamilySource.U11C47.key 24) m := by
  intro m hm
  apply CatalanCore.Li2.NVMod.FamilySource.U11C47.rho_source 24 m
  rwa [(CatalanCore.Li2.NVMod.FamilySource.U11C47.indices_set 24).trans (poles_eq_poleSet _)]

-- kcost: 3 s estimated; original endpoint check via proved source equalities
set_option trace.profiler true in
theorem endpoint0 : chk0 input=true := by
  change ((topPoles (CatalanCore.Li2.NVMod.FamilySource.U11C47.key 24)).length == 24 && ratUnitCheck 73 ((1271103042686470436267506215496935883032675744421912589107200000000:ℚ)^24*zeroLead (CatalanCore.Li2.NVMod.FamilySource.U11C47.key 24)))=true
  rw [zeroLead_with_residues (CatalanCore.Li2.NVMod.FamilySource.U11C47.key 24) CatalanCore.Li2.NVMod.FamilySource.U11C47.rho rho_source]
  decide +kernel
-- kcost: 3 s estimated; original endpoint check via proved source equalities
set_option trace.profiler true in
theorem endpoint1 : chk1 input=true := by
  unfold chk1
  change (match oneLead (CatalanCore.Li2.NVMod.FamilySource.U11C47.key 24) with | none=>false | some q=>ratUnitCheck 73 ((1271103042686470436267506215496935883032675744421912589107200000000:ℚ)^24*q))=true
  rw [oneLeadWith_spec (CatalanCore.Li2.NVMod.FamilySource.U11C47.key 24) (13) CatalanCore.Li2.NVMod.RegularFamily.U11C47.regularValue (CatalanCore.Li2.NVMod.RegularFamily.U11C47.h0_key 24) (CatalanCore.Li2.NVMod.RegularFamily.U11C47.regular_source 24)]
  decide +kernel
-- kcost: 3 s estimated; original endpoint check via proved source equalities
set_option trace.profiler true in
theorem endpointInf : chkInf input=true := by
  change (decide (24≤(slots (CatalanCore.Li2.NVMod.FamilySource.U11C47.key 24)).length) && ratUnitCheck 73 ((1271103042686470436267506215496935883032675744421912589107200000000:ℚ)^24*infLead (CatalanCore.Li2.NVMod.FamilySource.U11C47.key 24)))=true
  rw [infLeadNative_spec (CatalanCore.Li2.NVMod.FamilySource.U11C47.key 24) CatalanCore.Li2.NVMod.FamilySource.U11C47.num CatalanCore.Li2.NVMod.FamilySource.U11C47.den CatalanCore.Li2.NVMod.FamilySource.U11C47.indices CatalanCore.Li2.NVMod.FamilySource.U11C47.rho (CatalanCore.Li2.NVMod.FamilySource.U11C47.num_source 24) (CatalanCore.Li2.NVMod.FamilySource.U11C47.den_source 24) CatalanCore.Li2.NVMod.FamilySource.U11C47.indices_nodup ((CatalanCore.Li2.NVMod.FamilySource.U11C47.indices_set 24).trans (poles_eq_poleSet _)) rho_source]
  decide +kernel
-- kcost: 1 s estimated; coefficientwise integer remainder binding
set_option trace.profiler true in
theorem mod_ok : momentResidueCheck 73 24 CatalanCore.Li2.NVMod.FamilySource.U11C47.moments CatalanCore.Li2.NVMod.PolynomialData.U11C47S24.data.moments=true := by decide +kernel

-- kcost: 1 s estimated; existing arithmetic proofs and outer list length only
def interior : PolynomialCert.InteriorChecked input where
  data:=CatalanCore.Li2.NVMod.PolynomialData.U11C47S24.data.toCertificate
  bounds:=(PolynomialCompute.bounds_nat_transfer 24 73 CatalanCore.Li2.NVMod.PolynomialData.U11C47S24.data).symm.trans CatalanCore.Li2.NVMod.PolynomialData.U11C47S24.bounds_ok
  arithmetic:=(PolynomialCompute.arithmetic_transfer 24 73 CatalanCore.Li2.NVMod.PolynomialData.U11C47S24.data).symm.trans CatalanCore.Li2.NVMod.PolynomialData.U11C47S24.arithmetic_ok
  moments:=by
    intro e he
    exact momentResidueCheck_sound 73 24 CatalanCore.Li2.NVMod.FamilySource.U11C47.moments CatalanCore.Li2.NVMod.PolynomialData.U11C47S24.data.moments mod_ok (by decide +kernel) e he

def checked : KeyCertificate :=
  ⟨input,by decide +kernel,endpoint0,endpoint1,endpointInf,interior⟩
#print axioms checked
end
end CatalanCore.Li2.NVMod.KeyData.U11C47S24
