module
public import CatalanCore.Li2.NVMod.Data.Regular.V10C39
public import CatalanCore.Li2.NVMod.Data.Polynomial.V10C39S20
public import CatalanCore.Li2.NVMod.DataSupport.PolynomialPackageSupport
public import CatalanCore.Li2.NVMod.DataSupport.PolynomialInfSource
public import CatalanCore.Li2.NVMod.DataSupport.Factorials
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option backward.isDefEq.respectTransparency false
open Polynomial Finset
namespace CatalanCore.Li2.NVMod.KeyData.V10C39S20
open CatalanCore.Li2.NVMod CatalanCore.Li2.NVMod.DataSupport
noncomputable section

-- kcost: 1 s estimated; closed endpoint orders and literal fields, shared factorial theorem
def input : EndpointInput where
  -- kcost: 1 s estimated; finite endpoint orders, checked literal fields
  key:=CatalanCore.Li2.NVMod.FamilySource.V10C39.key 20
  p:=47
  D:=149345155424655805502816930985984000000
  clearZ:=38
  clearOne:=29
  v0:=210
  v1:=355
  D_pos:=by decide +kernel
  mz:=CatalanCore.Li2.NVMod.FamilySource.V10C39.mz
  moment_clear:=by
    intro i j
    apply CatalanCore.Li2.NVMod.FamilySource.V10C39.moment_source 20
    have hi:=i.isLt
    have hj:=j.isLt
    change i.val<20 at hi
    change j.val<20 at hj
    omega
  order_zero:=by decide +kernel
  order_one:=by
    change (355:ℤ)=(29:ℤ)*20+oneOrder (CatalanCore.Li2.NVMod.FamilySource.V10C39.key 20)
    rw [oneOrderWith_spec,CatalanCore.Li2.NVMod.RegularFamily.V10C39.h0_key]
    decide +kernel
  factorials:=allFactorials (CatalanCore.Li2.NVMod.FamilySource.V10C39.key 20)

theorem rho_source : ∀m∈poleSet (CatalanCore.Li2.NVMod.FamilySource.V10C39.key 20),CatalanCore.Li2.NVMod.FamilySource.V10C39.rho m=residue (CatalanCore.Li2.NVMod.FamilySource.V10C39.key 20) m := by
  intro m hm
  apply CatalanCore.Li2.NVMod.FamilySource.V10C39.rho_source 20 m
  rwa [(CatalanCore.Li2.NVMod.FamilySource.V10C39.indices_set 20).trans (poles_eq_poleSet _)]

-- kcost: 3 s estimated; original endpoint check via proved source equalities
set_option trace.profiler true in
theorem endpoint0 : chk0 input=true := by
  change ((topPoles (CatalanCore.Li2.NVMod.FamilySource.V10C39.key 20)).length == 20 && ratUnitCheck 47 ((149345155424655805502816930985984000000:ℚ)^20*zeroLead (CatalanCore.Li2.NVMod.FamilySource.V10C39.key 20)))=true
  rw [zeroLead_with_residues (CatalanCore.Li2.NVMod.FamilySource.V10C39.key 20) CatalanCore.Li2.NVMod.FamilySource.V10C39.rho rho_source]
  decide +kernel
-- kcost: 3 s estimated; original endpoint check via proved source equalities
set_option trace.profiler true in
theorem endpoint1 : chk1 input=true := by
  unfold chk1
  change (match oneLead (CatalanCore.Li2.NVMod.FamilySource.V10C39.key 20) with | none=>false | some q=>ratUnitCheck 47 ((149345155424655805502816930985984000000:ℚ)^20*q))=true
  rw [oneLeadWith_spec (CatalanCore.Li2.NVMod.FamilySource.V10C39.key 20) (9) CatalanCore.Li2.NVMod.RegularFamily.V10C39.regularValue (CatalanCore.Li2.NVMod.RegularFamily.V10C39.h0_key 20) (CatalanCore.Li2.NVMod.RegularFamily.V10C39.regular_source 20)]
  decide +kernel
-- kcost: 3 s estimated; original endpoint check via proved source equalities
set_option trace.profiler true in
theorem endpointInf : chkInf input=true := by
  change (decide (20≤(slots (CatalanCore.Li2.NVMod.FamilySource.V10C39.key 20)).length) && ratUnitCheck 47 ((149345155424655805502816930985984000000:ℚ)^20*infLead (CatalanCore.Li2.NVMod.FamilySource.V10C39.key 20)))=true
  rw [infLeadNative_spec (CatalanCore.Li2.NVMod.FamilySource.V10C39.key 20) CatalanCore.Li2.NVMod.FamilySource.V10C39.num CatalanCore.Li2.NVMod.FamilySource.V10C39.den CatalanCore.Li2.NVMod.FamilySource.V10C39.indices CatalanCore.Li2.NVMod.FamilySource.V10C39.rho (CatalanCore.Li2.NVMod.FamilySource.V10C39.num_source 20) (CatalanCore.Li2.NVMod.FamilySource.V10C39.den_source 20) CatalanCore.Li2.NVMod.FamilySource.V10C39.indices_nodup ((CatalanCore.Li2.NVMod.FamilySource.V10C39.indices_set 20).trans (poles_eq_poleSet _)) rho_source]
  decide +kernel
-- kcost: 1 s estimated; coefficientwise integer remainder binding
set_option trace.profiler true in
theorem mod_ok : momentResidueCheck 47 20 CatalanCore.Li2.NVMod.FamilySource.V10C39.moments CatalanCore.Li2.NVMod.PolynomialData.V10C39S20.data.moments=true := by decide +kernel

-- kcost: 1 s estimated; existing arithmetic proofs and outer list length only
def interior : PolynomialCert.InteriorChecked input where
  data:=CatalanCore.Li2.NVMod.PolynomialData.V10C39S20.data.toCertificate
  bounds:=(PolynomialCompute.bounds_nat_transfer 20 47 CatalanCore.Li2.NVMod.PolynomialData.V10C39S20.data).symm.trans CatalanCore.Li2.NVMod.PolynomialData.V10C39S20.bounds_ok
  arithmetic:=(PolynomialCompute.arithmetic_transfer 20 47 CatalanCore.Li2.NVMod.PolynomialData.V10C39S20.data).symm.trans CatalanCore.Li2.NVMod.PolynomialData.V10C39S20.arithmetic_ok
  moments:=by
    intro e he
    exact momentResidueCheck_sound 47 20 CatalanCore.Li2.NVMod.FamilySource.V10C39.moments CatalanCore.Li2.NVMod.PolynomialData.V10C39S20.data.moments mod_ok (by decide +kernel) e he

def checked : KeyCertificate :=
  ⟨input,by decide +kernel,endpoint0,endpoint1,endpointInf,interior⟩
#print axioms checked
end
end CatalanCore.Li2.NVMod.KeyData.V10C39S20
