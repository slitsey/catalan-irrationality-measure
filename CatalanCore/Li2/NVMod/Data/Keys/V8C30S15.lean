module
public import CatalanCore.Li2.NVMod.Data.Regular.V8C30
public import CatalanCore.Li2.NVMod.Data.Polynomial.V8C30S15
public import CatalanCore.Li2.NVMod.DataSupport.PolynomialPackageSupport
public import CatalanCore.Li2.NVMod.DataSupport.PolynomialInfSource
public import CatalanCore.Li2.NVMod.DataSupport.Factorials
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option backward.isDefEq.respectTransparency false
open Polynomial Finset
namespace CatalanCore.Li2.NVMod.KeyData.V8C30S15
open CatalanCore.Li2.NVMod CatalanCore.Li2.NVMod.DataSupport
noncomputable section

-- kcost: 1 s estimated; closed endpoint orders and literal fields, shared factorial theorem
def input : EndpointInput where
  -- kcost: 1 s estimated; finite endpoint orders, checked literal fields
  key:=CatalanCore.Li2.NVMod.FamilySource.V8C30.key 15
  p:=53
  D:=1703103561833815225244160000
  clearZ:=29
  clearOne:=22
  v0:=120
  v1:=198
  D_pos:=by decide +kernel
  mz:=CatalanCore.Li2.NVMod.FamilySource.V8C30.mz
  moment_clear:=by
    intro i j
    apply CatalanCore.Li2.NVMod.FamilySource.V8C30.moment_source 15
    have hi:=i.isLt
    have hj:=j.isLt
    change i.val<15 at hi
    change j.val<15 at hj
    omega
  order_zero:=by decide +kernel
  order_one:=by
    change (198:ℤ)=(22:ℤ)*15+oneOrder (CatalanCore.Li2.NVMod.FamilySource.V8C30.key 15)
    rw [oneOrderWith_spec,CatalanCore.Li2.NVMod.RegularFamily.V8C30.h0_key]
    decide +kernel
  factorials:=allFactorials (CatalanCore.Li2.NVMod.FamilySource.V8C30.key 15)

theorem rho_source : ∀m∈poleSet (CatalanCore.Li2.NVMod.FamilySource.V8C30.key 15),CatalanCore.Li2.NVMod.FamilySource.V8C30.rho m=residue (CatalanCore.Li2.NVMod.FamilySource.V8C30.key 15) m := by
  intro m hm
  apply CatalanCore.Li2.NVMod.FamilySource.V8C30.rho_source 15 m
  rwa [(CatalanCore.Li2.NVMod.FamilySource.V8C30.indices_set 15).trans (poles_eq_poleSet _)]

-- kcost: 3 s estimated; original endpoint check via proved source equalities
set_option trace.profiler true in
theorem endpoint0 : chk0 input=true := by
  change ((topPoles (CatalanCore.Li2.NVMod.FamilySource.V8C30.key 15)).length == 15 && ratUnitCheck 53 ((1703103561833815225244160000:ℚ)^15*zeroLead (CatalanCore.Li2.NVMod.FamilySource.V8C30.key 15)))=true
  rw [zeroLead_with_residues (CatalanCore.Li2.NVMod.FamilySource.V8C30.key 15) CatalanCore.Li2.NVMod.FamilySource.V8C30.rho rho_source]
  decide +kernel
-- kcost: 3 s estimated; original endpoint check via proved source equalities
set_option trace.profiler true in
theorem endpoint1 : chk1 input=true := by
  unfold chk1
  change (match oneLead (CatalanCore.Li2.NVMod.FamilySource.V8C30.key 15) with | none=>false | some q=>ratUnitCheck 53 ((1703103561833815225244160000:ℚ)^15*q))=true
  rw [oneLeadWith_spec (CatalanCore.Li2.NVMod.FamilySource.V8C30.key 15) (6) CatalanCore.Li2.NVMod.RegularFamily.V8C30.regularValue (CatalanCore.Li2.NVMod.RegularFamily.V8C30.h0_key 15) (CatalanCore.Li2.NVMod.RegularFamily.V8C30.regular_source 15)]
  decide +kernel
-- kcost: 3 s estimated; original endpoint check via proved source equalities
set_option trace.profiler true in
theorem endpointInf : chkInf input=true := by
  change (decide (15≤(slots (CatalanCore.Li2.NVMod.FamilySource.V8C30.key 15)).length) && ratUnitCheck 53 ((1703103561833815225244160000:ℚ)^15*infLead (CatalanCore.Li2.NVMod.FamilySource.V8C30.key 15)))=true
  rw [infLeadNative_spec (CatalanCore.Li2.NVMod.FamilySource.V8C30.key 15) CatalanCore.Li2.NVMod.FamilySource.V8C30.num CatalanCore.Li2.NVMod.FamilySource.V8C30.den CatalanCore.Li2.NVMod.FamilySource.V8C30.indices CatalanCore.Li2.NVMod.FamilySource.V8C30.rho (CatalanCore.Li2.NVMod.FamilySource.V8C30.num_source 15) (CatalanCore.Li2.NVMod.FamilySource.V8C30.den_source 15) CatalanCore.Li2.NVMod.FamilySource.V8C30.indices_nodup ((CatalanCore.Li2.NVMod.FamilySource.V8C30.indices_set 15).trans (poles_eq_poleSet _)) rho_source]
  decide +kernel
-- kcost: 1 s estimated; coefficientwise integer remainder binding
set_option trace.profiler true in
theorem mod_ok : momentResidueCheck 53 15 CatalanCore.Li2.NVMod.FamilySource.V8C30.moments CatalanCore.Li2.NVMod.PolynomialData.V8C30S15.data.moments=true := by decide +kernel

-- kcost: 1 s estimated; existing arithmetic proofs and outer list length only
def interior : PolynomialCert.InteriorChecked input where
  data:=CatalanCore.Li2.NVMod.PolynomialData.V8C30S15.data.toCertificate
  bounds:=(PolynomialCompute.bounds_nat_transfer 15 53 CatalanCore.Li2.NVMod.PolynomialData.V8C30S15.data).symm.trans CatalanCore.Li2.NVMod.PolynomialData.V8C30S15.bounds_ok
  arithmetic:=(PolynomialCompute.arithmetic_transfer 15 53 CatalanCore.Li2.NVMod.PolynomialData.V8C30S15.data).symm.trans CatalanCore.Li2.NVMod.PolynomialData.V8C30S15.arithmetic_ok
  moments:=by
    intro e he
    exact momentResidueCheck_sound 53 15 CatalanCore.Li2.NVMod.FamilySource.V8C30.moments CatalanCore.Li2.NVMod.PolynomialData.V8C30S15.data.moments mod_ok (by decide +kernel) e he

def checked : KeyCertificate :=
  ⟨input,by decide +kernel,endpoint0,endpoint1,endpointInf,interior⟩
#print axioms checked
end
end CatalanCore.Li2.NVMod.KeyData.V8C30S15
