module
public import CatalanCore.Li2.NVMod.Data.Regular.U11C44
public import CatalanCore.Li2.NVMod.Data.Polynomial.U11C44S22
public import CatalanCore.Li2.NVMod.DataSupport.PolynomialPackageSupport
public import CatalanCore.Li2.NVMod.DataSupport.PolynomialInfSource
public import CatalanCore.Li2.NVMod.DataSupport.Factorials
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option backward.isDefEq.respectTransparency false
open Polynomial Finset
namespace CatalanCore.Li2.NVMod.KeyData.U11C44S22
open CatalanCore.Li2.NVMod CatalanCore.Li2.NVMod.DataSupport
noncomputable section

-- kcost: 1 s estimated; closed endpoint orders and literal fields, shared factorial theorem
def input : EndpointInput where
  -- kcost: 1 s estimated; finite endpoint orders, checked literal fields
  key:=CatalanCore.Li2.NVMod.FamilySource.U11C44.key 22
  p:=47
  D:=14652918739915066489779653593160464615870184793047040000000
  clearZ:=44
  clearOne:=32
  v0:=253
  v1:=432
  D_pos:=by decide +kernel
  mz:=CatalanCore.Li2.NVMod.FamilySource.U11C44.mz
  moment_clear:=by
    intro i j
    apply CatalanCore.Li2.NVMod.FamilySource.U11C44.moment_source 22
    have hi:=i.isLt
    have hj:=j.isLt
    change i.val<22 at hi
    change j.val<22 at hj
    omega
  order_zero:=by decide +kernel
  order_one:=by
    change (432:ℤ)=(32:ℤ)*22+oneOrder (CatalanCore.Li2.NVMod.FamilySource.U11C44.key 22)
    rw [oneOrderWith_spec,CatalanCore.Li2.NVMod.RegularFamily.U11C44.h0_key]
    decide +kernel
  factorials:=allFactorials (CatalanCore.Li2.NVMod.FamilySource.U11C44.key 22)

theorem rho_source : ∀m∈poleSet (CatalanCore.Li2.NVMod.FamilySource.U11C44.key 22),CatalanCore.Li2.NVMod.FamilySource.U11C44.rho m=residue (CatalanCore.Li2.NVMod.FamilySource.U11C44.key 22) m := by
  intro m hm
  apply CatalanCore.Li2.NVMod.FamilySource.U11C44.rho_source 22 m
  rwa [(CatalanCore.Li2.NVMod.FamilySource.U11C44.indices_set 22).trans (poles_eq_poleSet _)]

-- kcost: 3 s estimated; original endpoint check via proved source equalities
set_option trace.profiler true in
theorem endpoint0 : chk0 input=true := by
  change ((topPoles (CatalanCore.Li2.NVMod.FamilySource.U11C44.key 22)).length == 22 && ratUnitCheck 47 ((14652918739915066489779653593160464615870184793047040000000:ℚ)^22*zeroLead (CatalanCore.Li2.NVMod.FamilySource.U11C44.key 22)))=true
  rw [zeroLead_with_residues (CatalanCore.Li2.NVMod.FamilySource.U11C44.key 22) CatalanCore.Li2.NVMod.FamilySource.U11C44.rho rho_source]
  decide +kernel
-- kcost: 3 s estimated; original endpoint check via proved source equalities
set_option trace.profiler true in
theorem endpoint1 : chk1 input=true := by
  unfold chk1
  change (match oneLead (CatalanCore.Li2.NVMod.FamilySource.U11C44.key 22) with | none=>false | some q=>ratUnitCheck 47 ((14652918739915066489779653593160464615870184793047040000000:ℚ)^22*q))=true
  rw [oneLeadWith_spec (CatalanCore.Li2.NVMod.FamilySource.U11C44.key 22) (10) CatalanCore.Li2.NVMod.RegularFamily.U11C44.regularValue (CatalanCore.Li2.NVMod.RegularFamily.U11C44.h0_key 22) (CatalanCore.Li2.NVMod.RegularFamily.U11C44.regular_source 22)]
  decide +kernel
-- kcost: 3 s estimated; original endpoint check via proved source equalities
set_option trace.profiler true in
theorem endpointInf : chkInf input=true := by
  change (decide (22≤(slots (CatalanCore.Li2.NVMod.FamilySource.U11C44.key 22)).length) && ratUnitCheck 47 ((14652918739915066489779653593160464615870184793047040000000:ℚ)^22*infLead (CatalanCore.Li2.NVMod.FamilySource.U11C44.key 22)))=true
  rw [infLeadNative_spec (CatalanCore.Li2.NVMod.FamilySource.U11C44.key 22) CatalanCore.Li2.NVMod.FamilySource.U11C44.num CatalanCore.Li2.NVMod.FamilySource.U11C44.den CatalanCore.Li2.NVMod.FamilySource.U11C44.indices CatalanCore.Li2.NVMod.FamilySource.U11C44.rho (CatalanCore.Li2.NVMod.FamilySource.U11C44.num_source 22) (CatalanCore.Li2.NVMod.FamilySource.U11C44.den_source 22) CatalanCore.Li2.NVMod.FamilySource.U11C44.indices_nodup ((CatalanCore.Li2.NVMod.FamilySource.U11C44.indices_set 22).trans (poles_eq_poleSet _)) rho_source]
  decide +kernel
-- kcost: 1 s estimated; coefficientwise integer remainder binding
set_option trace.profiler true in
theorem mod_ok : momentResidueCheck 47 22 CatalanCore.Li2.NVMod.FamilySource.U11C44.moments CatalanCore.Li2.NVMod.PolynomialData.U11C44S22.data.moments=true := by decide +kernel

-- kcost: 1 s estimated; existing arithmetic proofs and outer list length only
def interior : PolynomialCert.InteriorChecked input where
  data:=CatalanCore.Li2.NVMod.PolynomialData.U11C44S22.data.toCertificate
  bounds:=(PolynomialCompute.bounds_nat_transfer 22 47 CatalanCore.Li2.NVMod.PolynomialData.U11C44S22.data).symm.trans CatalanCore.Li2.NVMod.PolynomialData.U11C44S22.bounds_ok
  arithmetic:=(PolynomialCompute.arithmetic_transfer 22 47 CatalanCore.Li2.NVMod.PolynomialData.U11C44S22.data).symm.trans CatalanCore.Li2.NVMod.PolynomialData.U11C44S22.arithmetic_ok
  moments:=by
    intro e he
    exact momentResidueCheck_sound 47 22 CatalanCore.Li2.NVMod.FamilySource.U11C44.moments CatalanCore.Li2.NVMod.PolynomialData.U11C44S22.data.moments mod_ok (by decide +kernel) e he

def checked : KeyCertificate :=
  ⟨input,by decide +kernel,endpoint0,endpoint1,endpointInf,interior⟩
#print axioms checked
end
end CatalanCore.Li2.NVMod.KeyData.U11C44S22
