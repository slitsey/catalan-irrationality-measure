module
public import CatalanCore.Li2.NVMod.Data.Regular.V8C35
public import CatalanCore.Li2.NVMod.Data.Polynomial.V8C35S19
public import CatalanCore.Li2.NVMod.DataSupport.PolynomialPackageSupport
public import CatalanCore.Li2.NVMod.DataSupport.PolynomialInfSource
public import CatalanCore.Li2.NVMod.DataSupport.Factorials
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option backward.isDefEq.respectTransparency false
open Polynomial Finset
namespace CatalanCore.Li2.NVMod.KeyData.V8C35S19
open CatalanCore.Li2.NVMod CatalanCore.Li2.NVMod.DataSupport
noncomputable section

-- kcost: 1 s estimated; closed endpoint orders and literal fields, shared factorial theorem
def input : EndpointInput where
  -- kcost: 1 s estimated; finite endpoint orders, checked literal fields
  key:=CatalanCore.Li2.NVMod.FamilySource.V8C35.key 19
  p:=47
  D:=177791851696018816074782060697600000000
  clearZ:=34
  clearOne:=25
  v0:=190
  v1:=306
  D_pos:=by decide +kernel
  mz:=CatalanCore.Li2.NVMod.FamilySource.V8C35.mz
  moment_clear:=by
    intro i j
    apply CatalanCore.Li2.NVMod.FamilySource.V8C35.moment_source 19
    have hi:=i.isLt
    have hj:=j.isLt
    change i.val<19 at hi
    change j.val<19 at hj
    omega
  order_zero:=by decide +kernel
  order_one:=by
    change (306:ℤ)=(25:ℤ)*19+oneOrder (CatalanCore.Li2.NVMod.FamilySource.V8C35.key 19)
    rw [oneOrderWith_spec,CatalanCore.Li2.NVMod.RegularFamily.V8C35.h0_key]
    decide +kernel
  factorials:=allFactorials (CatalanCore.Li2.NVMod.FamilySource.V8C35.key 19)

theorem rho_source : ∀m∈poleSet (CatalanCore.Li2.NVMod.FamilySource.V8C35.key 19),CatalanCore.Li2.NVMod.FamilySource.V8C35.rho m=residue (CatalanCore.Li2.NVMod.FamilySource.V8C35.key 19) m := by
  intro m hm
  apply CatalanCore.Li2.NVMod.FamilySource.V8C35.rho_source 19 m
  rwa [(CatalanCore.Li2.NVMod.FamilySource.V8C35.indices_set 19).trans (poles_eq_poleSet _)]

-- kcost: 3 s estimated; original endpoint check via proved source equalities
set_option trace.profiler true in
theorem endpoint0 : chk0 input=true := by
  change ((topPoles (CatalanCore.Li2.NVMod.FamilySource.V8C35.key 19)).length == 19 && ratUnitCheck 47 ((177791851696018816074782060697600000000:ℚ)^19*zeroLead (CatalanCore.Li2.NVMod.FamilySource.V8C35.key 19)))=true
  rw [zeroLead_with_residues (CatalanCore.Li2.NVMod.FamilySource.V8C35.key 19) CatalanCore.Li2.NVMod.FamilySource.V8C35.rho rho_source]
  decide +kernel
-- kcost: 3 s estimated; original endpoint check via proved source equalities
set_option trace.profiler true in
theorem endpoint1 : chk1 input=true := by
  unfold chk1
  change (match oneLead (CatalanCore.Li2.NVMod.FamilySource.V8C35.key 19) with | none=>false | some q=>ratUnitCheck 47 ((177791851696018816074782060697600000000:ℚ)^19*q))=true
  rw [oneLeadWith_spec (CatalanCore.Li2.NVMod.FamilySource.V8C35.key 19) (11) CatalanCore.Li2.NVMod.RegularFamily.V8C35.regularValue (CatalanCore.Li2.NVMod.RegularFamily.V8C35.h0_key 19) (CatalanCore.Li2.NVMod.RegularFamily.V8C35.regular_source 19)]
  decide +kernel
-- kcost: 3 s estimated; original endpoint check via proved source equalities
set_option trace.profiler true in
theorem endpointInf : chkInf input=true := by
  change (decide (19≤(slots (CatalanCore.Li2.NVMod.FamilySource.V8C35.key 19)).length) && ratUnitCheck 47 ((177791851696018816074782060697600000000:ℚ)^19*infLead (CatalanCore.Li2.NVMod.FamilySource.V8C35.key 19)))=true
  rw [infLeadNative_spec (CatalanCore.Li2.NVMod.FamilySource.V8C35.key 19) CatalanCore.Li2.NVMod.FamilySource.V8C35.num CatalanCore.Li2.NVMod.FamilySource.V8C35.den CatalanCore.Li2.NVMod.FamilySource.V8C35.indices CatalanCore.Li2.NVMod.FamilySource.V8C35.rho (CatalanCore.Li2.NVMod.FamilySource.V8C35.num_source 19) (CatalanCore.Li2.NVMod.FamilySource.V8C35.den_source 19) CatalanCore.Li2.NVMod.FamilySource.V8C35.indices_nodup ((CatalanCore.Li2.NVMod.FamilySource.V8C35.indices_set 19).trans (poles_eq_poleSet _)) rho_source]
  decide +kernel
-- kcost: 1 s estimated; coefficientwise integer remainder binding
set_option trace.profiler true in
theorem mod_ok : momentResidueCheck 47 19 CatalanCore.Li2.NVMod.FamilySource.V8C35.moments CatalanCore.Li2.NVMod.PolynomialData.V8C35S19.data.moments=true := by decide +kernel

-- kcost: 1 s estimated; existing arithmetic proofs and outer list length only
def interior : PolynomialCert.InteriorChecked input where
  data:=CatalanCore.Li2.NVMod.PolynomialData.V8C35S19.data.toCertificate
  bounds:=(PolynomialCompute.bounds_nat_transfer 19 47 CatalanCore.Li2.NVMod.PolynomialData.V8C35S19.data).symm.trans CatalanCore.Li2.NVMod.PolynomialData.V8C35S19.bounds_ok
  arithmetic:=(PolynomialCompute.arithmetic_transfer 19 47 CatalanCore.Li2.NVMod.PolynomialData.V8C35S19.data).symm.trans CatalanCore.Li2.NVMod.PolynomialData.V8C35S19.arithmetic_ok
  moments:=by
    intro e he
    exact momentResidueCheck_sound 47 19 CatalanCore.Li2.NVMod.FamilySource.V8C35.moments CatalanCore.Li2.NVMod.PolynomialData.V8C35S19.data.moments mod_ok (by decide +kernel) e he

def checked : KeyCertificate :=
  ⟨input,by decide +kernel,endpoint0,endpoint1,endpointInf,interior⟩
#print axioms checked
end
end CatalanCore.Li2.NVMod.KeyData.V8C35S19
