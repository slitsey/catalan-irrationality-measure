module
public import CatalanCore.Li2.NVMod.Data.Regular.V8C32
public import CatalanCore.Li2.NVMod.Data.Polynomial.V8C32S16
public import CatalanCore.Li2.NVMod.DataSupport.PolynomialPackageSupport
public import CatalanCore.Li2.NVMod.DataSupport.PolynomialInfSource
public import CatalanCore.Li2.NVMod.DataSupport.Factorials
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option backward.isDefEq.respectTransparency false
open Polynomial Finset
namespace CatalanCore.Li2.NVMod.KeyData.V8C32S16
open CatalanCore.Li2.NVMod CatalanCore.Li2.NVMod.DataSupport
noncomputable section

-- kcost: 1 s estimated; closed endpoint orders and literal fields, shared factorial theorem
def input : EndpointInput where
  -- kcost: 1 s estimated; finite endpoint orders, checked literal fields
  key:=CatalanCore.Li2.NVMod.FamilySource.V8C32.key 16
  p:=47
  D:=455876542810304656602005283840000
  clearZ:=31
  clearOne:=22
  v0:=136
  v1:=220
  D_pos:=by decide +kernel
  mz:=CatalanCore.Li2.NVMod.FamilySource.V8C32.mz
  moment_clear:=by
    intro i j
    apply CatalanCore.Li2.NVMod.FamilySource.V8C32.moment_source 16
    have hi:=i.isLt
    have hj:=j.isLt
    change i.val<16 at hi
    change j.val<16 at hj
    omega
  order_zero:=by decide +kernel
  order_one:=by
    change (220:ℤ)=(22:ℤ)*16+oneOrder (CatalanCore.Li2.NVMod.FamilySource.V8C32.key 16)
    rw [oneOrderWith_spec,CatalanCore.Li2.NVMod.RegularFamily.V8C32.h0_key]
    decide +kernel
  factorials:=allFactorials (CatalanCore.Li2.NVMod.FamilySource.V8C32.key 16)

theorem rho_source : ∀m∈poleSet (CatalanCore.Li2.NVMod.FamilySource.V8C32.key 16),CatalanCore.Li2.NVMod.FamilySource.V8C32.rho m=residue (CatalanCore.Li2.NVMod.FamilySource.V8C32.key 16) m := by
  intro m hm
  apply CatalanCore.Li2.NVMod.FamilySource.V8C32.rho_source 16 m
  rwa [(CatalanCore.Li2.NVMod.FamilySource.V8C32.indices_set 16).trans (poles_eq_poleSet _)]

-- kcost: 3 s estimated; original endpoint check via proved source equalities
set_option trace.profiler true in
theorem endpoint0 : chk0 input=true := by
  change ((topPoles (CatalanCore.Li2.NVMod.FamilySource.V8C32.key 16)).length == 16 && ratUnitCheck 47 ((455876542810304656602005283840000:ℚ)^16*zeroLead (CatalanCore.Li2.NVMod.FamilySource.V8C32.key 16)))=true
  rw [zeroLead_with_residues (CatalanCore.Li2.NVMod.FamilySource.V8C32.key 16) CatalanCore.Li2.NVMod.FamilySource.V8C32.rho rho_source]
  decide +kernel
-- kcost: 3 s estimated; original endpoint check via proved source equalities
set_option trace.profiler true in
theorem endpoint1 : chk1 input=true := by
  unfold chk1
  change (match oneLead (CatalanCore.Li2.NVMod.FamilySource.V8C32.key 16) with | none=>false | some q=>ratUnitCheck 47 ((455876542810304656602005283840000:ℚ)^16*q))=true
  rw [oneLeadWith_spec (CatalanCore.Li2.NVMod.FamilySource.V8C32.key 16) (8) CatalanCore.Li2.NVMod.RegularFamily.V8C32.regularValue (CatalanCore.Li2.NVMod.RegularFamily.V8C32.h0_key 16) (CatalanCore.Li2.NVMod.RegularFamily.V8C32.regular_source 16)]
  decide +kernel
-- kcost: 3 s estimated; original endpoint check via proved source equalities
set_option trace.profiler true in
theorem endpointInf : chkInf input=true := by
  change (decide (16≤(slots (CatalanCore.Li2.NVMod.FamilySource.V8C32.key 16)).length) && ratUnitCheck 47 ((455876542810304656602005283840000:ℚ)^16*infLead (CatalanCore.Li2.NVMod.FamilySource.V8C32.key 16)))=true
  rw [infLeadNative_spec (CatalanCore.Li2.NVMod.FamilySource.V8C32.key 16) CatalanCore.Li2.NVMod.FamilySource.V8C32.num CatalanCore.Li2.NVMod.FamilySource.V8C32.den CatalanCore.Li2.NVMod.FamilySource.V8C32.indices CatalanCore.Li2.NVMod.FamilySource.V8C32.rho (CatalanCore.Li2.NVMod.FamilySource.V8C32.num_source 16) (CatalanCore.Li2.NVMod.FamilySource.V8C32.den_source 16) CatalanCore.Li2.NVMod.FamilySource.V8C32.indices_nodup ((CatalanCore.Li2.NVMod.FamilySource.V8C32.indices_set 16).trans (poles_eq_poleSet _)) rho_source]
  decide +kernel
-- kcost: 1 s estimated; coefficientwise integer remainder binding
set_option trace.profiler true in
theorem mod_ok : momentResidueCheck 47 16 CatalanCore.Li2.NVMod.FamilySource.V8C32.moments CatalanCore.Li2.NVMod.PolynomialData.V8C32S16.data.moments=true := by decide +kernel

-- kcost: 1 s estimated; existing arithmetic proofs and outer list length only
def interior : PolynomialCert.InteriorChecked input where
  data:=CatalanCore.Li2.NVMod.PolynomialData.V8C32S16.data.toCertificate
  bounds:=(PolynomialCompute.bounds_nat_transfer 16 47 CatalanCore.Li2.NVMod.PolynomialData.V8C32S16.data).symm.trans CatalanCore.Li2.NVMod.PolynomialData.V8C32S16.bounds_ok
  arithmetic:=(PolynomialCompute.arithmetic_transfer 16 47 CatalanCore.Li2.NVMod.PolynomialData.V8C32S16.data).symm.trans CatalanCore.Li2.NVMod.PolynomialData.V8C32S16.arithmetic_ok
  moments:=by
    intro e he
    exact momentResidueCheck_sound 47 16 CatalanCore.Li2.NVMod.FamilySource.V8C32.moments CatalanCore.Li2.NVMod.PolynomialData.V8C32S16.data.moments mod_ok (by decide +kernel) e he

def checked : KeyCertificate :=
  ⟨input,by decide +kernel,endpoint0,endpoint1,endpointInf,interior⟩
#print axioms checked
end
end CatalanCore.Li2.NVMod.KeyData.V8C32S16
