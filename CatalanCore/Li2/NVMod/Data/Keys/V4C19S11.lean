module
public import CatalanCore.Li2.NVMod.Data.Regular.V4C19
public import CatalanCore.Li2.NVMod.Data.Polynomial.V4C19S11
public import CatalanCore.Li2.NVMod.DataSupport.PolynomialPackageSupport
public import CatalanCore.Li2.NVMod.DataSupport.PolynomialInfSource
public import CatalanCore.Li2.NVMod.DataSupport.Factorials
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option backward.isDefEq.respectTransparency false
open Polynomial Finset
namespace CatalanCore.Li2.NVMod.KeyData.V4C19S11
open CatalanCore.Li2.NVMod CatalanCore.Li2.NVMod.DataSupport
noncomputable section

-- kcost: 1 s estimated; closed endpoint orders and literal fields, shared factorial theorem
def input : EndpointInput where
  -- kcost: 1 s estimated; finite endpoint orders, checked literal fields
  key:=CatalanCore.Li2.NVMod.FamilySource.V4C19.key 11
  p:=31
  D:=19654365366155520000
  clearZ:=18
  clearOne:=13
  v0:=66
  v1:=94
  D_pos:=by decide +kernel
  mz:=CatalanCore.Li2.NVMod.FamilySource.V4C19.mz
  moment_clear:=by
    intro i j
    apply CatalanCore.Li2.NVMod.FamilySource.V4C19.moment_source 11
    have hi:=i.isLt
    have hj:=j.isLt
    change i.val<11 at hi
    change j.val<11 at hj
    omega
  order_zero:=by decide +kernel
  order_one:=by
    change (94:ℤ)=(13:ℤ)*11+oneOrder (CatalanCore.Li2.NVMod.FamilySource.V4C19.key 11)
    rw [oneOrderWith_spec,CatalanCore.Li2.NVMod.RegularFamily.V4C19.h0_key]
    decide +kernel
  factorials:=allFactorials (CatalanCore.Li2.NVMod.FamilySource.V4C19.key 11)

theorem rho_source : ∀m∈poleSet (CatalanCore.Li2.NVMod.FamilySource.V4C19.key 11),CatalanCore.Li2.NVMod.FamilySource.V4C19.rho m=residue (CatalanCore.Li2.NVMod.FamilySource.V4C19.key 11) m := by
  intro m hm
  apply CatalanCore.Li2.NVMod.FamilySource.V4C19.rho_source 11 m
  rwa [(CatalanCore.Li2.NVMod.FamilySource.V4C19.indices_set 11).trans (poles_eq_poleSet _)]

-- kcost: 3 s estimated; original endpoint check via proved source equalities
set_option trace.profiler true in
theorem endpoint0 : chk0 input=true := by
  change ((topPoles (CatalanCore.Li2.NVMod.FamilySource.V4C19.key 11)).length == 11 && ratUnitCheck 31 ((19654365366155520000:ℚ)^11*zeroLead (CatalanCore.Li2.NVMod.FamilySource.V4C19.key 11)))=true
  rw [zeroLead_with_residues (CatalanCore.Li2.NVMod.FamilySource.V4C19.key 11) CatalanCore.Li2.NVMod.FamilySource.V4C19.rho rho_source]
  decide +kernel
-- kcost: 3 s estimated; original endpoint check via proved source equalities
set_option trace.profiler true in
theorem endpoint1 : chk1 input=true := by
  unfold chk1
  change (match oneLead (CatalanCore.Li2.NVMod.FamilySource.V4C19.key 11) with | none=>false | some q=>ratUnitCheck 31 ((19654365366155520000:ℚ)^11*q))=true
  rw [oneLeadWith_spec (CatalanCore.Li2.NVMod.FamilySource.V4C19.key 11) (7) CatalanCore.Li2.NVMod.RegularFamily.V4C19.regularValue (CatalanCore.Li2.NVMod.RegularFamily.V4C19.h0_key 11) (CatalanCore.Li2.NVMod.RegularFamily.V4C19.regular_source 11)]
  decide +kernel
-- kcost: 3 s estimated; original endpoint check via proved source equalities
set_option trace.profiler true in
theorem endpointInf : chkInf input=true := by
  change (decide (11≤(slots (CatalanCore.Li2.NVMod.FamilySource.V4C19.key 11)).length) && ratUnitCheck 31 ((19654365366155520000:ℚ)^11*infLead (CatalanCore.Li2.NVMod.FamilySource.V4C19.key 11)))=true
  rw [infLeadNative_spec (CatalanCore.Li2.NVMod.FamilySource.V4C19.key 11) CatalanCore.Li2.NVMod.FamilySource.V4C19.num CatalanCore.Li2.NVMod.FamilySource.V4C19.den CatalanCore.Li2.NVMod.FamilySource.V4C19.indices CatalanCore.Li2.NVMod.FamilySource.V4C19.rho (CatalanCore.Li2.NVMod.FamilySource.V4C19.num_source 11) (CatalanCore.Li2.NVMod.FamilySource.V4C19.den_source 11) CatalanCore.Li2.NVMod.FamilySource.V4C19.indices_nodup ((CatalanCore.Li2.NVMod.FamilySource.V4C19.indices_set 11).trans (poles_eq_poleSet _)) rho_source]
  decide +kernel
-- kcost: 1 s estimated; coefficientwise integer remainder binding
set_option trace.profiler true in
theorem mod_ok : momentResidueCheck 31 11 CatalanCore.Li2.NVMod.FamilySource.V4C19.moments CatalanCore.Li2.NVMod.PolynomialData.V4C19S11.data.moments=true := by decide +kernel

-- kcost: 1 s estimated; existing arithmetic proofs and outer list length only
def interior : PolynomialCert.InteriorChecked input where
  data:=CatalanCore.Li2.NVMod.PolynomialData.V4C19S11.data.toCertificate
  bounds:=(PolynomialCompute.bounds_nat_transfer 11 31 CatalanCore.Li2.NVMod.PolynomialData.V4C19S11.data).symm.trans CatalanCore.Li2.NVMod.PolynomialData.V4C19S11.bounds_ok
  arithmetic:=(PolynomialCompute.arithmetic_transfer 11 31 CatalanCore.Li2.NVMod.PolynomialData.V4C19S11.data).symm.trans CatalanCore.Li2.NVMod.PolynomialData.V4C19S11.arithmetic_ok
  moments:=by
    intro e he
    exact momentResidueCheck_sound 31 11 CatalanCore.Li2.NVMod.FamilySource.V4C19.moments CatalanCore.Li2.NVMod.PolynomialData.V4C19S11.data.moments mod_ok (by decide +kernel) e he

def checked : KeyCertificate :=
  ⟨input,by decide +kernel,endpoint0,endpoint1,endpointInf,interior⟩
#print axioms checked
end
end CatalanCore.Li2.NVMod.KeyData.V4C19S11
