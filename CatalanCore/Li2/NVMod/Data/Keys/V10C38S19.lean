module
public import CatalanCore.Li2.NVMod.Data.Regular.V10C38
public import CatalanCore.Li2.NVMod.Data.Polynomial.V10C38S19
public import CatalanCore.Li2.NVMod.DataSupport.PolynomialPackageSupport
public import CatalanCore.Li2.NVMod.DataSupport.PolynomialInfSource
public import CatalanCore.Li2.NVMod.DataSupport.Factorials
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option backward.isDefEq.respectTransparency false
open Polynomial Finset
namespace CatalanCore.Li2.NVMod.KeyData.V10C38S19
open CatalanCore.Li2.NVMod CatalanCore.Li2.NVMod.DataSupport
noncomputable section

-- kcost: 1 s estimated; closed endpoint orders and literal fields, shared factorial theorem
def input : EndpointInput where
  -- kcost: 1 s estimated; finite endpoint orders, checked literal fields
  key:=CatalanCore.Li2.NVMod.FamilySource.V10C38.key 19
  p:=61
  D:=5333755550880564482243461820928000000
  clearZ:=37
  clearOne:=28
  v0:=190
  v1:=322
  D_pos:=by decide +kernel
  mz:=CatalanCore.Li2.NVMod.FamilySource.V10C38.mz
  moment_clear:=by
    intro i j
    apply CatalanCore.Li2.NVMod.FamilySource.V10C38.moment_source 19
    have hi:=i.isLt
    have hj:=j.isLt
    change i.val<19 at hi
    change j.val<19 at hj
    omega
  order_zero:=by decide +kernel
  order_one:=by
    change (322:ℤ)=(28:ℤ)*19+oneOrder (CatalanCore.Li2.NVMod.FamilySource.V10C38.key 19)
    rw [oneOrderWith_spec,CatalanCore.Li2.NVMod.RegularFamily.V10C38.h0_key]
    decide +kernel
  factorials:=allFactorials (CatalanCore.Li2.NVMod.FamilySource.V10C38.key 19)

theorem rho_source : ∀m∈poleSet (CatalanCore.Li2.NVMod.FamilySource.V10C38.key 19),CatalanCore.Li2.NVMod.FamilySource.V10C38.rho m=residue (CatalanCore.Li2.NVMod.FamilySource.V10C38.key 19) m := by
  intro m hm
  apply CatalanCore.Li2.NVMod.FamilySource.V10C38.rho_source 19 m
  rwa [(CatalanCore.Li2.NVMod.FamilySource.V10C38.indices_set 19).trans (poles_eq_poleSet _)]

-- kcost: 3 s estimated; original endpoint check via proved source equalities
set_option trace.profiler true in
theorem endpoint0 : chk0 input=true := by
  change ((topPoles (CatalanCore.Li2.NVMod.FamilySource.V10C38.key 19)).length == 19 && ratUnitCheck 61 ((5333755550880564482243461820928000000:ℚ)^19*zeroLead (CatalanCore.Li2.NVMod.FamilySource.V10C38.key 19)))=true
  rw [zeroLead_with_residues (CatalanCore.Li2.NVMod.FamilySource.V10C38.key 19) CatalanCore.Li2.NVMod.FamilySource.V10C38.rho rho_source]
  decide +kernel
-- kcost: 3 s estimated; original endpoint check via proved source equalities
set_option trace.profiler true in
theorem endpoint1 : chk1 input=true := by
  unfold chk1
  change (match oneLead (CatalanCore.Li2.NVMod.FamilySource.V10C38.key 19) with | none=>false | some q=>ratUnitCheck 61 ((5333755550880564482243461820928000000:ℚ)^19*q))=true
  rw [oneLeadWith_spec (CatalanCore.Li2.NVMod.FamilySource.V10C38.key 19) (8) CatalanCore.Li2.NVMod.RegularFamily.V10C38.regularValue (CatalanCore.Li2.NVMod.RegularFamily.V10C38.h0_key 19) (CatalanCore.Li2.NVMod.RegularFamily.V10C38.regular_source 19)]
  decide +kernel
-- kcost: 3 s estimated; original endpoint check via proved source equalities
set_option trace.profiler true in
theorem endpointInf : chkInf input=true := by
  change (decide (19≤(slots (CatalanCore.Li2.NVMod.FamilySource.V10C38.key 19)).length) && ratUnitCheck 61 ((5333755550880564482243461820928000000:ℚ)^19*infLead (CatalanCore.Li2.NVMod.FamilySource.V10C38.key 19)))=true
  rw [infLeadNative_spec (CatalanCore.Li2.NVMod.FamilySource.V10C38.key 19) CatalanCore.Li2.NVMod.FamilySource.V10C38.num CatalanCore.Li2.NVMod.FamilySource.V10C38.den CatalanCore.Li2.NVMod.FamilySource.V10C38.indices CatalanCore.Li2.NVMod.FamilySource.V10C38.rho (CatalanCore.Li2.NVMod.FamilySource.V10C38.num_source 19) (CatalanCore.Li2.NVMod.FamilySource.V10C38.den_source 19) CatalanCore.Li2.NVMod.FamilySource.V10C38.indices_nodup ((CatalanCore.Li2.NVMod.FamilySource.V10C38.indices_set 19).trans (poles_eq_poleSet _)) rho_source]
  decide +kernel
-- kcost: 1 s estimated; coefficientwise integer remainder binding
set_option trace.profiler true in
theorem mod_ok : momentResidueCheck 61 19 CatalanCore.Li2.NVMod.FamilySource.V10C38.moments CatalanCore.Li2.NVMod.PolynomialData.V10C38S19.data.moments=true := by decide +kernel

-- kcost: 1 s estimated; existing arithmetic proofs and outer list length only
def interior : PolynomialCert.InteriorChecked input where
  data:=CatalanCore.Li2.NVMod.PolynomialData.V10C38S19.data.toCertificate
  bounds:=(PolynomialCompute.bounds_nat_transfer 19 61 CatalanCore.Li2.NVMod.PolynomialData.V10C38S19.data).symm.trans CatalanCore.Li2.NVMod.PolynomialData.V10C38S19.bounds_ok
  arithmetic:=(PolynomialCompute.arithmetic_transfer 19 61 CatalanCore.Li2.NVMod.PolynomialData.V10C38S19.data).symm.trans CatalanCore.Li2.NVMod.PolynomialData.V10C38S19.arithmetic_ok
  moments:=by
    intro e he
    exact momentResidueCheck_sound 61 19 CatalanCore.Li2.NVMod.FamilySource.V10C38.moments CatalanCore.Li2.NVMod.PolynomialData.V10C38S19.data.moments mod_ok (by decide +kernel) e he

def checked : KeyCertificate :=
  ⟨input,by decide +kernel,endpoint0,endpoint1,endpointInf,interior⟩
#print axioms checked
end
end CatalanCore.Li2.NVMod.KeyData.V10C38S19
