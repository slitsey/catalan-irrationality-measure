module
public import CatalanCore.Li2.NVMod.Data.Regular.V5C22
public import CatalanCore.Li2.NVMod.Data.Polynomial.V5C22S12
public import CatalanCore.Li2.NVMod.DataSupport.PolynomialPackageSupport
public import CatalanCore.Li2.NVMod.DataSupport.PolynomialInfSource
public import CatalanCore.Li2.NVMod.DataSupport.Factorials
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option backward.isDefEq.respectTransparency false
open Polynomial Finset
namespace CatalanCore.Li2.NVMod.KeyData.V5C22S12
open CatalanCore.Li2.NVMod CatalanCore.Li2.NVMod.DataSupport
noncomputable section

-- kcost: 1 s estimated; closed endpoint orders and literal fields, shared factorial theorem
def input : EndpointInput where
  -- kcost: 1 s estimated; finite endpoint orders, checked literal fields
  key:=CatalanCore.Li2.NVMod.FamilySource.V5C22.key 12
  p:=23
  D:=754727630060371968000
  clearZ:=21
  clearOne:=15
  v0:=78
  v1:=116
  D_pos:=by decide +kernel
  mz:=CatalanCore.Li2.NVMod.FamilySource.V5C22.mz
  moment_clear:=by
    intro i j
    apply CatalanCore.Li2.NVMod.FamilySource.V5C22.moment_source 12
    have hi:=i.isLt
    have hj:=j.isLt
    change i.val<12 at hi
    change j.val<12 at hj
    omega
  order_zero:=by decide +kernel
  order_one:=by
    change (116:ℤ)=(15:ℤ)*12+oneOrder (CatalanCore.Li2.NVMod.FamilySource.V5C22.key 12)
    rw [oneOrderWith_spec,CatalanCore.Li2.NVMod.RegularFamily.V5C22.h0_key]
    decide +kernel
  factorials:=allFactorials (CatalanCore.Li2.NVMod.FamilySource.V5C22.key 12)

theorem rho_source : ∀m∈poleSet (CatalanCore.Li2.NVMod.FamilySource.V5C22.key 12),CatalanCore.Li2.NVMod.FamilySource.V5C22.rho m=residue (CatalanCore.Li2.NVMod.FamilySource.V5C22.key 12) m := by
  intro m hm
  apply CatalanCore.Li2.NVMod.FamilySource.V5C22.rho_source 12 m
  rwa [(CatalanCore.Li2.NVMod.FamilySource.V5C22.indices_set 12).trans (poles_eq_poleSet _)]

-- kcost: 3 s estimated; original endpoint check via proved source equalities
set_option trace.profiler true in
theorem endpoint0 : chk0 input=true := by
  change ((topPoles (CatalanCore.Li2.NVMod.FamilySource.V5C22.key 12)).length == 12 && ratUnitCheck 23 ((754727630060371968000:ℚ)^12*zeroLead (CatalanCore.Li2.NVMod.FamilySource.V5C22.key 12)))=true
  rw [zeroLead_with_residues (CatalanCore.Li2.NVMod.FamilySource.V5C22.key 12) CatalanCore.Li2.NVMod.FamilySource.V5C22.rho rho_source]
  decide +kernel
-- kcost: 3 s estimated; original endpoint check via proved source equalities
set_option trace.profiler true in
theorem endpoint1 : chk1 input=true := by
  unfold chk1
  change (match oneLead (CatalanCore.Li2.NVMod.FamilySource.V5C22.key 12) with | none=>false | some q=>ratUnitCheck 23 ((754727630060371968000:ℚ)^12*q))=true
  rw [oneLeadWith_spec (CatalanCore.Li2.NVMod.FamilySource.V5C22.key 12) (7) CatalanCore.Li2.NVMod.RegularFamily.V5C22.regularValue (CatalanCore.Li2.NVMod.RegularFamily.V5C22.h0_key 12) (CatalanCore.Li2.NVMod.RegularFamily.V5C22.regular_source 12)]
  decide +kernel
-- kcost: 3 s estimated; original endpoint check via proved source equalities
set_option trace.profiler true in
theorem endpointInf : chkInf input=true := by
  change (decide (12≤(slots (CatalanCore.Li2.NVMod.FamilySource.V5C22.key 12)).length) && ratUnitCheck 23 ((754727630060371968000:ℚ)^12*infLead (CatalanCore.Li2.NVMod.FamilySource.V5C22.key 12)))=true
  rw [infLeadNative_spec (CatalanCore.Li2.NVMod.FamilySource.V5C22.key 12) CatalanCore.Li2.NVMod.FamilySource.V5C22.num CatalanCore.Li2.NVMod.FamilySource.V5C22.den CatalanCore.Li2.NVMod.FamilySource.V5C22.indices CatalanCore.Li2.NVMod.FamilySource.V5C22.rho (CatalanCore.Li2.NVMod.FamilySource.V5C22.num_source 12) (CatalanCore.Li2.NVMod.FamilySource.V5C22.den_source 12) CatalanCore.Li2.NVMod.FamilySource.V5C22.indices_nodup ((CatalanCore.Li2.NVMod.FamilySource.V5C22.indices_set 12).trans (poles_eq_poleSet _)) rho_source]
  decide +kernel
-- kcost: 1 s estimated; coefficientwise integer remainder binding
set_option trace.profiler true in
theorem mod_ok : momentResidueCheck 23 12 CatalanCore.Li2.NVMod.FamilySource.V5C22.moments CatalanCore.Li2.NVMod.PolynomialData.V5C22S12.data.moments=true := by decide +kernel

-- kcost: 1 s estimated; existing arithmetic proofs and outer list length only
def interior : PolynomialCert.InteriorChecked input where
  data:=CatalanCore.Li2.NVMod.PolynomialData.V5C22S12.data.toCertificate
  bounds:=(PolynomialCompute.bounds_nat_transfer 12 23 CatalanCore.Li2.NVMod.PolynomialData.V5C22S12.data).symm.trans CatalanCore.Li2.NVMod.PolynomialData.V5C22S12.bounds_ok
  arithmetic:=(PolynomialCompute.arithmetic_transfer 12 23 CatalanCore.Li2.NVMod.PolynomialData.V5C22S12.data).symm.trans CatalanCore.Li2.NVMod.PolynomialData.V5C22S12.arithmetic_ok
  moments:=by
    intro e he
    exact momentResidueCheck_sound 23 12 CatalanCore.Li2.NVMod.FamilySource.V5C22.moments CatalanCore.Li2.NVMod.PolynomialData.V5C22S12.data.moments mod_ok (by decide +kernel) e he

def checked : KeyCertificate :=
  ⟨input,by decide +kernel,endpoint0,endpoint1,endpointInf,interior⟩
#print axioms checked
end
end CatalanCore.Li2.NVMod.KeyData.V5C22S12
