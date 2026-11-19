module
public import CatalanCore.Li2.NVMod.Data.Regular.V11C45
public import CatalanCore.Li2.NVMod.Data.Polynomial.V11C45S23
public import CatalanCore.Li2.NVMod.DataSupport.PolynomialPackageSupport
public import CatalanCore.Li2.NVMod.DataSupport.PolynomialInfSource
public import CatalanCore.Li2.NVMod.DataSupport.Factorials
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option backward.isDefEq.respectTransparency false
open Polynomial Finset
namespace CatalanCore.Li2.NVMod.KeyData.V11C45S23
open CatalanCore.Li2.NVMod CatalanCore.Li2.NVMod.DataSupport
noncomputable section

-- kcost: 1 s estimated; closed endpoint orders and literal fields, shared factorial theorem
def input : EndpointInput where
  -- kcost: 1 s estimated; finite endpoint orders, checked literal fields
  key:=CatalanCore.Li2.NVMod.FamilySource.V11C45.key 23
  p:=53
  D:=113639681621550538211119330541899419282309120000000
  clearZ:=44
  clearOne:=32
  v0:=276
  v1:=464
  D_pos:=by decide +kernel
  mz:=CatalanCore.Li2.NVMod.FamilySource.V11C45.mz
  moment_clear:=by
    intro i j
    apply CatalanCore.Li2.NVMod.FamilySource.V11C45.moment_source 23
    have hi:=i.isLt
    have hj:=j.isLt
    change i.val<23 at hi
    change j.val<23 at hj
    omega
  order_zero:=by decide +kernel
  order_one:=by
    change (464:ℤ)=(32:ℤ)*23+oneOrder (CatalanCore.Li2.NVMod.FamilySource.V11C45.key 23)
    rw [oneOrderWith_spec,CatalanCore.Li2.NVMod.RegularFamily.V11C45.h0_key]
    decide +kernel
  factorials:=allFactorials (CatalanCore.Li2.NVMod.FamilySource.V11C45.key 23)

theorem rho_source : ∀m∈poleSet (CatalanCore.Li2.NVMod.FamilySource.V11C45.key 23),CatalanCore.Li2.NVMod.FamilySource.V11C45.rho m=residue (CatalanCore.Li2.NVMod.FamilySource.V11C45.key 23) m := by
  intro m hm
  apply CatalanCore.Li2.NVMod.FamilySource.V11C45.rho_source 23 m
  rwa [(CatalanCore.Li2.NVMod.FamilySource.V11C45.indices_set 23).trans (poles_eq_poleSet _)]

-- kcost: 3 s estimated; original endpoint check via proved source equalities
set_option trace.profiler true in
theorem endpoint0 : chk0 input=true := by
  change ((topPoles (CatalanCore.Li2.NVMod.FamilySource.V11C45.key 23)).length == 23 && ratUnitCheck 53 ((113639681621550538211119330541899419282309120000000:ℚ)^23*zeroLead (CatalanCore.Li2.NVMod.FamilySource.V11C45.key 23)))=true
  rw [zeroLead_with_residues (CatalanCore.Li2.NVMod.FamilySource.V11C45.key 23) CatalanCore.Li2.NVMod.FamilySource.V11C45.rho rho_source]
  decide +kernel
-- kcost: 3 s estimated; original endpoint check via proved source equalities
set_option trace.profiler true in
theorem endpoint1 : chk1 input=true := by
  unfold chk1
  change (match oneLead (CatalanCore.Li2.NVMod.FamilySource.V11C45.key 23) with | none=>false | some q=>ratUnitCheck 53 ((113639681621550538211119330541899419282309120000000:ℚ)^23*q))=true
  rw [oneLeadWith_spec (CatalanCore.Li2.NVMod.FamilySource.V11C45.key 23) (12) CatalanCore.Li2.NVMod.RegularFamily.V11C45.regularValue (CatalanCore.Li2.NVMod.RegularFamily.V11C45.h0_key 23) (CatalanCore.Li2.NVMod.RegularFamily.V11C45.regular_source 23)]
  decide +kernel
-- kcost: 3 s estimated; original endpoint check via proved source equalities
set_option trace.profiler true in
theorem endpointInf : chkInf input=true := by
  change (decide (23≤(slots (CatalanCore.Li2.NVMod.FamilySource.V11C45.key 23)).length) && ratUnitCheck 53 ((113639681621550538211119330541899419282309120000000:ℚ)^23*infLead (CatalanCore.Li2.NVMod.FamilySource.V11C45.key 23)))=true
  rw [infLeadNative_spec (CatalanCore.Li2.NVMod.FamilySource.V11C45.key 23) CatalanCore.Li2.NVMod.FamilySource.V11C45.num CatalanCore.Li2.NVMod.FamilySource.V11C45.den CatalanCore.Li2.NVMod.FamilySource.V11C45.indices CatalanCore.Li2.NVMod.FamilySource.V11C45.rho (CatalanCore.Li2.NVMod.FamilySource.V11C45.num_source 23) (CatalanCore.Li2.NVMod.FamilySource.V11C45.den_source 23) CatalanCore.Li2.NVMod.FamilySource.V11C45.indices_nodup ((CatalanCore.Li2.NVMod.FamilySource.V11C45.indices_set 23).trans (poles_eq_poleSet _)) rho_source]
  decide +kernel
-- kcost: 1 s estimated; coefficientwise integer remainder binding
set_option trace.profiler true in
theorem mod_ok : momentResidueCheck 53 23 CatalanCore.Li2.NVMod.FamilySource.V11C45.moments CatalanCore.Li2.NVMod.PolynomialData.V11C45S23.data.moments=true := by decide +kernel

-- kcost: 1 s estimated; existing arithmetic proofs and outer list length only
def interior : PolynomialCert.InteriorChecked input where
  data:=CatalanCore.Li2.NVMod.PolynomialData.V11C45S23.data.toCertificate
  bounds:=(PolynomialCompute.bounds_nat_transfer 23 53 CatalanCore.Li2.NVMod.PolynomialData.V11C45S23.data).symm.trans CatalanCore.Li2.NVMod.PolynomialData.V11C45S23.bounds_ok
  arithmetic:=(PolynomialCompute.arithmetic_transfer 23 53 CatalanCore.Li2.NVMod.PolynomialData.V11C45S23.data).symm.trans CatalanCore.Li2.NVMod.PolynomialData.V11C45S23.arithmetic_ok
  moments:=by
    intro e he
    exact momentResidueCheck_sound 53 23 CatalanCore.Li2.NVMod.FamilySource.V11C45.moments CatalanCore.Li2.NVMod.PolynomialData.V11C45S23.data.moments mod_ok (by decide +kernel) e he

def checked : KeyCertificate :=
  ⟨input,by decide +kernel,endpoint0,endpoint1,endpointInf,interior⟩
#print axioms checked
end
end CatalanCore.Li2.NVMod.KeyData.V11C45S23
