module
public import CatalanCore.Li2.NVMod.Data.Regular.V4C18
public import CatalanCore.Li2.NVMod.Data.Polynomial.V4C18S10
public import CatalanCore.Li2.NVMod.DataSupport.PolynomialPackageSupport
public import CatalanCore.Li2.NVMod.DataSupport.PolynomialInfSource
public import CatalanCore.Li2.NVMod.DataSupport.Factorials
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option backward.isDefEq.respectTransparency false
open Polynomial Finset
namespace CatalanCore.Li2.NVMod.KeyData.V4C18S10
open CatalanCore.Li2.NVMod CatalanCore.Li2.NVMod.DataSupport
noncomputable section

-- kcost: 1 s estimated; closed endpoint orders and literal fields, shared factorial theorem
def input : EndpointInput where
  -- kcost: 1 s estimated; finite endpoint orders, checked literal fields
  key:=CatalanCore.Li2.NVMod.FamilySource.V4C18.key 10
  p:=29
  D:=1403883240439680000
  clearZ:=17
  clearOne:=12
  v0:=55
  v1:=78
  D_pos:=by decide +kernel
  mz:=CatalanCore.Li2.NVMod.FamilySource.V4C18.mz
  moment_clear:=by
    intro i j
    apply CatalanCore.Li2.NVMod.FamilySource.V4C18.moment_source 10
    have hi:=i.isLt
    have hj:=j.isLt
    change i.val<10 at hi
    change j.val<10 at hj
    omega
  order_zero:=by decide +kernel
  order_one:=by
    change (78:ℤ)=(12:ℤ)*10+oneOrder (CatalanCore.Li2.NVMod.FamilySource.V4C18.key 10)
    rw [oneOrderWith_spec,CatalanCore.Li2.NVMod.RegularFamily.V4C18.h0_key]
    decide +kernel
  factorials:=allFactorials (CatalanCore.Li2.NVMod.FamilySource.V4C18.key 10)

theorem rho_source : ∀m∈poleSet (CatalanCore.Li2.NVMod.FamilySource.V4C18.key 10),CatalanCore.Li2.NVMod.FamilySource.V4C18.rho m=residue (CatalanCore.Li2.NVMod.FamilySource.V4C18.key 10) m := by
  intro m hm
  apply CatalanCore.Li2.NVMod.FamilySource.V4C18.rho_source 10 m
  rwa [(CatalanCore.Li2.NVMod.FamilySource.V4C18.indices_set 10).trans (poles_eq_poleSet _)]

-- kcost: 3 s estimated; original endpoint check via proved source equalities
set_option trace.profiler true in
theorem endpoint0 : chk0 input=true := by
  change ((topPoles (CatalanCore.Li2.NVMod.FamilySource.V4C18.key 10)).length == 10 && ratUnitCheck 29 ((1403883240439680000:ℚ)^10*zeroLead (CatalanCore.Li2.NVMod.FamilySource.V4C18.key 10)))=true
  rw [zeroLead_with_residues (CatalanCore.Li2.NVMod.FamilySource.V4C18.key 10) CatalanCore.Li2.NVMod.FamilySource.V4C18.rho rho_source]
  decide +kernel
-- kcost: 3 s estimated; original endpoint check via proved source equalities
set_option trace.profiler true in
theorem endpoint1 : chk1 input=true := by
  unfold chk1
  change (match oneLead (CatalanCore.Li2.NVMod.FamilySource.V4C18.key 10) with | none=>false | some q=>ratUnitCheck 29 ((1403883240439680000:ℚ)^10*q))=true
  rw [oneLeadWith_spec (CatalanCore.Li2.NVMod.FamilySource.V4C18.key 10) (6) CatalanCore.Li2.NVMod.RegularFamily.V4C18.regularValue (CatalanCore.Li2.NVMod.RegularFamily.V4C18.h0_key 10) (CatalanCore.Li2.NVMod.RegularFamily.V4C18.regular_source 10)]
  decide +kernel
-- kcost: 3 s estimated; original endpoint check via proved source equalities
set_option trace.profiler true in
theorem endpointInf : chkInf input=true := by
  change (decide (10≤(slots (CatalanCore.Li2.NVMod.FamilySource.V4C18.key 10)).length) && ratUnitCheck 29 ((1403883240439680000:ℚ)^10*infLead (CatalanCore.Li2.NVMod.FamilySource.V4C18.key 10)))=true
  rw [infLeadNative_spec (CatalanCore.Li2.NVMod.FamilySource.V4C18.key 10) CatalanCore.Li2.NVMod.FamilySource.V4C18.num CatalanCore.Li2.NVMod.FamilySource.V4C18.den CatalanCore.Li2.NVMod.FamilySource.V4C18.indices CatalanCore.Li2.NVMod.FamilySource.V4C18.rho (CatalanCore.Li2.NVMod.FamilySource.V4C18.num_source 10) (CatalanCore.Li2.NVMod.FamilySource.V4C18.den_source 10) CatalanCore.Li2.NVMod.FamilySource.V4C18.indices_nodup ((CatalanCore.Li2.NVMod.FamilySource.V4C18.indices_set 10).trans (poles_eq_poleSet _)) rho_source]
  decide +kernel
-- kcost: 1 s estimated; coefficientwise integer remainder binding
set_option trace.profiler true in
theorem mod_ok : momentResidueCheck 29 10 CatalanCore.Li2.NVMod.FamilySource.V4C18.moments CatalanCore.Li2.NVMod.PolynomialData.V4C18S10.data.moments=true := by decide +kernel

-- kcost: 1 s estimated; existing arithmetic proofs and outer list length only
def interior : PolynomialCert.InteriorChecked input where
  data:=CatalanCore.Li2.NVMod.PolynomialData.V4C18S10.data.toCertificate
  bounds:=(PolynomialCompute.bounds_nat_transfer 10 29 CatalanCore.Li2.NVMod.PolynomialData.V4C18S10.data).symm.trans CatalanCore.Li2.NVMod.PolynomialData.V4C18S10.bounds_ok
  arithmetic:=(PolynomialCompute.arithmetic_transfer 10 29 CatalanCore.Li2.NVMod.PolynomialData.V4C18S10.data).symm.trans CatalanCore.Li2.NVMod.PolynomialData.V4C18S10.arithmetic_ok
  moments:=by
    intro e he
    exact momentResidueCheck_sound 29 10 CatalanCore.Li2.NVMod.FamilySource.V4C18.moments CatalanCore.Li2.NVMod.PolynomialData.V4C18S10.data.moments mod_ok (by decide +kernel) e he

def checked : KeyCertificate :=
  ⟨input,by decide +kernel,endpoint0,endpoint1,endpointInf,interior⟩
#print axioms checked
end
end CatalanCore.Li2.NVMod.KeyData.V4C18S10
