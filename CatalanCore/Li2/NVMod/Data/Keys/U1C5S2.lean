module
public import CatalanCore.Li2.NVMod.Data.Regular.U1C5
public import CatalanCore.Li2.NVMod.Data.Polynomial.U1C5S2
public import CatalanCore.Li2.NVMod.DataSupport.PolynomialPackageSupport
public import CatalanCore.Li2.NVMod.DataSupport.PolynomialInfSource
public import CatalanCore.Li2.NVMod.DataSupport.Factorials
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option backward.isDefEq.respectTransparency false
open Polynomial Finset
namespace CatalanCore.Li2.NVMod.KeyData.U1C5S2
open CatalanCore.Li2.NVMod CatalanCore.Li2.NVMod.DataSupport
noncomputable section

-- kcost: 1 s estimated; closed endpoint orders and literal fields, shared factorial theorem
def input : EndpointInput where
  -- kcost: 1 s estimated; finite endpoint orders, checked literal fields
  key:=CatalanCore.Li2.NVMod.FamilySource.U1C5.key 2
  p:=31
  D:=21600
  clearZ:=5
  clearOne:=3
  v0:=3
  v1:=5
  D_pos:=by decide +kernel
  mz:=CatalanCore.Li2.NVMod.FamilySource.U1C5.mz
  moment_clear:=by
    intro i j
    apply CatalanCore.Li2.NVMod.FamilySource.U1C5.moment_source 2
    have hi:=i.isLt
    have hj:=j.isLt
    change i.val<2 at hi
    change j.val<2 at hj
    omega
  order_zero:=by decide +kernel
  order_one:=by
    change (5:ℤ)=(3:ℤ)*2+oneOrder (CatalanCore.Li2.NVMod.FamilySource.U1C5.key 2)
    rw [oneOrderWith_spec,CatalanCore.Li2.NVMod.RegularFamily.U1C5.h0_key]
    decide +kernel
  factorials:=allFactorials (CatalanCore.Li2.NVMod.FamilySource.U1C5.key 2)

theorem rho_source : ∀m∈poleSet (CatalanCore.Li2.NVMod.FamilySource.U1C5.key 2),CatalanCore.Li2.NVMod.FamilySource.U1C5.rho m=residue (CatalanCore.Li2.NVMod.FamilySource.U1C5.key 2) m := by
  intro m hm
  apply CatalanCore.Li2.NVMod.FamilySource.U1C5.rho_source 2 m
  rwa [(CatalanCore.Li2.NVMod.FamilySource.U1C5.indices_set 2).trans (poles_eq_poleSet _)]

-- kcost: 3 s estimated; original endpoint check via proved source equalities
set_option trace.profiler true in
theorem endpoint0 : chk0 input=true := by
  change ((topPoles (CatalanCore.Li2.NVMod.FamilySource.U1C5.key 2)).length == 2 && ratUnitCheck 31 ((21600:ℚ)^2*zeroLead (CatalanCore.Li2.NVMod.FamilySource.U1C5.key 2)))=true
  rw [zeroLead_with_residues (CatalanCore.Li2.NVMod.FamilySource.U1C5.key 2) CatalanCore.Li2.NVMod.FamilySource.U1C5.rho rho_source]
  decide +kernel
-- kcost: 3 s estimated; original endpoint check via proved source equalities
set_option trace.profiler true in
theorem endpoint1 : chk1 input=true := by
  unfold chk1
  change (match oneLead (CatalanCore.Li2.NVMod.FamilySource.U1C5.key 2) with | none=>false | some q=>ratUnitCheck 31 ((21600:ℚ)^2*q))=true
  rw [oneLeadWith_spec (CatalanCore.Li2.NVMod.FamilySource.U1C5.key 2) (1) CatalanCore.Li2.NVMod.RegularFamily.U1C5.regularValue (CatalanCore.Li2.NVMod.RegularFamily.U1C5.h0_key 2) (CatalanCore.Li2.NVMod.RegularFamily.U1C5.regular_source 2)]
  decide +kernel
-- kcost: 3 s estimated; original endpoint check via proved source equalities
set_option trace.profiler true in
theorem endpointInf : chkInf input=true := by
  change (decide (2≤(slots (CatalanCore.Li2.NVMod.FamilySource.U1C5.key 2)).length) && ratUnitCheck 31 ((21600:ℚ)^2*infLead (CatalanCore.Li2.NVMod.FamilySource.U1C5.key 2)))=true
  rw [infLeadNative_spec (CatalanCore.Li2.NVMod.FamilySource.U1C5.key 2) CatalanCore.Li2.NVMod.FamilySource.U1C5.num CatalanCore.Li2.NVMod.FamilySource.U1C5.den CatalanCore.Li2.NVMod.FamilySource.U1C5.indices CatalanCore.Li2.NVMod.FamilySource.U1C5.rho (CatalanCore.Li2.NVMod.FamilySource.U1C5.num_source 2) (CatalanCore.Li2.NVMod.FamilySource.U1C5.den_source 2) CatalanCore.Li2.NVMod.FamilySource.U1C5.indices_nodup ((CatalanCore.Li2.NVMod.FamilySource.U1C5.indices_set 2).trans (poles_eq_poleSet _)) rho_source]
  decide +kernel
-- kcost: 1 s estimated; coefficientwise integer remainder binding
set_option trace.profiler true in
theorem mod_ok : momentResidueCheck 31 2 CatalanCore.Li2.NVMod.FamilySource.U1C5.moments CatalanCore.Li2.NVMod.PolynomialData.U1C5S2.data.moments=true := by decide +kernel

-- kcost: 1 s estimated; existing arithmetic proofs and outer list length only
def interior : PolynomialCert.InteriorChecked input where
  data:=CatalanCore.Li2.NVMod.PolynomialData.U1C5S2.data.toCertificate
  bounds:=(PolynomialCompute.bounds_nat_transfer 2 31 CatalanCore.Li2.NVMod.PolynomialData.U1C5S2.data).symm.trans CatalanCore.Li2.NVMod.PolynomialData.U1C5S2.bounds_ok
  arithmetic:=(PolynomialCompute.arithmetic_transfer 2 31 CatalanCore.Li2.NVMod.PolynomialData.U1C5S2.data).symm.trans CatalanCore.Li2.NVMod.PolynomialData.U1C5S2.arithmetic_ok
  moments:=by
    intro e he
    exact momentResidueCheck_sound 31 2 CatalanCore.Li2.NVMod.FamilySource.U1C5.moments CatalanCore.Li2.NVMod.PolynomialData.U1C5S2.data.moments mod_ok (by decide +kernel) e he

def checked : KeyCertificate :=
  ⟨input,by decide +kernel,endpoint0,endpoint1,endpointInf,interior⟩
#print axioms checked
end
end CatalanCore.Li2.NVMod.KeyData.U1C5S2
