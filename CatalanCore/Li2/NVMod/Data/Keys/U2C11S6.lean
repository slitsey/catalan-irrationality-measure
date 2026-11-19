module
public import CatalanCore.Li2.NVMod.Data.Regular.U2C11
public import CatalanCore.Li2.NVMod.Data.Polynomial.U2C11S6
public import CatalanCore.Li2.NVMod.DataSupport.PolynomialPackageSupport
public import CatalanCore.Li2.NVMod.DataSupport.PolynomialInfSource
public import CatalanCore.Li2.NVMod.DataSupport.Factorials
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option backward.isDefEq.respectTransparency false
open Polynomial Finset
namespace CatalanCore.Li2.NVMod.KeyData.U2C11S6
open CatalanCore.Li2.NVMod CatalanCore.Li2.NVMod.DataSupport
noncomputable section

-- kcost: 1 s estimated; closed endpoint orders and literal fields, shared factorial theorem
def input : EndpointInput where
  -- kcost: 1 s estimated; finite endpoint orders, checked literal fields
  key:=CatalanCore.Li2.NVMod.FamilySource.U2C11.key 6
  p:=17
  D:=7745455872000
  clearZ:=11
  clearOne:=8
  v0:=21
  v1:=36
  D_pos:=by decide +kernel
  mz:=CatalanCore.Li2.NVMod.FamilySource.U2C11.mz
  moment_clear:=by
    intro i j
    apply CatalanCore.Li2.NVMod.FamilySource.U2C11.moment_source 6
    have hi:=i.isLt
    have hj:=j.isLt
    change i.val<6 at hi
    change j.val<6 at hj
    omega
  order_zero:=by decide +kernel
  order_one:=by
    change (36:ℤ)=(8:ℤ)*6+oneOrder (CatalanCore.Li2.NVMod.FamilySource.U2C11.key 6)
    rw [oneOrderWith_spec,CatalanCore.Li2.NVMod.RegularFamily.U2C11.h0_key]
    decide +kernel
  factorials:=allFactorials (CatalanCore.Li2.NVMod.FamilySource.U2C11.key 6)

theorem rho_source : ∀m∈poleSet (CatalanCore.Li2.NVMod.FamilySource.U2C11.key 6),CatalanCore.Li2.NVMod.FamilySource.U2C11.rho m=residue (CatalanCore.Li2.NVMod.FamilySource.U2C11.key 6) m := by
  intro m hm
  apply CatalanCore.Li2.NVMod.FamilySource.U2C11.rho_source 6 m
  rwa [(CatalanCore.Li2.NVMod.FamilySource.U2C11.indices_set 6).trans (poles_eq_poleSet _)]

-- kcost: 3 s estimated; original endpoint check via proved source equalities
set_option trace.profiler true in
theorem endpoint0 : chk0 input=true := by
  change ((topPoles (CatalanCore.Li2.NVMod.FamilySource.U2C11.key 6)).length == 6 && ratUnitCheck 17 ((7745455872000:ℚ)^6*zeroLead (CatalanCore.Li2.NVMod.FamilySource.U2C11.key 6)))=true
  rw [zeroLead_with_residues (CatalanCore.Li2.NVMod.FamilySource.U2C11.key 6) CatalanCore.Li2.NVMod.FamilySource.U2C11.rho rho_source]
  decide +kernel
-- kcost: 3 s estimated; original endpoint check via proved source equalities
set_option trace.profiler true in
theorem endpoint1 : chk1 input=true := by
  unfold chk1
  change (match oneLead (CatalanCore.Li2.NVMod.FamilySource.U2C11.key 6) with | none=>false | some q=>ratUnitCheck 17 ((7745455872000:ℚ)^6*q))=true
  rw [oneLeadWith_spec (CatalanCore.Li2.NVMod.FamilySource.U2C11.key 6) (4) CatalanCore.Li2.NVMod.RegularFamily.U2C11.regularValue (CatalanCore.Li2.NVMod.RegularFamily.U2C11.h0_key 6) (CatalanCore.Li2.NVMod.RegularFamily.U2C11.regular_source 6)]
  decide +kernel
-- kcost: 3 s estimated; original endpoint check via proved source equalities
set_option trace.profiler true in
theorem endpointInf : chkInf input=true := by
  change (decide (6≤(slots (CatalanCore.Li2.NVMod.FamilySource.U2C11.key 6)).length) && ratUnitCheck 17 ((7745455872000:ℚ)^6*infLead (CatalanCore.Li2.NVMod.FamilySource.U2C11.key 6)))=true
  rw [infLeadNative_spec (CatalanCore.Li2.NVMod.FamilySource.U2C11.key 6) CatalanCore.Li2.NVMod.FamilySource.U2C11.num CatalanCore.Li2.NVMod.FamilySource.U2C11.den CatalanCore.Li2.NVMod.FamilySource.U2C11.indices CatalanCore.Li2.NVMod.FamilySource.U2C11.rho (CatalanCore.Li2.NVMod.FamilySource.U2C11.num_source 6) (CatalanCore.Li2.NVMod.FamilySource.U2C11.den_source 6) CatalanCore.Li2.NVMod.FamilySource.U2C11.indices_nodup ((CatalanCore.Li2.NVMod.FamilySource.U2C11.indices_set 6).trans (poles_eq_poleSet _)) rho_source]
  decide +kernel
-- kcost: 1 s estimated; coefficientwise integer remainder binding
set_option trace.profiler true in
theorem mod_ok : momentResidueCheck 17 6 CatalanCore.Li2.NVMod.FamilySource.U2C11.moments CatalanCore.Li2.NVMod.PolynomialData.U2C11S6.data.moments=true := by decide +kernel

-- kcost: 1 s estimated; existing arithmetic proofs and outer list length only
def interior : PolynomialCert.InteriorChecked input where
  data:=CatalanCore.Li2.NVMod.PolynomialData.U2C11S6.data.toCertificate
  bounds:=(PolynomialCompute.bounds_nat_transfer 6 17 CatalanCore.Li2.NVMod.PolynomialData.U2C11S6.data).symm.trans CatalanCore.Li2.NVMod.PolynomialData.U2C11S6.bounds_ok
  arithmetic:=(PolynomialCompute.arithmetic_transfer 6 17 CatalanCore.Li2.NVMod.PolynomialData.U2C11S6.data).symm.trans CatalanCore.Li2.NVMod.PolynomialData.U2C11S6.arithmetic_ok
  moments:=by
    intro e he
    exact momentResidueCheck_sound 17 6 CatalanCore.Li2.NVMod.FamilySource.U2C11.moments CatalanCore.Li2.NVMod.PolynomialData.U2C11S6.data.moments mod_ok (by decide +kernel) e he

def checked : KeyCertificate :=
  ⟨input,by decide +kernel,endpoint0,endpoint1,endpointInf,interior⟩
#print axioms checked
end
end CatalanCore.Li2.NVMod.KeyData.U2C11S6
