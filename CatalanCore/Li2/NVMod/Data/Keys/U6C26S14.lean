module
public import CatalanCore.Li2.NVMod.Data.Regular.U6C26
public import CatalanCore.Li2.NVMod.Data.Polynomial.U6C26S14
public import CatalanCore.Li2.NVMod.DataSupport.PolynomialPackageSupport
public import CatalanCore.Li2.NVMod.DataSupport.PolynomialInfSource
public import CatalanCore.Li2.NVMod.DataSupport.Factorials
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option backward.isDefEq.respectTransparency false
open Polynomial Finset
namespace CatalanCore.Li2.NVMod.KeyData.U6C26S14
open CatalanCore.Li2.NVMod CatalanCore.Li2.NVMod.DataSupport
noncomputable section

-- kcost: 1 s estimated; closed endpoint orders and literal fields, shared factorial theorem
def input : EndpointInput where
  -- kcost: 1 s estimated; finite endpoint orders, checked literal fields
  key:=CatalanCore.Li2.NVMod.FamilySource.U6C26.key 14
  p:=37
  D:=168175799719216474108776652800000
  clearZ:=26
  clearOne:=19
  v0:=105
  v1:=166
  D_pos:=by decide +kernel
  mz:=CatalanCore.Li2.NVMod.FamilySource.U6C26.mz
  moment_clear:=by
    intro i j
    apply CatalanCore.Li2.NVMod.FamilySource.U6C26.moment_source 14
    have hi:=i.isLt
    have hj:=j.isLt
    change i.val<14 at hi
    change j.val<14 at hj
    omega
  order_zero:=by decide +kernel
  order_one:=by
    change (166:ℤ)=(19:ℤ)*14+oneOrder (CatalanCore.Li2.NVMod.FamilySource.U6C26.key 14)
    rw [oneOrderWith_spec,CatalanCore.Li2.NVMod.RegularFamily.U6C26.h0_key]
    decide +kernel
  factorials:=allFactorials (CatalanCore.Li2.NVMod.FamilySource.U6C26.key 14)

theorem rho_source : ∀m∈poleSet (CatalanCore.Li2.NVMod.FamilySource.U6C26.key 14),CatalanCore.Li2.NVMod.FamilySource.U6C26.rho m=residue (CatalanCore.Li2.NVMod.FamilySource.U6C26.key 14) m := by
  intro m hm
  apply CatalanCore.Li2.NVMod.FamilySource.U6C26.rho_source 14 m
  rwa [(CatalanCore.Li2.NVMod.FamilySource.U6C26.indices_set 14).trans (poles_eq_poleSet _)]

-- kcost: 3 s estimated; original endpoint check via proved source equalities
set_option trace.profiler true in
theorem endpoint0 : chk0 input=true := by
  change ((topPoles (CatalanCore.Li2.NVMod.FamilySource.U6C26.key 14)).length == 14 && ratUnitCheck 37 ((168175799719216474108776652800000:ℚ)^14*zeroLead (CatalanCore.Li2.NVMod.FamilySource.U6C26.key 14)))=true
  rw [zeroLead_with_residues (CatalanCore.Li2.NVMod.FamilySource.U6C26.key 14) CatalanCore.Li2.NVMod.FamilySource.U6C26.rho rho_source]
  decide +kernel
-- kcost: 3 s estimated; original endpoint check via proved source equalities
set_option trace.profiler true in
theorem endpoint1 : chk1 input=true := by
  unfold chk1
  change (match oneLead (CatalanCore.Li2.NVMod.FamilySource.U6C26.key 14) with | none=>false | some q=>ratUnitCheck 37 ((168175799719216474108776652800000:ℚ)^14*q))=true
  rw [oneLeadWith_spec (CatalanCore.Li2.NVMod.FamilySource.U6C26.key 14) (7) CatalanCore.Li2.NVMod.RegularFamily.U6C26.regularValue (CatalanCore.Li2.NVMod.RegularFamily.U6C26.h0_key 14) (CatalanCore.Li2.NVMod.RegularFamily.U6C26.regular_source 14)]
  decide +kernel
-- kcost: 3 s estimated; original endpoint check via proved source equalities
set_option trace.profiler true in
theorem endpointInf : chkInf input=true := by
  change (decide (14≤(slots (CatalanCore.Li2.NVMod.FamilySource.U6C26.key 14)).length) && ratUnitCheck 37 ((168175799719216474108776652800000:ℚ)^14*infLead (CatalanCore.Li2.NVMod.FamilySource.U6C26.key 14)))=true
  rw [infLeadNative_spec (CatalanCore.Li2.NVMod.FamilySource.U6C26.key 14) CatalanCore.Li2.NVMod.FamilySource.U6C26.num CatalanCore.Li2.NVMod.FamilySource.U6C26.den CatalanCore.Li2.NVMod.FamilySource.U6C26.indices CatalanCore.Li2.NVMod.FamilySource.U6C26.rho (CatalanCore.Li2.NVMod.FamilySource.U6C26.num_source 14) (CatalanCore.Li2.NVMod.FamilySource.U6C26.den_source 14) CatalanCore.Li2.NVMod.FamilySource.U6C26.indices_nodup ((CatalanCore.Li2.NVMod.FamilySource.U6C26.indices_set 14).trans (poles_eq_poleSet _)) rho_source]
  decide +kernel
-- kcost: 1 s estimated; coefficientwise integer remainder binding
set_option trace.profiler true in
theorem mod_ok : momentResidueCheck 37 14 CatalanCore.Li2.NVMod.FamilySource.U6C26.moments CatalanCore.Li2.NVMod.PolynomialData.U6C26S14.data.moments=true := by decide +kernel

-- kcost: 1 s estimated; existing arithmetic proofs and outer list length only
def interior : PolynomialCert.InteriorChecked input where
  data:=CatalanCore.Li2.NVMod.PolynomialData.U6C26S14.data.toCertificate
  bounds:=(PolynomialCompute.bounds_nat_transfer 14 37 CatalanCore.Li2.NVMod.PolynomialData.U6C26S14.data).symm.trans CatalanCore.Li2.NVMod.PolynomialData.U6C26S14.bounds_ok
  arithmetic:=(PolynomialCompute.arithmetic_transfer 14 37 CatalanCore.Li2.NVMod.PolynomialData.U6C26S14.data).symm.trans CatalanCore.Li2.NVMod.PolynomialData.U6C26S14.arithmetic_ok
  moments:=by
    intro e he
    exact momentResidueCheck_sound 37 14 CatalanCore.Li2.NVMod.FamilySource.U6C26.moments CatalanCore.Li2.NVMod.PolynomialData.U6C26S14.data.moments mod_ok (by decide +kernel) e he

def checked : KeyCertificate :=
  ⟨input,by decide +kernel,endpoint0,endpoint1,endpointInf,interior⟩
#print axioms checked
end
end CatalanCore.Li2.NVMod.KeyData.U6C26S14
