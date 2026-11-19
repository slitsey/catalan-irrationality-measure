module
public import CatalanCore.Li2.NVMod.Data.Regular.U2C10
public import CatalanCore.Li2.NVMod.Data.Polynomial.U2C10S5
public import CatalanCore.Li2.NVMod.DataSupport.PolynomialPackageSupport
public import CatalanCore.Li2.NVMod.DataSupport.PolynomialInfSource
public import CatalanCore.Li2.NVMod.DataSupport.Factorials
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option backward.isDefEq.respectTransparency false
open Polynomial Finset
namespace CatalanCore.Li2.NVMod.KeyData.U2C10S5
open CatalanCore.Li2.NVMod CatalanCore.Li2.NVMod.DataSupport
noncomputable section

-- kcost: 1 s estimated; closed endpoint orders and literal fields, shared factorial theorem
def input : EndpointInput where
  -- kcost: 1 s estimated; finite endpoint orders, checked literal fields
  key:=CatalanCore.Li2.NVMod.FamilySource.U2C10.key 5
  p:=29
  D:=8001504000
  clearZ:=10
  clearOne:=7
  v0:=15
  v1:=26
  D_pos:=by decide +kernel
  mz:=CatalanCore.Li2.NVMod.FamilySource.U2C10.mz
  moment_clear:=by
    intro i j
    apply CatalanCore.Li2.NVMod.FamilySource.U2C10.moment_source 5
    have hi:=i.isLt
    have hj:=j.isLt
    change i.val<5 at hi
    change j.val<5 at hj
    omega
  order_zero:=by decide +kernel
  order_one:=by
    change (26:ℤ)=(7:ℤ)*5+oneOrder (CatalanCore.Li2.NVMod.FamilySource.U2C10.key 5)
    rw [oneOrderWith_spec,CatalanCore.Li2.NVMod.RegularFamily.U2C10.h0_key]
    decide +kernel
  factorials:=allFactorials (CatalanCore.Li2.NVMod.FamilySource.U2C10.key 5)

theorem rho_source : ∀m∈poleSet (CatalanCore.Li2.NVMod.FamilySource.U2C10.key 5),CatalanCore.Li2.NVMod.FamilySource.U2C10.rho m=residue (CatalanCore.Li2.NVMod.FamilySource.U2C10.key 5) m := by
  intro m hm
  apply CatalanCore.Li2.NVMod.FamilySource.U2C10.rho_source 5 m
  rwa [(CatalanCore.Li2.NVMod.FamilySource.U2C10.indices_set 5).trans (poles_eq_poleSet _)]

-- kcost: 3 s estimated; original endpoint check via proved source equalities
set_option trace.profiler true in
theorem endpoint0 : chk0 input=true := by
  change ((topPoles (CatalanCore.Li2.NVMod.FamilySource.U2C10.key 5)).length == 5 && ratUnitCheck 29 ((8001504000:ℚ)^5*zeroLead (CatalanCore.Li2.NVMod.FamilySource.U2C10.key 5)))=true
  rw [zeroLead_with_residues (CatalanCore.Li2.NVMod.FamilySource.U2C10.key 5) CatalanCore.Li2.NVMod.FamilySource.U2C10.rho rho_source]
  decide +kernel
-- kcost: 3 s estimated; original endpoint check via proved source equalities
set_option trace.profiler true in
theorem endpoint1 : chk1 input=true := by
  unfold chk1
  change (match oneLead (CatalanCore.Li2.NVMod.FamilySource.U2C10.key 5) with | none=>false | some q=>ratUnitCheck 29 ((8001504000:ℚ)^5*q))=true
  rw [oneLeadWith_spec (CatalanCore.Li2.NVMod.FamilySource.U2C10.key 5) (3) CatalanCore.Li2.NVMod.RegularFamily.U2C10.regularValue (CatalanCore.Li2.NVMod.RegularFamily.U2C10.h0_key 5) (CatalanCore.Li2.NVMod.RegularFamily.U2C10.regular_source 5)]
  decide +kernel
-- kcost: 3 s estimated; original endpoint check via proved source equalities
set_option trace.profiler true in
theorem endpointInf : chkInf input=true := by
  change (decide (5≤(slots (CatalanCore.Li2.NVMod.FamilySource.U2C10.key 5)).length) && ratUnitCheck 29 ((8001504000:ℚ)^5*infLead (CatalanCore.Li2.NVMod.FamilySource.U2C10.key 5)))=true
  rw [infLeadNative_spec (CatalanCore.Li2.NVMod.FamilySource.U2C10.key 5) CatalanCore.Li2.NVMod.FamilySource.U2C10.num CatalanCore.Li2.NVMod.FamilySource.U2C10.den CatalanCore.Li2.NVMod.FamilySource.U2C10.indices CatalanCore.Li2.NVMod.FamilySource.U2C10.rho (CatalanCore.Li2.NVMod.FamilySource.U2C10.num_source 5) (CatalanCore.Li2.NVMod.FamilySource.U2C10.den_source 5) CatalanCore.Li2.NVMod.FamilySource.U2C10.indices_nodup ((CatalanCore.Li2.NVMod.FamilySource.U2C10.indices_set 5).trans (poles_eq_poleSet _)) rho_source]
  decide +kernel
-- kcost: 1 s estimated; coefficientwise integer remainder binding
set_option trace.profiler true in
theorem mod_ok : momentResidueCheck 29 5 CatalanCore.Li2.NVMod.FamilySource.U2C10.moments CatalanCore.Li2.NVMod.PolynomialData.U2C10S5.data.moments=true := by decide +kernel

-- kcost: 1 s estimated; existing arithmetic proofs and outer list length only
def interior : PolynomialCert.InteriorChecked input where
  data:=CatalanCore.Li2.NVMod.PolynomialData.U2C10S5.data.toCertificate
  bounds:=(PolynomialCompute.bounds_nat_transfer 5 29 CatalanCore.Li2.NVMod.PolynomialData.U2C10S5.data).symm.trans CatalanCore.Li2.NVMod.PolynomialData.U2C10S5.bounds_ok
  arithmetic:=(PolynomialCompute.arithmetic_transfer 5 29 CatalanCore.Li2.NVMod.PolynomialData.U2C10S5.data).symm.trans CatalanCore.Li2.NVMod.PolynomialData.U2C10S5.arithmetic_ok
  moments:=by
    intro e he
    exact momentResidueCheck_sound 29 5 CatalanCore.Li2.NVMod.FamilySource.U2C10.moments CatalanCore.Li2.NVMod.PolynomialData.U2C10S5.data.moments mod_ok (by decide +kernel) e he

def checked : KeyCertificate :=
  ⟨input,by decide +kernel,endpoint0,endpoint1,endpointInf,interior⟩
#print axioms checked
end
end CatalanCore.Li2.NVMod.KeyData.U2C10S5
