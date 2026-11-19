module
public import CatalanCore.Li2.NVMod.Data.Regular.U4C17
public import CatalanCore.Li2.NVMod.Data.Polynomial.U4C17S9
public import CatalanCore.Li2.NVMod.DataSupport.PolynomialPackageSupport
public import CatalanCore.Li2.NVMod.DataSupport.PolynomialInfSource
public import CatalanCore.Li2.NVMod.DataSupport.Factorials
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option backward.isDefEq.respectTransparency false
open Polynomial Finset
namespace CatalanCore.Li2.NVMod.KeyData.U4C17S9
open CatalanCore.Li2.NVMod CatalanCore.Li2.NVMod.DataSupport
noncomputable section

-- kcost: 1 s estimated; closed endpoint orders and literal fields, shared factorial theorem
def input : EndpointInput where
  -- kcost: 1 s estimated; finite endpoint orders, checked literal fields
  key:=CatalanCore.Li2.NVMod.FamilySource.U4C17.key 9
  p:=19
  D:=31209404345159040000
  clearZ:=17
  clearOne:=12
  v0:=45
  v1:=66
  D_pos:=by decide +kernel
  mz:=CatalanCore.Li2.NVMod.FamilySource.U4C17.mz
  moment_clear:=by
    intro i j
    apply CatalanCore.Li2.NVMod.FamilySource.U4C17.moment_source 9
    have hi:=i.isLt
    have hj:=j.isLt
    change i.val<9 at hi
    change j.val<9 at hj
    omega
  order_zero:=by decide +kernel
  order_one:=by
    change (66:ℤ)=(12:ℤ)*9+oneOrder (CatalanCore.Li2.NVMod.FamilySource.U4C17.key 9)
    rw [oneOrderWith_spec,CatalanCore.Li2.NVMod.RegularFamily.U4C17.h0_key]
    decide +kernel
  factorials:=allFactorials (CatalanCore.Li2.NVMod.FamilySource.U4C17.key 9)

theorem rho_source : ∀m∈poleSet (CatalanCore.Li2.NVMod.FamilySource.U4C17.key 9),CatalanCore.Li2.NVMod.FamilySource.U4C17.rho m=residue (CatalanCore.Li2.NVMod.FamilySource.U4C17.key 9) m := by
  intro m hm
  apply CatalanCore.Li2.NVMod.FamilySource.U4C17.rho_source 9 m
  rwa [(CatalanCore.Li2.NVMod.FamilySource.U4C17.indices_set 9).trans (poles_eq_poleSet _)]

-- kcost: 3 s estimated; original endpoint check via proved source equalities
set_option trace.profiler true in
theorem endpoint0 : chk0 input=true := by
  change ((topPoles (CatalanCore.Li2.NVMod.FamilySource.U4C17.key 9)).length == 9 && ratUnitCheck 19 ((31209404345159040000:ℚ)^9*zeroLead (CatalanCore.Li2.NVMod.FamilySource.U4C17.key 9)))=true
  rw [zeroLead_with_residues (CatalanCore.Li2.NVMod.FamilySource.U4C17.key 9) CatalanCore.Li2.NVMod.FamilySource.U4C17.rho rho_source]
  decide +kernel
-- kcost: 3 s estimated; original endpoint check via proved source equalities
set_option trace.profiler true in
theorem endpoint1 : chk1 input=true := by
  unfold chk1
  change (match oneLead (CatalanCore.Li2.NVMod.FamilySource.U4C17.key 9) with | none=>false | some q=>ratUnitCheck 19 ((31209404345159040000:ℚ)^9*q))=true
  rw [oneLeadWith_spec (CatalanCore.Li2.NVMod.FamilySource.U4C17.key 9) (4) CatalanCore.Li2.NVMod.RegularFamily.U4C17.regularValue (CatalanCore.Li2.NVMod.RegularFamily.U4C17.h0_key 9) (CatalanCore.Li2.NVMod.RegularFamily.U4C17.regular_source 9)]
  decide +kernel
-- kcost: 3 s estimated; original endpoint check via proved source equalities
set_option trace.profiler true in
theorem endpointInf : chkInf input=true := by
  change (decide (9≤(slots (CatalanCore.Li2.NVMod.FamilySource.U4C17.key 9)).length) && ratUnitCheck 19 ((31209404345159040000:ℚ)^9*infLead (CatalanCore.Li2.NVMod.FamilySource.U4C17.key 9)))=true
  rw [infLeadNative_spec (CatalanCore.Li2.NVMod.FamilySource.U4C17.key 9) CatalanCore.Li2.NVMod.FamilySource.U4C17.num CatalanCore.Li2.NVMod.FamilySource.U4C17.den CatalanCore.Li2.NVMod.FamilySource.U4C17.indices CatalanCore.Li2.NVMod.FamilySource.U4C17.rho (CatalanCore.Li2.NVMod.FamilySource.U4C17.num_source 9) (CatalanCore.Li2.NVMod.FamilySource.U4C17.den_source 9) CatalanCore.Li2.NVMod.FamilySource.U4C17.indices_nodup ((CatalanCore.Li2.NVMod.FamilySource.U4C17.indices_set 9).trans (poles_eq_poleSet _)) rho_source]
  decide +kernel
-- kcost: 1 s estimated; coefficientwise integer remainder binding
set_option trace.profiler true in
theorem mod_ok : momentResidueCheck 19 9 CatalanCore.Li2.NVMod.FamilySource.U4C17.moments CatalanCore.Li2.NVMod.PolynomialData.U4C17S9.data.moments=true := by decide +kernel

-- kcost: 1 s estimated; existing arithmetic proofs and outer list length only
def interior : PolynomialCert.InteriorChecked input where
  data:=CatalanCore.Li2.NVMod.PolynomialData.U4C17S9.data.toCertificate
  bounds:=(PolynomialCompute.bounds_nat_transfer 9 19 CatalanCore.Li2.NVMod.PolynomialData.U4C17S9.data).symm.trans CatalanCore.Li2.NVMod.PolynomialData.U4C17S9.bounds_ok
  arithmetic:=(PolynomialCompute.arithmetic_transfer 9 19 CatalanCore.Li2.NVMod.PolynomialData.U4C17S9.data).symm.trans CatalanCore.Li2.NVMod.PolynomialData.U4C17S9.arithmetic_ok
  moments:=by
    intro e he
    exact momentResidueCheck_sound 19 9 CatalanCore.Li2.NVMod.FamilySource.U4C17.moments CatalanCore.Li2.NVMod.PolynomialData.U4C17S9.data.moments mod_ok (by decide +kernel) e he

def checked : KeyCertificate :=
  ⟨input,by decide +kernel,endpoint0,endpoint1,endpointInf,interior⟩
#print axioms checked
end
end CatalanCore.Li2.NVMod.KeyData.U4C17S9
