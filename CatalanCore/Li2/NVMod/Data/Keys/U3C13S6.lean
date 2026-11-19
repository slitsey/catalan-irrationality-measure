module
public import CatalanCore.Li2.NVMod.Data.Regular.U3C13
public import CatalanCore.Li2.NVMod.Data.Polynomial.U3C13S6
public import CatalanCore.Li2.NVMod.DataSupport.PolynomialPackageSupport
public import CatalanCore.Li2.NVMod.DataSupport.PolynomialInfSource
public import CatalanCore.Li2.NVMod.DataSupport.Factorials
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option backward.isDefEq.respectTransparency false
open Polynomial Finset
namespace CatalanCore.Li2.NVMod.KeyData.U3C13S6
open CatalanCore.Li2.NVMod CatalanCore.Li2.NVMod.DataSupport
noncomputable section

-- kcost: 1 s estimated; closed endpoint orders and literal fields, shared factorial theorem
def input : EndpointInput where
  -- kcost: 1 s estimated; finite endpoint orders, checked literal fields
  key:=CatalanCore.Li2.NVMod.FamilySource.U3C13.key 6
  p:=43
  D:=1308982042368000
  clearZ:=13
  clearOne:=9
  v0:=21
  v1:=38
  D_pos:=by decide +kernel
  mz:=CatalanCore.Li2.NVMod.FamilySource.U3C13.mz
  moment_clear:=by
    intro i j
    apply CatalanCore.Li2.NVMod.FamilySource.U3C13.moment_source 6
    have hi:=i.isLt
    have hj:=j.isLt
    change i.val<6 at hi
    change j.val<6 at hj
    omega
  order_zero:=by decide +kernel
  order_one:=by
    change (38:ℤ)=(9:ℤ)*6+oneOrder (CatalanCore.Li2.NVMod.FamilySource.U3C13.key 6)
    rw [oneOrderWith_spec,CatalanCore.Li2.NVMod.RegularFamily.U3C13.h0_key]
    decide +kernel
  factorials:=allFactorials (CatalanCore.Li2.NVMod.FamilySource.U3C13.key 6)

theorem rho_source : ∀m∈poleSet (CatalanCore.Li2.NVMod.FamilySource.U3C13.key 6),CatalanCore.Li2.NVMod.FamilySource.U3C13.rho m=residue (CatalanCore.Li2.NVMod.FamilySource.U3C13.key 6) m := by
  intro m hm
  apply CatalanCore.Li2.NVMod.FamilySource.U3C13.rho_source 6 m
  rwa [(CatalanCore.Li2.NVMod.FamilySource.U3C13.indices_set 6).trans (poles_eq_poleSet _)]

-- kcost: 3 s estimated; original endpoint check via proved source equalities
set_option trace.profiler true in
theorem endpoint0 : chk0 input=true := by
  change ((topPoles (CatalanCore.Li2.NVMod.FamilySource.U3C13.key 6)).length == 6 && ratUnitCheck 43 ((1308982042368000:ℚ)^6*zeroLead (CatalanCore.Li2.NVMod.FamilySource.U3C13.key 6)))=true
  rw [zeroLead_with_residues (CatalanCore.Li2.NVMod.FamilySource.U3C13.key 6) CatalanCore.Li2.NVMod.FamilySource.U3C13.rho rho_source]
  decide +kernel
-- kcost: 3 s estimated; original endpoint check via proved source equalities
set_option trace.profiler true in
theorem endpoint1 : chk1 input=true := by
  unfold chk1
  change (match oneLead (CatalanCore.Li2.NVMod.FamilySource.U3C13.key 6) with | none=>false | some q=>ratUnitCheck 43 ((1308982042368000:ℚ)^6*q))=true
  rw [oneLeadWith_spec (CatalanCore.Li2.NVMod.FamilySource.U3C13.key 6) (3) CatalanCore.Li2.NVMod.RegularFamily.U3C13.regularValue (CatalanCore.Li2.NVMod.RegularFamily.U3C13.h0_key 6) (CatalanCore.Li2.NVMod.RegularFamily.U3C13.regular_source 6)]
  decide +kernel
-- kcost: 3 s estimated; original endpoint check via proved source equalities
set_option trace.profiler true in
theorem endpointInf : chkInf input=true := by
  change (decide (6≤(slots (CatalanCore.Li2.NVMod.FamilySource.U3C13.key 6)).length) && ratUnitCheck 43 ((1308982042368000:ℚ)^6*infLead (CatalanCore.Li2.NVMod.FamilySource.U3C13.key 6)))=true
  rw [infLeadNative_spec (CatalanCore.Li2.NVMod.FamilySource.U3C13.key 6) CatalanCore.Li2.NVMod.FamilySource.U3C13.num CatalanCore.Li2.NVMod.FamilySource.U3C13.den CatalanCore.Li2.NVMod.FamilySource.U3C13.indices CatalanCore.Li2.NVMod.FamilySource.U3C13.rho (CatalanCore.Li2.NVMod.FamilySource.U3C13.num_source 6) (CatalanCore.Li2.NVMod.FamilySource.U3C13.den_source 6) CatalanCore.Li2.NVMod.FamilySource.U3C13.indices_nodup ((CatalanCore.Li2.NVMod.FamilySource.U3C13.indices_set 6).trans (poles_eq_poleSet _)) rho_source]
  decide +kernel
-- kcost: 1 s estimated; coefficientwise integer remainder binding
set_option trace.profiler true in
theorem mod_ok : momentResidueCheck 43 6 CatalanCore.Li2.NVMod.FamilySource.U3C13.moments CatalanCore.Li2.NVMod.PolynomialData.U3C13S6.data.moments=true := by decide +kernel

-- kcost: 1 s estimated; existing arithmetic proofs and outer list length only
def interior : PolynomialCert.InteriorChecked input where
  data:=CatalanCore.Li2.NVMod.PolynomialData.U3C13S6.data.toCertificate
  bounds:=(PolynomialCompute.bounds_nat_transfer 6 43 CatalanCore.Li2.NVMod.PolynomialData.U3C13S6.data).symm.trans CatalanCore.Li2.NVMod.PolynomialData.U3C13S6.bounds_ok
  arithmetic:=(PolynomialCompute.arithmetic_transfer 6 43 CatalanCore.Li2.NVMod.PolynomialData.U3C13S6.data).symm.trans CatalanCore.Li2.NVMod.PolynomialData.U3C13S6.arithmetic_ok
  moments:=by
    intro e he
    exact momentResidueCheck_sound 43 6 CatalanCore.Li2.NVMod.FamilySource.U3C13.moments CatalanCore.Li2.NVMod.PolynomialData.U3C13S6.data.moments mod_ok (by decide +kernel) e he

def checked : KeyCertificate :=
  ⟨input,by decide +kernel,endpoint0,endpoint1,endpointInf,interior⟩
#print axioms checked
end
end CatalanCore.Li2.NVMod.KeyData.U3C13S6
