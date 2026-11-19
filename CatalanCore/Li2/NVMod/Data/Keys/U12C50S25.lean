module
public import CatalanCore.Li2.NVMod.Data.Regular.U12C50
public import CatalanCore.Li2.NVMod.Data.Polynomial.U12C50S25
public import CatalanCore.Li2.NVMod.DataSupport.PolynomialPackageSupport
public import CatalanCore.Li2.NVMod.DataSupport.PolynomialInfSource
public import CatalanCore.Li2.NVMod.DataSupport.Factorials
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option backward.isDefEq.respectTransparency false
open Polynomial Finset
namespace CatalanCore.Li2.NVMod.KeyData.U12C50S25
open CatalanCore.Li2.NVMod CatalanCore.Li2.NVMod.DataSupport
noncomputable section

-- kcost: 1 s estimated; closed endpoint orders and literal fields, shared factorial theorem
def input : EndpointInput where
  -- kcost: 1 s estimated; finite endpoint orders, checked literal fields
  key:=CatalanCore.Li2.NVMod.FamilySource.U12C50.key 25
  p:=53
  D:=576127454097642725238247192173986188984560281159231881012838400000000
  clearZ:=50
  clearOne:=37
  v0:=325
  v1:=601
  D_pos:=by decide +kernel
  mz:=CatalanCore.Li2.NVMod.FamilySource.U12C50.mz
  moment_clear:=by
    intro i j
    apply CatalanCore.Li2.NVMod.FamilySource.U12C50.moment_source 25
    have hi:=i.isLt
    have hj:=j.isLt
    change i.val<25 at hi
    change j.val<25 at hj
    omega
  order_zero:=by decide +kernel
  order_one:=by
    change (601:ℤ)=(37:ℤ)*25+oneOrder (CatalanCore.Li2.NVMod.FamilySource.U12C50.key 25)
    rw [oneOrderWith_spec,CatalanCore.Li2.NVMod.RegularFamily.U12C50.h0_key]
    decide +kernel
  factorials:=allFactorials (CatalanCore.Li2.NVMod.FamilySource.U12C50.key 25)

theorem rho_source : ∀m∈poleSet (CatalanCore.Li2.NVMod.FamilySource.U12C50.key 25),CatalanCore.Li2.NVMod.FamilySource.U12C50.rho m=residue (CatalanCore.Li2.NVMod.FamilySource.U12C50.key 25) m := by
  intro m hm
  apply CatalanCore.Li2.NVMod.FamilySource.U12C50.rho_source 25 m
  rwa [(CatalanCore.Li2.NVMod.FamilySource.U12C50.indices_set 25).trans (poles_eq_poleSet _)]

-- kcost: 3 s estimated; original endpoint check via proved source equalities
set_option trace.profiler true in
theorem endpoint0 : chk0 input=true := by
  change ((topPoles (CatalanCore.Li2.NVMod.FamilySource.U12C50.key 25)).length == 25 && ratUnitCheck 53 ((576127454097642725238247192173986188984560281159231881012838400000000:ℚ)^25*zeroLead (CatalanCore.Li2.NVMod.FamilySource.U12C50.key 25)))=true
  rw [zeroLead_with_residues (CatalanCore.Li2.NVMod.FamilySource.U12C50.key 25) CatalanCore.Li2.NVMod.FamilySource.U12C50.rho rho_source]
  decide +kernel
-- kcost: 3 s estimated; original endpoint check via proved source equalities
set_option trace.profiler true in
theorem endpoint1 : chk1 input=true := by
  unfold chk1
  change (match oneLead (CatalanCore.Li2.NVMod.FamilySource.U12C50.key 25) with | none=>false | some q=>ratUnitCheck 53 ((576127454097642725238247192173986188984560281159231881012838400000000:ℚ)^25*q))=true
  rw [oneLeadWith_spec (CatalanCore.Li2.NVMod.FamilySource.U12C50.key 25) (13) CatalanCore.Li2.NVMod.RegularFamily.U12C50.regularValue (CatalanCore.Li2.NVMod.RegularFamily.U12C50.h0_key 25) (CatalanCore.Li2.NVMod.RegularFamily.U12C50.regular_source 25)]
  decide +kernel
-- kcost: 3 s estimated; original endpoint check via proved source equalities
set_option trace.profiler true in
theorem endpointInf : chkInf input=true := by
  change (decide (25≤(slots (CatalanCore.Li2.NVMod.FamilySource.U12C50.key 25)).length) && ratUnitCheck 53 ((576127454097642725238247192173986188984560281159231881012838400000000:ℚ)^25*infLead (CatalanCore.Li2.NVMod.FamilySource.U12C50.key 25)))=true
  rw [infLeadNative_spec (CatalanCore.Li2.NVMod.FamilySource.U12C50.key 25) CatalanCore.Li2.NVMod.FamilySource.U12C50.num CatalanCore.Li2.NVMod.FamilySource.U12C50.den CatalanCore.Li2.NVMod.FamilySource.U12C50.indices CatalanCore.Li2.NVMod.FamilySource.U12C50.rho (CatalanCore.Li2.NVMod.FamilySource.U12C50.num_source 25) (CatalanCore.Li2.NVMod.FamilySource.U12C50.den_source 25) CatalanCore.Li2.NVMod.FamilySource.U12C50.indices_nodup ((CatalanCore.Li2.NVMod.FamilySource.U12C50.indices_set 25).trans (poles_eq_poleSet _)) rho_source]
  decide +kernel
-- kcost: 1 s estimated; coefficientwise integer remainder binding
set_option trace.profiler true in
theorem mod_ok : momentResidueCheck 53 25 CatalanCore.Li2.NVMod.FamilySource.U12C50.moments CatalanCore.Li2.NVMod.PolynomialData.U12C50S25.data.moments=true := by decide +kernel

-- kcost: 1 s estimated; existing arithmetic proofs and outer list length only
def interior : PolynomialCert.InteriorChecked input where
  data:=CatalanCore.Li2.NVMod.PolynomialData.U12C50S25.data.toCertificate
  bounds:=(PolynomialCompute.bounds_nat_transfer 25 53 CatalanCore.Li2.NVMod.PolynomialData.U12C50S25.data).symm.trans CatalanCore.Li2.NVMod.PolynomialData.U12C50S25.bounds_ok
  arithmetic:=(PolynomialCompute.arithmetic_transfer 25 53 CatalanCore.Li2.NVMod.PolynomialData.U12C50S25.data).symm.trans CatalanCore.Li2.NVMod.PolynomialData.U12C50S25.arithmetic_ok
  moments:=by
    intro e he
    exact momentResidueCheck_sound 53 25 CatalanCore.Li2.NVMod.FamilySource.U12C50.moments CatalanCore.Li2.NVMod.PolynomialData.U12C50S25.data.moments mod_ok (by decide +kernel) e he

def checked : KeyCertificate :=
  ⟨input,by decide +kernel,endpoint0,endpoint1,endpointInf,interior⟩
#print axioms checked
end
end CatalanCore.Li2.NVMod.KeyData.U12C50S25
