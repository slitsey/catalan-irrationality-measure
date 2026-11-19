module
public import CatalanCore.Li2.NVMod.Data.Regular.U12C49
public import CatalanCore.Li2.NVMod.Data.Polynomial.U12C49S25
public import CatalanCore.Li2.NVMod.DataSupport.PolynomialPackageSupport
public import CatalanCore.Li2.NVMod.DataSupport.PolynomialInfSource
public import CatalanCore.Li2.NVMod.DataSupport.Factorials
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option backward.isDefEq.respectTransparency false
open Polynomial Finset
namespace CatalanCore.Li2.NVMod.KeyData.U12C49S25
open CatalanCore.Li2.NVMod CatalanCore.Li2.NVMod.DataSupport
noncomputable section

-- kcost: 1 s estimated; closed endpoint orders and literal fields, shared factorial theorem
def input : EndpointInput where
  -- kcost: 1 s estimated; finite endpoint orders, checked literal fields
  key:=CatalanCore.Li2.NVMod.FamilySource.U12C49.key 25
  p:=89
  D:=15571012272909262844276951139837464567150277869168429216563200000000
  clearZ:=49
  clearOne:=36
  v0:=325
  v1:=558
  D_pos:=by decide +kernel
  mz:=CatalanCore.Li2.NVMod.FamilySource.U12C49.mz
  moment_clear:=by
    intro i j
    apply CatalanCore.Li2.NVMod.FamilySource.U12C49.moment_source 25
    have hi:=i.isLt
    have hj:=j.isLt
    change i.val<25 at hi
    change j.val<25 at hj
    omega
  order_zero:=by decide +kernel
  order_one:=by
    change (558:ℤ)=(36:ℤ)*25+oneOrder (CatalanCore.Li2.NVMod.FamilySource.U12C49.key 25)
    rw [oneOrderWith_spec,CatalanCore.Li2.NVMod.RegularFamily.U12C49.h0_key]
    decide +kernel
  factorials:=allFactorials (CatalanCore.Li2.NVMod.FamilySource.U12C49.key 25)

theorem rho_source : ∀m∈poleSet (CatalanCore.Li2.NVMod.FamilySource.U12C49.key 25),CatalanCore.Li2.NVMod.FamilySource.U12C49.rho m=residue (CatalanCore.Li2.NVMod.FamilySource.U12C49.key 25) m := by
  intro m hm
  apply CatalanCore.Li2.NVMod.FamilySource.U12C49.rho_source 25 m
  rwa [(CatalanCore.Li2.NVMod.FamilySource.U12C49.indices_set 25).trans (poles_eq_poleSet _)]

-- kcost: 3 s estimated; original endpoint check via proved source equalities
set_option trace.profiler true in
theorem endpoint0 : chk0 input=true := by
  change ((topPoles (CatalanCore.Li2.NVMod.FamilySource.U12C49.key 25)).length == 25 && ratUnitCheck 89 ((15571012272909262844276951139837464567150277869168429216563200000000:ℚ)^25*zeroLead (CatalanCore.Li2.NVMod.FamilySource.U12C49.key 25)))=true
  rw [zeroLead_with_residues (CatalanCore.Li2.NVMod.FamilySource.U12C49.key 25) CatalanCore.Li2.NVMod.FamilySource.U12C49.rho rho_source]
  decide +kernel
-- kcost: 3 s estimated; original endpoint check via proved source equalities
set_option trace.profiler true in
theorem endpoint1 : chk1 input=true := by
  unfold chk1
  change (match oneLead (CatalanCore.Li2.NVMod.FamilySource.U12C49.key 25) with | none=>false | some q=>ratUnitCheck 89 ((15571012272909262844276951139837464567150277869168429216563200000000:ℚ)^25*q))=true
  rw [oneLeadWith_spec (CatalanCore.Li2.NVMod.FamilySource.U12C49.key 25) (12) CatalanCore.Li2.NVMod.RegularFamily.U12C49.regularValue (CatalanCore.Li2.NVMod.RegularFamily.U12C49.h0_key 25) (CatalanCore.Li2.NVMod.RegularFamily.U12C49.regular_source 25)]
  decide +kernel
-- kcost: 3 s estimated; original endpoint check via proved source equalities
set_option trace.profiler true in
theorem endpointInf : chkInf input=true := by
  change (decide (25≤(slots (CatalanCore.Li2.NVMod.FamilySource.U12C49.key 25)).length) && ratUnitCheck 89 ((15571012272909262844276951139837464567150277869168429216563200000000:ℚ)^25*infLead (CatalanCore.Li2.NVMod.FamilySource.U12C49.key 25)))=true
  rw [infLeadNative_spec (CatalanCore.Li2.NVMod.FamilySource.U12C49.key 25) CatalanCore.Li2.NVMod.FamilySource.U12C49.num CatalanCore.Li2.NVMod.FamilySource.U12C49.den CatalanCore.Li2.NVMod.FamilySource.U12C49.indices CatalanCore.Li2.NVMod.FamilySource.U12C49.rho (CatalanCore.Li2.NVMod.FamilySource.U12C49.num_source 25) (CatalanCore.Li2.NVMod.FamilySource.U12C49.den_source 25) CatalanCore.Li2.NVMod.FamilySource.U12C49.indices_nodup ((CatalanCore.Li2.NVMod.FamilySource.U12C49.indices_set 25).trans (poles_eq_poleSet _)) rho_source]
  decide +kernel
-- kcost: 1 s estimated; coefficientwise integer remainder binding
set_option trace.profiler true in
theorem mod_ok : momentResidueCheck 89 25 CatalanCore.Li2.NVMod.FamilySource.U12C49.moments CatalanCore.Li2.NVMod.PolynomialData.U12C49S25.data.moments=true := by decide +kernel

-- kcost: 1 s estimated; existing arithmetic proofs and outer list length only
def interior : PolynomialCert.InteriorChecked input where
  data:=CatalanCore.Li2.NVMod.PolynomialData.U12C49S25.data.toCertificate
  bounds:=(PolynomialCompute.bounds_nat_transfer 25 89 CatalanCore.Li2.NVMod.PolynomialData.U12C49S25.data).symm.trans CatalanCore.Li2.NVMod.PolynomialData.U12C49S25.bounds_ok
  arithmetic:=(PolynomialCompute.arithmetic_transfer 25 89 CatalanCore.Li2.NVMod.PolynomialData.U12C49S25.data).symm.trans CatalanCore.Li2.NVMod.PolynomialData.U12C49S25.arithmetic_ok
  moments:=by
    intro e he
    exact momentResidueCheck_sound 89 25 CatalanCore.Li2.NVMod.FamilySource.U12C49.moments CatalanCore.Li2.NVMod.PolynomialData.U12C49S25.data.moments mod_ok (by decide +kernel) e he

def checked : KeyCertificate :=
  ⟨input,by decide +kernel,endpoint0,endpoint1,endpointInf,interior⟩
#print axioms checked
end
end CatalanCore.Li2.NVMod.KeyData.U12C49S25
