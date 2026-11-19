module
public import CatalanCore.Li2.NVMod.Data.Regular.U11C46
public import CatalanCore.Li2.NVMod.Data.Polynomial.U11C46S23
public import CatalanCore.Li2.NVMod.DataSupport.PolynomialPackageSupport
public import CatalanCore.Li2.NVMod.DataSupport.PolynomialInfSource
public import CatalanCore.Li2.NVMod.DataSupport.Factorials
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option backward.isDefEq.respectTransparency false
open Polynomial Finset
namespace CatalanCore.Li2.NVMod.KeyData.U11C46S23
open CatalanCore.Li2.NVMod CatalanCore.Li2.NVMod.DataSupport
noncomputable section

-- kcost: 1 s estimated; closed endpoint orders and literal fields, shared factorial theorem
def input : EndpointInput where
  -- kcost: 1 s estimated; finite endpoint orders, checked literal fields
  key:=CatalanCore.Li2.NVMod.FamilySource.U11C46.key 23
  p:=47
  D:=16440574826184704601532771331526041299006347337798778880000000
  clearZ:=46
  clearOne:=34
  v0:=276
  v1:=510
  D_pos:=by decide +kernel
  mz:=CatalanCore.Li2.NVMod.FamilySource.U11C46.mz
  moment_clear:=by
    intro i j
    apply CatalanCore.Li2.NVMod.FamilySource.U11C46.moment_source 23
    have hi:=i.isLt
    have hj:=j.isLt
    change i.val<23 at hi
    change j.val<23 at hj
    omega
  order_zero:=by decide +kernel
  order_one:=by
    change (510:ℤ)=(34:ℤ)*23+oneOrder (CatalanCore.Li2.NVMod.FamilySource.U11C46.key 23)
    rw [oneOrderWith_spec,CatalanCore.Li2.NVMod.RegularFamily.U11C46.h0_key]
    decide +kernel
  factorials:=allFactorials (CatalanCore.Li2.NVMod.FamilySource.U11C46.key 23)

theorem rho_source : ∀m∈poleSet (CatalanCore.Li2.NVMod.FamilySource.U11C46.key 23),CatalanCore.Li2.NVMod.FamilySource.U11C46.rho m=residue (CatalanCore.Li2.NVMod.FamilySource.U11C46.key 23) m := by
  intro m hm
  apply CatalanCore.Li2.NVMod.FamilySource.U11C46.rho_source 23 m
  rwa [(CatalanCore.Li2.NVMod.FamilySource.U11C46.indices_set 23).trans (poles_eq_poleSet _)]

-- kcost: 3 s estimated; original endpoint check via proved source equalities
set_option trace.profiler true in
theorem endpoint0 : chk0 input=true := by
  change ((topPoles (CatalanCore.Li2.NVMod.FamilySource.U11C46.key 23)).length == 23 && ratUnitCheck 47 ((16440574826184704601532771331526041299006347337798778880000000:ℚ)^23*zeroLead (CatalanCore.Li2.NVMod.FamilySource.U11C46.key 23)))=true
  rw [zeroLead_with_residues (CatalanCore.Li2.NVMod.FamilySource.U11C46.key 23) CatalanCore.Li2.NVMod.FamilySource.U11C46.rho rho_source]
  decide +kernel
-- kcost: 3 s estimated; original endpoint check via proved source equalities
set_option trace.profiler true in
theorem endpoint1 : chk1 input=true := by
  unfold chk1
  change (match oneLead (CatalanCore.Li2.NVMod.FamilySource.U11C46.key 23) with | none=>false | some q=>ratUnitCheck 47 ((16440574826184704601532771331526041299006347337798778880000000:ℚ)^23*q))=true
  rw [oneLeadWith_spec (CatalanCore.Li2.NVMod.FamilySource.U11C46.key 23) (12) CatalanCore.Li2.NVMod.RegularFamily.U11C46.regularValue (CatalanCore.Li2.NVMod.RegularFamily.U11C46.h0_key 23) (CatalanCore.Li2.NVMod.RegularFamily.U11C46.regular_source 23)]
  decide +kernel
-- kcost: 3 s estimated; original endpoint check via proved source equalities
set_option trace.profiler true in
theorem endpointInf : chkInf input=true := by
  change (decide (23≤(slots (CatalanCore.Li2.NVMod.FamilySource.U11C46.key 23)).length) && ratUnitCheck 47 ((16440574826184704601532771331526041299006347337798778880000000:ℚ)^23*infLead (CatalanCore.Li2.NVMod.FamilySource.U11C46.key 23)))=true
  rw [infLeadNative_spec (CatalanCore.Li2.NVMod.FamilySource.U11C46.key 23) CatalanCore.Li2.NVMod.FamilySource.U11C46.num CatalanCore.Li2.NVMod.FamilySource.U11C46.den CatalanCore.Li2.NVMod.FamilySource.U11C46.indices CatalanCore.Li2.NVMod.FamilySource.U11C46.rho (CatalanCore.Li2.NVMod.FamilySource.U11C46.num_source 23) (CatalanCore.Li2.NVMod.FamilySource.U11C46.den_source 23) CatalanCore.Li2.NVMod.FamilySource.U11C46.indices_nodup ((CatalanCore.Li2.NVMod.FamilySource.U11C46.indices_set 23).trans (poles_eq_poleSet _)) rho_source]
  decide +kernel
-- kcost: 1 s estimated; coefficientwise integer remainder binding
set_option trace.profiler true in
theorem mod_ok : momentResidueCheck 47 23 CatalanCore.Li2.NVMod.FamilySource.U11C46.moments CatalanCore.Li2.NVMod.PolynomialData.U11C46S23.data.moments=true := by decide +kernel

-- kcost: 1 s estimated; existing arithmetic proofs and outer list length only
def interior : PolynomialCert.InteriorChecked input where
  data:=CatalanCore.Li2.NVMod.PolynomialData.U11C46S23.data.toCertificate
  bounds:=(PolynomialCompute.bounds_nat_transfer 23 47 CatalanCore.Li2.NVMod.PolynomialData.U11C46S23.data).symm.trans CatalanCore.Li2.NVMod.PolynomialData.U11C46S23.bounds_ok
  arithmetic:=(PolynomialCompute.arithmetic_transfer 23 47 CatalanCore.Li2.NVMod.PolynomialData.U11C46S23.data).symm.trans CatalanCore.Li2.NVMod.PolynomialData.U11C46S23.arithmetic_ok
  moments:=by
    intro e he
    exact momentResidueCheck_sound 47 23 CatalanCore.Li2.NVMod.FamilySource.U11C46.moments CatalanCore.Li2.NVMod.PolynomialData.U11C46S23.data.moments mod_ok (by decide +kernel) e he

def checked : KeyCertificate :=
  ⟨input,by decide +kernel,endpoint0,endpoint1,endpointInf,interior⟩
#print axioms checked
end
end CatalanCore.Li2.NVMod.KeyData.U11C46S23
