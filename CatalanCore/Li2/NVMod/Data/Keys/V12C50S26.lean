module
public import CatalanCore.Li2.NVMod.Data.Regular.V12C50
public import CatalanCore.Li2.NVMod.Data.Polynomial.V12C50S26
public import CatalanCore.Li2.NVMod.DataSupport.PolynomialPackageSupport
public import CatalanCore.Li2.NVMod.DataSupport.PolynomialInfSource
public import CatalanCore.Li2.NVMod.DataSupport.Factorials
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option backward.isDefEq.respectTransparency false
open Polynomial Finset
namespace CatalanCore.Li2.NVMod.KeyData.V12C50S26
open CatalanCore.Li2.NVMod CatalanCore.Li2.NVMod.DataSupport
noncomputable section

-- kcost: 1 s estimated; closed endpoint orders and literal fields, shared factorial theorem
def input : EndpointInput where
  -- kcost: 1 s estimated; finite endpoint orders, checked literal fields
  key:=CatalanCore.Li2.NVMod.FamilySource.V12C50.key 26
  p:=73
  D:=1712466760969978825072328666356802307259774146969600000000
  clearZ:=49
  clearOne:=36
  v0:=351
  v1:=594
  D_pos:=by decide +kernel
  mz:=CatalanCore.Li2.NVMod.FamilySource.V12C50.mz
  moment_clear:=by
    intro i j
    apply CatalanCore.Li2.NVMod.FamilySource.V12C50.moment_source 26
    have hi:=i.isLt
    have hj:=j.isLt
    change i.val<26 at hi
    change j.val<26 at hj
    omega
  order_zero:=by decide +kernel
  order_one:=by
    change (594:ℤ)=(36:ℤ)*26+oneOrder (CatalanCore.Li2.NVMod.FamilySource.V12C50.key 26)
    rw [oneOrderWith_spec,CatalanCore.Li2.NVMod.RegularFamily.V12C50.h0_key]
    decide +kernel
  factorials:=allFactorials (CatalanCore.Li2.NVMod.FamilySource.V12C50.key 26)

theorem rho_source : ∀m∈poleSet (CatalanCore.Li2.NVMod.FamilySource.V12C50.key 26),CatalanCore.Li2.NVMod.FamilySource.V12C50.rho m=residue (CatalanCore.Li2.NVMod.FamilySource.V12C50.key 26) m := by
  intro m hm
  apply CatalanCore.Li2.NVMod.FamilySource.V12C50.rho_source 26 m
  rwa [(CatalanCore.Li2.NVMod.FamilySource.V12C50.indices_set 26).trans (poles_eq_poleSet _)]

-- kcost: 3 s estimated; original endpoint check via proved source equalities
set_option trace.profiler true in
theorem endpoint0 : chk0 input=true := by
  change ((topPoles (CatalanCore.Li2.NVMod.FamilySource.V12C50.key 26)).length == 26 && ratUnitCheck 73 ((1712466760969978825072328666356802307259774146969600000000:ℚ)^26*zeroLead (CatalanCore.Li2.NVMod.FamilySource.V12C50.key 26)))=true
  rw [zeroLead_with_residues (CatalanCore.Li2.NVMod.FamilySource.V12C50.key 26) CatalanCore.Li2.NVMod.FamilySource.V12C50.rho rho_source]
  decide +kernel
-- kcost: 3 s estimated; original endpoint check via proved source equalities
set_option trace.profiler true in
theorem endpoint1 : chk1 input=true := by
  unfold chk1
  change (match oneLead (CatalanCore.Li2.NVMod.FamilySource.V12C50.key 26) with | none=>false | some q=>ratUnitCheck 73 ((1712466760969978825072328666356802307259774146969600000000:ℚ)^26*q))=true
  rw [oneLeadWith_spec (CatalanCore.Li2.NVMod.FamilySource.V12C50.key 26) (14) CatalanCore.Li2.NVMod.RegularFamily.V12C50.regularValue (CatalanCore.Li2.NVMod.RegularFamily.V12C50.h0_key 26) (CatalanCore.Li2.NVMod.RegularFamily.V12C50.regular_source 26)]
  decide +kernel
-- kcost: 3 s estimated; original endpoint check via proved source equalities
set_option trace.profiler true in
theorem endpointInf : chkInf input=true := by
  change (decide (26≤(slots (CatalanCore.Li2.NVMod.FamilySource.V12C50.key 26)).length) && ratUnitCheck 73 ((1712466760969978825072328666356802307259774146969600000000:ℚ)^26*infLead (CatalanCore.Li2.NVMod.FamilySource.V12C50.key 26)))=true
  rw [infLeadNative_spec (CatalanCore.Li2.NVMod.FamilySource.V12C50.key 26) CatalanCore.Li2.NVMod.FamilySource.V12C50.num CatalanCore.Li2.NVMod.FamilySource.V12C50.den CatalanCore.Li2.NVMod.FamilySource.V12C50.indices CatalanCore.Li2.NVMod.FamilySource.V12C50.rho (CatalanCore.Li2.NVMod.FamilySource.V12C50.num_source 26) (CatalanCore.Li2.NVMod.FamilySource.V12C50.den_source 26) CatalanCore.Li2.NVMod.FamilySource.V12C50.indices_nodup ((CatalanCore.Li2.NVMod.FamilySource.V12C50.indices_set 26).trans (poles_eq_poleSet _)) rho_source]
  decide +kernel
-- kcost: 1 s estimated; coefficientwise integer remainder binding
set_option trace.profiler true in
theorem mod_ok : momentResidueCheck 73 26 CatalanCore.Li2.NVMod.FamilySource.V12C50.moments CatalanCore.Li2.NVMod.PolynomialData.V12C50S26.data.moments=true := by decide +kernel

-- kcost: 1 s estimated; existing arithmetic proofs and outer list length only
def interior : PolynomialCert.InteriorChecked input where
  data:=CatalanCore.Li2.NVMod.PolynomialData.V12C50S26.data.toCertificate
  bounds:=(PolynomialCompute.bounds_nat_transfer 26 73 CatalanCore.Li2.NVMod.PolynomialData.V12C50S26.data).symm.trans CatalanCore.Li2.NVMod.PolynomialData.V12C50S26.bounds_ok
  arithmetic:=(PolynomialCompute.arithmetic_transfer 26 73 CatalanCore.Li2.NVMod.PolynomialData.V12C50S26.data).symm.trans CatalanCore.Li2.NVMod.PolynomialData.V12C50S26.arithmetic_ok
  moments:=by
    intro e he
    exact momentResidueCheck_sound 73 26 CatalanCore.Li2.NVMod.FamilySource.V12C50.moments CatalanCore.Li2.NVMod.PolynomialData.V12C50S26.data.moments mod_ok (by decide +kernel) e he

def checked : KeyCertificate :=
  ⟨input,by decide +kernel,endpoint0,endpoint1,endpointInf,interior⟩
#print axioms checked
end
end CatalanCore.Li2.NVMod.KeyData.V12C50S26
