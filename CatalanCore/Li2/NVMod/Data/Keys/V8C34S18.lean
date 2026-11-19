module
public import CatalanCore.Li2.NVMod.Data.Regular.V8C34
public import CatalanCore.Li2.NVMod.Data.Polynomial.V8C34S18
public import CatalanCore.Li2.NVMod.DataSupport.PolynomialPackageSupport
public import CatalanCore.Li2.NVMod.DataSupport.PolynomialInfSource
public import CatalanCore.Li2.NVMod.DataSupport.Factorials
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option backward.isDefEq.respectTransparency false
open Polynomial Finset
namespace CatalanCore.Li2.NVMod.KeyData.V8C34S18
open CatalanCore.Li2.NVMod CatalanCore.Li2.NVMod.DataSupport
noncomputable section

-- kcost: 1 s estimated; closed endpoint orders and literal fields, shared factorial theorem
def input : EndpointInput where
  -- kcost: 1 s estimated; finite endpoint orders, checked literal fields
  key:=CatalanCore.Li2.NVMod.FamilySource.V8C34.key 18
  p:=37
  D:=6838148142154569849030079257600000000
  clearZ:=33
  clearOne:=24
  v0:=171
  v1:=276
  D_pos:=by decide +kernel
  mz:=CatalanCore.Li2.NVMod.FamilySource.V8C34.mz
  moment_clear:=by
    intro i j
    apply CatalanCore.Li2.NVMod.FamilySource.V8C34.moment_source 18
    have hi:=i.isLt
    have hj:=j.isLt
    change i.val<18 at hi
    change j.val<18 at hj
    omega
  order_zero:=by decide +kernel
  order_one:=by
    change (276:ℤ)=(24:ℤ)*18+oneOrder (CatalanCore.Li2.NVMod.FamilySource.V8C34.key 18)
    rw [oneOrderWith_spec,CatalanCore.Li2.NVMod.RegularFamily.V8C34.h0_key]
    decide +kernel
  factorials:=allFactorials (CatalanCore.Li2.NVMod.FamilySource.V8C34.key 18)

theorem rho_source : ∀m∈poleSet (CatalanCore.Li2.NVMod.FamilySource.V8C34.key 18),CatalanCore.Li2.NVMod.FamilySource.V8C34.rho m=residue (CatalanCore.Li2.NVMod.FamilySource.V8C34.key 18) m := by
  intro m hm
  apply CatalanCore.Li2.NVMod.FamilySource.V8C34.rho_source 18 m
  rwa [(CatalanCore.Li2.NVMod.FamilySource.V8C34.indices_set 18).trans (poles_eq_poleSet _)]

-- kcost: 3 s estimated; original endpoint check via proved source equalities
set_option trace.profiler true in
theorem endpoint0 : chk0 input=true := by
  change ((topPoles (CatalanCore.Li2.NVMod.FamilySource.V8C34.key 18)).length == 18 && ratUnitCheck 37 ((6838148142154569849030079257600000000:ℚ)^18*zeroLead (CatalanCore.Li2.NVMod.FamilySource.V8C34.key 18)))=true
  rw [zeroLead_with_residues (CatalanCore.Li2.NVMod.FamilySource.V8C34.key 18) CatalanCore.Li2.NVMod.FamilySource.V8C34.rho rho_source]
  decide +kernel
-- kcost: 3 s estimated; original endpoint check via proved source equalities
set_option trace.profiler true in
theorem endpoint1 : chk1 input=true := by
  unfold chk1
  change (match oneLead (CatalanCore.Li2.NVMod.FamilySource.V8C34.key 18) with | none=>false | some q=>ratUnitCheck 37 ((6838148142154569849030079257600000000:ℚ)^18*q))=true
  rw [oneLeadWith_spec (CatalanCore.Li2.NVMod.FamilySource.V8C34.key 18) (10) CatalanCore.Li2.NVMod.RegularFamily.V8C34.regularValue (CatalanCore.Li2.NVMod.RegularFamily.V8C34.h0_key 18) (CatalanCore.Li2.NVMod.RegularFamily.V8C34.regular_source 18)]
  decide +kernel
-- kcost: 3 s estimated; original endpoint check via proved source equalities
set_option trace.profiler true in
theorem endpointInf : chkInf input=true := by
  change (decide (18≤(slots (CatalanCore.Li2.NVMod.FamilySource.V8C34.key 18)).length) && ratUnitCheck 37 ((6838148142154569849030079257600000000:ℚ)^18*infLead (CatalanCore.Li2.NVMod.FamilySource.V8C34.key 18)))=true
  rw [infLeadNative_spec (CatalanCore.Li2.NVMod.FamilySource.V8C34.key 18) CatalanCore.Li2.NVMod.FamilySource.V8C34.num CatalanCore.Li2.NVMod.FamilySource.V8C34.den CatalanCore.Li2.NVMod.FamilySource.V8C34.indices CatalanCore.Li2.NVMod.FamilySource.V8C34.rho (CatalanCore.Li2.NVMod.FamilySource.V8C34.num_source 18) (CatalanCore.Li2.NVMod.FamilySource.V8C34.den_source 18) CatalanCore.Li2.NVMod.FamilySource.V8C34.indices_nodup ((CatalanCore.Li2.NVMod.FamilySource.V8C34.indices_set 18).trans (poles_eq_poleSet _)) rho_source]
  decide +kernel
-- kcost: 1 s estimated; coefficientwise integer remainder binding
set_option trace.profiler true in
theorem mod_ok : momentResidueCheck 37 18 CatalanCore.Li2.NVMod.FamilySource.V8C34.moments CatalanCore.Li2.NVMod.PolynomialData.V8C34S18.data.moments=true := by decide +kernel

-- kcost: 1 s estimated; existing arithmetic proofs and outer list length only
def interior : PolynomialCert.InteriorChecked input where
  data:=CatalanCore.Li2.NVMod.PolynomialData.V8C34S18.data.toCertificate
  bounds:=(PolynomialCompute.bounds_nat_transfer 18 37 CatalanCore.Li2.NVMod.PolynomialData.V8C34S18.data).symm.trans CatalanCore.Li2.NVMod.PolynomialData.V8C34S18.bounds_ok
  arithmetic:=(PolynomialCompute.arithmetic_transfer 18 37 CatalanCore.Li2.NVMod.PolynomialData.V8C34S18.data).symm.trans CatalanCore.Li2.NVMod.PolynomialData.V8C34S18.arithmetic_ok
  moments:=by
    intro e he
    exact momentResidueCheck_sound 37 18 CatalanCore.Li2.NVMod.FamilySource.V8C34.moments CatalanCore.Li2.NVMod.PolynomialData.V8C34S18.data.moments mod_ok (by decide +kernel) e he

def checked : KeyCertificate :=
  ⟨input,by decide +kernel,endpoint0,endpoint1,endpointInf,interior⟩
#print axioms checked
end
end CatalanCore.Li2.NVMod.KeyData.V8C34S18
