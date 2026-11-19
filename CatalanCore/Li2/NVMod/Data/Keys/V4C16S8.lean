module
public import CatalanCore.Li2.NVMod.Data.Regular.V4C16
public import CatalanCore.Li2.NVMod.Data.Polynomial.V4C16S8
public import CatalanCore.Li2.NVMod.DataSupport.PolynomialPackageSupport
public import CatalanCore.Li2.NVMod.DataSupport.PolynomialInfSource
public import CatalanCore.Li2.NVMod.DataSupport.Factorials
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option backward.isDefEq.respectTransparency false
open Polynomial Finset
namespace CatalanCore.Li2.NVMod.KeyData.V4C16S8
open CatalanCore.Li2.NVMod CatalanCore.Li2.NVMod.DataSupport
noncomputable section

-- kcost: 1 s estimated; closed endpoint orders and literal fields, shared factorial theorem
def input : EndpointInput where
  -- kcost: 1 s estimated; finite endpoint orders, checked literal fields
  key:=CatalanCore.Li2.NVMod.FamilySource.V4C16.key 8
  p:=29
  D:=53250009120000
  clearZ:=15
  clearOne:=10
  v0:=36
  v1:=50
  D_pos:=by decide +kernel
  mz:=CatalanCore.Li2.NVMod.FamilySource.V4C16.mz
  moment_clear:=by
    intro i j
    apply CatalanCore.Li2.NVMod.FamilySource.V4C16.moment_source 8
    have hi:=i.isLt
    have hj:=j.isLt
    change i.val<8 at hi
    change j.val<8 at hj
    omega
  order_zero:=by decide +kernel
  order_one:=by
    change (50:ℤ)=(10:ℤ)*8+oneOrder (CatalanCore.Li2.NVMod.FamilySource.V4C16.key 8)
    rw [oneOrderWith_spec,CatalanCore.Li2.NVMod.RegularFamily.V4C16.h0_key]
    decide +kernel
  factorials:=allFactorials (CatalanCore.Li2.NVMod.FamilySource.V4C16.key 8)

theorem rho_source : ∀m∈poleSet (CatalanCore.Li2.NVMod.FamilySource.V4C16.key 8),CatalanCore.Li2.NVMod.FamilySource.V4C16.rho m=residue (CatalanCore.Li2.NVMod.FamilySource.V4C16.key 8) m := by
  intro m hm
  apply CatalanCore.Li2.NVMod.FamilySource.V4C16.rho_source 8 m
  rwa [(CatalanCore.Li2.NVMod.FamilySource.V4C16.indices_set 8).trans (poles_eq_poleSet _)]

-- kcost: 3 s estimated; original endpoint check via proved source equalities
set_option trace.profiler true in
theorem endpoint0 : chk0 input=true := by
  change ((topPoles (CatalanCore.Li2.NVMod.FamilySource.V4C16.key 8)).length == 8 && ratUnitCheck 29 ((53250009120000:ℚ)^8*zeroLead (CatalanCore.Li2.NVMod.FamilySource.V4C16.key 8)))=true
  rw [zeroLead_with_residues (CatalanCore.Li2.NVMod.FamilySource.V4C16.key 8) CatalanCore.Li2.NVMod.FamilySource.V4C16.rho rho_source]
  decide +kernel
-- kcost: 3 s estimated; original endpoint check via proved source equalities
set_option trace.profiler true in
theorem endpoint1 : chk1 input=true := by
  unfold chk1
  change (match oneLead (CatalanCore.Li2.NVMod.FamilySource.V4C16.key 8) with | none=>false | some q=>ratUnitCheck 29 ((53250009120000:ℚ)^8*q))=true
  rw [oneLeadWith_spec (CatalanCore.Li2.NVMod.FamilySource.V4C16.key 8) (4) CatalanCore.Li2.NVMod.RegularFamily.V4C16.regularValue (CatalanCore.Li2.NVMod.RegularFamily.V4C16.h0_key 8) (CatalanCore.Li2.NVMod.RegularFamily.V4C16.regular_source 8)]
  decide +kernel
-- kcost: 3 s estimated; original endpoint check via proved source equalities
set_option trace.profiler true in
theorem endpointInf : chkInf input=true := by
  change (decide (8≤(slots (CatalanCore.Li2.NVMod.FamilySource.V4C16.key 8)).length) && ratUnitCheck 29 ((53250009120000:ℚ)^8*infLead (CatalanCore.Li2.NVMod.FamilySource.V4C16.key 8)))=true
  rw [infLeadNative_spec (CatalanCore.Li2.NVMod.FamilySource.V4C16.key 8) CatalanCore.Li2.NVMod.FamilySource.V4C16.num CatalanCore.Li2.NVMod.FamilySource.V4C16.den CatalanCore.Li2.NVMod.FamilySource.V4C16.indices CatalanCore.Li2.NVMod.FamilySource.V4C16.rho (CatalanCore.Li2.NVMod.FamilySource.V4C16.num_source 8) (CatalanCore.Li2.NVMod.FamilySource.V4C16.den_source 8) CatalanCore.Li2.NVMod.FamilySource.V4C16.indices_nodup ((CatalanCore.Li2.NVMod.FamilySource.V4C16.indices_set 8).trans (poles_eq_poleSet _)) rho_source]
  decide +kernel
-- kcost: 1 s estimated; coefficientwise integer remainder binding
set_option trace.profiler true in
theorem mod_ok : momentResidueCheck 29 8 CatalanCore.Li2.NVMod.FamilySource.V4C16.moments CatalanCore.Li2.NVMod.PolynomialData.V4C16S8.data.moments=true := by decide +kernel

-- kcost: 1 s estimated; existing arithmetic proofs and outer list length only
def interior : PolynomialCert.InteriorChecked input where
  data:=CatalanCore.Li2.NVMod.PolynomialData.V4C16S8.data.toCertificate
  bounds:=(PolynomialCompute.bounds_nat_transfer 8 29 CatalanCore.Li2.NVMod.PolynomialData.V4C16S8.data).symm.trans CatalanCore.Li2.NVMod.PolynomialData.V4C16S8.bounds_ok
  arithmetic:=(PolynomialCompute.arithmetic_transfer 8 29 CatalanCore.Li2.NVMod.PolynomialData.V4C16S8.data).symm.trans CatalanCore.Li2.NVMod.PolynomialData.V4C16S8.arithmetic_ok
  moments:=by
    intro e he
    exact momentResidueCheck_sound 29 8 CatalanCore.Li2.NVMod.FamilySource.V4C16.moments CatalanCore.Li2.NVMod.PolynomialData.V4C16S8.data.moments mod_ok (by decide +kernel) e he

def checked : KeyCertificate :=
  ⟨input,by decide +kernel,endpoint0,endpoint1,endpointInf,interior⟩
#print axioms checked
end
end CatalanCore.Li2.NVMod.KeyData.V4C16S8
