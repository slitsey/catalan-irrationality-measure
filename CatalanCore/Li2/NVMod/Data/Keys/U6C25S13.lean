module
public import CatalanCore.Li2.NVMod.Data.Regular.U6C25
public import CatalanCore.Li2.NVMod.Data.Polynomial.U6C25S13
public import CatalanCore.Li2.NVMod.DataSupport.PolynomialPackageSupport
public import CatalanCore.Li2.NVMod.DataSupport.PolynomialInfSource
public import CatalanCore.Li2.NVMod.DataSupport.Factorials
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option backward.isDefEq.respectTransparency false
open Polynomial Finset
namespace CatalanCore.Li2.NVMod.KeyData.U6C25S13
open CatalanCore.Li2.NVMod CatalanCore.Li2.NVMod.DataSupport
noncomputable section

-- kcost: 1 s estimated; closed endpoint orders and literal fields, shared factorial theorem
def input : EndpointInput where
  -- kcost: 1 s estimated; finite endpoint orders, checked literal fields
  key:=CatalanCore.Li2.NVMod.FamilySource.U6C25.key 13
  p:=67
  D:=8851357879958761795198771200000
  clearZ:=25
  clearOne:=18
  v0:=91
  v1:=144
  D_pos:=by decide +kernel
  mz:=CatalanCore.Li2.NVMod.FamilySource.U6C25.mz
  moment_clear:=by
    intro i j
    apply CatalanCore.Li2.NVMod.FamilySource.U6C25.moment_source 13
    have hi:=i.isLt
    have hj:=j.isLt
    change i.val<13 at hi
    change j.val<13 at hj
    omega
  order_zero:=by decide +kernel
  order_one:=by
    change (144:ℤ)=(18:ℤ)*13+oneOrder (CatalanCore.Li2.NVMod.FamilySource.U6C25.key 13)
    rw [oneOrderWith_spec,CatalanCore.Li2.NVMod.RegularFamily.U6C25.h0_key]
    decide +kernel
  factorials:=allFactorials (CatalanCore.Li2.NVMod.FamilySource.U6C25.key 13)

theorem rho_source : ∀m∈poleSet (CatalanCore.Li2.NVMod.FamilySource.U6C25.key 13),CatalanCore.Li2.NVMod.FamilySource.U6C25.rho m=residue (CatalanCore.Li2.NVMod.FamilySource.U6C25.key 13) m := by
  intro m hm
  apply CatalanCore.Li2.NVMod.FamilySource.U6C25.rho_source 13 m
  rwa [(CatalanCore.Li2.NVMod.FamilySource.U6C25.indices_set 13).trans (poles_eq_poleSet _)]

-- kcost: 3 s estimated; original endpoint check via proved source equalities
set_option trace.profiler true in
theorem endpoint0 : chk0 input=true := by
  change ((topPoles (CatalanCore.Li2.NVMod.FamilySource.U6C25.key 13)).length == 13 && ratUnitCheck 67 ((8851357879958761795198771200000:ℚ)^13*zeroLead (CatalanCore.Li2.NVMod.FamilySource.U6C25.key 13)))=true
  rw [zeroLead_with_residues (CatalanCore.Li2.NVMod.FamilySource.U6C25.key 13) CatalanCore.Li2.NVMod.FamilySource.U6C25.rho rho_source]
  decide +kernel
-- kcost: 3 s estimated; original endpoint check via proved source equalities
set_option trace.profiler true in
theorem endpoint1 : chk1 input=true := by
  unfold chk1
  change (match oneLead (CatalanCore.Li2.NVMod.FamilySource.U6C25.key 13) with | none=>false | some q=>ratUnitCheck 67 ((8851357879958761795198771200000:ℚ)^13*q))=true
  rw [oneLeadWith_spec (CatalanCore.Li2.NVMod.FamilySource.U6C25.key 13) (6) CatalanCore.Li2.NVMod.RegularFamily.U6C25.regularValue (CatalanCore.Li2.NVMod.RegularFamily.U6C25.h0_key 13) (CatalanCore.Li2.NVMod.RegularFamily.U6C25.regular_source 13)]
  decide +kernel
-- kcost: 3 s estimated; original endpoint check via proved source equalities
set_option trace.profiler true in
theorem endpointInf : chkInf input=true := by
  change (decide (13≤(slots (CatalanCore.Li2.NVMod.FamilySource.U6C25.key 13)).length) && ratUnitCheck 67 ((8851357879958761795198771200000:ℚ)^13*infLead (CatalanCore.Li2.NVMod.FamilySource.U6C25.key 13)))=true
  rw [infLeadNative_spec (CatalanCore.Li2.NVMod.FamilySource.U6C25.key 13) CatalanCore.Li2.NVMod.FamilySource.U6C25.num CatalanCore.Li2.NVMod.FamilySource.U6C25.den CatalanCore.Li2.NVMod.FamilySource.U6C25.indices CatalanCore.Li2.NVMod.FamilySource.U6C25.rho (CatalanCore.Li2.NVMod.FamilySource.U6C25.num_source 13) (CatalanCore.Li2.NVMod.FamilySource.U6C25.den_source 13) CatalanCore.Li2.NVMod.FamilySource.U6C25.indices_nodup ((CatalanCore.Li2.NVMod.FamilySource.U6C25.indices_set 13).trans (poles_eq_poleSet _)) rho_source]
  decide +kernel
-- kcost: 1 s estimated; coefficientwise integer remainder binding
set_option trace.profiler true in
theorem mod_ok : momentResidueCheck 67 13 CatalanCore.Li2.NVMod.FamilySource.U6C25.moments CatalanCore.Li2.NVMod.PolynomialData.U6C25S13.data.moments=true := by decide +kernel

-- kcost: 1 s estimated; existing arithmetic proofs and outer list length only
def interior : PolynomialCert.InteriorChecked input where
  data:=CatalanCore.Li2.NVMod.PolynomialData.U6C25S13.data.toCertificate
  bounds:=(PolynomialCompute.bounds_nat_transfer 13 67 CatalanCore.Li2.NVMod.PolynomialData.U6C25S13.data).symm.trans CatalanCore.Li2.NVMod.PolynomialData.U6C25S13.bounds_ok
  arithmetic:=(PolynomialCompute.arithmetic_transfer 13 67 CatalanCore.Li2.NVMod.PolynomialData.U6C25S13.data).symm.trans CatalanCore.Li2.NVMod.PolynomialData.U6C25S13.arithmetic_ok
  moments:=by
    intro e he
    exact momentResidueCheck_sound 67 13 CatalanCore.Li2.NVMod.FamilySource.U6C25.moments CatalanCore.Li2.NVMod.PolynomialData.U6C25S13.data.moments mod_ok (by decide +kernel) e he

def checked : KeyCertificate :=
  ⟨input,by decide +kernel,endpoint0,endpoint1,endpointInf,interior⟩
#print axioms checked
end
end CatalanCore.Li2.NVMod.KeyData.U6C25S13
