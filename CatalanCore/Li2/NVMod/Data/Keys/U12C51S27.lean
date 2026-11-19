module
public import CatalanCore.Li2.NVMod.Data.Regular.U12C51
public import CatalanCore.Li2.NVMod.Data.Polynomial.U12C51S27
public import CatalanCore.Li2.NVMod.DataSupport.PolynomialPackageSupport
public import CatalanCore.Li2.NVMod.DataSupport.PolynomialInfSource
public import CatalanCore.Li2.NVMod.DataSupport.Factorials
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option backward.isDefEq.respectTransparency false
open Polynomial Finset
namespace CatalanCore.Li2.NVMod.KeyData.U12C51S27
open CatalanCore.Li2.NVMod CatalanCore.Li2.NVMod.DataSupport
noncomputable section

-- kcost: 1 s estimated; closed endpoint orders and literal fields, shared factorial theorem
def input : EndpointInput where
  -- kcost: 1 s estimated; finite endpoint orders, checked literal fields
  key:=CatalanCore.Li2.NVMod.FamilySource.U12C51.key 27
  p:=59
  D:=21892843255710423559053393302611475181413290684050811478487859200000000
  clearZ:=51
  clearOne:=38
  v0:=378
  v1:=646
  D_pos:=by decide +kernel
  mz:=CatalanCore.Li2.NVMod.FamilySource.U12C51.mz
  moment_clear:=by
    intro i j
    apply CatalanCore.Li2.NVMod.FamilySource.U12C51.moment_source 27
    have hi:=i.isLt
    have hj:=j.isLt
    change i.val<27 at hi
    change j.val<27 at hj
    omega
  order_zero:=by decide +kernel
  order_one:=by
    change (646:ℤ)=(38:ℤ)*27+oneOrder (CatalanCore.Li2.NVMod.FamilySource.U12C51.key 27)
    rw [oneOrderWith_spec,CatalanCore.Li2.NVMod.RegularFamily.U12C51.h0_key]
    decide +kernel
  factorials:=allFactorials (CatalanCore.Li2.NVMod.FamilySource.U12C51.key 27)

theorem rho_source : ∀m∈poleSet (CatalanCore.Li2.NVMod.FamilySource.U12C51.key 27),CatalanCore.Li2.NVMod.FamilySource.U12C51.rho m=residue (CatalanCore.Li2.NVMod.FamilySource.U12C51.key 27) m := by
  intro m hm
  apply CatalanCore.Li2.NVMod.FamilySource.U12C51.rho_source 27 m
  rwa [(CatalanCore.Li2.NVMod.FamilySource.U12C51.indices_set 27).trans (poles_eq_poleSet _)]

-- kcost: 3 s estimated; original endpoint check via proved source equalities
set_option trace.profiler true in
theorem endpoint0 : chk0 input=true := by
  change ((topPoles (CatalanCore.Li2.NVMod.FamilySource.U12C51.key 27)).length == 27 && ratUnitCheck 59 ((21892843255710423559053393302611475181413290684050811478487859200000000:ℚ)^27*zeroLead (CatalanCore.Li2.NVMod.FamilySource.U12C51.key 27)))=true
  rw [zeroLead_with_residues (CatalanCore.Li2.NVMod.FamilySource.U12C51.key 27) CatalanCore.Li2.NVMod.FamilySource.U12C51.rho rho_source]
  decide +kernel
-- kcost: 3 s estimated; original endpoint check via proved source equalities
set_option trace.profiler true in
theorem endpoint1 : chk1 input=true := by
  unfold chk1
  change (match oneLead (CatalanCore.Li2.NVMod.FamilySource.U12C51.key 27) with | none=>false | some q=>ratUnitCheck 59 ((21892843255710423559053393302611475181413290684050811478487859200000000:ℚ)^27*q))=true
  rw [oneLeadWith_spec (CatalanCore.Li2.NVMod.FamilySource.U12C51.key 27) (14) CatalanCore.Li2.NVMod.RegularFamily.U12C51.regularValue (CatalanCore.Li2.NVMod.RegularFamily.U12C51.h0_key 27) (CatalanCore.Li2.NVMod.RegularFamily.U12C51.regular_source 27)]
  decide +kernel
-- kcost: 3 s estimated; original endpoint check via proved source equalities
set_option trace.profiler true in
theorem endpointInf : chkInf input=true := by
  change (decide (27≤(slots (CatalanCore.Li2.NVMod.FamilySource.U12C51.key 27)).length) && ratUnitCheck 59 ((21892843255710423559053393302611475181413290684050811478487859200000000:ℚ)^27*infLead (CatalanCore.Li2.NVMod.FamilySource.U12C51.key 27)))=true
  rw [infLeadNative_spec (CatalanCore.Li2.NVMod.FamilySource.U12C51.key 27) CatalanCore.Li2.NVMod.FamilySource.U12C51.num CatalanCore.Li2.NVMod.FamilySource.U12C51.den CatalanCore.Li2.NVMod.FamilySource.U12C51.indices CatalanCore.Li2.NVMod.FamilySource.U12C51.rho (CatalanCore.Li2.NVMod.FamilySource.U12C51.num_source 27) (CatalanCore.Li2.NVMod.FamilySource.U12C51.den_source 27) CatalanCore.Li2.NVMod.FamilySource.U12C51.indices_nodup ((CatalanCore.Li2.NVMod.FamilySource.U12C51.indices_set 27).trans (poles_eq_poleSet _)) rho_source]
  decide +kernel
-- kcost: 1 s estimated; coefficientwise integer remainder binding
set_option trace.profiler true in
theorem mod_ok : momentResidueCheck 59 27 CatalanCore.Li2.NVMod.FamilySource.U12C51.moments CatalanCore.Li2.NVMod.PolynomialData.U12C51S27.data.moments=true := by decide +kernel

-- kcost: 1 s estimated; existing arithmetic proofs and outer list length only
def interior : PolynomialCert.InteriorChecked input where
  data:=CatalanCore.Li2.NVMod.PolynomialData.U12C51S27.data.toCertificate
  bounds:=(PolynomialCompute.bounds_nat_transfer 27 59 CatalanCore.Li2.NVMod.PolynomialData.U12C51S27.data).symm.trans CatalanCore.Li2.NVMod.PolynomialData.U12C51S27.bounds_ok
  arithmetic:=(PolynomialCompute.arithmetic_transfer 27 59 CatalanCore.Li2.NVMod.PolynomialData.U12C51S27.data).symm.trans CatalanCore.Li2.NVMod.PolynomialData.U12C51S27.arithmetic_ok
  moments:=by
    intro e he
    exact momentResidueCheck_sound 59 27 CatalanCore.Li2.NVMod.FamilySource.U12C51.moments CatalanCore.Li2.NVMod.PolynomialData.U12C51S27.data.moments mod_ok (by decide +kernel) e he

def checked : KeyCertificate :=
  ⟨input,by decide +kernel,endpoint0,endpoint1,endpointInf,interior⟩
#print axioms checked
end
end CatalanCore.Li2.NVMod.KeyData.U12C51S27
