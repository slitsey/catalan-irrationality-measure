module

public import CatalanCore.Uniform.Bank.Plane3.Cover.Check
public import CatalanCore.Uniform.Decay.AltFold
public import CatalanCore.Uniform.Support.Theorem

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000

/-! Thin alpha1/20 receipt instance. Numerical values live in Cover.Data;
the full generic decay/content/point theorems remain unchanged. -/
namespace CatalanCore.Uniform.Bank.Plane3
open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Content.Shape
open CatalanCore.Uniform.Decay.PolyFull CatalanCore.Uniform.Decay.PolyWire3
open CatalanCore.Uniform.Decay.Cert CatalanCore.Uniform.Decay.Nodes
open CatalanCore.Uniform.Decay.Polygon CatalanCore.Uniform.Decay.AltDecay

theorem p3c_pos : (0:ℚ)<1/10 := by norm_num
noncomputable def P3G : BlockGeom := altGeom (1/10) p3c_pos
def p3Lam : ℚ := 3162410560009/960000000000

-- kcost: <1s estimated, two literal pieces, exact equality.
theorem p3_RP : Cover.RP=altPieces (1/10) := by decide +kernel
-- kcost: <1s estimated, two literal pieces, exact equality.
theorem p3_CP : Cover.CP=altPieces (1/10) := by decide +kernel
theorem p3_hrow : P3G.rowPieces=Cover.TabC.RP.map ratPiece := by
  rw [P3G,altGeom_rowPieces]
  show _=Cover.RP.map ratPiece
  rw [p3_RP]
theorem p3_hcol : P3G.colPieces=Cover.TabC.CP.map ratPiece := by
  rw [P3G,altGeom_colPieces]
  show _=Cover.CP.map ratPiece
  rw [p3_CP]
theorem p3_totalMass : P3G.totalMass=21/20 := by rw [P3G,altGeom_totalMass];norm_num
theorem p3_common_mass : P3G.common.mass=1 := by
  simp [P3G,altGeom,single_mass,commonB,PeriodicBlock.mass]
-- kcost: <1s estimated, exact rational literal comparisons.
theorem p3_hMq : Cover.TabC.Mq=P3G.totalMass := by rw [p3_totalMass];decide +kernel
-- kcost: <1s estimated, one exact rational literal comparison.
theorem p3_cc : 0<Cover.Dchi.ccert := by decide +kernel
-- kcost: <1s estimated, one natural field comparison.
theorem p3_dim : Cover.Dchi.dim=3 := by decide +kernel
-- kcost: <1s estimated, one rational literal comparison.
theorem p3_eps : 0<Cover.Dchi.ε := by decide +kernel
-- kcost: 0.26s measured existing N30/two-piece energy class, 4 pair contributions x30 log-series terms; 120 terms plus fixed bindings.
theorem p3_energy : energyCheck 30 (altPieces (1/10)) (altPieces (1/10)) Cover.Dchi.Inu=true := by
  decide +kernel

noncomputable def p3Cert : Support.Certificate P3G.nodePot where
  rules := rulesOfTablesF P3G Cover.TabC p3_hrow p3_hcol p3_hMq
  spline := Cover.Dchi
  polygon := Cover.Pply
  ok := checkPB_of_tablesF P3G Cover.TabC p3_hrow p3_hcol p3_hMq Cover.check_true
  D := Cover.Dchi.Dt
  c := Cover.Dchi.ccert
  hD := rfl
  hc' := rfl
  hc := p3_cc

-- kcost: <1s estimated, two vertices, exact rational inequalities.
theorem p3_negative : ∀ p∈p3Cert.polygon.verts,p.1+p3Cert.polygon.r0≤0 := by decide +kernel
-- kcost: <1s estimated, one exact rational identity.
theorem p3_spline_mass : p3Cert.spline.Mq=1+(1/10:ℚ)/2 := by decide +kernel
theorem p3_node_energy : (p3Cert.spline.Inu:ℝ)≤P3G.nodeEnergy :=
  inu_le_nodeEnergy_of_check (altGeom_rowPieces (1/10) p3c_pos)
    (altGeom_colPieces (1/10) p3c_pos) p3_energy
-- kcost: <1s estimated, two exact rational literals.
theorem p3_eta : p3Lam<Cover.Dchi.Dt := by decide +kernel
-- kcost: <1s estimated, rational difference/division/comparison, fixed scalar count.
theorem p3_ratio : Cover.Dchi.ccert/(Cover.Dchi.Dt-p3Lam)<118 := by decide +kernel

end CatalanCore.Uniform.Bank.Plane3
#print axioms CatalanCore.Uniform.Bank.Plane3.p3Cert
#print axioms CatalanCore.Uniform.Bank.Plane3.p3_energy
#print axioms CatalanCore.Uniform.Bank.Plane3.p3_node_energy
#print axioms CatalanCore.Uniform.Bank.Plane3.p3_ratio
