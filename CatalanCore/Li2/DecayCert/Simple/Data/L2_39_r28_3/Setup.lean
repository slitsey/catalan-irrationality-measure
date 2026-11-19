module
public import CatalanCore.Li2.DecayCert.Simple.Data.L2_39_r28_3.Src
public import CatalanCore.Li2.DecayCert.Simple.Data.L2_39_r28_3.CW0
public import CatalanCore.Li2.DecayCert.Simple.Data.L2_39_r28_3.CW1
public import CatalanCore.Li2.DecayCert.Simple.Data.L2_39_r28_3.CR0
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open MeasureTheory Set
namespace CatalanCore.Li2.DecayCert.Simple.Data.L2_39_r28_3
open CatalanCore.Li2.DecayCert CatalanCore.Li2.DecayCert.Simple CatalanCore.Li2.DecayCert.LatticeSimple CatalanCore.Li2.DecayCert.LatticeGate
theorem wcells_eq : wside.away.flatten++wside.roots=wcells := rfl
theorem wcells_ok : ∀ c ∈ wcells,WCell.ok source logs c=true := List.forall_mem_cons.2 ⟨c000_ok,List.forall_mem_cons.2 ⟨c001_ok,List.forall_mem_cons.2 ⟨c002_ok,List.forall_mem_cons.2 ⟨c003_ok,List.forall_mem_cons.2 ⟨c004_ok,List.forall_mem_cons.2 ⟨c005_ok,List.forall_mem_cons.2 ⟨c006_ok,List.forall_mem_cons.2 ⟨c007_ok,List.forall_mem_cons.2 ⟨c008_ok,List.forall_mem_cons.2 ⟨c009_ok,List.forall_mem_cons.2 ⟨c010_ok,List.forall_mem_cons.2 ⟨c011_ok,List.forall_mem_cons.2 ⟨c012_ok,List.forall_mem_cons.2 ⟨c013_ok,List.forall_mem_cons.2 ⟨c014_ok,List.forall_mem_cons.2 ⟨c015_ok,List.forall_mem_cons.2 ⟨c016_ok,List.forall_mem_cons.2 ⟨c018_ok,List.forall_mem_cons.2 ⟨c019_ok,List.forall_mem_cons.2 ⟨c020_ok,List.forall_mem_cons.2 ⟨c021_ok,List.forall_mem_cons.2 ⟨c022_ok,List.forall_mem_cons.2 ⟨c023_ok,List.forall_mem_cons.2 ⟨c024_ok,List.forall_mem_cons.2 ⟨c025_ok,List.forall_mem_cons.2 ⟨c026_ok,List.forall_mem_cons.2 ⟨c027_ok,List.forall_mem_cons.2 ⟨c028_ok,List.forall_mem_cons.2 ⟨c029_ok,List.forall_mem_cons.2 ⟨c030_ok,List.forall_mem_cons.2 ⟨c017_ok,(fun _ h => absurd h List.not_mem_nil)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem rcells_ok : rcells.all (RCell.ok source logs)=true := List.all_eq_true.2 (List.forall_mem_cons.2 ⟨c031_ok,List.forall_mem_cons.2 ⟨c032_ok,List.forall_mem_cons.2 ⟨c033_ok,List.forall_mem_cons.2 ⟨c034_ok,List.forall_mem_cons.2 ⟨c035_ok,List.forall_mem_cons.2 ⟨c036_ok,List.forall_mem_cons.2 ⟨c037_ok,List.forall_mem_cons.2 ⟨c038_ok,List.forall_mem_cons.2 ⟨c039_ok,List.forall_mem_cons.2 ⟨c040_ok,List.forall_mem_cons.2 ⟨c041_ok,List.forall_mem_cons.2 ⟨c042_ok,List.forall_mem_cons.2 ⟨c043_ok,List.forall_mem_cons.2 ⟨c044_ok,List.forall_mem_cons.2 ⟨c045_ok,List.forall_mem_cons.2 ⟨c046_ok,(fun _ h => absurd h List.not_mem_nil)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)
theorem wside_ok : wside.check (WCell.ok source logs) 0 source.Y=true :=
  side_check_of _ _ _ _ wcells wcells_eq wcells_ok (by decide +kernel)
theorem t01 : decide (0 < |z| ∧ |z| < 1 ∧ 1 ≤ setup.cutoff ∧ input.Y ≤ setup.cutoff)=true := by decide +kernel
theorem t06 : capsCheck (gapCapOK source logs setup.wIds aux.qI) wside wcaps=true := by decide +kernel
theorem t07 : decide (wside.pat.plusCap (fun i => wcaps.getD i 0)+wside.pat.rootCap wside.ep wside.em ≤ setup.TW)=true := by decide +kernel
theorem t08 : chainCheck source.Y setup.cutoff (rcells.map RCell.iv)=true := by decide +kernel
theorem t10 : decide ((rcells.map RCell.cap).sum ≤ setup.TR)=true := by decide +kernel
theorem t11 : scalarUpperCheck (latticeTailExpr z input setup.toLS) source.theta=true := by decide +kernel
theorem t12 : scalarUpperCheck (seAdd (seRat (3/(setup.cutoff+1))) (.log setup.terms |z|)) 0=true := by decide +kernel
theorem e1 : ordinaryMomentFast input.second (energyCenter input energy) energy.order emu=true := by decide +kernel
theorem e2 : (List.range energy.order).all (fun k : ℕ=>decide
      (coeffQ emu (k+1)*coeffQ sm (k+1)/(k+1:ℚ)≤(getI eup k:ℚ)/(S:ℚ)))=true := by decide +kernel
theorem e3 : energyShapeCheck input energy=true := by decide +kernel
theorem e4 : scalarUpperCheck (energyBody input energy (crossUpperQ S energy.order eup)) setup.Iup=true := by decide +kernel
theorem t13 : energyTableCheck input setup.energy S setup.emu aux.sm setup.eup setup.Iup=true := by
  simp only [energyTableCheck,Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨by decide +kernel,e1⟩,s17⟩,e2⟩,e3⟩,e4⟩
theorem setup_ok : simpleSetupCheck z input setup=true := by
  simp only [simpleSetupCheck,Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨t01,CatalanCore.Li2.DecayCert.Simple.Data.L2_39_r28_3.In.shape_checked⟩,CatalanCore.Li2.DecayCert.Simple.Data.L2_39_r28_3.In.datum_checked⟩,source_ok⟩,wside_ok⟩,t06⟩,t07⟩,t08⟩,rcells_ok⟩,t10⟩,t11⟩,t12⟩,t13⟩
end CatalanCore.Li2.DecayCert.Simple.Data.L2_39_r28_3
