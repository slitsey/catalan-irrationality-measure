module
public import CatalanCore.Li2.DecayCert.Simple.Data.L2_25_r26_3.CA0
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open MeasureTheory Set
namespace CatalanCore.Li2.DecayCert.Simple.Data.L2_25_r26_3
open CatalanCore.Li2.DecayCert CatalanCore.Li2.DecayCert.Simple CatalanCore.Li2.DecayCert.LatticeSimple CatalanCore.Li2.DecayCert.LatticeGate
theorem acells_eq : aside.away.flatten++aside.roots=acells := rfl
theorem acells_ok : ∀ c ∈ acells,ACell.ok (setup.sourceAt pair.rho) logs c=true := List.forall_mem_cons.2 ⟨c062_ok,List.forall_mem_cons.2 ⟨c063_ok,List.forall_mem_cons.2 ⟨c064_ok,List.forall_mem_cons.2 ⟨c065_ok,List.forall_mem_cons.2 ⟨c066_ok,List.forall_mem_cons.2 ⟨c067_ok,List.forall_mem_cons.2 ⟨c068_ok,List.forall_mem_cons.2 ⟨c069_ok,List.forall_mem_cons.2 ⟨c070_ok,List.forall_mem_cons.2 ⟨c071_ok,List.forall_mem_cons.2 ⟨c072_ok,List.forall_mem_cons.2 ⟨c074_ok,List.forall_mem_cons.2 ⟨c075_ok,List.forall_mem_cons.2 ⟨c076_ok,List.forall_mem_cons.2 ⟨c079_ok,List.forall_mem_cons.2 ⟨c080_ok,List.forall_mem_cons.2 ⟨c081_ok,List.forall_mem_cons.2 ⟨c078_ok,List.forall_mem_cons.2 ⟨c073_ok,List.forall_mem_cons.2 ⟨c077_ok,(fun _ h => absurd h List.not_mem_nil)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem aside_ok : aside.check (ACell.ok (setup.sourceAt pair.rho) logs) 1 4=true :=
  side_check_of _ _ _ _ acells acells_eq acells_ok (by decide +kernel)
theorem u01 : decide (0 < pair.rho)=true := by decide +kernel
theorem u03 : capsCheck (atomGapCapOK (setup.sourceAt pair.rho) logs pair.aIds aux.qAI) aside acaps=true := by decide +kernel
theorem u04 : decide (aside.pat.plusCap (fun i => acaps.getD i 0)+aside.pat.rootCap aside.ep aside.em ≤ pair.TA)=true := by decide +kernel
theorem u05 : scalarLowerCheck pair.lower (seSum [seScale (-12) (.log setup.terms 2),
    seRat (-4-setup.Iup-2*source.theta-2*(setup.TW+setup.TR)-pair.TA)])=true := by decide +kernel
theorem pair_ok : simplePairCheck setup pair=true := by
  simp only [simplePairCheck,Bool.and_eq_true]
  exact ⟨⟨⟨⟨u01,aside_ok⟩,u03⟩,u04⟩,u05⟩
end CatalanCore.Li2.DecayCert.Simple.Data.L2_25_r26_3
