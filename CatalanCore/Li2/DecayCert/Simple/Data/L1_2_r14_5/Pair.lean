module
public import CatalanCore.Li2.DecayCert.Simple.Data.L1_2_r14_5.CA0
public import CatalanCore.Li2.DecayCert.Simple.Data.L1_2_r14_5.CA1
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open MeasureTheory Set
namespace CatalanCore.Li2.DecayCert.Simple.Data.L1_2_r14_5
open CatalanCore.Li2.DecayCert CatalanCore.Li2.DecayCert.Simple CatalanCore.Li2.DecayCert.LatticeSimple CatalanCore.Li2.DecayCert.LatticeGate
theorem acells_eq : aside.away.flatten++aside.roots=acells := rfl
theorem acells_ok : ∀ c ∈ acells,ACell.ok (setup.sourceAt pair.rho) logs c=true := List.forall_mem_cons.2 ⟨c110_ok,List.forall_mem_cons.2 ⟨c111_ok,List.forall_mem_cons.2 ⟨c112_ok,List.forall_mem_cons.2 ⟨c113_ok,List.forall_mem_cons.2 ⟨c114_ok,List.forall_mem_cons.2 ⟨c115_ok,List.forall_mem_cons.2 ⟨c116_ok,List.forall_mem_cons.2 ⟨c117_ok,List.forall_mem_cons.2 ⟨c119_ok,List.forall_mem_cons.2 ⟨c120_ok,List.forall_mem_cons.2 ⟨c121_ok,List.forall_mem_cons.2 ⟨c122_ok,List.forall_mem_cons.2 ⟨c124_ok,List.forall_mem_cons.2 ⟨c125_ok,List.forall_mem_cons.2 ⟨c126_ok,List.forall_mem_cons.2 ⟨c127_ok,List.forall_mem_cons.2 ⟨c128_ok,List.forall_mem_cons.2 ⟨c129_ok,List.forall_mem_cons.2 ⟨c130_ok,List.forall_mem_cons.2 ⟨c131_ok,List.forall_mem_cons.2 ⟨c133_ok,List.forall_mem_cons.2 ⟨c134_ok,List.forall_mem_cons.2 ⟨c135_ok,List.forall_mem_cons.2 ⟨c136_ok,List.forall_mem_cons.2 ⟨c139_ok,List.forall_mem_cons.2 ⟨c140_ok,List.forall_mem_cons.2 ⟨c141_ok,List.forall_mem_cons.2 ⟨c142_ok,List.forall_mem_cons.2 ⟨c138_ok,List.forall_mem_cons.2 ⟨c118_ok,List.forall_mem_cons.2 ⟨c123_ok,List.forall_mem_cons.2 ⟨c132_ok,List.forall_mem_cons.2 ⟨c137_ok,(fun _ h => absurd h List.not_mem_nil)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
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
end CatalanCore.Li2.DecayCert.Simple.Data.L1_2_r14_5
