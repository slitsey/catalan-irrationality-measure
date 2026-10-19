module

public import CatalanFrames.LambdaHybrid.AssemblyDecay
public import CatalanFrames.LambdaHybrid.Mem2DecayProof

@[expose] public section

/-!
# λ hybrid measure theorem with both decay hypotheses discharged (MEM2D)

Only `Mem2Content` (content of the second member) remains.
-/

open Filter CatalanCore CatalanCore.Rect CatalanCore.Arith.Hybrid CatalanFrames.Lambda

namespace CatalanFrames.LambdaHybrid

/-- **λ hybrid measure theorem**, decay of both members proved; only `Mem2Content` remains. -/
theorem lam_hyb_measure_decayK2
    (M2c : Mem2Content lamFrame (((37102296 / 10000000 : ℚ)) : ℝ)) :
    Measure.MeasureLBAt ((∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2)
      - 5 * Real.pi ^ 2 / 48) (((3970 / 100 : ℚ)) : ℝ) :=
  lam_hyb_measure_decayK M2c lam_mem2_decay

#print axioms lam_hyb_measure_decayK2

end CatalanFrames.LambdaHybrid
