module

public import CatalanFrames.LambdaHybrid.Assembly
public import CatalanCore.Cert.SigmaHyb.FinalH

@[expose] public section

/-!
# λ hybrid: decay instantiated (MEM2D)

`LamHybDecayK180s` is discharged by `CatalanCore.Cert.SigmaHyb.lam_hybrid_decay`
(`D = 3.9028`, `c = 7.6444`).  The measure theorem is restated with these constants and
`Λ = 3.7102296`: exponent `c/(D - Λ) = 39.6966… ≤ 39.70`.  Only the second-member hypotheses
`Mem2Content`, `Mem2Decay` remain.
-/

open Filter CatalanCore CatalanCore.Rect CatalanCore.Arith.Hybrid CatalanFrames.Lambda

namespace CatalanFrames.LambdaHybrid

/-- Member-1 decay for the hybrid λ family, proved. -/
theorem lam_hyb_decay_member1 :
    HasDecay (hybridFamUp lamFrame (1 / 8)) (((39028 / 10000 : ℚ)) : ℝ)
      (((76444 / 10000 : ℚ)) : ℝ) :=
  CatalanCore.Cert.SigmaHyb.lam_hybrid_decay

/-- **λ hybrid measure, decay discharged**: `μ ≤ 39.70` for `G - 5π²/48`, given the
second-member content and decay. -/
theorem lam_hyb_measure_decayK
    (M2c : Mem2Content lamFrame (((37102296 / 10000000 : ℚ)) : ℝ))
    (M2d : Mem2Decay lamFrame (((39028 / 10000 : ℚ)) : ℝ) (((76444 / 10000 : ℚ)) : ℝ)) :
    Measure.MeasureLBAt ((∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2)
      - 5 * Real.pi ^ 2 / 48) (((3970 / 100 : ℚ)) : ℝ) :=
  lam_hyb_measure_G (Λ := 37102296 / 10000000) (D := 39028 / 10000)
    (C := 76444 / 10000) (E := 3970 / 100) (by norm_num) lam_hyb_decay_member1 M2c M2d
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

#print axioms lam_hyb_measure_decayK

end CatalanFrames.LambdaHybrid
