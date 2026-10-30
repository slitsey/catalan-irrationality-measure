import CatalanCore.Uniform.Bank.Chi3Rank.RankFinal
#print axioms CatalanCore.Uniform.Bank.Chi3New.chi3_decay
#print axioms CatalanCore.Uniform.Bank.Chi3Rank.chi3_measure_L2_rank
example : CatalanCore.Measure.MeasureLBAt CatalanFrames.P6.chi3L2
    ((137486 / 10000 : ℚ) : ℝ) :=
  CatalanCore.Uniform.Bank.Chi3Rank.chi3_measure_L2_rank
def main : IO Unit := IO.println "Chi3 final audit completed"
