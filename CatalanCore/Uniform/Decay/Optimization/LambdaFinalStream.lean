import CatalanCore.Uniform.Decay.Optimization.LambdaFinalData
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 1
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace CatalanCore.Uniform.Decay.Optimization.LambdaFinal
open CatalanCore.Uniform.Decay.SignedPilot
theorem streamed0 : streamCheck values (constant0Tape.getD 0 0) (constant0Tape.getD 1 0).toNat weights0 (2119241119044051255743988400340685656) (2119241119044051255743988400340697184) = true := by decide +kernel
theorem transferred0 : checkRows values [expression0] [(2119241119044051255743988400340685656,2119241119044051255743988400340697184)] = true := by
  unfold expression0
  rw [checkRows_stream]
  exact streamed0
theorem streamed1 : streamCheck values (constant1Tape.getD 0 0) (constant1Tape.getD 1 0).toNat weights1 (2119238693955236747588155126325566061) (2119238693955236747588155126325577689) = true := by decide +kernel
theorem transferred1 : checkRows values [expression1] [(2119238693955236747588155126325566061,2119238693955236747588155126325577689)] = true := by
  unfold expression1
  rw [checkRows_stream]
  exact streamed1
theorem streamed2 : streamCheck values (constant2Tape.getD 0 0) (constant2Tape.getD 1 0).toNat weights2 (2119236452294175874119368017933130696) (2119236452294175874119368017933142480) = true := by decide +kernel
theorem transferred2 : checkRows values [expression2] [(2119236452294175874119368017933130696,2119236452294175874119368017933142480)] = true := by
  unfold expression2
  rw [checkRows_stream]
  exact streamed2
theorem streamed3 : streamCheck values (constant3Tape.getD 0 0) (constant3Tape.getD 1 0).toNat weights3 (2119234268854999472802932114850870183) (2119234268854999472802932114850882215) = true := by decide +kernel
theorem transferred3 : checkRows values [expression3] [(2119234268854999472802932114850870183,2119234268854999472802932114850882215)] = true := by
  unfold expression3
  rw [checkRows_stream]
  exact streamed3
theorem streamed4 : streamCheck values (constant4Tape.getD 0 0) (constant4Tape.getD 1 0).toNat weights4 (2119232092810736921574468116337505225) (2119232092810736921574468116337517645) = true := by decide +kernel
theorem transferred4 : checkRows values [expression4] [(2119232092810736921574468116337505225,2119232092810736921574468116337517645)] = true := by
  unfold expression4
  rw [checkRows_stream]
  exact streamed4
theorem streamed5 : streamCheck values (constant5Tape.getD 0 0) (constant5Tape.getD 1 0).toNat weights5 (2119229889453954075348506002902562007) (2119229889453954075348506002902575007) = true := by decide +kernel
theorem transferred5 : checkRows values [expression5] [(2119229889453954075348506002902562007,2119229889453954075348506002902575007)] = true := by
  unfold expression5
  rw [checkRows_stream]
  exact streamed5
theorem streamed6 : streamCheck values (constant6Tape.getD 0 0) (constant6Tape.getD 1 0).toNat weights6 (2119227643079335587808351917937304276) (2119227643079335587808351917937318148) = true := by decide +kernel
theorem transferred6 : checkRows values [expression6] [(2119227643079335587808351917937304276,2119227643079335587808351917937318148)] = true := by
  unfold expression6
  rw [checkRows_stream]
  exact streamed6
theorem streamed7 : streamCheck values (constant7Tape.getD 0 0) (constant7Tape.getD 1 0).toNat weights7 (2119225343333895768470634112447372701) (2119225343333895768470634112447387833) = true := by decide +kernel
theorem transferred7 : checkRows values [expression7] [(2119225343333895768470634112447372701,2119225343333895768470634112447387833)] = true := by
  unfold expression7
  rw [checkRows_stream]
  exact streamed7
end CatalanCore.Uniform.Decay.Optimization.LambdaFinal
