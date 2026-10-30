import CatalanCore.Uniform.Decay.Optimization.Lambda24FinalData
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 1
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace CatalanCore.Uniform.Decay.Optimization.Lambda24Final
open CatalanCore.Uniform.Decay.SignedPilot
theorem streamed0 : streamCheck values (constant0Tape.getD 0 0) (constant0Tape.getD 1 0).toNat weights0 (2119691176337932005288694405198414652) (2119691176337932005288694405198418138) = true := by decide +kernel
theorem transferred0 : checkRows values [expression0] [(2119691176337932005288694405198414652,2119691176337932005288694405198418138)] = true := by
  unfold expression0
  rw [checkRows_stream]
  exact streamed0
theorem streamed1 : streamCheck values (constant1Tape.getD 0 0) (constant1Tape.getD 1 0).toNat weights1 (2119689204414005792908821978887404733) (2119689204414005792908821978887408267) = true := by decide +kernel
theorem transferred1 : checkRows values [expression1] [(2119689204414005792908821978887404733,2119689204414005792908821978887408267)] = true := by
  unfold expression1
  rw [checkRows_stream]
  exact streamed1
theorem streamed2 : streamCheck values (constant2Tape.getD 0 0) (constant2Tape.getD 1 0).toNat weights2 (2119687221371988095587318164799616619) (2119687221371988095587318164799620229) = true := by decide +kernel
theorem transferred2 : checkRows values [expression2] [(2119687221371988095587318164799616619,2119687221371988095587318164799620229)] = true := by
  unfold expression2
  rw [checkRows_stream]
  exact streamed2
theorem streamed3 : streamCheck values (constant3Tape.getD 0 0) (constant3Tape.getD 1 0).toNat weights3 (2119685164065200767763070719254753008) (2119685164065200767763070719254756734) = true := by decide +kernel
theorem transferred3 : checkRows values [expression3] [(2119685164065200767763070719254753008,2119685164065200767763070719254756734)] = true := by
  unfold expression3
  rw [checkRows_stream]
  exact streamed3
theorem streamed4 : streamCheck values (constant4Tape.getD 0 0) (constant4Tape.getD 1 0).toNat weights4 (2119683012245796616129740560537719762) (2119683012245796616129740560537723680) = true := by decide +kernel
theorem transferred4 : checkRows values [expression4] [(2119683012245796616129740560537719762,2119683012245796616129740560537723680)] = true := by
  unfold expression4
  rw [checkRows_stream]
  exact streamed4
theorem streamed5 : streamCheck values (constant5Tape.getD 0 0) (constant5Tape.getD 1 0).toNat weights5 (2119680756727707114104476244920425771) (2119680756727707114104476244920429969) = true := by decide +kernel
theorem transferred5 : checkRows values [expression5] [(2119680756727707114104476244920425771,2119680756727707114104476244920429969)] = true := by
  unfold expression5
  rw [checkRows_stream]
  exact streamed5
theorem streamed6 : streamCheck values (constant6Tape.getD 0 0) (constant6Tape.getD 1 0).toNat weights6 (2119678399547493429803843940331539158) (2119678399547493429803843940331543772) = true := by decide +kernel
theorem transferred6 : checkRows values [expression6] [(2119678399547493429803843940331539158,2119678399547493429803843940331543772)] = true := by
  unfold expression6
  rw [checkRows_stream]
  exact streamed6
theorem streamed7 : streamCheck values (constant7Tape.getD 0 0) (constant7Tape.getD 1 0).toNat weights7 (2119675946088667186595126394565861598) (2119675946088667186595126394565866828) = true := by decide +kernel
theorem transferred7 : checkRows values [expression7] [(2119675946088667186595126394565861598,2119675946088667186595126394565866828)] = true := by
  unfold expression7
  rw [checkRows_stream]
  exact streamed7
end CatalanCore.Uniform.Decay.Optimization.Lambda24Final
