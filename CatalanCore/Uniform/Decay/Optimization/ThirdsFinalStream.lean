import CatalanCore.Uniform.Decay.Optimization.ThirdsFinalData
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 1
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace CatalanCore.Uniform.Decay.Optimization.ThirdsFinal
open CatalanCore.Uniform.Decay.SignedPilot
theorem streamed0 : streamCheck values (constant0Tape.getD 0 0) (constant0Tape.getD 1 0).toNat weights0 (2060725616074619882112888785519761380) (2060725616074619882112888785519773568) = true := by decide +kernel
theorem transferred0 : checkRows values [expression0] [(2060725616074619882112888785519761380,2060725616074619882112888785519773568)] = true := by
  unfold expression0
  rw [checkRows_stream]
  exact streamed0
theorem streamed1 : streamCheck values (constant1Tape.getD 0 0) (constant1Tape.getD 1 0).toNat weights1 (2060711790385484559985403041853400103) (2060711790385484559985403041853412367) = true := by decide +kernel
theorem transferred1 : checkRows values [expression1] [(2060711790385484559985403041853400103,2060711790385484559985403041853412367)] = true := by
  unfold expression1
  rw [checkRows_stream]
  exact streamed1
theorem streamed2 : streamCheck values (constant2Tape.getD 0 0) (constant2Tape.getD 1 0).toNat weights2 (2060695775418716529696744710651849494) (2060695775418716529696744710651861872) = true := by decide +kernel
theorem transferred2 : checkRows values [expression2] [(2060695775418716529696744710651849494,2060695775418716529696744710651861872)] = true := by
  unfold expression2
  rw [checkRows_stream]
  exact streamed2
theorem streamed3 : streamCheck values (constant3Tape.getD 0 0) (constant3Tape.getD 1 0).toNat weights3 (2060678791485266607075937275113652628) (2060678791485266607075937275113665166) = true := by decide +kernel
theorem transferred3 : checkRows values [expression3] [(2060678791485266607075937275113652628,2060678791485266607075937275113665166)] = true := by
  unfold expression3
  rw [checkRows_stream]
  exact streamed3
theorem streamed4 : streamCheck values (constant4Tape.getD 0 0) (constant4Tape.getD 1 0).toNat weights4 (2060661468597018107645910518092222206) (2060661468597018107645910518092234944) = true := by decide +kernel
theorem transferred4 : checkRows values [expression4] [(2060661468597018107645910518092222206,2060661468597018107645910518092234944)] = true := by
  unfold expression4
  rw [checkRows_stream]
  exact streamed4
theorem streamed5 : streamCheck values (constant5Tape.getD 0 0) (constant5Tape.getD 1 0).toNat weights5 (2060644320348809064353242312628909902) (2060644320348809064353242312628922920) = true := by decide +kernel
theorem transferred5 : checkRows values [expression5] [(2060644320348809064353242312628909902,2060644320348809064353242312628922920)] = true := by
  unfold expression5
  rw [checkRows_stream]
  exact streamed5
theorem streamed6 : streamCheck values (constant6Tape.getD 0 0) (constant6Tape.getD 1 0).toNat weights6 (2060627673156025715857155778357195136) (2060627673156025715857155778357208512) = true := by decide +kernel
theorem transferred6 : checkRows values [expression6] [(2060627673156025715857155778357195136,2060627673156025715857155778357208512)] = true := by
  unfold expression6
  rw [checkRows_stream]
  exact streamed6
theorem streamed7 : streamCheck values (constant7Tape.getD 0 0) (constant7Tape.getD 1 0).toNat weights7 (2060611791598685052793531174650222637) (2060611791598685052793531174650236469) = true := by decide +kernel
theorem transferred7 : checkRows values [expression7] [(2060611791598685052793531174650222637,2060611791598685052793531174650236469)] = true := by
  unfold expression7
  rw [checkRows_stream]
  exact streamed7
end CatalanCore.Uniform.Decay.Optimization.ThirdsFinal
