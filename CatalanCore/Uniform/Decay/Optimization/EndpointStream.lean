import CatalanCore.Uniform.Decay.Optimization.EndpointData
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 1
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace CatalanCore.Uniform.Decay.Optimization.Endpoint
open CatalanCore.Uniform.Decay.SignedPilot
theorem streamed0 : streamCheck values (constant0Tape.getD 0 0) (constant0Tape.getD 1 0).toNat weights0 (47606315161005816641316918970061985) (47606315161005816641316918970062187) = true := by decide +kernel
theorem transferred0 : checkRows values [expression0] [(47606315161005816641316918970061985,47606315161005816641316918970062187)] = true := by
  unfold expression0
  rw [checkRows_stream]
  exact streamed0
theorem streamed1 : streamCheck values (constant1Tape.getD 0 0) (constant1Tape.getD 1 0).toNat weights1 (47606316238183355140050039495124266) (47606316238183355140050039495124468) = true := by decide +kernel
theorem transferred1 : checkRows values [expression1] [(47606316238183355140050039495124266,47606316238183355140050039495124468)] = true := by
  unfold expression1
  rw [checkRows_stream]
  exact streamed1
theorem streamed2 : streamCheck values (constant2Tape.getD 0 0) (constant2Tape.getD 1 0).toNat weights2 (47606317315360669232928824364783549) (47606317315360669232928824364783751) = true := by decide +kernel
theorem transferred2 : checkRows values [expression2] [(47606317315360669232928824364783549,47606317315360669232928824364783751)] = true := by
  unfold expression2
  rw [checkRows_stream]
  exact streamed2
theorem streamed3 : streamCheck values (constant3Tape.getD 0 0) (constant3Tape.getD 1 0).toNat weights3 (47606318392537758920061935116114407) (47606318392537758920061935116114609) = true := by decide +kernel
theorem transferred3 : checkRows values [expression3] [(47606318392537758920061935116114407,47606318392537758920061935116114609)] = true := by
  unfold expression3
  rw [checkRows_stream]
  exact streamed3
theorem streamed4 : streamCheck values (constant4Tape.getD 0 0) (constant4Tape.getD 1 0).toNat weights4 (47606319469714624201558033295356328) (47606319469714624201558033295356530) = true := by decide +kernel
theorem transferred4 : checkRows values [expression4] [(47606319469714624201558033295356328,47606319469714624201558033295356530)] = true := by
  unfold expression4
  rw [checkRows_stream]
  exact streamed4
theorem streamed5 : streamCheck values (constant5Tape.getD 0 0) (constant5Tape.getD 1 0).toNat weights5 (47606320546891265077525780457913682) (47606320546891265077525780457913884) = true := by decide +kernel
theorem transferred5 : checkRows values [expression5] [(47606320546891265077525780457913682,47606320546891265077525780457913884)] = true := by
  unfold expression5
  rw [checkRows_stream]
  exact streamed5
theorem streamed6 : streamCheck values (constant6Tape.getD 0 0) (constant6Tape.getD 1 0).toNat weights6 (47606321624067681548073838168355673) (47606321624067681548073838168355875) = true := by decide +kernel
theorem transferred6 : checkRows values [expression6] [(47606321624067681548073838168355673,47606321624067681548073838168355875)] = true := by
  unfold expression6
  rw [checkRows_stream]
  exact streamed6
theorem streamed7 : streamCheck values (constant7Tape.getD 0 0) (constant7Tape.getD 1 0).toNat weights7 (47606322701243873613310868000416303) (47606322701243873613310868000416505) = true := by decide +kernel
theorem transferred7 : checkRows values [expression7] [(47606322701243873613310868000416303,47606322701243873613310868000416505)] = true := by
  unfold expression7
  rw [checkRows_stream]
  exact streamed7
theorem streamed8 : streamCheck values (constant8Tape.getD 0 0) (constant8Tape.getD 1 0).toNat weights8 (2269339468533775896560856888570225704) (2269339468533775896560856888570230096) = true := by decide +kernel
theorem transferred8 : checkRows values [expression8] [(2269339468533775896560856888570225704,2269339468533775896560856888570230096)] = true := by
  unfold expression8
  rw [checkRows_stream]
  exact streamed8
theorem streamed9 : streamCheck values (constant9Tape.getD 0 0) (constant9Tape.getD 1 0).toNat weights9 (2270955017236630424518507619446355263) (2270955017236630424518507619446359655) = true := by decide +kernel
theorem transferred9 : checkRows values [expression9] [(2270955017236630424518507619446355263,2270955017236630424518507619446359655)] = true := by
  unfold expression9
  rw [checkRows_stream]
  exact streamed9
end CatalanCore.Uniform.Decay.Optimization.Endpoint
