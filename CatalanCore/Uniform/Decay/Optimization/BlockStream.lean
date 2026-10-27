import CatalanCore.Uniform.Decay.Optimization.BlockData
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 1
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace CatalanCore.Uniform.Decay.Optimization.Block
open CatalanCore.Uniform.Decay.SignedPilot
theorem streamed0 : streamCheck values (constant0Tape.getD 0 0) (constant0Tape.getD 1 0).toNat weights0 (2317826622312181232073547854188287003) (2317826622312181232073547854188290649) = true := by decide +kernel
theorem transferred0 : checkRows values [expression0] [(2317826622312181232073547854188287003,2317826622312181232073547854188290649)] = true := by
  unfold expression0
  rw [checkRows_stream]
  exact streamed0
theorem streamed1 : streamCheck values (constant1Tape.getD 0 0) (constant1Tape.getD 1 0).toNat weights1 (2317826622384405023551657451763354947) (2317826622384405023551657451763358599) = true := by decide +kernel
theorem transferred1 : checkRows values [expression1] [(2317826622384405023551657451763354947,2317826622384405023551657451763358599)] = true := by
  unfold expression1
  rw [checkRows_stream]
  exact streamed1
theorem streamed2 : streamCheck values (constant2Tape.getD 0 0) (constant2Tape.getD 1 0).toNat weights2 (2317826622910398246970162843863323158) (2317826622910398246970162843863326814) = true := by decide +kernel
theorem transferred2 : checkRows values [expression2] [(2317826622910398246970162843863323158,2317826622910398246970162843863326814)] = true := by
  unfold expression2
  rw [checkRows_stream]
  exact streamed2
theorem streamed3 : streamCheck values (constant3Tape.getD 0 0) (constant3Tape.getD 1 0).toNat weights3 (2317826623883421951497804035747872611) (2317826623883421951497804035747876267) = true := by decide +kernel
theorem transferred3 : checkRows values [expression3] [(2317826623883421951497804035747872611,2317826623883421951497804035747876267)] = true := by
  unfold expression3
  rw [checkRows_stream]
  exact streamed3
theorem streamed4 : streamCheck values (constant4Tape.getD 0 0) (constant4Tape.getD 1 0).toNat weights4 (2317826625141477621448088469363587617) (2317826625141477621448088469363591279) = true := by decide +kernel
theorem transferred4 : checkRows values [expression4] [(2317826625141477621448088469363587617,2317826625141477621448088469363591279)] = true := by
  unfold expression4
  rw [checkRows_stream]
  exact streamed4
theorem streamed5 : streamCheck values (constant5Tape.getD 0 0) (constant5Tape.getD 1 0).toNat weights5 (2317826626385590956073041282121306279) (2317826626385590956073041282121309945) = true := by decide +kernel
theorem transferred5 : checkRows values [expression5] [(2317826626385590956073041282121306279,2317826626385590956073041282121309945)] = true := by
  unfold expression5
  rw [checkRows_stream]
  exact streamed5
theorem streamed6 : streamCheck values (constant6Tape.getD 0 0) (constant6Tape.getD 1 0).toNat weights6 (2317826627189364973443393974447991116) (2317826627189364973443393974447994788) = true := by decide +kernel
theorem transferred6 : checkRows values [expression6] [(2317826627189364973443393974447991116,2317826627189364973443393974447994788)] = true := by
  unfold expression6
  rw [checkRows_stream]
  exact streamed6
theorem streamed7 : streamCheck values (constant7Tape.getD 0 0) (constant7Tape.getD 1 0).toNat weights7 (2317826627293468836828770013579931426) (2317826627293468836828770013579935096) = true := by decide +kernel
theorem transferred7 : checkRows values [expression7] [(2317826627293468836828770013579931426,2317826627293468836828770013579935096)] = true := by
  unfold expression7
  rw [checkRows_stream]
  exact streamed7
end CatalanCore.Uniform.Decay.Optimization.Block
