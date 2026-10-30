import CatalanCore.Uniform.Decay.Optimization.Chi3FinalData
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 1
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace CatalanCore.Uniform.Decay.Optimization.Chi3Final
open CatalanCore.Uniform.Decay.SignedPilot
theorem streamed0 : streamCheck values (constant0Tape.getD 0 0) (constant0Tape.getD 1 0).toNat weights0 (2317747724216825543874912463389393185) (2317747724216825543874912463389397589) = true := by decide +kernel
theorem transferred0 : checkRows values [expression0] [(2317747724216825543874912463389393185,2317747724216825543874912463389397589)] = true := by
  unfold expression0
  rw [checkRows_stream]
  exact streamed0
theorem streamed1 : streamCheck values (constant1Tape.getD 0 0) (constant1Tape.getD 1 0).toNat weights1 (2317747751851777905742197990117329638) (2317747751851777905742197990117334054) = true := by decide +kernel
theorem transferred1 : checkRows values [expression1] [(2317747751851777905742197990117329638,2317747751851777905742197990117334054)] = true := by
  unfold expression1
  rw [checkRows_stream]
  exact streamed1
theorem streamed2 : streamCheck values (constant2Tape.getD 0 0) (constant2Tape.getD 1 0).toNat weights2 (2317747880746866352906726215271892126) (2317747880746866352906726215271896550) = true := by decide +kernel
theorem transferred2 : checkRows values [expression2] [(2317747880746866352906726215271892126,2317747880746866352906726215271896550)] = true := by
  unfold expression2
  rw [checkRows_stream]
  exact streamed2
theorem streamed3 : streamCheck values (constant3Tape.getD 0 0) (constant3Tape.getD 1 0).toNat weights3 (2317748073127927326256821028544346984) (2317748073127927326256821028544351436) = true := by decide +kernel
theorem transferred3 : checkRows values [expression3] [(2317748073127927326256821028544346984,2317748073127927326256821028544351436)] = true := by
  unfold expression3
  rw [checkRows_stream]
  exact streamed3
theorem streamed4 : streamCheck values (constant4Tape.getD 0 0) (constant4Tape.getD 1 0).toNat weights4 (2317748293623803877036575697435637872) (2317748293623803877036575697435642350) = true := by decide +kernel
theorem transferred4 : checkRows values [expression4] [(2317748293623803877036575697435637872,2317748293623803877036575697435642350)] = true := by
  unfold expression4
  rw [checkRows_stream]
  exact streamed4
theorem streamed5 : streamCheck values (constant5Tape.getD 0 0) (constant5Tape.getD 1 0).toNat weights5 (2317748516077827460935683213661029290) (2317748516077827460935683213661033812) = true := by decide +kernel
theorem transferred5 : checkRows values [expression5] [(2317748516077827460935683213661029290,2317748516077827460935683213661033812)] = true := by
  unfold expression5
  rw [checkRows_stream]
  exact streamed5
theorem streamed6 : streamCheck values (constant6Tape.getD 0 0) (constant6Tape.getD 1 0).toNat weights6 (2317748721229542293694019427122443934) (2317748721229542293694019427122448512) = true := by decide +kernel
theorem transferred6 : checkRows values [expression6] [(2317748721229542293694019427122443934,2317748721229542293694019427122448512)] = true := by
  unfold expression6
  rw [checkRows_stream]
  exact streamed6
theorem streamed7 : streamCheck values (constant7Tape.getD 0 0) (constant7Tape.getD 1 0).toNat weights7 (2317748896750257563742961952188745128) (2317748896750257563742961952188749786) = true := by decide +kernel
theorem transferred7 : checkRows values [expression7] [(2317748896750257563742961952188745128,2317748896750257563742961952188749786)] = true := by
  unfold expression7
  rw [checkRows_stream]
  exact streamed7
end CatalanCore.Uniform.Decay.Optimization.Chi3Final
