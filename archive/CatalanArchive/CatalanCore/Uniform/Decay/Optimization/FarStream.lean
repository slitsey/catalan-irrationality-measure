import CatalanCore.Uniform.Decay.Optimization.FarData
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 1
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace CatalanCore.Uniform.Decay.Optimization.Far
open CatalanCore.Uniform.Decay.SignedPilot
theorem streamed0 : streamCheck values (constant0Tape.getD 0 0) (constant0Tape.getD 1 0).toNat weights0 (2317826623724890934845930946308975259) (2317826623724890934845930946308978913) = true := by decide +kernel
theorem transferred0 : checkRows values [expression0] [(2317826623724890934845930946308975259,2317826623724890934845930946308978913)] = true := by
  unfold expression0
  rw [checkRows_stream]
  exact streamed0
theorem streamed1 : streamCheck values (constant1Tape.getD 0 0) (constant1Tape.getD 1 0).toNat weights1 (2317826623955163795556619601732290014) (2317826623955163795556619601732293668) = true := by decide +kernel
theorem transferred1 : checkRows values [expression1] [(2317826623955163795556619601732290014,2317826623955163795556619601732293668)] = true := by
  unfold expression1
  rw [checkRows_stream]
  exact streamed1
theorem streamed2 : streamCheck values (constant2Tape.getD 0 0) (constant2Tape.getD 1 0).toNat weights2 (2317826624200046435850117168362719434) (2317826624200046435850117168362723090) = true := by decide +kernel
theorem transferred2 : checkRows values [expression2] [(2317826624200046435850117168362719434,2317826624200046435850117168362723090)] = true := by
  unfold expression2
  rw [checkRows_stream]
  exact streamed2
theorem streamed3 : streamCheck values (constant3Tape.getD 0 0) (constant3Tape.getD 1 0).toNat weights3 (2317826624456097674193273896874658154) (2317826624456097674193273896874661810) = true := by decide +kernel
theorem transferred3 : checkRows values [expression3] [(2317826624456097674193273896874658154,2317826624456097674193273896874661810)] = true := by
  unfold expression3
  rw [checkRows_stream]
  exact streamed3
theorem streamed4 : streamCheck values (constant4Tape.getD 0 0) (constant4Tape.getD 1 0).toNat weights4 (2317826624719396300722824970294004938) (2317826624719396300722824970294008596) = true := by decide +kernel
theorem transferred4 : checkRows values [expression4] [(2317826624719396300722824970294004938,2317826624719396300722824970294008596)] = true := by
  unfold expression4
  rw [checkRows_stream]
  exact streamed4
theorem streamed5 : streamCheck values (constant5Tape.getD 0 0) (constant5Tape.getD 1 0).toNat weights5 (2317826624985592866903725939284572107) (2317826624985592866903725939284575769) = true := by decide +kernel
theorem transferred5 : checkRows values [expression5] [(2317826624985592866903725939284572107,2317826624985592866903725939284575769)] = true := by
  unfold expression5
  rw [checkRows_stream]
  exact streamed5
theorem streamed6 : streamCheck values (constant6Tape.getD 0 0) (constant6Tape.getD 1 0).toNat weights6 (2317826625249986229636582767506900874) (2317826625249986229636582767506904540) = true := by decide +kernel
theorem transferred6 : checkRows values [expression6] [(2317826625249986229636582767506900874,2317826625249986229636582767506904540)] = true := by
  unfold expression6
  rw [checkRows_stream]
  exact streamed6
theorem streamed7 : streamCheck values (constant7Tape.getD 0 0) (constant7Tape.getD 1 0).toNat weights7 (2317826625507642773788689033346325054) (2317826625507642773788689033346328720) = true := by decide +kernel
theorem transferred7 : checkRows values [expression7] [(2317826625507642773788689033346325054,2317826625507642773788689033346328720)] = true := by
  unfold expression7
  rw [checkRows_stream]
  exact streamed7
end CatalanCore.Uniform.Decay.Optimization.Far

