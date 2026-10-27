import CatalanCore.Uniform.Decay.Optimization.CompactData
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 1
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace CatalanCore.Uniform.Decay.Optimization.Compact
open CatalanCore.Uniform.Decay.SignedPilot
theorem streamed0 : streamCheck values (constant0Tape.getD 0 0) (constant0Tape.getD 1 0).toNat weights0 (2317749702431208069526376901248730469) (2317749702431208069526447651106839811) = true := by decide +kernel
theorem transferred0 : checkRows values [expression0] [(2317749702431208069526376901248730469,2317749702431208069526447651106839811)] = true := by
  unfold expression0
  rw [checkRows_stream]
  exact streamed0
theorem streamed1 : streamCheck values (constant1Tape.getD 0 0) (constant1Tape.getD 1 0).toNat weights1 (2317749679113727184291655464583033323) (2317749679113727184291726623148342949) = true := by decide +kernel
theorem transferred1 : checkRows values [expression1] [(2317749679113727184291655464583033323,2317749679113727184291726623148342949)] = true := by
  unfold expression1
  rw [checkRows_stream]
  exact streamed1
theorem streamed2 : streamCheck values (constant2Tape.getD 0 0) (constant2Tape.getD 1 0).toNat weights2 (2317749655287870647657584493185566700) (2317749655287870647657656062501090304) = true := by decide +kernel
theorem transferred2 : checkRows values [expression2] [(2317749655287870647657584493185566700,2317749655287870647657656062501090304)] = true := by
  unfold expression2
  rw [checkRows_stream]
  exact streamed2
theorem streamed3 : streamCheck values (constant3Tape.getD 0 0) (constant3Tape.getD 1 0).toNat weights3 (2317749631005293847115290745529958058) (2317749631005293847115362727646774034) = true := by decide +kernel
theorem transferred3 : checkRows values [expression3] [(2317749631005293847115290745529958058,2317749631005293847115362727646774034)] = true := by
  unfold expression3
  rw [checkRows_stream]
  exact streamed3
theorem streamed4 : streamCheck values (constant4Tape.getD 0 0) (constant4Tape.getD 1 0).toNat weights4 (2317749606319789905216083750818909733) (2317749606319789905216156147796180843) = true := by decide +kernel
theorem transferred4 : checkRows values [expression4] [(2317749606319789905216083750818909733,2317749606319789905216156147796180843)] = true := by
  unfold expression4
  rw [checkRows_stream]
  exact streamed4
theorem streamed5 : streamCheck values (constant5Tape.getD 0 0) (constant5Tape.getD 1 0).toNat weights5 (2317749581287185751990497824457757953) (2317749581287185751990570638362750863) = true := by decide +kernel
theorem transferred5 : checkRows values [expression5] [(2317749581287185751990497824457757953,2317749581287185751990570638362750863)] = true := by
  unfold expression5
  rw [checkRows_stream]
  exact streamed5
theorem streamed6 : streamCheck values (constant6Tape.getD 0 0) (constant6Tape.getD 1 0).toNat weights6 (2317749555965235055240200491887523769) (2317749555965235055240273724795628665) = true := by decide +kernel
theorem transferred6 : checkRows values [expression6] [(2317749555965235055240200491887523769,2317749555965235055240273724795628665)] = true := by
  unfold expression6
  rw [checkRows_stream]
  exact streamed6
theorem streamed7 : streamCheck values (constant7Tape.getD 0 0) (constant7Tape.getD 1 0).toNat weights7 (2317749530413507769964911134350794020) (2317749530413507769964984788345544176) = true := by decide +kernel
theorem transferred7 : checkRows values [expression7] [(2317749530413507769964911134350794020,2317749530413507769964984788345544176)] = true := by
  unfold expression7
  rw [checkRows_stream]
  exact streamed7
end CatalanCore.Uniform.Decay.Optimization.Compact

