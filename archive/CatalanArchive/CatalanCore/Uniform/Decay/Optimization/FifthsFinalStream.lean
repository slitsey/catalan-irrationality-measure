import CatalanCore.Uniform.Decay.Optimization.FifthsFinalData
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 1
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace CatalanCore.Uniform.Decay.Optimization.FifthsFinal
open CatalanCore.Uniform.Decay.SignedPilot
theorem streamed0 : streamCheck values (constant0Tape.getD 0 0) (constant0Tape.getD 1 0).toNat weights0 (2075778705987793811375380310397970624) (2075778705987793811375380310397983918) = true := by decide +kernel
theorem transferred0 : checkRows values [expression0] [(2075778705987793811375380310397970624,2075778705987793811375380310397983918)] = true := by
  unfold expression0
  rw [checkRows_stream]
  exact streamed0
theorem streamed1 : streamCheck values (constant1Tape.getD 0 0) (constant1Tape.getD 1 0).toNat weights1 (2075776978299131031345003022417660990) (2075776978299131031345003022417674336) = true := by decide +kernel
theorem transferred1 : checkRows values [expression1] [(2075776978299131031345003022417660990,2075776978299131031345003022417674336)] = true := by
  unfold expression1
  rw [checkRows_stream]
  exact streamed1
theorem streamed2 : streamCheck values (constant2Tape.getD 0 0) (constant2Tape.getD 1 0).toNat weights2 (2075775261027200292565305100818666965) (2075775261027200292565305100818680403) = true := by decide +kernel
theorem transferred2 : checkRows values [expression2] [(2075775261027200292565305100818666965,2075775261027200292565305100818680403)] = true := by
  unfold expression2
  rw [checkRows_stream]
  exact streamed2
theorem streamed3 : streamCheck values (constant3Tape.getD 0 0) (constant3Tape.getD 1 0).toNat weights3 (2075773480253364043848990876969332009) (2075773480253364043848990876969345587) = true := by decide +kernel
theorem transferred3 : checkRows values [expression3] [(2075773480253364043848990876969332009,2075773480253364043848990876969345587)] = true := by
  unfold expression3
  rw [checkRows_stream]
  exact streamed3
theorem streamed4 : streamCheck values (constant4Tape.getD 0 0) (constant4Tape.getD 1 0).toNat weights4 (2075771610721659074227140166138280150) (2075771610721659074227140166138293940) = true := by decide +kernel
theorem transferred4 : checkRows values [expression4] [(2075771610721659074227140166138280150,2075771610721659074227140166138293940)] = true := by
  unfold expression4
  rw [checkRows_stream]
  exact streamed4
theorem streamed5 : streamCheck values (constant5Tape.getD 0 0) (constant5Tape.getD 1 0).toNat weights5 (2075769639531382162013069004160942043) (2075769639531382162013069004160956161) = true := by decide +kernel
theorem transferred5 : checkRows values [expression5] [(2075769639531382162013069004160942043,2075769639531382162013069004160956161)] = true := by
  unfold expression5
  rw [checkRows_stream]
  exact streamed5
theorem streamed6 : streamCheck values (constant6Tape.getD 0 0) (constant6Tape.getD 1 0).toNat weights6 (2075767566530145860760527404906987910) (2075767566530145860760527404907002516) = true := by decide +kernel
theorem transferred6 : checkRows values [expression6] [(2075767566530145860760527404906987910,2075767566530145860760527404907002516)] = true := by
  unfold expression6
  rw [checkRows_stream]
  exact streamed6
theorem streamed7 : streamCheck values (constant7Tape.getD 0 0) (constant7Tape.getD 1 0).toNat weights7 (2075765395409319365306830533744908342) (2075765395409319365306830533744923660) = true := by decide +kernel
theorem transferred7 : checkRows values [expression7] [(2075765395409319365306830533744908342,2075765395409319365306830533744923660)] = true := by
  unfold expression7
  rw [checkRows_stream]
  exact streamed7
end CatalanCore.Uniform.Decay.Optimization.FifthsFinal
