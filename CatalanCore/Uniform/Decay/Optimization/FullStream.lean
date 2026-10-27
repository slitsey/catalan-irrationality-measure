import CatalanCore.Uniform.Decay.Optimization.FullData
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 1
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace CatalanCore.Uniform.Decay.Optimization.Pilot
open CatalanCore.Uniform.Decay.SignedPilot
theorem shape0 : Potential0Expression = (Potential0Constant.getD 0 0,(Potential0Constant.getD 1 0).toNat,indexedTerms PotentialValues Potential0Weights) := by decide +kernel
theorem streamed0 : streamCheck PotentialValues (Potential0Constant.getD 0 0) (Potential0Constant.getD 1 0).toNat Potential0Weights 2317826624568240401251639979480757054 2317826624614550622167866255382777902 = true := by decide +kernel
theorem transferred0 : checkRows PotentialValues [Potential0Expression] [(2317826624568240401251639979480757054,2317826624614550622167866255382777902)] = true := by
  rw [shape0,checkRows_stream]
  exact streamed0
theorem shape1 : Potential1Expression = (Potential1Constant.getD 0 0,(Potential1Constant.getD 1 0).toNat,indexedTerms PotentialValues Potential1Weights) := by decide +kernel
theorem streamed1 : streamCheck PotentialValues (Potential1Constant.getD 0 0) (Potential1Constant.getD 1 0).toNat Potential1Weights 2317826624568266388224460736385118027 2317826624614576645151408458614766269 = true := by decide +kernel
theorem transferred1 : checkRows PotentialValues [Potential1Expression] [(2317826624568266388224460736385118027,2317826624614576645151408458614766269)] = true := by
  rw [shape1,checkRows_stream]
  exact streamed1
theorem shape2 : Potential2Expression = (Potential2Constant.getD 0 0,(Potential2Constant.getD 1 0).toNat,indexedTerms PotentialValues Potential2Weights) := by decide +kernel
theorem streamed2 : streamCheck PotentialValues (Potential2Constant.getD 0 0) (Potential2Constant.getD 1 0).toNat Potential2Weights 2317826624568292375246077157623609350 2317826624614602668183772296371414178 = true := by decide +kernel
theorem transferred2 : checkRows PotentialValues [Potential2Expression] [(2317826624568292375246077157623609350,2317826624614602668183772296371414178)] = true := by
  rw [shape2,checkRows_stream]
  exact streamed2
theorem shape3 : Potential3Expression = (Potential3Constant.getD 0 0,(Potential3Constant.getD 1 0).toNat,indexedTerms PotentialValues Potential3Weights) := by decide +kernel
theorem streamed3 : streamCheck PotentialValues (Potential3Constant.getD 0 0) (Potential3Constant.getD 1 0).toNat Potential3Weights 2317826624568318362316484933207947626 2317826624614628691264953458681189928 = true := by decide +kernel
theorem transferred3 : checkRows PotentialValues [Potential3Expression] [(2317826624568318362316484933207947626,2317826624614628691264953458681189928)] = true := by
  rw [shape3,checkRows_stream]
  exact streamed3
theorem shape4 : Potential4Expression = (Potential4Constant.getD 0 0,(Potential4Constant.getD 1 0).toNat,indexedTerms PotentialValues Potential4Weights) := by decide +kernel
theorem streamed4 : streamCheck PotentialValues (Potential4Constant.getD 0 0) (Potential4Constant.getD 1 0).toNat Potential4Weights 2317826624568344349435679753111694454 2317826624614654714394947635534406864 = true := by decide +kernel
theorem transferred4 : checkRows PotentialValues [Potential4Expression] [(2317826624568344349435679753111694454,2317826624614654714394947635534406864)] = true := by
  rw [shape4,checkRows_stream]
  exact streamed4
theorem shape5 : Potential5Expression = (Potential5Constant.getD 0 0,(Potential5Constant.getD 1 0).toNat,indexedTerms PotentialValues Potential5Weights) := by decide +kernel
theorem streamed5 : streamCheck PotentialValues (Potential5Constant.getD 0 0) (Potential5Constant.getD 1 0).toNat Potential5Weights 2317826624568370336603657307270257259 2317826624614680737573750516883224185 = true := by decide +kernel
theorem transferred5 : checkRows PotentialValues [Potential5Expression] [(2317826624568370336603657307270257259,2317826624614680737573750516883224185)] = true := by
  rw [shape5,checkRows_stream]
  exact streamed5
theorem shape6 : Potential6Expression = (Potential6Constant.getD 0 0,(Potential6Constant.getD 1 0).toNat,indexedTerms PotentialValues Potential6Weights) := by decide +kernel
theorem streamed6 : streamCheck PotentialValues (Potential6Constant.getD 0 0) (Potential6Constant.getD 1 0).toNat Potential6Weights 2317826624568396323820413285580890136 2317826624614706760801357792641647760 = true := by decide +kernel
theorem transferred6 : checkRows PotentialValues [Potential6Expression] [(2317826624568396323820413285580890136,2317826624614706760801357792641647760)] = true := by
  rw [shape6,checkRows_stream]
  exact streamed6
theorem shape7 : Potential7Expression = (Potential7Constant.getD 0 0,(Potential7Constant.getD 1 0).toNat,indexedTerms PotentialValues Potential7Weights) := by decide +kernel
theorem streamed7 : streamCheck PotentialValues (Potential7Constant.getD 0 0) (Potential7Constant.getD 1 0).toNat Potential7Weights 2317826624568422311085943377902694591 2317826624614732784077765152685530909 = true := by decide +kernel
theorem transferred7 : checkRows PotentialValues [Potential7Expression] [(2317826624568422311085943377902694591,2317826624614732784077765152685530909)] = true := by
  rw [shape7,checkRows_stream]
  exact streamed7
end CatalanCore.Uniform.Decay.Optimization.Pilot
