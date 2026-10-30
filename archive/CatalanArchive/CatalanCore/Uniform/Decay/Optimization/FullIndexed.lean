import CatalanCore.Uniform.Decay.Optimization.FullData
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 1
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace CatalanCore.Uniform.Decay.Optimization.Pilot
open CatalanCore.Uniform.Decay.SignedPilot
theorem indexed0 : checkRows PotentialValues [Potential0Expression] [(2317826624568240401251639979480757054,2317826624614550622167866255382777902)] = true := by decide +kernel
theorem indexed1 : checkRows PotentialValues [Potential1Expression] [(2317826624568266388224460736385118027,2317826624614576645151408458614766269)] = true := by decide +kernel
theorem indexed2 : checkRows PotentialValues [Potential2Expression] [(2317826624568292375246077157623609350,2317826624614602668183772296371414178)] = true := by decide +kernel
theorem indexed3 : checkRows PotentialValues [Potential3Expression] [(2317826624568318362316484933207947626,2317826624614628691264953458681189928)] = true := by decide +kernel
theorem indexed4 : checkRows PotentialValues [Potential4Expression] [(2317826624568344349435679753111694454,2317826624614654714394947635534406864)] = true := by decide +kernel
theorem indexed5 : checkRows PotentialValues [Potential5Expression] [(2317826624568370336603657307270257259,2317826624614680737573750516883224185)] = true := by decide +kernel
theorem indexed6 : checkRows PotentialValues [Potential6Expression] [(2317826624568396323820413285580890136,2317826624614706760801357792641647760)] = true := by decide +kernel
theorem indexed7 : checkRows PotentialValues [Potential7Expression] [(2317826624568422311085943377902694591,2317826624614732784077765152685530909)] = true := by decide +kernel
end CatalanCore.Uniform.Decay.Optimization.Pilot
