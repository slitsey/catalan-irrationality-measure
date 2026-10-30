import CatalanCore.Uniform.Decay.Breakpoint.GenBp
set_option Elab.async false
set_option maxRecDepth 100000

namespace CatalanCore.Uniform.Decay.Breakpoint.GenBp
open CatalanCore.Uniform.Bank.Chi3

#eval (List.range 8).map fun i => ((bps edgesLit[i]!).map fl, (bps edgesLit[i]!).map litQ)
-- probe at a fixed small L first
#eval report 0 0 false 8 (rb (1 / 20000))
#eval report 0 (8000 / 8499) false 8 (rb (1 / 200))
#eval report 0 (8000 / 8499) true 8 (rb (1 / 200))

end CatalanCore.Uniform.Decay.Breakpoint.GenBp
