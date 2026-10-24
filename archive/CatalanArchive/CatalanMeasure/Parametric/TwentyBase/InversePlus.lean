module
public import CatalanArchive.CatalanMeasure.Parametric.TwentyBase.InverseData
@[expose] public section
namespace CatalanMeasure.Parametric.TwentyBase
open Matrix
set_option maxRecDepth 10000
set_option maxHeartbeats 6000000

theorem inversePlus_checked : (literalCaseMatrix (1))*inversePlus=1 :=by
  ext r k
  simp only [Matrix.mul_apply,Matrix.one_apply]
  fin_cases r <;> fin_cases k <;> decide +kernel

end CatalanMeasure.Parametric.TwentyBase
