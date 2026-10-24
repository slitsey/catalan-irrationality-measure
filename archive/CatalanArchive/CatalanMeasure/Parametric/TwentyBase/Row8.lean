module
public import CatalanArchive.CatalanMeasure.Parametric.TwentyBase.Data
@[expose] public section
namespace CatalanMeasure.Parametric.TwentyBase
set_option maxRecDepth 8000
set_option maxHeartbeats 4000000

theorem actual_base_row8 (k : Fin 20) :
    baseFilteredContraction twenty 1009 8 k=literalBaseEntry 8 k :=by
  unfold baseFilteredContraction baseRawContraction
  simp_rw [rowP_coeff_algorithm,rowD_coeff_algorithm]
  fin_cases k <;> decide +kernel

end CatalanMeasure.Parametric.TwentyBase
