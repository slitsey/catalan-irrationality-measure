module
public import CatalanMeasure.Parametric.TwentyParameters
public import CatalanMeasure.Parametric.GoodPrimes
public import CatalanMeasure.Parametric.IntegerRows
@[expose] public section
namespace CatalanMeasure.Parametric.TwentyBase
open OAI.InternalCatalan
set_option maxRecDepth 8000
set_option maxHeartbeats 2000000
instance certificatePrime : Fact (Nat.Prime 1009) :=⟨by decide⟩

def literalRowZero (k : Fin 20) : ZMod 1009 :=
  match k.val with
  | 0 => 36
  | 1 => 365
  | 2 => 194
  | 3 => 491
  | 4 => 143
  | 5 => 657
  | 6 => 171
  | 7 => 718
  | 8 => 802
  | 9 => 150
  | 10 => 625
  | 11 => 886
  | 12 => 268
  | 13 => 207
  | 14 => 317
  | 15 => 240
  | 16 => 367
  | 17 => 764
  | 18 => 809
  | 19 => 590
  | _ => 0

theorem actual_base_row_zero (k : Fin 20) :
    baseFilteredContraction twenty 1009 0 k=literalRowZero k :=by
  unfold baseFilteredContraction baseRawContraction
  simp_rw [rowP_coeff_algorithm,rowD_coeff_algorithm]
  fin_cases k <;> decide +kernel

end CatalanMeasure.Parametric.TwentyBase
