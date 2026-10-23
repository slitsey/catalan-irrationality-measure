module
public import CatalanMeasure.Cert.LogApprox
@[expose] public section
/-!
# `cLog` with its series constants as literals

`barrierWeightedComplexLogRat` re-evaluates the series constants `barrierLogHRat 2`,
`barrierAtanJRat (1/2)` and `barrierAtanJRat (1/3)` (66 series terms) at every call.
`cLog1C` uses their literal values (proved in OAI), so `cLog1C = cLog1` and `cLogC = cLog`.
-/
namespace CatalanMeasure.G728
open CatalanMeasure.Cert OAI.InternalCatalan

def cLog1C (c d a b : ℚ) : Option ℚ :=
  match findExp (a * a + b * b), findOct (a, b) with
  | some m, some k =>
    if qabs c ≤ 1 ∧ qabs d ≤ 1 ∧ qabs m ≤ 100 then
      some (c * (((m : ℚ) * (5796068539909855793494541848 / 8361959339180483840538659925) +
          barrierLogHRat ((a * a + b * b) / 2 ^ m)) / 2) -
        d * ((k : ℚ) * (82070093885243869609160349250891 / 177009634670845858814825909452800 +
          112400876852048123008581938124204001832 / 349341672659511491372281601118448876275) +
          barrierAtanJRat ((octRot k (a, b)).2 / (octRot k (a, b)).1)))
    else none
  | _, _ => none

theorem cLog1C_eq : cLog1C = cLog1 := by
  funext c d a b
  unfold cLog1C cLog1 barrierWeightedComplexLogRat barrierScaledLogRat barrierArgApproxRat
  rw [barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]

def cLogC (c d a b : ℚ) : Option ℚ :=
  let n := wPieces c d
  (cLog1C (c / n) (d / n) a b).map (fun q => n * q)

theorem cLogC_eq : cLogC = cLog := by
  funext c d a b
  unfold cLogC cLog
  rw [cLog1C_eq]

end CatalanMeasure.G728
