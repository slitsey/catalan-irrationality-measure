import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Lambda.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type a4d7734fb2d441909284d51c52d3372423876d0ed6d6be727fe8f5f737557a43, root class 1. -/
def C1T00 : FibreCert where
  R := {0, 1, 2, 3, 4}
  C := {0, 1, 2, 3, 4, 5}
  lf := fun d => match d with | 0 => 0 | 1 => (-3) | 2 => (-33 / 10) | 3 => (-307 / 90) | 4 => (-8117 / 2340) | 5 => (-139393 / 39780) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-15) | 2 => (-1539 / 100) | 3 => (-125359 / 8100) | 4 => (-84918859 / 5475600) | 5 => (-4913172383 / 316489680) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 0, 5 => (-46828476566365856398527157 / 59214185736403478015585025) | 1, 1 => 1 | 1, 5 => (-7233520676717887784025253 / 47371348589122782412468020) | 2, 2 => 1 | 2, 5 => (-5969017753390856808338189 / 71057022883684173618702030) | 3, 3 => 1 | 3, 5 => (-101573501624923591963547 / 1754494392189732681943260) | 4, 4 => 1 | 4, 5 => (-1489858419882247197752 / 33740276772879474652755) | 5, 5 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 0, 5 => (46828476566365856398527157 / 59214185736403478015585025) | 1, 1 => 1 | 1, 5 => (7233520676717887784025253 / 47371348589122782412468020) | 2, 2 => 1 | 2, 5 => (5969017753390856808338189 / 71057022883684173618702030) | 3, 3 => 1 | 3, 5 => (101573501624923591963547 / 1754494392189732681943260) | 4, 4 => 1 | 4, 5 => (1489858419882247197752 / 33740276772879474652755) | 5, 5 => 1 | _, _ => 0
  kr := ∅
  kc := {5}

theorem C1T00_ok : C1T00.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C1T00_den : ℕ := 710570228836841736187020300
theorem C1T00_den_ok :
    (∀ d ∈ C1T00.R, ∀ e ∈ C1T00.R, (C1T00.Lq d e).den ∣ C1T00_den ∧ (C1T00.Lq' d e).den ∣ C1T00_den) ∧
    (∀ d ∈ C1T00.C, ∀ e ∈ C1T00.C, (C1T00.Pq d e).den ∣ C1T00_den ∧ (C1T00.Pq' d e).den ∣ C1T00_den) := by
  constructor <;> decide +kernel
theorem C1T00_cload_5 : C1T00.cload 5 = ((-23019541031259901542239981 / 177642557209210434046755075), (-88115843712078784229233687 / 36439498914709832624975400)) := by decide +kernel
#print axioms C1T00_ok
#print axioms C1T00_den_ok
end CatalanCore.Uniform.Bank.Lambda.RankData
