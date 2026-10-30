import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type a6720ba874a7e6e3750337721fca211bdfe89a8601ffc196c6c07dbafaf48dde, root class 13. -/
def C13T09 : FibreCert where
  R := {0, 1, 2, 3, 4, 5}
  C := {0, 1, 2, 3, 4}
  lf := fun d => match d with | 0 => 0 | 1 => (-1 / 6) | 2 => (-8 / 39) | 3 => (-173 / 780) | 4 => (-811 / 3510) | 5 => (-7069 / 29835) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-13 / 36) | 2 => (-610 / 1521) | 3 => (-27881 / 67600) | 4 => (-2569703 / 6160050) | 5 => (-1493789203 / 3560508900) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | 5, 0 => (-1664926881425183059 / 3919001265838381125) | 5, 1 => (-5253693803082904157 / 31352010126707049000) | 5, 2 => (-373531339781667851 / 3617539630004659500) | 5, 3 => (-5987069775334443 / 80389769555659100) | 5, 4 => (-1169848400143098 / 20097442388914775) | 5, 5 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | 5, 0 => (1664926881425183059 / 3919001265838381125) | 5, 1 => (5253693803082904157 / 31352010126707049000) | 5, 2 => (373531339781667851 / 3617539630004659500) | 5, 3 => (5987069775334443 / 80389769555659100) | 5, 4 => (1169848400143098 / 20097442388914775) | 5, 5 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | _, _ => 0
  kr := {5}
  kc := ∅

theorem C13T09_ok : C13T09.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C13T09_den : ℕ := 94056030380121147000
theorem C13T09_den_ok :
    (∀ d ∈ C13T09.R, ∀ e ∈ C13T09.R, (C13T09.Lq d e).den ∣ C13T09_den ∧ (C13T09.Lq' d e).den ∣ C13T09_den) ∧
    (∀ d ∈ C13T09.C, ∀ e ∈ C13T09.C, (C13T09.Pq d e).den ∣ C13T09_den ∧ (C13T09.Pq' d e).den ∣ C13T09_den) := by
  constructor <;> decide +kernel
theorem C13T09_rload_5 : C13T09.rload 5 = ((16145126832533680037 / 94056030380121147000), (-380708984950188733 / 2411693086669773000)) := by decide +kernel
#print axioms C13T09_ok
#print axioms C13T09_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
