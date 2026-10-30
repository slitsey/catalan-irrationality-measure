import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Fifths source type a8a691df4a4455e598067f5415a63bb82e0348f437c6b2a37e8e3a5d1381dd2c, prime class 3 mod 10. -/
def C3T03 : FibreCert where
  R := {0, 1, 2, 3, 4, 5}
  C := {0, 1, 2, 3, 4}
  lf := fun d => match d with | 0 => (-5 / 2) | 1 => (-31 / 14) | 2 => (-179 / 84) | 3 => (-2987 / 1428) | 4 => (-8125 / 3927) | 5 => (-363007 / 176715) | _ => 0
  ee := fun d => match d with | 0 => (-25 / 4) | 1 => (-1129 / 196) | 2 => (-40105 / 7056) | 3 => (-1282241 / 226576) | 4 => (-38713445 / 6853924) | 5 => (-704839727029 / 124912764900) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | 5, 0 => (-992049493866118375332997521049 / 72064323930052840317403301040750) | 5, 1 => (-253611250577501610207801148379 / 41179613674315908752801886309000) | 5, 2 => (-121440130999584647392534042223 / 30884710255736931564601414731750) | 5, 3 => (-1163849865264326333643153477 / 403721702689371654439234179500) | 5, 4 => (-20867722573671194923492536 / 9175493242940264873618958625) | 5, 5 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | 5, 0 => (992049493866118375332997521049 / 72064323930052840317403301040750) | 5, 1 => (253611250577501610207801148379 / 41179613674315908752801886309000) | 5, 2 => (121440130999584647392534042223 / 30884710255736931564601414731750) | 5, 3 => (1163849865264326333643153477 / 403721702689371654439234179500) | 5, 4 => (20867722573671194923492536 / 9175493242940264873618958625) | 5, 5 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | _, _ => 0
  kr := {5}
  kc := ∅

theorem C3T03_ok : C3T03.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C3T03_den : ℕ := 864771887160634083808839612489000
theorem C3T03_den_ok :
    (∀ d ∈ C3T03.R, ∀ e ∈ C3T03.R, (C3T03.Lq d e).den ∣ C3T03_den ∧ (C3T03.Lq' d e).den ∣ C3T03_den) ∧
    (∀ d ∈ C3T03.C, ∀ e ∈ C3T03.C, (C3T03.Pq d e).den ∣ C3T03_den ∧ (C3T03.Pq' d e).den ∣ C3T03_den) := by
  constructor <;> decide +kernel
theorem C3T03_rload_5 : C3T03.rload 5 = ((839681425775605209577675905657547 / 864771887160634083808839612489000), (-572775192000226766425927387784923 / 288257295720211361269613204163000)) := by decide +kernel
#print axioms C3T03_ok
#print axioms C3T03_den_ok
end CatalanCore.Uniform.Bank.FifthsContent.RankData
