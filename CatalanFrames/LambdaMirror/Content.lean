module

public import CatalanFrames.LambdaMirror.Frame
public import CatalanLambda.Mirror.Integrality
public import CatalanLambda.Mirror.GrowthFinal

/-!
# Mirror content: `HasContent (ofFrame mirFrame) (313/105)` from the legacy mirror integrality
-/

@[expose] public section

open CatalanCore

namespace CatalanFrames.LambdaMirror

theorem evalQ_eq (h : ℕ) (r : ℚ) :
    (PolyFamily.ofFrame mirFrame).evalQ h r = CatalanLambda.Mirror.Pbar h r := by
  show (mirFrame.Ppoly h).eval r = _
  rw [← Frame.P_eq_eval, P_eq]

theorem hasContent : HasContent (PolyFamily.ofFrame mirFrame) (313 / 105) := by
  refine ⟨CatalanLambda.Mirror.Dden, CatalanLambda.Mirror.Dden_pos, ?_, ?_⟩
  · intro (n : ℕ) _ p q hq
    obtain ⟨z, hz⟩ := CatalanLambda.Mirror.integrality n p q hq
    refine ⟨z, ?_⟩
    show (q : ℚ) ^ n * (CatalanLambda.Mirror.Dden n : ℚ) * (PolyFamily.ofFrame mirFrame).evalQ n _ = z
    rw [evalQ_eq]; exact hz
  · intro ε hε
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (CatalanLambda.Mirror.log_Dden_le_eventually hε)
    exact ⟨N, fun (n : ℕ) _ hn => hN n hn⟩

end CatalanFrames.LambdaMirror
