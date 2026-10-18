module

public import CatalanFrames.Lambda.PolyEval
public import CatalanLambda.Integrality
public import CatalanLambda.GrowthFinal

/-!
# λ content: `HasContent (ofFrame lamFrame) (313/105)` from the legacy integrality and growth
-/

@[expose] public section

open CatalanCore

namespace CatalanFrames.Lambda

theorem evalQ_eq (h : ℕ) (r : ℚ) :
    (PolyFamily.ofFrame lamFrame).evalQ h r = CatalanLambda.P h r := by
  show (lamFrame.Ppoly h).eval r = _
  rw [← Frame.P_eq_eval, P_eq]

theorem hasContent : HasContent (PolyFamily.ofFrame lamFrame) (313 / 105) := by
  refine ⟨CatalanLambda.Dden, CatalanLambda.Dden_pos, ?_, ?_⟩
  · intro (n : ℕ) _ p q hq
    obtain ⟨z, hz⟩ := CatalanLambda.integrality n p q hq
    refine ⟨z, ?_⟩
    show (q : ℚ) ^ n * (CatalanLambda.Dden n : ℚ) * (PolyFamily.ofFrame lamFrame).evalQ n _ = z
    rw [evalQ_eq]; exact hz
  · intro ε hε
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (CatalanLambda.log_Dden_le_eventually hε)
    exact ⟨N, fun (n : ℕ) _ hn => hN n hn⟩

end CatalanFrames.Lambda
