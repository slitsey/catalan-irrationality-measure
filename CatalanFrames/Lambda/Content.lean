module

public import CatalanFrames.Lambda.PolyEval
public import CatalanFrames.Lambda.ContentData

/-!
# λ content: `HasContent (ofFrame lamFrame) (313/105)` from the shared engine
-/

@[expose] public section

open CatalanCore CatalanCore.Arith

namespace CatalanFrames.Lambda

theorem evalQ_eq (h : ℕ) (r : ℚ) :
    (PolyFamily.ofFrame lamFrame).evalQ h r = CatalanLambda.P h r := by
  show (lamFrame.Ppoly h).eval r = _
  rw [← Frame.P_eq_eval, P_eq]

theorem hasContent : HasContent (PolyFamily.ofFrame lamFrame) (313 / 105) := by
  have : NeZero lamGD.M := inferInstanceAs (NeZero 4)
  have hunit : ∀ i, IsUnit (lamGD.res i) := by
    intro i; fin_cases i
    · exact (by decide : IsUnit (3 : ZMod 4))
    · exact isUnit_one
  have e : lamGD.Lam = 313 / 105 := by
    have : lamGD.Lam = 2 * ((Nat.totient 4 : ℕ) : ℝ)⁻¹ * ∑ i : Fin 2, Icont (![4, 4 / 3] i) := rfl
    rw [this, Fin.sum_univ_two]
    have : Nat.totient 4 = 2 := by decide
    norm_num [Icont, this]
  have := hasContent_of_classes lamGD hunit
  rwa [e] at this

end CatalanFrames.Lambda
