module

public import CatalanFrames.Lambda.PolyEval
public import CatalanFrames.LambdaMirror.ContentData

/-!
# Mirror content: `HasContent (ofFrame mirFrame) (313/105)` from the shared engine
-/

@[expose] public section

open CatalanCore CatalanCore.Arith

namespace CatalanFrames.LambdaMirror

theorem evalQ_eq (h : ℕ) (r : ℚ) :
    (PolyFamily.ofFrame mirFrame).evalQ h r = CatalanLambda.Mirror.Pbar h r := by
  show (mirFrame.Ppoly h).eval r = _
  rw [← Frame.P_eq_eval, P_eq]

theorem hasContent : HasContent (PolyFamily.ofFrame mirFrame) (313 / 105) := by
  have : NeZero mirGD.M := inferInstanceAs (NeZero 4)
  have hunit : ∀ i, IsUnit (mirGD.res i) := by
    intro i; fin_cases i
    · exact isUnit_one
    · exact (by decide : IsUnit (3 : ZMod 4))
  have e : mirGD.Lam = 313 / 105 := by
    have : mirGD.Lam = 2 * ((Nat.totient 4 : ℕ) : ℝ)⁻¹ * ∑ i : Fin 2, Icont (![4, 4 / 3] i) := rfl
    rw [this, Fin.sum_univ_two]
    have : Nat.totient 4 = 2 := by decide
    norm_num [Icont, this]
  have := hasContent_of_classes mirGD hunit
  rwa [e] at this

end CatalanFrames.LambdaMirror
