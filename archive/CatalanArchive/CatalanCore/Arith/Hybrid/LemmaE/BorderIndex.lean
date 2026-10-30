module
public import CatalanCore.Rect.BorderFull
@[expose] public section
namespace CatalanCore.Arith.Hybrid
/-- `Fin r ⊕ Option (Fin m) ≃ Option (Fin r ⊕ Fin m)` (the border is `none`). -/
def borderEquiv (r m : ℕ) : Fin r ⊕ Option (Fin m) ≃ Option (Fin r ⊕ Fin m) where
  toFun
    | Sum.inl c => some (Sum.inl c)
    | Sum.inr none => none
    | Sum.inr (some j) => some (Sum.inr j)
  invFun
    | none => Sum.inr none
    | some (Sum.inl c) => Sum.inl c
    | some (Sum.inr j) => Sum.inr (some j)
  left_inv := by rintro (_ | _ | _) <;> rfl
  right_inv := by rintro (_ | _ | _) <;> rfl


end CatalanCore.Arith.Hybrid
