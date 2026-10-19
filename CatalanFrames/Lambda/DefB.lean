module

public import CatalanFrames.Lambda.Frame
public import CatalanCore.Arith.Hybrid.DefBFinal

@[expose] public section

/-!
# Theorem B for λ (thin instance)

`lamFrame` satisfies `LamData`; hence `gleAt_B_lam` / `defAt_B_lam` apply to `lamFrame`.
-/

open CatalanCore CatalanCore.Arith.Hybrid

namespace CatalanFrames.Lambda

theorem lamData : LamData lamFrame 1 where
  norm_eq := rfl
  o_pos := by norm_num
  o_le := by norm_num
  delta_eq := by
    intro t ht
    rw [Delta_eq t ht]
    push_cast
    obtain ⟨h1, h2, _⟩ := one_le_ne ht
    field_simp
    ring
  dsq_eq := by
    intro t ht
    push_cast
    exact Dsq_eq t ht

end CatalanFrames.Lambda
