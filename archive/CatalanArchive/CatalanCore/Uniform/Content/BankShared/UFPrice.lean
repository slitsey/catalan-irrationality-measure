import CatalanCore.Uniform.Content.UFSimple.Closed
set_option Elab.async false
namespace CatalanCore.Uniform.Content.BankShared
open CatalanCore.Uniform.Content.UFSimple

theorem closedPrice_le_cand (m r p ρ : ℕ) (κ ζ : Bool) :
    closedPrice m r p ρ ≤ candPrice m r p ρ κ ζ := by
  cases κ <;> cases ζ
  · exact (min_le_left _ _).trans (min_le_left _ _)
  · exact (min_le_left _ _).trans (min_le_right _ _)
  · exact (min_le_right _ _).trans (min_le_left _ _)
  · exact (min_le_right _ _).trans (min_le_right _ _)

#print axioms closedPrice_le_cand
end CatalanCore.Uniform.Content.BankShared
