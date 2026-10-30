import CatalanCore.Uniform.Bank.Sevenths.Geom
import CatalanCore.Uniform.Bank.Sevenths.TwoTerm
import CatalanCore.Uniform.Content.UFSimple.Closed
set_option Elab.async false

namespace CatalanCore.Uniform.Bank.Sevenths
open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Content.Member
  CatalanCore.Uniform.Content.UFSimple

/-- The complete pointwise closed-UF validity region. Small and exceptional primes
are handled separately by the content assembler. -/
def seventhsUFValid (a : Fin 6) (ρ : ℕ → ℕ) (r p : ℕ) : Prop :=
  ∃ hp : Fact p.Prime,
    @ClosedHyp (1 / 6) one_sixth_pos (seventhsFrameAt a) 7
      (7 - seventhNumerator a) r p (ρ p) hp

/-- The generic closed UF supplier on precisely the sevenths family, with debit one.
It includes the top extension and all outside-window kills. -/
noncomputable def seventhsUFLayer (a : Fin 6) (depth : ℕ) (ρ : ℕ → ℕ) :
    DebitLayer F7 (seventhsFrameAt a) depth :=
  ufClosedLayer (c := 1 / 6) (hc := one_sixth_pos) (sevenths_twoTerm a)
    (seventhsUFValid a ρ) ρ (fun _ _ _ h => by obtain ⟨_, H⟩ := h; exact H)

theorem seventhsUFLayer_base (a : Fin 6) (depth : ℕ) (ρ : ℕ → ℕ) :
    (seventhsUFLayer a depth ρ).base =
      fun r p => closedPrice (F7.borderSize r) r p (ρ p) := rfl

#print axioms seventhsUFLayer
end CatalanCore.Uniform.Bank.Sevenths
