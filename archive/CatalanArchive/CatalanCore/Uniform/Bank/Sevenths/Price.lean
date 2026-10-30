import CatalanCore.Uniform.Bank.Sevenths.SmallPrimes
import CatalanCore.Uniform.Content.BankShared.LeastPrice
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Sevenths
open CatalanCore CatalanCore.Uniform CatalanCore.Arith.Hybrid
  CatalanCore.Uniform.Content.BankShared

/-- One exponent function for every epsilon-template. Crude clearing proves existence
at every prime, including every exceptional prime. -/
noncomputable def seventhsPrice (a : Fin 6) (depth : ℕ)
    (i : (F7.family (seventhsFrameAt a) depth).ι) (p : ℕ) : ℕ :=
  if hr : i.1 % 2 = 0 then
    if hp : p.Prime then
      @leastGLE p ⟨hp⟩ ((F7.family (seventhsFrameAt a) depth).Q i)
        ⟨Ecrude (cFr (seventhsFrameAt a)) i.1 p,
          @sevenths_gle_Ecrude a depth i hr p ⟨hp⟩⟩
    else 0
  else 0

theorem seventhsPrice_gle (a : Fin 6) (depth : ℕ)
    (i : (F7.family (seventhsFrameAt a) depth).ι) (hr : i.1 % 2 = 0)
    (p : ℕ) [Fact p.Prime] :
    GLE p (seventhsPrice a depth i p) ((F7.family (seventhsFrameAt a) depth).Q i) := by
  unfold seventhsPrice
  rw [dif_pos hr, dif_pos (Fact.out : p.Prime)]
  exact leastGLE_valid _ _ _

theorem seventhsPrice_le (a : Fin 6) (depth : ℕ)
    (i : (F7.family (seventhsFrameAt a) depth).ι) (hr : i.1 % 2 = 0)
    (p e : ℕ) [Fact p.Prime]
    (he : GLE p e ((F7.family (seventhsFrameAt a) depth).Q i)) :
    seventhsPrice a depth i p ≤ e := by
  unfold seventhsPrice
  rw [dif_pos hr, dif_pos (Fact.out : p.Prime)]
  exact leastGLE_le _ _ _ e he

theorem seventhsPrice_crude (a : Fin 6) (depth : ℕ)
    (i : (F7.family (seventhsFrameAt a) depth).ι) (hr : i.1 % 2 = 0)
    (p : ℕ) [Fact p.Prime] :
    seventhsPrice a depth i p ≤ Ecrude (cFr (seventhsFrameAt a)) i.1 p :=
  seventhsPrice_le a depth i hr p _ (sevenths_gle_Ecrude a depth i hr p)

noncomputable def seventhsCut (a : Fin 6) (depth : ℕ)
    (i : (F7.family (seventhsFrameAt a) depth).ι) : ℕ :=
  max (coefficientCut ((F7.family (seventhsFrameAt a) depth).Q i)) (14 * i.1 + 1)

theorem seventhsPrice_zero_ge (a : Fin 6) (depth : ℕ)
    (i : (F7.family (seventhsFrameAt a) depth).ι) (hr : i.1 % 2 = 0)
    (p : ℕ) [Fact p.Prime] (hp : seventhsCut a depth i ≤ p) :
    seventhsPrice a depth i p = 0 := by
  have hc : coefficientCut ((F7.family (seventhsFrameAt a) depth).Q i) ≤ p :=
    (le_max_left _ _).trans hp
  have he := seventhsPrice_le a depth i hr p 0 (gle_zero_of_coefficientCut p _ hc)
  omega

#print axioms seventhsPrice_gle
#print axioms seventhsPrice_crude
end CatalanCore.Uniform.Bank.Sevenths
