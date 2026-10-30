import CatalanCore.Uniform.Bank.Sevenths.PoleData
import CatalanCore.Uniform.Content.BankShared.PoleTropical
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Sevenths
open CatalanCore CatalanCore.Arith.Hybrid CatalanCore.Arith.Hybrid.Periodic
  CatalanCore.Uniform.Content.Smith CatalanCore.Uniform.Content.BankShared

theorem sevenths_poleLevels_low (a : Fin 6) (p N : ℕ) [Fact p.Prime]
    (hp8 : 8 ≤ p) (hN : 7 * N ≤ p * p) (c : ℕ) :
    poleLevels (sevenths_poleData_of_eight a p N hp8 hN) p c = 0 ↔ c < seventhRho a p := by
  let D := sevenths_poleData_of_eight a p N hp8 hN
  have hb := seventhRho_bounds a p hp8
  obtain ⟨j, hj0, hj6, he⟩ := seventhRho_root a p hp8
  have hs : TTSing p 7 (7 - seventhNumerator a) (p + seventhRho a p) (seventhRho a p) j :=
    ⟨by omega, he, hb.1, hb.2, hj0, le_rfl⟩
  apply poleLevels_zero_iff D (seventhRho a p) hb.1
  · change ttSing p 7 (7 - seventhNumerator a) (seventhRho a p : ℤ)
    rw [ttSing_nat (sevenths_twoTerm a) hb.1]
    exact Or.inr (seventhRho_dvd a p hp8)
  · intro t ht htk
    change ¬ ttSing p 7 (7 - seventhNumerator a) (t : ℤ)
    rw [hs.sing_iff (sevenths_twoTerm a) ht (by omega)]
    omega

#print axioms sevenths_poleLevels_low
end CatalanCore.Uniform.Bank.Sevenths
