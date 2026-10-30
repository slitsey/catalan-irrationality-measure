import CatalanCore.Uniform.Bank.Lambda.PolePalette
import CatalanCore.Uniform.Bank.Chi3Rank.Fibre
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Lambda
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.Hybrid
  CatalanCore.Uniform.Content.RankProducer
open CatalanCore.Uniform.Bank.Chi3Rank (realizes_of)

/-- Once digit membership is classified, the exact q4 palette supplies Realizes.
The remaining shape hypotheses concern finite node sets, not a valuation price. -/
theorem realizes_D4 {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a p B : ℕ) [Fact p.Prime] (hp4 : ¬ p ∣ 4)
    (hc : ∀ j, (D4 a).c j ∈ S p) (hpq : ∀ j, ¬ p ∣ (D4 a).q j)
    (hp3 : 3 ≤ p) (hbd : ∀ j, (D4 a).q j * B + (D4 a).u j ≤ p ^ 2)
    (rows cols : ι → ℕ) (k j x z : ℕ) (hk : k < p)
    (hroot : 4 * k + a = p * j) (hx : x < p)
    (hz : (if k < x then 1 else 0) = z) (c : FibreCert)
    (hrm : ∀ i, rows i % p = x → rows i / p ∈ c.R)
    (hrc : ∀ d ∈ c.R, ∃ i, rows i = x + p * d)
    (hcm : ∀ i, cols i % p = x → cols i / p ∈ c.C)
    (hcc : ∀ d ∈ c.C, ∃ i, cols i = x + p * d)
    (hpr : ∀ d ∈ c.R, c.lf d = poleL j z d ∧ c.ee d = poleE j z d)
    (hpc : ∀ d ∈ c.C, c.lf d = poleL j z d) :
    Realizes ((D4 a).poleSplit B hc hpq hp3 hbd) rows cols (x : ZMod p) c := by
  have node : ∀ n : ℕ, n % p = x → n = x + p * (n / p) := by
    intro n hn
    have h := Nat.mod_add_div n p
    omega
  have hL : ∀ n : ℕ, n % p = x → (D4 a).Lf p n = poleL j z (n / p) := by
    intro n hn
    have h := (D4_pole_node a p hp4 k j x (n / p) hk hroot hx).1
    rw [hz] at h
    conv_lhs => rw [node n hn]
    exact h
  have hE : ∀ n : ℕ, n % p = x → (D4 a).E p n = poleE j z (n / p) := by
    intro n hn
    have h := (D4_pole_node a p hp4 k j x (n / p) hk hroot hx).2
    rw [hz] at h
    conv_lhs => rw [node n hn]
    exact h
  apply realizes_of _ rows cols x hx c hrm hrc hcm hcc
  · intro i hi
    exact (hL _ hi).trans (hpr _ (hrm i hi)).1.symm
  · intro i hi
    exact (hL _ hi).trans (hpc _ (hcm i hi)).symm
  · intro i hi
    exact (hE _ hi).trans (hpr _ (hrm i hi)).2.symm

#print axioms realizes_D4
end CatalanCore.Uniform.Bank.Lambda
