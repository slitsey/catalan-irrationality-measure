import CatalanCore.Uniform.Bank.Lambda.Realize
import CatalanCore.Uniform.Bank.Lambda.DigitShape
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Lambda
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.Hybrid
  CatalanCore.Uniform.Content.RankProducer
open CatalanCore.Uniform.Bank.Chi3Rank

/-- A source-cell shape and exact palette realize an actual common-deletion
member, provided the fibre is untouched by the common-node deletion. -/
theorem realizes_commonMinor_D4 (a p B : ℕ) [Fact p.Prime] (hp4 : ¬ p ∣ 4)
    (hc : ∀ j, (D4 a).c j ∈ S p) (hpq : ∀ j, ¬ p ∣ (D4 a).q j)
    (hp3 : 3 ≤ p) (hbd : ∀ j, (D4 a).q j * B + (D4 a).u j ≤ p ^ 2)
    (r m : ℕ) (s : Finset (Fin r)) (k j x z : ℕ) (hk : k < p)
    (hroot : 4 * k + a = p * j) (hx : x < p)
    (hz : (if k < x then 1 else 0) = z) (c : FibreCert)
    (hrows : ∀ d, rowDigit r m p x d ↔ d ∈ c.R)
    (hcols : ∀ d, colDigit r m p x d ↔ d ∈ c.C)
    (hkeep : ∀ d : ℕ, x + p * d < r → keptN r s (x + p * d))
    (hpr : ∀ d ∈ c.R, c.lf d = poleL j z d ∧ c.ee d = poleE j z d)
    (hpc : ∀ d ∈ c.C, c.lf d = poleL j z d) :
    Realizes ((D4 a).poleSplit B hc hpq hp3 hbd)
      (rowsOf r m s) (colsOf r m s) (x : ZMod p) c := by
  have node : ∀ n : ℕ, n % p = x → n = x + p * (n / p) := by
    intro n hn
    have h := Nat.mod_add_div n p
    omega
  apply realizes_D4 a p B hp4 hc hpq hp3 hbd (rowsOf r m s) (colsOf r m s)
    k j x z hk hroot hx hz c
  · intro i hi
    apply (hrows _).1
    have hn := (rowN_iff r m s _).1 ⟨i, rfl⟩
    unfold rowDigit
    rw [← node _ hi]
    rcases hn with hn | hn
    · exact Or.inl hn.1
    · exact Or.inr hn
  · intro d hd
    have hn := (hrows d).2 hd
    rcases hn with hn | hn
    · exact (rowN_iff r m s _).2 (Or.inl (hkeep d hn))
    · exact (rowN_iff r m s _).2 (Or.inr hn)
  · intro i hi
    apply (hcols _).1
    have hn := (colN_iff r m s _).1 ⟨i, rfl⟩
    unfold colDigit
    rw [← node _ hi]
    rcases hn with hn | ⟨h1, h2, h3⟩
    · exact Or.inl hn.1
    · right
      omega
  · intro d hd
    have hn := (hcols d).2 hd
    rcases hn with hn | ⟨h1, h2, h3⟩
    · exact (colN_iff r m s _).2 (Or.inl (hkeep d hn))
    · apply (colN_iff r m s _).2
      right
      omega
  · exact hpr
  · exact hpc

#print axioms realizes_commonMinor_D4
end CatalanCore.Uniform.Bank.Lambda
