import CatalanCore.Uniform.Content.RankProducer.Cert
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Lambda

/-- Full alternating row/column membership, expressed in residue-digit coordinates. -/
def rowDigit (r m p x d : ℕ) : Prop :=
  x + p * d < r ∨
    (r ≤ x + p * d ∧ x + p * d < r + 2 * m ∧ (x + p * d - r) % 2 = 0)
def colDigit (r m p x d : ℕ) : Prop :=
  x + p * d < r ∨
    (r ≤ x + p * d ∧ x + p * d < r + 2 * m ∧ (x + p * d - r) % 2 = 1)

theorem rowDigit_lt_six {r m p x d : ℕ} (hround : 10 * m ≤ r + 5)
    (hrp : r ≤ 5 * p) (hx : 4 ≤ x) (h : rowDigit r m p x d) : d < 6 := by
  have hn : x + p * d < r + 2 * m := by
    rcases h with h | ⟨_, h, _⟩ <;> omega
  by_contra hd
  have hm : 6 * p ≤ p * d := by
    simpa [Nat.mul_comm] using Nat.mul_le_mul_left p (show 6 ≤ d by omega)
  omega

theorem colDigit_lt_six {r m p x d : ℕ} (hround : 10 * m ≤ r + 5)
    (hrp : r ≤ 5 * p) (hx : 4 ≤ x) (h : colDigit r m p x d) : d < 6 := by
  have hn : x + p * d < r + 2 * m := by
    rcases h with h | ⟨_, h, _⟩ <;> omega
  by_contra hd
  have hm : 6 * p ≤ p * d := by
    simpa [Nat.mul_comm] using Nat.mul_le_mul_left p (show 6 ≤ d by omega)
  omega
end CatalanCore.Uniform.Bank.Lambda
