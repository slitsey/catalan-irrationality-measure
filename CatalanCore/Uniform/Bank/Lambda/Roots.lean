import Mathlib.Tactic
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Lambda

/-- The inverse of an odd residue modulo four is itself. -/
def root4 (a p : ℕ) : ℕ := if p % 4 = 1 then a else 4 - a

def pole4 (a p : ℕ) : ℕ := (root4 a p * p - a) / 4

theorem root4_spec (a p : ℕ) (ha : a = 1 ∨ a = 3) (hp : p % 2 = 1) :
    (root4 a p = 1 ∨ root4 a p = 3) ∧
      4 * pole4 a p + a = p * root4 a p ∧ pole4 a p < p := by
  have h4 : p % 4 = 1 ∨ p % 4 = 3 := by omega
  rcases ha with rfl | rfl <;> rcases h4 with h4 | h4 <;>
    simp only [root4, h4, pole4] <;> norm_num <;> omega

/-- All nodes and shift denominators fit the poleSplit band above a fixed cutoff. -/
theorem q4_band (r m p a : ℕ) (ha : a = 1 ∨ a = 3) (hp : 29 ≤ p)
    (hrp : r ≤ 5 * p) (hm : 10 * m ≤ r + 5) :
    r + 2 * m < p ^ 2 ∧ 4 * (r + 2 * m) + a ≤ p ^ 2 ∧
      1 * (r + 2 * m) + 1 ≤ p ^ 2 := by
  have hB : r + 2 * m ≤ 6 * p + 1 := by omega
  have ha3 : a ≤ 3 := by omega
  have hsq : 24 * p + 7 ≤ p ^ 2 := by nlinarith
  constructor
  · nlinarith
  · constructor <;> nlinarith

#print axioms root4_spec
#print axioms q4_band
end CatalanCore.Uniform.Bank.Lambda
