import CatalanCore.Uniform.Content.BankShared.UFPrice
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace CatalanCore.Uniform.Bank.Sevenths.UFPrice
open CatalanCore.Uniform.Content.UFSimple CatalanCore.Uniform.Content.BankShared

theorem C1P26 (r m p ρ o : ℕ) (hp : 64 ≤ p) (hrp : r ≤ 6 * p)
    (hm1 : 12 * m ≤ r + 6) (hm2 : r ≤ 12 * m + 6)
    (hρ1 : 1 ≤ ρ) (hρp : ρ < p) (ho1 : 1 ≤ o) (ho6 : o ≤ 6)
    (hroot : 7 * ρ = 1 * p + o)
    (hleft : 1 * r ≤ 6 * p)
    (hright : 516 * p ≤ 91 * r) :
    (84 : ℤ) * (closedPrice m r p ρ : ℤ) ≤ -7 * (r : ℤ) + 1032 * (p : ℤ) + 84000 := by
  have hbound : r / p ≤ 6 := Nat.div_le_of_le_mul (by omega)
  have hd := Nat.div_add_mod r p
  have hrem := Nat.mod_lt r (by omega : 0 < p)
  have hc := closedPrice_le_cand m r p ρ true true
  have hci : (closedPrice m r p ρ : ℤ) ≤ (candPrice m r p ρ true true : ℤ) := by exact_mod_cast hc
  have hprice : (84 : ℤ) * (candPrice m r p ρ true true : ℤ) ≤
      -7 * (r : ℤ) + 1032 * (p : ℤ) + 84000 := by
    generalize hh : r / p = h at *
    interval_cases h <;>
      simp only [candPrice, CandOK, candB, candL, candU, candUb, hh,
        Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte, Nat.mul_zero, Nat.zero_mul,
        zero_add, add_zero, mul_one] <;>
      unfold closedBound beta3 ovl <;> omega
  linarith
#print axioms C1P26
end CatalanCore.Uniform.Bank.Sevenths.UFPrice
