module

public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
# The bispectral identity (polynomial level)

Coefficients of the commuting tridiagonal pair `(T, Y)` of the algebraic proof of Theorem A at
`θ = 0`, as polynomials in `a`, `y`, `K`, `s` over a commutative ring, and the identity

`bt(a)/(z+1) + Td(a)/z + bt(a-1)/(z-1) = bb(y)/(z+1) + Yd(y)/z + bb(y-1)/(z-1)`, `z = a + y`.
-/

@[expose] public section

namespace CatalanCore.ThmA

section Ring
variable {R : Type*} [CommRing R]

/-- Off-diagonal of `T`: `b̃(a) = (a+1)² (K-1-a) (s+a+1)`. -/
def bt (K s a : R) : R := (a + 1) ^ 2 * (K - 1 - a) * (s + a + 1)

/-- Off-diagonal of `Y`: `b(y) = y² (y+K) (s-y)`. -/
def bb (K s y : R) : R := y ^ 2 * (y + K) * (s - y)

/-- `δ(a) = -a (2a + s + 2 - K)`. -/
def dl (K s a : R) : R := -a * (2 * a + s + 2 - K)

/-- Diagonal of `T`. -/
def Td (K s a : R) : R := -bt K s a - bt K s (a - 1) + dl K s a

/-- Diagonal of `Y` (at the 1-indexed position `y`). -/
def Yd (K s y : R) : R := -bb K s y - bb K s (y - 1) + dl K s (-y)

lemma bb_eq_bt (K s y : R) : bb K s y = bt K s (-y - 1) := by
  simp only [bb, bt]; ring

lemma bt_neg_one (K s : R) : bt K s (-1) = 0 := by simp [bt]
lemma bb_zero (K s : R) : bb K s 0 = 0 := by simp [bb]

/-- The special entry `(0, 1)`: `b̃(0)/2 + T₀₀ = b(1)/2 + Y₁₁`, cleared of the denominator 2. -/
lemma special_entry (K s : R) :
    bt K s 0 + 2 * Td K s 0 = bb K s 1 + 2 * Yd K s 1 := by
  simp only [Td, Yd, bt, bb, dl]; ring

end Ring

section Field
variable {F : Type*} [Field F]

/-- The bispectral identity. -/
theorem bispectral (K s a y : F) (h0 : a + y ≠ 0) (h1 : a + y + 1 ≠ 0) (h2 : a + y - 1 ≠ 0) :
    bt K s a / (a + y + 1) + Td K s a / (a + y) + bt K s (a - 1) / (a + y - 1) =
      bb K s y / (a + y + 1) + Yd K s y / (a + y) + bb K s (y - 1) / (a + y - 1) := by
  simp only [Td, Yd, bt, bb, dl]
  field_simp
  ring

end Field

end CatalanCore.ThmA
