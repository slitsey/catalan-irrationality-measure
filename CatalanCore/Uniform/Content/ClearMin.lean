module
public import CatalanCore.Arith.Hybrid.Tropical
@[expose] public section

namespace CatalanCore.Uniform.Content

/-- A minimum selects one of two already certified prices; no valuation law is needed. -/
theorem clear_min {α : Type*} [LinearOrder α] (P : α → Prop) {a b : α}
    (ha : P a) (hb : P b) : P (min a b) := by
  rcases le_total a b with h | h
  · simpa only [min_eq_left h] using ha
  · simpa only [min_eq_right h] using hb

/-- Pointwise minimum of any two valid coefficientwise p-integrality prices. -/
theorem gle_min {p : Nat} [Fact p.Prime] {a b : Nat} {f : Polynomial Rat}
    (ha : CatalanCore.Arith.Hybrid.GLE p a f)
    (hb : CatalanCore.Arith.Hybrid.GLE p b f) :
    CatalanCore.Arith.Hybrid.GLE p (min a b) f :=
  clear_min (fun e => CatalanCore.Arith.Hybrid.GLE p e f) ha hb

#print axioms gle_min
end CatalanCore.Uniform.Content