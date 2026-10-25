module

public import CatalanCore.Cert.SigmaThirds.IBoundDef

@[expose] public section

/-! Exact assembly of individually checked triangular energy rows.
The list algebra is proved over an abstract function, so simplification never
traverses the closed witness or its energy functions.
-/
namespace CatalanCore.Cert.SigmaThirds

/-- Abstract list algebra: no numerical witness occurs in this proof. -/
theorem energy_sum_range_succ (f : ℕ → ℤ) (n : ℕ) :
    ((List.range (n + 1)).map f).sum = ((List.range n).map f).sum + f n := by
  simp only [List.range_succ, List.map_append, List.sum_append,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]

/-- Abstract equality assembly, kept separate from closed energy expressions. -/
theorem energy_add_eq_add (x y v w : ℤ) (hx : x = v) (hy : y = w) :
    x + y = v + w := by
  cases hx
  cases hy
  rfl

/-- The empty range contributes zero. -/
theorem rowsSum_zero (a : ℕ) : rowsSum a 0 = 0 := by rfl

/-- Instantiate abstract list algebra without simplifying the closed witness. -/
theorem rowsSum_succ (a n : ℕ) :
    rowsSum a (n + 1) = rowsSum a n + rowT sigH (a + n) :=
  energy_sum_range_succ (fun i => rowT sigH (a + i)) n

/-- A checked prefix and one checked row give the next checked prefix. -/
theorem rowsSum_step (a n : ℕ) (v w : ℤ)
    (hv : rowsSum a n = v) (hw : rowT sigH (a + n) = w) :
    rowsSum a (n + 1) = v + w :=
  (rowsSum_succ a n).trans
    (energy_add_eq_add (rowsSum a n) (rowT sigH (a + n)) v w hv hw)

end CatalanCore.Cert.SigmaThirds

#print axioms CatalanCore.Cert.SigmaThirds.rowsSum_step