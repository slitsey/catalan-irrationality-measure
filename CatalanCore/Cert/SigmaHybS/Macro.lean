module

public import CatalanCore.Cert.SigmaHybS.Taylor

@[expose] public section

/-!
# Packed macro data (generic helpers)

Data format (`P` a packed `Nat`, 64-bit slots biased by `2^62`): see `HMacro`.  `slot` unpacks one slot.
-/

namespace CatalanCore.Cert.SigmaHybS

def slot (P i : ℕ) : ℤ := (((P >>> (64 * i)) % 2 ^ 64 : ℕ) : ℤ) - 2 ^ 62

/-- ray cell `c` of macro `j` (macro stride `4 + 4M`): `xlo xhi ylo yhi` in units `2^-40`. -/
def cellBox (M P j c : ℕ) : ℤ × ℤ × ℤ × ℤ :=
  let a := j * (4 + 4 * M) + 4 + 4 * c
  (slot P a, slot P (a + 1), slot P (a + 2), slot P (a + 3))

lemma split_eq {α : Type _} (l : List α) (i0 i1 : ℕ) (h : i0 ≤ i1) :
    l.take i0 ++ (l.drop i0).take (i1 - i0) ++ l.drop i1 = l := by
  have h1 : (l.drop i0).take (i1 - i0) ++ (l.drop i0).drop (i1 - i0) = l.drop i0 := List.take_append_drop _ _
  have h2 : (l.drop i0).drop (i1 - i0) = l.drop i1 := by
    rw [List.drop_drop]; congr 1; omega
  rw [h2] at h1
  rw [List.append_assoc, h1, List.take_append_drop]

/-- assemble chunked theorems `∀ k < ch, ∀ j<4, ok (4k+j)` into `∀ j < 4*ch, ok j`. -/
theorem chunks_all (f : ℕ → Bool) (ch : ℕ)
    (hc : ∀ k < ch, (List.range 4).all (fun j => f (4 * k + j)) = true) :
    ∀ j < 4 * ch, f j = true := by
  intro j hj
  have h := hc (j / 4) (by omega)
  have := List.all_eq_true.mp h (j % 4) (List.mem_range.mpr (by omega))
  have e : 4 * (j / 4) + j % 4 = j := by omega
  rwa [e] at this

end CatalanCore.Cert.SigmaHybS
