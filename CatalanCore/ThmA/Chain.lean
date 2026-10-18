module

public import CatalanCore.ThmA.Intertwine

/-!
# Column chains: `T c_y = b(y) c_{y+1} + Y_yy c_y + b(y-1) c_{y-1}`

`cvec F K y = (1/(a+y))_{a<K}` for `y : F`.  This is (1c) of the algebraic proof.
-/

@[expose] public section

open Finset Matrix

namespace CatalanCore.ThmA

variable {F : Type*} [Field F]

/-- `c_y = (1/(a+y))_{a<K}`. -/
def cvec (F : Type*) [Field F] (K : ℕ) (y : F) : Fin K → F := fun a => 1 / (((a : ℕ) : F) + y)

lemma Tmat_mulVec_cvec_raw (K s : ℕ) (y : F) (a : Fin K) :
    (Tmat F K s *ᵥ cvec F K y) a =
      Td (K : F) (s : F) ((a : ℕ) : F) * (1 / (((a : ℕ) : F) + y)) +
      bt (K : F) (s : F) ((a : ℕ) : F) * (1 / (((a : ℕ) : F) + 1 + y)) +
      bt (K : F) (s : F) (((a : ℕ) : F) - 1) * (1 / (((a : ℕ) : F) - 1 + y)) := by
  set A : F := ((a : ℕ) : F) with hA
  have := tri_sum (n := K) (fun a => bt (K : F) (s : F) (a : F)) (fun a => Td (K : F) (s : F) (a : F))
    a (fun j => 1 / ((j : F) + y)) (1 / (A - 1 + y)) (bt (K : F) (s : F) (A - 1))
    (fun h => by
      have : (K : F) = A + 1 := by
        have h' := congrArg (Nat.cast (R := F)) h.symm
        simpa [hA] using h'
      simp only [bt, this]; ring)
    (fun h => by
      have : A = 0 := by rw [hA, h]; simp
      rw [this, zero_sub, bt_neg_one])
    (fun h => by
      refine ⟨?_, ?_⟩
      · rw [Nat.cast_sub (by omega)]; simp [hA]
      · rw [Nat.cast_sub (by omega)]; simp [hA])
  simpa [Tmat, cvec, Matrix.mulVec, dotProduct, hA, Nat.cast_add, add_assoc] using this

/-- (1c) as a vector identity. -/
theorem Tmat_mulVec_cvec (K s : ℕ) (y : F)
    (h0 : ∀ a : Fin K, ((a : ℕ) : F) + y ≠ 0) (h1 : ∀ a : Fin K, ((a : ℕ) : F) + y + 1 ≠ 0)
    (h2 : ∀ a : Fin K, ((a : ℕ) : F) + y - 1 ≠ 0) :
    Tmat F K s *ᵥ cvec F K y = bb (K : F) (s : F) y • cvec F K (y + 1) +
      Yd (K : F) (s : F) y • cvec F K y + bb (K : F) (s : F) (y - 1) • cvec F K (y - 1) := by
  ext a
  rw [Tmat_mulVec_cvec_raw]
  have key := bispectral (K : F) (s : F) ((a : ℕ) : F) y (h0 a) (h1 a) (h2 a)
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, cvec]
  have e1 : ((a : ℕ) : F) + 1 + y = ((a : ℕ) : F) + y + 1 := by ring
  have e2 : ((a : ℕ) : F) - 1 + y = ((a : ℕ) : F) + y - 1 := by ring
  have e3 : ((a : ℕ) : F) + (y + 1) = ((a : ℕ) : F) + y + 1 := by ring
  have e4 : ((a : ℕ) : F) + (y - 1) = ((a : ℕ) : F) + y - 1 := by ring
  rw [e1, e2, e3, e4]
  linear_combination key

end CatalanCore.ThmA
