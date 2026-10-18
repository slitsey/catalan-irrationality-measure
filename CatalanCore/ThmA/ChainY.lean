module

public import CatalanCore.ThmA.ChainKdet
public import CatalanCore.Linalg.TridiagCyclic

/-!
# Row chains: `Y c̃_a = b̃(a) c̃_{a+1} + T_aa c̃_a + b̃(a-1) c̃_{a-1}`

`ctil F m a = (1/(y+a))_{y=1..m}` (index `y' = y - 1`).  This is (1d) of the algebraic proof,
including the special case `a = 0` (transpose of the `(0,1)` entry).
-/

@[expose] public section

open Finset Matrix

namespace CatalanCore.ThmA

variable {F : Type*} [Field F] {N : ℕ}

/-- `c̃_a = (1/(y+a))_{y=1..m}`, with row `y'` standing for `y = y' + 1`. -/
def ctil (F : Type*) [Field F] (m : ℕ) (a : F) : Fin m → F :=
  fun y => 1 / (((y : ℕ) : F) + 1 + a)

lemma Ymat_mulVec_ctil_raw (K s : ℕ) (a : F) (y : Fin s) :
    (Ymat F K s *ᵥ ctil F s a) y =
      Yd (K : F) (s : F) (((y : ℕ) : F) + 1) * (1 / (((y : ℕ) : F) + 1 + a)) +
      bb (K : F) (s : F) (((y : ℕ) : F) + 1) * (1 / (((y : ℕ) : F) + 1 + 1 + a)) +
      bb (K : F) (s : F) ((y : ℕ) : F) * (1 / (((y : ℕ) : F) + a)) := by
  set Y : F := ((y : ℕ) : F) with hY
  have := tri_sum (n := s) (fun y => bb (K : F) (s : F) ((y : F) + 1))
    (fun y => Yd (K : F) (s : F) ((y : F) + 1)) y (fun j => 1 / ((j : F) + 1 + a))
    (1 / (Y + a)) (bb (K : F) (s : F) Y)
    (fun h => by
      have : (s : F) = Y + 1 := by
        have h' := congrArg (Nat.cast (R := F)) h.symm
        simpa [hY] using h'
      simp only [bb, this]; ring)
    (fun h => by
      have : Y = 0 := by rw [hY, h]; simp
      rw [this, bb_zero])
    (fun h => by
      refine ⟨?_, ?_⟩
      · rw [Nat.cast_sub (by omega)]; simp [hY]
      · rw [Nat.cast_sub (by omega)]; simp [hY])
  simpa [Ymat, ctil, Matrix.mulVec, dotProduct, hY, Nat.cast_add, add_assoc] using this

/-- (1d) as a vector identity, for `a` with no pole. -/
theorem Ymat_mulVec_ctil_apply (K s : ℕ) (a : F) (y : Fin s)
    (h0 : ((y : ℕ) : F) + 1 + a ≠ 0) (h1 : ((y : ℕ) : F) + 1 + 1 + a ≠ 0)
    (h2 : ((y : ℕ) : F) + a ≠ 0) :
    (Ymat F K s *ᵥ ctil F s a) y = (bt (K : F) (s : F) a • ctil F s (a + 1) +
      Td (K : F) (s : F) a • ctil F s a + bt (K : F) (s : F) (a - 1) • ctil F s (a - 1)) y := by
  rw [Ymat_mulVec_ctil_raw]
  have key := bispectral (K : F) (s : F) a (((y : ℕ) : F) + 1)
    (by intro h; apply h0; linear_combination h)
    (by intro h; apply h1; linear_combination h)
    (by intro h; apply h2; linear_combination h)
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, ctil]
  have e1 : ((y : ℕ) : F) + 1 + (a + 1) = a + (((y : ℕ) : F) + 1) + 1 := by ring
  have e2 : ((y : ℕ) : F) + 1 + a = a + (((y : ℕ) : F) + 1) := by ring
  have e3 : ((y : ℕ) : F) + 1 + (a - 1) = a + (((y : ℕ) : F) + 1) - 1 := by ring
  have e4 : ((y : ℕ) : F) + 1 + 1 + a = a + (((y : ℕ) : F) + 1) + 1 := by ring
  have e5 : ((y : ℕ) : F) + a = a + (((y : ℕ) : F) + 1) - 1 := by ring
  rw [e1, e3, e2, e4, e5]
  rw [add_sub_cancel_right] at key
  linear_combination -key

theorem Ymat_mulVec_ctil (K s : ℕ) (a : F)
    (h0 : ∀ y : Fin s, ((y : ℕ) : F) + 1 + a ≠ 0) (h1 : ∀ y : Fin s, ((y : ℕ) : F) + 1 + 1 + a ≠ 0)
    (h2 : ∀ y : Fin s, ((y : ℕ) : F) + a ≠ 0) :
    Ymat F K s *ᵥ ctil F s a = bt (K : F) (s : F) a • ctil F s (a + 1) +
      Td (K : F) (s : F) a • ctil F s a + bt (K : F) (s : F) (a - 1) • ctil F s (a - 1) :=
  funext fun y => Ymat_mulVec_ctil_apply K s a y (h0 y) (h1 y) (h2 y)

/-- The special case `a = 0`: the transpose of the `(0,1)` entry. -/
theorem Ymat_mulVec_ctil_zero (K s : ℕ) (two : (2 : F) ≠ 0)
    (h0 : ∀ y : Fin s, ((y : ℕ) : F) + 1 ≠ 0) (h1 : ∀ y : Fin s, ((y : ℕ) : F) + 1 + 1 ≠ 0)
    (h2 : ∀ y : Fin s, (y : ℕ) ≠ 0 → ((y : ℕ) : F) ≠ 0) :
    Ymat F K s *ᵥ ctil F s 0 = bt (K : F) (s : F) 0 • ctil F s 1 + Td (K : F) (s : F) 0 • ctil F s 0 := by
  ext y
  by_cases hy : (y : ℕ) = 0
  · rw [Ymat_mulVec_ctil_raw]
    have sp := special_entry (K : F) (s : F)
    simp only [hy, Nat.cast_zero, zero_add, add_zero, bb_zero, zero_mul, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, ctil, one_div, inv_one]
    have e : (1 : F) + 1 = 2 := by norm_num
    rw [e]
    field_simp
    linear_combination -sp
  · have := Ymat_mulVec_ctil_apply K s (0 : F) y (by simpa using h0 y) (by simpa using h1 y)
      (by simpa using h2 y hy)
    rw [this]
    simp [bt_neg_one]

lemma bt_nat_ne (h : CharGt F N) (K s j : ℕ) (hj : j + 1 < K) (hK : K ≤ N) (hsj : s + j + 1 ≤ N) :
    bt (K : F) (s : F) (j : F) ≠ 0 := by
  unfold bt
  have e1 : (j : F) + 1 = ((j + 1 : ℕ) : F) := by push_cast; ring
  have e2 : (K : F) - 1 - j = ((K - (j + 1) : ℕ) : F) := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have e3 : (s : F) + j + 1 = ((s + j + 1 : ℕ) : F) := by push_cast; ring
  rw [e1, e2, e3]
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero 2 (h.ne (by omega) (by omega)))
    (h.ne (by omega) (by omega))) (h.ne (by omega) (by omega))

lemma colMat_ctil_det_ne (h : CharGt F N) (s : ℕ) (hN : 2 * s ≤ N) :
    (colMat fun j => ctil F s (j : F)).det ≠ 0 := by
  have := cauchy_det_ne_zero (n := s) (fun i : Fin s => ((i : ℕ) : F) + 1)
    (fun j : Fin s => ((j : ℕ) : F))
    (fun a b hab => Fin.ext (h.inj (by have := a.2; omega) (by have := b.2; omega)
      (by linear_combination hab)))
    (fun a b hab => Fin.ext (h.inj (by have := a.2; omega) (by have := b.2; omega) hab))
    (fun i j => by
      have e : ((i : ℕ) : F) + 1 + ((j : ℕ) : F) = (((i : ℕ) + 1 + (j : ℕ) : ℕ) : F) := by
        push_cast; ring
      have := i.2
      have := j.2
      rw [e]; exact h.ne (by omega) (by omega))
  exact this

theorem kdet_Y_ne (h : CharGt F N) (K s : ℕ) (hs1 : 1 ≤ s) (hsK : s ≤ K) (hK : K ≤ N)
    (hN : 2 * s ≤ N) : kdet (Ymat F K s) (ctil F s 0) ≠ 0 := by
  have two : (2 : F) ≠ 0 := by simpa using h.ne (n := 2) (by omega) (by omega)
  have v0 : ctil F s 0 = ctil F s ((0 : ℕ) : F) := by simp
  rw [v0]
  refine kdet_ne_zero_of_chain (Ymat F K s) (fun j => ctil F s (j : F))
    (fun j => bt (K : F) (s : F) (j : F)) (fun j => Td (K : F) (s : F) (j : F))
    (fun j => bt (K : F) (s : F) ((j : F) - 1)) ?_ ?_ ?_ (colMat_ctil_det_ne h s hN)
  · intro j hj
    rcases j with _ | j
    · simp only [Nat.cast_zero, zero_sub, bt_neg_one, zero_smul, add_zero, zero_add, Nat.cast_one]
      exact Ymat_mulVec_ctil_zero K s two (fun y => by
          have := h.ne (n := (y : ℕ) + 1) (by omega) (by have := y.2; omega); simpa using this)
        (fun y => by
          have := h.ne (n := (y : ℕ) + 1 + 1) (by omega) (by have := y.2; omega); simpa using this)
        (fun y hy => h.ne (by omega) (by have := y.2; omega))
    · have hy : ∀ y : Fin s, (y : ℕ) < s := fun y => y.2
      have e1 : (((j + 1 : ℕ)) : F) + 1 = ((j + 1 + 1 : ℕ) : F) := by push_cast; ring
      rw [Ymat_mulVec_ctil K s (((j + 1 : ℕ)) : F)
        (fun y => by
          have e : ((y : ℕ) : F) + 1 + ((j + 1 : ℕ) : F) = (((y : ℕ) + 1 + (j + 1) : ℕ) : F) := by
            push_cast; ring
          rw [e]; exact h.ne (by omega) (by have := hy y; omega))
        (fun y => by
          have e : ((y : ℕ) : F) + 1 + 1 + ((j + 1 : ℕ) : F) = (((y : ℕ) + 1 + 1 + (j + 1) : ℕ) : F) := by
            push_cast; ring
          rw [e]; exact h.ne (by omega) (by have := hy y; omega))
        (fun y => by
          have e : ((y : ℕ) : F) + ((j + 1 : ℕ) : F) = (((y : ℕ) + (j + 1) : ℕ) : F) := by
            push_cast; ring
          rw [e]; exact h.ne (by omega) (by have := hy y; omega))]
      have e2 : (((j + 1 : ℕ)) : F) - 1 = (j : F) := by push_cast; ring
      simp only [Nat.add_sub_cancel]
      rw [e2, e1]
  · simp [bt_neg_one]
  · intro j hj
    exact bt_nat_ne h K s j (by omega) hK (by omega)

end CatalanCore.ThmA
