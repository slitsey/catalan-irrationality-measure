module

public import CatalanCore.ThmA.SStep
public import CatalanCore.ThmA.ChainY
public import CatalanCore.Linalg.KrylovBorder
public import CatalanCore.Linalg.Cauchy

/-!
# The K-step (nonvanishing form)

`u(K-1, K) ≠ 0 → u(K, K-1) ≠ 0`, via L1 for `(N, T)` and `(M, Y)` and the bordering lemma L5.
-/

@[expose] public section

open Finset Matrix

namespace CatalanCore.ThmA

variable {F : Type*} [Field F] {N : ℕ}

lemma CtC_eq (m : ℕ) : (Cmat F (m + 1) m)ᵀ * Cmat F (m + 1) m = Nmat F m (m + 1) := by
  ext y y'
  simp only [Nmat, Cmat, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [add_comm ((a : ℕ) : F), add_comm ((a : ℕ) : F)]

lemma ctil_succ_eq (m : ℕ) : ctil F m (((m + 1 : ℕ)) : F) = wvec F m (m + 1) := by
  ext y; simp only [ctil, wvec]; push_cast; ring_nf

lemma CT_e0 (m : ℕ) : (Cmat F (m + 1) m)ᵀ *ᵥ ev (m + 1) 0 = ctil F m 0 := by
  ext y
  simp [Matrix.mulVec, dotProduct, ev, Cmat, ctil, Matrix.transpose_apply, add_comm]

lemma border_det_ne (h : CharGt F N) (m : ℕ) (hN : 2 * m ≤ N) :
    (border (Cmat F (m + 1) m) (ev (m + 1) 0)).det ≠ 0 := by
  rw [Matrix.det_succ_column_zero, Finset.sum_eq_single 0]
  · simp only [border, ev, Matrix.of_apply, Fin.cases_zero, Fin.val_zero, if_true, one_mul,
      Fin.val_zero, pow_zero, Fin.succAbove_zero]
    have := cauchy_det_ne_zero (n := m) (fun a : Fin m => ((a : ℕ) : F) + 1)
      (fun b : Fin m => ((b : ℕ) : F) + 1)
      (fun a b hab => Fin.ext (h.inj (by have := a.2; omega) (by have := b.2; omega)
        (by linear_combination hab)))
      (fun a b hab => Fin.ext (h.inj (by have := a.2; omega) (by have := b.2; omega)
        (by linear_combination hab)))
      (fun i j => by
        have e : ((i : ℕ) : F) + 1 + (((j : ℕ) : F) + 1) = (((i : ℕ) + 1 + ((j : ℕ) + 1) : ℕ) : F) := by
          push_cast; ring
        have := i.2
        have := j.2
        rw [e]; exact h.ne (by omega) (by omega))
    convert this using 2
    ext a b
    simp [Cmat, border]
    ring_nf
  · intro i _ hi
    have : (i : ℕ) ≠ 0 := fun h0 => hi (Fin.ext h0)
    simp [border, ev, this]
    intro h0; exact absurd h0 hi
  · simp

lemma Ymat_cyclic (h : CharGt F N) (K s : ℕ) (hsK : s ≤ K) (hKN : K + s ≤ N) (hs : s ≤ N) :
    kdet (Ymat F K s) (ev s 0) ≠ 0 := by
  refine kdet_tri_ev_ne_zero _ _ fun j hj => ?_
  have := bb_nat_ne h K s (j + 1) (by omega) (by omega) hs (by omega)
  simpa using this

/-- The K-step: `u(K-1, K) ≠ 0 → u(K, K-1) ≠ 0` (here `K = m + 1`). -/
theorem uK_pred_ne (h : CharGt F N) (m : ℕ) (hm : 1 ≤ m) (hN : 3 * (m + 1) ≤ N)
    (hu : uK F m (m + 1) ≠ 0) : uK F (m + 1) m ≠ 0 := by
  have hF : ∀ n : ℕ, 0 < n → n ≤ (m + 1) + m → (n : F) ≠ 0 := fun n hn hle => h.ne hn (by omega)
  have hcommT := Tmat_commute_N (F := F) (m + 1) m hF
  have hcycT := Tmat_cyclic h (m + 1) m (by omega)
  have hcommY := Ymat_commute_M (F := F) (m + 1) m hF
  have hcycY := Ymat_cyclic h (m + 1) m (by omega) (by omega) (by omega)
  have e1 := kdet_cross_ratio hcycT hcommT (wvec F (m + 1) m) (ev (m + 1) 0)
  have e2 := kdet_mul_transpose (Cmat F (m + 1) m) (ev (m + 1) 0)
  have e3 := kdet_cross_ratio hcycY hcommY (ctil F m 0) (ctil F m ((m + 1 : ℕ) : F))
  have hTc : kdet (Tmat F (m + 1) m) (wvec F (m + 1) m) ≠ 0 := by
    rw [wvec_eq_cvec]; exact kdet_T_up_ne h (m + 1) m (by omega) hm (by omega)
  have hYc := kdet_Y_ne h (m + 1) m hm (by omega) (by omega) (by omega)
  have hb := border_det_ne h m (by omega)
  rw [CT_e0] at e2
  rw [CtC_eq, ctil_succ_eq] at e3
  rw [CtC_eq] at e2
  change kdet (Nmat F (m + 1) m) _ * _ = kdet (Nmat F (m + 1) m) _ * _ at e1
  change kdet (Nmat F (m + 1) m) _ = _ at e2
  intro hX
  have hX1 : kdet (Nmat F (m + 1) m) (wvec F (m + 1) m) = 0 := hX
  rw [hX1, zero_mul] at e1
  have hA : kdet (Nmat F (m + 1) m) (ev (m + 1) 0) = 0 := by
    rcases mul_eq_zero.1 e1.symm with h1 | h1
    · exact h1
    · exact absurd h1 hTc
  rw [hA] at e2
  have hM : kdet (Nmat F m (m + 1)) (ctil F m 0) = 0 := by
    rcases mul_eq_zero.1 e2.symm with h1 | h1
    · exact absurd h1 hb
    · exact h1
  rw [hM, zero_mul] at e3
  rcases mul_eq_zero.1 e3.symm with h1 | h1
  · exact hu h1
  · exact hYc h1

/-- Explicit form of `det [e₀ | C]` (a Cauchy matrix). -/
lemma border_det_eq (m : ℕ) :
    (border (Cmat F (m + 1) m) (ev (m + 1) 0)).det =
      (Matrix.of fun a b : Fin m => 1 / ((((a : ℕ) : F) + 1) + (((b : ℕ) : F) + 1))).det := by
  rw [Matrix.det_succ_column_zero, Finset.sum_eq_single 0]
  · simp only [border, ev, Matrix.of_apply, Fin.cases_zero, Fin.val_zero, ite_true, one_mul,
      pow_zero, Fin.succAbove_zero]
    congr 1
    ext a b
    simp [Cmat, border]
    ring_nf
  · intro i _ hi
    have : (i : ℕ) ≠ 0 := fun h0 => hi (Fin.ext h0)
    simp [border, ev, this]
    intro h0; exact absurd h0 hi
  · simp

end CatalanCore.ThmA
