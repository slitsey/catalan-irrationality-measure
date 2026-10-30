module

public import CatalanCore.ThmA.Defs
public import CatalanCore.ThmA.ChainKdet
public import CatalanCore.Linalg.TridiagCyclic

/-!
# The s-step (nonvanishing form)

`u(K, s+1) · u(T, c_σ) = u(K, s) · u(T, c_{σ+1})` with `σ = s + 1`, and hence
`u(K, s) ≠ 0 → u(K, s+1) ≠ 0` whenever the chain determinant `u(T, c_{σ+1})` is nonzero.
-/

@[expose] public section

open Finset Matrix

namespace CatalanCore.ThmA

variable {F : Type*} [Field F] {N : ℕ}

lemma wvec_eq_cvec (K s : ℕ) : wvec F K s = cvec F K ((s : F) + 1) := by
  ext a; simp [wvec, cvec, add_assoc]

lemma Nmat_succ (K s : ℕ) :
    Nmat F K (s + 1) = Nmat F K s + Matrix.vecMulVec (wvec F K s) (wvec F K s) := by
  ext a b
  simp [Nmat, Matrix.mul_apply, Fin.sum_univ_castSucc, Cmat, wvec, Matrix.vecMulVec]

lemma Tmat_cyclic (h : CharGt F N) (K σ : ℕ) (hN : σ + K ≤ N) :
    kdet (Tmat F K σ) (ev K 0) ≠ 0 := by
  refine kdet_tri_ev_ne_zero _ _ fun j hj => ?_
  unfold bt
  have e1 : (j : F) + 1 = ((j + 1 : ℕ) : F) := by push_cast; ring
  have e2 : (K : F) - 1 - j = ((K - (j + 1) : ℕ) : F) := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have e3 : (σ : F) + j + 1 = ((σ + j + 1 : ℕ) : F) := by push_cast; ring
  rw [e1, e2, e3]
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero 2 (h.ne (by omega) (by omega)))
    (h.ne (by omega) (by omega))) (h.ne (by omega) (by omega))

/-- The s-step: `u(K,s) ≠ 0 → u(K,s+1) ≠ 0`. -/
theorem uK_succ_ne (h : CharGt F N) (K s : ℕ) (hK : 1 ≤ K) (hs : K ≤ s + 1)
    (hN : s + 1 + 2 * K ≤ N + 1) (hu : uK F K s ≠ 0) : uK F K (s + 1) ≠ 0 := by
  have hcomm := Tmat_commute_N (F := F) K (s + 1) (fun n hn hle => h.ne hn (by omega))
  have hcyc := Tmat_cyclic h K (s + 1) (by omega)
  have cr := kdet_cross_ratio hcyc hcomm (cvec F K (((s + 1 : ℕ) : F)))
    (cvec F K (((s + 1 : ℕ) : F) + 1))
  have up := kdet_T_up_ne h K (s + 1) hK (by omega) hN
  have l2 : kdet (Nmat F K (s + 1)) (cvec F K (((s + 1 : ℕ) : F))) = uK F K s := by
    have : cvec F K (((s + 1 : ℕ) : F)) = wvec F K s := by
      rw [wvec_eq_cvec]; push_cast; rfl
    rw [this, Nmat_succ]
    exact kdet_add_vecMulVec _ _
  have l3 : kdet (Nmat F K (s + 1)) (cvec F K (((s + 1 : ℕ) : F) + 1)) = uK F K (s + 1) := by
    rw [uK, ← wvec_eq_cvec]
  change kdet (Nmat F K (s + 1)) _ * _ = kdet (Nmat F K (s + 1)) _ * _ at cr
  rw [l2, l3] at cr
  intro h0
  rw [h0, zero_mul] at cr
  exact mul_ne_zero hu up cr

end CatalanCore.ThmA
