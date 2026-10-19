module

public import CatalanCore.Star.Leonard.KgenAtil
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# `Hn` is invertible as soon as `Δ = det (W_Xᵀ W_Y)` is (package H7 glue)

`ubasis_inj`: the kernel basis `U` is injective (a polynomial `Π_X · g`, `deg g < n`, vanishing at the `K`
nodes is zero).  Then `H = V_Yᵀ U_X` is invertible: if `H x = 0`, `u = U x` is orthogonal to the columns
of `[W_X | V_Y]`, which form a basis (`bmat`, injective by `hΔ` and `V` injective), so `u = 0`.
-/

@[expose] public section

open Finset Matrix Polynomial

namespace CatalanCore.Star.Leonard

variable {F : Type*} [Field F]

lemma pia_ne_zero [CharZero F] (K : ℕ) (a : Fin K) : pia (F := F) K a ≠ 0 := by
  unfold pia
  rw [Finset.prod_ne_zero_iff]
  intro b hb h
  have hne : b ≠ a := Finset.ne_of_mem_erase hb
  apply hne
  apply Fin.ext
  exact Nat.cast_injective (by linear_combination h)

lemma ubasis_inj [CharZero F] (m n : ℕ) (θ : F) (b : Fin m → ℤ) (x : Fin n → F)
    (hx : ubasis (m + n) n θ b *ᵥ x = 0) : x = 0 := by
  classical
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact Subsingleton.elim _ _
  set g : F[X] := ∑ i : Fin n, C (x i) * X ^ (i : ℕ) with hg
  set Pi' : F[X] := ∏ k, (X - C (b k : F)) with hPi
  set P : F[X] := Pi' * g with hP
  have hev : ∀ a : Fin (m + n), P.eval (-(θ + ((a : ℕ) : F))) = 0 := by
    intro a
    have h1 := congrFun hx a
    simp only [Matrix.mulVec, dotProduct, ubasis_apply, Pi.zero_apply] at h1
    have h2 : ∑ i : Fin n, (fpoly (F := F) b i).eval (-(θ + ((a : ℕ) : F))) / pia (m + n) a * x i
        = P.eval (-(θ + ((a : ℕ) : F))) / pia (m + n) a := by
      rw [hP, hg, Polynomial.eval_mul, Polynomial.eval_finset_sum, Finset.mul_sum, Finset.sum_div]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [fpoly, hPi]
      ring
    rw [h2] at h1
    exact (div_eq_zero_iff.1 h1).resolve_right (pia_ne_zero _ _)
  have hinj : Function.Injective (fun a : Fin (m + n) => -(θ + ((a : ℕ) : F))) := by
    intro a a' h
    exact Fin.ext (by simpa using h)
  have hdeg : P.natDegree < Fintype.card (Fin (m + n)) := by
    rw [Fintype.card_fin]
    have h1 : Pi'.natDegree ≤ m := by
      refine (Polynomial.natDegree_prod_le _ _).trans ?_
      refine (Finset.sum_le_sum (g := fun _ => 1) (fun k _ => ?_)).trans (by simp)
      exact (natDegree_sub_le _ _).trans (by simp)
    have h2 : g.natDegree ≤ n - 1 := by
      refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun i _ => ?_
      refine (natDegree_C_mul_le _ _).trans ?_
      simpa using Nat.le_pred_of_lt i.2
    have := Polynomial.natDegree_mul_le (p := Pi') (q := g)
    rw [hP]
    omega
  have hP0 : P = 0 := Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero P hinj hev hdeg
  have hPi0 : Pi' ≠ 0 := (Polynomial.monic_prod_of_monic _ _ fun k _ => Polynomial.monic_X_sub_C _).ne_zero
  have hg0 : g = 0 := (mul_eq_zero.1 hP0).resolve_left hPi0
  funext i
  have := congrArg (fun p : F[X] => p.coeff (i : ℕ)) hg0
  simp only [hg, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_zero] at this
  rw [Finset.sum_eq_single i] at this
  · simpa using this
  · intro j _ hji
    rw [if_neg]
    intro h
    exact hji (Fin.ext h.symm)
  · simp

/-- **`Hn` is invertible when `Δ` is.** (`K = m + n`, borders `X = bX m S`, `Y = bY m S`.) -/
theorem Hn_isUnit [CharZero F] (m n S : ℕ) (θ : F) (hθ : Gen θ)
    (hΔ : IsUnit ((Wb (m + n) θ (bX m (S : ℤ)))ᵀ * Wb (m + n) θ (bY m (S : ℤ))).det) :
    IsUnit (Hn (m + n) m S n θ).det := by
  classical
  have hdist : ∀ a b : Fin (m + n), ((a : ℕ) : F) = ((b : ℕ) : F) → a = b :=
    fun a b h => Fin.ext (Nat.cast_injective h)
  have hmn : m + n ≤ m + n := le_rfl
  have hbx : ∀ (i : Fin m) (a : Fin (m + n)), θ + ((a : ℕ) : F) + (bX m (S : ℤ) i : F) ≠ 0 :=
    fun i a => gen_add hθ a _
  have hby : ∀ (i : Fin m) (a : Fin (m + n)), θ + ((a : ℕ) : F) + (bY m (S : ℤ) i : F) ≠ 0 :=
    fun i a => gen_add hθ a _
  set WX := Wb (m + n) θ (bX m (S : ℤ)) with hWX
  set WY := Wb (m + n) θ (bY m (S : ℤ)) with hWY
  set U := ubasis (m + n) n θ (bX m (S : ℤ)) with hU
  set V := ubasis (m + n) n θ (bY m (S : ℤ)) with hV
  have hgram : Vᵀ * U = Hn (m + n) m S n θ := gram_eq θ S (bX m (S : ℤ)) (bY m (S : ℤ))
    (piB_bX_bY_eq m S)
  have h2 : Vᵀ * WY = 0 := Wt_ubasis_cross θ hdist hmn (bX m (S : ℤ)) (bY m (S : ℤ)) hby
  have h3 : WXᵀ * U = 0 := Wt_ubasis_self θ hdist hmn (bX m (S : ℤ)) hbx
  -- the square matrix [W_X | V]
  have hMv : (CatalanCore.bmat WX V).det ≠ 0 := by
    intro h0
    obtain ⟨z, hz, hz0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    rw [CatalanCore.bmat_mulVec] at hz0
    set zb : Fin m → F := fun i => z (Fin.castAdd n i) with hzb
    set zv : Fin n → F := fun j => z (Fin.natAdd m j) with hzv
    -- apply W_Yᵀ
    have h4 : WYᵀ *ᵥ (WX *ᵥ zb + V *ᵥ zv) = 0 := by rw [hz0, Matrix.mulVec_zero]
    have h5 : WYᵀ *ᵥ (V *ᵥ zv) = 0 := by
      rw [Matrix.mulVec_mulVec]
      have : WYᵀ * V = 0 := by
        have := congrArg Matrix.transpose h2
        simpa [Matrix.transpose_mul] using this
      rw [this, Matrix.zero_mulVec]
    rw [Matrix.mulVec_add, h5, add_zero, Matrix.mulVec_mulVec] at h4
    have hGt : IsUnit ((WYᵀ * WX).det) := by
      have : WYᵀ * WX = (WXᵀ * WY)ᵀ := by rw [Matrix.transpose_mul, Matrix.transpose_transpose]
      rw [this, Matrix.det_transpose]; exact hΔ
    have hzb0 : zb = 0 := by
      by_contra hne
      have := Matrix.exists_mulVec_eq_zero_iff.1 ⟨zb, hne, h4⟩
      exact hGt.ne_zero this
    have hzv0 : zv = 0 := by
      refine ubasis_inj m n θ (bY m (S : ℤ)) zv ?_
      rw [hzb0, Matrix.mulVec_zero, zero_add] at hz0
      exact hz0
    apply hz
    funext j
    refine Fin.addCases (fun i => ?_) (fun j => ?_) j
    · exact congrFun hzb0 i
    · exact congrFun hzv0 j
  -- Hn injective
  by_contra hne
  have hdet : (Hn (m + n) m S n θ).det = 0 := by
    by_contra h; exact hne (isUnit_iff_ne_zero.2 h)
  obtain ⟨x, hx, hHx⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  set u := U *ᵥ x with hu
  have hWu : WXᵀ *ᵥ u = 0 := by rw [hu, Matrix.mulVec_mulVec, h3, Matrix.zero_mulVec]
  have hVu : Vᵀ *ᵥ u = 0 := by rw [hu, Matrix.mulVec_mulVec, hgram]; exact hHx
  have hu0 : u = 0 := by
    by_contra hne'
    have hMt : (CatalanCore.bmat WX V)ᵀ.det = 0 := by
      refine Matrix.exists_mulVec_eq_zero_iff.1 ⟨u, hne', ?_⟩
      funext j
      refine Fin.addCases (fun i => ?_) (fun j => ?_) j
      · have := congrFun hWu i
        simpa [Matrix.mulVec, dotProduct, CatalanCore.bmat, WX, Wb] using this
      · have := congrFun hVu j
        simpa [Matrix.mulVec, dotProduct, CatalanCore.bmat] using this
    rw [Matrix.det_transpose] at hMt
    exact hMv hMt
  exact hx (ubasis_inj m n θ (bX m (S : ℤ)) x hu0)

/-- The bridge `kgen ↔ u(Ã, Π w_S)` with the `Hn` hypothesis discharged. -/
theorem kgen_bridge' [CharZero F] (m n S : ℕ) (θ : F) (hθ : Gen θ)
    (hΔ : IsUnit ((Wb (m + n) θ (bX m (S : ℤ)))ᵀ * Wb (m + n) θ (bY m (S : ℤ))).det)
    (hS : 1 ≤ S) :
    (piB (bY m (S : ℤ)) (S : F) / ∏ a : Fin (m + n), (θ + ((a : ℕ) : F) + (S : F))) ^ n *
        (CatalanCore.bmat (Wb (m + n) θ (bY m (S : ℤ)))
          (ubasis (m + n) n θ (bX m (S : ℤ)))).det *
        kgen (m + n) m S θ =
      (piB (bX m (S : ℤ)) (S : F) / ∏ a : Fin (m + n), (θ + ((a : ℕ) : F) + (S : F))) ^ n *
        (Hn (m + n) m S n θ).det *
        CatalanCore.bkdet (Wb (m + n) θ (bY m (S : ℤ))) (Atil m n S θ)
          (projB (m + n) θ (bX m (S : ℤ)) (bY m (S : ℤ)) *ᵥ wcol (m + n) θ (S : ℤ)) :=
  kgen_bridge m n S θ hθ hΔ hS (Hn_isUnit m n S θ hθ hΔ)

end CatalanCore.Star.Leonard
