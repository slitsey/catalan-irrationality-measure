module

public import CatalanCore.Star.Leonard.HnUnit
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The kernel basis `U` spans `ker W_Xᵀ` in any field with distinct nodes

Generalisation of `ubasis_inj` (no `CharZero`; distinct nodes `a ∈ Fin K` instead), and
`ker W_Xᵀ = range U` by a dimension count (`W_Xᵀ` is onto because `W_Xᵀ W_Y` is invertible).
-/

@[expose] public section

open Finset Matrix Polynomial

namespace CatalanCore.Star.Leonard

variable {F : Type*} [Field F]

lemma pia_ne_zero' {K : ℕ} (hdist : ∀ a b : Fin K, ((a : ℕ) : F) = ((b : ℕ) : F) → a = b)
    (a : Fin K) : pia (F := F) K a ≠ 0 := by
  unfold pia
  rw [Finset.prod_ne_zero_iff]
  intro b hb h
  have hne : b ≠ a := Finset.ne_of_mem_erase hb
  exact hne (hdist b a (by linear_combination h))

lemma ubasis_inj' (m n : ℕ) (θ : F)
    (hdist : ∀ a b : Fin (m + n), ((a : ℕ) : F) = ((b : ℕ) : F) → a = b) (b : Fin m → ℤ)
    (x : Fin n → F) (hx : ubasis (m + n) n θ b *ᵥ x = 0) : x = 0 := by
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
    exact (div_eq_zero_iff.1 h1).resolve_right (pia_ne_zero' hdist _)
  have hinj : Function.Injective (fun a : Fin (m + n) => -(θ + ((a : ℕ) : F))) := by
    intro a a' h
    exact hdist a a' (by simpa using h)
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

/-- `ker W_Xᵀ = range U`. -/
theorem exists_ubasis_of_ker (m n : ℕ) (θ : F)
    (hdist : ∀ a b : Fin (m + n), ((a : ℕ) : F) = ((b : ℕ) : F) → a = b) (bx by' : Fin m → ℤ)
    (hbx : ∀ (i : Fin m) (a : Fin (m + n)), θ + ((a : ℕ) : F) + (bx i : F) ≠ 0)
    (hΔ : ((Wb (m + n) θ bx)ᵀ * Wb (m + n) θ by').det ≠ 0)
    (x : Fin (m + n) → F) (hx : (Wb (m + n) θ bx)ᵀ *ᵥ x = 0) :
    ∃ y : Fin n → F, ubasis (m + n) n θ bx *ᵥ y = x := by
  classical
  set T : Matrix (Fin m) (Fin (m + n)) F := (Wb (m + n) θ bx)ᵀ with hT
  set U : Matrix (Fin (m + n)) (Fin n) F := ubasis (m + n) n θ bx with hU
  set f := Matrix.toLin' T with hf
  set g := Matrix.toLin' U with hg
  have hTU : T * U = 0 := Wt_ubasis_self θ hdist le_rfl bx hbx
  have hsurj : LinearMap.range f = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro v
    have hu : IsUnit (T * Wb (m + n) θ by').det := isUnit_iff_ne_zero.2 hΔ
    refine ⟨(Wb (m + n) θ by') *ᵥ ((T * Wb (m + n) θ by')⁻¹ *ᵥ v), ?_⟩
    rw [hf, Matrix.toLin'_apply, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]
  have hinj : Function.Injective g := by
    rw [hg, injective_iff_map_eq_zero]
    intro y hy
    exact ubasis_inj' m n θ hdist bx y (by simpa [Matrix.toLin'_apply] using hy)
  have hle : LinearMap.range g ≤ LinearMap.ker f := by
    rintro _ ⟨y, rfl⟩
    rw [LinearMap.mem_ker, hf, hg, Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.mulVec_mulVec,
      hTU, Matrix.zero_mulVec]
  have hrk := LinearMap.finrank_range_add_finrank_ker f
  rw [hsurj, finrank_top] at hrk
  simp only [Module.finrank_fin_fun] at hrk
  have h1 : Module.finrank F (LinearMap.range g) = n := by
    rw [LinearMap.finrank_range_of_inj hinj]; simp
  have h2 : Module.finrank F (LinearMap.ker f) = n := by omega
  have heq := Submodule.eq_of_le_of_finrank_eq hle (by rw [h1, h2])
  have hxk : x ∈ LinearMap.ker f := by
    rw [LinearMap.mem_ker, hf, Matrix.toLin'_apply]; exact hx
  rw [← heq] at hxk
  obtain ⟨y, hy⟩ := hxk
  exact ⟨y, by simpa [hg, Matrix.toLin'_apply] using hy⟩

theorem exists_ubasis_of_ker_K (K m n : ℕ) (hKmn : m + n = K) (θ : F)
    (hdist : ∀ a b : Fin K, ((a : ℕ) : F) = ((b : ℕ) : F) → a = b) (bx by' : Fin m → ℤ)
    (hbx : ∀ (i : Fin m) (a : Fin K), θ + ((a : ℕ) : F) + (bx i : F) ≠ 0)
    (hΔ : ((Wb K θ bx)ᵀ * Wb K θ by').det ≠ 0)
    (x : Fin K → F) (hx : (Wb K θ bx)ᵀ *ᵥ x = 0) :
    ∃ y : Fin n → F, ubasis K n θ bx *ᵥ y = x := by
  subst hKmn
  exact exists_ubasis_of_ker m n θ hdist bx by' hbx hΔ x hx

end CatalanCore.Star.Leonard
