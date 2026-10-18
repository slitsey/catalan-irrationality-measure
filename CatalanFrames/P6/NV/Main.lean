module

public import CatalanFrames.P6.NV.Reduction
public import CatalanCore.ThmA.Statement
public import CatalanCore.Linalg.KrylovEigen

/-!
# P6 NV: the `ℓ`-integral case (WP11)

For `ℓ = 6t+1 ≥ 13` prime and `ℓ`-integral `r`, `P_{3t}(r)` and `P_{3t+1}(r)` do not both vanish.
The reduction (`reduce`) turns the two vanishings into `det (z + N_0) = 0` and
`det (z + N_0 - 2 w wᵀ) = 0`, which Theorem A (`u(K,m) ≠ 0`, `K = 2t+1`, `m = 3t`, `m + K < ℓ`)
excludes (Corollary kr with weight `γ = -2 ≠ 0`).
-/

@[expose] public section

open Finset Matrix CatalanCore

namespace CatalanFrames.P6.NV

open CatalanFrames.P6

section Kr
variable {F : Type*} [Field F] {n : ℕ}

/-- Corollary kr with an arbitrary nonzero weight `γ`. -/
theorem no_common_root_gamma (N : Matrix (Fin n) (Fin n) F) (hN : Nᵀ = N) (w : Fin n → F)
    (hu : kdet N w ≠ 0) (γ : F) (hγ : γ ≠ 0) (z : F) :
    (z • (1 : Matrix (Fin n) (Fin n) F) + N).det ≠ 0 ∨
      (z • (1 : Matrix (Fin n) (Fin n) F) + (N + γ • Matrix.vecMulVec w w)).det ≠ 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hA, hA'⟩ := hcon
  set A : Matrix (Fin n) (Fin n) F := z • (1 : Matrix (Fin n) (Fin n) F) + N with hAdef
  have hAsymm : Aᵀ = A := by
    rw [hAdef, Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_one, hN]
  have hrw : z • (1 : Matrix (Fin n) (Fin n) F) + (N + γ • Matrix.vecMulVec w w) =
      A + γ • Matrix.vecMulVec w w := by rw [hAdef, add_assoc]
  rw [hrw] at hA'
  obtain ⟨y, hy0, hy⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hA'
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hA
  have vmv : ∀ x : Fin n → F, Matrix.vecMulVec w w *ᵥ x = (w ⬝ᵥ x) • w := by
    intro x
    ext i
    simp only [Matrix.mulVec, Matrix.vecMulVec, dotProduct, Matrix.of_apply, Pi.smul_apply,
      smul_eq_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hy' : A *ᵥ y = -(γ • ((w ⬝ᵥ y) • w)) := by
    rw [Matrix.add_mulVec, Matrix.smul_mulVec, vmv] at hy
    exact eq_neg_of_add_eq_zero_left hy
  by_cases hc : w ⬝ᵥ y = 0
  · rw [hc, zero_smul, smul_zero, neg_zero] at hy'
    exact hu (kdet_eq_zero_of_eigen N hN w z y hy0 hy' hc)
  by_cases hd : w ⬝ᵥ v = 0
  · exact hu (kdet_eq_zero_of_eigen N hN w z v hv0 hv hd)
  have h1 : v ⬝ᵥ (A *ᵥ y) = 0 := by
    rw [dotProduct_mulVec, ← Matrix.mulVec_transpose, hAsymm, hv, zero_dotProduct]
  rw [hy', dotProduct_neg, dotProduct_smul, dotProduct_smul, dotProduct_comm v w] at h1
  simp only [smul_eq_mul, neg_eq_zero, mul_eq_zero] at h1
  rcases h1 with h1 | h1 | h1
  · exact hγ h1
  · exact hc h1
  · exact hd h1

end Kr

section Main
variable {ℓ t : ℕ} [Fact ℓ.Prime] (hl : ℓ = 6 * t + 1) (ht : 2 ≤ t)
include hl ht

lemma Nsig_zero : Nsig ℓ t 0 = ThmA.Nmat (ZMod ℓ) (2 * t + 1) (3 * t) := by
  ext a b
  simp only [Nsig, Matrix.of_apply, ThmA.Nmat, Matrix.mul_apply, Matrix.transpose_apply,
    ThmA.Cmat, Finset.range_zero, Finset.sum_empty, mul_zero, sub_zero, finv]
  rw [← Fin.sum_univ_eq_sum_range (fun j => ((((a : ℕ) + 1 + j : ℕ) : ZMod ℓ))⁻¹ *
    ((((b : ℕ) + 1 + j : ℕ) : ZMod ℓ))⁻¹)]
  refine Finset.sum_congr rfl fun j _ => ?_
  push_cast
  simp only [one_div]
  ring_nf

lemma Nsig_one : Nsig ℓ t 1 = ThmA.Nmat (ZMod ℓ) (2 * t + 1) (3 * t) +
    (-2 : ZMod ℓ) • Matrix.vecMulVec (ThmA.wvec (ZMod ℓ) (2 * t + 1) (3 * t))
      (ThmA.wvec (ZMod ℓ) (2 * t + 1) (3 * t)) := by
  have h0 := Nsig_zero hl ht (ℓ := ℓ)
  rw [← h0]
  ext a b
  simp only [Nsig, Matrix.of_apply, Finset.range_one, Finset.sum_singleton, Finset.range_zero,
    Finset.sum_empty, Matrix.add_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, ThmA.wvec,
    smul_eq_mul, finv, mul_zero, sub_zero, Nat.add_zero]
  push_cast
  simp only [one_div]
  ring_nf
  rw [Finset.sum_congr rfl (g := fun x : ℕ => (1 + ((a : ℕ) : ZMod ℓ) + (x : ZMod ℓ))⁻¹ * (1 + ((b : ℕ) : ZMod ℓ) + (x : ZMod ℓ))⁻¹) (fun x _ => by ring)]
  ring

/-- **Integral case.** -/
theorem nv_integral {r : ℚ} (hr : r ∈ S ℓ) :
    p6Frame.P (3 * t) r ≠ 0 ∨ p6Frame.P (3 * t + 1) r ≠ 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h0, h1⟩ := hcon
  have ht1 : 1 ≤ t := by omega
  have hg : Good ℓ r (red ℓ r) := good_red hr
  have e0 := reduce hl ht1 (n := t) le_rfl hg (by
    rw [show 2 * t + 1 + t = 3 * t + 1 by ring]; exact h1)
  have e1 := reduce hl ht1 (n := t - 1) (by omega) hg (by
    rw [show 2 * t + 1 + (t - 1) = 3 * t by omega]; exact h0)
  rw [Nat.sub_self] at e0
  rw [show t - (t - 1) = 1 by omega, Nsig_one hl ht] at e1
  rw [Nsig_zero hl ht] at e0
  have hunit : ThmA.uK (ZMod ℓ) (2 * t + 1) (3 * t) ≠ 0 :=
    ThmA.unit_of_lt ℓ (2 * t + 1) (3 * t) (by omega) (by omega) (by omega)
  have hsym : (ThmA.Nmat (ZMod ℓ) (2 * t + 1) (3 * t))ᵀ = ThmA.Nmat (ZMod ℓ) (2 * t + 1) (3 * t) := by
    simp [ThmA.Nmat, Matrix.transpose_mul]
  have h2 : (-2 : ZMod ℓ) ≠ 0 := neg_ne_zero.2 (two_ne hl (by omega))
  rcases no_common_root_gamma _ hsym _ hunit (-2) h2 (36 * red ℓ r - cc ℓ t) with h | h
  · exact h e0
  · exact h e1

end Main

end CatalanFrames.P6.NV
