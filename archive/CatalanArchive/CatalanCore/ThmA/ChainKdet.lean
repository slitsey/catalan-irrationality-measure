module

public import CatalanCore.ThmA.Chain
public import CatalanCore.Linalg.KrylovTri
public import CatalanCore.Linalg.CauchyNe
public import CatalanCore.Linalg.Cauchy

/-!
# Nonvanishing of the chain Krylov determinants `u(T, c_σ)` and `u(T, c_{σ+1})`

Over any field in which `1, …, N` are nonzero, with `σ + 2K ≤ N + 1` and `K ≤ σ`.  Only
nonvanishing is proved (no closed form): L3 + the Cauchy nonvanishing lemma.
-/

@[expose] public section

open Finset Matrix

namespace CatalanCore.ThmA

variable {F : Type*} [Field F] {N : ℕ}

/-- The integers `1, …, N` are nonzero in `F`. -/
def CharGt (F : Type*) [Field F] (N : ℕ) : Prop := ∀ n : ℕ, 0 < n → n ≤ N → (n : F) ≠ 0

lemma CharGt.ne (h : CharGt F N) {n : ℕ} (h0 : 0 < n) (hn : n ≤ N) : (n : F) ≠ 0 := h n h0 hn

lemma CharGt.inj (h : CharGt F N) {a b : ℕ} (ha : a ≤ N) (hb : b ≤ N) (hab : (a : F) = b) :
    a = b := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h1 | h1
  · apply h.ne (n := b - a) (by omega) (by omega)
    rw [Nat.cast_sub h1.le]; exact sub_eq_zero.2 hab.symm
  · apply h.ne (n := a - b) (by omega) (by omega)
    rw [Nat.cast_sub h1.le]; exact sub_eq_zero.2 hab

lemma bb_nat_ne (h : CharGt F N) (K σ m : ℕ) (hm : 0 < m) (hmK : m + K ≤ N) (hσ : σ ≤ N)
    (hne : m ≠ σ) : bb (K : F) (σ : F) (m : F) ≠ 0 := by
  unfold bb
  have h1 : (m : F) ≠ 0 := h.ne hm (by omega)
  have h2 : (m : F) + K ≠ 0 := by
    have := h.ne (n := m + K) (by omega) hmK
    simpa using this
  have h3 : (σ : F) - m ≠ 0 := fun hh => hne (h.inj (by omega) hσ (sub_eq_zero.1 hh).symm)
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero 2 h1) h2) h3

lemma colMat_cvec_det_ne (h : CharGt F N) (K : ℕ) (hK : K ≤ N) (yf : ℕ → F)
    (hinj : ∀ i j, i < K → j < K → yf i = yf j → i = j)
    (hne : ∀ a j, a < K → j < K → (a : F) + yf j ≠ 0) :
    (colMat fun j => cvec F K (yf j)).det ≠ 0 := by
  have := cauchy_det_ne_zero (n := K) (fun a : Fin K => ((a : ℕ) : F)) (fun j : Fin K => yf j)
    (fun a b hab => Fin.ext (h.inj (by have := a.2; omega) (by have := b.2; omega) hab))
    (fun a b hab => Fin.ext (hinj a b a.2 b.2 hab)) (fun a j => hne a j a.2 j.2)
  exact this

/-- Downward chain nodes `σ - j`. -/
def yDown (F : Type*) [Field F] (σ j : ℕ) : F := (σ : F) - (j : F)
/-- Upward chain nodes `σ + 1 + j`. -/
def yUp (F : Type*) [Field F] (σ j : ℕ) : F := (σ : F) + 1 + (j : F)

lemma T_down_hT (h : CharGt F N) (K σ : ℕ) (hK : 1 ≤ K) (hσ : K ≤ σ) (hN : σ + 2 * K ≤ N + 1) :
    ∀ j, j + 1 < K → Tmat F K σ *ᵥ cvec F K (yDown F σ j) =
      bb (K : F) (σ : F) (yDown F σ j - 1) • cvec F K (yDown F σ (j + 1)) +
      Yd (K : F) (σ : F) (yDown F σ j) • cvec F K (yDown F σ j) +
      bb (K : F) (σ : F) (yDown F σ j) • cvec F K (yDown F σ (j - 1)) := by
  intro j hj
  have d0 : ∀ a : Fin K, (a : F) + yDown F σ j ≠ 0 := fun a => by
    have e : ((a : ℕ) : F) + yDown F σ j = (((a : ℕ) + σ - j : ℕ) : F) := by
      rw [Nat.cast_sub (by omega)]; unfold yDown; push_cast; ring
    have := a.2
    rw [e]; exact h.ne (by omega) (by omega)
  have d1 : ∀ a : Fin K, (a : F) + yDown F σ j + 1 ≠ 0 := fun a => by
    have e : ((a : ℕ) : F) + yDown F σ j + 1 = (((a : ℕ) + σ + 1 - j : ℕ) : F) := by
      rw [Nat.cast_sub (by omega)]; unfold yDown; push_cast; ring
    have := a.2
    rw [e]; exact h.ne (by omega) (by omega)
  have d2 : ∀ a : Fin K, (a : F) + yDown F σ j - 1 ≠ 0 := fun a => by
    have e : ((a : ℕ) : F) + yDown F σ j - 1 = (((a : ℕ) + σ - (j + 1) : ℕ) : F) := by
      rw [Nat.cast_sub (by omega)]; unfold yDown; push_cast; ring
    have := a.2
    rw [e]; exact h.ne (by omega) (by omega)
  rw [Tmat_mulVec_cvec K σ (yDown F σ j) d0 d1 d2]
  have e1 : yDown F σ (j + 1) = yDown F σ j - 1 := by unfold yDown; push_cast; ring
  rcases j with _ | j
  · have : bb (K : F) (σ : F) (yDown F σ 0) = 0 := by simp [yDown, bb]
    simp only [this, zero_smul, add_zero, zero_add]
    rw [e1]; abel
  · have e2 : yDown F σ j = yDown F σ (j + 1) + 1 := by unfold yDown; push_cast; ring
    simp only [Nat.add_sub_cancel]
    rw [e2, e1]; abel

theorem kdet_T_down_ne (h : CharGt F N) (K σ : ℕ) (hK : 1 ≤ K) (hσ : K ≤ σ)
    (hN : σ + 2 * K ≤ N + 1) : kdet (Tmat F K σ) (cvec F K (σ : F)) ≠ 0 := by
  have v0 : cvec F K (σ : F) = cvec F K (yDown F σ 0) := by simp [yDown]
  rw [v0]
  refine kdet_ne_zero_of_chain (Tmat F K σ) (fun j => cvec F K (yDown F σ j))
    (fun j => bb (K : F) (σ : F) (yDown F σ j - 1)) (fun j => Yd (K : F) (σ : F) (yDown F σ j))
    (fun j => bb (K : F) (σ : F) (yDown F σ j)) ?_ ?_ ?_ ?_
  · exact T_down_hT h K σ hK hσ hN
  · simp [yDown, bb]
  · intro j hj
    have e : yDown F σ j - 1 = (((σ - (j + 1) : ℕ)) : F) := by
      rw [Nat.cast_sub (by omega)]; unfold yDown; push_cast; ring
    show bb (K : F) (σ : F) (yDown F σ j - 1) ≠ 0
    rw [e]
    exact bb_nat_ne h K σ _ (by omega) (by omega) (by omega) (by omega)
  · refine colMat_cvec_det_ne h K (by omega) _ ?_ ?_
    · intro i j hi hj hij
      have : (i : F) = j := by unfold yDown at hij; linear_combination -hij
      exact h.inj (by omega) (by omega) this
    · intro a j ha hj
      have e : (a : F) + yDown F σ j = ((a + σ - j : ℕ) : F) := by
        rw [Nat.cast_sub (by omega)]; unfold yDown; push_cast; ring
      rw [e]; exact h.ne (by omega) (by omega)

lemma T_up_hT (h : CharGt F N) (K σ : ℕ) (hK : 1 ≤ K) (hσ : 1 ≤ σ) (hN : σ + 2 * K ≤ N + 1) :
    ∀ j, j + 1 < K → Tmat F K σ *ᵥ cvec F K (yUp F σ j) =
      bb (K : F) (σ : F) (yUp F σ j) • cvec F K (yUp F σ (j + 1)) +
      Yd (K : F) (σ : F) (yUp F σ j) • cvec F K (yUp F σ j) +
      bb (K : F) (σ : F) (yUp F σ j - 1) • cvec F K (yUp F σ (j - 1)) := by
  intro j hj
  have d0 : ∀ a : Fin K, (a : F) + yUp F σ j ≠ 0 := fun a => by
    have e : ((a : ℕ) : F) + yUp F σ j = (((a : ℕ) + σ + 1 + j : ℕ) : F) := by
      unfold yUp; push_cast; ring
    have := a.2
    rw [e]; exact h.ne (by omega) (by omega)
  have d1 : ∀ a : Fin K, (a : F) + yUp F σ j + 1 ≠ 0 := fun a => by
    have e : ((a : ℕ) : F) + yUp F σ j + 1 = (((a : ℕ) + σ + 1 + j + 1 : ℕ) : F) := by
      unfold yUp; push_cast; ring
    have := a.2
    rw [e]; exact h.ne (by omega) (by omega)
  have d2 : ∀ a : Fin K, (a : F) + yUp F σ j - 1 ≠ 0 := fun a => by
    have e : ((a : ℕ) : F) + yUp F σ j - 1 = (((a : ℕ) + σ + j : ℕ) : F) := by
      unfold yUp; push_cast; ring
    have := a.2
    rw [e]; exact h.ne (by omega) (by omega)
  rw [Tmat_mulVec_cvec K σ (yUp F σ j) d0 d1 d2]
  have e1 : yUp F σ (j + 1) = yUp F σ j + 1 := by unfold yUp; push_cast; ring
  rcases j with _ | j
  · have : bb (K : F) (σ : F) (yUp F σ 0 - 1) = 0 := by simp [yUp, bb]
    simp only [this, zero_smul, add_zero, zero_add]
    rw [e1]
  · have e2 : yUp F σ j = yUp F σ (j + 1) - 1 := by unfold yUp; push_cast; ring
    simp only [Nat.add_sub_cancel]
    rw [e2, e1]

theorem kdet_T_up_ne (h : CharGt F N) (K σ : ℕ) (hK : 1 ≤ K) (hσ : 1 ≤ σ)
    (hN : σ + 2 * K ≤ N + 1) : kdet (Tmat F K σ) (cvec F K ((σ : F) + 1)) ≠ 0 := by
  have v0 : cvec F K ((σ : F) + 1) = cvec F K (yUp F σ 0) := by simp [yUp]
  rw [v0]
  refine kdet_ne_zero_of_chain (Tmat F K σ) (fun j => cvec F K (yUp F σ j))
    (fun j => bb (K : F) (σ : F) (yUp F σ j)) (fun j => Yd (K : F) (σ : F) (yUp F σ j))
    (fun j => bb (K : F) (σ : F) (yUp F σ j - 1)) ?_ ?_ ?_ ?_
  · exact T_up_hT h K σ hK hσ hN
  · simp [yUp, bb]
  · intro j hj
    have e : yUp F σ j = ((σ + 1 + j : ℕ) : F) := by unfold yUp; push_cast; ring
    show bb (K : F) (σ : F) (yUp F σ j) ≠ 0
    rw [e]
    exact bb_nat_ne h K σ _ (by omega) (by omega) (by omega) (by omega)
  · refine colMat_cvec_det_ne h K (by omega) _ ?_ ?_
    · intro i j hi hj hij
      have : (i : F) = j := by unfold yUp at hij; linear_combination hij
      exact h.inj (by omega) (by omega) this
    · intro a j ha hj
      have e : (a : F) + yUp F σ j = ((a + σ + 1 + j : ℕ) : F) := by
        unfold yUp; push_cast; ring
      rw [e]; exact h.ne (by omega) (by omega)

/-- Explicit form of `u(T, c_σ)` (downward chain). -/
theorem kdet_T_down_eq (h : CharGt F N) (K σ : ℕ) (hK : 1 ≤ K) (hσ : K ≤ σ)
    (hN : σ + 2 * K ≤ N + 1) :
    kdet (Tmat F K σ) (cvec F K (σ : F)) =
      (∏ k : Fin K, ∏ j ∈ Finset.range (k : ℕ), bb (K : F) (σ : F) (yDown F σ j - 1)) *
        ((∏ i : Fin K, ∏ j ∈ Finset.Ioi i,
            ((((j : ℕ) : F) - ((i : ℕ) : F)) * (yDown F σ j - yDown F σ i))) /
          ∏ i : Fin K, ∏ j : Fin K, (((i : ℕ) : F) + yDown F σ j)) := by
  have v0 : cvec F K (σ : F) = cvec F K (yDown F σ 0) := by simp [yDown]
  rw [v0, kdet_eq_of_chain (Tmat F K σ) (fun j => cvec F K (yDown F σ j))
    (fun j => bb (K : F) (σ : F) (yDown F σ j - 1)) (fun j => Yd (K : F) (σ : F) (yDown F σ j))
    (fun j => bb (K : F) (σ : F) (yDown F σ j)) (T_down_hT h K σ hK hσ hN) (by simp [yDown, bb])]
  congr 1
  have hne : ∀ i j : Fin K, ((i : ℕ) : F) + yDown F σ j ≠ 0 := fun a j => by
    have e : (((a : ℕ)) : F) + yDown F σ j = (((a : ℕ) + σ - j : ℕ) : F) := by
      rw [Nat.cast_sub (by have := j.2; have := a.2; omega)]; unfold yDown; push_cast; ring
    have := a.2
    have := j.2
    rw [e]; exact h.ne (by omega) (by omega)
  exact cauchy_det (fun i : Fin K => ((i : ℕ) : F)) (fun j : Fin K => yDown F σ j) hne

/-- Explicit form of `u(T, c_{σ+1})` (upward chain). -/
theorem kdet_T_up_eq (h : CharGt F N) (K σ : ℕ) (hK : 1 ≤ K) (hσ : 1 ≤ σ)
    (hN : σ + 2 * K ≤ N + 1) :
    kdet (Tmat F K σ) (cvec F K ((σ : F) + 1)) =
      (∏ k : Fin K, ∏ j ∈ Finset.range (k : ℕ), bb (K : F) (σ : F) (yUp F σ j)) *
        ((∏ i : Fin K, ∏ j ∈ Finset.Ioi i,
            ((((j : ℕ) : F) - ((i : ℕ) : F)) * (yUp F σ j - yUp F σ i))) /
          ∏ i : Fin K, ∏ j : Fin K, (((i : ℕ) : F) + yUp F σ j)) := by
  have v0 : cvec F K ((σ : F) + 1) = cvec F K (yUp F σ 0) := by simp [yUp]
  rw [v0, kdet_eq_of_chain (Tmat F K σ) (fun j => cvec F K (yUp F σ j))
    (fun j => bb (K : F) (σ : F) (yUp F σ j)) (fun j => Yd (K : F) (σ : F) (yUp F σ j))
    (fun j => bb (K : F) (σ : F) (yUp F σ j - 1)) (T_up_hT h K σ hK hσ hN) (by simp [yUp, bb])]
  congr 1
  have hne : ∀ i j : Fin K, ((i : ℕ) : F) + yUp F σ j ≠ 0 := fun a j => by
    have e : (((a : ℕ)) : F) + yUp F σ j = (((a : ℕ) + σ + 1 + j : ℕ) : F) := by
      unfold yUp; push_cast; ring
    have := a.2
    have := j.2
    rw [e]; exact h.ne (by omega) (by omega)
  exact cauchy_det (fun i : Fin K => ((i : ℕ) : F)) (fun j : Fin K => yUp F σ j) hne

end CatalanCore.ThmA
