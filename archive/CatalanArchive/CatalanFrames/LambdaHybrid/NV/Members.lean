module

public import CatalanArchive.CatalanFrames.LambdaHybrid.NV.Instance
public import CatalanCore.Linalg.Cauchy

/-!
# The two members `after r m` and `afterTop r m` at `r = ℓ - K - m`

Facts about node sets: with `K = s' + 1 + m`, `ℓ = 4K - 1`, `r = ℓ - K - m`:
* `X' ∪ Y' = [r, r + 2m)`;
* the absent nodes of `after r m` are `[r + 2m, ℓ) = {ℓ - 1 - i : i ≤ s'}`;
* the absent nodes of `afterTop r m` are `{ℓ - 1 - i : i < s'}`.
-/

@[expose] public section

open Finset CatalanCore CatalanCore.Rect

namespace CatalanArchive.CatalanFrames.LambdaHybrid.NV

lemma memXY (r m n : ℕ) :
    (n ∈ (after r m).X' ∨ n ∈ (after r m).Y') ↔ (r ≤ n ∧ n < r + 2 * m) := by
  simp only [after, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩) <;> omega
  · rintro ⟨h1, h2⟩
    obtain ⟨i, hi | hi⟩ := Nat.even_or_odd' (n - r)
    · exact Or.inl ⟨i, by omega, by omega⟩
    · exact Or.inr ⟨i, by omega, by omega⟩

lemma hab_after (ℓ K m s' : ℕ) (h2K : 2 * K ≤ ℓ) (hs : s' + 1 + m = K) :
    ∀ n, (∃ i : Fin (s' + 1), ℓ - 1 - (i : ℕ) = n) ↔
      n ∈ absS K ℓ (after (ℓ - K - m) m).C (after (ℓ - K - m) m).X' (after (ℓ - K - m) m).Y' := by
  intro n
  have hC : ∀ n, n ∈ (after (ℓ - K - m) m).C ↔ n < ℓ - K - m := by
    intro n; simp [after]
  simp only [absS, Finset.mem_filter, Finset.mem_Ico, hC]
  have hxy := memXY (ℓ - K - m) m n
  constructor
  · rintro ⟨i, rfl⟩
    refine ⟨⟨by omega, by omega⟩, by omega, ?_, ?_⟩
    · intro h; have := hxy.1 (Or.inl h); omega
    · intro h; have := hxy.1 (Or.inr h); omega
  · rintro ⟨⟨h1, h2⟩, h3, h4, h5⟩
    refine ⟨⟨ℓ - 1 - n, by
      have : ¬ (ℓ - K - m ≤ n ∧ n < ℓ - K - m + 2 * m) := fun h => by
        rcases hxy.2 h with h | h <;> contradiction
      omega⟩, by
      have : ¬ (ℓ - K - m ≤ n ∧ n < ℓ - K - m + 2 * m) := fun h => by
        rcases hxy.2 h with h | h <;> contradiction
      simp only; omega⟩

lemma hab_afterTop (ℓ K m s' : ℕ) (h2K : 2 * K ≤ ℓ) (hs : s' + 1 + m = K) :
    ∀ n, (∃ i : Fin s', ℓ - 1 - (i : ℕ) = n) ↔
      n ∈ absS K ℓ (afterTop (ℓ - K - m) m).C (afterTop (ℓ - K - m) m).X'
        (afterTop (ℓ - K - m) m).Y' := by
  intro n
  have hC : ∀ n, n ∈ (afterTop (ℓ - K - m) m).C ↔ (n = ℓ - K - m + 2 * m ∨ n < ℓ - K - m) := by
    intro n; simp [afterTop]
  have hxy := memXY (ℓ - K - m) m n
  simp only [absS, Finset.mem_filter, Finset.mem_Ico, hC]
  change _ ↔ _ ∧ ¬ _ ∧ ¬ (n ∈ (after (ℓ - K - m) m).X') ∧ ¬ (n ∈ (after (ℓ - K - m) m).Y')
  constructor
  · rintro ⟨i, rfl⟩
    have := i.2
    refine ⟨⟨by omega, by omega⟩, by omega, ?_, ?_⟩
    · intro h; have := hxy.1 (Or.inl h); omega
    · intro h; have := hxy.1 (Or.inr h); omega
  · rintro ⟨⟨h1, h2⟩, h3, h4, h5⟩
    have hn : ¬ (ℓ - K - m ≤ n ∧ n < ℓ - K - m + 2 * m) := fun h => by
      rcases hxy.2 h with h | h <;> contradiction
    exact ⟨⟨ℓ - 1 - n, by omega⟩, by simp only; omega⟩

section Cauchy

variable {ℓ : ℕ} [Fact ℓ.Prime]

/-- Nonvanishing of a Cauchy determinant `1/(u_i - v_j)` mod `ℓ`: `u` low nodes, `v` high nodes,
all distinct and `< ℓ` (every integer factor lies in `[1, ℓ-1]`). -/
lemma cauchy_ne_zero {ι : Type} [Fintype ι] [DecidableEq ι] (u v : ι → ℕ)
    (hu : Function.Injective u) (hv : Function.Injective v) {K : ℕ} (hKl : K ≤ ℓ)
    (hlow : ∀ i, u i < K) (hhigh : ∀ j, K ≤ v j ∧ v j < ℓ) :
    (Matrix.of fun i j : ι => 1 / ((u i : ZMod ℓ) - (v j : ZMod ℓ))).det ≠ 0 := by
  set σ : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm with hσ
  set x : Fin (Fintype.card ι) → ZMod ℓ := fun i => (u (σ i) : ZMod ℓ) with hx
  set y : Fin (Fintype.card ι) → ZMod ℓ := fun j => -(v (σ j) : ZMod ℓ) with hy
  have hM : (Matrix.of fun i j : ι => 1 / ((u i : ZMod ℓ) - (v j : ZMod ℓ))).submatrix σ σ =
      Matrix.of fun i j => 1 / (x i + y j) := by
    ext i j; simp [hx, hy, sub_eq_add_neg]
  have hxy : ∀ i j, x i + y j ≠ 0 := by
    intro i j
    simp only [hx, hy, ← sub_eq_add_neg]
    exact sub_ne_zero.2 (CatalanCore.natCast_ne_natCast (by have := hlow (σ i); omega)
      (hhigh (σ j)).2 (by have := hlow (σ i); have := (hhigh (σ j)).1; omega))
  have hc := CatalanCore.cauchy_det_mul x y hxy
  have hnum : CatalanCore.cauchyNum x y ≠ 0 := by
    unfold CatalanCore.cauchyNum
    refine Finset.prod_ne_zero_iff.2 fun i _ => Finset.prod_ne_zero_iff.2 fun j _ => ?_
    split_ifs with hij
    · refine mul_ne_zero ?_ ?_
      · simp only [hx]
        exact sub_ne_zero.2 (fun h => by
          have := CatalanCore.natCast_ne_natCast (p := ℓ) (a := u (σ j)) (b := u (σ i))
            (by have := hlow (σ j); omega) (by have := hlow (σ i); omega)
            (fun h' => absurd (σ.injective (hu h')) (ne_of_gt hij))
          exact this h)
      · simp only [hy]
        exact sub_ne_zero.2 (fun h => by
          have h' : (v (σ i) : ZMod ℓ) = v (σ j) := by simpa using h.symm
          have := CatalanCore.natCast_ne_natCast (p := ℓ) (a := v (σ i)) (b := v (σ j))
            (hhigh (σ i)).2 (hhigh (σ j)).2
            (fun h'' => absurd (σ.injective (hv h'')) (ne_of_lt hij))
          exact this h')
    · exact one_ne_zero
  rw [← Matrix.det_submatrix_equiv_self σ, hM]
  intro h0
  rw [h0, zero_mul] at hc
  exact hnum hc.symm

end Cauchy

end CatalanArchive.CatalanFrames.LambdaHybrid.NV
