module

public import CatalanFrames.LambdaHybrid.NV.Final
public import CatalanFrames.LambdaHybrid.NV.Primal

/-!
# P1 deliverable: the member pair at general absent count `S = s' + 1` (FG primal route)

For `S` absent nodes in member 1 (`{ℓ-1-i : i < S}`) the matrix `Γ̂` is singular (FG), so
`nv_hyb_pair_gen` (S = K - m only) does not apply.  Here the geometry is `after r m` /
`afterTop r m` with `r + 2m + S = ℓ` and `K ≤ r`, and the conclusion is the primal one:
`k^gen_R' = 0 ∨ k^gen_L' = 0` (for every kernel-spanning family; see `Primal.lean`), where
`N₂ = G₂ G₂ᵀ` is the Gram matrix of the `S - 1` absent columns of member 2 and `w` is the column of
the node `ℓ - 1 - s'` (the one member 2 moves into `C`).

`hΔ` (`det(WXᵀ WY)` is a unit mod `ℓ`, FG Prop hDelta / `Cor hRXY`) is a hypothesis here.
-/

@[expose] public section

open Finset Matrix CatalanCore CatalanCore.Rect

namespace CatalanFrames.LambdaHybrid.NV

variable {ℓ K : ℕ} [Fact ℓ.Prime]

lemma hab_afterS (ℓ K m r s' : ℕ) (hrK : K ≤ r) (hr : r + 2 * m + (s' + 1) = ℓ) :
    ∀ n, (∃ i : Fin (s' + 1), ℓ - 1 - (i : ℕ) = n) ↔
      n ∈ absS K ℓ (after r m).C (after r m).X' (after r m).Y' := by
  intro n
  have hC : ∀ n, n ∈ (after r m).C ↔ n < r := by
    intro n; simp [after]
  simp only [absS, Finset.mem_filter, Finset.mem_Ico, hC]
  have hxy := memXY r m n
  constructor
  · rintro ⟨i, rfl⟩
    have := i.2
    refine ⟨⟨by omega, by omega⟩, by omega, ?_, ?_⟩
    · intro h; have := hxy.1 (Or.inl h); omega
    · intro h; have := hxy.1 (Or.inr h); omega
  · rintro ⟨⟨h1, h2⟩, h3, h4, h5⟩
    have hn : ¬ (r ≤ n ∧ n < r + 2 * m) := fun h => by
      rcases hxy.2 h with h | h <;> contradiction
    exact ⟨⟨ℓ - 1 - n, by omega⟩, by simp only; omega⟩

lemma hab_afterTopS (ℓ K m r s' : ℕ) (hrK : K ≤ r) (hr : r + 2 * m + (s' + 1) = ℓ) :
    ∀ n, (∃ i : Fin s', ℓ - 1 - (i : ℕ) = n) ↔
      n ∈ absS K ℓ (afterTop r m).C (afterTop r m).X' (afterTop r m).Y' := by
  intro n
  have hC : ∀ n, n ∈ (afterTop r m).C ↔ (n = r + 2 * m ∨ n < r) := by
    intro n; simp [afterTop]
  have hxy := memXY r m n
  simp only [absS, Finset.mem_filter, Finset.mem_Ico, hC]
  change _ ↔ _ ∧ ¬ _ ∧ ¬ (n ∈ (after r m).X') ∧ ¬ (n ∈ (after r m).Y')
  constructor
  · rintro ⟨i, rfl⟩
    have := i.2
    refine ⟨⟨by omega, by omega⟩, by omega, ?_, ?_⟩
    · intro h; have := hxy.1 (Or.inl h); omega
    · intro h; have := hxy.1 (Or.inr h); omega
  · rintro ⟨⟨h1, h2⟩, h3, h4, h5⟩
    have hn : ¬ (r ≤ n ∧ n < r + 2 * m) := fun h => by
      rcases hxy.2 h with h | h <;> contradiction
    exact ⟨⟨ℓ - 1 - n, by omega⟩, by simp only; omega⟩

/-- the column of the moved node `ℓ - 1 - s'` -/
noncomputable def wLast (ℓ K s' : ℕ) [Fact ℓ.Prime] : Fin K → ZMod ℓ :=
  Wnode ℓ K (ndAbs ℓ s' (Fin.last s'))

/-- Gram matrix of member 2's absent columns -/
noncomputable def N2 (ℓ K s' : ℕ) [Fact ℓ.Prime] : Matrix (Fin K) (Fin K) (ZMod ℓ) :=
  Gcols ℓ K (ndAbs ℓ s' ∘ Fin.castSucc) * (Gcols ℓ K (ndAbs ℓ s' ∘ Fin.castSucc))ᵀ

lemma gram_split (ℓ K s' : ℕ) [Fact ℓ.Prime] :
    Gcols ℓ K (ndAbs ℓ s') * (Gcols ℓ K (ndAbs ℓ s'))ᵀ =
      N2 ℓ K s' + (1 : ZMod ℓ) • vecMulVec (wLast ℓ K s') (wLast ℓ K s') := by
  ext a b
  simp [N2, Matrix.mul_apply, Fin.sum_univ_castSucc, vecMulVec_apply, wLast, Gcols,
    Function.comp_def]

theorem nv_hyb_pair_genS {Fr : Frame} (D : ModData Fr ℓ K) (m s' r : ℕ) (hrK : K ≤ r)
    (hr : r + 2 * m + (s' + 1) = ℓ)
    (hΔ : IsUnit ((WX ℓ K (after r m))ᵀ * WY ℓ K (after r m)).det)
    {x : ℚ} (hx : x ∈ S ℓ)
    (h1 : ((after r m).Full Fr x).det = 0) (h2 : ((afterTop r m).Full Fr x).det = 0) :
    (∀ (n : ℕ) (U : Matrix (Fin K) (Fin n) (ZMod ℓ)), SpansKer (WX ℓ K (after r m)) U →
        kgenR' (N2 ℓ K s') (wLast ℓ K s') (WX ℓ K (after r m)) (WY ℓ K (after r m)) U = 0) ∨
    (∀ (n : ℕ) (U : Matrix (Fin K) (Fin n) (ZMod ℓ)), SpansKer (WY ℓ K (after r m)) U →
        kgenL' (N2 ℓ K s') (wLast ℓ K s') (WX ℓ K (after r m)) (WY ℓ K (after r m)) U = 0) := by
  have hk : (after r m).k = m := after_k r m
  have hmem := memXY r m
  have hlow1 : ∀ n, n < K → n ∈ (after r m).C := fun n hn => by simp [after]; omega
  have hlow2 : ∀ n, n < K → n ∈ (afterTop r m).C := fun n hn => by simp [afterTop]; omega
  have hlt1 : ∀ n, n ∈ (after r m).C ∨ n ∈ (after r m).X' ∨ n ∈ (after r m).Y' → n < ℓ := by
    intro n hn
    rcases hn with hn | hn
    · simp [after] at hn; omega
    · have := (hmem n).1 hn; omega
  have hlt2 : ∀ n, n ∈ (afterTop r m).C ∨ n ∈ (afterTop r m).X' ∨ n ∈ (afterTop r m).Y' →
      n < ℓ := by
    intro n hn
    rcases hn with hn | hn
    · simp [afterTop] at hn; omega
    · have := (hmem n).1 hn; omega
  have hhi : ∀ n, n ∈ (after r m).X' ∨ n ∈ (after r m).Y' → K ≤ n := by
    intro n hn; have := (hmem n).1 hn; omega
  have hnd : Function.Injective (ndAbs ℓ s') := by
    intro i j hij; simp only [ndAbs] at hij; have := i.2; have := j.2; exact Fin.ext (by omega)
  have hnd2 : Function.Injective (ndAbs ℓ s' ∘ Fin.castSucc) := hnd.comp (Fin.castSucc_injective _)
  have b1 := reduction_G D (after r m) hlow1 hlt1 hhi (ndAbs ℓ s') hnd (hab_afterS ℓ K m r s' hrK hr)
    hx h1
  have b2 := reduction_G D (afterTop r m) hlow2 hlt2 hhi (ndAbs ℓ s' ∘ Fin.castSucc) hnd2
    (hab_afterTopS ℓ K m r s' hrK hr) hx h2
  rw [bordered_eq_borderedN, gram_split] at b1
  rw [bordered_eq_borderedN] at b2
  exact primal_pair (z := D.h + red ℓ x / D.κ) (τ := (1 : ZMod ℓ)) one_ne_zero (N2 ℓ K s')
    (by simp [N2, Matrix.transpose_mul, Matrix.transpose_transpose]) (wLast ℓ K s') _ _ hΔ b2 b1

end CatalanFrames.LambdaHybrid.NV
