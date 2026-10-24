module

public import CatalanArchive.CatalanFrames.LambdaHybrid.NV.Final
public import CatalanArchive.CatalanFrames.LambdaHybrid.NV.Mod3
public import CatalanArchive.CatalanFrames.LambdaHybrid.NV.Primal

/-!
# The member pair at general absent count (generic over the node levels)

`pair_red`: for `ModData3 Fr ℓ K T` and the geometries `after r m` / `afterTop r m` with
`r + 2m + S = ℓ` (`S = s' + 1`) and `K ≤ r`, both members vanishing gives the two `borderedN`
determinants of `primal_pair` (`N₂ = N2 ℓ K s'` the Gram matrix of the `S - 1` absent columns of
member 2, `w = wLast` the column of the node `ℓ - 1 - s'` that member 2 moves into `C`, a scale
`τ ≠ 0`).  Two level structures are covered: `T = ℓ` (two-level data, `ModData.toLevels`; all absent
nodes are mid nodes) and `S = T`, `ℓ + 1 = 2T` (P6: one absent mid node, the other absent nodes top).
The hypothesis-free closed-form end of the chain is `hyb_primal_false` (`FinalNV.lean`).
-/

@[expose] public section

open Finset Matrix CatalanCore CatalanCore.Rect

namespace CatalanArchive.CatalanFrames.LambdaHybrid.NV

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

section Scale

variable {F : Type*} [Field F] {A ι : Type*} [Fintype A] [DecidableEq A] [Fintype ι] [DecidableEq ι]

lemma borderedN_smul_factor (c z : F) (hc : c ≠ 0) (N : Matrix A A F) (WX WY : Matrix A ι F) :
    borderedN z (c • N) WX WY =
      fromBlocks (c • (1 : Matrix A A F)) 0 0 (1 : Matrix ι ι F) * borderedN (z / c) N WX WY *
        fromBlocks (1 : Matrix A A F) 0 0 (c⁻¹ • (1 : Matrix ι ι F)) := by
  simp only [borderedN, Matrix.fromBlocks_multiply]
  rw [Matrix.fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals
    simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul, Matrix.add_mul, Matrix.mul_add, smul_add, smul_zero, add_zero,
      zero_add]
    try (first | module | (match_scalars <;> (try field_simp) <;> (try ring)))

lemma det_borderedN_smul_eq_zero (c z : F) (hc : c ≠ 0) (N : Matrix A A F) (WX WY : Matrix A ι F)
    (h : (borderedN z (c • N) WX WY).det = 0) : (borderedN (z / c) N WX WY).det = 0 := by
  rw [borderedN_smul_factor c z hc, Matrix.det_mul, Matrix.det_mul, det_fromBlocks_zero₂₁,
    det_fromBlocks_zero₂₁] at h
  simp only [det_smul, Matrix.det_one, mul_one, one_mul] at h
  have hne : c ^ Fintype.card A * (c⁻¹) ^ Fintype.card ι ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hc) (pow_ne_zero _ (inv_ne_zero hc))
  have h2 : c ^ Fintype.card A * (c⁻¹) ^ Fintype.card ι * (borderedN (z / c) N WX WY).det = 0 := by
    linear_combination h
  exact (mul_eq_zero.1 h2).resolve_left hne

end Scale

variable {T : ℕ}

/-- the single absent mid column of member 1 -/
noncomputable def nd1 (ℓ s' : ℕ) : Fin 1 → ℕ := fun _ => ndAbs ℓ s' (Fin.last s')

lemma Ttop_eq_N2 (ℓ K s' T : ℕ) [Fact ℓ.Prime] (hT : s' + 1 = T) (hℓT : ℓ + 1 = 2 * T) :
    Ttop ℓ K T = N2 ℓ K s' := by
  have hnd : Function.Injective (ndAbs ℓ s' ∘ Fin.castSucc) := by
    intro i j hij; simp only [ndAbs, Function.comp_apply, Fin.coe_castSucc] at hij
    have := i.2; have := j.2; exact Fin.ext (by omega)
  have hab : ∀ n, (∃ i : Fin s', (ndAbs ℓ s' ∘ Fin.castSucc) i = n) ↔ n ∈ Ico T ℓ := by
    intro n
    simp only [Finset.mem_Ico, ndAbs, Function.comp_apply, Fin.coe_castSucc]
    constructor
    · rintro ⟨i, rfl⟩; have := i.2; omega
    · rintro ⟨h1, h2⟩; exact ⟨⟨ℓ - 1 - n, by omega⟩, by simp only; omega⟩
  ext a b
  have := sum_family (ndAbs ℓ s' ∘ Fin.castSucc) hnd (Ico T ℓ) hab
    (fun n => Wnode ℓ K n a * Wnode ℓ K n b)
  simp only [Ttop, N2, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Gcols]
  rw [← this]

lemma gram_nd1 (ℓ K s' : ℕ) [Fact ℓ.Prime] :
    Gcols ℓ K (nd1 ℓ s') * (Gcols ℓ K (nd1 ℓ s'))ᵀ =
      vecMulVec (wLast ℓ K s') (wLast ℓ K s') := by
  ext a b
  simp [Matrix.mul_apply, vecMulVec_apply, wLast, Gcols, nd1]

/-- **Generic member pair.**  `hcase`: either `T = ℓ` (two-level data) or `S = T`, `ℓ + 1 = 2T` (P6). -/
theorem pair_red {Fr : Frame} (D : ModData3 Fr ℓ K T) (m s' r : ℕ) (hrK : K ≤ r)
    (hr : r + 2 * m + (s' + 1) = ℓ) (hcase : T = ℓ ∨ (s' + 1 = T ∧ ℓ + 1 = 2 * T))
    {x : ℚ} (hx : x ∈ S ℓ)
    (h1 : ((after r m).Full Fr x).det = 0) (h2 : ((afterTop r m).Full Fr x).det = 0) :
    ∃ z τ : ZMod ℓ, τ ≠ 0 ∧
      (borderedN z (N2 ℓ K s') (WX ℓ K (after r m)) (WY ℓ K (after r m))).det = 0 ∧
      (borderedN z (N2 ℓ K s' + τ • vecMulVec (wLast ℓ K s') (wLast ℓ K s'))
        (WX ℓ K (after r m)) (WY ℓ K (after r m))).det = 0 := by
  have hrT : r + 2 * m < T := by rcases hcase with h | ⟨h, _⟩ <;> omega
  have hmem := memXY r m
  have hlow1 : ∀ n, n < K → n ∈ (after r m).C := fun n hn => by simp [after]; omega
  have hlow2 : ∀ n, n < K → n ∈ (afterTop r m).C := fun n hn => by simp [afterTop]; omega
  have hlt1 : ∀ n, n ∈ (after r m).C ∨ n ∈ (after r m).X' ∨ n ∈ (after r m).Y' → n < T := by
    intro n hn
    rcases hn with hn | hn
    · simp [after] at hn; omega
    · have := (hmem n).1 hn; omega
  have hlt2 : ∀ n, n ∈ (afterTop r m).C ∨ n ∈ (afterTop r m).X' ∨ n ∈ (afterTop r m).Y' →
      n < T := by
    intro n hn
    rcases hn with hn | hn
    · simp [afterTop] at hn; omega
    · have := (hmem n).1 hn; omega
  have hhi : ∀ n, n ∈ (after r m).X' ∨ n ∈ (after r m).Y' → K ≤ n := by
    intro n hn; have := (hmem n).1 hn; omega
  have hnd : Function.Injective (ndAbs ℓ s') := by
    intro i j hij; simp only [ndAbs] at hij; have := i.2; have := j.2; exact Fin.ext (by omega)
  have hnd2 : Function.Injective (ndAbs ℓ s' ∘ Fin.castSucc) := hnd.comp (Fin.castSucc_injective _)
  -- the common tail: member Grams are `ww^T + c₀ N₂` and `c₀ N₂`
  have H : ∀ c₀ : ZMod ℓ, c₀ ≠ 0 →
      (borderedN (D.h + red ℓ x / D.κ) (vecMulVec (wLast ℓ K s') (wLast ℓ K s') + c₀ • N2 ℓ K s')
        (WX ℓ K (after r m)) (WY ℓ K (after r m))).det = 0 →
      (borderedN (D.h + red ℓ x / D.κ) (c₀ • N2 ℓ K s')
        (WX ℓ K (after r m)) (WY ℓ K (after r m))).det = 0 →
      ∃ z τ : ZMod ℓ, τ ≠ 0 ∧
        (borderedN z (N2 ℓ K s') (WX ℓ K (after r m)) (WY ℓ K (after r m))).det = 0 ∧
        (borderedN z (N2 ℓ K s' + τ • vecMulVec (wLast ℓ K s') (wLast ℓ K s'))
          (WX ℓ K (after r m)) (WY ℓ K (after r m))).det = 0 := by
    intro c₀ hc b1 b2
    refine ⟨_ / c₀, c₀⁻¹, inv_ne_zero hc, det_borderedN_smul_eq_zero _ _ hc _ _ _ b2, ?_⟩
    refine det_borderedN_smul_eq_zero _ _ hc _ _ _ ?_
    have e : c₀ • (N2 ℓ K s' + c₀⁻¹ • vecMulVec (wLast ℓ K s') (wLast ℓ K s')) =
        vecMulVec (wLast ℓ K s') (wLast ℓ K s') + c₀ • N2 ℓ K s' := by
      rw [smul_add, smul_smul, mul_inv_cancel₀ hc, one_smul, add_comm]
    rw [e]; exact b1

  rcases hcase with hT | ⟨hT, hℓT⟩
  · have hT' := hT.symm
    subst hT'
    have b1 := reduction_G3 D (after r m) hlow1 hlt1 hhi (ndAbs ℓ s') hnd
        (hab_afterS ℓ K m r s' hrK hr) hx h1
    have b2 := reduction_G3 D (afterTop r m) hlow2 hlt2 hhi (ndAbs ℓ s' ∘ Fin.castSucc) hnd2
      (hab_afterTopS ℓ K m r s' hrK hr) hx h2
    rw [Ttop_self, smul_zero, add_zero, gram_split] at b1
    rw [Ttop_self, smul_zero, add_zero] at b2
    refine H 1 one_ne_zero ?_ ?_
    · rw [one_smul, add_comm (vecMulVec (wLast ℓ K s') (wLast ℓ K s')) (N2 ℓ K s')]
      rw [one_smul] at b1; exact b1
    · rw [one_smul]; exact b2
  · have hnd1 : Function.Injective (nd1 ℓ s') := fun i j _ => Subsingleton.elim i j
    have hnd0 : Function.Injective (fun i : Fin 0 => (0 : ℕ)) := fun i => i.elim0
    have hab1 : ∀ n, (∃ i, nd1 ℓ s' i = n) ↔
        n ∈ absS K T (after r m).C (after r m).X' (after r m).Y' := by
      intro n
      have hC : ∀ n, n ∈ (after r m).C ↔ n < r := by intro n; simp [after]
      simp only [absS, Finset.mem_filter, Finset.mem_Ico, hC]
      have hxy := hmem n
      constructor
      · rintro ⟨i, hi⟩
        have hv : n = ℓ - 1 - s' := by rw [← hi]; simp [nd1, ndAbs]
        subst hv
        refine ⟨⟨by omega, by omega⟩, by omega, ?_, ?_⟩
        · intro h; have := hxy.1 (Or.inl h); omega
        · intro h; have := hxy.1 (Or.inr h); omega
      · rintro ⟨⟨h1, h2⟩, h3, h4, h5⟩
        have hn : ¬ (r ≤ n ∧ n < r + 2 * m) := fun h => by
          rcases hxy.2 h with h | h <;> contradiction
        exact ⟨0, by simp only [nd1, ndAbs, Fin.val_last]; omega⟩
    have hab2 : ∀ n, (∃ i : Fin 0, (fun i : Fin 0 => (0 : ℕ)) i = n) ↔
        n ∈ absS K T (afterTop r m).C (afterTop r m).X' (afterTop r m).Y' := by
      intro n
      have hC : ∀ n, n ∈ (afterTop r m).C ↔ (n = r + 2 * m ∨ n < r) := by
        intro n; simp [afterTop]
      have hxy := hmem n
      simp only [absS, Finset.mem_filter, Finset.mem_Ico, hC]
      change _ ↔ _ ∧ ¬ _ ∧ ¬ (n ∈ (after r m).X') ∧ ¬ (n ∈ (after r m).Y')
      constructor
      · rintro ⟨i, _⟩; exact i.elim0
      · rintro ⟨⟨h1, h2⟩, h3, h4, h5⟩
        have hn : ¬ (r ≤ n ∧ n < r + 2 * m) := fun h => by
          rcases hxy.2 h with h | h <;> contradiction
        exfalso; omega
    have b1 := reduction_G3 D (after r m) hlow1 hlt1 hhi (nd1 ℓ s') hnd1 hab1 hx h1
    have b2 := reduction_G3 D (afterTop r m) hlow2 hlt2 hhi (fun i : Fin 0 => (0 : ℕ)) hnd0 hab2
      hx h2
    rw [gram_nd1, Ttop_eq_N2 ℓ K s' T hT hℓT] at b1
    rw [Ttop_eq_N2 ℓ K s' T hT hℓT] at b2
    have e0 : Gcols ℓ K (fun i : Fin 0 => (0 : ℕ)) *
        (Gcols ℓ K (fun i : Fin 0 => (0 : ℕ)))ᵀ = 0 := by
      ext a b; simp [Matrix.mul_apply]
    rw [e0, zero_add] at b2
    exact H _ (div_ne_zero D.hτ D.hκ) b1 b2

end CatalanArchive.CatalanFrames.LambdaHybrid.NV
