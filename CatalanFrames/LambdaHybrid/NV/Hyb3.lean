module

public import CatalanFrames.LambdaHybrid.NV.Mod3
public import CatalanFrames.LambdaHybrid.NV.FinalNV

/-!
# Hybrid nonvanishing for three-level data (`ModData3`)

* `det_borderedN_smul`: scaling `N` by `c ≠ 0` rescales `z` and the determinant (no `kgen` scaling
  lemma is needed: the scaling is absorbed into `z` and the rank-one weight `τ`).
* `pair_red3`: for `ModData3 Fr ℓ K T` with `s' + 1 = T`, `ℓ + 1 = 2T`, both members vanishing gives the
  two `borderedN` determinants of `primal_pair` (`N₂ = N2 ℓ K s'`, `w = wLast`, `τ = (κ/τ₀)`).
* `hyb_primal_false`: the primal pair hypothesis contradicts the Leonard/Darboux closed form.
* `nv_hyb_nonvanishing3`: the three-level analogue of `nv_hyb_nonvanishing`.
-/

@[expose] public section

open Finset Matrix CatalanCore CatalanCore.Rect

namespace CatalanFrames.LambdaHybrid.NV

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
section Pair3

variable {ℓ K T : ℕ} [Fact ℓ.Prime]

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

theorem pair_red3 {Fr : Frame} (D : ModData3 Fr ℓ K T) (m s' r : ℕ) (hrK : K ≤ r)
    (hr : r + 2 * m + (s' + 1) = ℓ) (hT : s' + 1 = T) (hℓT : ℓ + 1 = 2 * T)
    {x : ℚ} (hx : x ∈ S ℓ)
    (h1 : ((after r m).Full Fr x).det = 0) (h2 : ((afterTop r m).Full Fr x).det = 0) :
    ∃ z τ : ZMod ℓ, τ ≠ 0 ∧
      (borderedN z (N2 ℓ K s') (WX ℓ K (after r m)) (WY ℓ K (after r m))).det = 0 ∧
      (borderedN z (N2 ℓ K s' + τ • vecMulVec (wLast ℓ K s') (wLast ℓ K s'))
        (WX ℓ K (after r m)) (WY ℓ K (after r m))).det = 0 := by
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
  have hnd1 : Function.Injective (nd1 ℓ s') := fun i j _ => Subsingleton.elim i j
  have hnd0 : Function.Injective (fun i : Fin 0 => (0 : ℕ)) := fun i => i.elim0
  have hab1 : ∀ n, (∃ i, nd1 ℓ s' i = n) ↔ n ∈ absS K T (after r m).C (after r m).X' (after r m).Y' := by
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
    have hC : ∀ n, n ∈ (afterTop r m).C ↔ (n = r + 2 * m ∨ n < r) := by intro n; simp [afterTop]
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
  have b2 := reduction_G3 D (afterTop r m) hlow2 hlt2 hhi (fun i : Fin 0 => (0 : ℕ)) hnd0 hab2 hx h2
  have hc : D.τ₀ / D.κ ≠ 0 := div_ne_zero D.hτ D.hκ
  rw [gram_nd1, Ttop_eq_N2 ℓ K s' T hT hℓT] at b1
  rw [Ttop_eq_N2 ℓ K s' T hT hℓT] at b2
  have e0 : Gcols ℓ K (fun i : Fin 0 => (0 : ℕ)) * (Gcols ℓ K (fun i : Fin 0 => (0 : ℕ)))ᵀ = 0 := by
    ext a b; simp [Matrix.mul_apply]
  rw [e0, zero_add] at b2
  refine ⟨(D.h + red ℓ x / D.κ) / (D.τ₀ / D.κ), (D.τ₀ / D.κ)⁻¹, inv_ne_zero hc, ?_, ?_⟩
  · exact det_borderedN_smul_eq_zero _ _ hc _ _ _ b2
  · refine det_borderedN_smul_eq_zero _ _ hc _ _ _ ?_
    have e : (D.τ₀ / D.κ) • (N2 ℓ K s' + (D.τ₀ / D.κ)⁻¹ • vecMulVec (wLast ℓ K s') (wLast ℓ K s')) =
        vecMulVec (wLast ℓ K s') (wLast ℓ K s') + (D.τ₀ / D.κ) • N2 ℓ K s' := by
      rw [smul_add, smul_smul, mul_inv_cancel₀ hc, one_smul, add_comm]
    rw [e]; exact b1

end Pair3
section Final3

variable {ℓ K T : ℕ} [Fact ℓ.Prime]

/-- **Generic closed-form end of the hybrid chain, from the primal pair.**  The hypothesis `hred` is the
output of the mod-`ℓ` reduction of both members (`pair_red3`, or the two-level analogue); the rest is the
frame-free chain of `nv_hyb_nonvanishing` (primal lemma with general `τ`, `hDelta_after`, Leonard/Darboux). -/
theorem hyb_primal_false (m s' r : ℕ) (hm : 1 ≤ m) (hmK : m < K) (hrK : K ≤ r)
    (hr : r + 2 * m + (s' + 1) = ℓ) (hS : K - m ≤ s' + 1)
    (hred : ∃ z τ : ZMod ℓ, τ ≠ 0 ∧
      (borderedN z (N2 ℓ K s') (WX ℓ K (after r m)) (WY ℓ K (after r m))).det = 0 ∧
      (borderedN z (N2 ℓ K s' + τ • vecMulVec (wLast ℓ K s') (wLast ℓ K s'))
        (WX ℓ K (after r m)) (WY ℓ K (after r m))).det = 0) : False := by
  obtain ⟨z, τ, hτ, hb2, hb1⟩ := hred
  have hΔ := hDelta_after (ℓ := ℓ) K m r (by omega) hmK.le hrK (by omega)
  have hpair := primal_pair hτ (N2 ℓ K s')
    (by simp [N2, Matrix.transpose_mul, Matrix.transpose_transpose]) (wLast ℓ K s') _ _ hΔ hb2 hb1
  have KS : CatalanCore.Star.Leonard.KSTransfer ℓ m := CatalanCore.Star.Leonard.ks_transfer_of_LpG m hm fun n' hn' hl =>
    CatalanCore.Star.Leonard.LpG_good m n' hm hn' hl
  obtain ⟨n, rfl⟩ : ∃ n, K = m + n := ⟨K - m, by omega⟩
  have hn : 1 ≤ n := by omega
  have huu := CatalanCore.Star.Leonard.uu_good m hm KS n hn (s' + 1) (by omega) (by omega)
  have hkg := CatalanCore.Star.Leonard.kgen_good m n (s' + 1) hm hn (by omega) (by omega) huu
  have hl : (s' + 1) + (m + n) + 2 * m ≤ ℓ := by omega
  have hR := CatalanCore.Star.Leonard.kgen_LU_of_good (ℓ := ℓ) (m + n) m (s' + 1) _ hmK hS
    (by omega) hkg
  have hL := CatalanCore.Star.Leonard.kgenL_LU_of_good (ℓ := ℓ) (m + n) m (s' + 1) _ hmK hS hl
    (by omega) hkg
  obtain ⟨U, hU, hne⟩ := kgenR'_ne_zero_of_LU (m + n) m r s' hmK hrK hr hR
  obtain ⟨U', hU', hne'⟩ := kgenL'_ne_zero_of_LU (m + n) m r s' hmK hrK hr (by simpa using hL)
  rcases hpair with h | h
  · exact hne (h _ U hU)
  · exact hne' (h _ U' hU')

/-- **Three-level hybrid nonvanishing** (analogue of `nv_hyb_nonvanishing` for `ModData3`, absent count
`s' + 1 = T = (ℓ+1)/2`). -/
theorem nv_hyb_nonvanishing3 {Fr : Frame} (D : ModData3 Fr ℓ K T) (m s' r : ℕ)
    (hm : 1 ≤ m) (hmK : m < K) (hrK : K ≤ r) (hr : r + 2 * m + (s' + 1) = ℓ)
    (hS : K - m ≤ s' + 1) (hT : s' + 1 = T) (hℓT : ℓ + 1 = 2 * T)
    {x : ℚ} (hx : x ∈ CatalanCore.S ℓ)
    (h1 : ((after r m).Full Fr x).det = 0) (h2 : ((afterTop r m).Full Fr x).det = 0) : False :=
  hyb_primal_false m s' r hm hmK hrK hr hS (pair_red3 D m s' r hrK hr hT hℓT hx h1 h2)

#print axioms nv_hyb_nonvanishing3

end Final3

end CatalanFrames.LambdaHybrid.NV
