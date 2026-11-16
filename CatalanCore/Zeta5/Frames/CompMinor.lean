module

public import CatalanCore.Zeta5.Local.Val

@[expose] public section

/-!
# ZC11: the complementary-minor lemma (INTEGRALITY (I16))

If `v^G(A_{st}) ≥ w_s + w_t` with nonpositive half-integer weights `w`, and `L = U V` is an
integral matrix of inner dimension `r` (so rank `≤ r`), and `z` of the weights are zero, then
`v^G det(A + p⁻¹ L) ≥ 2 ∑ w - min(r, z)`.

Proof (no Laplace expansion): `det(A + p⁻¹ U V) = det [[A, -U], [p⁻¹ V, 1]]`, and in the Leibniz
expansion of the block matrix a permutation `σ` that sends `a` of the first `h` columns into the
`V`-rows has valuation `≥ 2 ∑ w - ∑_S w - ∑_T w - a` (`T` = those columns, `S` = the rows reached
from the `U`-columns, `|S| = |T| = a ≤ r`). Since each `1/2 + w ≤ (1/2)·[w = 0]`, the loss is at most
`min(r, z)`.
-/

open Finset Polynomial Matrix

namespace Apery

variable {p : ℕ} [hp : Fact p.Prime]

/-- Entry lower bounds for the block matrix `[[A, -U], [p⁻¹ V, 1]]`. -/
def blockLB {h r : ℕ} (w : Fin h → ℚ) : Fin h ⊕ Fin r → Fin h ⊕ Fin r → ℚ
  | Sum.inl s, Sum.inl t => w s + w t
  | Sum.inl _, Sum.inr _ => 0
  | Sum.inr _, Sum.inl _ => -1
  | Sum.inr _, Sum.inr _ => 0

/-- A nonpositive half-integer is `0` or `≤ -1/2`. -/
lemma half_le (x : ℚ) (hx : x ≤ 0) (hh : ∃ k : ℤ, x = k / 2) :
    1 / 2 + x ≤ (if x = 0 then 1 / 2 else 0) := by
  obtain ⟨k, rfl⟩ := hh
  by_cases h0 : (k : ℚ) / 2 = 0
  · rw [if_pos h0]; linarith
  · rw [if_neg h0]
    have hk : k ≤ -1 := by
      by_contra hc
      push Not at hc
      have : k = 0 := by
        have : (k : ℚ) ≤ 0 := by linarith
        have : k ≤ 0 := by exact_mod_cast this
        omega
      exact h0 (by simp [this])
    have : (k : ℚ) ≤ -1 := by exact_mod_cast hk
    linarith

/-- The combinatorial core: every permutation of the block index has weight sum at least
`2 ∑ w - min(r, z)`. -/
theorem blockLB_perm_ge {h r : ℕ} (w : Fin h → ℚ) (hw : ∀ s, w s ≤ 0)
    (hwh : ∀ s, ∃ k : ℤ, w s = k / 2) (σ : Equiv.Perm (Fin h ⊕ Fin r)) :
    2 * ∑ s, w s - min (r : ℚ) ((Finset.univ.filter fun s => w s = 0).card : ℚ) ≤
      ∑ j, blockLB w (σ j) j := by
  classical
  -- the columns of the first block that are sent to the second block
  set T : Finset (Fin h) := Finset.univ.filter (fun t => ∃ u, σ (Sum.inl t) = Sum.inr u) with hT
  -- the row hit by the first-block column `t`, when it is in the first block
  let ψ : Fin h → Fin h := fun t => match σ (Sum.inl t) with
    | Sum.inl s => s
    | Sum.inr _ => t
  have hψ : ∀ t ∉ T, σ (Sum.inl t) = Sum.inl (ψ t) := by
    intro t ht
    have : ¬ ∃ u, σ (Sum.inl t) = Sum.inr u := fun h' => ht (by simp [hT, h'])
    unfold ψ
    rcases hσ : σ (Sum.inl t) with s | u
    · rfl
    · exact absurd ⟨u, hσ⟩ this
  have hψinj : Set.InjOn ψ (↑(Tᶜ : Finset (Fin h))) := by
    intro a ha b hb hab
    have ha' : a ∉ T := by simpa using ha
    have hb' : b ∉ T := by simpa using hb
    have := hψ a ha'
    rw [hab, ← hψ b hb'] at this
    exact Sum.inl_injective (σ.injective this) |> fun e => e
  set S' : Finset (Fin h) := (Tᶜ).image ψ with hS'
  have hS'card : S'.card = (Tᶜ).card := Finset.card_image_of_injOn hψinj
  have hTc : (Tᶜ).card + T.card = h := by
    rw [Finset.card_compl_add_card]; simp
  have hS'c : (S'ᶜ).card = T.card := by
    have := Finset.card_compl_add_card S'
    simp only [Finset.card_univ, Fintype.card_fin] at this
    omega
  -- |T| ≤ r
  have hTr : T.card ≤ r := by
    have : T.card ≤ ((Finset.univ : Finset (Fin r)).image (Sum.inr : Fin r → Fin h ⊕ Fin r)).card := by
      refine Finset.card_le_card_of_injOn (fun t => σ (Sum.inl t)) (fun t ht => ?_) ?_
      · obtain ⟨u, hu⟩ : ∃ u, σ (Sum.inl t) = Sum.inr u := by simpa [hT] using ht
        simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range]
        exact ⟨u, hu.symm⟩
      · intro a _ b _ hab
        exact Sum.inl_injective (σ.injective hab)
    exact this.trans (Finset.card_image_le.trans (by simp))
  -- the sum over columns
  have hsum : ∑ j, blockLB w (σ j) j =
      ∑ t : Fin h, blockLB w (σ (Sum.inl t)) (Sum.inl t) := by
    rw [Fintype.sum_sum_type]
    have : ∑ u : Fin r, blockLB w (σ (Sum.inr u)) (Sum.inr u) = 0 := by
      refine Finset.sum_eq_zero fun u _ => ?_
      rcases σ (Sum.inr u) with s | u' <;> simp [blockLB]
    rw [this, add_zero]
  have hterm : ∀ t : Fin h, blockLB w (σ (Sum.inl t)) (Sum.inl t) =
      if t ∈ T then -1 else w (ψ t) + w t := by
    intro t
    by_cases ht : t ∈ T
    · rw [if_pos ht]
      obtain ⟨u, hu⟩ : ∃ u, σ (Sum.inl t) = Sum.inr u := by simpa [hT] using ht
      rw [hu]; simp [blockLB]
    · rw [if_neg ht, hψ t ht]; simp [blockLB]
  rw [hsum, Finset.sum_congr rfl fun t _ => hterm t]
  rw [Finset.sum_ite, Finset.sum_const, nsmul_eq_mul]
  have hfil : Finset.univ.filter (fun t => ¬ t ∈ T) = Tᶜ := by
    ext; simp
  have e1 : ∑ x ∈ Tᶜ, (w (ψ x) + w x) =
      ∑ s ∈ S', w s + ∑ x ∈ Tᶜ, w x := by
    rw [Finset.sum_add_distrib, hS', Finset.sum_image hψinj]
  have e2 : ∑ s ∈ S', w s = ∑ s, w s - ∑ s ∈ S'ᶜ, w s := by
    rw [eq_sub_iff_add_eq, add_comm, Finset.sum_compl_add_sum]
  have e3 : ∑ x ∈ Tᶜ, w x = ∑ s, w s - ∑ s ∈ T, w s := by
    rw [eq_sub_iff_add_eq, Finset.sum_compl_add_sum]
  rw [hfil, e1, e2, e3]
  -- the loss
  set Z : Finset (Fin h) := Finset.univ.filter fun s => w s = 0 with hZ
  have hθ : ∀ x, 1 / 2 + w x ≤ (if w x = 0 then (1 : ℚ) / 2 else 0) := fun x =>
    half_le (w x) (hw x) (hwh x)
  have hθ1 : ∀ x, 1 / 2 + w x ≤ 1 / 2 := fun x => by linarith [hw x]
  have hLsum : (T.card : ℚ) + ∑ s ∈ S'ᶜ, w s + ∑ s ∈ T, w s =
      ∑ t ∈ T, (1 / 2 + w t) + ∑ s ∈ S'ᶜ, (1 / 2 + w s) := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.sum_const,
      nsmul_eq_mul, nsmul_eq_mul, hS'c]
    push_cast; ring
  have hL1 : (T.card : ℚ) + ∑ s ∈ S'ᶜ, w s + ∑ s ∈ T, w s ≤ r := by
    rw [hLsum]
    have a1 : ∑ t ∈ T, (1 / 2 + w t) ≤ ∑ t ∈ T, (1 / 2 : ℚ) := Finset.sum_le_sum fun x _ => hθ1 x
    have a2 : ∑ s ∈ S'ᶜ, (1 / 2 + w s) ≤ ∑ s ∈ S'ᶜ, (1 / 2 : ℚ) :=
      Finset.sum_le_sum fun x _ => hθ1 x
    rw [Finset.sum_const, nsmul_eq_mul] at a1 a2
    rw [hS'c] at a2
    have : (T.card : ℚ) ≤ r := by exact_mod_cast hTr
    linarith
  have hL2 : (T.card : ℚ) + ∑ s ∈ S'ᶜ, w s + ∑ s ∈ T, w s ≤ (Z.card : ℚ) := by
    rw [hLsum]
    have a1 : ∑ t ∈ T, (1 / 2 + w t) ≤ ∑ t ∈ T, (if w t = 0 then (1 : ℚ) / 2 else 0) :=
      Finset.sum_le_sum fun x _ => hθ x
    have a2 : ∑ s ∈ S'ᶜ, (1 / 2 + w s) ≤ ∑ s ∈ S'ᶜ, (if w s = 0 then (1 : ℚ) / 2 else 0) :=
      Finset.sum_le_sum fun x _ => hθ x
    have b1 : ∑ t ∈ T, (if w t = 0 then (1 : ℚ) / 2 else 0) ≤ (Z.card : ℚ) / 2 := by
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      have : (T.filter fun t => w t = 0).card ≤ Z.card :=
        Finset.card_le_card (fun x hx => by
          simp only [Finset.mem_filter, hZ, Finset.mem_univ, true_and] at hx ⊢; exact hx.2)
      have : ((T.filter fun t => w t = 0).card : ℚ) ≤ Z.card := by exact_mod_cast this
      nlinarith
    have b2 : ∑ s ∈ S'ᶜ, (if w s = 0 then (1 : ℚ) / 2 else 0) ≤ (Z.card : ℚ) / 2 := by
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      have : (S'ᶜ.filter fun t => w t = 0).card ≤ Z.card :=
        Finset.card_le_card (fun x hx => by
          simp only [Finset.mem_filter, hZ, Finset.mem_univ, true_and] at hx ⊢; exact hx.2)
      have : ((S'ᶜ.filter fun t => w t = 0).card : ℚ) ≤ Z.card := by exact_mod_cast this
      nlinarith
    linarith
  have hmin : (T.card : ℚ) + ∑ s ∈ S'ᶜ, w s + ∑ s ∈ T, w s ≤
      min (r : ℚ) (Z.card : ℚ) := le_min hL1 hL2
  have hc : (Finset.univ.filter fun x => x ∈ T).card = T.card := by congr 1; ext; simp
  have hc' : ((Finset.univ.filter fun x => x ∈ T).card : ℚ) = T.card := by rw [hc]
  linarith

/-- **ZC11, the complementary-minor lemma.** Weights `w` nonpositive half-integers,
`v^G(A_{st}) ≥ w_s + w_t`, `U`, `V` integral (so `L = U V` is integral of rank `≤ r`), and
`z` = number of zero weights: `v^G det(A + p⁻¹ U V) ≥ 2 ∑ w - min(r, z)`. -/
theorem zc11_comp_minor {h r : ℕ} (A : Matrix (Fin h) (Fin h) ℚ[X])
    (U : Matrix (Fin h) (Fin r) ℚ) (V : Matrix (Fin r) (Fin h) ℚ) (w : Fin h → ℚ)
    (hw : ∀ s, w s ≤ 0) (hwh : ∀ s, ∃ k : ℤ, w s = k / 2)
    (hA : ∀ s t, GV p (A s t) (w s + w t))
    (hU : ∀ s u, VG p (U s u) 0) (hV : ∀ u t, VG p (V u t) 0) :
    GV p (A + (((p : ℚ)⁻¹ • (U * V)).map (C : ℚ →+* ℚ[X]))).det
      (2 * ∑ s, w s -
        min (r : ℚ) ((Finset.univ.filter fun s => w s = 0).card : ℚ)) := by
  classical
  set B : Matrix (Fin h) (Fin r) ℚ[X] := (-U).map (C : ℚ →+* ℚ[X])
  set Cm : Matrix (Fin r) (Fin h) ℚ[X] := ((p : ℚ)⁻¹ • V).map (C : ℚ →+* ℚ[X])
  have hdet : (A + (((p : ℚ)⁻¹ • (U * V)).map (C : ℚ →+* ℚ[X]))).det =
      (Matrix.fromBlocks A B Cm 1).det := by
    rw [det_fromBlocks_one₂₂]
    congr 1
    refine Matrix.ext fun s t => ?_
    simp only [B, Cm, Matrix.add_apply, Matrix.sub_apply, Matrix.mul_apply, Matrix.map_apply,
      Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul, map_sum, map_mul, map_neg,
      Finset.sum_neg_distrib, Finset.mul_sum]
    rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    refine Finset.sum_congr rfl fun u _ => ?_
    ring
  rw [hdet]
  have hinv : VG p ((p : ℚ)⁻¹) (-1) := by
    have := VG.primePow (p := p) (-1)
    simpa using this
  have hentry : ∀ i j, GV p (Matrix.fromBlocks A B Cm 1 i j) (blockLB w i j) := by
    intro i j
    rcases i with s | u <;> rcases j with t | u'
    · exact hA s t
    · simp only [Matrix.fromBlocks_apply₁₂, B, Matrix.map_apply, Matrix.neg_apply, blockLB]
      exact GV.C (hU s u').neg
    · simp only [Matrix.fromBlocks_apply₂₁, Cm, Matrix.map_apply, Matrix.smul_apply,
        smul_eq_mul, blockLB]
      exact (GV.C (hinv.mul (hV u t))).mono (by norm_num)
    · simp only [Matrix.fromBlocks_apply₂₂, blockLB]
      rw [Matrix.one_apply]
      split_ifs
      · exact (GV.C (p := p) VG.one)
      · exact GV.zero _
  rw [Matrix.det_apply]
  refine GV.sum _ fun σ _ => ?_
  have hprod : GV p (∏ j, Matrix.fromBlocks A B Cm 1 (σ j) j) (∑ j, blockLB w (σ j) j) :=
    GV.prod _ fun j _ => hentry (σ j) j
  have hprod' := hprod.mono (blockLB_perm_ge w hw hwh σ)
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
  · rw [hs, one_smul]; exact hprod'
  · rw [hs, Units.neg_smul, one_smul]; exact hprod'.neg

end Apery
