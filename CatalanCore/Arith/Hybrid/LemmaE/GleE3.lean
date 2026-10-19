module

public import CatalanCore.Arith.Hybrid.LemmaE.GleE2

@[expose] public section

/-!
# Lemma E, class 1: the rank bound (`rank BE ≤ r`) from the label evaluations
-/

open Finset Polynomial CatalanCore CatalanCore.Basic Matrix

namespace CatalanCore.Arith.Hybrid

section Main

variable {p : ℕ} [Fact p.Prime] {Fr : Frame} {r m j k : ℕ}

/-- The `U × B₁` entries. -/
def VZE (p j : ℕ) [Fact p.Prime] (a i : ℕ) : ZMod p :=
  (16 * ((i : ZMod p) - a))⁻¹ * (-(4 * ((j : ℕ) : ZMod p)⁻¹))

/-- **The rank count of Lemma E (class 1).** -/
theorem rank_BE_le (S : ESetup p r m j k) (sU : ZMod p)
    (hj : ((j : ℕ) : ZMod p) ≠ 0) (he : -(4 * ((j : ℕ) : ZMod p)⁻¹) + 1 ≠ 0)
    (hUU : ∀ a b : ℕ, r - p ≤ a → a < k → r - p ≤ b → b < k →
      TE p j r k a b = (16 : ZMod p)⁻¹ * ((if a = b then sU else 0) +
        ∑ c ∈ Ico k p, ((c : ZMod p) - a)⁻¹ * ((c : ZMod p) - b)⁻¹)) :
    (BE p j r m k).rank ≤ r := by
  have hkp := S.hkp
  have hpr := S.hpr
  have hrk := S.hrk
  have hN := S.hN
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have h16 : (16 : ZMod p) ≠ 0 := by
    have : (16 : ZMod p) = 4 * 4 := by norm_num
    rw [this]; exact mul_ne_zero (four_ne_zmod p S.p5) (four_ne_zmod p S.p5)
  have hm2 : 2 * m < k := by omega
  let cXf : Fin m → UE p r k := fun x =>
    ⟨⟨r + 2 * (x : ℕ) - p, by have := x.2; omega⟩, by have := x.2; show r - p ≤ r + 2 * (x : ℕ) - p ∧ r + 2 * (x : ℕ) - p < k; omega⟩
  let cYf : Fin m → UE p r k := fun y =>
    ⟨⟨r + 2 * (y : ℕ) + 1 - p, by have := y.2; omega⟩, by have := y.2; show r - p ≤ r + 2 * (y : ℕ) + 1 - p ∧ r + 2 * (y : ℕ) + 1 - p < k; omega⟩
  set e0 : ZMod p := (16 : ZMod p)⁻¹ * (-(4 * ((j : ℕ) : ZMod p)⁻¹) + 1) with he0
  set π10 : ZMod p := (((j : ℕ) : ZMod p)⁻¹) ^ 2 with hπ10
  set π20 : ZMod p := (((j : ℕ) : ZMod p)⁻¹) ^ 2 - (16 : ZMod p)⁻¹ with hπ20
  have he0n : e0 ≠ 0 := mul_ne_zero (inv_ne_zero h16) he
  have hπ10n : π10 ≠ 0 := pow_ne_zero 2 (inv_ne_zero hj)
  set Bm := BmE p j r m k with hBm
  have hfb : fromBlocks Bm.toBlocks₁₁ Bm.toBlocks₁₂ Bm.toBlocks₂₁ Bm.toBlocks₂₂ = Bm :=
    Matrix.fromBlocks_toBlocks Bm
  have hlo1 : ∀ c : PE p r k, ((c.1 : ℕ) < r - p) → tauP S c ≠ c ∧ ¬ (((tauP S c).1 : ℕ) < r - p) :=
    fun c h => tauP_lo S c h
  -- zone rows/columns of Up, Wp vanish
  have hUpX : ∀ (x : Fin m) (c : PE p r k), Bm.toBlocks₁₂ (Sum.inr x) c = 0 := by
    intro x c
    rw [BmE_toBlocks₁₂_r, BE_zl, TE_big, rfC_zero]
    · have := c.1.2; have := x.2; omega
    · rw [wE_Z (by omega), wE_c]
  have hWpY : ∀ (c : PE p r k) (y : Fin m), Bm.toBlocks₂₁ c (Sum.inr y) = 0 := by
    intro c y
    rw [BmE_toBlocks₂₁_r, BE_lz, TE_big, rfC_zero]
    · have := c.1.2; have := y.2; omega
    · rw [wE_c, wE_Z (by omega)]
  -- U × P entries
  have hUP : ∀ (a : UE p r k) (c : PE p r k), Bm.toBlocks₁₂ (Sum.inl a) c =
      rfC p (if (a.1 : ℕ) < c.1 then (16 * (((c.1 : ℕ) : ZMod p) - (a.1 : ℕ)))⁻¹ *
          singE p j k a.1 c.1
        else (16 * (((a.1 : ℕ) : ZMod p) - (c.1 : ℕ)))⁻¹ * singE p j k c.1 a.1) := by
    intro a c
    rw [BmE_toBlocks₁₂_l, BE_ll]
    have hne : ¬ (a.1 = c.1 ∧ wE p r k (a.1 : ℕ) = 0) := by
      rintro ⟨h, _⟩
      have h2 := c.2
      rw [← h] at h2
      exact h2 a.2
    rw [if_neg hne, add_zero, TE_UP S a.2.1 a.2.2 c.1.2 c.2]
  have hUpLo : ∀ (a : UE p r k) (c : PE p r k), ((c.1 : ℕ) < r - p) →
      Bm.toBlocks₁₂ (Sum.inl a) c = 0 := by
    intro a c hc
    rw [hUP]
    have h1 : ¬ ((a.1 : ℕ) < c.1) := by have := a.2.1; omega
    rw [if_neg h1, singE_zero hkp a.2.2]
    simp [rfC_zero]
  have hWp : ∀ (c : PE p r k) (a : UE p r k),
      Bm.toBlocks₂₁ c (Sum.inl a) = Bm.toBlocks₁₂ (Sum.inl a) c := by
    intro c a
    rw [BmE_toBlocks₂₁_l, BmE_toBlocks₁₂_l, BE_ll, BE_ll, TE_symm' (c.1 : ℕ)]
    have hne : ¬ (c.1 = a.1 ∧ wE p r k (c.1 : ℕ) = 0) := by
      rintro ⟨h, _⟩
      have h2 := c.2
      rw [h] at h2
      exact h2 a.2
    have hne' : ¬ (a.1 = c.1 ∧ wE p r k (a.1 : ℕ) = 0) := by
      rintro ⟨h, _⟩
      exact hne ⟨h.symm, by rw [wE_c]; omega⟩
    rw [if_neg hne, if_neg hne']
  have hTXY : ∀ (x y : Fin m), Bm.toBlocks₁₁ (Sum.inr x) (Sum.inr y) = 0 := by
    intro x y
    rw [BmE_toBlocks₁₁_rr, BE_zz, TE_big, rfC_zero]
    · have := x.2; have := y.2; omega
    · rw [wE_Z (by omega), wE_Z (by omega)]; omega
  have hGx : ∀ (x : Fin m) (u : UE p r k), Bm.toBlocks₁₁ (Sum.inr x) (Sum.inl u) =
      if u = cXf x then rfCH p e0 else 0 := by
    intro x u
    rw [BmE_toBlocks₁₁_rl, BE_zl, TE_symm', TE_UZ S u.2.1 u.2.2 (by omega)]
    have hiff : (r + 2 * (x : ℕ) - (u.1 : ℕ) = p) ↔ u = cXf x := by
      have := x.2; have := u.1.2; have := u.2.1
      constructor
      · intro h; apply Subtype.ext; apply Fin.ext; show (u.1 : ℕ) = r + 2 * (x : ℕ) - p; omega
      · intro h; have := congrArg (fun t : UE p r k => (t.1 : ℕ)) h
        simp only [cXf] at this; omega
    by_cases h : u = cXf x
    · rw [if_pos (hiff.2 h), if_pos h]; rfl
    · rw [if_neg (fun hh => h (hiff.1 hh)), if_neg h, rfC_zero]
  have hGy : ∀ (u : UE p r k) (y : Fin m), Bm.toBlocks₁₁ (Sum.inl u) (Sum.inr y) =
      if u = cYf y then rfCH p e0 else 0 := by
    intro u y
    rw [BmE_toBlocks₁₁_lr, BE_lz, TE_UZ S u.2.1 u.2.2 (by omega)]
    have hiff : (r + 2 * (y : ℕ) + 1 - (u.1 : ℕ) = p) ↔ u = cYf y := by
      have := y.2; have := u.1.2; have := u.2.1
      constructor
      · intro h; apply Subtype.ext; apply Fin.ext; show (u.1 : ℕ) = r + 2 * (y : ℕ) + 1 - p; omega
      · intro h; have := congrArg (fun t : UE p r k => (t.1 : ℕ)) h
        simp only [cYf] at this; omega
    by_cases h : u = cYf y
    · rw [if_pos (hiff.2 h), if_pos h]; rfl
    · rw [if_neg (fun hh => h (hiff.1 hh)), if_neg h, rfC_zero]
  have hcXY : ∀ (x y : Fin m), cXf x ≠ cYf y := by
    intro x y h
    have := congrArg (fun t : UE p r k => (t.1 : ℕ)) h
    simp only [cXf, cYf] at this
    have := x.2; have := y.2; omega
  -- the pair block
  have hMp : Bm.toBlocks₂₂ = pairMat (tauP S) (fun c : PE p r k => (c.1 : ℕ) < r - p)
      (rfCH p e0) (rfCH p π10) (rfCH p π20) := by
    ext c c'
    rw [BmE_toBlocks₂₂, BE_ll]
    have hne : ¬ (c.1 = c'.1 ∧ wE p r k (c.1 : ℕ) = 0) := by
      rintro ⟨_, h⟩; rw [wE_c] at h; omega
    rw [if_neg hne, add_zero, TE_P S c.1.2 c.2 c'.1.2 c'.2]
    simp only [pairMat, Matrix.of_apply]
    by_cases h1 : c' = c
    · subst h1
      simp only [if_true]
      by_cases h2 : (c'.1 : ℕ) < r - p
      · simp [h2, rfC_zero]
      · have hfix : tauN p r (c'.1 : ℕ) = c'.1 ↔ tauP S c' = c' := by
          rw [tauP_fix S c']
          have := c'.2; have := c'.1.2
          unfold tauN; split_ifs <;> omega
        by_cases h3 : tauP S c' = c'
        · rw [if_neg h2, if_pos (hfix.2 h3), if_neg h2, if_pos h3]; rfl
        · rw [if_neg h2, if_neg (fun h => h3 (hfix.1 h)), if_neg h2, if_neg h3]
          simp [π20, rfCH, rfC]
    · have h1' : (c'.1 : ℕ) ≠ c.1 := fun h => h1 (Subtype.ext (Fin.ext h))
      rw [if_neg h1', if_neg h1]
      by_cases h3 : c' = tauP S c
      · have h3' : (c'.1 : ℕ) = tauN p r c.1 := by rw [h3]; rfl
        rw [if_pos h3', if_pos h3]; rfl
      · have h3' : (c'.1 : ℕ) ≠ tauN p r c.1 := fun h => h3 (Subtype.ext (Fin.ext (by rw [h]; rfl)))
        rw [if_neg h3', if_neg h3, rfC_zero]
  have hTUU : ∀ a a' : UE p r k, Bm.toBlocks₁₁ (Sum.inl a) (Sum.inl a') =
      (if a = a' then rfX p + rfCH p ((16 : ZMod p)⁻¹ * sU) else 0) +
      (rfCH p π10)⁻¹ * ∑ c : PE p r k, (if tauP S c = c then
        Bm.toBlocks₁₂ (Sum.inl a) c * Bm.toBlocks₁₂ (Sum.inl a') c else 0) := by
    intro a a'
    rw [BmE_toBlocks₁₁_ll, BE_ll]
    have hsum : ∑ c : PE p r k, (if tauP S c = c then
        Bm.toBlocks₁₂ (Sum.inl a) c * Bm.toBlocks₁₂ (Sum.inl a') c else 0) =
        rfCH p (∑ i ∈ Ico k p, VZE p j (a.1 : ℕ) i * VZE p j (a'.1 : ℕ) i) := by
      have h1 : ∀ c : PE p r k, (if tauP S c = c then
          Bm.toBlocks₁₂ (Sum.inl a) c * Bm.toBlocks₁₂ (Sum.inl a') c else 0) =
          (if tauP S c = c then
            rfCH p (VZE p j (a.1 : ℕ) (c.1 : ℕ) * VZE p j (a'.1 : ℕ) (c.1 : ℕ)) else 0) := by
        intro c
        by_cases h : tauP S c = c
        · rw [if_pos h, if_pos h]
          have hfx := (tauP_fix S c).1 h
          rw [hUP a c, hUP a' c, if_pos (by have := a.2.2; omega),
            if_pos (by have := a'.2.2; omega),
            singE_k a.2.2 hfx.1 hfx.2, singE_k a'.2.2 hfx.1 hfx.2, rfC_eq, rfC_eq, ← map_mul]
          rfl
        · rw [if_neg h, if_neg h]
      rw [Finset.sum_congr rfl (fun c _ => h1 c)]
      rw [sum_fixed S (fun i => rfCH p (VZE p j (a.1 : ℕ) i * VZE p j (a'.1 : ℕ) i)), map_sum]
    have key : (16 : ZMod p)⁻¹ * ∑ c ∈ Ico k p,
        ((c : ZMod p) - ((a.1 : ℕ) : ℕ))⁻¹ * ((c : ZMod p) - ((a'.1 : ℕ) : ℕ))⁻¹ =
        π10⁻¹ * ∑ i ∈ Ico k p, VZE p j (a.1 : ℕ) i * VZE p j (a'.1 : ℕ) i := by
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [VZE, hπ10, mul_inv]
      field_simp
      ring
    have hU := hUU (a.1 : ℕ) (a'.1 : ℕ) a.2.1 a.2.2 a'.2.1 a'.2.2
    rw [hsum, hU]
    have hmul : (rfCH p π10)⁻¹ * rfCH p (∑ i ∈ Ico k p, VZE p j (a.1 : ℕ) i * VZE p j (a'.1 : ℕ) i)
        = rfCH p ((16 : ZMod p)⁻¹ * ∑ c ∈ Ico k p,
          ((c : ZMod p) - ((a.1 : ℕ) : ℕ))⁻¹ * ((c : ZMod p) - ((a'.1 : ℕ) : ℕ))⁻¹) := by
      rw [key, map_mul, map_inv₀]
    rw [hmul]
    by_cases hh : a = a'
    · subst hh
      simp only [wE_u a, eq_self_iff_true, and_self, if_true]
      rw [rfC_eq, mul_add, map_add]
      abel
    · have hh' : (a.1 : ℕ) ≠ a'.1 := fun h => hh (Subtype.ext (Fin.ext h))
      have hh'' : ¬ (a.1 = a'.1 ∧ wE p r k (a.1 : ℕ) = 0) := fun h => hh (Subtype.ext h.1)
      rw [if_neg hh'', if_neg hh, if_neg hh', rfC_eq, zero_add, zero_add, add_zero]
  have hrk' := rank_E_abs Bm.toBlocks₁₁ Bm.toBlocks₁₂ Bm.toBlocks₂₁ (tauP S)
    (fun c : PE p r k => (c.1 : ℕ) < r - p) (rfCH p e0) (rfCH p π10) (rfCH p π20)
    (rfX p + rfCH p ((16 : ZMod p)⁻¹ * sU)) (rfCH p e0) (tauP_invol S) hlo1
    (fun c h1 h2 => tauP_hi S c h1 h2)
    ((map_ne_zero (rfCH p)).2 he0n) ((map_ne_zero (rfCH p)).2 hπ10n) (hs0_ne _)
    hUpX hWpY hUpLo hWp hTUU hTXY cXf cYf hGx hGy hcXY Bm.toBlocks₂₂ hMp
  rw [hfb] at hrk'
  have hr1 : Bm.rank = (BE p j r m k).rank := Matrix.rank_submatrix _ _ _
  have := card_UP p r k
  omega

end Main

end CatalanCore.Arith.Hybrid
