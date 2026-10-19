module

public import CatalanCore.Arith.Hybrid.DefC5Fam
public import CatalanCore.Arith.Hybrid.BorderDef

@[expose] public section

/-!
# Theorem C5 for the bordered member `afterTop r m` (MEM2C/C5)
-/

open Finset Polynomial CatalanCore CatalanCore.Rect CatalanCore.Basic CatalanCore.Linalg Matrix

namespace CatalanCore.Arith.Hybrid

section GleTop

variable {p : ℕ} [Fact p.Prime] {r m k : ℕ} (S : CSetup p r m k)

include S in
/-- Bordered twin of `gleAt_C5_lam`. -/
theorem gleAt_C5_lamTop {Fr : Frame} (I : HybInst Fr) (hL : LamData Fr) :
    GLE p (∑ a, wC p r k (Frame.hybRow r m a) + ∑ b, wC p r k (Frame.hybCol r m b) -
      (p + k - r - m) + topC I r m p) ((afterTop r m).fullPolyG Fr) := by
  classical
  haveI : Invertible (Mp5 p r k) := invMp5 S
  have hm0 := S.m0
  have hkp := S.kp
  have hrp := S.hrp
  have hLlo := S.hLlo
  have hLhi := S.hLhi
  have hs0 : s0L p k ≠ 0 := by
    unfold s0L rfX rfC
    rw [← map_add]
    exact (map_ne_zero_iff _ (RatFunc.algebraMap_injective (ZMod p))).2
      (Polynomial.X_add_C_ne_zero _)
  let u0 : BU p r k := ⟨⟨r - p, by omega⟩, ⟨le_rfl, by show r - p < k; omega⟩⟩
  let cX : ℕ → BU p r k := fun z =>
    if h : r ≤ z ∧ z < p + k then ⟨⟨z - p, by omega⟩, ⟨by show r - p ≤ z - p; omega, by show z - p < k; omega⟩⟩ else u0
  have cX_val : ∀ z, r ≤ z → z < p + k → ((cX z).1 : ℕ) = z - p := by
    intro z h1 h2
    simp only [cX, dif_pos (And.intro h1 h2)]
  let LX := Finset.univ.filter (fun x : Fin m => r + 2 * (x : ℕ) < p + k)
  let LY := Finset.univ.filter (fun y : Fin m => r + 2 * (y : ℕ) + 1 < p + k)
  have hcard : LX.card + LY.card = p + k - r := card_low S
  let Sc := T5 p r k m - Up5 p r k m * ⅟(Mp5 p r k) * Wp5 p r k m
  have h11 : Sc.toBlocks₁₁ = s0L p k • (1 : Matrix (BU p r k) (BU p r k) _) := by
    ext u w
    simp only [Matrix.toBlocks₁₁, Matrix.of_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    refine (ScUU S u w).trans ?_
    by_cases h : u = w <;> simp [h]
  have h22 : Sc.toBlocks₂₂ = 0 := by
    ext x y
    simp only [Matrix.toBlocks₂₂, Matrix.of_apply, Matrix.zero_apply]
    exact ScXY S x y
  have hSchur : T5 p r k m - Up5 p r k m * ⅟(Mp5 p r k) * Wp5 p r k m =
      fromBlocks (s0L p k • (1 : Matrix (BU p r k) (BU p r k) _)) Sc.toBlocks₁₂ Sc.toBlocks₂₁ 0 := by
    have hfb := Matrix.fromBlocks_toBlocks Sc
    rw [h11, h22] at hfb
    exact hfb.symm
  have hrank := rank_BbarC5_le (T5 p r k m) (Up5 p r k m) (Wp5 p r k m) (Mp5 p r k) (s0L p k) hs0
    Sc.toBlocks₂₁ Sc.toBlocks₁₂ hSchur LX LY (fun x => cX (r + 2 * (x : ℕ)))
    (fun y => cX (r + 2 * (y : ℕ) + 1)) (rfC p (eC p))
    (by
      intro x hx w
      have hx' := (Finset.mem_filter.1 hx).2
      have := x.2
      simp only [Matrix.toBlocks₂₁, Matrix.of_apply]
      refine (ScGx S w x hx').trans ?_
      by_cases h : w = cX (r + 2 * (x : ℕ))
      · have h2 := congrArg (fun t : BU p r k => (t.1 : ℕ)) h
        rw [cX_val _ (by omega) hx'] at h2
        rw [if_pos h, if_pos (by omega)]
      · rw [if_neg h, if_neg]
        intro h2
        apply h
        apply Subtype.ext; apply Fin.ext
        rw [cX_val _ (by omega) hx']
        omega)
    (by
      intro y hy w
      have hy' := (Finset.mem_filter.1 hy).2
      have := y.2
      simp only [Matrix.toBlocks₁₂, Matrix.of_apply]
      refine (ScGy S w y hy').trans ?_
      by_cases h : w = cX (r + 2 * (y : ℕ) + 1)
      · have h2 := congrArg (fun t : BU p r k => (t.1 : ℕ)) h
        rw [cX_val _ (by omega) hy'] at h2
        rw [if_pos h, if_pos (by omega)]
      · rw [if_neg h, if_neg]
        intro h2
        apply h
        apply Subtype.ext; apply Fin.ext
        rw [cX_val _ (by omega) hy']
        omega)
    (by
      intro x hx y hy
      have hx' := (Finset.mem_filter.1 hx).2
      have hy' := (Finset.mem_filter.1 hy).2
      have := x.2; have := y.2
      intro h
      have h2 := congrArg (fun t : BU p r k => (t.1 : ℕ)) h
      rw [cX_val _ (by omega) hx', cX_val _ (by omega) hy'] at h2
      omega)
  have hX : Fintype.card (Fin m) = m := Fintype.card_fin m
  have hLXm : LX.card ≤ m := by have := Finset.card_le_univ LX; rwa [Fintype.card_fin] at this
  have hLYm : LY.card ≤ m := by have := Finset.card_le_univ LY; rwa [Fintype.card_fin] at this
  have hBP := card_BU_BP (p := p) (r := r) (k := k)
  rw [hX] at hrank
  have hBT : BTc p r k m = (fromBlocks (T5 p r k m) (Up5 p r k m) (Wp5 p r k m) (Mp5 p r k)).submatrix
      (eU p r k m) (eU p r k m) := by
    ext a b
    rw [Matrix.submatrix_apply, BTc_eq]
  refine gle_fullTop_of_rank' I r m p (fun a => wC p r k (Frame.hybRow r m a))
    (fun b => wC p r k (Frame.hybCol r m b)) (BTc p r k m) (hred_C hL S) (p + k - r - m) ?_
  rw [hBT, Matrix.rank_submatrix]
  omega

end GleTop

open Classical in
/-- **Theorem C5 for the bordered member**: twin of `defHypT_C5`. -/
theorem defHypTop_C5 {Fr : Frame} (I : HybInst Fr) (hL : LamData Fr) (r m : ℕ) (T : ℕ → ℕ)
    (W : ℕ → Prop) (hSet : ∀ p : ℕ, p.Prime → W p → ∃ k, CSetup p r m k)
    (hT : ∀ p, p.Prime → p < Bnd I r m → tropExp I r m p ≤ T p)
    (hTd : ∀ p : ℕ, p.Prime → W p → ∀ k, CSetup p r m k →
      ∑ a, wC p r k (Frame.hybRow r m a) + ∑ b, wC p r k (Frame.hybCol r m b) ≤ T p) :
    DefHypTop I r m T (fun p => if W p then p + (p + 1) / 4 - r - m else 0) := by
  refine defHypTop_of_local T _ hT W (fun p hp => by simp [hp]) ?_
  intro p hp hb hWp
  obtain ⟨k, S⟩ := hSet p hp hWp
  haveI : Fact p.Prime := ⟨hp⟩
  have hd := hTd p hp hWp k S
  have h1 := wC_sum_ge (p := p) (r := r) (m := m) (k := k)
  have hg := gleAt_C5_lamTop S I hL
  have hk : (p + 1) / 4 = k := by have := S.hk; omega
  have hLhi := S.hLhi
  have hLlo := S.hLlo
  simp only [if_pos hWp, hk]
  exact fun [Fact p.Prime] => hg.mono (by omega)

end CatalanCore.Arith.Hybrid
