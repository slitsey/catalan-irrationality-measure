module

public import CatalanCore.Arith.Hybrid.DefC7Final

@[expose] public section

/-!
# Theorem C7 (j = 3, p ≡ 1 mod 4), dual form: `gleAt_C7_lam`
-/

open Finset Polynomial CatalanCore CatalanCore.Basic CatalanCore.Linalg Matrix

namespace CatalanCore.Arith.Hybrid

section Gle7

variable {p : ℕ} [Fact p.Prime] {r m k : ℕ} (S : CSetup7 p r m k)

lemma card_low7 (S : CSetup7 p r m k) :
    (Finset.univ.filter (fun x : Fin m => r + 2 * (x : ℕ) < p + k)).card +
      (Finset.univ.filter (fun y : Fin m => r + 2 * (y : ℕ) + 1 < p + k)).card = p + k - r := by
  have hLlo := S.hLlo; have hLhi := S.hLhi
  have e1 : (Finset.univ.filter (fun x : Fin m => r + 2 * (x : ℕ) < p + k)) =
      Finset.univ.filter (fun x : Fin m => (x : ℕ) < (p + k - r + 1) / 2) :=
    Finset.filter_congr fun x _ => by omega
  have e2 : (Finset.univ.filter (fun y : Fin m => r + 2 * (y : ℕ) + 1 < p + k)) =
      Finset.univ.filter (fun y : Fin m => (y : ℕ) < (p + k - r) / 2) :=
    Finset.filter_congr fun x _ => by omega
  rw [e1, e2, Fin.card_filter_val_lt, Fin.card_filter_val_lt]
  omega

include S in
/-- **Theorem C7 (j = 3, p ≡ 1 mod 4) at a prime `p < r`, in dual form** (λ-like frame). -/
theorem gleAt_C7_lam {Fr : Frame} (hL : LamData Fr) :
    GLE p (∑ a, wC7 p r k (Frame.hybRow r m a) + ∑ b, wC7 p r k (Frame.hybCol r m b) -
      (p + k - r - m)) (Fr.fullPoly r m) := by
  classical
  haveI : Invertible (Mp57 p r k) := invMp57 S
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
  let u0 : BU7 p r k := ⟨⟨r - p, by omega⟩, ⟨le_rfl, by show r - p < k; omega⟩⟩
  let cX : ℕ → BU7 p r k := fun z =>
    if h : r ≤ z ∧ z < p + k then ⟨⟨z - p, by omega⟩, ⟨by show r - p ≤ z - p; omega, by show z - p < k; omega⟩⟩ else u0
  have cX_val : ∀ z, r ≤ z → z < p + k → ((cX z).1 : ℕ) = z - p := by
    intro z h1 h2
    simp only [cX, dif_pos (And.intro h1 h2)]
  let LX := Finset.univ.filter (fun x : Fin m => r + 2 * (x : ℕ) < p + k)
  let LY := Finset.univ.filter (fun y : Fin m => r + 2 * (y : ℕ) + 1 < p + k)
  have hcard : LX.card + LY.card = p + k - r := card_low7 S
  let Sc := T57 p r k m - Up57 p r k m * ⅟(Mp57 p r k) * Wp57 p r k m
  have h11 : Sc.toBlocks₁₁ = s0L p k • (1 : Matrix (BU7 p r k) (BU7 p r k) _) := by
    ext u w
    simp only [Matrix.toBlocks₁₁, Matrix.of_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    refine (ScUU7 S u w).trans ?_
    by_cases h : u = w <;> simp [h]
  have h22 : Sc.toBlocks₂₂ = 0 := by
    ext x y
    simp only [Matrix.toBlocks₂₂, Matrix.of_apply, Matrix.zero_apply]
    exact ScXY7 S x y
  have hSchur : T57 p r k m - Up57 p r k m * ⅟(Mp57 p r k) * Wp57 p r k m =
      fromBlocks (s0L p k • (1 : Matrix (BU7 p r k) (BU7 p r k) _)) Sc.toBlocks₁₂ Sc.toBlocks₂₁ 0 := by
    have hfb := Matrix.fromBlocks_toBlocks Sc
    rw [h11, h22] at hfb
    exact hfb.symm
  have hrank := rank_BbarC5_le (T57 p r k m) (Up57 p r k m) (Wp57 p r k m) (Mp57 p r k) (s0L p k) hs0
    Sc.toBlocks₂₁ Sc.toBlocks₁₂ hSchur LX LY (fun x => cX (r + 2 * (x : ℕ)))
    (fun y => cX (r + 2 * (y : ℕ) + 1)) (rfC p (eC7 p))
    (by
      intro x hx w
      have hx' := (Finset.mem_filter.1 hx).2
      have := x.2
      simp only [Matrix.toBlocks₂₁, Matrix.of_apply]
      refine (ScGx7 S w x hx').trans ?_
      by_cases h : w = cX (r + 2 * (x : ℕ))
      · have h2 := congrArg (fun t : BU7 p r k => (t.1 : ℕ)) h
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
      refine (ScGy7 S w y hy').trans ?_
      by_cases h : w = cX (r + 2 * (y : ℕ) + 1)
      · have h2 := congrArg (fun t : BU7 p r k => (t.1 : ℕ)) h
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
      have h2 := congrArg (fun t : BU7 p r k => (t.1 : ℕ)) h
      rw [cX_val _ (by omega) hx', cX_val _ (by omega) hy'] at h2
      omega)
  have hX : Fintype.card (Fin m) = m := Fintype.card_fin m
  have hLXm : LX.card ≤ m := by have := Finset.card_le_univ LX; rwa [Fintype.card_fin] at this
  have hLYm : LY.card ≤ m := by have := Finset.card_le_univ LY; rwa [Fintype.card_fin] at this
  have hBP := card_BU_BP7 (p := p) (r := r) (k := k)
  rw [hX] at hrank
  have hBT : BTc7 p r k m = (fromBlocks (T57 p r k m) (Up57 p r k m) (Wp57 p r k m) (Mp57 p r k)).submatrix
      (eU7 p r k m) (eU7 p r k m) := by
    ext a b
    rw [Matrix.submatrix_apply, BTc7_eq]
  refine gle_full_of_rank p Fr r m (fun a => wC7 p r k (Frame.hybRow r m a))
    (fun b => wC7 p r k (Frame.hybCol r m b)) (BTc7 p r k m) (hred_C7 hL S) (p + k - r - m) ?_
  rw [hBT, Matrix.rank_submatrix]
  omega

end Gle7

end CatalanCore.Arith.Hybrid
