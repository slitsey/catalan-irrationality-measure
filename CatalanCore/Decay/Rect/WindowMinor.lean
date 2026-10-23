module

public import CatalanCore.Decay.Rect.WindowNodes
public import CatalanCore.Rect.CommonMinor

@[expose] public section

open Finset Polynomial Matrix



namespace CatalanCore

variable {sl : ℝ}

open Decay

/-- The original energy estimate with an arbitrary subset of the common nodes.
The only extra price is `cc*r` for each forced deletion. -/
theorem window_rect_common {ι : Type} [Fintype ι] [DecidableEq ι]
    {Fr : Frame} (hFr : Fr.DecayOKs' sl) {e : ℝ} (he0 : 0 < e) (he1 : e < 1)
    {m0 : ℝ} (hm0xs : m0 ≤ Fr.xs) (hm0μ : ∀ i, m0 ≤ Fr.μ i) {r m N0 : ℕ} {R : ℝ}
    (hR : (N0 : ℝ) ≤ R) {T0 cc : ℝ} (c : ι → Fin r) (hc : Function.Injective c)
    (hEn : ∀ (k : ℕ) (s : Fin k → Fin (r + m)), Function.Injective s →
        (∀ b : Fin (r + m), r ≤ (b : ℕ) → ∃ i, s i = b) →
        Frame.RectEnergy Fr sl N0 k e m0 (max (Real.log Fr.Aco) 0) (T0 + r * (((r : ℝ) + m) - k) * cc)
          (fun i => xnode r (s i)) (fun i => ynode r (s i)))
    {t : ℝ} (ht : |t| ≤ Real.exp (-cc * r)) :
    |(Rect.FullN Fr (fun a => (c a : ℕ)) (fun i : Fin m => r + 2 * (i : ℕ))
      (fun i : Fin m => r + 2 * (i : ℕ) + 1) (Fr.const + t : ℝ)).det| ≤
      2 ^ r * Real.exp (T0 + cc * r * ((r : ℝ) - Fintype.card ι) + ((r : ℝ) + m) *
        Real.log (Fr.Wabs * R + (Fr.Wabs * ⌈(Fr.xs : ℝ)⌉₊ +
          2 * (Fr.Aco ^ e / Frame.betaE sl e) + 1))) := by
  classical
  rw [Rect.det_fullN_expansion Fr _ _ _ (Fr.const : ℝ) t]
  let L0 := Real.log (Fr.Wabs * R + (Fr.Wabs * ⌈(Fr.xs : ℝ)⌉₊ +
    2 * (Fr.Aco ^ e / Frame.betaE sl e) + 1))
  let B := Real.exp (T0 + cc * r * ((r : ℝ) - Fintype.card ι) + ((r : ℝ) + m) * L0)
  have hι : Fintype.card ι ≤ r := by simpa using Fintype.card_le_of_injective c hc
  have hq : |t| * Real.exp (cc * r) ≤ 1 := by
    calc
      _ ≤ Real.exp (-cc * r) * Real.exp (cc * r) := mul_le_mul_of_nonneg_right ht (by positivity)
      _ = 1 := by rw [← Real.exp_add]; simp
  have hterm : ∀ S ∈ (Finset.univ : Finset ι).powerset,
      |t ^ (Fintype.card ι - S.card) * (Rect.FullN Fr (fun a : S => (c a.1 : ℕ))
        (fun i : Fin m => r + 2 * (i : ℕ)) (fun i : Fin m => r + 2 * (i : ℕ) + 1)
        (Fr.const : ℝ)).det| ≤ B := by
    intro S _
    have hS : S.card ≤ Fintype.card ι := Finset.card_le_univ S
    let k := S.card + m
    let eq : (S ⊕ Fin m) ≃ Fin k := Fintype.equivFinOfCardEq (by simp [k])
    let cs : S → Fin r := fun a => c a.1
    have hcs : Function.Injective cs := hc.comp Subtype.val_injective
    let s : Fin k → Fin (r + m) := fun i => Rect.commonIdx r m cs (eq.symm i)
    have hs : Function.Injective s := (Rect.commonIdx_injective r m cs hcs).comp eq.symm.injective
    have hkeep : ∀ b : Fin (r + m), r ≤ (b : ℕ) → ∃ i, s i = b := by
      intro b hb
      refine ⟨eq (Sum.inr ⟨(b : ℕ) - r, by have := b.isLt; omega⟩), ?_⟩
      simp only [s, Equiv.symm_apply_apply, Rect.commonIdx, Sum.elim_inr]
      exact Fin.ext (by simp; omega)
    have hdet : (Rect.FullN Fr (fun a : S => (c a.1 : ℕ))
        (fun i : Fin m => r + 2 * (i : ℕ)) (fun i : Fin m => r + 2 * (i : ℕ) + 1)
        (Fr.const : ℝ)).det = (Matrix.of fun i j : Fin k =>
          Fr.Tent (xnode r (s i)) (ynode r (s j))).det := by
      rw [Rect.fullN_common_const Fr r m cs hcs]
      exact (Matrix.det_submatrix_equiv_self eq.symm _).symm
    have hxinj : Function.Injective (fun i => xnode r (s i)) :=
      fun a b h => hs (Fin.ext (xnode_inj r h))
    have hyinj : Function.Injective (fun i => ynode r (s i)) :=
      fun a b h => hs (Fin.ext (ynode_inj r h))
    have hkN : k ≤ r + m := by dsimp [k]; omega
    have hN := Frame.theoremN_rect hFr he0 he1 hm0xs hm0μ hkN hR hxinj hyinj (hEn k s hs hkeep)
    have hsub : ((Fintype.card ι - S.card : ℕ) : ℝ) = (Fintype.card ι : ℝ) - S.card :=
      Nat.cast_sub hS
    have hk : (k : ℝ) = S.card + m := by simp [k]
    have hexp : Real.exp (T0 + r * (((r : ℝ) + m) - k) * cc + ((r + m : ℕ) : ℝ) * L0) =
        Real.exp (cc * r) ^ (Fintype.card ι - S.card) * B := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      rw [hsub, hk]
      push_cast
      ring
    rw [abs_mul, abs_pow, hdet]
    change |t| ^ (Fintype.card ι - S.card) * _ ≤ B
    have hN' : |(Matrix.of fun i j : Fin k => Fr.Tent (xnode r (s i)) (ynode r (s j))).det| ≤
        Real.exp (cc * r) ^ (Fintype.card ι - S.card) * B := by
      rw [← hexp]; exact hN
    calc
      _ ≤ |t| ^ (Fintype.card ι - S.card) * (Real.exp (cc * r) ^ (Fintype.card ι - S.card) * B) :=
        mul_le_mul_of_nonneg_left hN' (by positivity)
      _ = (|t| * Real.exp (cc * r)) ^ (Fintype.card ι - S.card) * B := by rw [mul_pow]; ring
      _ ≤ 1 * B := mul_le_mul_of_nonneg_right (pow_le_one₀ (by positivity) hq) (by dsimp [B]; positivity)
      _ = B := one_mul _
  calc
    _ ≤ ∑ S ∈ (Finset.univ : Finset ι).powerset, |t ^ (Fintype.card ι - S.card) *
        (Rect.FullN Fr (fun a : S => (c a.1 : ℕ)) (fun i : Fin m => r + 2 * (i : ℕ))
          (fun i : Fin m => r + 2 * (i : ℕ) + 1) (Fr.const : ℝ)).det| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ S ∈ (Finset.univ : Finset ι).powerset, B := Finset.sum_le_sum hterm
    _ = 2 ^ Fintype.card ι * B := by simp [Finset.card_powerset]
    _ ≤ 2 ^ r * B := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hι)
      (by dsimp [B]; positivity)

end CatalanCore
