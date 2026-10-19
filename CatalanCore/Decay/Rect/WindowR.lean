module

public import CatalanCore.Decay.Rect.IntegR
public import CatalanCore.Decay.Rect.Energy2
public import CatalanCore.Rect.Geometry

@[expose] public section

/-!
# Rectangular window: `det Full(const + t)` for the hybrid family (WP-H2-core)

`window_rect` : if for every kept-node pattern `s : Fin k → Fin (r + m)` (all extra nodes kept) the
two-family energy bound `RectEnergy` holds with exponent `T0 + r (N - k) cc` (`N = r + m`), then
`|Q_{(r,m)}(const + t)| ≤ 2^r exp (T0 + N log M0)` for `|t| ≤ exp (-cc r)`, where
`Q_{(r,m)} = Frame.fullPoly r m`.  Uses `det_fullN_expansion` (WP-H1) and `theoremN_rect`.
-/

open Finset Polynomial

namespace CatalanCore.Rect

variable (Fr : Frame) (r m : ℕ)

theorem fullPoly_eq_FullN :
    Fr.fullPoly r m = (FullN Fr (fun c : Fin r => (c : ℕ)) (fun i : Fin m => r + 2 * (i : ℕ))
      (fun i : Fin m => r + 2 * (i : ℕ) + 1) (X : ℚ[X])).det := by
  unfold Frame.fullPoly
  congr 1
  ext a b
  rcases a with a | a <;> rcases b with b | b <;>
    simp [FullN, Blk, blkA, blkB, blkC, blkD, Matrix.fromBlocks, Matrix.one_apply,
      Frame.hybRow, Frame.hybCol, Matrix.of_apply, add_comm]

theorem aeval_fullPoly (x : ℝ) :
    Polynomial.aeval x (Fr.fullPoly r m)
      = (FullN Fr (fun c : Fin r => (c : ℕ)) (fun i : Fin m => r + 2 * (i : ℕ))
          (fun i : Fin m => r + 2 * (i : ℕ) + 1) x).det := by
  rw [fullPoly_eq_FullN]
  have h2 : (Polynomial.aeval x : ℚ[X] →ₐ[ℚ] ℝ)
      (FullN Fr (fun c : Fin r => (c : ℕ)) (fun i : Fin m => r + 2 * (i : ℕ))
        (fun i : Fin m => r + 2 * (i : ℕ) + 1) (X : ℚ[X])).det
      = ((FullN Fr (fun c : Fin r => (c : ℕ)) (fun i : Fin m => r + 2 * (i : ℕ))
        (fun i : Fin m => r + 2 * (i : ℕ) + 1) (X : ℚ[X])).map
          (Polynomial.aeval x : ℚ[X] →ₐ[ℚ] ℝ)).det :=
    map_det' (Polynomial.aeval x : ℚ[X] →ₐ[ℚ] ℝ).toRingHom _
  rw [h2, map_fullN]

/-- The embedding of the node index set `S ⊕ Fin m` into `Fin (r + m)`. -/
def hybIdx (S : Finset (Fin r)) : (↥S ⊕ Fin m) → Fin (r + m) :=
  Sum.elim (fun a => ⟨((a.1 : Fin r) : ℕ), Nat.lt_of_lt_of_le a.1.isLt (Nat.le_add_right r m)⟩)
    (fun j => ⟨r + (j : ℕ), Nat.add_lt_add_left j.isLt r⟩)

theorem hybIdx_inj (S : Finset (Fin r)) : Function.Injective (hybIdx r m S) := by
  intro p q h
  rcases p with a | i <;> rcases q with b | j
  · simp only [hybIdx, Sum.elim_inl, Fin.mk.injEq] at h
    exact congrArg Sum.inl (Subtype.ext (Fin.ext h))
  · simp only [hybIdx, Sum.elim_inl, Sum.elim_inr, Fin.mk.injEq] at h
    have := a.1.isLt; omega
  · simp only [hybIdx, Sum.elim_inl, Sum.elim_inr, Fin.mk.injEq] at h
    have := b.1.isLt; omega
  · simp only [hybIdx, Sum.elim_inr, Fin.mk.injEq] at h
    exact congrArg Sum.inr (Fin.ext (by omega))

theorem fullNS_eq (S : Finset (Fin r)) :
    FullN Fr (fun a : ↥S => ((a.1 : Fin r) : ℕ)) (fun i : Fin m => r + 2 * (i : ℕ))
        (fun i : Fin m => r + 2 * (i : ℕ) + 1) (Fr.const : ℝ)
      = Matrix.of fun p q => Fr.Tent (Decay.xnode r (hybIdx r m S p)) (Decay.ynode r (hybIdx r m S q)) := by
  have hxj : ∀ j : ℕ, Decay.xnode r (r + j) = r + 2 * j := fun j => by simp [Decay.xnode]
  have hyj : ∀ j : ℕ, Decay.ynode r (r + j) = r + 2 * j + 1 := fun j => by simp [Decay.ynode]
  ext p q
  rcases p with a | i <;> rcases q with b | j
  · have ha : ((a.1 : Fin r) : ℕ) < r := a.1.isLt
    have hb : ((b.1 : Fin r) : ℕ) < r := b.1.isLt
    have hxa : Decay.xnode r ((a.1 : Fin r) : ℕ) = ((a.1 : Fin r) : ℕ) := Decay.xnode_lt r ha
    have hyb : Decay.ynode r ((b.1 : Fin r) : ℕ) = ((b.1 : Fin r) : ℕ) := Decay.ynode_lt r hb
    simp only [FullN, Blk, Matrix.fromBlocks_apply₁₁, Matrix.add_apply, Matrix.smul_apply,
      Matrix.one_apply, blkA, Matrix.of_apply, hybIdx, Sum.elim_inl, Fin.val_mk, hxa, hyb,
      Frame.Tent, smul_eq_mul]
    by_cases hab : a = b
    · subst hab; simp [add_comm]
    · have h2 : ((a.1 : Fin r) : ℕ) ≠ ((b.1 : Fin r) : ℕ) :=
        fun h => hab (Subtype.ext (Fin.ext h))
      simp [hab, h2]
  · have ha : ((a.1 : Fin r) : ℕ) < r := a.1.isLt
    have hxa : Decay.xnode r ((a.1 : Fin r) : ℕ) = ((a.1 : Fin r) : ℕ) := Decay.xnode_lt r ha
    simp only [FullN, Blk, Matrix.fromBlocks_apply₁₂, blkB, Matrix.of_apply, hybIdx, Sum.elim_inl,
      Sum.elim_inr, Fin.val_mk, hxa, hyj, Frame.Tent]
    have h2 : ((a.1 : Fin r) : ℕ) ≠ r + 2 * (j : ℕ) + 1 := by omega
    simp [h2]
  · have hb : ((b.1 : Fin r) : ℕ) < r := b.1.isLt
    have hyb : Decay.ynode r ((b.1 : Fin r) : ℕ) = ((b.1 : Fin r) : ℕ) := Decay.ynode_lt r hb
    simp only [FullN, Blk, Matrix.fromBlocks_apply₂₁, blkC, Matrix.of_apply, hybIdx, Sum.elim_inl,
      Sum.elim_inr, Fin.val_mk, hxj, hyb, Frame.Tent]
    have h2 : r + 2 * (i : ℕ) ≠ ((b.1 : Fin r) : ℕ) := by omega
    simp [h2]
  · simp only [FullN, Blk, Matrix.fromBlocks_apply₂₂, blkD, Matrix.of_apply, hybIdx, Sum.elim_inr,
      Fin.val_mk, hxj, hyj, Frame.Tent]
    have h2 : r + 2 * (i : ℕ) ≠ r + 2 * (j : ℕ) + 1 := by omega
    simp [h2]

end CatalanCore.Rect

namespace CatalanCore

open Decay

/-- **The rectangular window.** -/
theorem window_rect {Fr : Frame} (hFr : Fr.DecayOK') {e : ℝ} (he0 : 0 < e) (he1 : e < 1)
    {m0 : ℝ} (hm0xs : m0 ≤ Fr.xs) (hm0μ : ∀ i, m0 ≤ Fr.μ i) {r m N0 : ℕ} {R : ℝ}
    (hR : (N0 : ℝ) ≤ R) {T0 cc : ℝ}
    (hEn : ∀ (k : ℕ) (s : Fin k → Fin (r + m)), Function.Injective s →
        (∀ b : Fin (r + m), r ≤ (b : ℕ) → ∃ i, s i = b) →
        Frame.RectEnergy Fr N0 k e m0 (max (Real.log Fr.Aco) 0) (T0 + r * (((r : ℝ) + m) - k) * cc)
          (fun i => xnode r (s i)) (fun i => ynode r (s i)))
    {t : ℝ} (ht : |t| ≤ Real.exp (-cc * r)) :
    |Polynomial.aeval (Fr.const + t) (Fr.fullPoly r m)|
      ≤ 2 ^ r * Real.exp (T0 + ((r : ℝ) + m) * Real.log (Fr.Wabs * R
          + (Fr.Wabs * ⌈(Fr.xs : ℝ)⌉₊ + 2 * (Fr.Aco ^ e / Frame.betaE e) + 1))) := by
  classical
  rw [Rect.aeval_fullPoly, Rect.det_fullN_expansion Fr _ _ _ (Fr.const : ℝ) t]
  set L0 : ℝ := Real.log (Fr.Wabs * R + (Fr.Wabs * ⌈(Fr.xs : ℝ)⌉₊
      + 2 * (Fr.Aco ^ e / Frame.betaE e) + 1)) with hL0
  have hq : |t| * Real.exp (cc * r) ≤ 1 := by
    calc |t| * Real.exp (cc * r) ≤ Real.exp (-cc * r) * Real.exp (cc * r) :=
          mul_le_mul_of_nonneg_right ht (Real.exp_pos _).le
      _ = 1 := by rw [← Real.exp_add]; simp
  have hterm : ∀ S ∈ (Finset.univ : Finset (Fin r)).powerset,
      |t ^ (Fintype.card (Fin r) - S.card) * (Rect.FullN Fr (fun a : ↥S => ((a.1 : Fin r) : ℕ))
          (fun i : Fin m => r + 2 * (i : ℕ)) (fun i : Fin m => r + 2 * (i : ℕ) + 1)
          (Fr.const : ℝ)).det|
        ≤ Real.exp (T0 + ((r : ℝ) + m) * L0) := by
    intro S _
    have hSr : S.card ≤ r := by simpa using Finset.card_le_univ S
    set k : ℕ := S.card + m with hk
    let eq : (↥S ⊕ Fin m) ≃ Fin k :=
      Fintype.equivFinOfCardEq (by simp [Fintype.card_sum, hk])
    set s' : Fin k → Fin (r + m) := fun i => Rect.hybIdx r m S (eq.symm i) with hs'
    have hs'inj : Function.Injective s' := (Rect.hybIdx_inj r m S).comp eq.symm.injective
    have hkeep : ∀ b : Fin (r + m), r ≤ (b : ℕ) → ∃ i, s' i = b := by
      intro b hb
      refine ⟨eq (Sum.inr ⟨(b : ℕ) - r, by have := b.isLt; omega⟩), ?_⟩
      simp only [hs', Equiv.symm_apply_apply, Rect.hybIdx, Sum.elim_inr]
      exact Fin.ext (by simp; omega)
    have hdet : (Rect.FullN Fr (fun a : ↥S => ((a.1 : Fin r) : ℕ))
          (fun i : Fin m => r + 2 * (i : ℕ)) (fun i : Fin m => r + 2 * (i : ℕ) + 1)
          (Fr.const : ℝ)).det
        = (Matrix.of fun i j : Fin k =>
            Fr.Tent (xnode r (s' i)) (ynode r (s' j))).det := by
      rw [Rect.fullNS_eq]
      exact (Matrix.det_submatrix_equiv_self eq.symm _).symm
    have hxinj : Function.Injective (fun i => xnode r (s' i)) := by
      intro a b h
      exact hs'inj (Fin.ext (xnode_inj r h))
    have hyinj : Function.Injective (fun i => ynode r (s' i)) := by
      intro a b h
      exact hs'inj (Fin.ext (ynode_inj r h))
    have hkN : k ≤ r + m := by omega
    have hE := hEn k s' hs'inj hkeep
    have hN := Frame.theoremN_rect hFr he0 he1 hm0xs hm0μ hkN hR hxinj hyinj hE
    rw [abs_mul, abs_pow, hdet]
    have hcard : Fintype.card (Fin r) - S.card = r - S.card := by simp
    rw [hcard]
    have hsub : (((r - S.card : ℕ)) : ℝ) = (r : ℝ) - S.card := by
      rw [Nat.cast_sub hSr]
    have hk' : (k : ℝ) = S.card + m := by rw [hk]; push_cast; ring
    have hexp : Real.exp (T0 + r * (((r : ℝ) + m) - k) * cc + ((r + m : ℕ) : ℝ) * L0)
        = Real.exp (cc * r) ^ (r - S.card) * Real.exp (T0 + ((r : ℝ) + m) * L0) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      rw [hsub, hk']
      push_cast
      ring
    have hN' : |(Matrix.of fun i j : Fin k => Fr.Tent (xnode r (s' i)) (ynode r (s' j))).det|
        ≤ Real.exp (cc * r) ^ (r - S.card) * Real.exp (T0 + ((r : ℝ) + m) * L0) := by
      rw [← hexp]; exact hN
    calc |t| ^ (r - S.card) * |(Matrix.of fun i j : Fin k =>
            Fr.Tent (xnode r (s' i)) (ynode r (s' j))).det|
        ≤ |t| ^ (r - S.card) * (Real.exp (cc * r) ^ (r - S.card)
            * Real.exp (T0 + ((r : ℝ) + m) * L0)) :=
          mul_le_mul_of_nonneg_left hN' (by positivity)
      _ = (|t| * Real.exp (cc * r)) ^ (r - S.card) * Real.exp (T0 + ((r : ℝ) + m) * L0) := by
          rw [mul_pow]; ring
      _ ≤ 1 * Real.exp (T0 + ((r : ℝ) + m) * L0) :=
          mul_le_mul_of_nonneg_right (pow_le_one₀ (by positivity) hq) (Real.exp_pos _).le
      _ = _ := one_mul _
  calc |∑ S ∈ (Finset.univ : Finset (Fin r)).powerset, t ^ (Fintype.card (Fin r) - S.card) *
          (Rect.FullN Fr (fun a : ↥S => ((a.1 : Fin r) : ℕ)) (fun i : Fin m => r + 2 * (i : ℕ))
            (fun i : Fin m => r + 2 * (i : ℕ) + 1) (Fr.const : ℝ)).det|
      ≤ ∑ S ∈ (Finset.univ : Finset (Fin r)).powerset, |t ^ (Fintype.card (Fin r) - S.card) *
          (Rect.FullN Fr (fun a : ↥S => ((a.1 : Fin r) : ℕ)) (fun i : Fin m => r + 2 * (i : ℕ))
            (fun i : Fin m => r + 2 * (i : ℕ) + 1) (Fr.const : ℝ)).det| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ S ∈ (Finset.univ : Finset (Fin r)).powerset, Real.exp (T0 + ((r : ℝ) + m) * L0) :=
        Finset.sum_le_sum hterm
    _ = 2 ^ r * Real.exp (T0 + ((r : ℝ) + m) * L0) := by
        rw [Finset.sum_const, Finset.card_powerset, Finset.card_univ, Fintype.card_fin]
        simp

end CatalanCore
