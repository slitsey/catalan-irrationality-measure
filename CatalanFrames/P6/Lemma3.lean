module

public import CatalanFrames.P6.NV.Reduction

/-!
# P6 Lemma 3 analogue (WP11)

`ℓ = 6t+1`, `h = 2t+1+n` with `n ≤ t`, `e ≥ 1`, `e ≠ 2`, and `u = ℓ^e r` an `ℓ`-adic unit
imply `P_h(r) ≠ 0`.  Rows are scaled by `ℓ^e` (low) and `ℓ^{e-2}` (middle); modulo `ℓ` the matrix
is block lower triangular with diagonal blocks `u I` and `-1/2 I` (`e = 1`) or `u I` (`e ≥ 3`).
(The exceptional residues are at `e = 2` only: `u = -1/2`, where the middle block degenerates.)
-/

@[expose] public section

open Finset Matrix CatalanCore

namespace CatalanFrames.P6.NV

open CatalanFrames.P6

variable {ℓ t : ℕ} [Fact ℓ.Prime]

/-- scaling exponent of the rows. -/
def exI (t n e : ℕ) : Fin (2 * t + 1) ⊕ Fin n → ℕ := Sum.elim (fun _ => e) (fun _ => e - 2)

lemma lpow_zero {k : ℕ} (hk : 1 ≤ k) : Good ℓ ((ℓ : ℚ) ^ k) 0 := by
  have := (Good.natCast (ℓ := ℓ) ℓ).pow' k
  rw [ZMod.natCast_self, zero_pow (by omega)] at this
  simpa using this

lemma sc_split (r : ℚ) (a b : ℕ) :
    sc ℓ t r a b = (if a < 2 * t + 1 then (1 : ℚ) else (ℓ : ℚ)) * (if b < 2 * t + 1 then (1 : ℚ) else (ℓ : ℚ)) *
      (if a = b then r else 0) + sc ℓ t 0 a b := by
  unfold sc
  by_cases hab : a = b
  · subst hab; simp only [if_true, eq_self_iff_true]; ring
  · simp only [hab, if_false]; ring

/-- `sc ℓ t 0` is `ℓ`-integral on all node pairs of the relevant range. -/
lemma scM_mem (hl : ℓ = 6 * t + 1) (ht : 1 ≤ t) {a b : ℕ} (ha : a ≤ 3 * t) (hb : b ≤ 3 * t) :
    sc ℓ t 0 a b ∈ S ℓ := by
  by_cases ha' : a ≤ 2 * t <;> by_cases hb' : b ≤ 2 * t
  · exact (sc_ll hl ht Good.zero ha' hb').mem
  · exact (sc_lm hl ht (r := 0) ha' (by omega) hb).mem
  · exact (sc_ml hl ht (r := 0) hb' (by omega) ha).mem
  · exact (sc_mm hl ht Good.zero (by omega) ha (by omega) hb).mem

lemma lemma3 (hl : ℓ = 6 * t + 1) (ht : 1 ≤ t) {n : ℕ} (hn : n ≤ t) {r : ℚ} {e : ℕ}
    (he1 : 1 ≤ e) (he2 : e ≠ 2) (hu : (ℓ : ℚ) ^ e * r ∈ S ℓ)
    (hu0 : red ℓ ((ℓ : ℚ) ^ e * r) ≠ 0) : p6Frame.P (2 * t + 1 + n) r ≠ 0 := by
  intro hP
  set ub : ZMod ℓ := red ℓ ((ℓ : ℚ) ^ e * r) with hub
  have gu : Good ℓ ((ℓ : ℚ) ^ e * r) ub := ⟨hu, rfl⟩
  let e' := finSumEquiv (2 * t + 1) n (2 * t + 1 + n) rfl
  let d : Fin (2 * t + 1 + n) → ℚ := fun a => if (a : ℕ) < 2 * t + 1 then 1 else (ℓ : ℚ)
  let NS : Matrix (Fin (2 * t + 1) ⊕ Fin n) (Fin (2 * t + 1) ⊕ Fin n) ℚ :=
    Matrix.of fun i j => (ℓ : ℚ) ^ (exI t n e i) * sc ℓ t r (e' i : ℕ) (e' j : ℕ)
  have key : ∀ i j, scaleDiag d r (p6Frame.M (2 * t + 1 + n)) (e' i) (e' j) =
      sc ℓ t r (e' i : ℕ) (e' j : ℕ) := by
    intro i j
    simp [scaleDiag, sc, Frame.M, Frame.MRect, d, Fin.ext_iff]
  have hNS : NS = Matrix.diagonal (fun i => (ℓ : ℚ) ^ (exI t n e i)) *
      (scaleDiag d r (p6Frame.M (2 * t + 1 + n))).submatrix e' e' := by
    ext i j
    simp [NS, Matrix.diagonal_mul, key]
  have hdet : NS.det = 0 := by
    rw [hNS, Matrix.det_mul, Matrix.det_submatrix_equiv_self,
      det_scaleDiag_eq_zero d r _ hP, mul_zero]
  let Dm' : Matrix (Fin n) (Fin n) (ZMod ℓ) := (if e = 1 then (-(1 / 2) : ZMod ℓ) else ub) • 1
  let Cm : Matrix (Fin n) (Fin (2 * t + 1)) (ZMod ℓ) :=
    Matrix.of fun j a => red ℓ (NS (Sum.inr j) (Sum.inl a))
  let y : Matrix (Fin (2 * t + 1) ⊕ Fin n) (Fin (2 * t + 1) ⊕ Fin n) (ZMod ℓ) :=
    Matrix.fromBlocks (ub • 1) 0 Cm Dm'
  have hy : ∀ i j, Good ℓ (NS i j) (y i j) := by
    intro i j
    rcases i with a | j1 <;> rcases j with b | j2
    · have h1 := lpow_zero (ℓ := ℓ) he1
      have hm := (sc_ll hl ht (Good.zero (ℓ := ℓ)) (a := a) (b := b) (by omega) (by omega))
      have hg : Good ℓ ((ℓ : ℚ) ^ e * sc ℓ t 0 a b) 0 := by
        have := h1.mul hm
        simpa using this
      have hd := (good_ite (a = b) gu).add hg
      simp only [NS, exI, Matrix.of_apply, y, Matrix.fromBlocks_apply₁₁, Matrix.smul_apply,
        Matrix.one_apply, smul_eq_mul, e', finSumEquiv_inl]
      rw [sc_split]
      rw [if_pos (show (a : ℕ) < 2 * t + 1 by omega), if_pos (show (b : ℕ) < 2 * t + 1 by omega)]
      by_cases hab : a = b
      · subst hab; simp only [if_true] at hd ⊢; simpa [mul_add] using hd
      · have : ¬ ((a : ℕ) = b) := fun h => hab (Fin.ext h)
        simp only [hab, this, if_false] at hd ⊢; simpa [mul_add] using hd
    · have hm := sc_lm hl ht (r := r) (a := (a : ℕ)) (b := 2 * t + 1 + j2) (by omega) (by omega)
        (by omega)
      have := (lpow_zero (ℓ := ℓ) he1).mul hm
      simp only [NS, exI, Matrix.of_apply, y, Matrix.fromBlocks_apply₁₂, e', finSumEquiv_inl,
        finSumEquiv_inr, Matrix.zero_apply, Sum.elim_inl]
      simpa using this
    · have hm := sc_ml hl ht (r := r) (a := (b : ℕ)) (b := 2 * t + 1 + j1) (by omega) (by omega)
        (by omega)
      have hmem : (ℓ : ℚ) ^ (e - 2) * sc ℓ t r (2 * t + 1 + j1) b ∈ S ℓ :=
        ((Good.natCast (ℓ := ℓ) ℓ).pow' (e - 2)).mul hm |>.mem
      simp only [NS, exI, Matrix.of_apply, y, Matrix.fromBlocks_apply₂₁, e', finSumEquiv_inl,
        finSumEquiv_inr, Sum.elim_inr, Cm]
      exact good_red (by simpa [NS, exI, e', finSumEquiv_inl, finSumEquiv_inr] using hmem)
    · have hm := sc_mm hl ht (Good.zero (ℓ := ℓ)) (a := 2 * t + 1 + j1) (b := 2 * t + 1 + j2)
        (by omega) (by omega) (by omega) (by omega)
      simp only [NS, exI, Matrix.of_apply, y, Matrix.fromBlocks_apply₂₂, e', finSumEquiv_inr,
        Sum.elim_inr, Dm', Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
      rw [sc_split, if_neg (show ¬ (2 * t + 1 + (j1 : ℕ) < 2 * t + 1) by omega),
        if_neg (show ¬ (2 * t + 1 + (j2 : ℕ) < 2 * t + 1) by omega)]
      have hjj : (2 * t + 1 + (j1 : ℕ) = 2 * t + 1 + j2) ↔ j1 = j2 := by
        constructor
        · intro h; exact Fin.ext (by omega)
        · intro h; subst h; rfl
      simp only [hjj] at hm ⊢
      rcases (show e = 1 ∨ 3 ≤ e by omega) with h1 | h3
      · subst h1
        simp only [Nat.reduceSub, pow_zero, one_mul, if_true]
        by_cases hj : j1 = j2
        · subst hj
          simp only [if_true] at hm ⊢
          have g2 : Good ℓ ((ℓ : ℚ) * (ℓ : ℚ) * r) 0 := by
            have := gu.ell_mul
            simpa [pow_one, mul_assoc] using this
          have := g2.add hm
          simpa using this
        · simp only [hj, if_false] at hm ⊢
          have := (Good.zero (ℓ := ℓ)).add hm
          simpa using this
      · have hpos := lpow_zero (ℓ := ℓ) (show 1 ≤ e - 2 by omega)
        have hg : Good ℓ ((ℓ : ℚ) ^ (e - 2) * sc ℓ t 0 (2 * t + 1 + j1) (2 * t + 1 + j2)) 0 := by
          have := hpos.mul hm
          simpa using this
        have hne : e ≠ 1 := by omega
        have e2 : (ℓ : ℚ) ^ (e - 2) * ((ℓ : ℚ) * (ℓ : ℚ) * r) = (ℓ : ℚ) ^ e * r := by
          have : (ℓ : ℚ) ^ e = (ℓ : ℚ) ^ (e - 2) * (ℓ : ℚ) * (ℓ : ℚ) := by
            rw [← pow_succ, ← pow_succ]; congr 1; omega
          rw [this]; ring
        by_cases hj : j1 = j2
        · subst hj
          simp only [if_true, hne, if_false] at hg ⊢
          have hd := (good_ite True gu).add hg
          simp only [if_true] at hd
          rw [mul_add, e2]
          simpa using hd
        · simp only [hj, if_false, hne] at hg ⊢
          have := (Good.zero (ℓ := ℓ)).add hg
          rw [mul_add]
          simpa using this
  have hy0 : y.det = 0 := (red_det NS y hy).eq_zero hdet
  rw [Matrix.det_fromBlocks_zero₁₂, Matrix.det_smul, Matrix.det_smul, Matrix.det_one,
    Matrix.det_one] at hy0
  have h2 := two_ne hl ht
  have : ub ^ (2 * t + 1) * 1 * ((if e = 1 then (-(1 / 2) : ZMod ℓ) else ub) ^ n * 1) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (pow_ne_zero _ hu0) one_ne_zero)
      (mul_ne_zero (pow_ne_zero _ ?_) one_ne_zero)
    split_ifs
    · simpa using h2
    · exact hu0
  simp only [Fintype.card_fin] at hy0
  exact this hy0

end CatalanFrames.P6.NV
