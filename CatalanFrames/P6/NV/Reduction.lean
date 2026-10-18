module

public import CatalanFrames.P6.NV.Mid
public import CatalanCore.NV.ModL

/-!
# P6 NV: the mod-`ℓ` reduction identity (WP11)

For `ℓ = 6t+1`, `K = 2t+1`, `h = K + n` (`n ≤ t` middle nodes) and an `ℓ`-integral `r` with
`P_h(r) = 0`, the Schur complement of the scaled matrix `D (r I + M) D` (`D = diag(1_K, ℓ 1_n)`)
gives
`det ((36 r̄ - c) I + N_σ) = 0`, `σ = t - n`, `N_σ = ∑_{y ≤ 3t} v_y v_yᵀ - 2 ∑_{j<σ} v_{3t+1+j} v_{3t+1+j}ᵀ`,
`v_y(a) = 1/(a+y)`.  (Exact identity: `ℓ^{2n} P_h = 2^{-n} 36^{-K} det(...)` up to the unit.)
-/

@[expose] public section

open Finset Matrix CatalanCore

namespace CatalanFrames.P6.NV

open CatalanFrames.P6

variable {ℓ t : ℕ} [Fact ℓ.Prime]

/-- the Gram-type matrix `N_σ` of the reduction, `K = 2t+1`. -/
noncomputable def Nsig (ℓ t σ : ℕ) : Matrix (Fin (2 * t + 1)) (Fin (2 * t + 1)) (ZMod ℓ) :=
  Matrix.of fun a b =>
    ∑ j ∈ range (3 * t), finv ℓ ((a : ℕ) + 1 + j) * finv ℓ ((b : ℕ) + 1 + j) -
      2 * ∑ j ∈ range σ, finv ℓ ((a : ℕ) + 3 * t + 1 + j) * finv ℓ ((b : ℕ) + 3 * t + 1 + j)

/-- the low block of the reduced matrix. -/
noncomputable def Xlow (ℓ t : ℕ) [Fact ℓ.Prime] (rb : ZMod ℓ) :
    Matrix (Fin (2 * t + 1)) (Fin (2 * t + 1)) (ZMod ℓ) :=
  Matrix.of fun a b => (if a = b then rb else 0) +
    (Gw ℓ t a b - if a = b then cc ℓ t else 0) / 36

/-- the low-middle block of the reduced matrix. -/
noncomputable def Bmid (ℓ t n : ℕ) [Fact ℓ.Prime] : Matrix (Fin (2 * t + 1)) (Fin n) (ZMod ℓ) :=
  Matrix.of fun a j => 1 / (6 * (((2 * t + 1 + (j : ℕ) : ℕ) : ZMod ℓ) - (a : ℕ)))

lemma sum_tail (f : ℕ → ZMod ℓ) (t : ℕ) : ∀ n, n ≤ t →
    ∑ j ∈ range n, f (t - 1 - j) = ∑ j ∈ range t, f j - ∑ j ∈ range (t - n), f j := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ n ih =>
    intro hn
    rw [Finset.sum_range_succ, ih (by omega)]
    have e : t - n = (t - (n + 1)) + 1 := by omega
    rw [e, Finset.sum_range_succ]
    have e2 : t - (n + 1) = t - 1 - n := by omega
    rw [e2]; ring

lemma sum_fin_tail {n : ℕ} (f : ℕ → ZMod ℓ) (hn : n ≤ t) :
    ∑ j : Fin n, f (t - 1 - j) = ∑ j ∈ range t, f j - ∑ j ∈ range (t - n), f j := by
  rw [← Finset.sum_range (fun j => f (t - 1 - j))]
  exact sum_tail f t n hn

variable (hl : ℓ = 6 * t + 1) (ht : 1 ≤ t)
include hl ht

lemma Bmid_term {n : ℕ} (hn : n ≤ t) (a b : Fin (2 * t + 1)) (j : Fin n) :
    Bmid ℓ t n a j * Bmid ℓ t n b j =
      (1 / 36) * (finv ℓ ((a : ℕ) + 3 * t + 1 + (t - 1 - j)) *
        finv ℓ ((b : ℕ) + 3 * t + 1 + (t - 1 - j))) := by
  have hj := j.2
  have hu : ((t - 1 - (j : ℕ) : ℕ) : ZMod ℓ) + 1 + (j : ℕ) = t := by
    have : (t - 1 - (j : ℕ)) + 1 + (j : ℕ) = t := by omega
    exact_mod_cast congrArg (Nat.cast (R := ZMod ℓ)) this
  have h6 := six_t hl ht
  have rel : ∀ c : Fin (2 * t + 1), ((2 * t + 1 + (j : ℕ) : ℕ) : ZMod ℓ) - (c : ℕ) =
      -(((c : ℕ) + 3 * t + 1 + (t - 1 - j) : ℕ) : ZMod ℓ) := by
    intro c
    push_cast
    linear_combination h6 + hu
  have h36 : (36 : ZMod ℓ) = 6 * 6 := by norm_num
  simp only [Bmid, Matrix.of_apply, rel, finv]
  rw [h36]
  simp only [one_div, mul_neg, inv_neg, mul_inv]
  ring

lemma Bmid_sq {n : ℕ} (hn : n ≤ t) (a b : Fin (2 * t + 1)) :
    ∑ j : Fin n, Bmid ℓ t n a j * Bmid ℓ t n b j =
      (1 / 36) * (∑ j ∈ range t, finv ℓ ((a : ℕ) + 3 * t + 1 + j) * finv ℓ ((b : ℕ) + 3 * t + 1 + j) -
        ∑ j ∈ range (t - n), finv ℓ ((a : ℕ) + 3 * t + 1 + j) * finv ℓ ((b : ℕ) + 3 * t + 1 + j)) := by
  let Tf : ℕ → ZMod ℓ := fun i => finv ℓ ((a : ℕ) + 3 * t + 1 + i) * finv ℓ ((b : ℕ) + 3 * t + 1 + i)
  have h1 : ∑ j : Fin n, Bmid ℓ t n a j * Bmid ℓ t n b j =
      (1 / 36) * ∑ j : Fin n, Tf (t - 1 - j) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => Bmid_term hl ht hn a b j
  rw [h1]
  exact congrArg (HMul.hMul (1 / 36 : ZMod ℓ)) (sum_fin_tail Tf hn)

/-- the scaled entry of `D (r I + M) D` on natural nodes, `D = diag (1 on low, ℓ on middle)`. -/
noncomputable def sc (ℓ t : ℕ) (r : ℚ) (a b : ℕ) : ℚ :=
  (if a < 2 * t + 1 then 1 else (ℓ : ℚ)) * (if b < 2 * t + 1 then 1 else (ℓ : ℚ)) *
    ((if a = b then r else 0) + p6Frame.Mn a b)

omit hl ht in
lemma good_ite {r : ℚ} {rb : ZMod ℓ} (c : Prop) [Decidable c] (hr : Good ℓ r rb) :
    Good ℓ (if c then r else 0) (if c then rb else 0) := by
  split_ifs
  · exact hr
  · exact Good.zero

lemma sc_ll {r : ℚ} {rb : ZMod ℓ} (hr : Good ℓ r rb) {a b : ℕ} (ha : a ≤ 2 * t) (hb : b ≤ 2 * t) :
    Good ℓ (sc ℓ t r a b)
      ((if a = b then rb else 0) + (Gw ℓ t a b - if a = b then cc ℓ t else 0) / 36) := by
  unfold sc
  rw [if_pos (show a < 2 * t + 1 by omega), if_pos (show b < 2 * t + 1 by omega), one_mul, one_mul]
  exact (good_ite (a = b) hr).add (low_good hl ht ha hb)

lemma sc_lm {r : ℚ} {a b : ℕ} (ha : a ≤ 2 * t) (hb1 : 2 * t + 1 ≤ b) (hb2 : b ≤ 3 * t) :
    Good ℓ (sc ℓ t r a b) (1 / (6 * ((b : ZMod ℓ) - a))) := by
  unfold sc
  rw [if_pos (show a < 2 * t + 1 by omega), if_neg (show ¬ b < 2 * t + 1 by omega),
    if_neg (show ¬ a = b by omega), one_mul, zero_add]
  exact (lowmid_good hl ht ha hb1 hb2).congr' (by ring)

lemma sc_ml {r : ℚ} {a b : ℕ} (ha : a ≤ 2 * t) (hb1 : 2 * t + 1 ≤ b) (hb2 : b ≤ 3 * t) :
    Good ℓ (sc ℓ t r b a) (1 / (6 * ((b : ZMod ℓ) - a))) := by
  unfold sc
  rw [if_pos (show a < 2 * t + 1 by omega), if_neg (show ¬ b < 2 * t + 1 by omega),
    if_neg (show ¬ b = a by omega), mul_one, zero_add, Mn_comm]
  exact (lowmid_good hl ht ha hb1 hb2).congr' (by ring)

lemma sc_mm {r : ℚ} {rb : ZMod ℓ} (hr : Good ℓ r rb) {a b : ℕ} (ha1 : 2 * t + 1 ≤ a)
    (ha2 : a ≤ 3 * t) (hb1 : 2 * t + 1 ≤ b) (hb2 : b ≤ 3 * t) :
    Good ℓ (sc ℓ t r a b) (if a = b then -(1 / 2) else 0) := by
  unfold sc
  rw [if_neg (show ¬ a < 2 * t + 1 by omega), if_neg (show ¬ b < 2 * t + 1 by omega)]
  by_cases hab : a = b
  · subst hab
    rw [if_pos rfl, if_pos rfl, mul_add]
    have h1 : (ℓ : ℚ) * (ℓ : ℚ) * r = (ℓ : ℚ) * ((ℓ : ℚ) * r) := by ring
    rw [h1]
    have := (hr.ell_mul.ell_mul).add (midmid_diag_good hl ht ha1 ha2)
    refine (this.congr (by ring)).congr' ?_
    ring
  · rw [if_neg hab, if_neg hab, zero_add]
    rcases lt_or_gt_of_ne hab with h | h
    · exact (midmid_off_good hl ht ha1 h hb2).congr' (by ring)
    · rw [Mn_comm]
      exact (midmid_off_good hl ht hb1 h ha2).congr' (by ring)

lemma Dm_inv (n : ℕ) :
    ((-(1 / 2) : ZMod ℓ) • (1 : Matrix (Fin n) (Fin n) (ZMod ℓ)))⁻¹ =
      (-2 : ZMod ℓ) • (1 : Matrix (Fin n) (Fin n) (ZMod ℓ)) := by
  refine Matrix.inv_eq_right_inv ?_
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_one]
  have h2 := two_ne hl ht
  have : (-(1 / 2) : ZMod ℓ) * -2 = 1 := by field_simp
  simp only [this, one_smul]

theorem reduce {n : ℕ} (hn : n ≤ t) {r : ℚ} {rb : ZMod ℓ} (hr : Good ℓ r rb)
    (hP : p6Frame.P (2 * t + 1 + n) r = 0) :
    ((36 * rb - cc ℓ t) • (1 : Matrix (Fin (2 * t + 1)) (Fin (2 * t + 1)) (ZMod ℓ)) +
      Nsig ℓ t (t - n)).det = 0 := by
  let e := finSumEquiv (2 * t + 1) n (2 * t + 1 + n) rfl
  let d : Fin (2 * t + 1 + n) → ℚ := fun a => if (a : ℕ) < 2 * t + 1 then 1 else (ℓ : ℚ)
  let Dm : Matrix (Fin n) (Fin n) (ZMod ℓ) := (-(1 / 2) : ZMod ℓ) • 1
  let y : Matrix (Fin (2 * t + 1) ⊕ Fin n) (Fin (2 * t + 1) ⊕ Fin n) (ZMod ℓ) :=
    Matrix.fromBlocks (Xlow ℓ t rb) (Bmid ℓ t n) (Bmid ℓ t n)ᵀ Dm
  have key : ∀ i j, scaleDiag d r (p6Frame.M (2 * t + 1 + n)) (e i) (e j) =
      sc ℓ t r (e i : ℕ) (e j : ℕ) := by
    intro i j
    simp [scaleDiag, sc, Frame.M, Frame.MRect, d, Fin.ext_iff]
  have hy : ∀ i j, Good ℓ (scaleDiag d r (p6Frame.M (2 * t + 1 + n)) (e i) (e j)) (y i j) := by
    intro i j
    rw [key]
    rcases i with a | j1 <;> rcases j with b | j2
    · simp only [e, finSumEquiv_inl, y, Matrix.fromBlocks_apply₁₁, Xlow, Matrix.of_apply]
      have := sc_ll hl ht hr (a := a) (b := b) (by omega) (by omega)
      simpa [Fin.ext_iff] using this
    · simp only [e, finSumEquiv_inl, finSumEquiv_inr, y, Matrix.fromBlocks_apply₁₂, Bmid,
        Matrix.of_apply]
      exact sc_lm hl ht (r := r) (a := a) (b := 2 * t + 1 + j2) (by omega) (by omega) (by omega)
    · simp only [e, finSumEquiv_inl, finSumEquiv_inr, y, Matrix.fromBlocks_apply₂₁,
        Matrix.transpose_apply, Bmid, Matrix.of_apply]
      exact sc_ml hl ht (r := r) (a := b) (b := 2 * t + 1 + j1) (by omega) (by omega) (by omega)
    · simp only [e, finSumEquiv_inr, y, Matrix.fromBlocks_apply₂₂, Dm, Matrix.smul_apply,
        Matrix.one_apply, smul_eq_mul]
      have := sc_mm hl ht hr (a := 2 * t + 1 + j1) (b := 2 * t + 1 + j2) (by omega) (by omega)
        (by omega) (by omega)
      by_cases hj : j1 = j2
      · subst hj; simpa using this
      · have hj' : (2 * t + 1 + (j1 : ℕ)) ≠ 2 * t + 1 + j2 := by
          intro h; apply hj; exact Fin.ext (by omega)
        have hjn : ¬ ((j1 : ℕ) = j2) := fun h => hj (Fin.ext h)
        simpa [hj, hj', hjn] using this
  have h0 : y.det = 0 :=
    reduce_det_eq_zero e d r _ y hy hP
  have hD : Dm.det ≠ 0 := by
    have h2 := two_ne hl ht
    simp only [Dm, Matrix.det_smul, Matrix.det_one, mul_one]
    exact pow_ne_zero _ (by simpa using h2)
  have hs := schur_zero_diag (Xlow ℓ t rb) (Bmid ℓ t n) (Bmid ℓ t n)ᵀ Dm hD h0
  rw [show Dm⁻¹ = (-2 : ZMod ℓ) • (1 : Matrix (Fin n) (Fin n) (ZMod ℓ)) from Dm_inv hl ht n] at hs
  have hmat : Xlow ℓ t rb - Bmid ℓ t n * ((-2 : ZMod ℓ) • (1 : Matrix (Fin n) (Fin n) (ZMod ℓ))) *
      (Bmid ℓ t n)ᵀ = (1 / 36 : ZMod ℓ) • ((36 * rb - cc ℓ t) •
        (1 : Matrix (Fin (2 * t + 1)) (Fin (2 * t + 1)) (ZMod ℓ)) + Nsig ℓ t (t - n)) := by
    ext a b
    have hB := Bmid_sq hl ht hn a b
    simp only [Matrix.sub_apply, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
      Matrix.smul_apply, Matrix.mul_apply, Matrix.transpose_apply, Xlow, Nsig, Matrix.of_apply,
      Matrix.add_apply, Matrix.one_apply, smul_eq_mul]
    rw [hB]
    unfold Gw
    by_cases hab : a = b
    · have h : (36 : ZMod ℓ)⁻¹ * 36 = 1 := inv_mul_cancel₀ (n36_ne hl ht)
      simp only [hab, if_true]
      linear_combination (-rb) * h
    · simp only [hab, if_false]; ring
  rw [hmat, Matrix.det_smul] at hs
  have h36 : (1 / 36 : ZMod ℓ) ≠ 0 := by
    have := n36_ne hl ht; simpa using this
  exact (mul_eq_zero.1 hs).resolve_left (pow_ne_zero _ h36)

end CatalanFrames.P6.NV
