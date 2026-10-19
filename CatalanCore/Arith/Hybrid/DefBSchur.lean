module

public import CatalanCore.Arith.Hybrid.DefBLam

@[expose] public section

/-!
# Theorem B: the scalar Schur complement in `𝔽_p`

`schur_Z`: for `u, w < k`, with `S̄ = Ā00 - π⁻¹ V Vᵀ` computed from the table `Tfull`,

  `S̄_{uw} = [u = w] H^{(2)}_{k-1}/16 + (1/16) ∑_{i=1}^{d} E_{ui} E_{wi}`,   `E_{ui} = 1/(u+i)`,

(the `X`-part is carried separately).  This is the harmonic-reflection identity `harm_off/harm_diag`
transported along `4k ≡ 1`.
-/

open Finset CatalanCore Matrix

namespace CatalanCore.Arith.Hybrid

section

variable {p : ℕ} [Fact p.Prime]

lemma conv4 (hp5 : 5 ≤ p) {k : ℕ} (hk4 : (4 : ZMod p) * (k : ZMod p) = 1) (t : ZMod p) :
    4 * (4 * t - 1)⁻¹ = (t - (k : ZMod p))⁻¹ := by
  have h4 := four_ne_zmod p hp5
  have : 4 * t - 1 = 4 * (t - (k : ZMod p)) := by linear_combination hk4
  rw [this, mul_inv]
  field_simp

lemma conv4sq (hp5 : 5 ≤ p) {k : ℕ} (hk4 : (4 : ZMod p) * (k : ZMod p) = 1) (t : ZMod p) :
    16 * ((4 * t - 1)⁻¹) ^ 2 = ((t - (k : ZMod p))⁻¹) ^ 2 := by
  have h4 := four_ne_zmod p hp5
  have : 4 * t - 1 = 4 * (t - (k : ZMod p)) := by linear_combination hk4
  rw [this, mul_inv]
  field_simp
  ring

variable {j k : ℕ}

lemma Tfull_lh {u c : ℕ} (hu : u < k) (hc : k ≤ c) (hcp : c < p) :
    Tfull p j k u c = (16 * ((c : ZMod p) - u))⁻¹ * (-(4 * ((j : ℕ) : ZMod p)⁻¹)) := by
  unfold Tfull TB
  rw [if_pos (by omega), if_neg (by omega), if_pos hu, if_pos hcp]

lemma Tfull_ll {u w : ℕ} (hp5 : 5 ≤ p) (hk4 : (4 : ZMod p) * (k : ZMod p) = 1) (huw : u < w)
    (hw : w < k) :
    Tfull p j k u w = (16 * ((w : ZMod p) - u))⁻¹ *
      ∑ t ∈ Ioc u w, (((t : ℕ) : ZMod p)⁻¹ - ((t : ZMod p) - (k : ZMod p))⁻¹) := by
  unfold Tfull TB
  rw [if_pos huw, if_pos hw]
  congr 1
  exact Finset.sum_congr rfl fun t _ => by rw [conv4 hp5 hk4]

lemma Tfull_dd {u : ℕ} (hp5 : 5 ≤ p) (hk4 : (4 : ZMod p) * (k : ZMod p) = 1) (hu : u < k) :
    Tfull p j k u u = -(1 / 16 : ZMod p) * ∑ t ∈ Icc 1 u,
      ((((t : ℕ) : ZMod p)⁻¹) ^ 2 - (((t : ZMod p) - (k : ZMod p))⁻¹) ^ 2) := by
  unfold Tfull TD
  rw [if_neg (lt_irrefl _), if_neg (lt_irrefl _), if_pos hu]
  congr 1
  exact Finset.sum_congr rfl fun t _ => by rw [conv4sq hp5 hk4]

/-- **The scalar Schur complement.**  -/
theorem schur_Z (hp5 : 5 ≤ p) (hk4 : (4 : ZMod p) * (k : ZMod p) = 1)
    (hj : ((j : ℕ) : ZMod p) ≠ 0) {r d : ℕ} (hrd : r + d = p) (hkr : k ≤ r) {u w : ℕ}
    (hu : u < k) (hw : w < k) :
    Tfull p j k u w - ((((j : ℕ) : ZMod p)⁻¹) ^ 2)⁻¹ *
        ∑ c ∈ Ico k r, Tfull p j k u c * Tfull p j k w c =
      (if u = w then hm2 p (k - 1) / 16 else 0) +
        (1 / 16) * ∑ i ∈ Icc 1 d, ((u : ZMod p) + (i : ℕ))⁻¹ * ((w : ZMod p) + (i : ℕ))⁻¹ := by
  have h16 : (16 : ZMod p) ≠ 0 := by
    have : (16 : ZMod p) = 4 * 4 := by norm_num
    rw [this]; exact mul_ne_zero (four_ne_zmod p hp5) (four_ne_zmod p hp5)
  have hp3 : 3 ≤ p := by omega
  -- the sum over the high block
  have hS : ∀ u w : ℕ, u < k → w < k →
      ((((j : ℕ) : ZMod p)⁻¹) ^ 2)⁻¹ * ∑ c ∈ Ico k r, Tfull p j k u c * Tfull p j k w c =
        (1 / 16) * ∑ c ∈ Ico k r, (((c : ℕ) : ZMod p) - u)⁻¹ * (((c : ℕ) : ZMod p) - w)⁻¹ := by
    intro u w hu hw
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c hc => ?_
    have hc' := Finset.mem_Ico.1 hc
    rw [Tfull_lh hu hc'.1 (by omega), Tfull_lh hw hc'.1 (by omega)]
    field_simp
    ring
  rcases lt_trichotomy u w with huw | huw | huw
  · rw [if_neg huw.ne, hS u w hu hw, Tfull_ll hp5 hk4 huw hw]
    have := harm_off hp3 hrd hkr huw hw
    rw [zero_add]
    linear_combination this
  · subst huw
    rw [if_pos rfl, hS u u hu hu, Tfull_dd hp5 hk4 hu]
    have := harm_diag hp5 hrd hkr hu
    simp only [← sq] at this ⊢
    linear_combination this
  · rw [if_neg huw.ne', Tfull_symm p j k u w]
    have hS' := hS w u hw hu
    rw [show ∑ c ∈ Ico k r, Tfull p j k u c * Tfull p j k w c =
        ∑ c ∈ Ico k r, Tfull p j k w c * Tfull p j k u c from
          Finset.sum_congr rfl fun c _ => mul_comm _ _, hS', Tfull_ll hp5 hk4 huw hu]
    have := harm_off hp3 hrd hkr huw hu
    rw [zero_add]
    have e : ∑ i ∈ Icc 1 d, ((u : ZMod p) + (i : ℕ))⁻¹ * ((w : ZMod p) + (i : ℕ))⁻¹ =
        ∑ i ∈ Icc 1 d, ((w : ZMod p) + (i : ℕ))⁻¹ * ((u : ZMod p) + (i : ℕ))⁻¹ :=
      Finset.sum_congr rfl fun i _ => mul_comm _ _
    rw [e]
    linear_combination this

/-- **Theorem C5, scalar Schur complement of the `B1` block** (`d = 0`, `r := p`): for `u, w < k`,
`T_{uw} - π⁻¹ ∑_{c=k}^{p-1} T_{uc} T_{wc} = [u = w] H^{(2)}_{k-1}/16`.  This is DQ Lemma 3.1
with the sum over the whole of `[k, p)`. -/
theorem schur_Z_C5 (hp5 : 5 ≤ p) (hk4 : (4 : ZMod p) * (k : ZMod p) = 1)
    (hj : ((j : ℕ) : ZMod p) ≠ 0) (hkp : k ≤ p) {u w : ℕ} (hu : u < k) (hw : w < k) :
    Tfull p j k u w - ((((j : ℕ) : ZMod p)⁻¹) ^ 2)⁻¹ *
        ∑ c ∈ Ico k p, Tfull p j k u c * Tfull p j k w c =
      (if u = w then hm2 p (k - 1) / 16 else 0) := by
  have := schur_Z (j := j) hp5 hk4 hj (r := p) (d := 0) (by omega) hkp hu hw
  simpa using this

end

/-! ### The matrix identity over `𝔽_p(X)` -/

section Mat

variable (p : ℕ) [Fact p.Prime] (r m j k : ℕ)

/-- `rfC` as a ring homomorphism. -/
noncomputable def rfCH : ZMod p →+* RatFunc (ZMod p) :=
  (algebraMap (Polynomial (ZMod p)) (RatFunc (ZMod p))).comp Polynomial.C

lemma rfC_eq (a : ZMod p) : rfC p a = rfCH p a := rfl

lemma sum_Blk1 {M : Type*} [AddCommMonoid M] (f : ℕ → M) (hkr : k ≤ r) :
    ∑ c : Blk1 r k, f c.1.val = ∑ c ∈ Ico k r, f c := by
  refine Finset.sum_bij (fun c _ => c.1.val) ?_ ?_ ?_ ?_
  · intro c _; have := c.1.2; have := c.2; simp only [Finset.mem_Ico]; omega
  · intro a _ b _ h; exact Subtype.ext (Fin.ext h)
  · intro c hc
    have := Finset.mem_Ico.1 hc
    exact ⟨⟨⟨c, by omega⟩, by simp only; omega⟩, Finset.mem_univ _, rfl⟩
  · intro c _; rfl

lemma sum_FinD {M : Type*} [AddCommMonoid M] (g : ℕ → M) (d : ℕ) :
    ∑ i : Fin d, g ((i : ℕ) + 1) = ∑ i ∈ Icc 1 d, g i := by
  rw [sum_Icc_eq_range, Fin.sum_univ_eq_sum_range (fun i => g (i + 1)) d]

/-- The Schur data `E` (`E_{ui} = 1/(u + i + 1)`, `i < d`). -/
noncomputable def EL (d : ℕ) : Matrix (Blk0 r k) (Fin d) (RatFunc (ZMod p)) :=
  Matrix.of fun u i => rfC p ((((u.1 : ℕ) : ZMod p) + (((i : ℕ) + 1 : ℕ) : ZMod p))⁻¹)

noncomputable def s0L : RatFunc (ZMod p) := rfX p + rfC p (hm2 p (k - 1) / 16)

noncomputable def κL : RatFunc (ZMod p) := rfC p (-(1 / 16 : ZMod p))

/-- **Theorem B, Schur identity over `𝔽_p(X)`**: `Ā00 - π⁻¹ V Vᵀ = s₀ I - κ E Eᵀ`. -/
theorem hS_L (hp5 : 5 ≤ p) (hk4 : (4 : ZMod p) * (k : ZMod p) = 1)
    (hj : ((j : ℕ) : ZMod p) ≠ 0) {d : ℕ} (hrd : r + d = p) (hkr : k ≤ r) :
    A0L p r j k - (piL p j)⁻¹ • (VL p r j k * (VL p r j k)ᵀ) =
      s0L p k • (1 : Matrix (Blk0 r k) (Blk0 r k) _) - κL p • (EL p r k d * (EL p r k d)ᵀ) := by
  ext u w
  have hZ := schur_Z (j := j) hp5 hk4 hj hrd hkr (u := u.1.val) (w := w.1.val) u.2 w.2
  have hpi : (piL p j)⁻¹ = rfCH p (((((j : ℕ) : ZMod p)⁻¹) ^ 2)⁻¹) := by
    unfold piL; rw [rfC_eq, map_inv₀]
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.mul_apply, Matrix.transpose_apply,
    smul_eq_mul, A0L, VL, EL, Matrix.of_apply, Matrix.one_apply, s0L, κL]
  have h1 : ∑ c : Blk1 r k, rfC p (Tfull p j k u.1.val c.1.val) * rfC p (Tfull p j k w.1.val c.1.val) =
      ∑ c ∈ Ico k r, rfC p (Tfull p j k u.1.val c) * rfC p (Tfull p j k w.1.val c) :=
    sum_Blk1 r k (M := RatFunc (ZMod p)) (fun c => rfC p (Tfull p j k u.1.val c) *
      rfC p (Tfull p j k w.1.val c)) hkr
  have h2 : ∑ i : Fin d, rfC p ((((u.1 : ℕ) : ZMod p) + (((i : ℕ) + 1 : ℕ) : ZMod p))⁻¹) *
        rfC p ((((w.1 : ℕ) : ZMod p) + (((i : ℕ) + 1 : ℕ) : ZMod p))⁻¹) =
      ∑ i ∈ Icc 1 d, rfC p ((((u.1 : ℕ) : ZMod p) + ((i : ℕ) : ZMod p))⁻¹) *
        rfC p ((((w.1 : ℕ) : ZMod p) + ((i : ℕ) : ZMod p))⁻¹) :=
    sum_FinD (M := RatFunc (ZMod p)) (fun i => rfC p ((((u.1 : ℕ) : ZMod p) + ((i : ℕ) : ZMod p))⁻¹) *
      rfC p ((((w.1 : ℕ) : ZMod p) + ((i : ℕ) : ZMod p))⁻¹)) d
  rw [h1, h2, hpi]
  have hZ' := congrArg (rfCH p) hZ
  simp only [rfC_eq, map_sub, map_mul, map_add, map_sum, map_inv₀, map_div₀, map_one,
    map_ofNat, map_neg, apply_ite (rfCH p), map_zero] at hZ' ⊢
  by_cases huw : u = w
  · subst huw
    simp only [if_true, mul_one] at hZ' ⊢
    linear_combination hZ'
  · have hne : u.1.val ≠ w.1.val := fun h => huw (Subtype.ext (Fin.ext h))
    simp only [if_neg huw, if_neg hne, mul_zero] at hZ' ⊢
    linear_combination hZ'

end Mat

end CatalanCore.Arith.Hybrid
