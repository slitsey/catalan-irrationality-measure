module

public import CatalanCore.Uniform.Content.Smith.LP2Matrix

@[expose] public section

/-!
# LP2 for a general two-term frame: the scalar and matrix Schur complements

After eliminating the level-one block `B1 = [k, r)` the `B0 × B0` Schur complement is
`(x + nr⁻¹ H^{(2)}_{k-1}) I + nr⁻¹ E Eᵀ`, `E_{u,i} = 1/(u + i)` (`1 ≤ i ≤ d = p - r`).  This is
Lemma PT (`pt`, `pt_diag`) transported along the table `Tsym`; the harmonic input is generic in the
frame.
-/

open Finset Polynomial CatalanCore CatalanCore.Basic CatalanCore.Linalg Matrix
  CatalanCore.Arith.Hybrid CatalanCore.Arith.Hybrid.Periodic

namespace CatalanCore.Uniform.Content.Smith

variable {p : ℕ} [Fact p.Prime]

/-- Reflection `c ↦ p - c` of the tail block `[r, p)`. -/
lemma sum_Ico_refl {r d : ℕ} (hrd : r + d = p) (f : ℕ → ZMod p) :
    ∑ c ∈ Ico r p, f c = ∑ i ∈ Icc 1 d, f (p - i) := by
  refine Finset.sum_nbij' (fun c => p - c) (fun i => p - i) ?_ ?_ ?_ ?_ ?_
  · intro c hc; simp only [mem_Ico, mem_Icc] at hc ⊢; omega
  · intro i hi; simp only [mem_Ico, mem_Icc] at hi ⊢; omega
  · intro c hc; simp only [mem_Ico] at hc; omega
  · intro i hi; simp only [mem_Icc] at hi; omega
  · intro c hc
    simp only [mem_Ico] at hc
    rw [Nat.sub_sub_self hc.2.le]

lemma sum_cauchy_refl {r d : ℕ} (hrd : r + d = p) (u w : ℕ) :
    ∑ c ∈ Ico r p, cauchyKer (p := p) u w c =
      ∑ i ∈ Icc 1 d, ((u : ZMod p) + (i : ZMod p))⁻¹ * ((w : ZMod p) + (i : ZMod p))⁻¹ := by
  rw [sum_Ico_refl hrd]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hip : i ≤ p := by have := (mem_Icc.1 hi).2; omega
  unfold cauchyKer
  rw [Nat.cast_sub hip, ZMod.natCast_self]
  have e1 : (0 - (i : ZMod p) - (u : ZMod p)) = -((u : ZMod p) + (i : ZMod p)) := by ring
  have e2 : (0 - (i : ZMod p) - (w : ZMod p)) = -((w : ZMod p) + (i : ZMod p)) := by ring
  rw [e1, e2, inv_neg, inv_neg, neg_mul_neg]

lemma cauchyKer_comm (u w x : ℕ) : cauchyKer (p := p) u w x = cauchyKer (p := p) w u x := by
  unfold cauchyKer; ring

lemma Tsym_lh {k : ℕ} {nr v : ZMod p} {u c : ℕ} (hu : u < k) (hc : k ≤ c) (hcp : c < p) :
    Tsym p k nr v u c = nr⁻¹ * (((c : ZMod p) - u)⁻¹ * v) := by
  unfold Tsym
  rw [if_pos (by omega)]
  unfold Tg
  rw [if_neg (by omega), if_pos hu, if_pos hcp]

/-- **The scalar Schur complement.** -/
theorem schur_scalar (hp5 : 5 ≤ p) {k r d : ℕ} (hrd : r + d = p) (hkr : k ≤ r)
    {nr v : ZMod p} (hnr : nr ≠ 0) (hv : v ≠ 0) {u w : ℕ} (hu : u < k) (hw : w < k) :
    Tsym p k nr v u w - (nr⁻¹ * v ^ 2)⁻¹ * ∑ c ∈ Ico k r, Tsym p k nr v u c * Tsym p k nr v w c =
      (if u = w then nr⁻¹ * H2 (p := p) (k - 1) else 0) +
        nr⁻¹ * ∑ i ∈ Icc 1 d,
          ((u : ZMod p) + (i : ZMod p))⁻¹ * ((w : ZMod p) + (i : ZMod p))⁻¹ := by
  have hkp : k ≤ p := by omega
  have hrp : r ≤ p := by omega
  -- the high block
  have hS : (nr⁻¹ * v ^ 2)⁻¹ * ∑ c ∈ Ico k r, Tsym p k nr v u c * Tsym p k nr v w c =
      nr⁻¹ * ∑ c ∈ Ico k r, cauchyKer (p := p) u w c := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c hc => ?_
    have hc' := mem_Ico.1 hc
    rw [Tsym_lh hu hc'.1 (by omega), Tsym_lh hw hc'.1 (by omega)]
    unfold cauchyKer
    field_simp
  have hsplit : ∀ f : ℕ → ZMod p, ∑ c ∈ Ico k p, f c = ∑ c ∈ Ico k r, f c + ∑ c ∈ Ico r p, f c :=
    fun f => (Finset.sum_Ico_consecutive f hkr hrp).symm
  rw [hS]
  rcases lt_trichotomy u w with huw | huw | huw
  · rw [if_neg huw.ne, zero_add]
    have hTs : Tsym p k nr v u w = nr⁻¹ * ∑ c ∈ Ico k p, cauchyKer (p := p) u w c := by
      unfold Tsym; rw [if_pos huw]; unfold Tg; rw [if_pos hw]
      have := pt_loewner (p := p) huw hw hkp (by omega)
      rw [← this, div_eq_inv_mul]
    rw [hTs, hsplit, sum_cauchy_refl hrd]
    ring
  · subst huw
    rw [if_pos rfl, Tsym_diag_lt p k nr v hu]
    have hd := pt_diag (p := p) hp5 hkp u
    have hsq : ∀ c : ℕ, cauchyKer (p := p) u u c = ((((c : ZMod p) - u)⁻¹) ^ 2) := by
      intro c; unfold cauchyKer; ring
    have hd' : E2 (p := p) k u - ∑ x ∈ Ico k p, cauchyKer (p := p) u u x = H2 (p := p) (k - 1) := by
      simp_rw [hsq]; exact hd
    rw [hsplit] at hd'
    rw [← sum_cauchy_refl hrd u u]
    linear_combination nr⁻¹ * hd'
  · rw [if_neg huw.ne', Tsym_symm p k nr v u w]
    have hS2 : ∑ c ∈ Ico k r, Tsym p k nr v u c * Tsym p k nr v w c =
        ∑ c ∈ Ico k r, Tsym p k nr v w c * Tsym p k nr v u c :=
      Finset.sum_congr rfl fun c _ => mul_comm _ _
    have hTs : Tsym p k nr v w u = nr⁻¹ * ∑ c ∈ Ico k p, cauchyKer (p := p) w u c := by
      unfold Tsym; rw [if_pos huw]; unfold Tg; rw [if_pos hu]
      have := pt_loewner (p := p) huw hu hkp (by omega)
      rw [← this, div_eq_inv_mul]
    rw [hTs, hsplit, sum_cauchy_refl hrd]
    simp_rw [cauchyKer_comm u w]
    have e : ∑ i ∈ Icc 1 d, ((u : ZMod p) + (i : ZMod p))⁻¹ * ((w : ZMod p) + (i : ZMod p))⁻¹ =
        ∑ i ∈ Icc 1 d, ((w : ZMod p) + (i : ZMod p))⁻¹ * ((u : ZMod p) + (i : ZMod p))⁻¹ :=
      Finset.sum_congr rfl fun i _ => mul_comm _ _
    rw [e]
    ring

/-! ### The matrix identity over `𝔽_p(X)` -/

section Mat

variable (r m k : ℕ) (nr v : ZMod p)

noncomputable def s0g : RatFunc (ZMod p) := rfX p + rfC p (nr⁻¹ * H2 (p := p) (k - 1))

noncomputable def κg : RatFunc (ZMod p) := rfC p (-nr⁻¹)

/-- **LP2 Schur identity over `𝔽_p(X)`**: `Ā00 - π⁻¹ V Vᵀ = s₀ I - κ E Eᵀ`. -/
theorem hS_g (hp5 : 5 ≤ p) {d : ℕ} (hrd : r + d = p) (hkr : k ≤ r) (hnr : nr ≠ 0) (hv : v ≠ 0) :
    A0g p r k nr v - (piG p nr v)⁻¹ • (Vg p r k nr v * (Vg p r k nr v)ᵀ) =
      s0g k nr • (1 : Matrix (Blk0 r k) (Blk0 r k) _) -
        κg nr • (EL p r k d * (EL p r k d)ᵀ) := by
  ext u w
  have hZ := schur_scalar hp5 hrd hkr hnr hv (u := u.1.val) (w := w.1.val) u.2 w.2
  have hpi : (piG p nr v)⁻¹ = rfCH p ((nr⁻¹ * v ^ 2)⁻¹) := by
    unfold piG; rw [rfC_eq, map_inv₀]
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.mul_apply, Matrix.transpose_apply,
    smul_eq_mul, A0g, Vg, EL, Matrix.of_apply, Matrix.one_apply, s0g, κg]
  have h1 : ∑ c : Blk1 r k, rfC p (Tsym p k nr v u.1.val c.1.val) *
        rfC p (Tsym p k nr v w.1.val c.1.val) =
      ∑ c ∈ Ico k r, rfC p (Tsym p k nr v u.1.val c) * rfC p (Tsym p k nr v w.1.val c) :=
    sum_Blk1 r k (M := RatFunc (ZMod p)) (fun c => rfC p (Tsym p k nr v u.1.val c) *
      rfC p (Tsym p k nr v w.1.val c)) hkr
  have h2 : ∑ i : Fin d, rfC p ((((u.1 : ℕ) : ZMod p) + (((i : ℕ) + 1 : ℕ) : ZMod p))⁻¹) *
        rfC p ((((w.1 : ℕ) : ZMod p) + (((i : ℕ) + 1 : ℕ) : ZMod p))⁻¹) =
      ∑ i ∈ Icc 1 d, rfC p ((((u.1 : ℕ) : ZMod p) + ((i : ℕ) : ZMod p))⁻¹) *
        rfC p ((((w.1 : ℕ) : ZMod p) + ((i : ℕ) : ZMod p))⁻¹) :=
    sum_FinD (M := RatFunc (ZMod p)) (fun i => rfC p ((((u.1 : ℕ) : ZMod p) + ((i : ℕ) : ZMod p))⁻¹) *
      rfC p ((((w.1 : ℕ) : ZMod p) + ((i : ℕ) : ZMod p))⁻¹)) d
  rw [h1, h2, hpi]
  have hZ' := congrArg (rfCH p) hZ
  simp only [rfC_eq, map_sub, map_mul, map_add, map_sum, map_inv₀, map_one,
    map_neg, apply_ite (rfCH p), map_zero] at hZ' ⊢
  by_cases huw : u = w
  · subst huw
    simp only [if_true, mul_one] at hZ' ⊢
    linear_combination hZ'
  · have hne : u.1.val ≠ w.1.val := fun h => huw (Subtype.ext (Fin.ext h))
    simp only [if_neg huw, if_neg hne, mul_zero] at hZ' ⊢
    linear_combination hZ'

end Mat

end CatalanCore.Uniform.Content.Smith
