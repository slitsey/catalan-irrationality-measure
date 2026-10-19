module

public import CatalanCore.Star.Leonard.KgenLUL

/-!
# The "good form" interface: `kgen = C · ∏_{c ≤ B} (θ+c)^{e_c}` with `C` an `ℓ`-unit

To get `LU ℓ (kgen(0))` it is enough to know that, for rational `θ > 0`, `kgen K m S θ` is an
`ℓ`-unit times an *integer-exponent* product of the factors `θ + c`, `1 ≤ c ≤ B < ℓ`
(no need for the exact exponents `ec` or for `κ_S`).  `GoodF ℓ B f` is this property.  The induction
(diagonal steps in `S`, Darboux K-steps in `n`) only has to show that every step ratio is good
with support `c ≥ 0` (shifted to `c ≥ 1` by the descending orientation).
-/

@[expose] public section

open Finset Filter Topology CatalanCore.ThmA

namespace CatalanCore.Star.Leonard

/-- `f` is, on positive generic rationals, an `ℓ`-unit times `∏_{c<B} (θ + (c+1))^{e c}`. -/
def GoodF (ℓ B : ℕ) [Fact ℓ.Prime] (f : ℚ → ℚ) : Prop :=
  ∃ C : ℚ, LU ℓ C ∧ ∃ e : ℕ → ℤ, ∀ θ : ℚ, 0 < θ → Gen θ →
    f θ = C * ∏ c ∈ range B, (θ + ((c + 1 : ℕ) : ℚ)) ^ e c

variable {ℓ : ℕ} [Fact ℓ.Prime]

lemma lin_pos {θ : ℚ} (h : 0 < θ) (c : ℕ) : θ + ((c + 1 : ℕ) : ℚ) ≠ 0 := by
  have : (0 : ℚ) ≤ ((c + 1 : ℕ) : ℚ) := Nat.cast_nonneg _
  linarith

lemma GoodF.mono {B B' : ℕ} (h : B ≤ B') {f : ℚ → ℚ} (hf : GoodF ℓ B f) : GoodF ℓ B' f := by
  obtain ⟨C, hC, e, he⟩ := hf
  refine ⟨C, hC, fun c => if c < B then e c else 0, fun θ h0 hg => ?_⟩
  rw [he θ h0 hg]
  congr 1
  rw [← Finset.prod_subset (Finset.range_subset_range.2 h) (f := fun c =>
      (θ + ((c + 1 : ℕ) : ℚ)) ^ (if c < B then e c else 0))]
  · exact Finset.prod_congr rfl fun c hc => by rw [if_pos (Finset.mem_range.1 hc)]
  · intro c _ hc; rw [if_neg (by simpa using hc)]; simp

lemma GoodF.mul {B : ℕ} {f g : ℚ → ℚ} (hf : GoodF ℓ B f) (hg : GoodF ℓ B g) :
    GoodF ℓ B (fun θ => f θ * g θ) := by
  obtain ⟨C, hC, e, he⟩ := hf
  obtain ⟨C', hC', e', he'⟩ := hg
  refine ⟨C * C', hC.mul hC', fun c => e c + e' c, fun θ h0 hgen => ?_⟩
  simp only [he θ h0 hgen, he' θ h0 hgen]
  have : ∏ c ∈ range B, (θ + ((c + 1 : ℕ) : ℚ)) ^ (e c + e' c) =
      (∏ c ∈ range B, (θ + ((c + 1 : ℕ) : ℚ)) ^ e c) * ∏ c ∈ range B, (θ + ((c + 1 : ℕ) : ℚ)) ^ e' c := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun c _ => zpow_add₀ (lin_pos h0 c) _ _
  rw [this]; ring

lemma GoodF.inv {B : ℕ} {f : ℚ → ℚ} (hf : GoodF ℓ B f) : GoodF ℓ B (fun θ => (f θ)⁻¹) := by
  obtain ⟨C, hC, e, he⟩ := hf
  refine ⟨C⁻¹, hC.inv, fun c => - e c, fun θ h0 hgen => ?_⟩
  simp only [he θ h0 hgen, mul_inv]
  congr 1
  rw [← Finset.prod_inv_distrib]
  exact Finset.prod_congr rfl fun c _ => by rw [zpow_neg]

lemma GoodF.div {B : ℕ} {f g : ℚ → ℚ} (hf : GoodF ℓ B f) (hg : GoodF ℓ B g) :
    GoodF ℓ B (fun θ => f θ / g θ) := by
  have := hf.mul hg.inv
  simpa [div_eq_mul_inv] using this

lemma GoodF.const {B : ℕ} {C : ℚ} (hC : LU ℓ C) : GoodF ℓ B (fun _ => C) :=
  ⟨C, hC, fun _ => 0, fun θ _ _ => by simp⟩

lemma GoodF.lin {B : ℕ} (c : ℕ) (hc : c < B) (k : ℤ) :
    GoodF ℓ B (fun θ => (θ + ((c + 1 : ℕ) : ℚ)) ^ k) :=
  ⟨1, LU.one, fun x => if x = c then k else 0, fun θ _ _ => by
    rw [one_mul, Finset.prod_eq_single c]
    · simp
    · intro b _ hb; simp [hb]
    · intro h; exact absurd (Finset.mem_range.2 hc) h⟩

/-- shift `θ ↦ θ + 1` raises the support by one -/
lemma GoodF.shift1 {B : ℕ} {f : ℚ → ℚ} (hf : GoodF ℓ B f) :
    GoodF ℓ (B + 1) (fun θ => f (θ + 1)) := by
  obtain ⟨C, hC, e, he⟩ := hf
  refine ⟨C, hC, fun c => if c = 0 then 0 else e (c - 1), fun θ h0 hgen => ?_⟩
  have h0' : 0 < θ + 1 := by linarith
  have hg' : Gen (θ + 1) := by
    intro z; have := hgen (z + 1); push_cast at this; intro h; apply this; linear_combination h
  show f (θ + 1) = C * ∏ c ∈ range (B + 1), (θ + ((c + 1 : ℕ) : ℚ)) ^ (if c = 0 then 0 else e (c - 1))
  rw [he (θ + 1) h0' hg', Finset.prod_range_succ']
  simp only [if_pos, zpow_zero, mul_one, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
  congr 1
  exact Finset.prod_congr rfl fun c _ => by push_cast; ring_nf

lemma GoodF.shift {B : ℕ} {f : ℚ → ℚ} (hf : GoodF ℓ B f) (j : ℕ) :
    GoodF ℓ (B + j) (fun θ => f (θ + j)) := by
  induction j with
  | zero => simpa using hf
  | succ j ih =>
    have := ih.shift1
    convert this using 2 with θ
    push_cast; ring_nf

/-! ### Consumers: `LU ℓ (kgen(0))` from the good form -/

lemma goodF_cont {B : ℕ} (C : ℚ) (e : ℕ → ℤ) :
    ContinuousAt (fun θ : ℚ => C * ∏ c ∈ range B, (θ + ((c + 1 : ℕ) : ℚ)) ^ e c) 0 := by
  refine continuousAt_const.mul ?_
  apply tendsto_finset_prod
  intro c _
  refine ContinuousAt.tendsto ?_
  refine ContinuousAt.zpow₀ (by fun_prop) _ (Or.inl ?_)
  simp only [zero_add]; exact_mod_cast (by omega : c + 1 ≠ 0)

lemma goodF_zero_LU {B : ℕ} (hB : B < ℓ) {C : ℚ} (hC : LU ℓ C) (e : ℕ → ℤ) :
    LU ℓ (C * ∏ c ∈ range B, ((0 : ℚ) + ((c + 1 : ℕ) : ℚ)) ^ e c) := by
  refine hC.mul (LU.prod _ _ fun c hc => LU_zpow ?_ _)
  have := Finset.mem_range.1 hc
  simp only [zero_add]
  exact LU_natCast_lt (by omega) (by omega)

theorem kgen_LU_of_good (K m S B : ℕ) (hmK : m < K) (hS : K - m ≤ S) (hB : B < ℓ)
    (hg : GoodF ℓ B (kgen K m S)) : LU ℓ (kgen K m S (0 : ℚ)) := by
  obtain ⟨C, hC, e, he⟩ := hg
  have h0 := kgenR_zero_of_generic K m S (by omega) hmK.le (by omega)
    (fun θ => C * ∏ c ∈ range B, (θ + ((c + 1 : ℕ) : ℚ)) ^ e c) (goodF_cont C e)
    (fun θ h0 h1 => he θ h0 (gen_of_small h0 h1))
  rw [h0]
  exact goodF_zero_LU hB hC e

theorem kgenL_LU_of_good (K m S B : ℕ) (hmK : m < K) (hS : K - m ≤ S)
    (hl : S + K + 2 * m ≤ ℓ) (hB : B < ℓ) (hg : GoodF ℓ B (kgen K m S)) :
    LU ℓ (kgenL K m (0 : ℚ) (Finset.Icc 1 ((S : ℤ) - 1)) S) := by
  obtain ⟨C, hC, e, he⟩ := hg
  have hS1 : 1 ≤ S := by omega
  have hX : piB (bX m S) (S : ℚ) ≠ 0 := piB_ne m S _ (fun i => by simp only [bX]; omega)
  set Fn : ℚ → ℚ := fun θ => C * ∏ c ∈ range B, (θ + ((c + 1 : ℕ) : ℚ)) ^ e c with hFn
  have hcont : ContinuousAt (fun θ : ℚ => (cSL K m S θ / cSR K m S θ) ^ (K - m) * Fn θ) 0 := by
    refine ContinuousAt.mul (ContinuousAt.pow (ContinuousAt.div (cA_cS K m S hS1 _)
      (cA_cS K m S hS1 _) ?_) _) (goodF_cont C e)
    show piB (bX m S) (S : ℚ) / ∏ a : Fin K, ((0 : ℚ) + ((a : ℕ) : ℚ) + (S : ℚ)) ≠ 0
    exact div_ne_zero hX (by simpa using prodAS_ne K S hS1 0 le_rfl)
  have h0 := kgenL_zero_of_generic K m S (by omega) hmK.le hS1
    (fun θ => (cSL K m S θ / cSR K m S θ) ^ (K - m) * Fn θ) hcont (by
      intro θ h0 h1
      have hR := kgenL_generic K m S hmK hS1 θ h0 h1
      have hcR : cSR K m S θ ≠ 0 := by
        simp only [cSR]
        exact div_ne_zero hX (prodAS_ne K S hS1 θ h0.le)
      have hk : Fn θ = kgen K m S θ := (he θ h0 (gen_of_small h0 h1)).symm
      rw [hk]
      have hpow : cSR K m S θ ^ (K - m) ≠ 0 := pow_ne_zero _ hcR
      rw [div_pow, div_mul_eq_mul_div, eq_div_iff hpow]
      linear_combination hR)
  rw [h0]
  simp only [cSL, cSR, zero_add]
  have hP : ∏ a : Fin K, ((0 : ℚ) + ((a : ℕ) : ℚ) + (S : ℚ)) ≠ 0 := by simpa using prodAS_ne K S hS1 0 le_rfl
  have hY : LU ℓ (piB (bY m S) (S : ℚ)) := LU_piB m S _ (fun i => by
    have := i.2; simp only [bY]; omega)
  have hXl : LU ℓ (piB (bX m S) (S : ℚ)) := LU_piB m S _ (fun i => by
    have := i.2; simp only [bX]; omega)
  have hq : (piB (bY m S) (S : ℚ) / ∏ a : Fin K, ((0 : ℚ) + ((a : ℕ) : ℚ) + (S : ℚ))) /
      (piB (bX m S) (S : ℚ) / ∏ a : Fin K, ((0 : ℚ) + ((a : ℕ) : ℚ) + (S : ℚ))) =
      piB (bY m S) (S : ℚ) / piB (bX m S) (S : ℚ) := by
    field_simp
  simp only [zero_add] at hq hP ⊢
  rw [hq]
  have hF0 : LU ℓ (Fn 0) := goodF_zero_LU hB hC e
  exact ((hY.div hXl).pow _).mul hF0

end CatalanCore.Star.Leonard
