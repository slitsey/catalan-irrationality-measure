module

public import CatalanCore.Star.Leonard.GoodForm

/-!
# Step ratios with support `c ≥ 0`

`GoodF0 ℓ B f`: on positive generic rationals `f θ = C · ∏_{c<B} (θ + c)^{e_c}` with `C` an
`ℓ`-unit.  A step ratio `R(θ)` of this form gives, in the descending orientation,
`u(…,θ) = u(…,θ+1)/R(θ+1)` with `R(θ+1)` of the *good* form (support `c ≥ 1`).
-/

@[expose] public section

open Finset CatalanCore.ThmA

namespace CatalanCore.Star.Leonard

variable {ℓ : ℕ} [Fact ℓ.Prime]

def GoodF0 (ℓ B : ℕ) [Fact ℓ.Prime] (f : ℚ → ℚ) : Prop :=
  ∃ C : ℚ, LU ℓ C ∧ ∃ e : ℕ → ℤ, ∀ θ : ℚ, 0 < θ → Gen θ →
    f θ = C * ∏ c ∈ range B, (θ + (c : ℚ)) ^ e c

lemma lin_pos0 {θ : ℚ} (h : 0 < θ) (c : ℕ) : θ + (c : ℚ) ≠ 0 := by
  have : (0 : ℚ) ≤ (c : ℚ) := Nat.cast_nonneg _
  linarith

lemma GoodF0.congr {B : ℕ} {f g : ℚ → ℚ} (hf : GoodF0 ℓ B f)
    (h : ∀ θ : ℚ, 0 < θ → Gen θ → f θ = g θ) : GoodF0 ℓ B g := by
  obtain ⟨C, hC, e, he⟩ := hf
  exact ⟨C, hC, e, fun θ h0 hg => by rw [← h θ h0 hg, he θ h0 hg]⟩

lemma GoodF.congr {B : ℕ} {f g : ℚ → ℚ} (hf : GoodF ℓ B f)
    (h : ∀ θ : ℚ, 0 < θ → Gen θ → f θ = g θ) : GoodF ℓ B g := by
  obtain ⟨C, hC, e, he⟩ := hf
  exact ⟨C, hC, e, fun θ h0 hg => by rw [← h θ h0 hg, he θ h0 hg]⟩

lemma GoodF0.mono {B B' : ℕ} (h : B ≤ B') {f : ℚ → ℚ} (hf : GoodF0 ℓ B f) : GoodF0 ℓ B' f := by
  obtain ⟨C, hC, e, he⟩ := hf
  refine ⟨C, hC, fun c => if c < B then e c else 0, fun θ h0 hg => ?_⟩
  rw [he θ h0 hg]
  congr 1
  rw [← Finset.prod_subset (Finset.range_subset_range.2 h) (f := fun c : ℕ =>
      (θ + (c : ℚ)) ^ (if c < B then e c else 0))]
  · exact Finset.prod_congr rfl fun c hc => by rw [if_pos (Finset.mem_range.1 hc)]
  · intro c _ hc; rw [if_neg (by simpa using hc)]; simp

lemma GoodF0.mul {B : ℕ} {f g : ℚ → ℚ} (hf : GoodF0 ℓ B f) (hg : GoodF0 ℓ B g) :
    GoodF0 ℓ B (fun θ => f θ * g θ) := by
  obtain ⟨C, hC, e, he⟩ := hf
  obtain ⟨C', hC', e', he'⟩ := hg
  refine ⟨C * C', hC.mul hC', fun c => e c + e' c, fun θ h0 hgen => ?_⟩
  simp only [he θ h0 hgen, he' θ h0 hgen]
  have : ∏ c ∈ range B, (θ + (c : ℚ)) ^ (e c + e' c) =
      (∏ c ∈ range B, (θ + (c : ℚ)) ^ e c) * ∏ c ∈ range B, (θ + (c : ℚ)) ^ e' c := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun c _ => zpow_add₀ (lin_pos0 h0 c) _ _
  rw [this]; ring

lemma GoodF0.inv {B : ℕ} {f : ℚ → ℚ} (hf : GoodF0 ℓ B f) : GoodF0 ℓ B (fun θ => (f θ)⁻¹) := by
  obtain ⟨C, hC, e, he⟩ := hf
  refine ⟨C⁻¹, hC.inv, fun c => - e c, fun θ h0 hgen => ?_⟩
  simp only [he θ h0 hgen, mul_inv]
  congr 1
  rw [← Finset.prod_inv_distrib]
  exact Finset.prod_congr rfl fun c _ => by rw [zpow_neg]

lemma GoodF0.div {B : ℕ} {f g : ℚ → ℚ} (hf : GoodF0 ℓ B f) (hg : GoodF0 ℓ B g) :
    GoodF0 ℓ B (fun θ => f θ / g θ) := by
  have := hf.mul hg.inv
  simpa [div_eq_mul_inv] using this

lemma GoodF0.const {B : ℕ} {C : ℚ} (hC : LU ℓ C) : GoodF0 ℓ B (fun _ => C) :=
  ⟨C, hC, fun _ => 0, fun θ _ _ => by simp⟩

lemma GoodF0.lin {B : ℕ} (c : ℕ) (hc : c < B) (k : ℤ) :
    GoodF0 ℓ B (fun θ => (θ + (c : ℚ)) ^ k) :=
  ⟨1, LU.one, fun x => if x = c then k else 0, fun θ _ _ => by
    rw [one_mul, Finset.prod_eq_single c]
    · simp
    · intro b _ hb; simp [hb]
    · intro h; exact absurd (Finset.mem_range.2 hc) h⟩

lemma GoodF0.prod {ι : Type*} {B : ℕ} (s : Finset ι) (f : ι → ℚ → ℚ)
    (h : ∀ i ∈ s, GoodF0 ℓ B (f i)) : GoodF0 ℓ B (fun θ => ∏ i ∈ s, f i θ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (GoodF0.const (B := B) (LU.one : LU ℓ 1))
  | insert a s ha ih =>
    have h1 := h a (Finset.mem_insert_self a s)
    have h2 := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    simpa [Finset.prod_insert ha] using h1.mul h2

/-- the descending shift: a step ratio of support `≥ 0` becomes good at `θ + 1`. -/
lemma GoodF0.shift1 {B : ℕ} {f : ℚ → ℚ} (hf : GoodF0 ℓ B f) :
    GoodF ℓ B (fun θ => f (θ + 1)) := by
  obtain ⟨C, hC, e, he⟩ := hf
  refine ⟨C, hC, e, fun θ h0 hgen => ?_⟩
  have h0' : 0 < θ + 1 := by linarith
  have hg' : Gen (θ + 1) := by
    intro z; have := hgen (z + 1); push_cast at this; intro h; apply this; linear_combination h
  show f (θ + 1) = _
  rw [he (θ + 1) h0' hg']
  congr 1
  exact Finset.prod_congr rfl fun c _ => by push_cast; ring_nf

/-- a good function is `GoodF0` (support `c ≥ 1` is a special case) -/
lemma GoodF.toF0 {B : ℕ} {f : ℚ → ℚ} (hf : GoodF ℓ B f) : GoodF0 ℓ (B + 1) f := by
  obtain ⟨C, hC, e, he⟩ := hf
  refine ⟨C, hC, fun c => if c = 0 then 0 else e (c - 1), fun θ h0 hgen => ?_⟩
  rw [he θ h0 hgen, Finset.prod_range_succ']
  simp only [Nat.succ_ne_zero, if_false, Nat.add_sub_cancel, if_true, zpow_zero, mul_one]

end CatalanCore.Star.Leonard
