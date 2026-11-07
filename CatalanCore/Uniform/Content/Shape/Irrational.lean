module

public import CatalanCore.Measure.Scaling
public import CatalanCore.Uniform.Measure.NV0
public import CatalanCore.Uniform.Content.Shape.Reindex

@[expose] public section
set_option Elab.async false

/-!
# Irrationality from a family, and the measure for all fractions (generic part)

`MeasureLBAt x E` bounds `|x - p/q|` for reduced fractions only, and every rational `x` satisfies it.
For irrational `x` the same bound holds for all fractions `p/q` (`MeasureLBAt.all_of_irrational`).
`irrational_of_family_nv0_even` is the even-scale form of `irrational_of_family_nv0` (the same reindexing
`s = r / 2` as `measure_of_family_nv0_even`); it needs no bank, so plane modules can import it.
The per-bank irrationality statements stay in `Bank.Irrational`.
-/

namespace CatalanCore.Measure

/-- The measure statement for every fraction `p/q`, reduced or not. -/
def MeasureAt (x E : ℝ) : Prop :=
  ∀ e > 0, ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), q₀ ≤ q → (q : ℝ) ^ (-(E + e)) < |x - (p : ℝ) / q|

/-- For irrational `x` the bound for reduced fractions gives the bound for all fractions. -/
theorem MeasureLBAt.all_of_irrational {x E : ℝ} (hE : 0 ≤ E) (hx : Irrational x)
    (h : MeasureLBAt x E) : MeasureAt x E := by
  intro e he
  have hL := h.not_liouvilleWith hE (r := E + e / 2) (by linarith)
  have hev : ∀ᶠ n : ℕ in Filter.atTop,
      ¬ ∃ m : ℤ, x ≠ m / n ∧ |x - m / n| < 1 / (n : ℝ) ^ (E + e / 2) := by
    exact Filter.not_frequently.1 fun hf => hL ⟨1, hf⟩
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hev
  refine ⟨max N 2, fun p q hq => ?_⟩
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast le_trans (le_max_right _ _) hq
  have hne : x ≠ (p : ℝ) / q := fun e => hx ⟨(p : ℚ) / q, by push_cast; exact e.symm⟩
  have h1 : 1 / (q : ℝ) ^ (E + e / 2) ≤ |x - p / q| := by
    by_contra hlt
    exact hN q (le_trans (le_max_left _ _) hq) ⟨p, hne, lt_of_not_ge hlt⟩
  refine lt_of_lt_of_le ?_ h1
  rw [one_div, ← Real.rpow_neg (by linarith)]
  exact Real.rpow_lt_rpow_of_exponent_lt (by linarith) (by linarith)

/-- Irrationality passes from `x` to `T` when `x = a T` with rational `a ≠ 0`. -/
theorem irrational_of_eq_mul {x T : ℝ} {a : ℚ} (ha : a ≠ 0) (hx : Irrational x)
    (h : x = (a : ℝ) * T) : Irrational T := by
  have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha
  have hT : T = ((a⁻¹ : ℚ) : ℝ) * x + ((0 : ℚ) : ℝ) := by
    rw [h, Rat.cast_inv, Rat.cast_zero, add_zero, ← mul_assoc, inv_mul_cancel₀ ha', one_mul]
  rw [hT]
  exact irrational_affine hx _ _ (inv_ne_zero ha)

end CatalanCore.Measure

namespace CatalanCore.Uniform
open Real

/-- Irrationality from the hypotheses of `measure_of_family_nv0_even` (same reindexing `s = r / 2`). -/
theorem irrational_of_family_nv0_even (Fam : PolyFamily) (scale : Fam.ι → ℕ)
    {Λ D c γ K : ℝ} (hΛ : HasScaledContent Fam scale Λ)
    (hD : HasScaledDecay Fam scale D c) (hη : Λ < D) (hc : 0 < c)
    (hγ : 0 < γ) (hK : 0 ≤ K)
    (hdeg : ∀ n, Fam.Adm n → (Fam.deg n : ℝ) ≤ γ * scale n + K)
    (heven : ∀ n, Fam.Adm n → scale n % 2 = 0)
    (hnv : ∃ R0 : ℕ, ∀ s : ℕ, R0 ≤ s → ∀ x : ℚ,
      ∃ n, Fam.Adm n ∧ scale n = 2 * s ∧ Fam.evalQ n x ≠ 0) :
    Irrational Fam.const := by
  have hcast : ∀ n, Fam.Adm n → (scale n : ℝ) = 2 * ((scale n / 2 : ℕ) : ℝ) := by
    intro n hn
    have := heven n hn
    exact_mod_cast (by omega : scale n = 2 * (scale n / 2))
  have hΛ' : HasScaledContent Fam (fun n => scale n / 2) (4 * Λ) := by
    obtain ⟨den, hpos, hint, hlog⟩ := hΛ
    refine ⟨den, hpos, hint, ?_⟩
    intro ε hε
    obtain ⟨R0, h⟩ := hlog (ε / 4) (by positivity)
    refine ⟨R0, fun n hn hr => ?_⟩
    have h1 := h n hn (by have := heven n hn; have hr' : R0 ≤ scale n / 2 := hr; omega)
    rw [hcast n hn] at h1
    nlinarith [h1]
  have hD' : HasScaledDecay Fam (fun n => scale n / 2) (4 * D) (2 * c) := by
    intro ε hε
    obtain ⟨R0, h⟩ := hD (ε / 4) (by positivity)
    refine ⟨R0, fun n hn hr t ht => ?_⟩
    have hs := hcast n hn
    have hs0 : (0 : ℝ) ≤ ((scale n / 2 : ℕ) : ℝ) := Nat.cast_nonneg _
    have h1 := h n hn (by have := heven n hn; have hr' : R0 ≤ scale n / 2 := hr; omega) t (by
      refine ht.trans (Real.exp_le_exp.2 ?_)
      rw [hs]
      nlinarith)
    refine h1.trans (le_of_eq ?_)
    congr 1
    rw [hs]
    ring
  have hnv' : HasNV0 Fam (fun n => scale n / 2) := by
    obtain ⟨R0, h⟩ := hnv
    refine ⟨R0, fun r hr x => ?_⟩
    obtain ⟨n, hn, hs, hne⟩ := h r hr x
    exact ⟨n, hn, by show scale n / 2 = r; omega, hne⟩
  have hdeg' : ∀ n, Fam.Adm n → (Fam.deg n : ℝ) ≤ (2 * γ) * ((scale n / 2 : ℕ) : ℝ) + K := by
    intro n hn
    have := hdeg n hn
    rw [hcast n hn] at this
    linarith
  exact irrational_of_family_nv0 Fam (fun n => scale n / 2) hΛ' hD' (by linarith)
    (by positivity) hK hdeg' hnv'

end CatalanCore.Uniform
