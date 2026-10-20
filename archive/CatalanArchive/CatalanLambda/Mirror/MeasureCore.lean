module

public import CatalanArchive.CatalanLambda.Mirror.Sep
public import CatalanArchive.CatalanLambda.Mirror.Prime
public import CatalanArchive.CatalanLambda.Mirror.Irrational

@[expose] public section

/-!
# The irrationality measure of `λ'`: the generic deduction (mirror of BN §4)
-/

open Filter

namespace CatalanLambda.Mirror

open CatalanLambda.Decay

/-- **Generic measure deduction.**  Suppose that for all `a > 0`, `b > a + s` and all large `q`,
there are `ℓ ∈ (a log q, b log q]` and `h ∈ [(3ℓ-1)/4, ℓ-1]` with `P̄_h(p/q) ≠ 0`.  Then for every
`e > 0` and all large `q`, `|λ - p/q| > q^{-(c (4/(3η) + s) + e)}`, where `c = c_cert` and
`η = D_cert - 313/105`. -/
theorem measure_core {K : ℕ} {ρ ε : ℝ} {c : Fin K → ℂ} {m : Fin K → ℝ}
    (F : CertFacts K ρ ε c m) (hD : (313 / 105 : ℝ) < F.Dcert) (hc : 0 < (F.ccert : ℝ))
    (s : ℝ) (hs : 0 < s) (Pr : ℤ → ℕ → Prop)
    (Hex : ∀ a b : ℝ, 0 < a → a + s < b → ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), Pr p q → q₀ ≤ q →
      ∃ ℓ h : ℕ, a * Real.log q < ℓ ∧ (ℓ : ℝ) ≤ b * Real.log q ∧ 3 * ℓ ≤ 4 * h + 4 ∧
        h ≤ ℓ - 1 ∧ Pbar h ((p : ℚ) / (q : ℚ)) ≠ 0)
    {e : ℝ} (he : 0 < e) :
    ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), Pr p q → q₀ ≤ q →
      (q : ℝ) ^ (-((F.ccert : ℝ) * (4 / (3 * ((F.Dcert : ℝ) - 313 / 105)) + s) + e))
        < |lamB - (p : ℝ) / q| := by
  set η : ℝ := (F.Dcert : ℝ) - 313 / 105 with hη
  have hη0 : 0 < η := by rw [hη]; linarith
  set M : ℝ := (F.ccert : ℝ) * (4 / (3 * η) + s) with hM
  have hM0 : 0 < M := by rw [hM]; have : 0 < 4 / (3 * η) := by positivity
                         positivity
  set δ : ℝ := e / M with hδ
  have hδ0 : 0 < δ := div_pos he hM0
  set a : ℝ := 4 / 3 * (1 + δ) / η with ha
  set b : ℝ := (1 + δ) * (4 / (3 * η) + s) with hb
  have ha0 : 0 < a := by rw [ha]; positivity
  have hab : a + s < b := by
    have : b = a + (1 + δ) * s := by rw [hb, ha]; field_simp
    rw [this]; nlinarith
  have hcb : M + e = (F.ccert : ℝ) * b := by
    have : e = δ * M := by rw [hδ]; field_simp
    rw [this, hb, hM]; ring
  set θ : ℝ := η * (1 + δ / 2) / (1 + δ) with hθ
  have hθ0 : 0 < θ := by rw [hθ]; positivity
  have hθη : θ < η := by
    rw [hθ, div_lt_iff₀ (by positivity)]; nlinarith
  obtain ⟨h₀, H⟩ := sep_core F hθ0 (by rw [hη] at hθη; exact hθη)
  obtain ⟨q₁, hq₁⟩ := Hex a b ha0 hab
  set L₁ : ℝ := max ((4 * h₀ + 8) / a) (2 * θ / δ + 1) with hL₁
  refine ⟨max q₁ ⌈Real.exp L₁⌉₊, fun p q hPr hq => ?_⟩
  have hq1 : q₁ ≤ q := le_trans (le_max_left _ _) hq
  have hqe : Real.exp L₁ ≤ q := le_trans (Nat.le_ceil _) (by exact_mod_cast le_trans (le_max_right _ _) hq)
  have hqpos : (0 : ℝ) < q := lt_of_lt_of_le (Real.exp_pos _) hqe
  have hq0 : 0 < q := by exact_mod_cast hqpos
  have hL : L₁ ≤ Real.log q := (Real.le_log_iff_exp_le hqpos).2 hqe
  set L := Real.log q with hLdef
  by_contra hcon
  push Not at hcon
  obtain ⟨ℓ, h, hl1, hl2, hh1, hh2, hP⟩ := hq₁ p q hPr hq1
  have hLa : (4 * h₀ + 8 : ℝ) ≤ a * L := by
    have : (4 * h₀ + 8 : ℝ) / a ≤ L := le_trans (le_max_left _ _) hL
    rw [div_le_iff₀ ha0] at this; linarith
  have hLδ : 2 * θ / δ + 1 ≤ L := le_trans (le_max_right _ _) hL
  have hℓh : 4 * h₀ + 8 < ℓ := by
    have : (4 * h₀ + 8 : ℝ) < ℓ := by linarith
    exact_mod_cast this
  have hh0 : h₀ ≤ h := by omega
  have hhℓ : (h : ℝ) ≤ b * L := by
    have : h ≤ ℓ := by omega
    have : (h : ℝ) ≤ ℓ := by exact_mod_cast this
    linarith
  have hclose : |lamB - (p : ℝ) / q| ≤ Real.exp (-(F.ccert : ℝ) * h) := by
    refine le_trans hcon ?_
    rw [Real.rpow_def_of_pos hqpos, ← hLdef, hcb]
    apply Real.exp_le_exp.2
    nlinarith [mul_le_mul_of_nonneg_left hhℓ hc.le]
  have key := H h hh0 p (q : ℤ) (by exact_mod_cast hq0) (by simpa using hP) (by simpa using hclose)
  simp only [Int.cast_natCast] at key
  have h4 : (3 * (ℓ : ℝ) - 4) ≤ 4 * h := by
    have : 3 * ℓ ≤ 4 * h + 4 := hh1
    have : (3 * ℓ : ℝ) ≤ 4 * h + 4 := by exact_mod_cast this
    linarith
  have hθa : θ * (3 * a / 4) = 1 + δ / 2 := by rw [hθ, ha]; field_simp
  have hδL : 2 * θ + δ ≤ δ * L := by
    have h1 : (2 * θ / δ + 1) * δ ≤ L * δ := mul_le_mul_of_nonneg_right hLδ hδ0.le
    have h2 : (2 * θ / δ + 1) * δ = 2 * θ + δ := by field_simp
    nlinarith
  have hlt : θ * (3 * (a * L) - 4) < θ * (3 * ℓ - 4) :=
    mul_lt_mul_of_pos_left (by linarith) hθ0
  nlinarith
end CatalanLambda.Mirror
