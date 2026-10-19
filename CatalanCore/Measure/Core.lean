module

public import CatalanCore.Measure.Sep

@[expose] public section

/-!
# The generic measure deduction for a polynomial family

Generic form of `CatalanLambda.Measure.measure_core` + `hex_one`/`hex_two`: the prime window
hypothesis (`PrimeRule.HasWindow`), the NV hypothesis (`HasNV`), content and decay give
`|const - p/q| > q^{-(c (g₂/(g₁ η) + g₂ s) + e)}`, `η = D - Λ`, `s = R.s`.
Legacy λ: `g₁ = 3/4`, `g₂ = 1`.
-/

namespace CatalanCore.Measure

open Real

theorem measure_of_family_realC (Fam : PolyFamily) {Λ D c g₁ g₂ s : ℝ}
    (hΛ : HasContent Fam Λ) (hD : HasDecay Fam D c) (hη : Λ < D) (hc : 0 < c)
    {Cls : ℕ → Prop} {Bad : ℕ → ℕ → Prop} (hs : 0 < s) (hg : 0 < g₁ ∧ g₁ ≤ g₂)
    (hNV : HasNVC Fam Cls Bad g₁ g₂) (hwin : HasWindowC Cls Bad s) {e : ℝ} (he : 0 < e) :
    ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), q₀ ≤ q → IsCoprime p (q : ℤ) →
      (q : ℝ) ^ (-(c * (g₂ / (g₁ * (D - Λ)) + g₂ * s) + e)) < |Fam.const - (p : ℝ) / q| := by
  obtain ⟨hg1, hg12⟩ := hg
  have hg2 : 0 < g₂ := lt_of_lt_of_le hg1 hg12
  set η : ℝ := D - Λ with hηdef
  have hη0 : 0 < η := by rw [hηdef]; linarith
  set M : ℝ := c * (g₂ / (g₁ * η) + g₂ * s) with hM
  have hM0 : 0 < M := by rw [hM]; positivity
  set δ : ℝ := e / (2 * M) with hδ
  have hδ0 : 0 < δ := by rw [hδ]; positivity
  set a : ℝ := (1 + δ) / (g₁ * η) with ha
  set b : ℝ := (1 + δ) * (1 / (g₁ * η) + s) with hb
  have ha0 : 0 < a := by rw [ha]; positivity
  have hab : a + s < b := by
    have : b = a + (1 + δ) * s := by rw [hb, ha]; field_simp
    rw [this]; nlinarith
  have hcb : c * g₂ * b = M + e / 2 := by
    have h1 : M * δ = e / 2 := by rw [hδ]; field_simp
    have h2 : c * g₂ * b = M * (1 + δ) := by rw [hb, hM]; field_simp
    rw [h2]; linarith
  set θ : ℝ := η * (1 + δ / 2) / (1 + δ) with hθ
  have hθ0 : 0 < θ := by rw [hθ]; positivity
  have hθη : θ < η := by
    rw [hθ, div_lt_iff₀ (by positivity)]; nlinarith
  have hθa : θ * (g₁ * a) = 1 + δ / 2 := by rw [hθ, ha]; field_simp
  obtain ⟨N₀, HS⟩ := sep_core Fam hΛ hD hθ0 hθη
  obtain ⟨q₁, hq₁⟩ := hwin a b ha0 hab
  obtain ⟨C, l₀, HNV⟩ := hNV
  set C' : ℝ := max C 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  have hCC' : C ≤ C' := le_max_left _ _
  set L₁ : ℝ := max (max (l₀ / a) ((N₀ + C') / (g₁ * a))) (max (2 * θ * C' / δ) (2 * c * C' / e))
    with hL₁
  refine ⟨max q₁ ⌈Real.exp L₁⌉₊, fun p q hq hcop => ?_⟩
  have hq1 : q₁ ≤ q := le_trans (le_max_left _ _) hq
  have hqe : Real.exp L₁ ≤ q :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast le_trans (le_max_right _ _) hq)
  have hqpos : (0 : ℝ) < q := lt_of_lt_of_le (Real.exp_pos _) hqe
  have hq0 : 0 < q := by exact_mod_cast hqpos
  have hL : L₁ ≤ Real.log q := (Real.le_log_iff_exp_le hqpos).2 hqe
  set L := Real.log q with hLdef
  by_contra hcon
  push Not at hcon
  obtain ⟨l, hlp, hlr, hl1, hl2, hbad⟩ := hq₁ q hq1
  have hlL : (l₀ : ℝ) ≤ a * L := by
    have : (l₀ : ℝ) / a ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hL
    rw [div_le_iff₀ ha0] at this; linarith
  have hl0 : l₀ ≤ l := by
    have : (l₀ : ℝ) ≤ l := by linarith
    exact_mod_cast this
  obtain ⟨n, hAdm, hn1, hn2, hQ⟩ := HNV l hlp hl0 hlr (p : ℤ) (q : ℤ) (by exact_mod_cast hq0) hcop
    (by simpa using hbad)
  have hN : (N₀ : ℝ) + C' ≤ g₁ * (a * L) := by
    have : ((N₀ : ℝ) + C') / (g₁ * a) ≤ L :=
      le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hL
    rw [div_le_iff₀ (by positivity)] at this; linarith
  have hdeg : (N₀ : ℝ) ≤ Fam.deg n := by
    have : g₁ * (a * L) < g₁ * l := by
      have := mul_lt_mul_of_pos_left hl1 hg1; linarith
    linarith
  have hdeg' : N₀ ≤ Fam.deg n := by exact_mod_cast hdeg
  have hclose : |Fam.const - (p : ℝ) / q| ≤ Real.exp (-c * Fam.deg n) := by
    refine le_trans hcon ?_
    rw [Real.rpow_def_of_pos hqpos, ← hLdef]
    apply Real.exp_le_exp.2
    have hLe : 2 * c * C' / e ≤ L := le_trans (le_max_right _ _) hL |>.trans' (le_max_right _ _)
    have h3 : c * C' ≤ e / 2 * L := by
      rw [div_le_iff₀ he] at hLe; nlinarith
    have h4 : (Fam.deg n : ℝ) ≤ g₂ * (b * L) + C' := by
      have : (l : ℝ) ≤ b * L := hl2
      have := mul_le_mul_of_nonneg_left this hg2.le
      linarith
    have h5 : c * (Fam.deg n : ℝ) ≤ c * (g₂ * (b * L)) + c * C' := by
      have := mul_le_mul_of_nonneg_left h4 hc.le
      rw [mul_add] at this; exact this
    have h6 : c * (g₂ * (b * L)) = (M + e / 2) * L := by
      rw [← hcb]; ring
    linarith
  have key := HS n hAdm hdeg' p (q : ℤ) (by exact_mod_cast hq0) (by simpa using hQ)
    (by simpa using hclose)
  simp only [Int.cast_natCast] at key
  have hδL : 2 * θ * C' ≤ δ * L := by
    have : 2 * θ * C' / δ ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hL
    rw [div_le_iff₀ hδ0] at this; linarith
  have hdeg2 : g₁ * (a * L) - C' < Fam.deg n := by
    have := mul_lt_mul_of_pos_left hl1 hg1
    linarith
  have hfin : θ * (g₁ * (a * L) - C') < θ * Fam.deg n := mul_lt_mul_of_pos_left hdeg2 hθ0
  have : θ * (g₁ * (a * L)) = (1 + δ / 2) * L := by rw [← mul_assoc, ← hθa]; ring
  rw [mul_sub] at hfin
  linarith

theorem measure_of_family_real (Fam : PolyFamily) {Λ D c g₁ g₂ : ℝ}
    (hΛ : HasContent Fam Λ) (hD : HasDecay Fam D c) (hη : Λ < D) (hc : 0 < c)
    (R : PrimeRule) (hs : (0 : ℚ) < R.s) (hg : 0 < g₁ ∧ g₁ ≤ g₂)
    (hNV : HasNV Fam R g₁ g₂) (hwin : R.HasWindow) {e : ℝ} (he : 0 < e) :
    ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), q₀ ≤ q → IsCoprime p (q : ℤ) →
      (q : ℝ) ^ (-(c * (g₂ / (g₁ * (D - Λ)) + g₂ * (R.s : ℝ)) + e)) < |Fam.const - (p : ℝ) / q| :=
  measure_of_family_realC Fam hΛ hD hη hc (by exact_mod_cast hs) hg hNV.toC
    (PrimeRule.hasWindowC R hwin) he

end CatalanCore.Measure
