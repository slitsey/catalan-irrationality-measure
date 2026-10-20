module

public import CatalanFrames.HybCommon.Sums2
public import CatalanFrames.HybCommon.Num

@[expose] public section

/-!
# The `ε`-form of the member-1/member-2 content bound for the five bordered deficits (generic)

`both_eps_G`: from the content bound `hlogT` for the glued deficit family (the instance supplies it:
for the mirror, `mir_logDhybT_le`), the sums of `Sums`/`Sums2` and `defBoth_all5` give, for every
`Λ ≥ 24729491161/6665218560 - 1/448` (deficits E, B, C5, C7, no GK), an `ε`-family of `DefBothG`
families with `log DhybT ≤ (Λ + ε) r²`.
-/

open Finset Filter Classical CatalanCore CatalanCore.Arith CatalanCore.Arith.Hybrid

namespace CatalanFrames.HybCommon

variable {Fr : Frame}

theorem both_eps_G (I : HybInst Fr) [∀ r, I.DiagOK r (r / 8)] {o : ℕ} (hL : LamData Fr o) (ho : o = 1 ∨ o = 3)
    (hlogT : ∀ ε > 0, ∀ᶠ r : ℕ in atTop, ∀ δ : ℕ → ℕ, DefHypT I r (r / 8) (TfunG o I r) δ →
      Real.log (DhybT I r (r / 8) (TfunG o I r) δ) ≤
        (24994314577 / 6665218560 + ε) * (r : ℝ) ^ 2 -
        ∑ p ∈ (Finset.range (Bnd I r (r / 8))).filter Nat.Prime, (δ p : ℝ) * Real.log p)
    {Λ : ℝ} (hΛ : 24729491161 / 6665218560 - 1 / 448 ≤ Λ) :
    ∀ ε > 0, ∀ᶠ r : ℕ in atTop, ∃ T δ : ℕ → ℕ, DefBothG I r T δ ∧
      Real.log (DhybT I r (r / 8) T δ) ≤ (Λ + ε) * (r : ℝ) ^ 2 := by
  intro ε hε
  set ε₁ : ℝ := min (ε / 2) (1 / 100) with hε₁
  have hε₁0 : 0 < ε₁ := lt_min (by positivity) (by norm_num)
  have hε₁1 : ε₁ ≤ 1 / 100 := min_le_right _ _
  have hε₁2 : ε₁ ≤ ε / 2 := min_le_left _ _
  have hd := hlogT (ε₁ / 10) (by positivity)
  have hl := eventually_log_le (e := ε₁ / 10) (by positivity)
  have hbig : ∀ᶠ r : ℕ in atTop, 3 ≤ ε₁ * r := by
    have : Tendsto (fun r : ℕ => ε₁ * (r : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.const_mul_atTop hε₁0
    exact this.eventually_ge_atTop 3
  have h1 := sum_E1 I ho (ε := ε₁ / 10) (by positivity)
  have h3 := sum_E3 I ho (ε := ε₁ / 10) (by positivity)
  have hB := sum_B I (ε := ε₁ / 10) (by positivity)
  have h5 := sum_C5 I ho (ε := ε₁ / 10) (by positivity)
  have h7 := sum_C7 I ho (ε := ε₁ / 10) (by positivity)
  filter_upwards [hd, hl, hbig, eventually_ge_atTop 16, h1, h3, hB, h5, h7] with r hdr hL' hb hr16
    s1 s3 sB s5 s7
  refine ⟨TfunG o I r, dAll5 o r, defBoth_all5 hL ho hr16, ?_⟩
  have hlog := hdr (dAll5 o r) (defBoth_all5 hL ho hr16).1
  have hsum : ∑ p ∈ (Finset.range (Bnd I r (r / 8))).filter Nat.Prime,
      (dAll5 o r p : ℝ) * Real.log p =
      ∑ p ∈ (Finset.range (Bnd I r (r / 8))).filter Nat.Prime, (dE1 o r p : ℝ) * Real.log p +
      ∑ p ∈ (Finset.range (Bnd I r (r / 8))).filter Nat.Prime, (dE3 o r p : ℝ) * Real.log p +
      ∑ p ∈ (Finset.range (Bnd I r (r / 8))).filter Nat.Prime, (dB r p : ℝ) * Real.log p +
      ∑ p ∈ (Finset.range (Bnd I r (r / 8))).filter Nat.Prime, (dC5 o r p : ℝ) * Real.log p +
      ∑ p ∈ (Finset.range (Bnd I r (r / 8))).filter Nat.Prime, (dC7 o r p : ℝ) * Real.log p := by
    simp only [dAll5, Nat.cast_add, add_mul, Finset.sum_add_distrib]
  rw [hsum] at hlog
  have hm : (r : ℝ) / 8 - 1 ≤ ((r / 8 : ℕ) : ℝ) := by
    have : (r : ℝ) < 8 * ((r / 8 : ℕ) : ℝ) + 8 := by
      exact_mod_cast (by omega : r < 8 * (r / 8) + 8)
    linarith
  have hL0 : 0 ≤ Real.log r := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ r))
  have key := num5 (Λ := Λ + 1 / 448 + (ε - 11 / 10 * ε₁)) (ε := ε₁) (r := (r : ℝ))
    (L := Real.log r) (m := ((r / 8 : ℕ) : ℝ))
    (lg := Real.log (DhybT I r (r / 8) (TfunG o I r) (dAll5 o r)) +
      (1 / 448 - ε₁ / 10) * (r : ℝ) ^ 2)
    (by linarith) hε₁0 hε₁1 hb hL0 hL' hm (by linarith)
  nlinarith [key]

/-- **All seven bordered deficits (E, B, C5, C7, GK)**: constant
`Λ₁ = 24729491161/6665218560 - 1/448 - 1/576 - 1/352 = 3.7034204…`. -/
theorem both_eps_G7_extra (I : HybInst Fr) [∀ r, I.DiagOK r (r / 8)] {o : ℕ} (ho : o = 1 ∨ o = 3)
    (Exp Extra : ℕ → ℕ → ℕ) (gain : ℝ)
    (hdef : ∀ᶠ r : ℕ in atTop, DefBothG I r (Exp r) (fun p => dAll7 o r p + Extra r p))
    (hextra : ∀ ε>0, ∀ᶠ r : ℕ in atTop,
      (gain-ε)*(r : ℝ)^2 ≤ ∑p∈(Finset.range (Bnd I r (r/8))).filter Nat.Prime,
        (Extra r p : ℝ)*Real.log p)
    (hlogT : ∀ ε > 0, ∀ᶠ r : ℕ in atTop, ∀ δ : ℕ → ℕ, DefHypT I r (r / 8) (Exp r) δ →
      Real.log (DhybT I r (r / 8) (Exp r) δ) ≤
        (24994314577 / 6665218560 + ε) * (r : ℝ) ^ 2 -
        ∑ p ∈ (Finset.range (Bnd I r (r / 8))).filter Nat.Prime, (δ p : ℝ) * Real.log p)
    {Λ : ℝ} (hΛ : 24729491161 / 6665218560 - 1 / 448 - 1 / 576 - 1 / 352 - gain ≤ Λ) :
    ∀ ε > 0, ∀ᶠ r : ℕ in atTop, ∃ T δ : ℕ → ℕ, DefBothG I r T δ ∧
      Real.log (DhybT I r (r / 8) T δ) ≤ (Λ + ε) * (r : ℝ) ^ 2 := by
  intro ε hε
  set ε₁ : ℝ := min (ε / 3) (1 / 100) with hε₁
  have hε₁0 : 0 < ε₁ := lt_min (by positivity) (by norm_num)
  have hε₁1 : ε₁ ≤ 1 / 100 := min_le_right _ _
  have hε₁2 : ε₁ ≤ ε / 3 := min_le_left _ _
  have hd := hlogT (ε₁ / 10) (by positivity)
  have he := hextra ε₁ hε₁0
  have hl := eventually_log_le (e := ε₁ / 10) (by positivity)
  have hbig : ∀ᶠ r : ℕ in atTop, 3 ≤ ε₁ * r := by
    have : Tendsto (fun r : ℕ => ε₁ * (r : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.const_mul_atTop hε₁0
    exact this.eventually_ge_atTop 3
  have h1 := sum_E1 I ho (ε := ε₁ / 10) (by positivity)
  have h3 := sum_E3 I ho (ε := ε₁ / 10) (by positivity)
  have hB := sum_B I (ε := ε₁ / 10) (by positivity)
  have h5 := sum_C5 I ho (ε := ε₁ / 10) (by positivity)
  have h7 := sum_C7 I ho (ε := ε₁ / 10) (by positivity)
  have ha := sum_GKa I ho (ε := ε₁ / 10) (by positivity)
  have hb' := sum_GKb I ho (ε := ε₁ / 10) (by positivity)
  filter_upwards [hd, he, hl, hbig, eventually_ge_atTop 16, h1, h3, hB, h5, h7, ha, hb', hdef] with r hdr heR
    hL' hb hr16 s1 s3 sB s5 s7 sa sb hdefR
  let δ : ℕ → ℕ := fun p => dAll7 o r p+Extra r p
  refine ⟨Exp r, δ, hdefR, ?_⟩
  have hlog := hdr δ hdefR.1
  have hsplit : (∑p∈(Finset.range (Bnd I r (r/8))).filter Nat.Prime,
      (δ p : ℝ)*Real.log p) =
      (∑p∈(Finset.range (Bnd I r (r/8))).filter Nat.Prime,
        (dAll7 o r p : ℝ)*Real.log p) +
      (∑p∈(Finset.range (Bnd I r (r/8))).filter Nat.Prime,
        (Extra r p : ℝ)*Real.log p) := by
    simp only [δ, Nat.cast_add, add_mul, Finset.sum_add_distrib]
  rw [hsplit] at hlog
  have hsum : ∑ p ∈ (Finset.range (Bnd I r (r / 8))).filter Nat.Prime,
      (dAll7 o r p : ℝ) * Real.log p =
      ∑ p ∈ (Finset.range (Bnd I r (r / 8))).filter Nat.Prime, (dE1 o r p : ℝ) * Real.log p +
      ∑ p ∈ (Finset.range (Bnd I r (r / 8))).filter Nat.Prime, (dE3 o r p : ℝ) * Real.log p +
      ∑ p ∈ (Finset.range (Bnd I r (r / 8))).filter Nat.Prime, (dB r p : ℝ) * Real.log p +
      ∑ p ∈ (Finset.range (Bnd I r (r / 8))).filter Nat.Prime, (dC5 o r p : ℝ) * Real.log p +
      ∑ p ∈ (Finset.range (Bnd I r (r / 8))).filter Nat.Prime, (dC7 o r p : ℝ) * Real.log p +
      ∑ p ∈ (Finset.range (Bnd I r (r / 8))).filter Nat.Prime, (dGKa o r p : ℝ) * Real.log p +
      ∑ p ∈ (Finset.range (Bnd I r (r / 8))).filter Nat.Prime, (dGKb o r p : ℝ) * Real.log p := by
    simp only [dAll7, dAll5, Nat.cast_add, add_mul, Finset.sum_add_distrib]
    ring
  rw [hsum] at hlog
  have hm : (r : ℝ) / 8 - 1 ≤ ((r / 8 : ℕ) : ℝ) := by
    have : (r : ℝ) < 8 * ((r / 8 : ℕ) : ℝ) + 8 := by
      exact_mod_cast (by omega : r < 8 * (r / 8) + 8)
    linarith
  have hL0 : 0 ≤ Real.log r := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ r))
  have key := num7 (Λ := Λ+gain) (ε := ε₁) (r := (r : ℝ)) (L := Real.log r)
    (m := ((r / 8 : ℕ) : ℝ)) (lg := Real.log (DhybT I r (r / 8) (Exp r) δ)+(gain-ε₁)*(r : ℝ)^2)
    (by linarith) hε₁0 hε₁1 hb hL0 hL' hm (by linarith)
  have hr2 : 0 ≤ (r : ℝ) ^ 2 := sq_nonneg _
  nlinarith [key]


/-- **All seven bordered deficits (E, B, C5, C7, GK)**: constant
`Λ₁ = 24729491161/6665218560 - 1/448 - 1/576 - 1/352 = 3.7034204…`. -/
theorem both_eps_G7 (I : HybInst Fr) [∀ r, I.DiagOK r (r / 8)] {o : ℕ} (hL : LamData Fr o) (ho : o = 1 ∨ o = 3)
    (hlogT : ∀ ε > 0, ∀ᶠ r : ℕ in atTop, ∀ δ : ℕ → ℕ, DefHypT I r (r / 8) (TfunG o I r) δ →
      Real.log (DhybT I r (r / 8) (TfunG o I r) δ) ≤
        (24994314577 / 6665218560 + ε) * (r : ℝ) ^ 2 -
        ∑ p ∈ (Finset.range (Bnd I r (r / 8))).filter Nat.Prime, (δ p : ℝ) * Real.log p)
    {Λ : ℝ} (hΛ : 24729491161 / 6665218560 - 1 / 448 - 1 / 576 - 1 / 352 ≤ Λ) :
    ∀ ε > 0, ∀ᶠ r : ℕ in atTop, ∃ T δ : ℕ → ℕ, DefBothG I r T δ ∧
      Real.log (DhybT I r (r / 8) T δ) ≤ (Λ + ε) * (r : ℝ) ^ 2 := by
  have h := both_eps_G7_extra I ho (TfunG o I) (fun _ _ => 0) 0
    (by filter_upwards [eventually_ge_atTop 16] with r hr; simpa using defBoth_all7 hL ho hr)
    (fun ε hε => Filter.Eventually.of_forall fun r => by
      simp only [zero_sub, Nat.cast_zero, zero_mul, Finset.sum_const_zero]
      simpa only [neg_mul] using neg_nonpos.mpr (mul_nonneg hε.le (sq_nonneg (r : ℝ))))
    hlogT (by simpa using hΛ)
  exact h

end CatalanFrames.HybCommon
