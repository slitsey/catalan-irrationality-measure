module

public import CatalanCore.Decay.Rect.Asymp

@[expose] public section

/-!
# Asymptotics, part 2: `RerrR_le` and `asymp_main` (WP-H2-core)
-/

open Finset Filter Topology MeasureTheory intervalIntegral
open CatalanLambda.Decay

namespace CatalanCore.Decay

theorem RerrRW_le {α w : ℝ} (hα : 0 < α) (hw : 1 ≤ w) {m0 : ℝ} (hm0 : 0 < m0) {Γd A0 ρ Cl : ℝ}
    (hΓ : 0 ≤ Γd) (hA : 0 ≤ A0) (hC : 0 ≤ Cl) :
    ∃ C1 C2 : ℝ, ∀ r m : ℕ, 1 ≤ r → (m : ℝ) ≤ (α + w) * r →
      RerrRW w Γd A0 ρ m0 Cl α r m ≤ C1 * r + C2 * r * Real.log r := by
  set Lα : ℝ := Real.log (2 * α + 2 * w + 1) with hLα
  have hLα0 : 0 ≤ Lα := Real.log_nonneg (by linarith)
  refine ⟨2 * Γd + 2 * (α + w + 1) * (w * A0) + (α + w) * Lα
      + 2 * (α + w + 1) * (Real.log (1 / m0 + 1) + Lα)
      + 2 * (α + w + 1) * (Lα + w * |Real.log (2 * α)|) + (α + w + 1) * |Real.log ρ|
      + (α + w + 1) * Cl,
    (α + w) + 2 * (α + w + 1) + 2 * (α + w + 1), ?_⟩
  intro r m hr hm
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hr0 : (0 : ℝ) < r := by linarith
  have hm0' : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hN : (r : ℝ) + m ≤ (α + w + 1) * r := by nlinarith
  have hlogr : 0 ≤ Real.log r := Real.log_nonneg hr1
  have h3 : (m : ℝ) * Real.log (r + 2 * m) ≤ (α + w) * r * (Lα + Real.log r) := by
    have h1 : Real.log (r + 2 * m) ≤ Lα + Real.log r := by
      rw [hLα, ← Real.log_mul (by linarith) hr0.ne']
      apply Real.log_le_log (by positivity)
      nlinarith
    have h2 : 0 ≤ Real.log ((r : ℝ) + 2 * m) := Real.log_nonneg (by nlinarith)
    calc (m : ℝ) * Real.log (r + 2 * m) ≤ ((α + w) * r) * (Lα + Real.log r) :=
          mul_le_mul hm h1 h2 (by positivity)
      _ = _ := by ring
  have h4 : Real.log (1 + r / m0) ≤ Real.log (1 / m0 + 1) + Real.log r := by
    have := log_lin_le (1 / m0) 1 (by positivity) le_rfl hr
    have e : (1 : ℝ) + r / m0 = 1 / m0 * r + 1 := by ring
    rw [e]; exact this
  have h5 : Real.log (1 + 2 * m / r) ≤ Lα := by
    rw [hLα]
    apply Real.log_le_log (by positivity)
    have : 2 * (m : ℝ) / r ≤ 2 * (α + w) := by
      rw [div_le_iff₀ hr0]; nlinarith
    linarith
  have h6 : Real.log (1 + 2 * m) ≤ Lα + Real.log r := by
    rw [hLα, ← Real.log_mul (by linarith) hr0.ne']
    apply Real.log_le_log (by positivity)
    nlinarith
  have hE1nn : 0 ≤ Real.log (1 + r / m0) + Real.log (1 + 2 * m / r) := by
    have a1 : 0 ≤ Real.log (1 + (r : ℝ) / m0) := Real.log_nonneg (by
      have : (0 : ℝ) ≤ r / m0 := by positivity
      linarith)
    have a2 : 0 ≤ Real.log (1 + 2 * (m : ℝ) / r) := Real.log_nonneg (by
      have : (0 : ℝ) ≤ 2 * m / r := by positivity
      linarith)
    linarith
  have hE2nn : 0 ≤ Real.log (1 + 2 * (m : ℝ)) + w * |Real.log (2 * α)| := by
    have a1 : 0 ≤ Real.log (1 + 2 * (m : ℝ)) := Real.log_nonneg (by linarith)
    have := mul_nonneg (by linarith : (0 : ℝ) ≤ w) (abs_nonneg (Real.log (2 * α)))
    linarith
  have hE1 : Real.log (1 + r / m0) + Real.log (1 + 2 * m / r)
      ≤ Real.log (1 / m0 + 1) + Real.log r + Lα := by linarith
  have hE2 : Real.log (1 + 2 * (m : ℝ)) + w * |Real.log (2 * α)|
      ≤ Lα + Real.log r + w * |Real.log (2 * α)| := by linarith
  have t4 := mul_le_mul hN hE1 hE1nn (by positivity)
  have t5 := mul_le_mul hN hE2 hE2nn (by positivity)
  have t2 := mul_le_mul_of_nonneg_right hN (mul_nonneg (by linarith : (0 : ℝ) ≤ w) hA)
  have t6 := mul_le_mul_of_nonneg_right hN (abs_nonneg (Real.log ρ))
  have t7 := mul_le_mul_of_nonneg_right hN hC
  unfold RerrRW
  nlinarith [h3, t2, t4, t5, t6, t7]

set_option maxHeartbeats 4000000 in
theorem asymp_mainW {α w m' dS Ib Inu Γd A0 ρ m0 Cl L0 D : ℝ} (hα : 0 < α) (hw : 1 ≤ w)
    (hm0 : 0 < m0)
    (hΓ : 0 ≤ Γd) (hA : 0 ≤ A0) (hC : 0 ≤ Cl)
    (hInu : Inu ≤ Jfun α) (hD : D ≤ 2 * ((1 + α) * m' + dS) - (1 + α) ^ 2 * Ib + Inu)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ r0 : ℕ, ∀ r m : ℕ, r0 ≤ r → α * r ≤ m → (m : ℝ) ≤ α * r + w →
      r * Real.log 2 + ((r : ℝ) + m) * (L0 + Real.log r) + RerrRW w Γd A0 ρ m0 Cl α r m
        - (2 * r * ((r : ℝ) + m) * m' + 2 * r ^ 2 * dS - ((r : ℝ) + m) ^ 2 * Ib + Alow r m)
      ≤ -(D - δ) * (r : ℝ) ^ 2 := by
  obtain ⟨r1, C3, C4, hAl⟩ := Alow_geW hα hw (δ := δ / 4) (by positivity)
  obtain ⟨C1, C2, hR⟩ := RerrRW_le hα hw hm0 (ρ := ρ) hΓ hA hC
  set c1 : ℝ := Real.log 2 + (α + w + 1) * |L0| + C1 + 2 * w * |m'| + (2 * (1 + α) * w + w ^ 2) * |Ib| + C3 with hc1
  set c2 : ℝ := C2 + C4 + (α + w + 1) with hc2
  obtain ⟨r2, hr2⟩ := Filter.eventually_atTop.1 (err_small c1 c2 (δ / 2) (by positivity))
  refine ⟨max r1 (max r2 1), ?_⟩
  intro r m hr hαr hαr'
  have hr1' : r1 ≤ r := le_trans (le_max_left _ _) hr
  have hr2' : r2 ≤ r := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hr
  have hr3' : 1 ≤ r := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hr
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr3'
  have hr0 : (0 : ℝ) < r := by linarith
  have hmM : (m : ℝ) ≤ (α + w) * r := by nlinarith
  have hA' := hAl r m hr1' hαr hαr'
  have hR' := hR r m hr3' hmM
  have hs := hr2 r hr2'
  obtain ⟨δ', hδ'⟩ : ∃ δ', δ' = (m : ℝ) - α * r := ⟨_, rfl⟩
  have hδ0 : 0 ≤ δ' := by rw [hδ']; linarith
  have hδ1 : δ' ≤ w := by rw [hδ']; linarith
  have hN : (r : ℝ) + m = (1 + α) * r + δ' := by rw [hδ']; ring
  have he1 : 2 * (r : ℝ) * ((r : ℝ) + m) * m' + 2 * r ^ 2 * dS - ((r : ℝ) + m) ^ 2 * Ib
      = (r : ℝ) ^ 2 * (2 * (1 + α) * m' + 2 * dS - (1 + α) ^ 2 * Ib)
        + (2 * r * δ' * m' - 2 * (1 + α) * r * δ' * Ib - δ' ^ 2 * Ib) := by
    rw [hN]; ring
  have hm1 : -(δ' * m') ≤ w * |m'| := by
    nlinarith [abs_nonneg m', neg_abs_le m', le_abs_self m', mul_nonneg hδ0 (abs_nonneg m'),
      mul_nonneg (sub_nonneg.2 hδ1) (abs_nonneg m')]
  have hIb1 : δ' * Ib ≤ w * |Ib| := by
    nlinarith [abs_nonneg Ib, le_abs_self Ib, mul_nonneg hδ0 (abs_nonneg Ib),
      mul_nonneg (sub_nonneg.2 hδ1) (abs_nonneg Ib)]
  have hIb2 : δ' ^ 2 * Ib ≤ w ^ 2 * |Ib| := by
    have h0 : δ' ^ 2 ≤ w ^ 2 := by nlinarith
    nlinarith [abs_nonneg Ib, le_abs_self Ib, mul_nonneg (sq_nonneg δ') (abs_nonneg Ib),
      mul_nonneg (sub_nonneg.2 h0) (abs_nonneg Ib)]
  have he1b : -(2 * (r : ℝ) * δ' * m' - 2 * (1 + α) * r * δ' * Ib - δ' ^ 2 * Ib)
      ≤ (2 * w * |m'| + (2 * (1 + α) * w + w ^ 2) * |Ib|) * r := by
    have a1 := mul_le_mul_of_nonneg_left hm1 (by positivity : (0 : ℝ) ≤ 2 * r)
    have a2 := mul_le_mul_of_nonneg_left hIb1 (by positivity : (0 : ℝ) ≤ 2 * (1 + α) * r)
    have a3 := mul_le_mul_of_nonneg_right hIb2 (by positivity : (0 : ℝ) ≤ 1)
    have a4 : w ^ 2 * |Ib| ≤ w ^ 2 * |Ib| * r := by
      nlinarith [mul_nonneg (sq_nonneg w) (abs_nonneg Ib)]
    nlinarith [a1, a2, hIb2, a4, abs_nonneg Ib]
  have hlogr : 0 ≤ Real.log r := Real.log_nonneg hr1
  have hNL : ((r : ℝ) + m) * (L0 + Real.log r)
      ≤ (α + w + 1) * r * |L0| + (α + w + 1) * r * Real.log r := by
    have h1 : (r : ℝ) + m ≤ (α + w + 1) * r := by nlinarith
    have h2 : L0 + Real.log r ≤ |L0| + Real.log r := by linarith [le_abs_self L0]
    calc ((r : ℝ) + m) * (L0 + Real.log r) ≤ ((r : ℝ) + m) * (|L0| + Real.log r) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ ≤ (α + w + 1) * r * (|L0| + Real.log r) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = _ := by ring
  have hg1 := mul_le_mul_of_nonneg_left hD (sq_nonneg (r : ℝ))
  have hg2 := mul_le_mul_of_nonneg_left hInu (sq_nonneg (r : ℝ))
  rw [he1]
  rw [hc1, hc2] at hs
  have hδr : 0 ≤ δ * (r : ℝ) ^ 2 := mul_nonneg hδ.le (sq_nonneg _)
  linarith [hA', hR', hs, he1b, hNL, hg1, hg2, hδr]

/-- The window-`1` case of `asymp_mainW`. -/
theorem asymp_main {α m' dS Ib Inu Γd A0 ρ m0 Cl L0 D : ℝ} (hα : 0 < α) (hm0 : 0 < m0)
    (hΓ : 0 ≤ Γd) (hA : 0 ≤ A0) (hC : 0 ≤ Cl)
    (hInu : Inu ≤ Jfun α) (hD : D ≤ 2 * ((1 + α) * m' + dS) - (1 + α) ^ 2 * Ib + Inu)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ r0 : ℕ, ∀ r m : ℕ, r0 ≤ r → α * r ≤ m → (m : ℝ) ≤ α * r + 1 →
      r * Real.log 2 + ((r : ℝ) + m) * (L0 + Real.log r) + RerrR Γd A0 ρ m0 Cl α r m
        - (2 * r * ((r : ℝ) + m) * m' + 2 * r ^ 2 * dS - ((r : ℝ) + m) ^ 2 * Ib + Alow r m)
      ≤ -(D - δ) * (r : ℝ) ^ 2 :=
  asymp_mainW (w := 1) hα le_rfl hm0 hΓ hA hC hInu hD hδ

end CatalanCore.Decay
