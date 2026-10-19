module

public import CatalanCore.Cert.SigmaP6H.Data
public import CatalanCore.Cert.SigmaHyb.UexForm

@[expose] public section

/-!
# `h = U^λ - U^ex_{1/4} ≥ 0` (P6DECAY, the domination step)

The 32 correction atoms sit at the LEFT endpoint (shifted by `ρ`) of the 32 cells of
`[1, 1 + 1/4]`.  For `Re s + ρ ≤ a ≤ u` one has `(x-(a-ρ))² + y² + ρ² ≤ (x-u)² + y²`
(`shift_sq`), so each cell integral of `-log‖s-u‖` is below `h/2` times the regularised kernel at
`a - ρ` (`cell_le`).  On the real sliver `[1-ρ, 1]` cell `0` is compared with the closed form
`Uex_one`.
-/

open Real MeasureTheory intervalIntegral
open CatalanLambda.Decay CatalanCore.Decay

namespace CatalanCore.Cert.SigmaP6H

lemma shift_sq {x y u a ρ : ℝ} (hρ : 0 < ρ) (hxa : x + ρ ≤ a) (hau : a ≤ u) :
    (x - (a - ρ)) ^ 2 + y ^ 2 + ρ ^ 2 ≤ (x - u) ^ 2 + y ^ 2 := by
  nlinarith [mul_nonneg hρ.le (sub_nonneg.2 hxa),
    mul_nonneg (sub_nonneg.2 hau) (by linarith : (0 : ℝ) ≤ (u - x) + (a - x))]

lemma integrable_elog_of_lt {σ : ℂ} {a : ℝ} (hσ : σ.re < a) {b c : ℝ} (hb : a ≤ b) (hc : a ≤ c) :
    IntervalIntegrable (fun u : ℝ => elog σ (u : ℂ)) volume b c := by
  have hanti : AntitoneOn (fun u : ℝ => elog σ (u : ℂ)) (Set.Ici a) :=
    fun u hu v hv huv => elog_real_anti (lt_of_lt_of_le hσ hu) huv
  refine (hanti.mono ?_).intervalIntegrable
  intro x hx
  rw [Set.mem_uIcc] at hx
  simp only [Set.mem_Ici]
  rcases hx with ⟨h1, _⟩ | ⟨h1, _⟩ <;> linarith

/-- One cell: `½ ∫_a^{a+h} -log‖s-u‖ du ≤ (h/2) k_ρ(s, a-ρ)` when `Re s + ρ ≤ a`. -/
lemma cell_le {s : ℂ} {a h ρ : ℝ} (hρ : 0 < ρ) (hh : 0 ≤ h) (hs : s.re + ρ ≤ a) :
    (1 / 2) * ∫ u in a..a + h, elog s (u : ℂ) ≤ (h / 2) * krho ρ s (((a - ρ : ℝ)) : ℂ) := by
  have hsa : s.re < a := by linarith
  have hint := integrable_elog_of_lt hsa (le_refl a) (by linarith : a ≤ a + h)
  have key : ∀ u ∈ Set.Icc a (a + h), elog s (u : ℂ) ≤ krho ρ s (((a - ρ : ℝ)) : ℂ) := by
    intro u hu
    have hu1 : a ≤ u := hu.1
    have hN : ‖s - (((a - ρ : ℝ)) : ℂ)‖ ^ 2 + ρ ^ 2 ≤ ‖s - (u : ℂ)‖ ^ 2 := by
      rw [norm_sub_real_sq, norm_sub_real_sq]
      have := shift_sq (y := s.im) hρ hs hu1
      linarith
    unfold elog krho
    have hN0 : 0 < ‖s - (((a - ρ : ℝ)) : ℂ)‖ ^ 2 + ρ ^ 2 := by positivity
    have := Real.log_le_log hN0 hN
    have h2 : Real.log (‖s - (u : ℂ)‖ ^ 2) = 2 * Real.log ‖s - (u : ℂ)‖ := by
      rw [Real.log_pow]; norm_num
    rw [h2] at this
    linarith
  have hmono := intervalIntegral.integral_mono_on (by linarith : a ≤ a + h) hint (by simp) key
  rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
  have e : a + h - a = h := by ring
  rw [e] at hmono
  linarith

/-- `Uex` as a sum of `K` equal cells. -/
lemma Uex_split {L : ℝ} (hL : 0 ≤ L) (K : ℕ) (hK : 0 < K) {s : ℂ}
    (hint : IntervalIntegrable (fun u : ℝ => elog s (u : ℂ)) volume 1 (1 + L)) :
    Uex L s = ∑ k : Fin K, (1 / 2) * ∫ u in (1 + ((k : ℕ) : ℝ) * (L / K))..(1 + (((k : ℕ) : ℝ) + 1) * (L / K)),
      elog s (u : ℂ) := by
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  have hLK : 0 ≤ L / K := div_nonneg hL hK'.le
  have hmem : ∀ k : ℕ, k ≤ K → (1 + (k : ℝ) * (L / K)) ∈ Set.uIcc (1 : ℝ) (1 + L) := by
    intro k hk
    have hk' : (k : ℝ) ≤ K := by exact_mod_cast hk
    rw [Set.mem_uIcc]
    left
    constructor
    · have := mul_nonneg (Nat.cast_nonneg k) hLK; linarith
    · have : (k : ℝ) * (L / K) ≤ K * (L / K) := mul_le_mul_of_nonneg_right hk' hLK
      have e : (K : ℝ) * (L / K) = L := by field_simp
      linarith
  have h := intervalIntegral.sum_integral_adjacent_intervals (μ := volume)
    (f := fun u : ℝ => elog s (u : ℂ)) (a := fun k : ℕ => 1 + (k : ℝ) * (L / K)) (n := K)
    (fun k hk => hint.mono_set (Set.uIcc_subset_uIcc (hmem k hk.le) (hmem (k + 1) hk)))
  have e0 : (1 + ((0 : ℕ) : ℝ) * (L / K)) = 1 := by simp
  have eK : (1 + ((K : ℕ) : ℝ) * (L / K)) = 1 + L := by field_simp
  simp only [e0, eK, Nat.cast_succ] at h
  unfold Uex
  rw [← h, Finset.mul_sum, Fin.sum_univ_eq_sum_range
    (fun k => (1 / 2 : ℝ) * ∫ u in (1 + (k : ℝ) * (L / K))..(1 + ((k : ℝ) + 1) * (L / K)),
      elog s (u : ℂ)) K]

theorem h_left {s : ℂ} (hs : s.re ≤ 1 - 1 / 2048) :
    Uex (2 * (1 / 8)) s ≤ Usig (1 / 2048) lamC lamW s := by
  have hs1 : s.re < 1 := by linarith
  rw [Uex_split (L := 2 * (1 / 8)) (by norm_num) 32 (by norm_num)
    (integrable_elog hs1 le_rfl (by norm_num))]
  unfold Usig
  refine Finset.sum_le_sum (fun k _ => ?_)
  have hk0 : (0 : ℝ) ≤ ((k : ℕ) : ℝ) := Nat.cast_nonneg _
  have eA : (1 + ((k : ℕ) : ℝ) * (2 * (1 / 8) / ((32 : ℕ) : ℝ))) = 1 + ((k : ℕ) : ℝ) / 128 := by
    push_cast; ring
  have eB : (1 + (((k : ℕ) : ℝ) + 1) * (2 * (1 / 8) / ((32 : ℕ) : ℝ)))
      = (1 + ((k : ℕ) : ℝ) / 128) + 1 / 128 := by
    push_cast; ring
  rw [eA, eB]
  have := cell_le (s := s) (a := 1 + ((k : ℕ) : ℝ) / 128) (h := 1 / 128) (ρ := 1 / 2048)
    (by norm_num) (by norm_num) (by linarith)
  unfold lamW lamC
  have e2 : (1 / 128 : ℝ) / 2 = 1 / 256 := by norm_num
  rw [e2] at this
  exact this

lemma elog_one_eq (u : ℝ) : elog (1 : ℂ) (u : ℂ) = -Real.log (u - 1) := by
  unfold elog
  have : (1 : ℂ) - (u : ℂ) = ((1 - u : ℝ) : ℂ) := by push_cast; ring
  rw [this, Complex.norm_real, Real.norm_eq_abs, Real.log_abs, ← Real.log_neg_eq_log (u - 1)]
  ring_nf

lemma integrable_elog_one (b c : ℝ) :
    IntervalIntegrable (fun u : ℝ => elog (1 : ℂ) (u : ℂ)) volume b c := by
  have h := ((intervalIntegral.intervalIntegrable_log' (a := b - 1) (b := c - 1)).comp_sub_right
    (1 : ℝ)).neg
  simp only [sub_add_cancel] at h
  have e : (fun u : ℝ => elog (1 : ℂ) (u : ℂ)) = -fun x : ℝ => Real.log (x - 1) := by
    funext u; simp [elog_one_eq]
  rw [e]; exact h

lemma integrable_elog_real {x : ℝ} (h1 : x ≤ 1) (b c : ℝ) (hb : 1 ≤ b) (hc : 1 ≤ c) :
    IntervalIntegrable (fun u : ℝ => elog (x : ℂ) (u : ℂ)) volume b c := by
  rcases h1.lt_or_eq with hlt | rfl
  · exact integrable_elog (by simpa using hlt) hb hc
  · simpa using integrable_elog_one b c

/-- Cell `0` on the real sliver `[1-ρ, 1]`: compared with the closed form `Uex_one`. -/
lemma cell0 {x : ℝ} (h0 : 1 - 1 / 2048 ≤ x) (h1 : x ≤ 1) :
    (1 / 2) * ∫ u in (1 : ℝ)..1 + 1 / 128, elog (x : ℂ) (u : ℂ)
      ≤ ((1 / 128) / 2) * krho (1 / 2048) (x : ℂ) (((1 - 1 / 2048 : ℝ)) : ℂ) := by
  have hint := integrable_elog_real h1 1 (1 + 1 / 128) le_rfl (by norm_num)
  have hle : (∫ u in (1 : ℝ)..1 + 1 / 128, elog (x : ℂ) (u : ℂ))
      ≤ ∫ u in (1 : ℝ)..1 + 1 / 128, elog (1 : ℂ) (u : ℂ) := by
    refine intervalIntegral.integral_mono_on_of_le_Ioo (by norm_num) hint
      (integrable_elog_one _ _) ?_
    intro u hu
    have hu1 : 1 < u := hu.1
    have e : ∀ a : ℝ, ‖(a : ℂ) - (u : ℂ)‖ = |a - u| := fun a => by
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    unfold elog
    have e1 : ‖(1 : ℂ) - (u : ℂ)‖ = u - 1 := by
      have := e 1
      simp only [Complex.ofReal_one] at this
      rw [this, abs_of_neg (by linarith)]; ring
    have e2 : ‖(x : ℂ) - (u : ℂ)‖ = u - x := by
      rw [e x, abs_of_neg (by linarith)]; ring
    rw [e1, e2]
    have := Real.log_le_log (by linarith : (0 : ℝ) < u - 1) (by linarith : u - 1 ≤ u - x)
    linarith
  have hU := SigmaHyb.Uex_one (L := 1 / 128) (by norm_num)
  unfold Uex at hU
  have hk : -(1 / 2) * Real.log (2 * (1 / 2048) ^ 2)
      ≤ krho (1 / 2048) (x : ℂ) (((1 - 1 / 2048 : ℝ)) : ℂ) := by
    unfold krho
    rw [norm_sub_real_sq]
    simp only [Complex.ofReal_re, Complex.ofReal_im]
    have hpos : (0 : ℝ) < (x - (1 - 1 / 2048)) ^ 2 + 0 ^ 2 + (1 / 2048) ^ 2 := by positivity
    have hl := Real.log_le_log hpos (by nlinarith : (x - (1 - 1 / 2048)) ^ 2 + 0 ^ 2 + (1 / 2048) ^ 2
      ≤ 2 * (1 / 2048) ^ 2)
    linarith
  have l128 : Real.log (1 / 128 : ℝ) = -(7 * Real.log 2) := by
    rw [one_div, Real.log_inv]
    have : (128 : ℝ) = 2 ^ 7 := by norm_num
    rw [this, Real.log_pow]; push_cast; ring
  have l2 : Real.log (2 * (1 / 2048 : ℝ) ^ 2) = -21 * Real.log 2 := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow, one_div, Real.log_inv]
    have : (2048 : ℝ) = 2 ^ 11 := by norm_num
    rw [this, Real.log_pow]; push_cast; ring
  have hl2 := Real.log_two_gt_d9
  have hnum : 1 - Real.log (1 / 128 : ℝ) ≤ krho (1 / 2048) (x : ℂ) (((1 - 1 / 2048 : ℝ)) : ℂ) := by
    rw [l128]
    rw [l2] at hk
    linarith
  have h3 := mul_le_mul_of_nonneg_left hnum (by norm_num : (0 : ℝ) ≤ (1 / 128) / 2)
  have h4 := mul_le_mul_of_nonneg_left hle (by norm_num : (0 : ℝ) ≤ 1 / 2)
  linarith

theorem h_sliver {x : ℝ} (h0 : 1 - 1 / 2048 ≤ x) (h1 : x ≤ 1) :
    Uex (2 * (1 / 8)) (x : ℂ) ≤ Usig (1 / 2048) lamC lamW (x : ℂ) := by
  rw [Uex_split (L := 2 * (1 / 8)) (by norm_num) 32 (by norm_num)
    (integrable_elog_real h1 1 _ le_rfl (by norm_num))]
  unfold Usig
  refine Finset.sum_le_sum (fun k _ => ?_)
  have hk0 : (0 : ℝ) ≤ ((k : ℕ) : ℝ) := Nat.cast_nonneg _
  have eA : (1 + ((k : ℕ) : ℝ) * (2 * (1 / 8) / ((32 : ℕ) : ℝ))) = 1 + ((k : ℕ) : ℝ) / 128 := by
    push_cast; ring
  have eB : (1 + (((k : ℕ) : ℝ) + 1) * (2 * (1 / 8) / ((32 : ℕ) : ℝ)))
      = (1 + ((k : ℕ) : ℝ) / 128) + 1 / 128 := by
    push_cast; ring
  rw [eA, eB]
  by_cases hk : (k : ℕ) = 0
  · have hk' : ((k : ℕ) : ℝ) = 0 := by exact_mod_cast hk
    have e1 : (1 + ((k : ℕ) : ℝ) / 128) = 1 := by rw [hk']; norm_num
    have e2 : lamC k = (((1 - 1 / 2048 : ℝ)) : ℂ) := by
      unfold lamC; rw [hk']; norm_num
    rw [e1, e2]
    have := cell0 h0 h1
    have e3 : lamW k = (1 / 128) / 2 := by unfold lamW; norm_num
    rw [e3]
    exact this
  · have hk1 : (1 : ℝ) ≤ ((k : ℕ) : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hk
    have := cell_le (s := (x : ℂ)) (a := 1 + ((k : ℕ) : ℝ) / 128) (h := 1 / 128) (ρ := 1 / 2048)
      (by norm_num) (by norm_num) (by simp only [Complex.ofReal_re]; linarith)
    unfold lamW lamC
    have e2 : (1 / 128 : ℝ) / 2 = 1 / 256 := by norm_num
    rw [e2] at this
    exact this

/-- **`h ≥ 0`** on the region where the certificate reads `g`. -/
theorem h_nonneg {s : ℂ} (hs : (s.im = 0 ∧ s.re ≤ 1) ∨ s.re ≤ -(1 / 10 : ℝ) + 1 / 2 ^ 30) :
    0 ≤ Usig (1 / 2048) lamC lamW s - Uex (2 * (1 / 8)) s := by
  rw [sub_nonneg]
  rcases hs with ⟨him, hre⟩ | hre
  · by_cases hx : s.re ≤ 1 - 1 / 2048
    · exact h_left hx
    · rw [not_le] at hx
      have hs' : s = ((s.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [him])
      have := h_sliver (x := s.re) hx.le hre
      rwa [← hs'] at this
  · refine h_left ?_
    have : (1 : ℝ) / 2 ^ 30 ≤ 1 / 2048 := by norm_num
    linarith

end CatalanCore.Cert.SigmaP6H
