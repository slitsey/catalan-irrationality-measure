import CatalanCore.Uniform.Decay.NearCells.Link
set_option Elab.async false

/-!
# Endpoint (point-evaluation) cells (lane D, package D6b)

`ptOk`: the model at the centre (`h = 0`, so only enclosure errors) plus the segment modulus
(D5a `segment_log_modulus`, via `PhiW_modulus`) over the ball of radius `ρ`.  Used for cells that
touch a segment endpoint, where jets do not converge.
-/

namespace CatalanCore.Uniform.Decay.NearCells

open Finset CatalanCore.Uniform.Decay.Tools

def ptOk (n : ℕ) (ps : List WP) (zc : CQ) (ρ Rtwo cpi m' : ℚ) (eW eP : ℕ) : Bool :=
  match aggEval n zc ⟨1, 0⟩ 0 ps with
  | some (C, F) =>
    decide (0 < ρ) && decide (0 ≤ cpi) && decide (1 ≤ n) && modAll Rtwo ρ eW eP ps &&
      decide (m' ≤ coeffs C 0 - F - modSum Rtwo ρ eW eP ps + cpi * max (zc.im - ρ) 0)
  | none => false

theorem ptOk_sound {n : ℕ} {ps : List WP} {zc : CQ} {ρ Rtwo cpi m' : ℚ} {eW eP : ℕ}
    (hc : ptOk n ps zc ρ Rtwo cpi m' eW eP = true) (z : ℂ) (hz : ‖z - zc.toC‖ ≤ (ρ : ℝ)) :
    (m' : ℝ) ≤ -(ps.map (fun P => (P.w : ℝ) * PhiW P z)).sum + (cpi : ℝ) * |z.im| := by
  unfold ptOk at hc
  split at hc
  · rename_i C F hag
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨⟨hρ, hcpi⟩, hn⟩, hmod⟩, hfin⟩ := hc
    have hρR : (0 : ℝ) < ρ := by exact_mod_cast hρ
    have hcp : (0 : ℝ) ≤ cpi := by exact_mod_cast hcpi
    have hagg := aggEval_sound (n := n) (zc := zc) (dd := ⟨1, 0⟩) (h := 0) 0 (by simp) ps hag
    have hC0 : ∑ m ∈ range n, ((coeffs C m : ℚ) : ℝ) * (0 : ℝ) ^ m = ((coeffs C 0 : ℚ) : ℝ) := by
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      rw [Finset.sum_range_succ']
      simp
    simp only [Complex.ofReal_zero, zero_mul, add_zero] at hagg
    rw [hC0] at hagg
    have hms := modAll_sum hρR ps hmod (z := zc.toC) (z' := z) (by rw [norm_sub_rev]; exact hz)
    have him : (zc.im : ℝ) - ρ ≤ |z.im| := by
      have h1 := Complex.abs_im_le_norm (z - zc.toC)
      have h2 : (z - zc.toC).im = z.im - (zc.im : ℝ) := by simp [CQ.toC]
      rw [h2] at h1
      have := le_abs_self (z.im - zc.im)
      have h3 := neg_abs_le (z.im - (zc.im : ℝ))
      have h4 := le_abs_self z.im
      linarith
    have hy : ((max (zc.im - ρ) 0 : ℚ) : ℝ) ≤ |z.im| := by
      push_cast
      exact max_le him (abs_nonneg _)
    have hfinR : (m' : ℝ) ≤ ((coeffs C 0 : ℚ) : ℝ) - F - modSum Rtwo ρ eW eP ps + cpi * (max (zc.im - ρ) 0 : ℚ) := by
      exact_mod_cast hfin
    have hcy := mul_le_mul_of_nonneg_left hy hcp
    rw [abs_le] at hagg hms
    nlinarith [hagg.1, hagg.2, hms.1, hms.2]
  · cases hc

end CatalanCore.Uniform.Decay.NearCells
