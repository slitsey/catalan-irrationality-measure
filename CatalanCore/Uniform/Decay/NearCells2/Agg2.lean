module

public import CatalanCore.Uniform.Decay.NearCells2.Sound2
public import CatalanCore.Uniform.Decay.NearCells.Agg

@[expose] public section
set_option Elab.async false

/-!
# Aggregation with endpoint-merged remainders (lane D, package D6d)

`aggEvalM_sound` has exactly the statement of `NearCells.aggEval_sound`, with `aggEvalM`.
-/

namespace CatalanCore.Uniform.Decay.NearCells

open Finset CatalanCore.Uniform.Decay.Tools

theorem aggEval2_sound {n : ℕ} {zc dd : CQ} {h : ℚ} (s : ℝ) (hs : |s| ≤ h) :
    ∀ (ps : List WP) {C : List ℚ} {F : ℚ} {T : List Tm}, aggEval2 n zc dd h ps = some (C, F, T) →
    |(-(ps.map (fun P => (P.w : ℝ) * PhiW P (zc.toC + (s : ℂ) * dd.toC))).sum)
        - ∑ m ∈ range n, ((coeffs C m : ℚ) : ℝ) * s ^ m - (remSum n T (s : ℂ)).re| ≤ (F : ℝ) := by
  intro ps
  induction ps with
  | nil =>
    intro C F T hC
    simp only [aggEval2] at hC
    cases hC
    simp [coeffs, remSum]
  | cons P ps ih =>
    intro C F T hC
    simp only [aggEval2] at hC
    split at hC
    · rename_i c E T1 C' F' T' hce hag
      cases hC
      have h1 := pieceEval2_sound hce s hs
      have h2 := ih hag
      have hsplit : ∑ m ∈ range n, ((coeffs (addL (scaleL (-P.w) c) C') m : ℚ) : ℝ) * s ^ m
          = -(P.w : ℝ) * ∑ m ∈ range n, ((coeffs c m : ℚ) : ℝ) * s ^ m
            + ∑ m ∈ range n, ((coeffs C' m : ℚ) : ℝ) * s ^ m := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [coeffs_addL, coeffs_scaleL]; push_cast; ring
      have hrs : (remSum n (T1.map (fun t => (⟨t.q, scaleC (-P.w) t.P⟩ : Tm)) ++ T') (s : ℂ)).re
          = -(P.w : ℝ) * (remSum n T1 (s : ℂ)).re + (remSum n T' (s : ℂ)).re := by
        rw [remSum_append, remSum_scale]
        simp [Complex.add_re, Complex.re_ofReal_mul]
      rw [hsplit, hrs, List.map_cons, List.sum_cons]
      have hP : PhiW P (zc.toC + (s : ℂ) * dd.toC) =
          ∫ t in (0 : ℝ)..1, (∑ k ∈ range (P.a.length - 1 + 1), ((coeffs P.a k : ℚ) : ℝ) * t ^ k) *
            Real.log ‖(zc.toC + (s : ℂ) * dd.toC) - (P.A.toC + (t : ℂ) * (P.B.toC - P.A.toC))‖ := rfl
      rw [← hP] at h1
      have hw : |(P.w : ℝ)| * |PhiW P (zc.toC + (s : ℂ) * dd.toC)
          - ∑ m ∈ range n, ((coeffs c m : ℚ) : ℝ) * s ^ m - (remSum n T1 (s : ℂ)).re|
          ≤ |(P.w : ℝ)| * E :=
        mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      rw [← abs_mul] at hw
      have e : -((P.w : ℝ) * PhiW P (zc.toC + (s : ℂ) * dd.toC) +
            (List.map (fun P => (P.w : ℝ) * PhiW P (zc.toC + (s : ℂ) * dd.toC)) ps).sum)
          - (-(P.w : ℝ) * ∑ m ∈ range n, ((coeffs c m : ℚ) : ℝ) * s ^ m
            + ∑ m ∈ range n, ((coeffs C' m : ℚ) : ℝ) * s ^ m)
          - (-(P.w : ℝ) * (remSum n T1 (s : ℂ)).re + (remSum n T' (s : ℂ)).re)
          = -((P.w : ℝ) * (PhiW P (zc.toC + (s : ℂ) * dd.toC)
              - ∑ m ∈ range n, ((coeffs c m : ℚ) : ℝ) * s ^ m - (remSum n T1 (s : ℂ)).re))
            + (-(List.map (fun P => (P.w : ℝ) * PhiW P (zc.toC + (s : ℂ) * dd.toC)) ps).sum
              - ∑ m ∈ range n, ((coeffs C' m : ℚ) : ℝ) * s ^ m - (remSum n T' (s : ℂ)).re) := by ring
      rw [e]
      refine (abs_add_le _ _).trans ?_
      rw [abs_neg]
      push_cast
      exact add_le_add hw h2
    · cases hC

theorem aggEvalM_sound {n : ℕ} {zc dd : CQ} {h : ℚ} (s : ℝ) (hs : |s| ≤ h)
    (ps : List WP) {C : List ℚ} {F : ℚ} (hC : aggEvalM n zc dd h ps = some (C, F)) :
    |(-(ps.map (fun P => (P.w : ℝ) * PhiW P (zc.toC + (s : ℂ) * dd.toC))).sum)
        - ∑ m ∈ range n, ((coeffs C m : ℚ) : ℝ) * s ^ m| ≤ (F : ℝ) := by
  unfold aggEvalM at hC
  split at hC
  · rename_i C0 F0 T hag
    split at hC
    · rename_i hok
      cases hC
      have h1 := aggEval2_sound s hs ps hag
      have hsC : ‖(s : ℂ)‖ ≤ (h : ℝ) := by rw [Complex.norm_real, Real.norm_eq_abs]; exact hs
      have h2 := norm_remSum_le n (mergeAll T) hok (s : ℂ) hsC
      rw [remSum_mergeAll] at h2
      have h3 := (Complex.abs_re_le_norm (remSum n T (s : ℂ))).trans h2
      push_cast
      rw [abs_le] at h1 h3 ⊢
      constructor <;> linarith [h1.1, h1.2, h3.1, h3.2]
    · cases hC
  · cases hC

end CatalanCore.Uniform.Decay.NearCells
