module

public import CatalanCore.Uniform.Decay.NearFast.Piece

@[expose] public section
set_option Elab.async false

/-!
# Aggregation of fast pieces (lane D, package D12)

`aggEvalMF` is `NearCells.aggEvalM` with `pieceEval2` replaced by `pieceEval2F`;
`aggEvalMF_sound` has exactly the statement of `aggEvalM_sound`.
-/

namespace CatalanCore.Uniform.Decay.NearFast

open Finset CatalanCore.Uniform.Decay.Tools CatalanCore.Uniform.Decay.NearCells

/-- Soundness of one fast piece (the statement of `pieceEval2_sound`). -/
theorem pieceEval2F_sound {n : ℕ} {P : WP} {zc dd : CQ} {h : ℚ} {c : List ℚ} {E : ℚ} {T : List Tm}
    (hev : pieceEval2F n P zc dd h = some (c, E, T)) (s : ℝ) (hs : |s| ≤ h) :
    |(∫ t in (0 : ℝ)..1, (∑ k ∈ range (P.a.length - 1 + 1), ((coeffs P.a k : ℚ) : ℝ) * t ^ k) *
        Real.log ‖(zc.toC + (s : ℂ) * dd.toC) - (P.A.toC + (t : ℂ) * (P.B.toC - P.A.toC))‖)
      - ∑ m ∈ range n, ((coeffs c m : ℚ) : ℝ) * s ^ m - (remSum n T (s : ℂ)).re| ≤ (E : ℝ) := by
  obtain ⟨c0, E0, hev0, hclose, hE⟩ := pieceEval2F_imp hev
  have h1 := pieceEval2_sound hev0 s hs
  have hh : (0 : ℝ) ≤ h := le_trans (abs_nonneg s) hs
  have hG := GG_posR
  have hdiff : |∑ m ∈ range n, ((coeffs c m : ℚ) : ℝ) * s ^ m - ∑ m ∈ range n, ((coeffs c0 m : ℚ) : ℝ) * s ^ m|
      ≤ 6 / (GG : ℝ) * ∑ m ∈ range n, (h : ℝ) ^ m := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun m hm => ?_)
    rw [← sub_mul, abs_mul, abs_pow]
    have hs' : |s| ^ m ≤ (h : ℝ) ^ m := pow_le_pow_left₀ (abs_nonneg _) hs m
    exact mul_le_mul (hclose m (Finset.mem_range.1 hm)) hs' (by positivity) (by positivity)
  have hEr : (E : ℝ) = (E0 : ℝ) + 6 / (GG : ℝ) * ∑ m ∈ range n, (h : ℝ) ^ m := by
    rw [hE]; unfold rndAllow; rw [lsum_eq]; push_cast; ring
  rw [hEr]
  rw [abs_le] at h1 hdiff ⊢
  constructor <;> linarith [h1.1, h1.2, hdiff.1, hdiff.2]

/-- Aggregate (weights `-w`) of the fast pieces. -/
def aggEval2F (n : ℕ) (zc dd : CQ) (h : ℚ) : List WP → Option (List ℚ × ℚ × List Tm)
  | [] => some ([], 0, [])
  | P :: ps =>
    match pieceEval2F n P zc dd h, aggEval2F n zc dd h ps with
    | some (c, E, T), some (C, F, T') =>
      some (addL (scaleL (-P.w) c) C, |P.w| * E + F,
        T.map (fun t => (⟨t.q, scaleC (-P.w) t.P⟩ : Tm)) ++ T')
    | _, _ => none

/-- The merged fast aggregate: model `C` and total error `F`. -/
def aggEvalMF (n : ℕ) (zc dd : CQ) (h : ℚ) (ps : List WP) : Option (List ℚ × ℚ) :=
  match aggEval2F n zc dd h ps with
  | some (C, F, T) =>
    if tmOk h (mergeAll T) then some (C, F + tmErr n h (mergeAll T)) else none
  | none => none

theorem aggEval2F_sound {n : ℕ} {zc dd : CQ} {h : ℚ} (s : ℝ) (hs : |s| ≤ h) :
    ∀ (ps : List WP) {C : List ℚ} {F : ℚ} {T : List Tm}, aggEval2F n zc dd h ps = some (C, F, T) →
    |(-(ps.map (fun P => (P.w : ℝ) * PhiW P (zc.toC + (s : ℂ) * dd.toC))).sum)
        - ∑ m ∈ range n, ((coeffs C m : ℚ) : ℝ) * s ^ m - (remSum n T (s : ℂ)).re| ≤ (F : ℝ) := by
  intro ps
  induction ps with
  | nil =>
    intro C F T hC
    simp only [aggEval2F] at hC
    cases hC
    simp [coeffs, remSum]
  | cons P ps ih =>
    intro C F T hC
    simp only [aggEval2F] at hC
    split at hC
    · rename_i c E T1 C' F' T' hce hag
      cases hC
      have h1 := pieceEval2F_sound hce s hs
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

theorem aggEvalMF_sound {n : ℕ} {zc dd : CQ} {h : ℚ} (s : ℝ) (hs : |s| ≤ h)
    (ps : List WP) {C : List ℚ} {F : ℚ} (hC : aggEvalMF n zc dd h ps = some (C, F)) :
    |(-(ps.map (fun P => (P.w : ℝ) * PhiW P (zc.toC + (s : ℂ) * dd.toC))).sum)
        - ∑ m ∈ range n, ((coeffs C m : ℚ) : ℝ) * s ^ m| ≤ (F : ℝ) := by
  unfold aggEvalMF at hC
  split at hC
  · rename_i C0 F0 T hag
    split at hC
    · rename_i hok
      cases hC
      have h1 := aggEval2F_sound s hs ps hag
      have hsC : ‖(s : ℂ)‖ ≤ (h : ℝ) := by rw [Complex.norm_real, Real.norm_eq_abs]; exact hs
      have h2 := norm_remSum_le n (mergeAll T) hok (s : ℂ) hsC
      rw [remSum_mergeAll] at h2
      have h3 := (Complex.abs_re_le_norm (remSum n T (s : ℂ))).trans h2
      push_cast
      rw [abs_le] at h1 h3 ⊢
      constructor <;> linarith [h1.1, h1.2, h3.1, h3.2]
    · cases hC
  · cases hC

end CatalanCore.Uniform.Decay.NearFast
