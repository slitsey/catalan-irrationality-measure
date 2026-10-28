import CatalanCore.Uniform.Decay.NearCells.PieceEval
set_option Elab.async false

/-!
# Aggregating the segment models and the lower Bernstein test (lane D, package D6b)
-/

namespace CatalanCore.Uniform.Decay.NearCells

open Finset CatalanCore.Uniform.Decay.Tools

/-- Semantic potential of a weighted segment (log-integral). -/
noncomputable def PhiW (P : WP) (z : ℂ) : ℝ :=
  ∫ t in (0 : ℝ)..1, (∑ k ∈ range (P.a.length - 1 + 1), ((coeffs P.a k : ℚ) : ℝ) * t ^ k) *
    Real.log ‖z - (P.A.toC + (t : ℂ) * (P.B.toC - P.A.toC))‖

def addL : List ℚ → List ℚ → List ℚ
  | [], l => l
  | l, [] => l
  | x :: xs, y :: ys => (x + y) :: addL xs ys

theorem coeffs_addL (a b : List ℚ) (m : ℕ) : coeffs (addL a b) m = coeffs a m + coeffs b m := by
  induction a generalizing b m with
  | nil => simp [addL, coeffs]
  | cons x xs ih =>
    cases b with
    | nil => simp [addL, coeffs]
    | cons y ys =>
      cases m with
      | zero => simp [addL, coeffs]
      | succ m => simpa [addL, coeffs] using ih ys m

def scaleL (q : ℚ) (c : List ℚ) : List ℚ := c.map (fun x => q * x)

theorem coeffs_scaleL (q : ℚ) (c : List ℚ) (m : ℕ) : coeffs (scaleL q c) m = q * coeffs c m := by
  induction c generalizing m with
  | nil => simp [scaleL, coeffs]
  | cons x xs ih =>
    cases m with
    | zero => simp [scaleL, coeffs]
    | succ m => simpa [scaleL, coeffs] using ih m

/-- Aggregate model `-∑ w_P c_P` and error `∑ |w_P| E_P`. -/
def aggEval (n : ℕ) (zc dd : CQ) (h : ℚ) : List WP → Option (List ℚ × ℚ)
  | [] => some ([], 0)
  | P :: ps =>
    match pieceEval n P zc dd h, aggEval n zc dd h ps with
    | some (c, E), some (C, F) => some (addL (scaleL (-P.w) c) C, |P.w| * E + F)
    | _, _ => none

theorem aggEval_sound {n : ℕ} {zc dd : CQ} {h : ℚ} (s : ℝ) (hs : |s| ≤ h) :
    ∀ (ps : List WP) {C : List ℚ} {F : ℚ}, aggEval n zc dd h ps = some (C, F) →
    |(-(ps.map (fun P => (P.w : ℝ) * PhiW P (zc.toC + (s : ℂ) * dd.toC))).sum)
        - ∑ m ∈ range n, ((coeffs C m : ℚ) : ℝ) * s ^ m| ≤ (F : ℝ) := by
  intro ps
  induction ps with
  | nil =>
    intro C F hC
    simp only [aggEval] at hC
    cases hC
    simp [coeffs]
  | cons P ps ih =>
    intro C F hC
    simp only [aggEval] at hC
    split at hC
    · rename_i c E C' F' hce hag
      cases hC
      have h1 := pieceEval_sound hce s hs
      have h2 := ih hag
      have hsplit : ∑ m ∈ range n, ((coeffs (addL (scaleL (-P.w) c) C') m : ℚ) : ℝ) * s ^ m
          = -(P.w : ℝ) * ∑ m ∈ range n, ((coeffs c m : ℚ) : ℝ) * s ^ m
            + ∑ m ∈ range n, ((coeffs C' m : ℚ) : ℝ) * s ^ m := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [coeffs_addL, coeffs_scaleL]; push_cast; ring
      rw [hsplit, List.map_cons, List.sum_cons]
      have hP : PhiW P (zc.toC + (s : ℂ) * dd.toC) =
          ∫ t in (0 : ℝ)..1, (∑ k ∈ range (P.a.length - 1 + 1), ((coeffs P.a k : ℚ) : ℝ) * t ^ k) *
            Real.log ‖(zc.toC + (s : ℂ) * dd.toC) - (P.A.toC + (t : ℂ) * (P.B.toC - P.A.toC))‖ := rfl
      rw [← hP] at h1
      have hw : |(P.w : ℝ)| * |PhiW P (zc.toC + (s : ℂ) * dd.toC)
          - ∑ m ∈ range n, ((coeffs c m : ℚ) : ℝ) * s ^ m| ≤ |(P.w : ℝ)| * E :=
        mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      rw [← abs_mul] at hw
      have e : -((P.w : ℝ) * PhiW P (zc.toC + (s : ℂ) * dd.toC) +
            (List.map (fun P => (P.w : ℝ) * PhiW P (zc.toC + (s : ℂ) * dd.toC)) ps).sum)
          - (-(P.w : ℝ) * ∑ m ∈ range n, ((coeffs c m : ℚ) : ℝ) * s ^ m
            + ∑ m ∈ range n, ((coeffs C' m : ℚ) : ℝ) * s ^ m)
          = -((P.w : ℝ) * (PhiW P (zc.toC + (s : ℂ) * dd.toC)
              - ∑ m ∈ range n, ((coeffs c m : ℚ) : ℝ) * s ^ m))
            + (-(List.map (fun P => (P.w : ℝ) * PhiW P (zc.toC + (s : ℂ) * dd.toC)) ps).sum
              - ∑ m ∈ range n, ((coeffs C' m : ℚ) : ℝ) * s ^ m) := by ring
      rw [e]
      refine (abs_add_le _ _).trans ?_
      rw [abs_neg]
      push_cast
      exact add_le_add hw h2
    · cases hC

/-- Lower Bernstein test on `[u, u + w]` (only the lower bound). -/
def bernLoOk (a : ℕ → ℚ) (d : ℕ) (u w lo : ℚ) : Bool :=
  (List.range (d + 1)).all fun k => decide (lo ≤ bernK (affK a d u w) d k)

theorem bernLoOk_sound {a : ℕ → ℚ} {d : ℕ} {u w lo : ℚ} (hw : 0 < w)
    (h : bernLoOk a d u w lo = true) {x : ℚ} (hx0 : u ≤ x) (hx1 : x ≤ u + w) :
    lo ≤ peval a d x := by
  unfold bernLoOk at h
  rw [List.all_eq_true] at h
  have hlo : ∀ k ≤ d, lo ≤ bern (affCoeffs a d u w) d k := by
    intro k hk
    have := h k (List.mem_range.mpr (by omega))
    simp only [decide_eq_true_eq, bernK_eq, affK_eq] at this
    exact this
  have hhi : ∀ k ≤ d, bern (affCoeffs a d u w) d k ≤
      ∑ j ∈ range (d + 1), |bern (affCoeffs a d u w) d j| := by
    intro k hk
    exact (le_abs_self _).trans (Finset.single_le_sum (f := fun j => |bern (affCoeffs a d u w) d j|)
      (fun j _ => abs_nonneg _) (Finset.mem_range.2 (by omega)))
  exact (bernstein_range_Icc a d u w hw hlo hhi hx0 hx1).1

/-- Shared-table version of `bernLoOk`: the affine coefficients are computed once. -/
def bernLoOk2 (a : ℕ → ℚ) (d : ℕ) (u w lo : ℚ) : Bool :=
  let aff := (List.range (d + 1)).map (affK a d u w)
  (List.range (d + 1)).all fun k => decide (lo ≤ bernK (coeffs aff) d k)

theorem bernLoOk2_imp {a : ℕ → ℚ} {d : ℕ} {u w lo : ℚ} (h : bernLoOk2 a d u w lo = true) :
    bernLoOk a d u w lo = true := by
  unfold bernLoOk2 at h
  unfold bernLoOk
  rw [List.all_eq_true] at h ⊢
  intro k hk
  have := h k hk
  simp only [decide_eq_true_eq] at this ⊢
  have hkd : k < d + 1 := List.mem_range.1 hk
  have hcongr : bernK (coeffs ((List.range (d + 1)).map (affK a d u w))) d k
      = bernK (affK a d u w) d k := by
    unfold bernK
    rw [lsum_eq, lsum_eq]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i < k + 1 := Finset.mem_range.1 hi
    have : coeffs ((List.range (d + 1)).map (affK a d u w)) i = affK a d u w i := by
      simp [coeffs, List.getD_eq_getElem?_getD, List.getElem?_map, show i < d + 1 by omega]
    rw [this]
  rw [← hcongr]; exact this

end CatalanCore.Uniform.Decay.NearCells
