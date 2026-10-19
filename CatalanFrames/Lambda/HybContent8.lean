module

public import CatalanFrames.Lambda.HybD1Pieces
public import CatalanFrames.Lambda.HybFinal

@[expose] public section

/-!
# λ: the hybrid content theorem with the exact D1 (truncation `K = 8`)

`lam_content_trop8` : for every `ε > 0`, eventually in `r`,
`log (Dhyb lamInst r ⌊r/8⌋) ≤ (Λ8 + ε) r²` with `Λ8 = 24994314577/6665218560 = 3.7499617...`
(exact `Λ_trop(1/8) = 3.7499347`; the loss `2.7·10⁻⁵` is the truncated tail of
`(2 - 2 log 2) α²`).  The prime `p ≡ c (4)` is handled by the constant prefix `9/4` on `(0, 1/68]`,
the 16 exact-D1 pieces on `(1/68, 1/4]`, and the dual pieces D3/D2/D45/D6 beyond.
-/

open Finset Filter CatalanCore CatalanCore.Arith CatalanCore.Arith.Hybrid

namespace CatalanFrames.Lambda

lemma chain_append : ∀ (l1 l2 : List Piece) (s0 : ℝ),
    Chain s0 (l1 ++ l2) ↔ Chain s0 l1 ∧ Chain (lastEnd s0 l1) l2
  | [], l2, s0 => by simp [Chain, lastEnd]
  | P :: l, l2, s0 => by
    simp only [List.cons_append, Chain, lastEnd]
    rw [chain_append l l2 P.t]
    tauto

lemma lastEnd_append : ∀ (l1 l2 : List Piece) (s0 : ℝ),
    lastEnd s0 (l1 ++ l2) = lastEnd (lastEnd s0 l1) l2
  | [], l2, s0 => by simp [lastEnd]
  | P :: l, l2, s0 => by simp only [List.cons_append, lastEnd]; exact lastEnd_append l l2 P.t

lemma listInt_append : ∀ (l1 l2 : List Piece), listInt (l1 ++ l2) = listInt l1 + listInt l2
  | [], l2 => by simp [listInt]
  | P :: l, l2 => by simp only [List.cons_append, listInt]; rw [listInt_append l l2]; ring

lemma ld1_chain : Chain (1 / 68) ld1 := by
  simp only [ld1, Chain, mkPiece]
  norm_num

lemma ld1_end : lastEnd (1 / 68) ld1 = 1 / 4 := by
  simp [ld1, lastEnd, mkPiece]

/-- The two extended lists. -/
noncomputable def l3x : List Piece := ld1 ++ l3
noncomputable def l1x : List Piece := ld1 ++ l1

lemma l3x_chain : Chain (1 / 68) l3x := by
  unfold l3x; rw [chain_append, ld1_end]; exact ⟨ld1_chain, l3_chain⟩

lemma l1x_chain : Chain (1 / 68) l1x := by
  unfold l1x; rw [chain_append, ld1_end]; exact ⟨ld1_chain, l1_chain⟩

lemma l3x_end : lastEnd (1 / 68) l3x = ((5 : ℕ) : ℝ) / ((1 : ℕ) : ℝ) := by
  unfold l3x; rw [lastEnd_append, ld1_end, l3_end]

lemma l1x_end : lastEnd (1 / 68) l1x = ((5 : ℕ) : ℝ) / ((3 : ℕ) : ℝ) := by
  unfold l1x; rw [lastEnd_append, ld1_end, l1_end]

/-- The constant of the exact-D1 route (truncation `K = 8`). -/
theorem lam_const8 :
    ((9 / 4 : ℝ) * (1 / 68) + listInt l3x) / 2 + ((9 / 4 : ℝ) * (1 / 68) + listInt l1x) / 2 =
      24994314577 / 6665218560 := by
  simp only [l3x, l1x, listInt_append, ld1, l3, l1, listInt, Piece.int, mkPiece]
  norm_num

theorem class3_total8 {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop, clsSum 4 (3 : ZMod 4) (lamW r) 0 (5 * r) ≤
      (r : ℝ) ^ 2 * (((9 / 4 : ℝ) * (1 / 68) + listInt l3x) / 2 + ε) := by
  have h := class_total (M := 4) isUnit4_3 (α0 := 9 / 4) (t1 := 1 / 68) (by norm_num)
    (by norm_num) l3x l3x_chain hε
  filter_upwards [h] with r hr
  have := hr (lamW r) (fun p _ _ _ => lam_prefix r p) (by
    intro P hP
    unfold l3x at hP
    rcases List.mem_append.mp hP with h | h
    · exact ld1_covers 3 (by decide) r P h
    · exact l3_covers r P h)
  rw [l3x_end, floor_frac] at this
  simpa [tot4] using this

theorem class1_total8 {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop, clsSum 4 (1 : ZMod 4) (lamW r) 0 (5 * r / 3) ≤
      (r : ℝ) ^ 2 * (((9 / 4 : ℝ) * (1 / 68) + listInt l1x) / 2 + ε) := by
  have h := class_total (M := 4) isUnit4_1 (α0 := 9 / 4) (t1 := 1 / 68) (by norm_num)
    (by norm_num) l1x l1x_chain hε
  filter_upwards [h] with r hr
  have := hr (lamW r) (fun p _ _ _ => lam_prefix r p) (by
    intro P hP
    unfold l1x at hP
    rcases List.mem_append.mp hP with h | h
    · exact ld1_covers 1 (by decide) r P h
    · exact l1_covers r P h)
  rw [l1x_end, floor_frac] at this
  simpa [tot4] using this

/-- **The λ hybrid content theorem (tropical), exact D1 truncated at `K = 8`.** -/
theorem lam_content_trop8 {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop, Real.log (Dhyb lamInst r (r / 8)) ≤
      (24994314577 / 6665218560 + ε) * (r : ℝ) ^ 2 := by
  have h3 := class3_total8 (ε := ε / 4) (by positivity)
  have h1 := class1_total8 (ε := ε / 4) (by positivity)
  have hx := extra_small (ε / 2) (by positivity)
  filter_upwards [h3, h1, hx, eventually_ge_atTop 1] with r hr3 hr1 hrx hr0
  have hmain := lam_log_Dhyb_le r hr0
  have hex := hrx (r / 8) (Nat.div_le_self r 8)
  have hc := lam_const8
  have e : (r : ℝ) ^ 2 * (((9 / 4 : ℝ) * (1 / 68) + listInt l3x) / 2 + ε / 4) +
      (r : ℝ) ^ 2 * (((9 / 4 : ℝ) * (1 / 68) + listInt l1x) / 2 + ε / 4) =
      (r : ℝ) ^ 2 * (24994314577 / 6665218560 + ε / 2) := by
    rw [← mul_add]
    congr 1
    linarith
  nlinarith [hmain, hr3, hr1, hex, e]

end CatalanFrames.Lambda
