module

public import CatalanCore.Arith.Hybrid.PieceSum

@[expose] public section

/-!
# Chains of linear pieces: the summation over a residue class

A class `c` (mod `M`) is covered by a *template*: a constant piece `α0` on `(0, t1]` followed by a
chain of linear pieces `α + β θ` on contiguous intervals.  `class_total` gives, eventually in `r`,

  `clsSum M c w 0 ⌊T r⌋ ≤ r² ((α0 t1 + ∑ ∫ pieces) / φ(M) + ε)`

for every weight `w` bounded by the pieces.  The piece tables are instance data; the bounds
`w p ≤ α r + β p + C` are supplied by the instance (from the generic duals).
-/

open Finset Filter Topology CatalanCore.NT

namespace CatalanCore.Arith.Hybrid

/-- A linear piece `α + β θ` on `(s, t]`, with an additive slack `C`. -/
structure Piece where
  s : ℝ
  t : ℝ
  α : ℝ
  β : ℝ
  C : ℝ

/-- The integral of the piece. -/
noncomputable def Piece.int (P : Piece) : ℝ := P.α * (P.t - P.s) + P.β * (P.t ^ 2 - P.s ^ 2) / 2

/-- Contiguous chain starting at `s0`. -/
def Chain : ℝ → List Piece → Prop
  | _, [] => True
  | s0, P :: l => P.s = s0 ∧ 0 < P.s ∧ P.s ≤ P.t ∧ 0 ≤ P.C ∧ 0 ≤ P.α + P.β * P.s ∧
      0 ≤ P.α + P.β * P.t ∧ Chain P.t l

/-- End of a chain. -/
noncomputable def lastEnd : ℝ → List Piece → ℝ
  | s0, [] => s0
  | _, P :: l => lastEnd P.t l

noncomputable def listInt : List Piece → ℝ
  | [] => 0
  | P :: l => P.int + listInt l

lemma lastEnd_ge : ∀ (l : List Piece) (s0 : ℝ), Chain s0 l → s0 ≤ lastEnd s0 l
  | [], s0, _ => le_refl _
  | P :: l, s0, h => by
    obtain ⟨h1, -, h3, -, -, -, h7⟩ := h
    have := lastEnd_ge l P.t h7
    simp only [lastEnd]; linarith

/-- The pointwise hypothesis of a piece. -/
def Covers {M : ℕ} (c : ZMod M) (w : ℕ → ℝ) (r : ℕ) (P : Piece) : Prop :=
  ∀ p, ⌊P.s * r⌋₊ < p → p ≤ ⌊P.t * r⌋₊ → p.Prime → (p : ZMod M) = c →
    w p ≤ P.α * r + P.β * p + P.C

variable {M : ℕ} [NeZero M]

theorem chain_sum {c : ZMod M} (hc : IsUnit c) :
    ∀ (l : List Piece) (s0 : ℝ), Chain s0 l → ∀ {ε : ℝ}, 0 < ε →
      ∀ᶠ r : ℕ in atTop, ∀ w : ℕ → ℝ, (∀ P ∈ l, Covers c w r P) →
        clsSum M c w ⌊s0 * r⌋₊ ⌊lastEnd s0 l * r⌋₊ ≤
          (r : ℝ) ^ 2 * (listInt l / (M.totient : ℝ) + ε)
  | [], s0, _, ε, hε => by
    filter_upwards [eventually_ge_atTop 0] with r _ w _
    have : clsSum M c w ⌊s0 * r⌋₊ ⌊s0 * r⌋₊ = 0 := by simp [clsSum]
    simp only [lastEnd, this, listInt, zero_div, zero_add]
    positivity
  | P :: l, s0, h, ε, hε => by
    obtain ⟨h1, hs, hst, hC, h0, h1', h7⟩ := h
    have hε2 : 0 < ε / 2 := by positivity
    have hP := piece_sum hc hs hst hC h0 h1' hε2
    have hl := chain_sum hc l P.t h7 hε2
    filter_upwards [hP, hl] with r hPr hlr w hw
    have hPw := hPr w (hw P (List.mem_cons_self))
    have hlw := hlr w (fun Q hQ => hw Q (List.mem_cons_of_mem _ hQ))
    have hle1 : ⌊s0 * r⌋₊ ≤ ⌊P.t * r⌋₊ := by
      apply Nat.floor_le_floor
      exact mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg r)
    have hle2 : ⌊P.t * r⌋₊ ≤ ⌊lastEnd P.t l * r⌋₊ := by
      apply Nat.floor_le_floor
      exact mul_le_mul_of_nonneg_right (lastEnd_ge l P.t h7) (Nat.cast_nonneg r)
    simp only [lastEnd, listInt]
    rw [← clsSum_add c w hle1 hle2]
    have e : ⌊s0 * r⌋₊ = ⌊P.s * r⌋₊ := by rw [h1]
    rw [e] at hle1 ⊢
    have hφ : (M.totient : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne M))).ne'
    have : (r : ℝ) ^ 2 * ((P.int + listInt l) / (M.totient : ℝ) + ε) =
        (r : ℝ) ^ 2 * (P.int / (M.totient : ℝ) + ε / 2) +
          (r : ℝ) ^ 2 * (listInt l / (M.totient : ℝ) + ε / 2) := by
      field_simp; ring
    rw [this]
    have hPw' : clsSum M c w ⌊P.s * r⌋₊ ⌊P.t * r⌋₊ ≤
        (r : ℝ) ^ 2 * (P.int / (M.totient : ℝ) + ε / 2) := by
      simpa [Piece.int] using hPw
    linarith

/-- The prefix `(0, s0 r]` with a constant bound. -/
theorem prefix_sum {c : ZMod M} (hc : IsUnit c) {s0 α0 C0 : ℝ} (hs0 : 0 < s0) (hα : 0 ≤ α0)
    (hC : 0 ≤ C0) {ε1 : ℝ} (hε1 : 0 < ε1) :
    ∀ᶠ r : ℕ in atTop, ∀ w : ℕ → ℝ,
      (∀ p, p ≤ ⌊s0 * r⌋₊ → p.Prime → (p : ZMod M) = c → w p ≤ α0 * r + C0) →
      clsSum M c w 0 ⌊s0 * r⌋₊ ≤ (α0 * r + C0) * (((M.totient : ℝ)⁻¹ + ε1) * (s0 * r)) := by
  have hup := (thetaClass_upper hc hε1)
  have hlim : Tendsto (fun r : ℕ => s0 * (r : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop).const_mul_atTop hs0
  filter_upwards [hlim.eventually hup, eventually_ge_atTop 0] with r hr _ w hw
  have hK : 0 ≤ α0 * r + C0 := add_nonneg (mul_nonneg hα (Nat.cast_nonneg r)) hC
  have hcell := clsSum_le_cell c w (A := 0) (B := ⌊s0 * r⌋₊) (Nat.zero_le _) (K := α0 * r + C0)
    (fun p hp1 hp2 hpp hpc => hw p hp2 hpp hpc)
  have h0 : thetaClassN M c 0 = 0 := by
    unfold thetaClassN
    simp [Finset.sum_filter, Nat.not_prime_zero]
  rw [h0, sub_zero] at hcell
  refine hcell.trans (mul_le_mul_of_nonneg_left ?_ hK)
  exact hr


/-- **The class total**: constant prefix `α0` on `(0, t1]`, then a chain of linear pieces. -/
theorem class_total {c : ZMod M} (hc : IsUnit c) {α0 t1 : ℝ} (hα0 : 0 ≤ α0) (ht1 : 0 < t1)
    (l : List Piece) (hl : Chain t1 l) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop, ∀ w : ℕ → ℝ,
      (∀ p, p ≤ ⌊t1 * r⌋₊ → p.Prime → (p : ZMod M) = c → w p ≤ α0 * r) →
      (∀ P ∈ l, Covers c w r P) →
      clsSum M c w 0 ⌊lastEnd t1 l * r⌋₊ ≤
        (r : ℝ) ^ 2 * ((α0 * t1 + listInt l) / (M.totient : ℝ) + ε) := by
  have hφ : (0 : ℝ) < (M.totient : ℝ) :=
    by exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne M))
  set φ : ℝ := (M.totient : ℝ) with hφdef
  have hφi : 0 < φ⁻¹ := inv_pos.mpr hφ
  set δ : ℝ := ε / (4 * (α0 + 1) * (φ⁻¹ + 1)) with hδ
  have hδpos : 0 < δ := by positivity
  set s0 : ℝ := min t1 δ with hs0
  have hs0pos : 0 < s0 := lt_min ht1 hδpos
  have hs0t : s0 ≤ t1 := min_le_left _ _
  have hs0δ : s0 ≤ δ := min_le_right _ _
  set P0 : Piece := ⟨s0, t1, α0, 0, 0⟩ with hP0
  have hch : Chain s0 (P0 :: l) := by
    refine ⟨rfl, hs0pos, hs0t, le_refl _, ?_, ?_, hl⟩
    · simp [hP0]; exact hα0
    · simp [hP0]; exact hα0
  have hε4 : 0 < ε / 4 := by positivity
  have hch_sum := chain_sum hc (P0 :: l) s0 hch (ε := ε / 2) (by positivity)
  have hpre := prefix_sum hc hs0pos hα0 (le_refl (0 : ℝ)) (ε1 := 1) one_pos
  filter_upwards [hch_sum, hpre] with r hr1 hr2 w hw1 hw2
  have hP0c : Covers c w r P0 := by
    intro p hp1 hp2 hpp hpc
    have : p ≤ ⌊t1 * r⌋₊ := hp2
    have := hw1 p this hpp hpc
    simp only [hP0]
    linarith
  have hall : ∀ P ∈ P0 :: l, Covers c w r P := by
    intro P hP
    rcases List.mem_cons.mp hP with rfl | hP
    · exact hP0c
    · exact hw2 P hP
  have hA := hr1 w hall
  have hB := hr2 w (fun p hp hpp hpc =>
    (hw1 p (le_trans hp (Nat.floor_le_floor (mul_le_mul_of_nonneg_right hs0t
      (Nat.cast_nonneg r)))) hpp hpc).trans (by linarith))
  have hend : lastEnd s0 (P0 :: l) = lastEnd t1 l := by simp [lastEnd, hP0]
  rw [hend] at hA
  have hle1 : ⌊s0 * r⌋₊ ≤ ⌊lastEnd t1 l * r⌋₊ := by
    apply Nat.floor_le_floor
    exact mul_le_mul_of_nonneg_right (hs0t.trans (lastEnd_ge l t1 hl)) (Nat.cast_nonneg r)
  rw [← clsSum_add c w (Nat.zero_le _) hle1]
  have hint : listInt (P0 :: l) = α0 * (t1 - s0) + listInt l := by
    simp [listInt, Piece.int, hP0]
  rw [hint] at hA
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hpre_bound : (α0 * r + 0) * ((φ⁻¹ + 1) * (s0 * r)) ≤ (r : ℝ) ^ 2 * (ε / 4) := by
    have e : (α0 * r + 0) * ((φ⁻¹ + 1) * (s0 * r)) = (r : ℝ) ^ 2 * (α0 * (φ⁻¹ + 1) * s0) := by ring
    rw [e]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have : α0 * (φ⁻¹ + 1) * s0 ≤ α0 * (φ⁻¹ + 1) * δ :=
      mul_le_mul_of_nonneg_left hs0δ (by positivity)
    refine this.trans ?_
    rw [hδ]
    have : α0 * (φ⁻¹ + 1) * (ε / (4 * (α0 + 1) * (φ⁻¹ + 1))) = ε / 4 * (α0 / (α0 + 1)) := by
      field_simp
    rw [this]
    have : α0 / (α0 + 1) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    nlinarith
  have hfin : (r : ℝ) ^ 2 * ((α0 * (t1 - s0) + listInt l) / φ + ε / 2) ≤
      (r : ℝ) ^ 2 * ((α0 * t1 + listInt l) / φ + ε / 2) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have : α0 * (t1 - s0) ≤ α0 * t1 := by nlinarith
    gcongr
  have hrε : 0 ≤ (r : ℝ) ^ 2 * ε := by positivity
  nlinarith [hA, hB, hpre_bound, hfin, hrε]

end CatalanCore.Arith.Hybrid
