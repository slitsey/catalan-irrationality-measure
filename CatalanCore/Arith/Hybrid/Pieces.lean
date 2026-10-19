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

end CatalanCore.Arith.Hybrid
