module

public import CatalanCore.Arith.Hybrid.Pieces
public import CatalanCore.Arith.Hybrid.DefC5Entries
public import CatalanCore.Arith.Hybrid.DefC7Entries
public import CatalanCore.Arith.Hybrid.PieceTools
public import Mathlib.Analysis.SpecialFunctions.Log.Base

@[expose] public section

/-!
# Frame-free pieces shared by the generic hybrid layer

The piece tables `l3`, `l1`, `ld1` (and the glued `l3x`, `l1x` with the exact `D1` prefix) with their
chain and end-point facts, the dual sums `wC_dual_eq`, `wC7_dual_eq` of the C5/C7 potentials, and a few
elementary lemmas (`sum_range_le_ind`, `sum_Icc_affine`, `not_dvd_6255`, `prime_class4`, ...).  Nothing
here mentions a frame; the λ and mirror instances both use these.
-/

open Finset Filter CatalanCore CatalanCore.Arith CatalanCore.Arith.Hybrid

namespace CatalanFrames.HybCommon


noncomputable def l3 : List Piece :=
  [mkPiece 1 4 9 10 17 0 64 8, mkPiece 9 10 1 1 13 (-5) 32 4, mkPiece 1 1 5 4 7 (-3) 32 2,
   mkPiece 5 4 4 1 9 (-2) 32 4, mkPiece 4 1 5 1 5 (-1) 32 4]

noncomputable def l1 : List Piece :=
  [mkPiece 1 4 9 14 17 0 64 8, mkPiece 9 14 5 7 13 (-7) 32 4, mkPiece 5 7 1 1 9 (-7) 16 2,
   mkPiece 1 1 5 4 7 (-5) 16 2, mkPiece 5 4 4 3 9 (-6) 32 4, mkPiece 4 3 5 3 5 (-3) 32 4]

lemma l3_chain : Chain (1 / 4) l3 := by
  simp only [l3, Chain, mkPiece]
  norm_num

lemma l1_chain : Chain (1 / 4) l1 := by
  simp only [l1, Chain, mkPiece]
  norm_num

lemma l3_end : lastEnd (1 / 4) l3 = ((5 : ℕ) : ℝ) / ((1 : ℕ) : ℝ) := by
  simp [l3, lastEnd, mkPiece]

lemma l1_end : lastEnd (1 / 4) l1 = ((5 : ℕ) : ℝ) / ((3 : ℕ) : ℝ) := by
  simp [l1, lastEnd, mkPiece]

/-! ### Class totals -/

lemma tot4 : ((Nat.totient 4 : ℕ) : ℝ) = 2 := by
  rw [show Nat.totient 4 = 2 by decide]; norm_num

lemma isUnit4_3 : IsUnit (3 : ZMod 4) := by decide
lemma isUnit4_1 : IsUnit (1 : ZMod 4) := isUnit_one

noncomputable def ld1 : List Piece :=
  [mkPiece 1 68 1 64 17 (64) 320 8,
   mkPiece 1 64 1 60 19 (-64) 320 8,
   mkPiece 1 60 1 56 17 (56) 320 8,
   mkPiece 1 56 1 52 19 (-56) 320 8,
   mkPiece 1 52 1 48 17 (48) 320 8,
   mkPiece 1 48 1 44 19 (-48) 320 8,
   mkPiece 1 44 1 40 17 (40) 320 8,
   mkPiece 1 40 1 36 19 (-40) 320 8,
   mkPiece 1 36 1 32 17 (32) 320 8,
   mkPiece 1 32 1 28 19 (-32) 320 8,
   mkPiece 1 28 1 24 17 (24) 320 8,
   mkPiece 1 24 1 20 19 (-24) 320 8,
   mkPiece 1 20 1 16 17 (16) 320 8,
   mkPiece 1 16 1 12 19 (-16) 320 8,
   mkPiece 1 12 1 8 17 (8) 320 8,
   mkPiece 1 8 1 4 19 (-8) 320 8]


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
theorem const8 :
    ((9 / 4 : ℝ) * (1 / 68) + listInt l3x) / 2 + ((9 / 4 : ℝ) * (1 / 68) + listInt l1x) / 2 =
      24994314577 / 6665218560 := by
  simp only [l3x, l1x, listInt_append, ld1, l3, l1, listInt, Piece.int, mkPiece]
  norm_num

lemma sum_range_gap (n q k : ℕ) (hqk : q ≤ k) :
    ∑ i ∈ Finset.range n, (if q ≤ i ∧ i < k then 0 else 1) + (min n k - min n q) = n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    split_ifs <;> omega

lemma sum_range_two (n q : ℕ) :
    ∑ i ∈ Finset.range n, (if i < q then 2 else 1) = n + min n q := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    split_ifs <;> omega

/-- The dual value of the D2 potentials. -/
lemma wC_dual_eq {o p r m k : ℕ} (S : CSetup o p r m k) :
    ∑ a : Fin r ⊕ Fin m, wC p r k (Frame.hybRow r m a) +
      ∑ b : Fin r ⊕ Fin m, wC p r k (Frame.hybCol r m b) = 2 * r + 2 * m - (p + k - r) := by
  have hk := S.hk; have := S.ho0; have := S.ho3; have := S.hp6
  have hLlo := S.hLlo
  have hLhi := S.hLhi
  have hrp := S.hrp
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  have hc : ∑ c : Fin r, wC p r k (c : ℕ) = r - (p + k - r) := by
    have : ∀ c : Fin r, wC p r k (c : ℕ) = if r - p ≤ (c : ℕ) ∧ (c : ℕ) < k then 0 else 1 :=
      fun c => by unfold wC; rw [if_pos c.2]
    simp only [this]
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => if r - p ≤ i ∧ i < k then 0 else 1) r]
    have := sum_range_gap r (r - p) k (by omega)
    omega
  have hzr : ∑ i : Fin m, wC p r k (Frame.hybRow r m (Sum.inr i)) =
      m + min m ((p + k - r + 1) / 2) := by
    have : ∀ i : Fin m, wC p r k (Frame.hybRow r m (Sum.inr i)) =
        if (i : ℕ) < (p + k - r + 1) / 2 then 2 else 1 := fun i => by
      show wC p r k (r + 2 * (i : ℕ)) = _
      unfold wC
      rw [if_neg (by omega)]
      by_cases h : (i : ℕ) < (p + k - r + 1) / 2
      · rw [if_pos h, if_pos (by omega)]
      · rw [if_neg h, if_neg (by omega)]
    simp only [this]
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => if i < (p + k - r + 1) / 2 then 2 else 1) m,
      sum_range_two]
  have hzc : ∑ i : Fin m, wC p r k (Frame.hybCol r m (Sum.inr i)) =
      m + min m ((p + k - r) / 2) := by
    have : ∀ i : Fin m, wC p r k (Frame.hybCol r m (Sum.inr i)) =
        if (i : ℕ) < (p + k - r) / 2 then 2 else 1 := fun i => by
      show wC p r k (r + 2 * (i : ℕ) + 1) = _
      unfold wC
      rw [if_neg (by omega)]
      by_cases h : (i : ℕ) < (p + k - r) / 2
      · rw [if_pos h, if_pos (by omega)]
      · rw [if_neg h, if_neg (by omega)]
    simp only [this]
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => if i < (p + k - r) / 2 then 2 else 1) m,
      sum_range_two]
  have hcc : ∑ c : Fin r, wC p r k (Frame.hybCol r m (Sum.inl c)) = r - (p + k - r) := hc
  have hrr : ∑ c : Fin r, wC p r k (Frame.hybRow r m (Sum.inl c)) = r - (p + k - r) := hc
  rw [hrr, hcc, hzr, hzc]
  omega


/-- The dual value of the D2 potentials of C7. -/
lemma wC7_dual_eq {o p r m k : ℕ} (S : CSetup7 o p r m k) :
    ∑ a : Fin r ⊕ Fin m, wC7 p r k (Frame.hybRow r m a) +
      ∑ b : Fin r ⊕ Fin m, wC7 p r k (Frame.hybCol r m b) = 2 * r + 2 * m - (p + k - r) := by
  have hk := S.hk; have := S.ho0; have := S.ho3; have := S.hp6
  have hLlo := S.hLlo
  have hLhi := S.hLhi
  have hrp := S.hrp
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  have hc : ∑ c : Fin r, wC7 p r k (c : ℕ) = r - (p + k - r) := by
    have : ∀ c : Fin r, wC7 p r k (c : ℕ) = if r - p ≤ (c : ℕ) ∧ (c : ℕ) < k then 0 else 1 :=
      fun c => by unfold wC7; rw [if_pos c.2]
    simp only [this]
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => if r - p ≤ i ∧ i < k then 0 else 1) r]
    have := sum_range_gap r (r - p) k (by omega)
    omega
  have hzr : ∑ i : Fin m, wC7 p r k (Frame.hybRow r m (Sum.inr i)) =
      m + min m ((p + k - r + 1) / 2) := by
    have : ∀ i : Fin m, wC7 p r k (Frame.hybRow r m (Sum.inr i)) =
        if (i : ℕ) < (p + k - r + 1) / 2 then 2 else 1 := fun i => by
      show wC7 p r k (r + 2 * (i : ℕ)) = _
      unfold wC7
      rw [if_neg (by omega)]
      by_cases h : (i : ℕ) < (p + k - r + 1) / 2
      · rw [if_pos h, if_pos (by omega)]
      · rw [if_neg h, if_neg (by omega)]
    simp only [this]
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => if i < (p + k - r + 1) / 2 then 2 else 1) m,
      sum_range_two]
  have hzc : ∑ i : Fin m, wC7 p r k (Frame.hybCol r m (Sum.inr i)) =
      m + min m ((p + k - r) / 2) := by
    have : ∀ i : Fin m, wC7 p r k (Frame.hybCol r m (Sum.inr i)) =
        if (i : ℕ) < (p + k - r) / 2 then 2 else 1 := fun i => by
      show wC7 p r k (r + 2 * (i : ℕ) + 1) = _
      unfold wC7
      rw [if_neg (by omega)]
      by_cases h : (i : ℕ) < (p + k - r) / 2
      · rw [if_pos h, if_pos (by omega)]
      · rw [if_neg h, if_neg (by omega)]
    simp only [this]
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => if i < (p + k - r) / 2 then 2 else 1) m,
      sum_range_two]
  have hcc : ∑ c : Fin r, wC7 p r k (Frame.hybCol r m (Sum.inl c)) = r - (p + k - r) := hc
  have hrr : ∑ c : Fin r, wC7 p r k (Frame.hybRow r m (Sum.inl c)) = r - (p + k - r) := hc
  rw [hrr, hcc, hzr, hzc]
  omega

lemma sum_range_le_ind (n k : ℕ) :
    ∑ i ∈ Finset.range n, (if k ≤ i then 1 else 0) = n - k := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    by_cases h : k ≤ n
    · rw [if_pos h]; omega
    · rw [if_neg h]; omega

lemma not_dvd_6255 {p : ℕ} (hp : p.Prime) (h7 : 7 ≤ p) (h139 : p ≠ 139) : ¬ p ∣ 6255 := by
  intro hd
  have h : (6255 : ℕ) = 3 * 3 * 5 * 139 := by norm_num
  rw [h] at hd
  rcases (Nat.Prime.dvd_mul hp).1 hd with h1 | h1
  · rcases (Nat.Prime.dvd_mul hp).1 h1 with h2 | h2
    · rcases (Nat.Prime.dvd_mul hp).1 h2 with h3 | h3
      · have := Nat.le_of_dvd (by norm_num) h3; omega
      · have := Nat.le_of_dvd (by norm_num) h3; omega
    · have := Nat.le_of_dvd (by norm_num) h2; omega
  · have := (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 139)).1 h1
    exact h139 this

lemma sum_Icc_affine (J : ℕ) (a b : ℝ) :
    ∑ j ∈ Finset.Icc 1 J, (a - b * j) = J * a - b * (J * (J + 1) / 2) := by
  induction J with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    push_cast
    ring


lemma cast4_two : (2 : ZMod 4) ≠ 3 ∧ (2 : ZMod 4) ≠ 1 := by decide

lemma prime_class4 {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) :
    ((p : ZMod 4) = 3 ∧ (p : ZMod 4) ≠ 1) ∨ ((p : ZMod 4) = 1 ∧ (p : ZMod 4) ≠ 3) := by
  have hodd := hp.eq_two_or_odd.resolve_left h2
  have : p % 4 = 1 ∨ p % 4 = 3 := by omega
  rcases this with h | h
  · right
    have e : (p : ZMod 4) = ((p % 4 : ℕ) : ZMod 4) := (ZMod.natCast_mod p 4).symm
    rw [e, h]; decide
  · left
    have e : (p : ZMod 4) = ((p % 4 : ℕ) : ZMod 4) := (ZMod.natCast_mod p 4).symm
    rw [e, h]; decide


end CatalanFrames.HybCommon
