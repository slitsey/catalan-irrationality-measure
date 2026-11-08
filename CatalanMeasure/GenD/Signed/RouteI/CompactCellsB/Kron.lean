module

public import CatalanMeasure.GenD.Signed.RouteI.CompactCells

@[expose] public section
set_option Elab.async false

/-!
# Route I `CompactCellsB.Kron`: Kronecker-packed check of the C7 compact cells (GP Lemma 7.5)

Generic. `CompactCells.cellChk` evaluates the Chebyshev recurrence in `ℤ[z]` on lists of about 130
integers of about 8000 bits. Here the same recurrence is evaluated at the integer `z = X`,
`X = 2^s + 51` (an odd radix): `pk X` is the ring homomorphism `ℤ[z] → ℤ` (`pk_addP`, `pk_smulP`,
`pk_linP`, `pk_mulP`), `packN` is the packed value of `cellN` (`pk_cellN`), and `dec` reads the
balanced base-`X` digits back (`dec_pk`). A scalar `l1` majorant `nBound` of the cell polynomial
(`l1_cellN_le`) gives `2 · nBound < X`, hence all coefficients of `cellN` are below `X/2`
and the decoded list is `cellN` followed by zeros. `cellChkK_sound`: `cellChkK … = true →
cellChk … = true`, so `cell_le`, `ordCap_of_chain` and `nearCap_of_chain` of `CompactCells`
apply unchanged.

kcost: one cell is 129 packed steps on integers of at most about 1.1 million bits, then one decode of
`P.length + 5` digits (measured 0.4 to 1.0 s per cell, prototype).
-/

namespace CatalanMeasure.GenD.Signed.RouteI.CompactCellsB

open CatalanMeasure.Signed.ChebSquare
open CatalanMeasure.GenD.Signed.RouteI.CompactCells

/-! ### Packing homomorphism -/

def pk (X : ℤ) : List ℤ → ℤ
  | [] => 0
  | a :: l => a + X * pk X l

theorem pk_addP (X : ℤ) : ∀ a b : List ℤ, pk X (addP a b) = pk X a + pk X b
  | [], b => by simp [addP, pk]
  | a :: l, [] => by simp [addP, pk]
  | a :: l, b :: r => by
    simp only [addP, pk, pk_addP X l r]; ring

theorem pk_smulP (X c : ℤ) : ∀ l : List ℤ, pk X (smulP c l) = c * pk X l
  | [] => by simp [smulP, pk]
  | a :: l => by
    have := pk_smulP X c l
    simp only [smulP, List.map_cons, pk] at this ⊢
    rw [this]; ring

theorem pk_linP (X A B : ℤ) (l : List ℤ) : pk X (linP A B l) = (A + B * X) * pk X l := by
  simp only [linP, pk_addP, pk_smulP, pk]
  ring

theorem pk_mulP (X : ℤ) : ∀ a b : List ℤ, pk X (mulP a b) = pk X a * pk X b
  | [], b => by simp [mulP, pk]
  | a :: l, b => by
    simp only [mulP, pk_addP, pk_smulP, pk, pk_mulP X l b]
    ring

theorem pk_sNext (X A B E : ℤ) (s0 s1 : List ℤ) :
    pk X (sNext A B E s0 s1) = 2 * (A + B * X) * pk X s1 - E ^ 2 * pk X s0 := by
  simp only [sNext, pk_addP, pk_smulP, pk_linP]
  ring

/-- The packed recurrence. -/
def clocI (A B X E : ℤ) : List ℤ → ℤ → ℤ → ℤ → ℤ
  | [], _, _, acc => acc
  | p :: ps, s0, s1, acc =>
    clocI A B X E ps s1 (2 * (A + B * X) * s1 - E ^ 2 * s0) (E * acc + p * s0)

theorem pk_cloc (X A B E : ℤ) : ∀ (ps : List ℤ) (s0 s1 acc : List ℤ),
    pk X (cloc A B E ps s0 s1 acc) = clocI A B X E ps (pk X s0) (pk X s1) (pk X acc)
  | [], s0, s1, acc => by simp [cloc, clocI]
  | p :: ps, s0, s1, acc => by
    simp only [cloc, clocI, pk_cloc X A B E ps, pk_sNext, pk_addP, pk_smulP]

/-- The packed value of `cellN`. -/
def packN (P : List ℤ) (D : ℕ) (loN loD MN MD eN eD Q : ℤ) (c : CellData) (X : ℤ) : ℤ :=
  let E := cE loN loD Q
  let A := cA loN loD Q c
  let B := cB loD c
  let cL := clocI A B X E P 1 (A + B * X) 0
  let G := cm MN MD eN eD c * (D : ℤ) * E ^ P.length - cDen MD eD * E * cL
  let q := ((2 * Q) ^ 2 + (c.u0 + c.u1) ^ 2) + 2 * (c.u0 + c.u1) * (c.u1 - c.u0) * X
    + (c.u1 - c.u0) ^ 2 * X * X
  2 ^ 60 * (G * q) - 2 * c.b * (2 * Q) * (cDen MD eD * (D : ℤ) * E ^ P.length) *
    ((c.u0 + c.u1) + (c.u1 - c.u0) * X)

theorem pk_cellN (P : List ℤ) (D : ℕ) (loN loD MN MD eN eD Q : ℤ) (c : CellData) (X : ℤ) :
    pk X (cellN P D loN loD MN MD eN eD Q c) = packN P D loN loD MN MD eN eD Q c X := by
  unfold cellN cG cLz packN
  simp only [pk_addP, pk_smulP, pk_mulP, pk_cloc, pk]
  ring

/-! ### Balanced digits -/

def dig (X v : ℤ) : ℤ × ℤ :=
  let d := (v + X / 2) % X - X / 2
  (d, (v - d) / X)

def dec (X : ℤ) : ℕ → ℤ → List ℤ
  | 0, _ => []
  | f + 1, v => (dig X v).1 :: dec X f (dig X v).2

theorem dig_pk {X a r : ℤ} (hX : 0 < X) (ha : 2 * |a| < X) : dig X (a + X * r) = (a, r) := by
  have h : (a + X * r + X / 2) % X = a + X / 2 := by
    rw [show a + X * r + X / 2 = (a + X / 2) + X * r by ring, Int.add_mul_emod_self_left]
    apply Int.emod_eq_of_lt
    · rcases abs_cases a with ⟨h1, _⟩ | ⟨h1, _⟩ <;> omega
    · rcases abs_cases a with ⟨h1, _⟩ | ⟨h1, _⟩ <;> omega
  simp only [dig, h]
  have e1 : a + X / 2 - X / 2 = a := by ring
  rw [e1]
  have e2 : a + X * r - a = X * r := by ring
  rw [e2, Int.mul_ediv_cancel_left r (ne_of_gt hX)]

theorem dec_zero {X : ℤ} (hX : 0 < X) : ∀ f : ℕ, dec X f 0 = List.replicate f 0
  | 0 => rfl
  | f + 1 => by
    have h : dig X 0 = (0, 0) := by
      have := dig_pk (X := X) (a := 0) (r := 0) hX (by simpa using hX)
      simpa using this
    simp only [dec, h, dec_zero hX f, List.replicate_succ]

theorem dec_pk {X : ℤ} (hX : 0 < X) : ∀ (l : List ℤ) (f : ℕ), l.length ≤ f →
    (∀ a ∈ l, 2 * |a| < X) → dec X f (pk X l) = l ++ List.replicate (f - l.length) 0
  | [], f, _, _ => by simp [pk, dec_zero hX]
  | a :: l, f, hf, hl => by
    cases f with
    | zero => simp at hf
    | succ f =>
      have ha : 2 * |a| < X := hl a (List.mem_cons_self ..)
      have hl' : ∀ b ∈ l, 2 * |b| < X := fun b hb => hl b (List.mem_cons_of_mem _ hb)
      have ih := dec_pk hX l f (by simpa using hf) hl'
      simp only [pk, dec, dig_pk hX ha, ih, List.length_cons, List.cons_append, Nat.add_sub_add_right]

/-! ### `l1` -/

theorem l1_nn : ∀ l : List ℤ, 0 ≤ l1 l
  | [] => by simp [l1]
  | a :: t => by
    have := l1_nn t
    have := abs_nonneg a
    simp only [l1]; linarith

theorem abs_le_l1' : ∀ (l : List ℤ) (e : ℤ), e ∈ l → |e| ≤ l1 l
  | [], e, h => by simp at h
  | a :: t, e, h => by
    have := l1_nn t
    have := abs_nonneg a
    simp only [l1]
    rcases List.mem_cons.mp h with rfl | h
    · linarith
    · have := abs_le_l1' t e h
      linarith

theorem l1_append_zeros : ∀ (L : List ℤ) (k : ℕ), l1 (L ++ List.replicate k 0) = l1 L
  | [], k => by
    induction k with
    | zero => simp [l1]
    | succ k ih => simpa [List.replicate_succ, l1] using ih
  | a :: L, k => by
    simp only [List.cons_append, l1, l1_append_zeros L k]

def chkL (L : List ℤ) : Bool := decide (l1 L.tail ≤ L.headD 0)

theorem chkL_pad (L : List ℤ) (k : ℕ) : chkL (L ++ List.replicate k 0) = chkL L := by
  cases L with
  | nil =>
    cases k with
    | zero => rfl
    | succ k =>
      have h0 : l1 (List.replicate k 0) = 0 := by
        have := l1_append_zeros [] k
        simpa [l1] using this
      simp [chkL, List.replicate_succ, h0, l1]
  | cons a t =>
    simp [chkL, l1_append_zeros]

theorem l1_addP_le : ∀ a b : List ℤ, l1 (addP a b) ≤ l1 a + l1 b
  | [], b => by simp [addP, l1]
  | a :: t, [] => by simp [addP, l1]
  | a :: t, b :: r => by
    have := l1_addP_le t r
    have := abs_add_le a b
    simp only [addP, l1]; linarith

theorem l1_smulP (c : ℤ) : ∀ l : List ℤ, l1 (smulP c l) = |c| * l1 l
  | [] => by simp [smulP, l1]
  | a :: l => by
    have := l1_smulP c l
    simp only [smulP, List.map_cons, l1] at this ⊢
    rw [this, abs_mul]; ring

theorem l1_linP_le (A B : ℤ) (l : List ℤ) : l1 (linP A B l) ≤ (|A| + |B|) * l1 l := by
  have h := l1_addP_le (smulP A l) (0 :: smulP B l)
  simp only [linP, l1_smulP, l1, abs_zero, zero_add] at h ⊢
  linarith

theorem l1_mulP_le : ∀ a b : List ℤ, l1 (mulP a b) ≤ l1 a * l1 b
  | [], b => by simp [mulP, l1]
  | x :: l, b => by
    have ih := l1_mulP_le l b
    have h := l1_addP_le (smulP x b) (0 :: mulP l b)
    simp only [mulP, l1_smulP, l1, abs_zero, zero_add] at h ⊢
    nlinarith

/-- Scalar majorant of the recurrence (`a = |A| + |B|`). -/
def clocB (a E : ℤ) : List ℤ → ℤ → ℤ → ℤ → ℤ
  | [], _, _, m => m
  | p :: ps, m0, m1, m => clocB a E ps m1 (2 * a * m1 + E ^ 2 * m0) (|E| * m + |p| * m0)

theorem l1_sNext_le (A B E : ℤ) (s0 s1 : List ℤ) (m0 m1 : ℤ) (h0 : l1 s0 ≤ m0) (h1 : l1 s1 ≤ m1) :
    l1 (sNext A B E s0 s1) ≤ 2 * (|A| + |B|) * m1 + E ^ 2 * m0 := by
  have h := l1_addP_le (smulP 2 (linP A B s1)) (smulP (-(E ^ 2)) s0)
  simp only [sNext, l1_smulP] at h ⊢
  have hl := l1_linP_le A B s1
  have hE : |-(E ^ 2)| = E ^ 2 := by rw [abs_neg]; exact abs_of_nonneg (sq_nonneg E)
  rw [hE] at h
  have hab : 0 ≤ |A| + |B| := by positivity
  have e1 : (|A| + |B|) * l1 s1 ≤ (|A| + |B|) * m1 := mul_le_mul_of_nonneg_left h1 hab
  have e2 : E ^ 2 * l1 s0 ≤ E ^ 2 * m0 := mul_le_mul_of_nonneg_left h0 (sq_nonneg E)
  have e3 : |(2 : ℤ)| = 2 := by norm_num
  rw [e3] at h
  nlinarith

theorem l1_cloc_le (A B E : ℤ) : ∀ (ps : List ℤ) (s0 s1 acc : List ℤ) (m0 m1 m : ℤ),
    l1 s0 ≤ m0 → l1 s1 ≤ m1 → l1 acc ≤ m →
    l1 (cloc A B E ps s0 s1 acc) ≤ clocB (|A| + |B|) E ps m0 m1 m
  | [], s0, s1, acc, m0, m1, m, _, _, h => by simpa [cloc, clocB] using h
  | p :: ps, s0, s1, acc, m0, m1, m, h0, h1, h => by
    simp only [cloc, clocB]
    refine l1_cloc_le A B E ps s1 _ _ m1 _ _ h1 (l1_sNext_le A B E s0 s1 m0 m1 h0 h1) ?_
    have h2 := l1_addP_le (smulP E acc) (smulP p s0)
    simp only [l1_smulP] at h2
    have e1 : |E| * l1 acc ≤ |E| * m := mul_le_mul_of_nonneg_left h (abs_nonneg E)
    have e2 : |p| * l1 s0 ≤ |p| * m0 := mul_le_mul_of_nonneg_left h0 (abs_nonneg p)
    linarith

/-- The scalar bound on `l1 (cellN …)`. -/
def nBound (P : List ℤ) (D : ℕ) (loN loD MN MD eN eD Q : ℤ) (c : CellData) : ℤ :=
  let E := cE loN loD Q
  let a := |cA loN loD Q c| + |cB loD c|
  let mG := |cm MN MD eN eD c * (D : ℤ) * E ^ P.length| + |cDen MD eD * E| * clocB a E P 1 a 0
  let qb := |(2 * Q) ^ 2 + (c.u0 + c.u1) ^ 2| + (|2 * (c.u0 + c.u1) * (c.u1 - c.u0)| + |(c.u1 - c.u0) ^ 2|)
  2 ^ 60 * (mG * qb) + |2 * c.b * (2 * Q) * (cDen MD eD * (D : ℤ) * E ^ P.length)| *
    (|c.u0 + c.u1| + |c.u1 - c.u0|)

theorem l1_cellN_le (P : List ℤ) (D : ℕ) (loN loD MN MD eN eD Q : ℤ) (c : CellData) :
    l1 (cellN P D loN loD MN MD eN eD Q c) ≤ nBound P D loN loD MN MD eN eD Q c := by
  have hc := l1_cloc_le (cA loN loD Q c) (cB loD c) (cE loN loD Q) P [1]
    [cA loN loD Q c, cB loD c] [] 1 (|cA loN loD Q c| + |cB loD c|) 0
    (by simp [l1]) (by simp [l1]) (by simp [l1])
  have hG : l1 (cG P D loN loD MN MD eN eD Q c) ≤
      |cm MN MD eN eD c * (D : ℤ) * cE loN loD Q ^ P.length| + |cDen MD eD * cE loN loD Q| *
        clocB (|cA loN loD Q c| + |cB loD c|) (cE loN loD Q) P 1 (|cA loN loD Q c| + |cB loD c|) 0 := by
    have h := l1_addP_le [cm MN MD eN eD c * (D : ℤ) * cE loN loD Q ^ P.length]
      (smulP (-(cDen MD eD * cE loN loD Q)) (cLz P loN loD Q c))
    simp only [cG, l1_smulP, l1, abs_neg, add_zero] at h ⊢
    have : |cDen MD eD * cE loN loD Q| * l1 (cLz P loN loD Q c) ≤ |cDen MD eD * cE loN loD Q| *
        clocB (|cA loN loD Q c| + |cB loD c|) (cE loN loD Q) P 1 (|cA loN loD Q c| + |cB loD c|) 0 :=
      mul_le_mul_of_nonneg_left hc (abs_nonneg _)
    linarith
  have hq : l1 [(2 * Q) ^ 2 + (c.u0 + c.u1) ^ 2, 2 * (c.u0 + c.u1) * (c.u1 - c.u0), (c.u1 - c.u0) ^ 2] =
      |(2 * Q) ^ 2 + (c.u0 + c.u1) ^ 2| + (|2 * (c.u0 + c.u1) * (c.u1 - c.u0)| + |(c.u1 - c.u0) ^ 2|) := by
    simp [l1]
  have hm := l1_mulP_le (cG P D loN loD MN MD eN eD Q c)
    [(2 * Q) ^ 2 + (c.u0 + c.u1) ^ 2, 2 * (c.u0 + c.u1) * (c.u1 - c.u0), (c.u1 - c.u0) ^ 2]
  rw [hq] at hm
  have hg0 := l1_nn (cG P D loN loD MN MD eN eD Q c)
  have hqnn : 0 ≤ |(2 * Q) ^ 2 + (c.u0 + c.u1) ^ 2| + (|2 * (c.u0 + c.u1) * (c.u1 - c.u0)| + |(c.u1 - c.u0) ^ 2|) := by
    positivity
  have hmq : l1 (mulP (cG P D loN loD MN MD eN eD Q c)
      [(2 * Q) ^ 2 + (c.u0 + c.u1) ^ 2, 2 * (c.u0 + c.u1) * (c.u1 - c.u0), (c.u1 - c.u0) ^ 2]) ≤
      (|cm MN MD eN eD c * (D : ℤ) * cE loN loD Q ^ P.length| + |cDen MD eD * cE loN loD Q| *
        clocB (|cA loN loD Q c| + |cB loD c|) (cE loN loD Q) P 1 (|cA loN loD Q c| + |cB loD c|) 0) *
      (|(2 * Q) ^ 2 + (c.u0 + c.u1) ^ 2| + (|2 * (c.u0 + c.u1) * (c.u1 - c.u0)| + |(c.u1 - c.u0) ^ 2|)) :=
    hm.trans (mul_le_mul_of_nonneg_right hG hqnn)
  have h := l1_addP_le (smulP (2 ^ 60) (mulP (cG P D loN loD MN MD eN eD Q c)
      [(2 * Q) ^ 2 + (c.u0 + c.u1) ^ 2, 2 * (c.u0 + c.u1) * (c.u1 - c.u0), (c.u1 - c.u0) ^ 2]))
    (smulP (-(2 * c.b * (2 * Q) * (cDen MD eD * D * (cE loN loD Q) ^ P.length)))
      [c.u0 + c.u1, c.u1 - c.u0])
  have e60 : |(2 : ℤ) ^ 60| = 2 ^ 60 := abs_of_pos (by positivity)
  unfold cellN nBound
  refine h.trans ?_
  simp only [l1_smulP, abs_neg, l1, add_zero, e60]
  have := mul_le_mul_of_nonneg_left hmq (show (0 : ℤ) ≤ 2 ^ 60 by positivity)
  linarith

/-! ### Lengths -/

theorem len_addP : ∀ a b : List ℤ, (addP a b).length = max a.length b.length
  | [], b => by simp [addP]
  | a :: l, [] => by simp [addP]
  | a :: l, b :: r => by
    simp only [addP, List.length_cons, len_addP l r]; omega

theorem len_smulP (c : ℤ) (l : List ℤ) : (smulP c l).length = l.length := by simp [smulP]

theorem len_linP_le (A B : ℤ) (l : List ℤ) : (linP A B l).length ≤ l.length + 1 := by
  simp only [linP, len_addP, len_smulP, List.length_cons]; omega

theorem len_sNext_le (A B E : ℤ) (s0 s1 : List ℤ) :
    (sNext A B E s0 s1).length ≤ max (s1.length + 1) s0.length := by
  have := len_linP_le A B s1
  simp only [sNext, len_addP, len_smulP]; omega

theorem len_cloc_le (A B E : ℤ) : ∀ (ps : List ℤ) (k : ℕ) (s0 s1 acc : List ℤ),
    s0.length ≤ k + 1 → s1.length ≤ k + 2 →
    (cloc A B E ps s0 s1 acc).length ≤ max acc.length (k + ps.length)
  | [], k, s0, s1, acc, _, _ => by simp [cloc]
  | p :: ps, k, s0, s1, acc, h0, h1 => by
    have hs := len_sNext_le A B E s0 s1
    have ih := len_cloc_le A B E ps (k + 1) s1 (sNext A B E s0 s1)
      (addP (smulP E acc) (smulP p s0)) (by omega) (by omega)
    have ha : (addP (smulP E acc) (smulP p s0)).length = max acc.length s0.length := by
      rw [len_addP, len_smulP, len_smulP]
    simp only [cloc, List.length_cons]
    omega

theorem len_mulP_le : ∀ a b : List ℤ, (mulP a b).length ≤ a.length + b.length
  | [], b => by simp [mulP]
  | x :: l, b => by
    have := len_mulP_le l b
    simp only [mulP, len_addP, len_smulP, List.length_cons]; omega

theorem len_cellN_le (P : List ℤ) (D : ℕ) (loN loD MN MD eN eD Q : ℤ) (c : CellData) :
    (cellN P D loN loD MN MD eN eD Q c).length ≤ P.length + 5 := by
  have h1 := len_cloc_le (cA loN loD Q c) (cB loD c) (cE loN loD Q) P 0 [1]
    [cA loN loD Q c, cB loD c] [] (by simp) (by simp)
  have h2 := len_mulP_le (cG P D loN loD MN MD eN eD Q c)
    [(2 * Q) ^ 2 + (c.u0 + c.u1) ^ 2, 2 * (c.u0 + c.u1) * (c.u1 - c.u0), (c.u1 - c.u0) ^ 2]
  have h3 : (cG P D loN loD MN MD eN eD Q c).length ≤ P.length + 1 := by
    simp only [cG, len_addP, len_smulP, List.length_singleton]
    unfold cLz
    simp at h1
    omega
  simp only [cellN, len_addP, len_smulP, List.length_cons, List.length_nil] at h2 ⊢
  omega

/-! ### The packed cell check -/

/-- Packed check of one cell with radix `X = 2^s + 51`. -/
def cellChkK (P : List ℤ) (D : ℕ) (loN loD MN MD eN eD Q : ℤ) (c : CellData) (s : ℕ) : Bool :=
  decide (c.u0 < c.u1) &&
    (decide (2 * nBound P D loN loD MN MD eN eD Q c < 2 ^ s + 51) &&
      chkL (dec (2 ^ s + 51) (P.length + 5) (packN P D loN loD MN MD eN eD Q c (2 ^ s + 51))))

theorem cellChkK_sound {P : List ℤ} {D : ℕ} {loN loD MN MD eN eD Q : ℤ} {c : CellData} {s : ℕ}
    (h : cellChkK P D loN loD MN MD eN eD Q c s = true) :
    cellChk P D loN loD MN MD eN eD Q c = true := by
  simp only [cellChkK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hlt, hb, hc⟩ := h
  have hX : (0 : ℤ) < 2 ^ s + 51 := by positivity
  have hent : ∀ a ∈ cellN P D loN loD MN MD eN eD Q c, 2 * |a| < 2 ^ s + 51 := by
    intro a ha
    have h1 := abs_le_l1' _ a ha
    have h2 := l1_cellN_le P D loN loD MN MD eN eD Q c
    linarith
  have hd := dec_pk hX (cellN P D loN loD MN MD eN eD Q c) (P.length + 5)
    (len_cellN_le P D loN loD MN MD eN eD Q c) hent
  rw [← pk_cellN P D loN loD MN MD eN eD Q c (2 ^ s + 51), hd, chkL_pad] at hc
  simp only [cellChk, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨hlt, by simpa [chkL] using hc⟩

theorem all_cons_K {P : List ℤ} {D : ℕ} {loN loD MN MD eN eD Q : ℤ} {c : CellData} {s : ℕ}
    {rest : List CellData} (h : cellChkK P D loN loD MN MD eN eD Q c s = true)
    (hr : rest.all (cellChk P D loN loD MN MD eN eD Q) = true) :
    (c :: rest).all (cellChk P D loN loD MN MD eN eD Q) = true := by
  simp [List.all_cons, cellChkK_sound h, hr]

end CatalanMeasure.GenD.Signed.RouteI.CompactCellsB

#print axioms CatalanMeasure.GenD.Signed.RouteI.CompactCellsB.cellChkK_sound
#print axioms CatalanMeasure.GenD.Signed.RouteI.CompactCellsB.all_cons_K
