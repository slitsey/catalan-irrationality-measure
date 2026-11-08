module

public import CatalanCore.Uniform.Content.BankShared.KTerm.Bank

@[expose] public section
set_option Elab.async false

/-! # The period table of the prefix layer: cells, `PCell.ok`, and the expansion pieces (wave H5a-closed)

For a `k`-shift bank with `α = a / b` in lowest terms the profile of the prefix layer on `θ ≤ 1 / b` is periodic in
`s = 1 / θ` with period `b`: `Φ(θ) = 2 + 2 α - θ Γ(1 / θ)` and `Γ(s + b) = Γ(s)` (the periodic closed form,
`THREE-TERM-CONTENT-2026-11-07.md`, Theorem P).  The table of one period is a list of **cells**
`PCell`: `Γ = g0 + g1 u` on `[u0, u1]` in the coordinate `u = s - b n'`, each inside one unit `[kc, kc + 1]`, with
the prefix offset `nu` (`⌊α u⌋ = nu` on the cell) and the attaining branch: `d1x` or the prefix window
`pre j0 j1 j2`.

`PCell.ok` is the n-free endpoint certificate: for every upper cut `h` and lower cut `l` of the window of the
branch (affine in `u`; `hiL`, `loL`) the line of the cell is below `h - l` at both ends, hence on the whole cell
(`ok_pair`).  `expPiece` is the `θ`-piece of the cell in the strip `n'`:
`(1 / (b n' + u1), 1 / (b n' + u0)]`, `Φ = (2 + 2 α - g1) + (b n' g1 - g0) θ`; `expList` lists the strips
`n' = N, …, 1` (increasing `θ`) given the cells in increasing `θ`.  `PieceBasic` is the part of `pieceOK`
(`K0`) that the chain machinery uses; `expPiece_basic` proves it for every expansion piece. -/

namespace CatalanCore.Uniform.Content.BankShared.KTerm
open CatalanCore.Uniform.Content.BankShared.Check

/-- The branch attaining `Γ` on a cell. -/
inductive CellBr where
  | d1x : CellBr
  | pre (j0 j1 j2 : ℕ) : CellBr

/-- A cell of the period table. -/
structure PCell where
  u0 : ℚ
  u1 : ℚ
  kc : ℕ
  nu : ℕ
  g0 : ℚ
  g1 : ℚ
  br : CellBr

/-- The value `l₀ + l₁ u` of an affine form. -/
def lnEval (l : ℚ × ℚ) (u : ℚ) : ℚ := l.1 + l.2 * u

/-- Upper cuts of the window of the cell, as affine forms in `u` (units of `p`, origin `p ⌊r / p⌋`). -/
def PCell.hiL (α κ0 κ1 : ℚ) (c : PCell) : List (ℚ × ℚ) :=
  match c.br with
  | .d1x => [(-(c.nu : ℚ), α), ((c.nu : ℚ) + 1, -α)]
  | .pre j0 j1 j2 =>
    [(-(c.kc : ℚ) - 2 * (c.nu : ℚ), 1 + 2 * α), (1 - (c.kc : ℚ), 1), ((j0 : ℚ) + 1, 0),
      (κ0 + (j1 : ℚ), 0), (κ1 + (j2 : ℚ), 0)]

/-- Lower cuts of the window of the cell. -/
def PCell.loL (α κ0 κ1 : ℚ) (c : PCell) : List (ℚ × ℚ) :=
  match c.br with
  | .d1x => [((0 : ℚ), (0 : ℚ))]
  | .pre j0 j1 j2 =>
    [(-(c.kc : ℚ) - 2 * (c.nu : ℚ) - 1, 1 + 2 * α), (-(c.kc : ℚ), 1), ((j0 : ℚ), 0),
      if j1 = 0 then (-(c.kc : ℚ), 1) else (κ0 + (j1 : ℚ) - 1, 0),
      if j2 = 0 then (-(c.kc : ℚ), 1) else (κ1 + (j2 : ℚ) - 1, 0)]

/-- **The endpoint certificate of a cell** (`κ0`, `κ1` the pole positions `j_i / q_i` of the class). -/
def PCell.ok (α κ0 κ1 : ℚ) (c : PCell) : Bool :=
  decide (c.u0 < c.u1) && decide ((c.kc : ℚ) ≤ c.u0) && decide (c.u1 ≤ (c.kc : ℚ) + 1) &&
    decide ((c.nu : ℚ) ≤ α * c.u0) && decide (α * c.u1 ≤ (c.nu : ℚ) + 1) &&
    (c.hiL α κ0 κ1).all (fun h => (c.loL α κ0 κ1).all (fun l =>
      decide (c.g0 + c.g1 * c.u0 ≤ lnEval h c.u0 - lnEval l c.u0) &&
      decide (c.g0 + c.g1 * c.u1 ≤ lnEval h c.u1 - lnEval l c.u1)))

theorem PCell.ok_spec {α κ0 κ1 : ℚ} {c : PCell} (h : c.ok α κ0 κ1 = true) :
    c.u0 < c.u1 ∧ (c.kc : ℚ) ≤ c.u0 ∧ c.u1 ≤ (c.kc : ℚ) + 1 ∧ (c.nu : ℚ) ≤ α * c.u0 ∧
      α * c.u1 ≤ (c.nu : ℚ) + 1 ∧
      ∀ hh ∈ c.hiL α κ0 κ1, ∀ ll ∈ c.loL α κ0 κ1,
        c.g0 + c.g1 * c.u0 ≤ lnEval hh c.u0 - lnEval ll c.u0 ∧
          c.g0 + c.g1 * c.u1 ≤ lnEval hh c.u1 - lnEval ll c.u1 := by
  simp only [PCell.ok, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  refine ⟨h1, h2, h3, h4, h5, fun hh hhm ll llm => ?_⟩
  have := h6 hh hhm ll llm
  simpa only [Bool.and_eq_true, decide_eq_true_eq] using this

/-- An affine function nonnegative at both ends of an interval is nonnegative on it. -/
theorem pair_between {g0 g1 h0 h1 l0 l1 u0 u1 u : ℚ} (hu0 : u0 ≤ u) (hu1 : u ≤ u1)
    (e0 : g0 + g1 * u0 ≤ (h0 + h1 * u0) - (l0 + l1 * u0))
    (e1 : g0 + g1 * u1 ≤ (h0 + h1 * u1) - (l0 + l1 * u1)) :
    g0 + g1 * u ≤ (h0 + h1 * u) - (l0 + l1 * u) := by
  rcases le_total 0 (h1 - l1 - g1) with hB | hB
  · nlinarith [mul_nonneg hB (sub_nonneg.2 hu0)]
  · nlinarith [mul_nonneg (neg_nonneg.2 hB) (sub_nonneg.2 hu1)]

/-- **A certified cell lies below every window gap** on its whole interval. -/
theorem PCell.ok_pair {α κ0 κ1 : ℚ} {c : PCell} (h : c.ok α κ0 κ1 = true) {u : ℚ} (hu0 : c.u0 ≤ u)
    (hu1 : u ≤ c.u1) {hh ll : ℚ × ℚ} (hhm : hh ∈ c.hiL α κ0 κ1) (llm : ll ∈ c.loL α κ0 κ1) :
    c.g0 + c.g1 * u ≤ lnEval hh u - lnEval ll u := by
  obtain ⟨-, -, -, -, -, hp⟩ := c.ok_spec h
  obtain ⟨e0, e1⟩ := hp hh hhm ll llm
  exact pair_between hu0 hu1 e0 e1

/-- The line of a cell lies below `2 α u`. -/
theorem PCell.line_le {α κ0 κ1 : ℚ} {c : PCell} (h : c.ok α κ0 κ1 = true) (hα : 0 ≤ α) {u : ℚ}
    (hu0 : c.u0 ≤ u) (hu1 : u ≤ c.u1) : c.g0 + c.g1 * u ≤ 2 * α * u := by
  obtain ⟨-, hk, -, -, -, -⟩ := c.ok_spec h
  have hkc : (0 : ℚ) ≤ c.kc := Nat.cast_nonneg _
  have hnu : (0 : ℚ) ≤ c.nu := Nat.cast_nonneg _
  have hu : 0 ≤ u := by linarith
  have hαu : 0 ≤ α * u := mul_nonneg hα hu
  rcases hbr : c.br with _ | ⟨j0, j1, j2⟩
  · have := c.ok_pair h hu0 hu1 (hh := (-(c.nu : ℚ), α)) (ll := ((0 : ℚ), (0 : ℚ)))
      (by simp [PCell.hiL, hbr]) (by simp [PCell.loL, hbr])
    simp only [lnEval] at this
    nlinarith
  · have := c.ok_pair h hu0 hu1 (hh := (-(c.kc : ℚ) - 2 * (c.nu : ℚ), 1 + 2 * α))
      (ll := (-(c.kc : ℚ), 1)) (by simp [PCell.hiL, hbr]) (by simp [PCell.loL, hbr])
    simp only [lnEval] at this
    nlinarith

/-! ### Expansion pieces -/

/-- The part of `pieceOK` (K0) used by the chain machinery. -/
def PieceBasic (x : QPiece) : Prop :=
  0 < x.s ∧ x.s < x.t ∧ 0 ≤ x.C ∧ 0 ≤ x.a + x.b * x.s ∧ 0 ≤ x.a + x.b * x.t

/-- The `θ`-piece of the cell `c` in the strip `n'` (slack `C`). -/
def expPiece (α : ℚ) (b : ℕ) (C : ℚ) (n' : ℕ) (c : PCell) : QPiece :=
  ⟨1 / ((b : ℚ) * n' + c.u1), 1 / ((b : ℚ) * n' + c.u0), 2 + 2 * α - c.g1, (b : ℚ) * n' * c.g1 - c.g0, C⟩

/-- The strips `n' = N, …, 1` (increasing `θ`) of the cells (given in increasing `θ`). -/
def expList (α : ℚ) (b : ℕ) (C : ℚ) (N : ℕ) (cells : List PCell) : List QPiece :=
  (List.range N).reverse.flatMap (fun i => cells.map (expPiece α b C (i + 1)))

theorem mem_expList {α : ℚ} {b : ℕ} {C : ℚ} {N : ℕ} {cells : List PCell} {x : QPiece}
    (h : x ∈ expList α b C N cells) :
    ∃ n' c, 1 ≤ n' ∧ n' ≤ N ∧ c ∈ cells ∧ x = expPiece α b C n' c := by
  simp only [expList, List.mem_flatMap, List.mem_reverse, List.mem_range, List.mem_map] at h
  obtain ⟨i, hi, c, hc, rfl⟩ := h
  exact ⟨i + 1, c, by omega, by omega, hc, rfl⟩

/-- The line of an expansion piece at `θ = 1 / (b n' + u)` is `2 + 2 α - θ (g0 + g1 u)`, nonnegative. -/
theorem exp_line_nonneg {α : ℚ} (hα : 0 ≤ α) {b n' : ℕ} (hb : 1 ≤ b) (hn : 1 ≤ n') {κ0 κ1 : ℚ}
    {c : PCell} (hc : c.ok α κ0 κ1 = true) {u : ℚ} (hu0 : c.u0 ≤ u) (hu1 : u ≤ c.u1) :
    0 ≤ (2 + 2 * α - c.g1) + ((b : ℚ) * n' * c.g1 - c.g0) * (1 / ((b : ℚ) * n' + u)) := by
  obtain ⟨-, hk, -, -, -, -⟩ := c.ok_spec hc
  have hkc : (0 : ℚ) ≤ c.kc := Nat.cast_nonneg _
  have hu : 0 ≤ u := by linarith
  have hbn : (1 : ℚ) ≤ (b : ℚ) * n' := by
    have h1 : (1 : ℚ) ≤ b := by exact_mod_cast hb
    have h2 : (1 : ℚ) ≤ n' := by exact_mod_cast hn
    nlinarith
  have hD : 0 < (b : ℚ) * n' + u := by linarith
  have hl := c.line_le hc hα hu0 hu1
  have e : (2 + 2 * α - c.g1) + ((b : ℚ) * n' * c.g1 - c.g0) * (1 / ((b : ℚ) * n' + u)) =
      ((2 + 2 * α) * ((b : ℚ) * n' + u) - (c.g0 + c.g1 * u)) / ((b : ℚ) * n' + u) := by
    field_simp
    ring
  rw [e]
  apply div_nonneg _ hD.le
  nlinarith

/-- **Every expansion piece satisfies (K0)** (positivity, order, nonnegative line at both ends). -/
theorem expPiece_basic {α : ℚ} (hα : 0 ≤ α) {b n' : ℕ} (hb : 1 ≤ b) (hn : 1 ≤ n') {κ0 κ1 : ℚ} {c : PCell}
    (hc : c.ok α κ0 κ1 = true) {C : ℚ} (hC : 0 ≤ C) : PieceBasic (expPiece α b C n' c) := by
  obtain ⟨hlt, hk, -, -, -, -⟩ := c.ok_spec hc
  have hkc : (0 : ℚ) ≤ c.kc := Nat.cast_nonneg _
  have hbn : (1 : ℚ) ≤ (b : ℚ) * n' := by
    have h1 : (1 : ℚ) ≤ b := by exact_mod_cast hb
    have h2 : (1 : ℚ) ≤ n' := by exact_mod_cast hn
    nlinarith
  have h0 : 0 < (b : ℚ) * n' + c.u0 := by linarith
  have h1 : 0 < (b : ℚ) * n' + c.u1 := by linarith
  refine ⟨?_, ?_, hC, ?_, ?_⟩
  · show 0 < 1 / ((b : ℚ) * n' + c.u1)
    positivity
  · show 1 / ((b : ℚ) * n' + c.u1) < 1 / ((b : ℚ) * n' + c.u0)
    exact one_div_lt_one_div_of_lt h0 (by linarith)
  · exact exp_line_nonneg hα hb hn hc hlt.le le_rfl
  · exact exp_line_nonneg hα hb hn hc le_rfl hlt.le

end CatalanCore.Uniform.Content.BankShared.KTerm
#print axioms CatalanCore.Uniform.Content.BankShared.KTerm.PCell.ok_pair
#print axioms CatalanCore.Uniform.Content.BankShared.KTerm.PCell.line_le
#print axioms CatalanCore.Uniform.Content.BankShared.KTerm.mem_expList
#print axioms CatalanCore.Uniform.Content.BankShared.KTerm.expPiece_basic
