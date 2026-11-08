module

public import CatalanMeasure.GenD.Signed.LogEval
public import CatalanMeasure.GenD.Signed.RouteI.Theorem296
public import CatalanMeasure.GenD.Signed.RouteI.Pay
public import CatalanMeasure.GenD.Signed.RouteI.SigmaC
public import CatalanMeasure.GenD.Signed.RouteI.IntervalNodesData
public import CatalanMeasure.GenD.Signed.RouteI.ChordTableData
public import CatalanMeasure.GenD.Signed.Count.LedgerContent
public import CatalanMeasure.GenD.Signed.Count.WinCertGlue
public import CatalanMeasure.GenD.Signed.RouteI.Family
public import CatalanMeasure.GenD.Signed.RouteI.T4Instance
public import CatalanMeasure.GenD.Signed.RouteI.UnsignedInstance

@[expose] public section

set_option Elab.async false

/-!
# Route I terminal assembly, parametric (design C, `μ(G) ≤ 270`)

The data certificates of the terminal enter as hypotheses in the exact type of their producers; this
module proves `measure_270` from them.

* weights: `hweights_d` (from `IntervalNodes.hweights_tauI` with (hcirc), (hseg) as hypotheses and
  `ChordTableData.neg_L_le_table`), `hw_d` (`ψ` clause), `hC0_d`, `hsupport_d`, `hG_d`;
* sheets: `firstSheet_of_pieces`, `largeSheet_of_pieces`, `nearSheet_of_cells` turn the piece checks
  (`T4Instance.wV_cells`, `sig_cells1/2`, `phys_cells`) and record skeletons into `FreeFirstBoundZ`,
  `FreeLargeBoundZ`, `FreeNearBoundZ`; `cmp_on_cell`, `low_on_cell` are `selected_comparison`,
  `selected_low_or_pick` on one cell;
* `measure_of_sheets`, `measure_of_data`, `measure_270`: the terminal.
-/
namespace CatalanMeasure.GenD.Signed.RouteI.TerminalC

open Filter Set CatalanMeasure.GenD CatalanMeasure.GenD.Analytic CatalanMeasure.Parametric
open CatalanMeasure.GenD.Signed.RouteI CatalanMeasure.GenD.Signed.RouteI.Family
open OAI.InternalCatalan

noncomputable section

/-- The uniform partition of `[A, B]` into `n` cells covers `[A, B]`. -/
theorem cells_cover {A B : ℝ} (hAB : A < B) {n : ℕ} (hn : 0 < n) {α : ℝ} (hα : α ∈ Icc A B) :
    ∃ i : ℕ, i < n ∧ α ∈ Icc (A + (B - A) * i / n) (A + (B - A) * (i + 1) / n) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  set h : ℝ := (B - A) / n with hh
  have hhpos : 0 < h := div_pos (by linarith) hnR
  set i : ℕ := min (⌊(α - A) / h⌋₊) (n - 1) with hi
  have hin : i < n := by
    have : min (⌊(α - A) / h⌋₊) (n - 1) ≤ n - 1 := min_le_right _ _
    omega
  have e0 : A + (B - A) * (i : ℝ) / n = A + h * i := by rw [hh]; ring
  have e2 : A + (B - A) * ((i : ℝ) + 1) / n = A + h * ((i : ℝ) + 1) := by rw [hh]; ring
  have hx0 : 0 ≤ (α - A) / h := div_nonneg (by linarith [hα.1]) hhpos.le
  have hxn : (α - A) / h ≤ n := by
    rw [div_le_iff₀ hhpos, hh]
    field_simp
    linarith [hα.2]
  have hlo : (i : ℝ) ≤ (α - A) / h :=
    (Nat.cast_le.mpr (min_le_left _ _)).trans (Nat.floor_le hx0)
  have hhi : (α - A) / h ≤ i + 1 := by
    by_cases hc : ⌊(α - A) / h⌋₊ ≤ n - 1
    · have : i = ⌊(α - A) / h⌋₊ := min_eq_left hc
      rw [this]
      exact (Nat.lt_floor_add_one _).le
    · have : i = n - 1 := min_eq_right (by omega)
      rw [this]
      have : ((n - 1 : ℕ) : ℝ) = n - 1 := by rw [Nat.cast_sub (by omega)]; simp
      rw [this]
      linarith [hxn]
  have hlo' : h * i ≤ α - A := by
    rw [le_div_iff₀ hhpos] at hlo
    linarith
  have hhi' : α - A ≤ h * (i + 1) := by
    rw [div_le_iff₀ hhpos] at hhi
    linarith
  exact ⟨i, hin, by rw [e0, e2]; exact ⟨by linarith, by linarith⟩⟩

theorem cell_sub {A B : ℝ} {n i : ℕ} (hi : i < n) (hn : 0 < n) (hAB : A ≤ B) :
    Icc (A + (B - A) * i / n) (A + (B - A) * (i + 1) / n) ⊆ Icc A B := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hi' : (i : ℝ) + 1 ≤ n := by exact_mod_cast hi
  intro α hα
  constructor
  · have : 0 ≤ (B - A) * i / n := by positivity
    linarith [hα.1]
  · have : (B - A) * ((i : ℝ) + 1) / n ≤ B - A := by
      rw [div_le_iff₀ hnR]; nlinarith
    linarith [hα.2]

theorem first_of_cells_fintype {P : Parameters} (hP : Admissible P) {ζ : ℝ} (hζ : 0 ≤ ζ)
    {δ : ℝ → ℝ} {G : ℝ → Prop} {target c : ℝ} {ι : Type} [Fintype ι]
    (W : ι → Set ℝ) (γ : ι → ℝ)
    (hcov : ∀ α ∈ Icc (0 : ℝ) 1, ∃ i, α ∈ W i) (hWγ : ∀ i, ∀ α ∈ W i, α ≤ γ i)
    (hrec : ∀ i, Nonempty (FirstTrialBoundsEnd P (W i) (colCell P ζ (γ i)) (nodeD P δ) G target c)) :
    FreeFirstBoundZ P G ζ δ target ((P.n0 : ℝ) * c) := by
  let e := Fintype.equivFin ι
  refine first_of_cells hP hζ (fun ε _ => ⟨Fintype.card ι, fun j => W (e.symm j), fun j => γ (e.symm j),
    fun _ => target, ?_, fun j => hWγ _, fun _ => by linarith, fun j => hrec _⟩)
  intro α hα
  obtain ⟨i, hi⟩ := hcov α hα
  exact ⟨e i, by simpa using hi⟩

theorem large_of_cells_fintype {P : Parameters} (hP : Admissible P) {ζ : ℝ} (hζ : 0 ≤ ζ)
    {δ : ℝ → ℝ} {G : ℝ → Prop} {target c' α₁ : ℝ} {ι : Type} [Fintype ι]
    (W : ι → Set ℝ) (γ residual nearCap : ι → ℝ)
    (hcov : ∀ α ∈ Icc α₁ 1, ∃ i, α ∈ W i) (hWγ : ∀ i, ∀ α ∈ W i, α ≤ γ i)
    (hrec : ∀ i, Nonempty (SecondTrialBoundsEnd P (W i) (colCell P ζ (γ i)) (nodeD P δ) target
      (residual i) (nearCap i) c' G)) :
    FreeLargeBoundZ P G ζ δ target ((P.n0 : ℝ) * c') α₁ := by
  let e := Fintype.equivFin ι
  refine large_of_cells hP hζ (fun ε _ => ⟨Fintype.card ι, fun j => W (e.symm j), fun j => γ (e.symm j),
    fun _ => target, fun j => residual (e.symm j), fun j => nearCap (e.symm j), ?_, fun j => hWγ _,
    fun _ => by linarith, fun j => hrec _⟩)
  intro α hα
  obtain ⟨i, hi⟩ := hcov α hα
  exact ⟨e i, by simpa using hi⟩

open CatalanMeasure.GenD.Signed.RouteI.T4Instance CatalanMeasure.GenD.D58 CatalanMeasure.GenD.Signed.RouteI.CompletedGas

/-- Change the window of a first-case record, with a new budget. -/
def reWindowFirst {P : Parameters} {W0 : Set ℝ} {Cf : ℕ → ℝ → ℝ} {d : ℝ → ℝ} {G : ℝ → Prop}
    {t c : ℝ} (D : FirstTrialBoundsEnd P W0 Cf d G t c) (W : Set ℝ)
    (hb : ∀ a ∈ W, (-gC0 P + gC1 P * a - a ^ 2) * Real.log 2 + D.normCap + (1 - a) * D.fieldCap +
      a * D.M₁ ≤ -t + Real.log 2 / 2 + c * a) : FirstTrialBoundsEnd P W Cf d G t c where
  p := D.p
  v := D.v
  lambda := D.lambda
  MX := D.MX
  MY := D.MY
  normCap := D.normCap
  fieldCap := D.fieldCap
  M₁ := D.M₁
  lambda_nonneg := D.lambda_nonneg
  p_summable := D.p_summable
  v_summable := D.v_summable
  norm_le := D.norm_le
  field_sum := D.field_sum
  row := D.row
  marked := D.marked
  column := D.column
  budget := hb

/-- **The first sheet from the piece checks** (GP §9(e), Theorem 8.3 first case).  On each piece
`[A k, B k]` of `[0, 1]` the check `σ α + 0 - η - wV ≥ 0` of `wPq` (with `np = rs`), and for every cell
end `β` of the piece a record skeleton (window `∅`, column field `colCell P ζ β`) whose caps are
below the piece polynomials at `β`. -/
theorem firstSheet_of_pieces {P : Parameters} (hP : Admissible P) (hg0 : gC0 P = 6 / 29)
    (hg1 : gC1 P = 47 / 29) {ζ : ℝ} (hζ : 0 ≤ ζ) {δ : ℝ → ℝ} {G : ℝ → Prop} {σ η : ℚ} (hη : 0 < η)
    {κ : ℕ} (A B : Fin κ → ℚ) (hA0 : ∀ k, 0 ≤ A k) (hB1 : ∀ k, B k ≤ 1) (hAB : ∀ k, A k < B k)
    (hcov : ∀ α ∈ Icc (0 : ℝ) 1, ∃ k, (A k : ℝ) ≤ α ∧ α ≤ B k)
    (nC fC rs : Fin κ → QP)
    (hPoly : ∀ k, PolyNonneg (wPq σ η 0 (nC k) (fC k) (rs k) (rs k)) (A k) (B k))
    (R : ∀ k, ∀ β ∈ Icc (A k : ℝ) (B k),
      FirstTrialBoundsEnd P ∅ (colCell P ζ β) (nodeD P δ) G (tQ : ℝ) ((c2Q : ℝ) + σ))
    (hN : ∀ k β hβ, (R k β hβ).normCap ≤ evalQ (nC k) β)
    (hF : ∀ k β hβ, (R k β hβ).fieldCap ≤ evalQ (fC k) β)
    (hM : ∀ k β hβ, (R k β hβ).M₁ ≤ evalQ (rs k) β) :
    FreeFirstBoundZ P G ζ δ (tQ : ℝ) ((P.n0 : ℝ) * ((c2Q : ℝ) + σ)) := by
  have hlo := Real.log_two_gt_d9
  choose n hn hcell using fun k => wV_cells (hAB k) hη (hPoly k)
  let ι := Σ k : Fin κ, Fin (n k)
  let lo : ι → ℝ := fun j => (A j.1 : ℝ) + ((B j.1 : ℝ) - A j.1) * (j.2 : ℕ) / n j.1
  let hi : ι → ℝ := fun j => (A j.1 : ℝ) + ((B j.1 : ℝ) - A j.1) * ((j.2 : ℕ) + 1) / n j.1
  have hAB' : ∀ k, (A k : ℝ) < B k := fun k => by exact_mod_cast hAB k
  have hlh : ∀ j : ι, lo j ≤ hi j := fun j => by
    have hnR : (0 : ℝ) < n j.1 := by exact_mod_cast hn j.1
    have : 0 ≤ ((B j.1 : ℝ) - A j.1) / n j.1 := div_nonneg (by linarith [hAB' j.1]) hnR.le
    simp only [lo, hi]
    have e : (A j.1 : ℝ) + ((B j.1 : ℝ) - A j.1) * ((j.2 : ℕ) + 1) / n j.1 =
        ((A j.1 : ℝ) + ((B j.1 : ℝ) - A j.1) * (j.2 : ℕ) / n j.1) + ((B j.1 : ℝ) - A j.1) / n j.1 := by
      field_simp; ring
    rw [e]; linarith
  have hsub : ∀ j : ι, Icc (lo j) (hi j) ⊆ Icc (A j.1 : ℝ) (B j.1) := fun j =>
    cell_sub j.2.2 (hn j.1) (hAB' j.1).le
  have hhi : ∀ j : ι, hi j ∈ Icc (A j.1 : ℝ) (B j.1) := fun j => hsub j ⟨hlh j, le_rfl⟩
  refine first_of_cells_fintype hP hζ (ι := ι) (fun j => Icc (lo j) (hi j)) hi ?_ (fun j α hα => hα.2) ?_
  · intro α hα
    obtain ⟨k, hk1, hk2⟩ := hcov α hα
    obtain ⟨i, hi', hmem⟩ := cells_cover (hAB' k) (hn k) ⟨hk1, hk2⟩
    exact ⟨⟨k, ⟨i, hi'⟩⟩, hmem⟩
  · intro j
    refine ⟨reWindowFirst (R j.1 (hi j) (hhi j)) (Icc (lo j) (hi j)) ?_⟩
    intro a ha
    have haa := hsub j ha
    have ha0 : 0 ≤ a := le_trans (by exact_mod_cast hA0 j.1) haa.1
    have ha1 : a ≤ 1 := le_trans haa.2 (by exact_mod_cast hB1 j.1)
    have hV := hcell j.1 j.2 j.2.2 a ha
    have hV' : wV (evalQ (nC j.1) (hi j)) (evalQ (fC j.1) (hi j)) (evalQ (rs j.1) (hi j))
        (evalQ (rs j.1) (hi j)) a ≤ σ * a + 0 := by simpa using hV
    have hb := first_budget_of_wV (P := P) hg0 hg1 (ℓ := Real.log 2)
      (by have := Real.log_two_gt_d9; norm_num [loQ] at this ⊢; linarith) hV'
    have h1 := hN j.1 (hi j) (hhi j)
    have h2 := hF j.1 (hi j) (hhi j)
    have h3 := hM j.1 (hi j) (hhi j)
    have e1 : (1 - a) * (R j.1 (hi j) (hhi j)).fieldCap ≤ (1 - a) * evalQ (fC j.1) (hi j) :=
      mul_le_mul_of_nonneg_left h2 (by linarith)
    have e2 : a * (R j.1 (hi j) (hhi j)).M₁ ≤ a * evalQ (rs j.1) (hi j) :=
      mul_le_mul_of_nonneg_left h3 ha0
    show (-gC0 P + gC1 P * a - a ^ 2) * Real.log 2 + (R j.1 (hi j) (hhi j)).normCap +
      (1 - a) * (R j.1 (hi j) (hhi j)).fieldCap + a * (R j.1 (hi j) (hhi j)).M₁ ≤ _
    linarith

/-- Change the window of a second-case record, with a new budget. -/
def reWindowSecond {P : Parameters} {W0 : Set ℝ} {Cf : ℕ → ℝ → ℝ} {d : ℝ → ℝ} {G : ℝ → Prop}
    {t r nr c : ℝ} (D : SecondTrialBoundsEnd P W0 Cf d t r nr c G) (W : Set ℝ)
    (hb : ∀ {a s : ℝ}, a ∈ W → 0 ≤ a → 0 ≤ s →
      (-gC0 P + gC1 P * a - a ^ 2 + s - s ^ 2) * Real.log 2 + D.normCap + (1 - a) * D.fieldCap +
        (a - s) * r + s * nr ≤ -t + Real.log 2 / 2 + c * a) :
    SecondTrialBoundsEnd P W Cf d t r nr c G where
  p := D.p
  v := D.v
  MX := D.MX
  MY := D.MY
  normCap := D.normCap
  fieldCap := D.fieldCap
  p_summable := D.p_summable
  v_summable := D.v_summable
  norm_le := D.norm_le
  field_sum := D.field_sum
  row := D.row
  column := D.column
  marked := D.marked
  near := D.near
  budget := hb

/-- **The large sheet from the piece checks** (GP §9(b), Theorem 8.3 second case).  Pieces
`[A k, B k] ⊂ [α₁, 1]`, the check of `wPq` with `Δ = 0`, and for every cell end `β` a record skeleton
with residual `rs(β)` and near cap `np(β) - log 2` and caps below the piece polynomials. -/
theorem largeSheet_of_pieces {P : Parameters} (hP : Admissible P) (hg0 : gC0 P = 6 / 29)
    (hg1 : gC1 P = 47 / 29) {ζ : ℝ} (hζ : 0 ≤ ζ) {δ : ℝ → ℝ} {G : ℝ → Prop} {σ η : ℚ} (hη : 0 < η)
    {α₁ : ℝ} (hα₁ : 0 ≤ α₁) {κ : ℕ} (A B : Fin κ → ℚ) (hA0 : ∀ k, α₁ ≤ A k) (hB1 : ∀ k, B k ≤ 1)
    (hAB : ∀ k, A k < B k) (hcov : ∀ α ∈ Icc α₁ 1, ∃ k, (A k : ℝ) ≤ α ∧ α ≤ B k)
    (nC fC rs np : Fin κ → QP)
    (hPoly : ∀ k, PolyNonneg (wPq σ η 0 (nC k) (fC k) (rs k) (np k)) (A k) (B k))
    (R : ∀ k, ∀ β ∈ Icc (A k : ℝ) (B k),
      SecondTrialBoundsEnd P ∅ (colCell P ζ β) (nodeD P δ) (tQ : ℝ) (evalQ (rs k) β)
        (evalQ (np k) β - Real.log 2) ((c2Q : ℝ) + σ) G)
    (hN : ∀ k β hβ, (R k β hβ).normCap ≤ evalQ (nC k) β)
    (hF : ∀ k β hβ, (R k β hβ).fieldCap ≤ evalQ (fC k) β) :
    FreeLargeBoundZ P G ζ δ (tQ : ℝ) ((P.n0 : ℝ) * ((c2Q : ℝ) + σ)) α₁ := by
  have hlo := Real.log_two_gt_d9
  choose n hn hcell using fun k => wV_cells (hAB k) hη (hPoly k)
  let ι := Σ k : Fin κ, Fin (n k)
  let lo : ι → ℝ := fun j => (A j.1 : ℝ) + ((B j.1 : ℝ) - A j.1) * (j.2 : ℕ) / n j.1
  let hi : ι → ℝ := fun j => (A j.1 : ℝ) + ((B j.1 : ℝ) - A j.1) * ((j.2 : ℕ) + 1) / n j.1
  have hAB' : ∀ k, (A k : ℝ) < B k := fun k => by exact_mod_cast hAB k
  have hlh : ∀ j : ι, lo j ≤ hi j := fun j => by
    have hnR : (0 : ℝ) < n j.1 := by exact_mod_cast hn j.1
    have : 0 ≤ ((B j.1 : ℝ) - A j.1) / n j.1 := div_nonneg (by linarith [hAB' j.1]) hnR.le
    simp only [lo, hi]
    have e : (A j.1 : ℝ) + ((B j.1 : ℝ) - A j.1) * ((j.2 : ℕ) + 1) / n j.1 =
        ((A j.1 : ℝ) + ((B j.1 : ℝ) - A j.1) * (j.2 : ℕ) / n j.1) + ((B j.1 : ℝ) - A j.1) / n j.1 := by
      field_simp; ring
    rw [e]; linarith
  have hsub : ∀ j : ι, Icc (lo j) (hi j) ⊆ Icc (A j.1 : ℝ) (B j.1) := fun j =>
    cell_sub j.2.2 (hn j.1) (hAB' j.1).le
  have hhi : ∀ j : ι, hi j ∈ Icc (A j.1 : ℝ) (B j.1) := fun j => hsub j ⟨hlh j, le_rfl⟩
  refine large_of_cells_fintype hP hζ (ι := ι) (fun j => Icc (lo j) (hi j)) hi
    (fun j => evalQ (rs j.1) (hi j)) (fun j => evalQ (np j.1) (hi j) - Real.log 2) ?_
    (fun j α hα => hα.2) ?_
  · intro α hα
    obtain ⟨k, hk1, hk2⟩ := hcov α hα
    obtain ⟨i, hi', hmem⟩ := cells_cover (hAB' k) (hn k) ⟨hk1, hk2⟩
    exact ⟨⟨k, ⟨i, hi'⟩⟩, hmem⟩
  · intro j
    refine ⟨reWindowSecond (R j.1 (hi j) (hhi j)) (Icc (lo j) (hi j)) ?_⟩
    intro a s ha ha0 hs0
    have haa := hsub j ha
    have ha1 : a ≤ 1 := le_trans haa.2 (by exact_mod_cast hB1 j.1)
    have hV := hcell j.1 j.2 j.2.2 a ha
    have hV' : wV (evalQ (nC j.1) (hi j)) (evalQ (fC j.1) (hi j)) (evalQ (rs j.1) (hi j))
        (evalQ (np j.1) (hi j)) a ≤ σ * a + 0 := by simpa using hV
    have hb := oldBound_budget_of_wV (P := P) hg0 hg1 (ℓ := Real.log 2) (β := s) rfl
      (by have := Real.log_two_gt_d9; norm_num [loQ] at this ⊢; linarith) hV'
    have h1 := hN j.1 (hi j) (hhi j)
    have h2 := hF j.1 (hi j) (hhi j)
    have e1 : (1 - a) * (R j.1 (hi j) (hhi j)).fieldCap ≤ (1 - a) * evalQ (fC j.1) (hi j) :=
      mul_le_mul_of_nonneg_left h2 (by linarith)
    unfold oldBound at hb
    show (-gC0 P + gC1 P * a - a ^ 2 + s - s ^ 2) * Real.log 2 + (R j.1 (hi j) (hhi j)).normCap +
      (1 - a) * (R j.1 (hi j) (hhi j)).fieldCap + (a - s) * evalQ (rs j.1) (hi j) +
        s * (evalQ (np j.1) (hi j) - Real.log 2) ≤ _
    linarith

open CatalanMeasure.GenD.Signed.RouteI.CompletedGas CatalanMeasure.GenD.Signed.RouteI.CapFields
open CatalanMeasure.GenD.Signed.RouteI.CapSourceData CatalanMeasure.GenD.Signed.RouteI.UnsignedInstance
open CatalanMeasure.GenD.Signed.PhysicalPick

/-- The moved row increment `−2 T(da⁰ + τ da¹) − S(dv⁰ + τ dv¹)` of the anchor. -/
def fRm (da0 da1 dv0 dv1 : ℕ → ℝ) (τ x : ℝ) : ℝ :=
  -(2 * barrierTrialT (fun k => da0 k + τ * da1 k) x) - barrierTrialS (fun k => dv0 k + τ * dv1 k) x

/-- The moved column increment `2 T(dv⁰ + τ dv¹)`. -/
def fCm (dv0 dv1 : ℕ → ℝ) (τ s : ℝ) : ℝ := 2 * barrierTrialT (fun k => dv0 k + τ * dv1 k) s

theorem finsupp_moment {w : ℕ → ℝ} {K : ℕ} (hw : ∀ k, K ≤ k → w k = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k, k ≠ 0 → |w k| ≤ C / k := by
  refine ⟨Finset.sum (Finset.range K) (fun j : ℕ => (j : ℝ) * |w j|), Finset.sum_nonneg fun j _ => by positivity,
    fun k hk => ?_⟩
  have hk0 : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
  rw [le_div_iff₀ hk0]
  by_cases hkK : k < K
  · have : (k : ℝ) * |w k| ≤ Finset.sum (Finset.range K) (fun j : ℕ => (j : ℝ) * |w j|) :=
      Finset.single_le_sum (f := fun j : ℕ => (j : ℝ) * |w j|) (fun j _ => by positivity)
        (Finset.mem_range.mpr hkK)
    linarith
  · rw [hw k (not_lt.mp hkK)]
    simp only [abs_zero, zero_mul]
    exact Finset.sum_nonneg fun j _ => by positivity

theorem T_add' {u w : ℕ → ℝ} {C Cw : ℝ} (hu : ∀ k, k ≠ 0 → |u k| ≤ C / k)
    (hw : ∀ k, k ≠ 0 → |w k| ≤ Cw / k) {x : ℝ} (hx : |x| ≤ 1) :
    barrierTrialT (fun k => u k + w k) x = barrierTrialT u x + barrierTrialT w x := by
  have hx' : x ∈ Icc (-1 : ℝ) 1 := abs_le.mp hx
  rw [barrierTrialT_eq, barrierTrialT_eq, barrierTrialT_eq, ← (termT_summable hu hx').tsum_add (termT_summable hw hx')]
  congr 1; ext n; unfold termT; ring

theorem S_add' {u w : ℕ → ℝ} {C Cw : ℝ} (hu : ∀ k, k ≠ 0 → |u k| ≤ C / k)
    (hw : ∀ k, k ≠ 0 → |w k| ≤ Cw / k) {x : ℝ} (hx : |x| ≤ 1) :
    barrierTrialS (fun k => u k + w k) x = barrierTrialS u x + barrierTrialS w x := by
  have hx' : x ∈ Icc (-1 : ℝ) 1 := abs_le.mp hx
  rw [barrierTrialS_eq, barrierTrialS_eq, barrierTrialS_eq, ← (termS_summable hu hx').tsum_add (termS_summable hw hx')]
  congr 1; ext n; unfold termS; ring

theorem fRm_affine {da0 da1 dv0 dv1 : ℕ → ℝ} {K : ℕ} (ha0 : ∀ k, K ≤ k → da0 k = 0)
    (ha1 : ∀ k, K ≤ k → da1 k = 0) (hv0 : ∀ k, K ≤ k → dv0 k = 0) (hv1 : ∀ k, K ≤ k → dv1 k = 0)
    (τ : ℝ) {x : ℝ} (hx : |x| ≤ 1) :
    fRm da0 da1 dv0 dv1 τ x = fRm da0 da1 dv0 dv1 0 x +
      τ * (fRm da0 da1 dv0 dv1 1 x - fRm da0 da1 dv0 dv1 0 x) := by
  have sa : Summable (fun k => |da0 k|) := summable_of_support ha0
  have sv : Summable (fun k => |dv0 k|) := summable_of_support hv0
  unfold fRm
  rw [barrierTrialT_shift da0 da1 τ sa ha1 hx, barrierTrialS_shift dv0 dv1 τ sv hv1 hx,
    barrierTrialT_shift da0 da1 1 sa ha1 hx, barrierTrialS_shift dv0 dv1 1 sv hv1 hx,
    barrierTrialT_shift da0 da1 0 sa ha1 hx, barrierTrialS_shift dv0 dv1 0 sv hv1 hx]
  ring

theorem fCm_affine {dv0 dv1 : ℕ → ℝ} {K : ℕ} (hv0 : ∀ k, K ≤ k → dv0 k = 0)
    (hv1 : ∀ k, K ≤ k → dv1 k = 0) (τ : ℝ) {s : ℝ} (hs : |s| ≤ 1) :
    fCm dv0 dv1 τ s = fCm dv0 dv1 0 s + τ * (fCm dv0 dv1 1 s - fCm dv0 dv1 0 s) := by
  have sv : Summable (fun k => |dv0 k|) := summable_of_support hv0
  unfold fCm
  rw [barrierTrialT_shift dv0 dv1 τ sv hv1 hs, barrierTrialT_shift dv0 dv1 1 sv hv1 hs,
    barrierTrialT_shift dv0 dv1 0 sv hv1 hs]
  ring

theorem hI_move (b : ℝ) {a v da0 da1 dv0 dv1 : ℕ → ℝ} {K : ℕ}
    (ha : Summable (fun k : ℕ => a (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)))
    (hv : Summable (fun k : ℕ => v (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)))
    (ha0 : ∀ k, K ≤ k → da0 k = 0) (ha1 : ∀ k, K ≤ k → da1 k = 0)
    (hv0 : ∀ k, K ≤ k → dv0 k = 0) (hv1 : ∀ k, K ≤ k → dv1 k = 0)
    {L0 L1 Q00 Q01 Q11 τ : ℝ} (hτ : 0 ≤ τ)
    (hL0 : 2 * barrierInner a da0 + barrierInner v dv0 ≤ L0)
    (hL1 : 2 * barrierInner a da1 + barrierInner v dv1 ≤ L1)
    (hQ00 : barrierInner da0 da0 + barrierInner dv0 dv0 / 2 ≤ Q00)
    (hQ01 : barrierInner da0 da1 + barrierInner dv0 dv1 / 2 ≤ Q01)
    (hQ11 : barrierInner da1 da1 + barrierInner dv1 dv1 / 2 ≤ Q11) :
    anchorIntercept b (fun k => a k + (da0 k + τ * da1 k)) (fun k => v k + (dv0 k + τ * dv1 k)) ≤
      anchorIntercept b a v + (L0 + Q00) + τ * (L1 + 2 * Q01) + τ ^ 2 * Q11 := by
  rw [anchorIntercept_move b ha hv ha0 ha1 hv0 hv1 τ]
  have h1 : τ * (2 * barrierInner a da1 + barrierInner v dv1 +
      2 * (barrierInner da0 da1 + barrierInner dv0 dv1 / 2)) ≤ τ * (L1 + 2 * Q01) :=
    mul_le_mul_of_nonneg_left (by linarith) hτ
  have h2 : τ ^ 2 * (barrierInner da1 da1 + barrierInner dv1 dv1 / 2) ≤ τ ^ 2 * Q11 :=
    mul_le_mul_of_nonneg_left hQ11 (sq_nonneg τ)
  linarith

/-- **The comparison bound on one signed cell** (GP §9(a), Theorem 8.3): `selected_comparison` at the
moved anchor `(aT + da⁰ + τ da¹, aV + dv⁰ + τ dv¹)` of the cell, from the E2 bounds, the chord caps
`r`, `c` and `sigV ≤ σ α` on the window. -/
theorem cmp_on_cell {P : Parameters} [Shape58 P] {d : ℝ → ℝ} {G : ℝ → Prop} {gasI : ℝ}
    {anchI : Fin 2 → ℝ} (B : capSource.CapBundle Trunc.exact d G gasI anchI)
    (hang : ∀ σ, B.angCap σ ≤ kappa σ) (hgas : gasConst capSource ≤ gasI)
    (hgasB : B.gasICap ≤ gasConst capSource) (hM : markCap B ≤ -976 / 1000)
    {da0 da1 dv0 dv1 : ℕ → ℝ} {K : ℕ} (ha0 : ∀ k, K ≤ k → da0 k = 0) (ha1 : ∀ k, K ≤ k → da1 k = 0)
    (hv0 : ∀ k, K ≤ k → dv0 k = 0) (hv1 : ∀ k, K ≤ k → dv1 k = 0)
    (l : SigLits) (hI1 : anchorVal 0 + gasConst capSource ≤ l.I1)
    (hL0 : 2 * barrierInner (aT capSource 0) da0 + barrierInner (aV capSource 0) dv0 ≤ l.L0)
    (hL1 : 2 * barrierInner (aT capSource 0) da1 + barrierInner (aV capSource 0) dv1 ≤ l.L1)
    (hQ00 : barrierInner da0 da0 + barrierInner dv0 dv0 / 2 ≤ l.Q00)
    (hQ01 : barrierInner da0 da1 + barrierInner dv0 dv1 / 2 ≤ l.Q01)
    (hQ11 : barrierInner da1 da1 + barrierInner dv1 dv1 / 2 ≤ l.Q11)
    {τ γ r c J ζ : ℝ} (hτ : 0 ≤ τ) (hζ : 0 ≤ ζ) (hγ0 : 0 ≤ γ)
    (hrc : ∀ x ∈ CapSource.rowDom, capSource.freeRow Trunc.exact 0 x + fRm da0 da1 dv0 dv1 τ x ≤ r)
    (hcc : ∀ s ∈ Ioo (0 : ℝ) 1, capSource.colField 0 s + fCm dv0 dv1 τ s +
      γ * Real.log (1 + ζ * s) ≤ c)
    (hJ : l.I1 + (l.L0 + l.Q00) + τ * (l.L1 + 2 * l.Q01) + τ ^ 2 * l.Q11 ≤ J)
    {W : Set ℝ} (hW0 : ∀ α ∈ W, 0 ≤ α) (hW1 : ∀ α ∈ W, α ≤ 51 / 500) (hWγ : ∀ α ∈ W, α ≤ γ)
    (hV : ∀ α ∈ W, sigV J r c α ≤ l.σ * α)
    {δ : ℝ → ℝ} (hdδ : ∀ u, d u = δ (realCoordinateInv u) / 58)
    (hG : ∀ y, G y → (0 < y → y ∈ CapSource.ordDom Sign.pos) ∧
      (y < 0 → -y ∈ CapSource.ordDom Sign.neg))
    {Q : ∀ (N p m : ℕ), (Fin p → ℝ) → (Fin m → ℝ) → (Fin p → ℝ) → Prop}
    (hQ : ∀ N p m x y s, Q N p m x y s → ((m : ℝ) / (P.n N : ℝ)) ∈ W) :
    SelectedComparisonOnPick P ζ δ (tQ : ℝ) (58 * ((c2Q : ℝ) + l.σ)) G Q := by
  obtain ⟨K0, hK0, hb0⟩ := anchor_moment_bound (ref_cell capSource_admissible 0) (colCell_capSource 0)
  have hA0 : ∀ k, k ≠ 0 → |aT capSource 0 k| ≤ K0 / k := fun k hk => (hb0 k hk).1
  have hV0 : ∀ k, k ≠ 0 → |aV capSource 0 k| ≤ K0 / k := fun k hk => (hb0 k hk).2
  have hwa : ∀ k, K ≤ k → da0 k + τ * da1 k = 0 := fun k hk => by simp [ha0 k hk, ha1 k hk]
  have hwv : ∀ k, K ≤ k → dv0 k + τ * dv1 k = 0 := fun k hk => by simp [hv0 k hk, hv1 k hk]
  obtain ⟨Ca, hCa0, hCa⟩ := finsupp_moment hwa
  obtain ⟨Cv, hCv0, hCv⟩ := finsupp_moment hwv
  have hmA : ∀ k, k ≠ 0 → |aT capSource 0 k + (da0 k + τ * da1 k)| ≤ (K0 + Ca + Cv) / k := by
    intro k hk
    have hk0 : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
    have := hA0 k hk; have := hCa k hk
    calc _ ≤ |aT capSource 0 k| + |da0 k + τ * da1 k| := abs_add_le _ _
      _ ≤ K0 / k + Ca / k := add_le_add (hA0 k hk) (hCa k hk)
      _ ≤ _ := by
        rw [← add_div]
        exact div_le_div_of_nonneg_right (by linarith) hk0.le
  have hmV : ∀ k, k ≠ 0 → |aV capSource 0 k + (dv0 k + τ * dv1 k)| ≤ (K0 + Ca + Cv) / k := by
    intro k hk
    have hk0 : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
    calc _ ≤ |aV capSource 0 k| + |dv0 k + τ * dv1 k| := abs_add_le _ _
      _ ≤ K0 / k + Cv / k := add_le_add (hV0 k hk) (hCv k hk)
      _ ≤ _ := by
        rw [← add_div]
        exact div_le_div_of_nonneg_right (by linarith) hk0.le
  have sTa := (summable_of_moment_bound hA0).1
  have sTv := (summable_of_moment_bound hV0).1
  refine selected_comparison capSource_admissible foldSeed_capSource colCell_capSource B hang hgas 0
    (A := fun k => aT capSource 0 k + (da0 k + τ * da1 k))
    (V := fun k => aV capSource 0 k + (dv0 k + τ * dv1 k))
    (fR := fRm da0 da1 dv0 dv1 τ) (fC := fCm dv0 dv1 τ) (K := K0 + Ca + Cv) hmA hmV ?_ ?_ ?_ ?_
    hζ hγ0 hrc hcc (I := anchorIntercept (aB capSource 0) (fun k => aT capSource 0 k + (da0 k + τ * da1 k))
      (fun k => aV capSource 0 k + (dv0 k + τ * dv1 k))) le_rfl hWγ ?_ hdδ hG hQ
  · intro x hx hx0
    have hx1 : |x| ≤ 1 := abs_le.mpr ⟨hx.1.le, hx.2.le⟩
    unfold anchorRowField fRm
    rw [T_add' hA0 hCa hx1, S_add' hV0 hCv hx1]
    ring
  · intro s hs
    have hs1 : |s| ≤ 1 := abs_le.mpr ⟨hs.1.le.trans' (by linarith [hs.1]) , hs.2.le⟩
    unfold anchorColumnField fCm
    rw [T_add' hV0 hCv hs1]
    ring
  · obtain ⟨Ma, -, hMa⟩ := trial_bound hCa
    obtain ⟨Mv, -, hMv⟩ := trial_bound hCv
    refine ⟨2 * Ma + Mv, fun x hx => ?_⟩
    have hx1 : x ∈ Icc (-1 : ℝ) 1 := ⟨hx.1.le, hx.2.le⟩
    have h1 := (hMa x hx1).1
    have h2 := (hMv x hx1).2
    unfold fRm
    rw [abs_le] at h1 h2 ⊢
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  · obtain ⟨Mv, -, hMv⟩ := trial_bound hCv
    refine ⟨2 * Mv, fun x hx => ?_⟩
    have hx1 : x ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [hx.1], hx.2.le⟩
    have h1 := (hMv x hx1).1
    unfold fCm
    rw [abs_le] at h1 ⊢
    constructor <;> linarith [h1.1, h1.2]
  · intro α hα
    have hI := hI_move (aB capSource 0) (a := aT capSource 0) (v := aV capSource 0)
      (summable_of_moment_bound hA0).2 (summable_of_moment_bound hV0).2 ha0 ha1 hv0 hv1 hτ hL0 hL1
      hQ00 hQ01 hQ11
    have hanch : anchorVal 0 = anchorIntercept (aB capSource 0) (aT capSource 0) (aV capSource 0) := rfl
    have hJ' : anchorIntercept (aB capSource 0) (fun k => aT capSource 0 k + (da0 k + τ * da1 k))
        (fun k => aV capSource 0 k + (dv0 k + τ * dv1 k)) + B.gasICap ≤ J := by
      rw [hanch] at hI1
      linarith [hI, hI1, hgasB, hJ]
    have := hbud_of_sigV B (aB_zero) (hW0 α hα) (hW1 α hα) hM hJ' (hV α hα)
    have e : 58 * ((c2Q : ℝ) + l.σ) * α / 58 = ((c2Q : ℝ) + l.σ) * α := by ring
    rw [e]
    exact this


theorem nodeD_eq {P : Parameters} [Shape58 P] (δ : ℝ → ℝ) (u : ℝ) :
    nodeD P δ u = δ (realCoordinateInv u) / 58 := by
  unfold nodeD; rw [Shape58.n0_eq (P := P)]; norm_num

/-- **The low branch on one physical cell** (GP §9(c), (d)): `selected_low_or_pick` with `testT`, the
cell constants of `phys_cells` and the hole `PhaseHole`.  `D` is a record skeleton whose residual is
`rs` and near cap `np - log 2`, with caps below the cell constants and the phase data below the
sums of `testT` against `D.p`. -/
theorem low_on_cell {P : Parameters} [Shape58 P] (hg0 : gC0 P = 6 / 29) (hg1 : gC1 P = 47 / 29)
    {G : ℝ → Prop} {ζ γ : ℝ} (hζ : 0 ≤ ζ) {δ : ℝ → ℝ} {W : Set ℝ} {σ Δ : ℚ} (hΔ0 : 0 ≤ (Δ : ℝ))
    {nC fC rs np : ℝ} {residual nearCap : ℝ}
    (D : SecondTrialBoundsEnd P W (colCell P ζ γ) (nodeD P δ) ((tQ : ℝ) - Δ) residual nearCap
      ((c2Q : ℝ) + σ) G)
    (hres : residual = rs) (hnear : nearCap = np - Real.log 2)
    (hN : D.normCap ≤ nC) (hF : D.fieldCap ≤ fC)
    (hWγ : ∀ α ∈ W, α ≤ γ) (hW0 : ∀ α ∈ W, 0 ≤ α) (hW1 : ∀ α ∈ W, α ≤ 1)
    (hV : ∀ α ∈ W, wV nC fC rs np α ≤ σ * α + Δ)
    {F0 U FU s p2lo s' β : ℝ} (hF0 : F0 = testF 0)
    (hphi : ∀ α ∈ W, 0 ≤ phiS F0 U FU s α β)
    (hom : ∀ α ∈ W, 0 ≤ 5 / 6 * (48 / 58) - (1 - (1 - α + p2lo - s') / 2 + 1 / 1000))
    (hS : U + (β / a1Q) * FU ≤ ∑' k : ℕ, testT.F (k + 1) * D.p (k + 1))
    (hp2 : p2lo ≤ D.p 2)
    (hs : Real.sqrt (7877 / 10000 * ((Δ : ℝ) / 2)) ≤ s) (hs' : Real.sqrt (2 * ((Δ : ℝ) / 2)) ≤ s')
    (hole : PhaseHole)
    {Q : ∀ (N p m : ℕ), (Fin p → ℝ) → (Fin m → ℝ) → (Fin p → ℝ) → Prop}
    (hQ : ∀ N p m x y s, Q N p m x y s → ((m : ℝ) / (P.n N : ℝ)) ∈ W) :
    SelectedLowOrPick P ζ δ (tQ : ℝ) (58 * ((c2Q : ℝ) + σ)) G Q := by
  have hlo : (loQ : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9; norm_num [loQ] at this ⊢; linarith
  subst hF0
  subst hres
  have hnp : np = nearCap + Real.log 2 := by linarith
  subst hnp
  refine selected_low_or_pick hζ hWγ D testT (nodeD_eq δ) (ξ := 1 / 1000) (d := 1) (Δ := fun _ => (Δ : ℝ))
    (by norm_num) one_pos ?_ ?_ ?_ (Filter.Eventually.of_forall fun N x hx => by simp [testT] at hx)
    (fun y _ hy => by simpa [testT] using hy.le) hQ
    (fun w e hinj h0 h1 _ hstat => pickWindow_of_phaseHole hole hinj h0 h1 e hstat)
  · intro α hα β' hβ'
    have hb := oldBound_budget_of_wV (P := P) hg0 hg1 (ℓ := Real.log 2) (β := β') rfl hlo (hV α hα)
    have e1 : (1 - α) * D.fieldCap ≤ (1 - α) * fC := mul_le_mul_of_nonneg_left hF (by linarith [hW1 α hα])
    unfold oldBound at hb ⊢
    have e : 58 * ((c2Q : ℝ) + σ) / 58 * α = ((c2Q : ℝ) + σ) * α := by ring
    rw [e]
    linarith
  · intro α hα
    have hsq : Real.sqrt (testT.H * ((Δ : ℝ) / 2)) ≤ s :=
      (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right testH_le (by positivity))).trans hs
    have := hphase_arith (F0 := testF 0) (U := U) (FU := FU) (s := s) (τ := β / a1Q) (α := α)
      (Hh := testT.H) (Δ := (Δ : ℝ)) hS hsq (hphi α hα) phase_rhs_le
    have h0 : testT.h₀ = 0 := rfl
    have hF : testT.F 0 = testF 0 := rfl
    simp only [h0, hF]
    simpa using this
  · intro α hα
    exact hone_arith hp2 hs' (hom α hα)

theorem rowChord {da0 da1 dv0 dv1 : ℕ → ℝ} {K : ℕ} (ha0 : ∀ k, K ≤ k → da0 k = 0)
    (ha1 : ∀ k, K ≤ k → da1 k = 0) (hv0 : ∀ k, K ≤ k → dv0 k = 0) (hv1 : ∀ k, K ≤ k → dv1 k = 0)
    {c0 c1 : ℝ}
    (R0 : ∀ x ∈ CapSource.rowDom, capSource.freeRow Trunc.exact 0 x + fRm da0 da1 dv0 dv1 0 x ≤ c0)
    (R1 : ∀ x ∈ CapSource.rowDom, capSource.freeRow Trunc.exact 0 x + fRm da0 da1 dv0 dv1 1 x ≤ c1)
    {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) :
    ∀ x ∈ CapSource.rowDom, capSource.freeRow Trunc.exact 0 x + fRm da0 da1 dv0 dv1 τ x ≤
      (1 - τ) * c0 + τ * c1 := by
  intro x hx
  have hx1 : |x| ≤ 1 := by
    rcases hx with h | h
    · exact abs_le.mpr ⟨h.1, by linarith [h.2]⟩
    · exact abs_le.mpr ⟨by linarith [h.1], h.2.le⟩
  rw [fRm_affine ha0 ha1 hv0 hv1 τ hx1, ← add_assoc]
  have := chord_row (F := capSource.freeRow Trunc.exact 0 x) (h0 := fRm da0 da1 dv0 dv1 0 x)
    (h1 := fRm da0 da1 dv0 dv1 1 x - fRm da0 da1 dv0 dv1 0 x) hτ0 hτ1 (R0 x hx)
    (by have := R1 x hx; linarith)
  linarith

theorem colChord1 {dv0 dv1 : ℕ → ℝ} {K : ℕ} (hv0 : ∀ k, K ≤ k → dv0 k = 0)
    (hv1 : ∀ k, K ≤ k → dv1 k = 0) {ζ c0 c1 : ℝ}
    (C0 : ∀ s ∈ Ioo (0 : ℝ) 1, capSource.colField 0 s + fCm dv0 dv1 0 s ≤ c0)
    (C1 : ∀ s ∈ Ioo (0 : ℝ) 1, capSource.colField 0 s + fCm dv0 dv1 1 s +
      (aeQ : ℝ) * Real.log (1 + ζ * s) ≤ c1)
    {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) :
    ∀ s ∈ Ioo (0 : ℝ) 1, capSource.colField 0 s + fCm dv0 dv1 τ s +
      (τ * aeQ) * Real.log (1 + ζ * s) ≤ (1 - τ) * c0 + τ * c1 := by
  intro s hs
  have hs1 : |s| ≤ 1 := abs_le.mpr ⟨by linarith [hs.1], hs.2.le⟩
  rw [fCm_affine hv0 hv1 τ hs1, ← add_assoc]
  have := chord_col (F := capSource.colField 0 s) (k0 := fCm dv0 dv1 0 s)
    (k1 := fCm dv0 dv1 1 s - fCm dv0 dv1 0 s) (g := Real.log (1 + ζ * s)) (ae := (aeQ : ℝ))
    hτ0 hτ1 (C0 s hs) (by have := C1 s hs; linarith)
  linarith

theorem colChord2 {dv0 dv1 : ℕ → ℝ} {ζ c1 c2 γ : ℝ}
    (C1 : ∀ s ∈ Ioo (0 : ℝ) 1, capSource.colField 0 s + fCm dv0 dv1 1 s +
      (aeQ : ℝ) * Real.log (1 + ζ * s) ≤ c1)
    (C2 : ∀ s ∈ Ioo (0 : ℝ) 1, capSource.colField 0 s + fCm dv0 dv1 1 s +
      (a1Q : ℝ) * Real.log (1 + ζ * s) ≤ c2)
    (hγ0 : (aeQ : ℝ) ≤ γ) (hγ1 : γ ≤ a1Q) :
    ∀ s ∈ Ioo (0 : ℝ) 1, capSource.colField 0 s + fCm dv0 dv1 1 s + γ * Real.log (1 + ζ * s) ≤
      c1 + ((γ - aeQ) / ((a1Q : ℝ) - aeQ)) * (c2 - c1) := by
  intro s hs
  have hae : (aeQ : ℝ) < a1Q := by norm_num [aeQ, a1Q]
  have := chord_col_gamma (F := capSource.colField 0 s + fCm dv0 dv1 1 s)
    (g := Real.log (1 + ζ * s)) hae hγ0 hγ1 (C1 s hs) (C2 s hs)
  have hd : 0 < (a1Q : ℝ) - aeQ := sub_pos.mpr hae
  have e : c1 + ((γ - aeQ) / ((a1Q : ℝ) - aeQ)) * (c2 - c1) =
      ((a1Q - γ) * c1 + (γ - aeQ) * c2) / (a1Q - aeQ) := by
    field_simp; ring
  rw [e]; exact this

/-- Uniform partition cell ends. -/
def cLo (A B : ℝ) (n i : ℕ) : ℝ := A + (B - A) * i / n
def cHi (A B : ℝ) (n i : ℕ) : ℝ := A + (B - A) * (i + 1) / n

theorem cLo_le_cHi {A B : ℝ} (hAB : A ≤ B) {n : ℕ} (hn : 0 < n) (i : ℕ) : cLo A B n i ≤ cHi A B n i := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  unfold cLo cHi
  have : 0 ≤ (B - A) / n := div_nonneg (by linarith) hnR.le
  have e : A + (B - A) * ((i : ℝ) + 1) / n = (A + (B - A) * i / n) + (B - A) / n := by
    field_simp; ring
  rw [e]; linarith

/-- **The low branch on one cell of a physical step** (`phys_cells` output and a record skeleton at the
cell end). -/
theorem low_of_phys_cell {P : Parameters} [Shape58 P] (hg0 : gC0 P = 6 / 29) (hg1 : gC1 P = 47 / 29)
    {G : ℝ → Prop} {ζ : ℝ} (hζ : 0 ≤ ζ) {δ : ℝ → ℝ} {σ Δ : ℚ} (hΔ0 : 0 ≤ (Δ : ℝ))
    {A B : ℚ} (hAB : A < B) (hA0 : 0 ≤ A) (hB1 : B ≤ a1Q) {n i : ℕ} (hn : 0 < n) (hi : i < n)
    {nC fC rs np : QP} {F0 U FU s p2 du2 s' : ℚ} (hF0 : (F0 : ℝ) = testF 0)
    (hcell : ∀ α ∈ Icc (cLo A B n i) (cHi A B n i),
      wV (evalQ nC (cHi A B n i)) (evalQ fC (cHi A B n i)) (evalQ rs (cHi A B n i))
        (evalQ np (cHi A B n i)) α ≤ σ * α + Δ ∧
      0 ≤ phiS F0 U FU s α (cHi A B n i) ∧ 0 ≤ omS p2 du2 s' α (cHi A B n i))
    (R : ∀ β ∈ Icc (A : ℝ) B, SecondTrialBoundsEnd P ∅ (colCell P ζ β) (nodeD P δ) ((tQ : ℝ) - Δ)
      (evalQ rs β) (evalQ np β - Real.log 2) ((c2Q : ℝ) + σ) G)
    (hN : ∀ β hβ, (R β hβ).normCap ≤ evalQ nC β) (hF : ∀ β hβ, (R β hβ).fieldCap ≤ evalQ fC β)
    (hS : ∀ β hβ, (U : ℝ) + (β / a1Q) * FU ≤ ∑' k : ℕ, testT.F (k + 1) * (R β hβ).p (k + 1))
    (hp2 : ∀ β hβ, (p2 : ℝ) + (β / a1Q) * du2 ≤ (R β hβ).p 2)
    (hs : Real.sqrt (7877 / 10000 * ((Δ : ℝ) / 2)) ≤ s) (hs' : Real.sqrt (2 * ((Δ : ℝ) / 2)) ≤ s')
    (hole : PhaseHole)
    {Q : ∀ (N p m : ℕ), (Fin p → ℝ) → (Fin m → ℝ) → (Fin p → ℝ) → Prop}
    (hQ : ∀ N p m x y s, Q N p m x y s → ((m : ℝ) / (P.n N : ℝ)) ∈ Icc (cLo A B n i) (cHi A B n i)) :
    SelectedLowOrPick P ζ δ (tQ : ℝ) (58 * ((c2Q : ℝ) + σ)) G Q := by
  have hAB' : (A : ℝ) < B := by exact_mod_cast hAB
  have hsub : Icc (cLo A B n i) (cHi A B n i) ⊆ Icc (A : ℝ) B := cell_sub hi hn hAB'.le
  have hhi : cHi A B n i ∈ Icc (A : ℝ) B := hsub ⟨cLo_le_cHi hAB'.le hn i, le_rfl⟩
  have hlo : (loQ : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9; norm_num [loQ] at this ⊢; linarith
  have hA0' : (0 : ℝ) ≤ A := by exact_mod_cast hA0
  have hB1' : (B : ℝ) ≤ 51 / 500 := by
    have h : (B : ℝ) ≤ a1Q := by exact_mod_cast hB1
    norm_num [a1Q] at h; linarith
  let D0 := R (cHi A B n i) hhi
  have hW0 : ∀ α ∈ Icc (cLo A B n i) (cHi A B n i), 0 ≤ α := fun α hα => hA0'.trans (hsub hα).1
  have hW1 : ∀ α ∈ Icc (cLo A B n i) (cHi A B n i), α ≤ 1 := fun α hα =>
    (hsub hα).2.trans (hB1'.trans (by norm_num))
  let D := reWindowSecond D0 (Icc (cLo A B n i) (cHi A B n i)) (by
    intro a s ha ha0 hs0
    have hb := oldBound_budget_of_wV (P := P) hg0 hg1 (ℓ := Real.log 2) (β := s) rfl hlo
      (hcell a ha).1
    have h1 := hN (cHi A B n i) hhi
    have h2 := hF (cHi A B n i) hhi
    have e1 : (1 - a) * D0.fieldCap ≤ (1 - a) * evalQ fC (cHi A B n i) :=
      mul_le_mul_of_nonneg_left h2 (by linarith [hW1 a ha])
    unfold oldBound at hb
    show (-gC0 P + gC1 P * a - a ^ 2 + s - s ^ 2) * Real.log 2 + D0.normCap + (1 - a) * D0.fieldCap +
      (a - s) * evalQ rs (cHi A B n i) + s * (evalQ np (cHi A B n i) - Real.log 2) ≤ _
    linarith)
  refine low_on_cell hg0 hg1 hζ (γ := cHi A B n i) (W := Icc (cLo A B n i) (cHi A B n i)) hΔ0
    (nC := evalQ nC (cHi A B n i)) (fC := evalQ fC (cHi A B n i)) (rs := evalQ rs (cHi A B n i))
    (np := evalQ np (cHi A B n i)) (residual := evalQ rs (cHi A B n i))
    (nearCap := evalQ np (cHi A B n i) - Real.log 2) D rfl rfl (hN _ hhi) (hF _ hhi)
    (fun α hα => hα.2) hW0 hW1 (fun α hα => (hcell α hα).1) (F0 := F0) (U := U) (FU := FU) (s := s)
    (p2lo := p2 + (cHi A B n i / a1Q) * du2) (s' := s') (β := cHi A B n i) hF0
    (fun α hα => (hcell α hα).2.1) (fun α hα => by have := (hcell α hα).2.2; unfold omS at this; linarith)
    (hS _ hhi) (hp2 _ hhi) hs hs' hole hQ

section CmpSec

variable {P : Parameters} [Shape58 P] {G : ℝ → Prop} {δ : ℝ → ℝ} {gasI : ℝ} {anchI : Fin 2 → ℝ}
  (B : capSource.CapBundle Trunc.exact (nodeD P δ) G gasI anchI)
  (hang : ∀ σ, B.angCap σ ≤ kappa σ) (hgas : gasConst capSource ≤ gasI)
  (hgasB : B.gasICap ≤ gasConst capSource) (hM : markCap B ≤ -976 / 1000)
  {da0 da1 dv0 dv1 : ℕ → ℝ} {K : ℕ} (ha0 : ∀ k, K ≤ k → da0 k = 0) (ha1 : ∀ k, K ≤ k → da1 k = 0)
  (hv0 : ∀ k, K ≤ k → dv0 k = 0) (hv1 : ∀ k, K ≤ k → dv1 k = 0)
  (l : SigLits) (hI1 : anchorVal 0 + gasConst capSource ≤ l.I1)
  (hL0 : 2 * barrierInner (aT capSource 0) da0 + barrierInner (aV capSource 0) dv0 ≤ l.L0)
  (hL1 : 2 * barrierInner (aT capSource 0) da1 + barrierInner (aV capSource 0) dv1 ≤ l.L1)
  (hQ00 : barrierInner da0 da0 + barrierInner dv0 dv0 / 2 ≤ l.Q00)
  (hQ01 : barrierInner da0 da1 + barrierInner dv0 dv1 / 2 ≤ l.Q01)
  (hQ11 : barrierInner da1 da1 + barrierInner dv1 dv1 / 2 ≤ l.Q11)
  {ζ : ℝ} (hζ : 0 ≤ ζ)
  (R0 : ∀ x ∈ CapSource.rowDom, capSource.freeRow Trunc.exact 0 x + fRm da0 da1 dv0 dv1 0 x ≤ l.c0R)
  (R1 : ∀ x ∈ CapSource.rowDom, capSource.freeRow Trunc.exact 0 x + fRm da0 da1 dv0 dv1 1 x ≤ l.c1R)
  (C0 : ∀ s ∈ Ioo (0 : ℝ) 1, capSource.colField 0 s + fCm dv0 dv1 0 s ≤ l.c0C)
  (C1 : ∀ s ∈ Ioo (0 : ℝ) 1, capSource.colField 0 s + fCm dv0 dv1 1 s +
    (aeQ : ℝ) * Real.log (1 + ζ * s) ≤ l.c1C)
  (C2 : ∀ s ∈ Ioo (0 : ℝ) 1, capSource.colField 0 s + fCm dv0 dv1 1 s +
    (a1Q : ℝ) * Real.log (1 + ζ * s) ≤ l.c2C)
  (hG : ∀ y, G y → (0 < y → y ∈ CapSource.ordDom Sign.pos) ∧ (y < 0 → -y ∈ CapSource.ordDom Sign.neg))

include B hang hgas hgasB hM ha0 ha1 hv0 hv1 hI1 hL0 hL1 hQ00 hQ01 hQ11 hζ R0 R1 C0 C1 C2 hG

/-- The comparison bound on a cell of the first signed piece `[0, α_e]` (right end `hi`, `τ = hi/α_e`). -/
theorem cmp_sig1 {lo hi : ℝ} (hlo : 0 ≤ lo) (hlh : lo ≤ hi) (hhi : hi ≤ aeQ)
    (hV : ∀ α ∈ Icc lo hi, sigV (sigJ1 l hi) (sigR1 l hi) (sigC1 l hi) α ≤ l.σ * α)
    {Q : ∀ (N p m : ℕ), (Fin p → ℝ) → (Fin m → ℝ) → (Fin p → ℝ) → Prop}
    (hQ : ∀ N p m x y s, Q N p m x y s → ((m : ℝ) / (P.n N : ℝ)) ∈ Icc lo hi) :
    SelectedComparisonOnPick P ζ δ (tQ : ℝ) (58 * ((c2Q : ℝ) + l.σ)) G Q := by
  have hae : (0 : ℝ) < aeQ := by norm_num [aeQ]
  have hτ0 : 0 ≤ hi / aeQ := div_nonneg (hlo.trans hlh) hae.le
  have hτ1 : hi / aeQ ≤ 1 := by rw [div_le_one hae]; exact hhi
  have hγ : (hi / aeQ) * aeQ = hi := by field_simp
  have hae1 : (aeQ : ℝ) ≤ 51 / 500 := by norm_num [aeQ]
  refine cmp_on_cell B hang hgas hgasB hM ha0 ha1 hv0 hv1 l hI1 hL0 hL1 hQ00 hQ01 hQ11 (τ := hi / aeQ)
    (γ := hi) (r := (1 - hi / aeQ) * l.c0R + (hi / aeQ) * l.c1R)
    (c := (1 - hi / aeQ) * l.c0C + (hi / aeQ) * l.c1C) (J := sigJ1 l hi) hτ0 hζ (hlo.trans hlh)
    (rowChord ha0 ha1 hv0 hv1 R0 R1 hτ0 hτ1) ?_ ?_ (W := Icc lo hi) (fun α hα => hlo.trans hα.1)
    (fun α hα => hα.2.trans (hhi.trans hae1)) (fun α hα => hα.2) ?_ (nodeD_eq δ) hG hQ
  · have := colChord1 hv0 hv1 (ζ := ζ) C0 C1 hτ0 hτ1
    rw [hγ] at this
    exact this
  · unfold sigJ1; apply le_of_eq; ring
  · intro α hα
    have := hV α hα
    unfold sigR1 sigC1 at this
    convert this using 2 <;> ring

/-- The comparison bound on a cell of the second signed piece `[α_e, α₁]` (`τ = 1`, `γ = hi`). -/
theorem cmp_sig2 {lo hi : ℝ} (hlo : (aeQ : ℝ) ≤ lo) (hlh : lo ≤ hi) (hhi : hi ≤ a1Q)
    (hV : ∀ α ∈ Icc lo hi, sigV (sigJ2 l) l.c1R (sigC2 l hi) α ≤ l.σ * α)
    {Q : ∀ (N p m : ℕ), (Fin p → ℝ) → (Fin m → ℝ) → (Fin p → ℝ) → Prop}
    (hQ : ∀ N p m x y s, Q N p m x y s → ((m : ℝ) / (P.n N : ℝ)) ∈ Icc lo hi) :
    SelectedComparisonOnPick P ζ δ (tQ : ℝ) (58 * ((c2Q : ℝ) + l.σ)) G Q := by
  have hae : (0 : ℝ) < aeQ := by norm_num [aeQ]
  have ha1Q : (a1Q : ℝ) = 51 / 500 := by norm_num [a1Q]
  have hlo0 : 0 ≤ lo := hae.le.trans hlo
  refine cmp_on_cell B hang hgas hgasB hM ha0 ha1 hv0 hv1 l hI1 hL0 hL1 hQ00 hQ01 hQ11 (τ := 1)
    (γ := hi) (r := l.c1R) (c := l.c1C + ((hi - aeQ) / ((a1Q : ℝ) - aeQ)) * (l.c2C - l.c1C))
    (J := sigJ2 l) zero_le_one hζ (hlo0.trans hlh) ?_ ?_ ?_ (W := Icc lo hi) (fun α hα => hlo0.trans hα.1)
    (fun α hα => hα.2.trans (hhi.trans (le_of_eq ha1Q))) (fun α hα => hα.2) ?_ (nodeD_eq δ) hG hQ
  · have := rowChord ha0 ha1 hv0 hv1 R0 R1 zero_le_one le_rfl
    simpa using this
  · exact colChord2 C1 C2 (hlo.trans hlh) hhi
  · unfold sigJ2; apply le_of_eq; ring
  · intro α hα
    have := hV α hα
    unfold sigC2 at this
    exact this

/-- **The near sheet from the cell checks** (GP §9(a), (c), (d), Theorem 8.3): the signed comparison
cells (`sig_cells1/2`) and the 64 physical steps (`phys_cells`), refined against each other, give the
selected bound on the near sheet and hence `FreeNearBoundZ`. -/
theorem nearSheet_of_cells (hg0 : gC0 P = 6 / 29) (hg1 : gC1 P = 47 / 29) (hη : 0 < l.η)
    (hP1 : PolyNonneg (sigP1 l) 0 aeQ) (hP2 : PolyNonneg (sigP2 l) aeQ a1Q)
    {κ : ℕ} (A B' : Fin κ → ℚ) (hAB : ∀ j, A j < B' j) (hA0 : ∀ j, 0 ≤ A j) (hB1 : ∀ j, B' j ≤ a1Q)
    (hcovP : ∀ α ∈ Icc (0 : ℝ) (a1Q : ℝ), ∃ j, (A j : ℝ) ≤ α ∧ α ≤ B' j)
    (Δ : Fin κ → ℚ) (hΔ0 : ∀ j, 0 ≤ (Δ j : ℝ)) (nC fC rs np : Fin κ → QP)
    (F0 U FU p2 du2 : ℚ) (s s' : Fin κ → ℚ) (hF0 : (F0 : ℝ) = testF 0)
    (hPW : ∀ j, PolyNonneg (wPq l.σ l.η (Δ j) (nC j) (fC j) (rs j) (np j)) (A j) (B' j))
    (hPφ : ∀ j, PolyNonneg (addQ [-l.η] (phiQ F0 U FU (s j))) (A j) (B' j))
    (hPω : ∀ j, PolyNonneg (addQ [-l.η] (omQ p2 du2 (s' j))) (A j) (B' j))
    (Rp : ∀ j, ∀ β ∈ Icc (A j : ℝ) (B' j), SecondTrialBoundsEnd P ∅ (colCell P ζ β) (nodeD P δ)
      ((tQ : ℝ) - Δ j) (evalQ (rs j) β) (evalQ (np j) β - Real.log 2) ((c2Q : ℝ) + l.σ) G)
    (hNp : ∀ j β hβ, (Rp j β hβ).normCap ≤ evalQ (nC j) β)
    (hFp : ∀ j β hβ, (Rp j β hβ).fieldCap ≤ evalQ (fC j) β)
    (hSp : ∀ j β hβ, (U : ℝ) + (β / a1Q) * FU ≤ ∑' k : ℕ, testT.F (k + 1) * (Rp j β hβ).p (k + 1))
    (hp2p : ∀ j β hβ, (p2 : ℝ) + (β / a1Q) * du2 ≤ (Rp j β hβ).p 2)
    (hs : ∀ j, Real.sqrt (7877 / 10000 * ((Δ j : ℝ) / 2)) ≤ s j)
    (hs' : ∀ j, Real.sqrt (2 * ((Δ j : ℝ) / 2)) ≤ s' j)
    (hole : PhaseHole) {Nd : ∀ (N m : ℕ), (Fin m → ℝ) → Prop} :
    FreeNearBoundZ P G Nd ζ δ (tQ : ℝ) (58 * ((c2Q : ℝ) + l.σ)) (51 / 500) := by
  obtain ⟨n1, hn1, hc1⟩ := sig_cells1 l hη hP1
  obtain ⟨n2, hn2, hc2⟩ := sig_cells2 l hη hP2
  have hAB' : ∀ j, (A j : ℝ) < B' j := fun j => by exact_mod_cast hAB j
  choose m hm hcellP using fun j => phys_cells (hAB j) hη (hPW j) (hPφ j) (hPω j)
  have hae : (0 : ℝ) < aeQ := by norm_num [aeQ]
  have haeb : (aeQ : ℝ) < a1Q := by norm_num [aeQ, a1Q]
  let slo : Fin n1 ⊕ Fin n2 → ℝ := Sum.elim (fun i => cLo 0 aeQ n1 i) (fun i => cLo aeQ a1Q n2 i)
  let shi : Fin n1 ⊕ Fin n2 → ℝ := Sum.elim (fun i => cHi 0 aeQ n1 i) (fun i => cHi aeQ a1Q n2 i)
  let plo : (Σ j : Fin κ, Fin (m j)) → ℝ := fun p => cLo (A p.1) (B' p.1) (m p.1) p.2
  let phi : (Σ j : Fin κ, Fin (m j)) → ℝ := fun p => cHi (A p.1) (B' p.1) (m p.1) p.2
  have cmpS : ∀ (sx : Fin n1 ⊕ Fin n2) {Q : ∀ (N p m : ℕ), (Fin p → ℝ) → (Fin m → ℝ) → (Fin p → ℝ) → Prop},
      (∀ N p m x y s, Q N p m x y s → ((m : ℝ) / (P.n N : ℝ)) ∈ Icc (slo sx) (shi sx)) →
      SelectedComparisonOnPick P ζ δ (tQ : ℝ) (58 * ((c2Q : ℝ) + l.σ)) G Q := by
    intro sx Q hQ
    rcases sx with i | i
    · have hsub := cell_sub (A := 0) (B := (aeQ : ℝ)) i.2 hn1 hae.le
      have hlh := cLo_le_cHi (A := 0) (B := (aeQ : ℝ)) hae.le hn1 i
      exact cmp_sig1 B hang hgas hgasB hM ha0 ha1 hv0 hv1 l hI1 hL0 hL1 hQ00 hQ01 hQ11 hζ R0 R1 C0 C1 C2 hG
        (hsub ⟨le_rfl, hlh⟩).1 hlh (hsub ⟨hlh, le_rfl⟩).2 (fun α hα => hc1 i i.2 α hα) hQ
    · have hsub := cell_sub (A := (aeQ : ℝ)) (B := (a1Q : ℝ)) i.2 hn2 haeb.le
      have hlh := cLo_le_cHi (A := (aeQ : ℝ)) (B := (a1Q : ℝ)) haeb.le hn2 i
      exact cmp_sig2 B hang hgas hgasB hM ha0 ha1 hv0 hv1 l hI1 hL0 hL1 hQ00 hQ01 hQ11 hζ R0 R1 C0 C1 C2 hG
        (hsub ⟨le_rfl, hlh⟩).1 hlh (hsub ⟨hlh, le_rfl⟩).2 (fun α hα => hc2 i i.2 α hα) hQ
  have lowP : ∀ (pp : Σ j : Fin κ, Fin (m j)) {Q : ∀ (N p m : ℕ), (Fin p → ℝ) → (Fin m → ℝ) → (Fin p → ℝ) → Prop},
      (∀ N p m x y s, Q N p m x y s → ((m : ℝ) / (P.n N : ℝ)) ∈ Icc (plo pp) (phi pp)) →
      SelectedLowOrPick P ζ δ (tQ : ℝ) (58 * ((c2Q : ℝ) + l.σ)) G Q := by
    intro pp Q hQ
    exact low_of_phys_cell hg0 hg1 hζ (hΔ0 pp.1) (hAB pp.1) (hA0 pp.1) (hB1 pp.1) (hm pp.1) pp.2.2 hF0
      (hcellP pp.1 pp.2 pp.2.2) (Rp pp.1) (hNp pp.1) (hFp pp.1) (hSp pp.1) (hp2p pp.1) (hs pp.1) (hs' pp.1) hole hQ
  let Wc : (Fin n1 ⊕ Fin n2) × (Σ j : Fin κ, Fin (m j)) → Set ℝ := fun sp =>
    Icc (slo sp.1) (shi sp.1) ∩ Icc (plo sp.2) (phi sp.2)
  have hsel := selected_of_cells (P := P) (ζ := ζ) (δ := δ) (G := G) (target := (tQ : ℝ))
    (cost := 58 * ((c2Q : ℝ) + l.σ)) (Finset.univ) Wc
    (Q := fun N _ m _ y _ => (m : ℝ) ≤ (51 / 500) * (P.n N : ℝ) ∧ Nd N m y) ?_ ?_
  · exact hnear296 hζ hsel
  · intro N p' m' x y s0 hQ0
    set α : ℝ := (m' : ℝ) / (P.n N : ℝ) with hα
    have hα0 : 0 ≤ α := by positivity
    have hα1 : α ≤ 51 / 500 := by
      rw [hα]
      by_cases hn : (P.n N : ℝ) = 0
      · rw [hn, div_zero]; norm_num
      · have hnp : 0 < (P.n N : ℝ) := lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm hn)
        rw [div_le_iff₀ hnp]; exact hQ0.1
    have ha1Q : (a1Q : ℝ) = 51 / 500 := by norm_num [a1Q]
    obtain ⟨j, hj1, hj2⟩ := hcovP α ⟨hα0, hα1.trans ha1Q.ge⟩
    obtain ⟨i, hi, hmem⟩ := cells_cover (hAB' j) (hm j) ⟨hj1, hj2⟩
    have hsx : ∃ sx : Fin n1 ⊕ Fin n2, α ∈ Icc (slo sx) (shi sx) := by
      by_cases hle : α ≤ aeQ
      · obtain ⟨i1, hi1, hm1⟩ := cells_cover (A := 0) (B := (aeQ : ℝ)) hae hn1 ⟨hα0, hle⟩
        exact ⟨Sum.inl ⟨i1, hi1⟩, hm1⟩
      · obtain ⟨i2, hi2, hm2⟩ := cells_cover (A := (aeQ : ℝ)) (B := (a1Q : ℝ)) haeb hn2
          ⟨(not_le.mp hle).le, hα1.trans ha1Q.ge⟩
        exact ⟨Sum.inr ⟨i2, hi2⟩, hm2⟩
    obtain ⟨sx, hsx⟩ := hsx
    exact ⟨(sx, ⟨j, ⟨i, hi⟩⟩), Finset.mem_univ _, hsx, hmem⟩
  · intro sp _
    exact selectedFree_of_lowOrPick (Shape58.adm (P := P)) hζ
      (lowP sp.2 (fun N p m x y s h => h.2.2)) (cmpS sp.1 (fun N p m x y s h => h.2.1))

end CmpSec

section TopSec
open CatalanMeasure.GenD.Signed.RouteI.IntervalNodesData CatalanMeasure.GenD.Signed.RouteI.ChordTable
open CatalanMeasure.GenD.Signed.RouteI.ChordTableData CatalanMeasure.GenD.Signed CatalanMeasure.GenD.D58 CatalanMeasure.GenD.Signed.RouteI.CapFields

/-- The window of the design: `G_W`, the preimage of the 106 frozen intervals. -/
def Uset : Set ℝ := ⋃ c : Fin 53 × Fin 2, Ioo (ivlLo c) (ivlHi c)
def Gd : ℝ → Prop := GW Uset
/-- The node correction `δ̂` of the frozen chord table. -/
def δc : ℝ → ℝ := pwl 865 kt vt

theorem hsupport_d (N : ℕ) (a : Fin (53 * N)) : Gd (realCoordinate (tauI ivlLo ivlHi N a)) := by
  have hm := tauI_mem_data N a
  refine ⟨(abs_le.mpr ⟨(realCoordinate_mem hm).1.le, (realCoordinate_mem hm).2.le⟩), ?_⟩
  rw [realCoordinate_right_inverse hm]
  exact mem_iUnion.mpr ⟨_, tauI_mem_Ioo ivlLo ivlHi ivlLo_lt N a⟩

theorem hC0_d (N : ℕ) (a : Fin (53 * N)) :
    -ivlL ivlLo ivlHi ((tauI ivlLo ivlHi N a : ℝ) : ℂ) ≤ 8263 / 250 + δc (tauI ivlLo ivlHi N a) := by
  have h := tauI_mem_Ioo ivlLo ivlHi ivlLo_lt N a
  have hh := hull_table (pairEquiv 53 N a).1
  exact neg_L_le_table (hh.1.trans h.1.le) (h.2.le.trans hh.2)

/-- The ψ clause: `C₀ + D - 48 log (3/4) < ψ`. -/
def logOK : Bool :=
  match LogEval.logQ 12 (4 / 3) with
  | some (v, e) => decide (8263 / 250 + 32506 / 10000 + 48 * (v + e) < 50111339578 / 1000000000)
  | _ => false

theorem logOK_true : logOK = true := by
  -- kcost: 0.02 s estimated; one logQ at n = 12.
  decide +kernel

theorem hw_d : 8263 / 250 + (32506 / 10000 : ℝ) - ((58 : ℝ) - 2 * 5) * Real.log (3 / 4) < psi296 := by
  have h := logOK_true
  unfold logOK at h
  split at h
  · rename_i v e h1
    have hp := of_decide_eq_true h
    have l1 := (LogEval.logQ_spec h1).2.le_upper
    have hp' : ((8263 / 250 + 32506 / 10000 + 48 * (v + e) : ℚ) : ℝ) <
        ((50111339578 / 1000000000 : ℚ) : ℝ) := Rat.cast_lt.mpr hp
    have hlog : Real.log (3 / 4) = -Real.log (4 / 3) := by
      rw [← Real.log_inv]; norm_num
    push_cast at hp' l1
    unfold psi296
    rw [hlog]
    norm_num at hp' l1 ⊢
    linarith
  · simp at h

/-- `hweights` of the terminal on the interval nodes, from (hcirc) and (hseg). -/
theorem hweights_d
    (hcirc : ∀ z : ℂ, ‖z‖ = 3 / 4 →
      ((dc58.toParameters.h0 + dc58.toParameters.q0 : ℕ) : ℝ) * Real.log ‖(1 : ℂ) - z‖ +
        ivlL ivlLo ivlHi z ≤ 32506 / 10000)
    (hseg : ∀ x : ℝ, 3 / 4 ≤ |x| → |x| < 1 →
      ((dc58.toParameters.h0 + dc58.toParameters.q0 : ℕ) : ℝ) * Real.log ‖(1 : ℂ) - (x : ℂ)‖ +
        ivlL ivlLo ivlHi (x : ℂ) - 2 * (dc58.toParameters.g0 : ℝ) * Real.log (3 / 4) ≤ 32506 / 10000) :
    ∀ᶠ N : ℕ in atTop, ∀ p m : ℕ, p + m = dc58.toParameters.n N →
      ∀ k : ℕ, k < dc58.toParameters.n N → ∀ a : Fin (dc58.d0 * N),
      |(rowCommonFactor dc58.toParameters N).eval (tauI ivlLo ivlHi N a)| *
        |restrictedWeight dc58.toParameters N k (tauI ivlLo ivlHi N) a| *
        CatalanMeasure.zetaBeta (3 / 4) p m k ≤
          1 * (N : ℝ) * Real.exp ((psi296 + δc (tauI ivlLo ivlHi N a)) * N) :=
  hweights_tauI dc58.toParameters dc58.admissible (by norm_num) (by norm_num) ivlLo ivlHi ivlLo_lt
    ivl_disj ivl_lo_ge ivl_hi_le _ _ psi296 δc hcirc hseg
    (fun N a => hC0_d N a) (by simpa using hw_d) 1 one_pos

/-- **The terminal on the interval nodes** (GP Theorem 10.1): the three sheet bounds with `ζ = 3/4`,
`δ̂ = δc`, target `T296` and cost `58 costC`, plus (hcirc) and (hseg), give `μ(G) ≤ μ`. -/
theorem measure_of_sheets (μ : ℚ) (hμ1 : (269787 / 1000 : ℝ) ≤ μ) (hμ2 : (μ : ℝ) ≤ 400)
    (hcirc : ∀ z : ℂ, ‖z‖ = 3 / 4 →
      ((dc58.toParameters.h0 + dc58.toParameters.q0 : ℕ) : ℝ) * Real.log ‖(1 : ℂ) - z‖ +
        ivlL ivlLo ivlHi z ≤ 32506 / 10000)
    (hseg : ∀ x : ℝ, 3 / 4 ≤ |x| → |x| < 1 →
      ((dc58.toParameters.h0 + dc58.toParameters.q0 : ℕ) : ℝ) * Real.log ‖(1 : ℂ) - (x : ℂ)‖ +
        ivlL ivlLo ivlHi (x : ℂ) - 2 * (dc58.toParameters.g0 : ℝ) * Real.log (3 / 4) ≤ 32506 / 10000)
    (hfirst : FreeFirstBoundZ dc58.toParameters Gd (3 / 4) δc T296 (58 * costC))
    (hnear : FreeNearBoundZ dc58.toParameters Gd (CatalanMeasure.Signed.NodeSub (tauI ivlLo ivlHi))
      (3 / 4) δc T296 (58 * costC) alpha296)
    (hlarge : FreeLargeBoundZ dc58.toParameters Gd (3 / 4) δc T296 (58 * costC) alpha296) :
    ∀ᶠ b : ℕ in atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-(μ : ℝ)) <
        |(∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) - a / b| := by
  obtain ⟨lbC, gain, hg, hc⟩ := Count.LedgerContent.content
  have hpay := pay_designC (B := (μ : ℝ)) hμ1 hμ2
  exact catalan_irrationalityMeasure_of_nodes_C (tauI ivlLo ivlHi) Gd tauI_injective_data tauI_mem_data
    tauI_ne_zero_data hsupport_d _ μ eta295 _ alpha296 (3 / 4) 1 δc (by norm_num) zero_le_one hpay
    hc (Count.WinCertGlue.eta295_lt_of_gain hg) hfirst hnear hlarge (hweights_d hcirc hseg)


theorem ivl_P_nat : (List.range 106).all (fun i =>
    decide (0 ≤ ivlAN.getD i 0 → (215054274947 : ℤ) ≤ ivlAN.getD i 0)) = true := by
  -- kcost: 0.01 s estimated; 106 integer comparisons.
  decide +kernel

theorem ivl_N_nat : (List.range 106).all (fun i =>
    decide (ivlBN.getD i 0 ≤ 0 → ivlBN.getD i 0 ≤ (-413122735120 : ℤ))) = true := by
  -- kcost: 0.01 s estimated; 106 integer comparisons.
  decide +kernel

theorem ivl_P (c : Fin 53 × Fin 2) (h : 0 ≤ ivlLo c) : (215054274947 : ℝ) / 2 ^ 40 ≤ ivlLo c := by
  have h1 := List.all_eq_true.mp ivl_P_nat (finProdFinEquiv c : Fin (53 * 2))
    (List.mem_range.mpr (finProdFinEquiv c).2)
  have hp : (0 : ℝ) < 2 ^ 40 := by positivity
  have h2 := of_decide_eq_true h1
  unfold ivlLo loF at h ⊢
  have h3 : (0 : ℤ) ≤ ivlAN.getD (finProdFinEquiv c) 0 := by
    by_contra hn
    have hn' : ((ivlAN.getD (finProdFinEquiv c) 0 : ℤ) : ℝ) < 0 := by exact_mod_cast not_le.mp hn
    have := div_neg_of_neg_of_pos hn' hp
    linarith
  have h4 := h2 h3
  rw [div_le_div_iff_of_pos_right hp]
  exact_mod_cast h4

theorem ivl_N (c : Fin 53 × Fin 2) (h : ivlHi c ≤ 0) : ivlHi c ≤ (-413122735120 : ℝ) / 2 ^ 40 := by
  have h1 := List.all_eq_true.mp ivl_N_nat (finProdFinEquiv c : Fin (53 * 2))
    (List.mem_range.mpr (finProdFinEquiv c).2)
  have hp : (0 : ℝ) < 2 ^ 40 := by positivity
  have h2 := of_decide_eq_true h1
  unfold ivlHi hiF at h ⊢
  have h3 : ivlBN.getD (finProdFinEquiv c) 0 ≤ 0 := by
    by_contra hn
    have hn' : (0 : ℝ) < ((ivlBN.getD (finProdFinEquiv c) 0 : ℤ) : ℝ) := by exact_mod_cast not_le.mp hn
    have := div_pos hn' hp
    linarith
  have h4 := h2 h3
  rw [div_le_div_iff_of_pos_right hp]
  exact_mod_cast h4

theorem tmono {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ 1) :
    2 * u / (1 + u ^ 2) ≤ 2 * v / (1 + v ^ 2) := by
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_nonneg (sub_nonneg.mpr huv) (sub_nonneg.mpr (show u * v ≤ 1 by nlinarith))]

/-- The window `G_W` lies in the ordinary domains of the compact caps. -/
theorem hG_d : ∀ y, Gd y → (0 < y → y ∈ CapSource.ordDom Sign.pos) ∧
    (y < 0 → -y ∈ CapSource.ordDom Sign.neg) := by
  intro y ⟨hy1, hyU⟩
  obtain ⟨c, hc⟩ := mem_iUnion.mp hyU
  have hz := ivl_zero c
  have hy' := abs_le.mp hy1
  constructor
  · intro hy
    refine ⟨?_, hy'.2⟩
    by_contra hlt'
    have hlt'' := not_le.mp hlt'
    have ht0 : 0 < realCoordinateInv y := by unfold realCoordinateInv; positivity
    have hlo0 : 0 ≤ ivlLo c := by
      by_contra hn
      exact hz ⟨not_le.mp hn, ht0.trans hc.2⟩
    have h1 := ivl_P c hlo0
    have h2 := tmono hy.le hlt''.le (show (98749 / 1000000 : ℝ) ≤ 1 by norm_num)
    have h3 : 2 * (98749 / 1000000 : ℝ) / (1 + (98749 / 1000000) ^ 2) <
        (215054274947 : ℝ) / 2 ^ 40 := by norm_num
    have h4 := hc.1
    unfold realCoordinateInv at h4
    linarith
  · intro hy
    refine ⟨?_, by linarith [hy'.1]⟩
    by_contra hlt'
    have hlt'' := not_le.mp hlt'
    have ht0 : realCoordinateInv y < 0 := by
      unfold realCoordinateInv
      have : 2 * y < 0 := by linarith
      exact div_neg_of_neg_of_pos this (by positivity)
    have hhi0 : ivlHi c ≤ 0 := by
      by_contra hn
      exact hz ⟨hc.1.trans ht0, not_le.mp hn⟩
    have h1 := ivl_N c hhi0
    have h2 := tmono (show 0 ≤ -y by linarith) hlt''.le (show (19501 / 100000 : ℝ) ≤ 1 by norm_num)
    have h3 : 2 * (19501 / 100000 : ℝ) / (1 + (19501 / 100000) ^ 2) <
        (413122735120 : ℝ) / 2 ^ 40 := by norm_num
    have h4 := hc.2
    have h5 : realCoordinateInv y = -(2 * (-y) / (1 + (-y) ^ 2)) := by
      unfold realCoordinateInv; field_simp
    rw [h5] at h4
    have h6 : (-413122735120 : ℝ) / 2 ^ 40 = -((413122735120 : ℝ) / 2 ^ 40) := by ring
    linarith

end TopSec

/-! ### The data records and the terminal theorem

The design is `P58`, `ζ = 3/4`, `δ̂ = δc`, `G = Gd`, `σ = 33871/10^5`.  Each sheet record collects the
leaf certificates of one sheet in the exact type of its producer. -/

section Terminal
open CatalanMeasure.GenD.Signed.RouteI.IntervalNodesData CatalanMeasure.GenD.Signed.RouteI.ChordTableData

/-- `σ` of the design (`sigmaC`). -/
def sigQ : ℚ := 33871 / 100000

theorem cost_eq : 58 * costC = ((P58.n0 : ℕ) : ℝ) * ((c2Q : ℝ) + sigQ) := by
  norm_num [costC, sigmaC, c2Q, sigQ, P58]

theorem T296_tQ : T296 = (tQ : ℝ) := T296_eq'

theorem P58_gC0 : gC0 P58 = 6 / 29 := Analytic.Instances.d58_gC0
theorem P58_gC1 : gC1 P58 = 47 / 29 := Analytic.Instances.d58_gC1

/-- The first sheet (GP §9(e)): pieces, `wPq` checks and the record skeletons of the K = 24 trial. -/
structure FirstData where
  κ : ℕ
  A : Fin κ → ℚ
  B : Fin κ → ℚ
  hA0 : ∀ k, 0 ≤ A k
  hB1 : ∀ k, B k ≤ 1
  hAB : ∀ k, A k < B k
  hcov : ∀ α ∈ Icc (0 : ℝ) 1, ∃ k, (A k : ℝ) ≤ α ∧ α ≤ B k
  nC : Fin κ → QP
  fC : Fin κ → QP
  rs : Fin κ → QP
  η : ℚ
  hη : 0 < η
  hPoly : ∀ k, PolyNonneg (wPq sigQ η 0 (nC k) (fC k) (rs k) (rs k)) (A k) (B k)
  R : ∀ k, ∀ β ∈ Icc (A k : ℝ) (B k),
    FirstTrialBoundsEnd P58 ∅ (colCell P58 (3 / 4) β) (nodeD P58 δc) Gd (tQ : ℝ) ((c2Q : ℝ) + sigQ)
  hN : ∀ k β hβ, (R k β hβ).normCap ≤ evalQ (nC k) β
  hF : ∀ k β hβ, (R k β hβ).fieldCap ≤ evalQ (fC k) β
  hM : ∀ k β hβ, (R k β hβ).M₁ ≤ evalQ (rs k) β

theorem FirstData.sheet (D : FirstData) :
    FreeFirstBoundZ P58 Gd (3 / 4) δc T296 (58 * costC) := by
  rw [T296_tQ, cost_eq]
  exact firstSheet_of_pieces (P := P58) (Shape58.adm (P := P58)) P58_gC0 P58_gC1 (by norm_num)
    D.hη D.A D.B D.hA0 D.hB1 D.hAB D.hcov D.nC D.fC D.rs D.hPoly D.R D.hN D.hF D.hM

/-- The large sheet (GP §9(b)). -/
structure LargeData where
  κ : ℕ
  A : Fin κ → ℚ
  B : Fin κ → ℚ
  hA0 : ∀ k, (51 / 500 : ℝ) ≤ A k
  hB1 : ∀ k, B k ≤ 1
  hAB : ∀ k, A k < B k
  hcov : ∀ α ∈ Icc (51 / 500 : ℝ) 1, ∃ k, (A k : ℝ) ≤ α ∧ α ≤ B k
  nC : Fin κ → QP
  fC : Fin κ → QP
  rs : Fin κ → QP
  np : Fin κ → QP
  η : ℚ
  hη : 0 < η
  hPoly : ∀ k, PolyNonneg (wPq sigQ η 0 (nC k) (fC k) (rs k) (np k)) (A k) (B k)
  R : ∀ k, ∀ β ∈ Icc (A k : ℝ) (B k),
    SecondTrialBoundsEnd P58 ∅ (colCell P58 (3 / 4) β) (nodeD P58 δc) (tQ : ℝ) (evalQ (rs k) β)
      (evalQ (np k) β - Real.log 2) ((c2Q : ℝ) + sigQ) Gd
  hN : ∀ k β hβ, (R k β hβ).normCap ≤ evalQ (nC k) β
  hF : ∀ k β hβ, (R k β hβ).fieldCap ≤ evalQ (fC k) β

theorem LargeData.sheet (D : LargeData) :
    FreeLargeBoundZ P58 Gd (3 / 4) δc T296 (58 * costC) alpha296 := by
  rw [T296_tQ, cost_eq]
  have : alpha296 = (51 / 500 : ℝ) := rfl
  rw [this]
  exact largeSheet_of_pieces (P := P58) (Shape58.adm (P := P58)) P58_gC0 P58_gC1 (by norm_num) D.hη
    (by norm_num) D.A D.B D.hA0 D.hB1 D.hAB D.hcov D.nC D.fC D.rs D.np D.hPoly D.R D.hN D.hF

/-- The near sheet (GP §9(a), (c), (d)): the caps of the bundle, the K = 128 moves with their chord
caps, the signed and physical checks and the K = 40 record skeletons. -/
structure NearData where
  oc : Sign → ℝ
  nc : ℝ
  ho : ∀ σ, capSource.OrdCap Trunc.exact σ (nodeD P58 δc) Gd (oc σ)
  hn : capSource.NearCap Trunc.exact (nodeD P58 δc) Gd nc
  hoc : ∀ σ, oc σ ≤ -976 / 1000
  hnc : nc ≤ -976 / 1000
  ha : ∀ σ, capSource.AngCap Trunc.exact σ (kappa σ)
  da0 : ℕ → ℝ
  da1 : ℕ → ℝ
  dv0 : ℕ → ℝ
  dv1 : ℕ → ℝ
  K : ℕ
  ha0 : ∀ k, K ≤ k → da0 k = 0
  ha1 : ∀ k, K ≤ k → da1 k = 0
  hv0 : ∀ k, K ≤ k → dv0 k = 0
  hv1 : ∀ k, K ≤ k → dv1 k = 0
  l : SigLits
  hσ : l.σ = sigQ
  hI1 : anchorVal 0 + gasConst capSource ≤ l.I1
  hL0 : 2 * barrierInner (aT capSource 0) da0 + barrierInner (aV capSource 0) dv0 ≤ l.L0
  hL1 : 2 * barrierInner (aT capSource 0) da1 + barrierInner (aV capSource 0) dv1 ≤ l.L1
  hQ00 : barrierInner da0 da0 + barrierInner dv0 dv0 / 2 ≤ l.Q00
  hQ01 : barrierInner da0 da1 + barrierInner dv0 dv1 / 2 ≤ l.Q01
  hQ11 : barrierInner da1 da1 + barrierInner dv1 dv1 / 2 ≤ l.Q11
  R0 : ∀ x ∈ CapSource.rowDom, capSource.freeRow Trunc.exact 0 x + fRm da0 da1 dv0 dv1 0 x ≤ l.c0R
  R1 : ∀ x ∈ CapSource.rowDom, capSource.freeRow Trunc.exact 0 x + fRm da0 da1 dv0 dv1 1 x ≤ l.c1R
  C0 : ∀ s ∈ Ioo (0 : ℝ) 1, capSource.colField 0 s + fCm dv0 dv1 0 s ≤ l.c0C
  C1 : ∀ s ∈ Ioo (0 : ℝ) 1, capSource.colField 0 s + fCm dv0 dv1 1 s +
    (aeQ : ℝ) * Real.log (1 + (3 / 4) * s) ≤ l.c1C
  C2 : ∀ s ∈ Ioo (0 : ℝ) 1, capSource.colField 0 s + fCm dv0 dv1 1 s +
    (a1Q : ℝ) * Real.log (1 + (3 / 4) * s) ≤ l.c2C
  hη : 0 < l.η
  hP1 : PolyNonneg (sigP1 l) 0 aeQ
  hP2 : PolyNonneg (sigP2 l) aeQ a1Q
  κ : ℕ
  A : Fin κ → ℚ
  B' : Fin κ → ℚ
  hAB : ∀ j, A j < B' j
  hA0 : ∀ j, 0 ≤ A j
  hB1 : ∀ j, B' j ≤ a1Q
  hcovP : ∀ α ∈ Icc (0 : ℝ) (a1Q : ℝ), ∃ j, (A j : ℝ) ≤ α ∧ α ≤ B' j
  Δ : Fin κ → ℚ
  hΔ0 : ∀ j, 0 ≤ (Δ j : ℝ)
  nC : Fin κ → QP
  fC : Fin κ → QP
  rs : Fin κ → QP
  np : Fin κ → QP
  F0 : ℚ
  U : ℚ
  FU : ℚ
  p2 : ℚ
  du2 : ℚ
  s : Fin κ → ℚ
  s' : Fin κ → ℚ
  hF0 : (F0 : ℝ) = testF 0
  hPW : ∀ j, PolyNonneg (wPq l.σ l.η (Δ j) (nC j) (fC j) (rs j) (np j)) (A j) (B' j)
  hPφ : ∀ j, PolyNonneg (addQ [-l.η] (phiQ F0 U FU (s j))) (A j) (B' j)
  hPω : ∀ j, PolyNonneg (addQ [-l.η] (omQ p2 du2 (s' j))) (A j) (B' j)
  Rp : ∀ j, ∀ β ∈ Icc (A j : ℝ) (B' j), SecondTrialBoundsEnd P58 ∅ (colCell P58 (3 / 4) β)
    (nodeD P58 δc) ((tQ : ℝ) - Δ j) (evalQ (rs j) β) (evalQ (np j) β - Real.log 2)
    ((c2Q : ℝ) + l.σ) Gd
  hNp : ∀ j β hβ, (Rp j β hβ).normCap ≤ evalQ (nC j) β
  hFp : ∀ j β hβ, (Rp j β hβ).fieldCap ≤ evalQ (fC j) β
  hSp : ∀ j β hβ, (U : ℝ) + (β / a1Q) * FU ≤ ∑' k : ℕ, testT.F (k + 1) * (Rp j β hβ).p (k + 1)
  hp2p : ∀ j β hβ, (p2 : ℝ) + (β / a1Q) * du2 ≤ (Rp j β hβ).p 2
  hs : ∀ j, Real.sqrt (7877 / 10000 * ((Δ j : ℝ) / 2)) ≤ s j
  hs' : ∀ j, Real.sqrt (2 * ((Δ j : ℝ) / 2)) ≤ s' j
  hole : PhaseHole

theorem NearData.sheet (D : NearData) (Nd : ∀ (N m : ℕ), (Fin m → ℝ) → Prop) :
    FreeNearBoundZ P58 Gd Nd (3 / 4) δc T296 (58 * costC) alpha296 := by
  rw [T296_tQ]
  have e : 58 * costC = 58 * ((c2Q : ℝ) + D.l.σ) := by
    rw [D.hσ]; norm_num [costC, sigmaC, c2Q, sigQ]
  rw [e]
  have : alpha296 = (51 / 500 : ℝ) := rfl
  rw [this]
  let B := bundle0 (d := nodeD P58 δc) (G := Gd) (R := Classical.choose (row_cap_exists 0))
    (C := Classical.choose (col_cap_exists 0)) (nc := D.nc) (oc := D.oc)
    (Classical.choose_spec (row_cap_exists 0)) (Classical.choose_spec (col_cap_exists 0)) D.ho D.hn D.ha
  exact nearSheet_of_cells (P := P58) B (fun σ => le_rfl) le_rfl le_rfl
    (max_le (max_le (D.hoc _) (D.hoc _)) D.hnc) D.ha0 D.ha1 D.hv0 D.hv1 D.l D.hI1 D.hL0 D.hL1 D.hQ00
    D.hQ01 D.hQ11 (by norm_num) D.R0 D.R1 D.C0 D.C1 D.C2 hG_d P58_gC0 P58_gC1 D.hη D.hP1 D.hP2 D.A
    D.B' D.hAB D.hA0 D.hB1 D.hcovP D.Δ D.hΔ0 D.nC D.fC D.rs D.np D.F0 D.U D.FU D.p2 D.du2 D.s D.s' D.hF0
    D.hPW D.hPφ D.hPω D.Rp D.hNp D.hFp D.hSp D.hp2p D.hs D.hs' D.hole

/-- **μ(G) ≤ μ for any rational `μ ∈ [269.787, 400]`, from the data records.**  The stated value of the
design is `μ = 270`. -/
theorem measure_of_data (μ : ℚ) (hμ1 : (269787 / 1000 : ℝ) ≤ μ) (hμ2 : (μ : ℝ) ≤ 400)
    (F : FirstData) (Lg : LargeData) (Nr : NearData)
    (hcirc : ∀ z : ℂ, ‖z‖ = 3 / 4 →
      ((dc58.toParameters.h0 + dc58.toParameters.q0 : ℕ) : ℝ) * Real.log ‖(1 : ℂ) - z‖ +
        ivlL ivlLo ivlHi z ≤ 32506 / 10000)
    (hseg : ∀ x : ℝ, 3 / 4 ≤ |x| → |x| < 1 →
      ((dc58.toParameters.h0 + dc58.toParameters.q0 : ℕ) : ℝ) * Real.log ‖(1 : ℂ) - (x : ℂ)‖ +
        ivlL ivlLo ivlHi (x : ℂ) - 2 * (dc58.toParameters.g0 : ℝ) * Real.log (3 / 4) ≤ 32506 / 10000) :
    ∀ᶠ b : ℕ in atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-(μ : ℝ)) <
        |(∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) - a / b| :=
  measure_of_sheets μ hμ1 hμ2 hcirc hseg F.sheet (Nr.sheet _) Lg.sheet

theorem measure_270 (F : FirstData) (Lg : LargeData) (Nr : NearData)
    (hcirc : ∀ z : ℂ, ‖z‖ = 3 / 4 →
      ((dc58.toParameters.h0 + dc58.toParameters.q0 : ℕ) : ℝ) * Real.log ‖(1 : ℂ) - z‖ +
        ivlL ivlLo ivlHi z ≤ 32506 / 10000)
    (hseg : ∀ x : ℝ, 3 / 4 ≤ |x| → |x| < 1 →
      ((dc58.toParameters.h0 + dc58.toParameters.q0 : ℕ) : ℝ) * Real.log ‖(1 : ℂ) - (x : ℂ)‖ +
        ivlL ivlLo ivlHi (x : ℂ) - 2 * (dc58.toParameters.g0 : ℝ) * Real.log (3 / 4) ≤ 32506 / 10000) :
    ∀ᶠ b : ℕ in atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-(270 : ℝ)) <
        |(∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) - a / b| := by
  have h := measure_of_data 270 (by norm_num) (by norm_num) F Lg Nr hcirc hseg
  simpa using h

end Terminal

end
end CatalanMeasure.GenD.Signed.RouteI.TerminalC

#print axioms CatalanMeasure.GenD.Signed.RouteI.TerminalC.measure_270
#print axioms CatalanMeasure.GenD.Signed.RouteI.TerminalC.measure_of_data
#print axioms CatalanMeasure.GenD.Signed.RouteI.TerminalC.NearData.sheet
#print axioms CatalanMeasure.GenD.Signed.RouteI.TerminalC.FirstData.sheet
#print axioms CatalanMeasure.GenD.Signed.RouteI.TerminalC.LargeData.sheet
#print axioms CatalanMeasure.GenD.Signed.RouteI.TerminalC.hG_d
#print axioms CatalanMeasure.GenD.Signed.RouteI.TerminalC.hweights_d
#print axioms CatalanMeasure.GenD.Signed.RouteI.TerminalC.cmp_on_cell
