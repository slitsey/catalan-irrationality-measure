module

public import CatalanMeasure.GenD.Signed.RouteI.CompletedGasTangent
public import CatalanMeasure.GenD.Signed.RouteI.Wrappers

@[expose] public section
set_option Elab.async false

/-!
# Route I `Family`: the cell records and the family theorem (GP §8, Lemmas 8.0 to 8.2, Theorem 8.3)

The design family `P58 = ⟨58, 9, 3, 5, 3⟩` (moved here from `CompletedGasTangent`, GD4) and the
conversion of the cell records of `Analytic.First` / `Analytic.Second` (window `W`, column field
`Cf`, node correction `d = δ ∘ t / n₀`) into the three bounds the terminal assembly consumes, with
the column factor `Z = (∏ (1 + ζ s))^m` and the node field `δ`:

* `first_of_cells`  : `FreeFirstBoundZ` from first-case cell records (Lemma 8.2 + Theorem 8.3),
* `large_of_cells`  : `FreeLargeBoundZ` from second-case cell records,
* `near_of_cells`   : `SelectedFreeProductCostOnRestr` from per-cell selected bounds
  (`CompletedGas.selected_free_product`), hence `FreeNearBoundZ` through `Wrappers.hnear296`,
* `exists_net`      : Lemma 8.1, the finite net of cells.

Every quantity of the design (`ζ`, `δ`, `d`, the windows, `γ`) is a parameter.
-/

namespace CatalanMeasure.GenD.Signed.RouteI.Family

open CatalanMeasure.GenD CatalanMeasure.GenD.Analytic CatalanMeasure.Parametric
open CatalanMeasure.GenD.Signed.RouteI CatalanMeasure.GenD.Signed.RouteI.CompletedGas
open CatalanMeasure.GenD.Signed.PhysicalPick OAI.InternalCatalan
open Filter Set Finset
open scoped BigOperators

noncomputable section

/-- The design parameters `n = 58 N`, `b = 9 N`, `q = 3 N`, `g = 5 N`, `h = 3 N`. -/
abbrev P58 : Parameters := ⟨58, 9, 3, 5, 3⟩

theorem P58_admissible : Admissible P58 := by decide

instance : Shape58 P58 := ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The column field of a cell: the endpoint field plus `γ log (1 + ζ s)` (the factor
`Z = (∏ (1 + ζ s))^m` of the energy side, with `γ` at least the marked fraction). -/
def colCell (P : Parameters) (ζ γ : ℝ) : ℕ → ℝ → ℝ :=
  fun N u => populationEndpointColumnField P N 0 u + γ * Real.log (1 + ζ * u)

/-- The node correction `d = δ ∘ t / n₀` of the records. -/
def nodeD (P : Parameters) (δ : ℝ → ℝ) : ℝ → ℝ := fun u => δ (realCoordinateInv u) / (P.n0 : ℝ)

/-! ### Lemma 8.1: the finite net -/

/-- **GP Lemma 8.1.**  A continuous `F` that is `≤ rhs` on the diagonal of `[A, B]` is
`≤ rhs + ε` at the right end of a small enough cell of `[A, B]`: there is `n` such that every
`α ∈ [A, B]` lies in a cell `[a_i, b_i]` of the uniform partition with `F α b_i ≤ rhs α + ε`. -/
theorem exists_net {A B : ℝ} (hAB : A < B) {F : ℝ → ℝ → ℝ} {rhs : ℝ → ℝ}
    (hF : ContinuousOn (fun q : ℝ × ℝ => F q.1 q.2) (Icc A B ×ˢ Icc A B))
    (hdiag : ∀ α ∈ Icc A B, F α α ≤ rhs α) {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, 0 < n ∧ ∀ α ∈ Icc A B, ∃ i : ℕ, i < n ∧
      α ∈ Icc (A + (B - A) * i / n) (A + (B - A) * (i + 1) / n) ∧
      F α (A + (B - A) * (i + 1) / n) ≤ rhs α + ε := by
  have hK : IsCompact (Icc A B ×ˢ Icc A B) := isCompact_Icc.prod isCompact_Icc
  have huc := hK.uniformContinuousOn_of_continuous hF
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨η, hη, hu⟩ := huc ε hε
  obtain ⟨n, hn⟩ := exists_nat_gt ((B - A) / η)
  have hn0 : 0 < n := by
    have : 0 < (B - A) / η := div_pos (by linarith) hη
    exact_mod_cast this.trans hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  refine ⟨n, hn0, fun α hα => ?_⟩
  set h : ℝ := (B - A) / n with hh
  have hhpos : 0 < h := div_pos (by linarith) hnR
  have hhη : h < η := by
    rw [hh, div_lt_iff₀ hnR]
    have := (div_lt_iff₀ hη).mp hn
    linarith
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
  have hu_mem : A + h * (i + 1) ∈ Icc A B := by
    constructor
    · have : 0 ≤ h * ((i : ℝ) + 1) := by positivity
      linarith
    · have : ((i : ℝ) + 1) ≤ n := by exact_mod_cast hin
      have : h * ((i : ℝ) + 1) ≤ h * n := mul_le_mul_of_nonneg_left this hhpos.le
      have e : h * (n : ℝ) = B - A := by rw [hh]; field_simp
      linarith
  have hd : dist (α, α) (α, A + h * (i + 1)) < η := by
    rw [Prod.dist_eq]
    simp only [dist_self, Real.dist_eq]
    refine max_lt hη ?_
    rw [abs_of_nonpos (by linarith)]
    linarith
  have hk := hu (α, α) ⟨hα, hα⟩ (α, A + h * (i + 1)) ⟨hα, hu_mem⟩ hd
  rw [Real.dist_eq] at hk
  have hk2 := (abs_lt.mp hk).1
  refine ⟨i, hin, ?_, ?_⟩
  · rw [e0, e2]
    exact ⟨by linarith, by linarith⟩
  · rw [e2]
    have := hdiag α hα
    simp only at hk2
    linarith

/-! ### Lemma 8.2, first case, one cell -/

/-- **GP Lemma 8.2 / Theorem 8.3, first case, one cell.**  A first-case record with window `W`, column
field `colCell P ζ γ` (`γ` at least every fraction of `W`), node correction `nodeD P δ` and target
`t₀ ≥ target - ε/2` gives, for the configurations with `m / n ∈ W`, the factor-free first bound with
the column factor `Z = (∏ (1 + ζ s))^m` and the node field `δ`. -/
theorem first_cell {P : Parameters} (hP : Admissible P) {W : Set ℝ} {γ ζ : ℝ} (hζ : 0 ≤ ζ)
    (hWγ : ∀ α ∈ W, α ≤ γ) {δ : ℝ → ℝ} {G : ℝ → Prop} {t₀ target c : ℝ}
    (D : FirstTrialBoundsEnd P W (colCell P ζ γ) (nodeD P δ) G t₀ c) {ε : ℝ} (hε : 0 < ε)
    (ht : target - ε / 2 ≤ t₀) :
    ∀ᶠ N : ℕ in atTop, ∀ (p m : ℕ) (hpm : p + m = P.n N)
      (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ),
      (∀ i, x i ∈ Ioo (-1 : ℝ) 1) → (∀ i, x i ≠ 0) →
      (∀ j, y j ∈ Ioo (-1 : ℝ) 1) → (∀ j, y j ≠ 0) → (∀ j, G (y j)) →
      (∀ i, s i ∈ Ioo (0 : ℝ) 1) → Function.Injective x → Function.Injective s →
      (-1 < ∑ i : Fin (p + m), paramCaseField P N (Fin.append x y i)) →
      ((m : ℝ) / (P.n N : ℝ)) ∈ W →
      (∏ l, (1 + ζ * s l)) ^ m * markedSheetFree P N hpm x y s ≤
        ((3 / 2 : ℝ) ^ P.n N * (P.n N : ℝ) ^ ((P.n N : ℝ) / 2)) *
          Real.exp (((P.n0 : ℝ) * N) ^ 2 * (-target + Real.log 2 / 2 + ε) +
            ((P.n0 : ℝ) * c) * N * m - N * ∑ j, δ (realCoordinateInv (y j))) := by
  filter_upwards [first_energy_end hP D (δ := ε / 2) (by positivity),
    eventually_gt_atTop (0 : ℕ)]
    with N he hN p m hpm x y s hx hx0 hy hy0 hyG hs hxi hsi hcase hW
  have hz : ∀ i, Fin.append x y i ∈ Ioo (-1 : ℝ) 1 := by
    intro i
    exact Fin.addCases (fun j => by simpa using hx j) (fun j => by simpa using hy j) i
  have hz0 : ∀ i, Fin.append x y i ≠ 0 := by
    intro i
    exact Fin.addCases (fun j => by simpa using hx0 j) (fun j => by simpa using hy0 j) i
  have hp := populationOneProduct_pos hP hN hpm x y s hz hz0 hs hxi hsi
  have hc : ∀ j, 0 < |(rowCommonFactor P N).eval (realCoordinateInv (y j))| := by
    intro j
    apply abs_pos.mpr
    apply rowCommonFactor_eval_ne_zero_of P N
    · unfold realCoordinateInv
      exact div_ne_zero (mul_ne_zero (by norm_num) (hy0 j)) (by positivity)
    · exact (sub_pos.mp (one_sub_realCoordinateInv_pos (hy j))).ne
  have hcp : 0 < ∏ j, |(rowCommonFactor P N).eval (realCoordinateInv (y j))| :=
    prod_pos fun j _ => hc j
  have hlog := log_populationOneProduct_weighted hP hN hpm x y s hz hz0 hs hxi hsi
  have hval := he p m hpm x y s hx hx0 hy hy0 hyG hs hxi hsi hcase hW
  have hweq := weighted_one_value_eq (P := P) (N := N) x y s
  have hn : (P.n N : ℝ) = (P.n0 : ℝ) * N := n_cast P N
  have hn0 : (P.n0 : ℝ) ≠ 0 := (n0_pos hP).ne'
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hνpos : (0 : ℝ) < P.n N := by exact_mod_cast n_pos hP hN
  set V : ℝ := freePopulationValueWithFields (P.n N : ℝ) (populationPhysicalOneConstant P N p)
    (populationPhysicalOneFreeField P N)
    (fun u => populationPhysicalOneFixedField P N u - populationCommonLog P N u / (P.n N : ℝ))
    (populationEndpointColumnField P N 0) x y s with hV
  have hsplit : freePopulationValueWithFields (P.n N : ℝ) (populationPhysicalOneConstant P N p)
      (populationPhysicalOneFreeField P N)
      (fun u => populationPhysicalOneFixedField P N u - populationCommonLog P N u / (P.n N : ℝ)
        + nodeD P δ u) (colCell P ζ γ N) x y s =
      V + ((∑ j, nodeD P δ (y j)) + γ * ∑ i, Real.log (1 + ζ * s i)) / (P.n N : ℝ) := by
    rw [hV]
    unfold freePopulationValueWithFields colCell
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    ring
  rw [hsplit] at hval
  have hSpos : 0 < (∏ i, (1 + s i)) ^ m :=
    pow_pos (prod_pos fun i _ => by linarith [(hs i).1]) _
  have hZpos : 0 < (∏ i, (1 + ζ * s i)) ^ m :=
    pow_pos (prod_pos fun i _ => by have := mul_nonneg hζ (hs i).1.le; linarith) _
  have hprod : (∏ i, (1 + s i)) ^ m = Real.exp ((m : ℝ) * ∑ i, Real.log (1 + s i)) := by
    have hp' : 0 < ∏ i, (1 + s i) := prod_pos fun i _ => by linarith [(hs i).1]
    rw [← Real.exp_log (pow_pos hp' m), Real.log_pow,
      Real.log_prod (fun i _ => (show 0 < 1 + s i by linarith [(hs i).1]).ne')]
  have hprodZ : (∏ i, (1 + ζ * s i)) ^ m =
      Real.exp ((m : ℝ) * ∑ i, Real.log (1 + ζ * s i)) := by
    have hp' : 0 < ∏ i, (1 + ζ * s i) :=
      prod_pos fun i _ => by have := mul_nonneg hζ (hs i).1.le; linarith
    rw [← Real.exp_log (pow_pos hp' m), Real.log_pow,
      Real.log_prod (fun i _ => (show 0 < 1 + ζ * s i by
        have := mul_nonneg hζ (hs i).1.le; linarith).ne')]
  have hlogfm : Real.log (firstMarkedProduct P N hpm x y s) =
      (P.n N : ℝ) ^ 2 * V + (m : ℝ) * ∑ i, Real.log (1 + s i) := by
    have h1 : Real.log (firstMarkedProduct P N hpm x y s) =
        Real.log (populationOneProduct P N hpm x y s) -
          ∑ j, populationCommonLog P N (y j) := by
      rw [firstMarkedProduct, Real.log_div hp.ne' hcp.ne',
        Real.log_prod (fun j _ => (hc j).ne')]
      rfl
    rw [h1, hlog, hweq, mul_add]
    have hk : (P.n N : ℝ) ^ 2 * ((((m : ℝ) / (P.n N : ℝ)) * ∑ i, Real.log (1 + s i)) /
        (P.n N : ℝ)) = (m : ℝ) * ∑ i, Real.log (1 + s i) := by
      field_simp
    rw [hk]
  have hfm : firstMarkedProduct P N hpm x y s = (∏ i, (1 + s i)) ^ m *
      Real.exp ((P.n N : ℝ) ^ 2 * V) := by
    have hfpos : 0 < firstMarkedProduct P N hpm x y s := div_pos hp hcp
    rw [hprod, ← Real.exp_add, ← Real.exp_log hfpos, hlogfm]
    congr 1
    ring
  have hsheet := marked_sheet_product_first_le hP hN hpm x y s hx hx0 hy hy0 hs
  rw [markedSheetProduct_eq_pow_mul_free, hfm] at hsheet
  have hK : 0 ≤ (3 / 2 : ℝ) ^ P.n N * (P.n N : ℝ) ^ ((P.n N : ℝ) / 2) := by positivity
  have hfree : markedSheetFree P N hpm x y s ≤
      ((3 / 2 : ℝ) ^ P.n N * (P.n N : ℝ) ^ ((P.n N : ℝ) / 2)) *
        Real.exp ((P.n N : ℝ) ^ 2 * V) := by
    have h2 : (∏ i, (1 + s i)) ^ m * markedSheetFree P N hpm x y s ≤
        (∏ i, (1 + s i)) ^ m * (((3 / 2 : ℝ) ^ P.n N * (P.n N : ℝ) ^ ((P.n N : ℝ) / 2)) *
          Real.exp ((P.n N : ℝ) ^ 2 * V)) := by
      refine hsheet.trans (le_of_eq ?_)
      ring
    exact le_of_mul_le_mul_left h2 hSpos
  -- the exponent
  have hg0 : ∀ i, 0 ≤ Real.log (1 + ζ * s i) := fun i =>
    Real.log_nonneg (by have := mul_nonneg hζ (hs i).1.le; linarith)
  have hmγ : (m : ℝ) ≤ (P.n N : ℝ) * γ := by
    have := hWγ _ hW
    rw [div_le_iff₀ hνpos] at this
    linarith
  have hZm : (m : ℝ) * ∑ i, Real.log (1 + ζ * s i) ≤
      (P.n N : ℝ) * (γ * ∑ i, Real.log (1 + ζ * s i)) := by
    calc (m : ℝ) * ∑ i, Real.log (1 + ζ * s i)
        ≤ ((P.n N : ℝ) * γ) * ∑ i, Real.log (1 + ζ * s i) :=
          mul_le_mul_of_nonneg_right hmγ (Finset.sum_nonneg fun i _ => hg0 i)
      _ = _ := by ring
  have hbound := mul_le_mul_of_nonneg_left hval (sq_nonneg (P.n N : ℝ))
  have hid : (P.n N : ℝ) ^ 2 *
      (-t₀ + Real.log 2 / 2 + c * ((m : ℝ) / P.n N) + ε / 2) =
      ((P.n0 : ℝ) * N) ^ 2 * (-t₀ + Real.log 2 / 2 + ε / 2) + ((P.n0 : ℝ) * c) * N * m := by
    rw [hn]
    field_simp
    ring
  have hk2 : (P.n N : ℝ) ^ 2 * (((∑ j, nodeD P δ (y j)) +
      γ * ∑ i, Real.log (1 + ζ * s i)) / (P.n N : ℝ)) =
      (P.n N : ℝ) * (∑ j, nodeD P δ (y j)) +
        (P.n N : ℝ) * (γ * ∑ i, Real.log (1 + ζ * s i)) := by
    field_simp
  have hE : (P.n N : ℝ) * (∑ j, nodeD P δ (y j)) = (N : ℝ) * ∑ j, δ (realCoordinateInv (y j)) := by
    unfold nodeD
    rw [← Finset.sum_div, hn]
    field_simp
  rw [hid, mul_add, hk2] at hbound
  have hexp : (P.n N : ℝ) ^ 2 * V + (m : ℝ) * ∑ i, Real.log (1 + ζ * s i) ≤
      ((P.n0 : ℝ) * N) ^ 2 * (-target + Real.log 2 / 2 + ε) + ((P.n0 : ℝ) * c) * N * m -
        N * ∑ j, δ (realCoordinateInv (y j)) := by
    have hn2 : ((P.n0 : ℝ) * N) ^ 2 * (-t₀ + Real.log 2 / 2 + ε / 2) ≤
        ((P.n0 : ℝ) * N) ^ 2 * (-target + Real.log 2 / 2 + ε) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      linarith
    linarith only [hbound, hZm, hE, hn2]
  calc (∏ i, (1 + ζ * s i)) ^ m * markedSheetFree P N hpm x y s
      ≤ (∏ i, (1 + ζ * s i)) ^ m * (((3 / 2 : ℝ) ^ P.n N * (P.n N : ℝ) ^ ((P.n N : ℝ) / 2)) *
          Real.exp ((P.n N : ℝ) ^ 2 * V)) := mul_le_mul_of_nonneg_left hfree hZpos.le
    _ = ((3 / 2 : ℝ) ^ P.n N * (P.n N : ℝ) ^ ((P.n N : ℝ) / 2)) *
          Real.exp ((P.n N : ℝ) ^ 2 * V + (m : ℝ) * ∑ i, Real.log (1 + ζ * s i)) := by
        rw [hprodZ, Real.exp_add]
        ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) hK

/-! ### Lemma 8.2, second case, one cell -/

/-- **GP Lemma 8.2, second case, one cell** (the selected-sheet form of the large-`m` bound).  A
second-case record with window `W`, column field `colCell P ζ γ` and node correction
`nodeD P δ`, at a target `t₀ ≥ target - ε/2`, bounds the selected determinant with the column
factor `Z` for every configuration with `m / n ∈ W` and field sum `≤ -1` (no Pick window, no
comparison: the grouped energy is below the target on the whole window). -/
theorem selected_large_at {P : Parameters} (hP : Admissible P) {W : Set ℝ} {γ ζ : ℝ} (hζ : 0 ≤ ζ)
    (hWγ : ∀ α ∈ W, α ≤ γ) {δ : ℝ → ℝ} {G : ℝ → Prop} {t₀ target residual nearCap c' : ℝ}
    (D : SecondTrialBoundsEnd P W (colCell P ζ γ) (nodeD P δ) t₀ residual nearCap c' G)
    {ε : ℝ} (hε : 0 < ε) (ht : target - ε / 2 ≤ t₀) :
    ∀ᶠ N : ℕ in atTop, ∀ (p m : ℕ), p + m = P.n N →
      ∀ (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ),
      (∀ i, x i ∈ Ioo (-1 : ℝ) 1) → (∀ i, x i ≠ 0) →
      (∀ j, y j ∈ Ioo (-1 : ℝ) 1) → (∀ j, y j ≠ 0) → (∀ j, G (y j)) →
      (∀ i, s i ∈ Ioo (0 : ℝ) 1) →
      Function.Injective (Fin.append x y) → Function.Injective s →
      (∑ i : Fin (p + m), paramCaseField P N (Fin.append x y i)) ≤ -1 →
      ((m : ℝ) / (P.n N : ℝ)) ∈ W → ∀ sel : Fin (p + m) → Bool,
      (∏ l, (1 + ζ * s l)) ^ m * (selectedScalar P N x y s *
        |(selectedLaurent (P.g N) (Fin.append x y) (selectedRows x y sel)).det|) ≤
        selectedCap P target ((P.n0 : ℝ) * c') N m ε (N * ∑ j, δ (realCoordinateInv (y j))) := by
  filter_upwards [second_energy_end hP D (δ := ε / 2) (by positivity), eventually_ge_atTop 48]
    with N henergy hN48
  intro p m hpm x y s hx hx0 hy hy0 hG hs hinj hsi hcase hW sel
  obtain ⟨a, b, hab, eq, hnear, hinj2, hyb, hsheet⟩ :=
    selected_sheet_grouped hP hN48 hpm x y s hx hx0 hy hy0 hs hinj hcase sel
  have hcount : p + a + b = P.n N := by omega
  have hxi : Function.Injective x := fun i j h => by
    have h2 := @hinj2 (Fin.castAdd a i) (Fin.castAdd a j) (by simpa using h)
    exact Fin.castAdd_injective _ _ h2
  have hya : ∀ i, y (eq (Sum.inl i)) ∈ Ioo (-1 : ℝ) 1 := fun i => hy _
  have hNpos : 0 < N := by omega
  have hν : 0 < (P.n N : ℝ) := by exact_mod_cast n_pos hP hNpos
  have habR : (a : ℝ) + b = m := by exact_mod_cast hab
  have hn : (P.n N : ℝ) = (P.n0 : ℝ) * N := n_cast P N
  have hn0 : (P.n0 : ℝ) ≠ 0 := (n0_pos hP).ne'
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hNpos.ne'
  set α : ℝ := ((a + b : ℕ) : ℝ) / (P.n N : ℝ) with hαd
  have hαW : α ∈ W := by
    have h : ((a + b : ℕ) : ℝ) = m := by exact_mod_cast hab
    rw [hαd, h]
    exact hW
  have hval := henergy p a b hcount x (fun i => y (eq (Sum.inl i)))
    (fun i => y (eq (Sum.inr i))) s hx hx0 hya (fun i => hG _) hnear (fun i => hG _) hs hxi hinj2
    hyb hsi (by rw [← hαd]; exact hαW)
  -- from the cell column field to the `α`-field
  have hmono : groupedValueWithFields (P.n N : ℝ) (groupedConstant P N p a b)
        (populationPhysicalFreeField P N) (fun u => groupedMarkedField P N u + nodeD P δ u)
        (fun u => groupedNearField P N u + nodeD P δ u)
        (fun u => populationEndpointColumnField P N 0 u + α * Real.log (1 + ζ * u)) x
        (fun i => y (eq (Sum.inl i))) (fun i => y (eq (Sum.inr i))) s ≤
      groupedValueWithFields (P.n N : ℝ) (groupedConstant P N p a b)
        (populationPhysicalFreeField P N) (fun u => groupedMarkedField P N u + nodeD P δ u)
        (fun u => groupedNearField P N u + nodeD P δ u) (colCell P ζ γ N) x
        (fun i => y (eq (Sum.inl i))) (fun i => y (eq (Sum.inr i))) s := by
    unfold groupedValueWithFields colCell
    have hsum : ∑ i, (populationEndpointColumnField P N 0 (s i) + α * Real.log (1 + ζ * s i)) ≤
        ∑ i, (populationEndpointColumnField P N 0 (s i) + γ * Real.log (1 + ζ * s i)) :=
      Finset.sum_le_sum fun i _ => by
        have hg0 : 0 ≤ Real.log (1 + ζ * s i) :=
          Real.log_nonneg (by have := mul_nonneg hζ (hs i).1.le; linarith)
        have := mul_le_mul_of_nonneg_right (hWγ α hαW) hg0
        linarith
    have := div_le_div_of_nonneg_right hsum hν.le
    linarith
  have hV : groupedValueWithFields (P.n N : ℝ) (groupedConstant P N p a b)
        (populationPhysicalFreeField P N) (fun u => groupedMarkedField P N u + nodeD P δ u)
        (fun u => groupedNearField P N u + nodeD P δ u)
        (fun u => populationEndpointColumnField P N 0 u + α * Real.log (1 + ζ * u)) x
        (fun i => y (eq (Sum.inl i))) (fun i => y (eq (Sum.inr i))) s ≤
      -target + Real.log 2 / 2 + c' * α + ε := by
    linarith only [hmono, hval, ht]
  have hl := low_of_value hP hNpos hcount hζ hx hx0 hya hnear hs
    (fun i j h => hxi h) hinj2 hyb hsi hV
  have hPr : 0 < ∏ i, (1 + s i) := Finset.prod_pos fun i _ => by linarith [(hs i).1]
  have hPm : 0 < (∏ i, (1 + s i)) ^ m := pow_pos hPr _
  have hK : 0 ≤ (1 + 10 * Real.exp 12 * (P.n N : ℝ)) ^ P.n N := by positivity
  have hZ : 0 ≤ (∏ i, (1 + ζ * s i)) ^ m :=
    pow_nonneg (Finset.prod_nonneg fun i _ => by
      have := mul_nonneg hζ (hs i).1.le; linarith) _
  have hcost : (P.n0 : ℝ) * c' * N * ((a : ℝ) + b) = (P.n0 : ℝ) * c' * N * m := by
    rw [habR]
  have hEs : (P.n N : ℝ) * ((∑ i, nodeD P δ (y (eq (Sum.inl i)))) +
      ∑ i, nodeD P δ (y (eq (Sum.inr i)))) = (N : ℝ) * ∑ j, δ (realCoordinateInv (y j)) := by
    have h1 : ∑ j, nodeD P δ (y j) =
        (∑ i, nodeD P δ (y (eq (Sum.inl i)))) + ∑ i, nodeD P δ (y (eq (Sum.inr i))) := by
      rw [← Equiv.sum_comp eq, Fintype.sum_sum_type]
    rw [← h1]
    unfold nodeD
    rw [← Finset.sum_div, hn]
    field_simp
  rw [hcost, hEs, hab] at hl
  unfold selectedCap
  refine le_of_mul_le_mul_left ?_ hPm
  calc (∏ i, (1 + s i)) ^ m * ((∏ i, (1 + ζ * s i)) ^ m * (selectedScalar P N x y s *
        |(selectedLaurent (P.g N) (Fin.append x y) (selectedRows x y sel)).det|))
      = (∏ i, (1 + ζ * s i)) ^ m * ((∏ i, (1 + s i)) ^ m * (selectedScalar P N x y s *
        |(selectedLaurent (P.g N) (Fin.append x y) (selectedRows x y sel)).det|)) := by ring
    _ ≤ (∏ i, (1 + ζ * s i)) ^ m * ((1 + 10 * Real.exp 12 * (P.n N : ℝ)) ^ P.n N *
        groupedProduct P N x (fun i => y (eq (Sum.inl i))) (fun i => y (eq (Sum.inr i))) s) :=
      mul_le_mul_of_nonneg_left hsheet hZ
    _ = (1 + 10 * Real.exp 12 * (P.n N : ℝ)) ^ P.n N * ((∏ i, (1 + ζ * s i)) ^ m *
        groupedProduct P N x (fun i => y (eq (Sum.inl i))) (fun i => y (eq (Sum.inr i))) s) := by
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hl hK
    _ = _ := by ring

/-! ### Theorem 8.3: the family theorem -/

theorem frac_mem {P : Parameters} (hP : Admissible P) {N p m : ℕ} (hN : 0 < N)
    (hpm : p + m = P.n N) : ((m : ℝ) / (P.n N : ℝ)) ∈ Icc (0 : ℝ) 1 := by
  have hn : (0 : ℝ) < P.n N := by exact_mod_cast n_pos hP hN
  refine ⟨div_nonneg (Nat.cast_nonneg _) hn.le, ?_⟩
  rw [div_le_one hn]
  exact_mod_cast (by omega : m ≤ P.n N)

/-- **GP Theorem 8.3, first case.**  If for every `ε > 0` finitely many first-case cell records
(windows `W i` covering `[0, 1]`, column fields `colCell P ζ (γ i)` with `γ i` above the window,
targets `t₀ i ≥ target - ε/2`) exist, then `FreeFirstBoundZ` holds at cost `n₀ c`. -/
theorem first_of_cells {P : Parameters} (hP : Admissible P) {ζ : ℝ} (hζ : 0 ≤ ζ) {δ : ℝ → ℝ}
    {G : ℝ → Prop} {target c : ℝ}
    (hcells : ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (W : Fin n → Set ℝ) (γ t₀ : Fin n → ℝ),
      (∀ α ∈ Icc (0 : ℝ) 1, ∃ i, α ∈ W i) ∧ (∀ i, ∀ α ∈ W i, α ≤ γ i) ∧
      (∀ i, target - ε / 2 ≤ t₀ i) ∧
      ∀ i, Nonempty (FirstTrialBoundsEnd P (W i) (colCell P ζ (γ i)) (nodeD P δ) G (t₀ i) c)) :
    FreeFirstBoundZ P G ζ δ target ((P.n0 : ℝ) * c) := by
  intro ε hε
  obtain ⟨n, W, γ, t₀, hcov, hWγ, ht, hrec⟩ := hcells ε hε
  have hall := Filter.eventually_all.mpr
    (fun i : Fin n => first_cell hP hζ (hWγ i) (hrec i).some hε (ht i))
  filter_upwards [hall, eventually_gt_atTop (0 : ℕ)] with N hN hN0
  intro p m hpm x y s hx hx0 hy hy0 hyG hs hxi hsi hcase
  obtain ⟨i, hi⟩ := hcov _ (frac_mem hP hN0 hpm)
  exact hN i p m hpm x y s hx hx0 hy hy0 hyG hs hxi hsi hcase hi

/-- The unexpanded determinant of the selected sheet is `selectedLaurent`. -/
theorem selected_det_eq {P : Parameters} {N p m : ℕ} (x : Fin p → ℝ) (y : Fin m → ℝ)
    (sel : Fin (p + m) → Bool) :
    (Matrix.of fun i r : Fin (p + m) =>
        if sel i && (Fin.addCases (fun _ => false) (fun _ => true) i) &&
            decide (0 ≤ Fin.append x y i) then
          Fin.append x y i ^ ((r : ℤ) - P.g N)
        else actualLaurentEntry (P.g N) r (Fin.append x y i)) =
      selectedLaurent (P.g N) (Fin.append x y) (selectedRows x y sel) := by
  ext i r
  simp only [selectedLaurent, selectedRows, Matrix.of_apply, Finset.mem_filter,
    Finset.mem_univ, true_and]

/-- **GP Theorem 8.3, second case, large `m`.**  Cell records on windows covering `[α₁, 1]` give
`FreeLargeBoundZ` at cost `n₀ c'`. -/
theorem large_of_cells {P : Parameters} (hP : Admissible P) {ζ : ℝ} (hζ : 0 ≤ ζ) {δ : ℝ → ℝ}
    {G : ℝ → Prop} {target c' α₁ : ℝ}
    (hcells : ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (W : Fin n → Set ℝ) (γ t₀ residual nearCap : Fin n → ℝ),
      (∀ α ∈ Icc α₁ 1, ∃ i, α ∈ W i) ∧ (∀ i, ∀ α ∈ W i, α ≤ γ i) ∧
      (∀ i, target - ε / 2 ≤ t₀ i) ∧
      ∀ i, Nonempty (SecondTrialBoundsEnd P (W i) (colCell P ζ (γ i)) (nodeD P δ) (t₀ i)
        (residual i) (nearCap i) c' G)) :
    FreeLargeBoundZ P G ζ δ target ((P.n0 : ℝ) * c') α₁ := by
  refine hlarge296 hζ ?_
  intro ε hε
  obtain ⟨n, W, γ, t₀, residual, nearCap, hcov, hWγ, ht, hrec⟩ := hcells ε hε
  have hall := Filter.eventually_all.mpr
    (fun i : Fin n => selected_large_at hP hζ (hWγ i) (hrec i).some hε (ht i))
  filter_upwards [hall, eventually_gt_atTop (0 : ℕ)] with N hN hN0
  intro p m hpm x y s hx hx0 hy hy0 hyG hs hzi hsi hcase hQ sel
  have hα : ((m : ℝ) / (P.n N : ℝ)) ∈ Icc α₁ 1 := by
    obtain ⟨h0, h1⟩ := frac_mem hP hN0 hpm
    have hn : (0 : ℝ) < P.n N := by exact_mod_cast n_pos hP hN0
    exact ⟨by rw [le_div_iff₀ hn]; exact hQ, h1⟩
  obtain ⟨i, hi⟩ := hcov _ hα
  have := hN i p m hpm x y s hx hx0 hy hy0 hyG hs hzi hsi hcase hi sel
  rw [selected_det_eq (P := P) (N := N) x y sel]
  exact this

/-- Finitely many windows covering a class of configurations give the selected bound on the class
(the near sheet: each window is one cell of `CompletedGas.selected_free_product`). -/
theorem selected_of_cells {P : Parameters} {ζ : ℝ} {δ : ℝ → ℝ} {G : ℝ → Prop} {target cost : ℝ}
    {ι : Type*} (cells : Finset ι) (W : ι → Set ℝ)
    {Q : ∀ (N p m : ℕ), (Fin p → ℝ) → (Fin m → ℝ) → (Fin p → ℝ) → Prop}
    (hcov : ∀ N p m x y s, Q N p m x y s → ∃ i ∈ cells, ((m : ℝ) / (P.n N : ℝ)) ∈ W i)
    (h : ∀ i ∈ cells, SelectedFreeProductCostOnRestr P ζ δ target cost G
      (fun N p m x y s => Q N p m x y s ∧ ((m : ℝ) / (P.n N : ℝ)) ∈ W i)) :
    SelectedFreeProductCostOnRestr P ζ δ target cost G Q := by
  intro ε hε
  have hall := (Filter.eventually_all_finset cells).mpr (fun i hi => h i hi ε hε)
  filter_upwards [hall] with N hN
  intro p m hpm x y s hx hx0 hy hy0 hyG hs hzi hsi hcase hQ sel
  obtain ⟨i, hi, hW⟩ := hcov N p m x y s hQ
  exact hN i hi p m hpm x y s hx hx0 hy hy0 hyG hs hzi hsi hcase ⟨hQ, hW⟩ sel

end

end CatalanMeasure.GenD.Signed.RouteI.Family

#print axioms CatalanMeasure.GenD.Signed.RouteI.Family.exists_net
#print axioms CatalanMeasure.GenD.Signed.RouteI.Family.first_cell
#print axioms CatalanMeasure.GenD.Signed.RouteI.Family.selected_large_at
#print axioms CatalanMeasure.GenD.Signed.RouteI.Family.first_of_cells
#print axioms CatalanMeasure.GenD.Signed.RouteI.Family.large_of_cells
#print axioms CatalanMeasure.GenD.Signed.RouteI.Family.selected_of_cells
