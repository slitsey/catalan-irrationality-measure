module

public import CatalanMeasure.GenD.Signed.PhysicalPick
public import CatalanMeasure.GenD.Signed.RouteI.Wrappers
public import CatalanMeasure.GenD.Signed.Brackets
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.LinearAlgebra.Vandermonde
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import CatalanMeasure.GenD.Signed.RealPlace
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import CatalanMeasure.GenD.Signed.RouteI.CapFields
public import CatalanMeasure.FreePopulationFields
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import CatalanMeasure.GenD.Analytic.Fields
public import Mathlib.Analysis.Normed.Group.FunctionSeries

@[expose] public section




namespace CatalanMeasure.GenD.Signed.RouteI
open CatalanMeasure.GenD D58 Analytic Budget Filter Set Polynomial CatalanMeasure.Parametric
open OAI.InternalCatalan Finset
open CatalanMeasure.GenD.Signed.PhysicalPick
open scoped BigOperators
noncomputable section

/-- The actual scalar in front of the selected determinant. -/
def selectedScalar (P : Parameters) (N : ℕ) {p m : ℕ} (x : Fin p → ℝ) (y : Fin m → ℝ)
    (s : Fin p → ℝ) : ℝ :=
  (∏ j, paramRowNodeWeight P N (y j))*paramPinPrincipal P N x s /
    ∏ j, |(rowCommonFactor P N).eval (realCoordinateInv (y j))|

/-- The rows put on the second sheet by a selector. -/
def selectedRows {p m : ℕ} (x : Fin p → ℝ) (y : Fin m → ℝ) (sel : Fin (p+m) → Bool) :
    Finset (Fin (p+m)) :=
  Finset.univ.filter fun i =>
    (sel i && (Fin.addCases (fun _ => false) (fun _ => true) i) &&
      decide (0≤Fin.append x y i)) = true

/-- The common right side of the near-sheet bound.  `E` is the node field `N ∑_j δ(t(y_j))`
(GP §11.1); `E = 0` is the original cap. -/
def selectedCap (P : Parameters) (target cost : ℝ) (N m : ℕ) (ε E : ℝ) : ℝ :=
  (1+10*Real.exp 12*(P.n N:ℝ))^P.n N *
    Real.exp (((P.n0:ℝ)*N)^2*(-target+Real.log 2/2+ε)+cost*N*m - E)

/-- Low branch or physical Pick window, for every selector of every configuration, with the
cutoff before configurations. -/
def SelectedLowOrPick (P : Parameters) (ζ : ℝ) (δ : ℝ → ℝ) (target cost : ℝ) (G : ℝ → Prop)
    (Q : ∀ (N p m : ℕ), (Fin p → ℝ) → (Fin m → ℝ) → (Fin p → ℝ) → Prop) : Prop :=
  ∀ ε : ℝ, 0<ε → ∀ᶠ N : ℕ in atTop,
    ∀ (p m : ℕ), p+m=P.n N →
    ∀ (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ),
    (∀ i, x i ∈ Ioo (-1:ℝ) 1) → (∀ i, x i≠0) →
    (∀ j, y j ∈ Ioo (-1:ℝ) 1) → (∀ j, y j≠0) → (∀ j, G (y j)) →
    (∀ i, s i ∈ Ioo (0:ℝ) 1) →
    Function.Injective (Fin.append x y) → Function.Injective s →
    (∑ i : Fin (p+m), paramCaseField P N (Fin.append x y i))≤-1 →
    Q N p m x y s → ∀ sel : Fin (p+m) → Bool,
    (∏ l, (1 + ζ * s l)) ^ m * (selectedScalar P N x y s *
      |(selectedLaurent (P.g N) (Fin.append x y) (selectedRows x y sel)).det|) ≤
        selectedCap P target cost N m ε (N * ∑ j, δ (realCoordinateInv (y j))) ∨
    PickWindow (1/100) (p+m-1-2*P.g N) (Fin.append x y)

/-- The `w = 0` comparison bound on the Pick class. -/
def SelectedComparisonOnPick (P : Parameters) (ζ : ℝ) (δ : ℝ → ℝ) (target cost : ℝ)
    (G : ℝ → Prop)
    (Q : ∀ (N p m : ℕ), (Fin p → ℝ) → (Fin m → ℝ) → (Fin p → ℝ) → Prop) : Prop :=
  ∀ ε : ℝ, 0<ε → ∀ᶠ N : ℕ in atTop,
    ∀ (p m : ℕ), p+m=P.n N →
    ∀ (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ),
    (∀ i, x i ∈ Ioo (-1:ℝ) 1) → (∀ i, x i≠0) →
    (∀ j, y j ∈ Ioo (-1:ℝ) 1) → (∀ j, y j≠0) → (∀ j, G (y j)) →
    (∀ i, s i ∈ Ioo (0:ℝ) 1) →
    Function.Injective (Fin.append x y) → Function.Injective s →
    (∑ i : Fin (p+m), paramCaseField P N (Fin.append x y i))≤-1 →
    Q N p m x y s → ∀ sel : Fin (p+m) → Bool,
    PickWindow (1/100) (p+m-1-2*P.g N) (Fin.append x y) →
    (∏ l, (1 + ζ * s l)) ^ m * (selectedScalar P N x y s *
      |(comparisonLaurent (P.g N) (Fin.append x y) (selectedRows x y sel)).det|) ≤
        selectedCap P target cost N m ε (N * ∑ j, δ (realCoordinateInv (y j)))

theorem selectedCap_mono {P : Parameters} {target cost : ℝ} {N m : ℕ} {a b E : ℝ} (hab : a ≤ b) :
    selectedCap P target cost N m a E ≤ selectedCap P target cost N m b E := by
  unfold selectedCap
  gcongr

theorem selectedCap_absorb {P : Parameters} (hP : Admissible P) {target cost ε E : ℝ}
    (hε : 0 < ε) {N m : ℕ} (hN : 2 * Real.log 499 / ε ≤ (N:ℝ)) :
    (499:ℝ)^P.n N * selectedCap P target cost N m (ε/2) E ≤ selectedCap P target cost N m ε E := by
  have hn0 : (1:ℝ) ≤ (P.n0:ℝ) := by exact_mod_cast hP.1
  have hlog : 0 < Real.log 499 := Real.log_pos (by norm_num)
  have hNpos : 0 ≤ (N:ℝ) := Nat.cast_nonneg N
  set n : ℝ := (P.n0:ℝ)*N with hn
  have hnN : (N:ℝ) ≤ n := by rw [hn]; nlinarith
  have hcast : (P.n N : ℝ) = n := by simp [Parameters.n, hn]
  have hlog2 : Real.log 499 ≤ n * (ε/2) := by
    have h1 : 2 * Real.log 499 ≤ (N:ℝ) * ε := (div_le_iff₀ hε).mp hN
    have h2 : (N:ℝ) * ε ≤ n * ε := by gcongr
    linarith
  have hn0' : 0 ≤ n := hNpos.trans hnN
  have hpow : (499:ℝ)^P.n N ≤ Real.exp (n^2 * (ε/2)) := by
    rw [← Real.rpow_natCast, hcast, Real.rpow_def_of_pos (by norm_num)]
    apply Real.exp_le_exp.mpr
    nlinarith
  unfold selectedCap
  rw [← hn]
  have hexp : Real.exp (n^2*(-target+Real.log 2/2+ε)+cost*N*m - E) =
      Real.exp (n^2 * (ε/2)) * Real.exp (n^2*(-target+Real.log 2/2+ε/2)+cost*N*m - E) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hexp]
  calc (499:ℝ)^P.n N * ((1+10*Real.exp 12*(P.n N:ℝ))^P.n N *
        Real.exp (n^2*(-target+Real.log 2/2+ε/2)+cost*N*m - E))
      ≤ Real.exp (n^2 * (ε/2)) * ((1+10*Real.exp 12*(P.n N:ℝ))^P.n N *
        Real.exp (n^2*(-target+Real.log 2/2+ε/2)+cost*N*m - E)) := by gcongr
    _ = _ := by ring

/-- **Terminal branch assembly.** The two branch predicates give exactly the consumer of
`hnear296`. The cutoff is chosen before configurations and selectors. -/
theorem selectedFree_of_lowOrPick {P : Parameters} (hP : Admissible P) {target cost ζ : ℝ}
    {δ : ℝ → ℝ} (hζ : 0 ≤ ζ) {G : ℝ → Prop}
    {Q : ∀ (N p m : ℕ), (Fin p → ℝ) → (Fin m → ℝ) → (Fin p → ℝ) → Prop}
    (hlow : SelectedLowOrPick P ζ δ target cost G Q)
    (hcmp : SelectedComparisonOnPick P ζ δ target cost G Q) :
    SelectedFreeProductCostOnRestr P ζ δ target cost G Q := by
  intro ε hε
  have hε2 : 0 < ε/2 := by positivity
  filter_upwards [hlow (ε/2) hε2, hcmp (ε/2) hε2,
    eventually_ge_atTop (⌈2 * Real.log 499 / ε⌉₊), eventually_ge_atTop 1] with N h1 h2 hN hN1
  intro p m hpm x y s hx hx0 hy hy0 hyG hs hzi hsi hcase hQ sel
  have hNr : 2 * Real.log 499 / ε ≤ (N:ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hN)
  have hw : 0 ≤ selectedScalar P N x y s := by
    unfold selectedScalar
    exact div_nonneg (mul_nonneg
      (prod_nonneg fun i _ => paramRowNodeWeight_nonneg P N (hy i))
      (paramPinPrincipal_nonneg P N x s hx hs))
      (prod_nonneg fun i _ => abs_nonneg _)
  have hmat : (Matrix.of fun i r : Fin (p+m) =>
        if sel i && (Fin.addCases (fun _ => false) (fun _ => true) i) &&
            decide (0≤Fin.append x y i) then
          Fin.append x y i ^ ((r:ℤ)-P.g N)
        else actualLaurentEntry (P.g N) r (Fin.append x y i)) =
      selectedLaurent (P.g N) (Fin.append x y) (selectedRows x y sel) := by
    ext i r
    simp only [selectedLaurent, selectedRows, Matrix.of_apply, Finset.mem_filter,
      Finset.mem_univ, true_and]
  have hZ : 0 ≤ (∏ l, (1 + ζ * s l)) ^ m :=
    pow_nonneg (prod_nonneg fun i _ => by nlinarith [(hs i).1, (hs i).2]) _
  have hgoal : (∏ l, (1 + ζ * s l)) ^ m * (selectedScalar P N x y s *
      |(selectedLaurent (P.g N) (Fin.append x y) (selectedRows x y sel)).det|) ≤
        selectedCap P target cost N m ε (N * ∑ j, δ (realCoordinateInv (y j))) := by
    rcases h1 p m hpm x y s hx hx0 hy hy0 hyG hs hzi hsi hcase hQ sel with hl | hpick
    · exact hl.trans (selectedCap_mono (by linarith))
    · have hg : 2 * P.g N + 1 ≤ p + m := by
        rw [hpm]
        have h2 : (2 * P.g0 + 1) * N ≤ P.n0 * N :=
          Nat.mul_le_mul_right N (Nat.succ_le_of_lt hP.2.2.2.2)
        have h3 : (2 * P.g0 + 1) * N = 2 * (P.g0 * N) + N := by ring
        simp only [Parameters.n, Parameters.g]
        omega
      have hz0 : ∀ i : Fin (p+m), Fin.append x y i ≠ 0 := fun i =>
        Fin.addCases (fun j => by simpa using hx0 j) (fun j => by simpa using hy0 j) i
      have hz1 : ∀ i : Fin (p+m), |Fin.append x y i| < 1 := fun i =>
        Fin.addCases (fun j => by simpa using abs_lt.mpr (hx j))
          (fun j => by simpa using abs_lt.mpr (hy j)) i
      have hc := selected_laurent_comparison hg (Fin.append x y) hzi hz0 hz1 hpick
        (selectedRows x y sel)
      have h3 := h2 p m hpm x y s hx hx0 hy hy0 hyG hs hzi hsi hcase hQ sel hpick
      calc (∏ l, (1 + ζ * s l)) ^ m * (selectedScalar P N x y s *
            |(selectedLaurent (P.g N) (Fin.append x y) (selectedRows x y sel)).det|)
          ≤ (∏ l, (1 + ζ * s l)) ^ m * (selectedScalar P N x y s * ((499:ℝ)^(p+m) *
            |(comparisonLaurent (P.g N) (Fin.append x y) (selectedRows x y sel)).det|)) := by
            gcongr
        _ = (499:ℝ)^(p+m) * ((∏ l, (1 + ζ * s l)) ^ m * (selectedScalar P N x y s *
            |(comparisonLaurent (P.g N) (Fin.append x y) (selectedRows x y sel)).det|)) := by ring
        _ ≤ (499:ℝ)^(p+m) * selectedCap P target cost N m (ε/2)
              (N * ∑ j, δ (realCoordinateInv (y j))) := by gcongr
        _ ≤ selectedCap P target cost N m ε (N * ∑ j, δ (realCoordinateInv (y j))) := by
            rw [hpm]; exact selectedCap_absorb hP hε hNr
  rw [hmat]
  exact hgoal

end
end CatalanMeasure.GenD.Signed.RouteI





/-!
The selected sheet against the grouped product.  The theorems `marked_partition_prod` to
`marked_selected_sheet_le_grouped` are the proofs of `Analytic/MarkedSecond.lean`, where they are
private; the copy here leaves that module untouched.
-/

namespace CatalanMeasure.GenD.Signed.RouteI.CompletedGas

open CatalanMeasure.GenD CatalanMeasure.GenD.Analytic
open CatalanMeasure.Parametric OAI.InternalCatalan Set Finset Filter
open CatalanMeasure.GenD.Signed.PhysicalPick
open scoped BigOperators Topology

noncomputable section

theorem marked_partition_prod {m a b : ℕ} (e : Fin a ⊕ Fin b ≃ Fin m)
    (f : Fin m → ℝ) :
    (∏ i, f i) = (∏ i : Fin a, f (e (Sum.inl i))) *
      (∏ i : Fin b, f (e (Sum.inr i))) := by
  calc
    _ = ∏ i : Fin a ⊕ Fin b, f (e i) :=
      (Fintype.prod_equiv e (fun i => f (e i)) f (fun _ => rfl)).symm
    _ = _ := by rw [Fintype.prod_sum_type]

theorem marked_partition_sum {m a b : ℕ} (e : Fin a ⊕ Fin b ≃ Fin m)
    (f : Fin m → ℝ) :
    (∑ i, f i) = (∑ i : Fin a, f (e (Sum.inl i))) +
      (∑ i : Fin b, f (e (Sum.inr i))) := by
  calc
    _ = ∑ i : Fin a ⊕ Fin b, f (e i) :=
      (Fintype.sum_equiv e (fun i => f (e i)) f (fun _ => rfl)).symm
    _ = _ := by rw [Fintype.sum_sum_type]

def marked_selection_equiv {p m a b : ℕ} (e : Fin a ⊕ Fin b ≃ Fin m) :
    Fin (p + a) ⊕ Fin b ≃ Fin (p + m) :=
  ((Equiv.sumCongr finSumFinEquiv.symm (Equiv.refl (Fin b))).trans
    (Equiv.sumAssoc (Fin p) (Fin a) (Fin b))).trans
      ((Equiv.sumCongr (Equiv.refl (Fin p)) e).trans finSumFinEquiv)

theorem marked_selection_nodes {p m a b : ℕ} (e : Fin a ⊕ Fin b ≃ Fin m)
    (x : Fin p → ℝ) (y : Fin m → ℝ) :
    (fun j : Fin (p + a + b) =>
      Fin.append x y (marked_selection_equiv e (finSumFinEquiv.symm j))) =
      Fin.append (Fin.append x (fun i => y (e (Sum.inl i))))
        (fun i => y (e (Sum.inr i))) := by
  funext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · refine Fin.addCases (fun k => ?_) (fun k => ?_) i <;>
      simp [marked_selection_equiv]
  · simp [marked_selection_equiv]

theorem marked_selection_left {p m a b : ℕ} (e : Fin a ⊕ Fin b ≃ Fin m)
    (t : Fin m → Bool) (hleft : ∀ i, t (e (Sum.inl i)) = false) :
    ∀ i : Fin (p + a),
      Fin.addCases (fun _ => false) t (marked_selection_equiv e (Sum.inl i)) = false := by
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simp [marked_selection_equiv, hleft]

theorem marked_selection_right {p m a b : ℕ} (e : Fin a ⊕ Fin b ≃ Fin m)
    (t : Fin m → Bool) (hright : ∀ i, t (e (Sum.inr i)) = true) :
    ∀ i : Fin b,
      Fin.addCases (fun _ => false) t (marked_selection_equiv (p := p) e (Sum.inr i)) = true := by
  intro i
  simp [marked_selection_equiv, hright]

theorem marked_selection_actual_nodes {p m a b : ℕ}
    (e : Fin a ⊕ Fin b ≃ Fin m) (x : Fin p → ℝ) (y : Fin m → ℝ) :
    (fun i : Fin (p + a) => Fin.append x y (marked_selection_equiv e (Sum.inl i))) =
      Fin.append x (fun i => y (e (Sum.inl i))) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simp [marked_selection_equiv]

theorem marked_selection_near_nodes {p m a b : ℕ}
    (e : Fin a ⊕ Fin b ≃ Fin m) (x : Fin p → ℝ) (y : Fin m → ℝ) :
    (fun i : Fin b => Fin.append x y (marked_selection_equiv e (Sum.inr i))) =
      (fun i => y (e (Sum.inr i))) := by
  funext i
  simp [marked_selection_equiv]

theorem marked_sheet_weight_prod {P : Parameters} (hP : Admissible P)
    {N m : ℕ} (hN : 0 < N) (y : Fin m → ℝ)
    (hy : ∀ i, y i ∈ Ioo (-1 : ℝ) 1) (hy0 : ∀ i, y i ≠ 0) :
    (∏ i, |y i| ^ ((P.g N : ℤ) - (P.n N - 1 : ℕ))) *
        (∏ i, paramRowNodeWeight P N (y i)) =
      (∏ i, |(rowCommonFactor P N).eval (realCoordinateInv (y i))|) *
        (∏ i, markedSheetWeight P N (y i)) := by
  rw [← prod_mul_distrib, ← prod_mul_distrib]
  apply prod_congr rfl
  intro i _
  exact marked_sheet_weight_cancellation hP hN (hy i) (hy0 i)

def marked_sheet_scalar (P : Parameters) (N : ℕ) {p m : ℕ}
    (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ) : ℝ :=
  (∏ i, (1 + s i)) ^ m * (∏ j, paramRowNodeWeight P N (y j)) *
    paramPinPrincipal P N x s /
      ∏ j, |(rowCommonFactor P N).eval (realCoordinateInv (y j))|

theorem marked_grouped_majorant_product {P : Parameters} (hP : Admissible P)
    {N p m a b : ℕ} (hN : 0 < N) (hpm : p + m = P.n N) (hab : a + b = m)
    (e : Fin a ⊕ Fin b ≃ Fin m) (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ)
    (hy : ∀ i, y i ∈ Ioo (-1 : ℝ) 1) (hy0 : ∀ i, y i ≠ 0) :
    marked_sheet_scalar P N x y s * groupedLaurentMajorant (p := p + a) (q := b)
      (Fin.append (Fin.append x (fun i => y (e (Sum.inl i))))
        (fun i => y (e (Sum.inr i)))) (P.g N) =
      (1 + 10 * Real.exp 12 * (P.n N : ℝ)) ^ (p + a) *
        groupedProduct P N x (fun i => y (e (Sum.inl i)))
          (fun i => y (e (Sum.inr i))) s := by
  have hcount : p + a + b = P.n N := by omega
  have hc : (∏ j, |(rowCommonFactor P N).eval (realCoordinateInv (y j))|) ≠ 0 := by
    apply prod_ne_zero_iff.mpr
    intro j _
    apply abs_ne_zero.mpr
    apply rowCommonFactor_eval_ne_zero_of P N
    · unfold realCoordinateInv
      exact div_ne_zero (mul_ne_zero (by norm_num) (hy0 j)) (by positivity)
    · exact (sub_pos.mp (one_sub_realCoordinateInv_pos (hy j))).ne
  have hcan := marked_sheet_weight_prod hP hN y hy hy0
  have hratio :
      (∏ j, |y j| ^ ((P.g N : ℤ) - (P.n N - 1 : ℕ))) *
          (∏ j, paramRowNodeWeight P N (y j)) /
            (∏ j, |(rowCommonFactor P N).eval (realCoordinateInv (y j))|) =
        ∏ j, markedSheetWeight P N (y j) := by
    apply (div_eq_iff hc).mpr
    simpa [mul_comm] using hcan
  have hpow := marked_partition_prod e
    (fun j => |y j| ^ ((P.g N : ℤ) - (P.n N - 1 : ℕ)))
  have hmarked := marked_partition_prod e (fun j => markedSheetWeight P N (y j))
  let pair := groupedPairProduct (Fin.append x (fun i => y (e (Sum.inl i))))
    (fun i => y (e (Sum.inr i)))
  calc
    _ = (1 + 10 * Real.exp 12 * (P.n N : ℝ)) ^ (p + a) *
        ((∏ i, (1 + s i)) ^ (a + b) *
          (∏ i, |x i| ^ ((P.g N : ℤ) - (P.n N - 1 : ℕ))) *
          ((∏ j, |y j| ^ ((P.g N : ℤ) - (P.n N - 1 : ℕ))) *
            (∏ j, paramRowNodeWeight P N (y j)) /
              (∏ j, |(rowCommonFactor P N).eval (realCoordinateInv (y j))|)) *
          (∏ j : Fin b, |y (e (Sum.inr j))| ^ (P.n N - 1 - 2 * P.g N)) *
          pair * paramPinPrincipal P N x s) := by
      unfold marked_sheet_scalar groupedLaurentMajorant pair groupedPairProduct
      simp only [Fin.prod_univ_add, Fin.append_left, Fin.append_right, hcount]
      rw [hpow, hab]
      ring
    _ = _ := by
      rw [hratio, hmarked]
      unfold groupedProduct pair
      rw [prod_mul_distrib]
      ring

theorem marked_selected_sheet_le_grouped {P : Parameters} (hP : Admissible P)
    {N p m a b : ℕ} (hN : 0 < N) (hpm : p + m = P.n N) (hab : a + b = m)
    (e : Fin a ⊕ Fin b ≃ Fin m) (t : Fin m → Bool)
    (hleft : ∀ i, t (e (Sum.inl i)) = false)
    (hright : ∀ i, t (e (Sum.inr i)) = true)
    (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ)
    (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) (hx0 : ∀ i, x i ≠ 0)
    (hy : ∀ i, y i ∈ Ioo (-1 : ℝ) 1) (hy0 : ∀ i, y i ≠ 0)
    (hs : ∀ i, s i ∈ Ioo (0 : ℝ) 1)
    (hzi : Function.Injective (Fin.append x y))
    (hn48 : 48 ≤ P.n N) (hng : 2 * P.g N + 1 < P.n N)
    (hweight : (∑ i : Fin (p + m), blaschkeWeight (Fin.append x y i)) ≤
      ((P.n N - 1 - 2 * P.g N : ℕ) : ℝ)) :
    marked_sheet_scalar P N x y s *
      |(Matrix.of fun i r : Fin (p + m) =>
        if (Fin.addCases (fun _ => false) t i : Bool) then
          Fin.append x y i ^ ((r : ℤ) - P.g N)
        else actualLaurentEntry (P.g N) r (Fin.append x y i)).det| ≤
      (1 + 10 * Real.exp 12 * (P.n N : ℝ)) ^ P.n N *
        groupedProduct P N x (fun i => y (e (Sum.inl i)))
          (fun i => y (e (Sum.inr i))) s := by
  have hcount : p + a + b = p + m := by omega
  have htotal : p + a + b = P.n N := by omega
  have hz : ∀ i : Fin (p + m), Fin.append x y i ∈ Ioo (-1 : ℝ) 1 := by
    intro i
    exact Fin.addCases (fun j => by simpa using hx j) (fun j => by simpa using hy j) i
  have hz0 : ∀ i : Fin (p + m), Fin.append x y i ≠ 0 := by
    intro i
    exact Fin.addCases (fun j => by simpa using hx0 j) (fun j => by simpa using hy0 j) i
  have hwnear : 0 ≤ ∑ j : Fin b, blaschkeWeight (y (e (Sum.inr j))) := by
    apply sum_nonneg
    intro j _
    unfold blaschkeWeight
    apply div_nonneg
    · have h1 : 0 < (1 - y (e (Sum.inr j))) * (1 + y (e (Sum.inr j))) :=
        mul_pos (sub_pos.mpr (hy _).2) (by linarith [(hy (e (Sum.inr j))).1])
      nlinarith
    · positivity
  have hsplit :
      (∑ i : Fin (p + a), blaschkeWeight
        (Fin.append x (fun j => y (e (Sum.inl j))) i)) +
      (∑ j : Fin b, blaschkeWeight (y (e (Sum.inr j)))) =
        ∑ i : Fin (p + m), blaschkeWeight (Fin.append x y i) := by
    simp only [Fin.sum_univ_add, Fin.append_left, Fin.append_right]
    rw [marked_partition_sum e (fun j => blaschkeWeight (y j))]
    ring
  have hwactual : (∑ i : Fin (p + a), blaschkeWeight
      (Fin.append x (fun j => y (e (Sum.inl j))) i)) ≤
        ((p + a + b - 1 - 2 * P.g N : ℕ) : ℝ) := by
    rw [htotal]
    linarith
  have hactual : ∀ i : Fin (p + a),
      Fin.append x y (marked_selection_equiv e (Sum.inl i)) =
        Fin.append x (fun j => y (e (Sum.inl j))) i :=
    fun i => congrFun (marked_selection_actual_nodes e x y) i
  have hdet := selected_laurent_det_bound (g := P.g N) hcount (Fin.append x y)
    (Fin.addCases (fun _ => false) t) (marked_selection_equiv e)
    (marked_selection_left e t hleft) (marked_selection_right e t hright)
    (by omega) (by omega) hz0 (fun i => abs_lt.mpr (hz i)) hzi
    (by simpa only [hactual] using hwactual)
  rw [marked_selection_nodes] at hdet
  have hscalar : 0 ≤ marked_sheet_scalar P N x y s := by
    unfold marked_sheet_scalar
    exact div_nonneg (mul_nonneg (mul_nonneg
      (pow_nonneg (prod_nonneg fun i _ => by linarith [(hs i).1]) _)
      (prod_nonneg fun i _ => paramRowNodeWeight_nonneg P N (hy i)))
      (paramPinPrincipal_nonneg P N x s hx hs))
      (prod_nonneg fun i _ => abs_nonneg _)
  have hG : 0 ≤ groupedProduct P N x (fun i => y (e (Sum.inl i)))
      (fun i => y (e (Sum.inr i))) s := by
    have hcross : 0 ≤ crossCauchyProduct
        (Fin.append x (fun i => y (e (Sum.inl i)))) (fun i => y (e (Sum.inr i))) :=
      (crossCauchyProduct_pos _ _
        (fun i => Fin.addCases (fun j => by simpa using abs_lt.mpr (hx j))
          (fun j => by simpa using abs_lt.mpr (hy (e (Sum.inl j)))) i)
        (fun i => abs_lt.mpr (hy _))).le
    have hS : 0 ≤ (∏ i, (1 + s i)) ^ (a + b) :=
      pow_nonneg (prod_nonneg fun i _ => by linarith [(hs i).1]) _
    have hZ : 0 ≤ ∏ i, |x i| ^ ((P.g N : ℤ) - (P.n N - 1 : ℕ)) :=
      prod_nonneg fun i _ => zpow_nonneg (abs_nonneg _) _
    have hX : 0 ≤ ∏ i : Fin a, markedSheetWeight P N (y (e (Sum.inl i))) :=
      prod_nonneg fun i _ => (markedSheetWeight_pos P N _).le
    have hY : 0 ≤ ∏ i : Fin b, markedSheetWeight P N (y (e (Sum.inr i))) *
        |y (e (Sum.inr i))| ^ (P.n N - 1 - 2 * P.g N) :=
      prod_nonneg fun i _ => mul_nonneg (markedSheetWeight_pos P N _).le
        (pow_nonneg (abs_nonneg _) _)
    have hPair : 0 ≤ groupedPairProduct
        (Fin.append x (fun i => y (e (Sum.inl i)))) (fun i => y (e (Sum.inr i))) :=
      mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hcross
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hS hZ) hX) hY)
      hPair) (paramPinPrincipal_nonneg P N x s hx hs)
  calc
    _ ≤ marked_sheet_scalar P N x y s *
        groupedLaurentMajorant (p := p + a) (q := b)
          (Fin.append (Fin.append x (fun i => y (e (Sum.inl i))))
            (fun i => y (e (Sum.inr i)))) (P.g N) :=
      mul_le_mul_of_nonneg_left hdet hscalar
    _ = (1 + 10 * Real.exp 12 * (P.n N : ℝ)) ^ (p + a) *
        groupedProduct P N x (fun i => y (e (Sum.inl i)))
          (fun i => y (e (Sum.inr i))) s :=
      marked_grouped_majorant_product hP hN hpm hab e x y s hy hy0
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by
        have hh : 0 ≤ 10 * Real.exp 12 * (P.n N : ℝ) := by positivity
        linarith) (by omega : p + a ≤ P.n N)) hG

/-- The selected determinant against the grouped product of its own near split. -/
theorem selected_sheet_grouped {P : Parameters} (hP : CatalanMeasure.Parametric.Admissible P)
    {N p m : ℕ} (hN : 48 ≤ N) (hpm : p + m = P.n N)
    (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ)
    (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) (hx0 : ∀ i, x i ≠ 0)
    (hy : ∀ i, y i ∈ Ioo (-1 : ℝ) 1) (hy0 : ∀ i, y i ≠ 0)
    (hs : ∀ i, s i ∈ Ioo (0 : ℝ) 1)
    (hzi : Function.Injective (Fin.append x y))
    (hcase : (∑ i : Fin (p + m), paramCaseField P N (Fin.append x y i)) ≤ -1)
    (sel : Fin (p + m) → Bool) :
    ∃ (a b : ℕ) (_ : a + b = m) (e : Fin a ⊕ Fin b ≃ Fin m),
      (∀ i, y (e (Sum.inr i)) ∈ Ioo (0 : ℝ) 1) ∧
      Function.Injective (Fin.append x (fun i => y (e (Sum.inl i)))) ∧
      Function.Injective (fun i => y (e (Sum.inr i))) ∧
      (∏ i, (1 + s i)) ^ m * (selectedScalar P N x y s *
        |(selectedLaurent (P.g N) (Fin.append x y) (selectedRows x y sel)).det|) ≤
      (1 + 10 * Real.exp 12 * (P.n N : ℝ)) ^ P.n N *
        groupedProduct P N x (fun i => y (e (Sum.inl i))) (fun i => y (e (Sum.inr i))) s := by
  classical
  have hN0 : 0 < N := by omega
  have hn1 : 1 * N ≤ P.n0 * N := Nat.mul_le_mul_right N hP.1
  have hn2 : (2 * P.g0 + 1) * N ≤ P.n0 * N :=
    Nat.mul_le_mul_right N (Nat.succ_le_of_lt hP.2.2.2.2)
  have hn3 : (2 * P.g0 + 1) * N = 2 * (P.g0 * N) + N := by ring
  have hn48 : 48 ≤ P.n N := by simp only [Parameters.n]; omega
  have hng : 2 * P.g N + 1 < P.n N := by
    simp only [Parameters.n, Parameters.g]; omega
  let z : Fin (P.n N) → ℝ := fun i => Fin.append x y (Fin.cast hpm.symm i)
  have hcaseN : (∑ i, paramCaseField P N (z i)) ≤ -1 := by
    change (∑ i, paramCaseField P N (Fin.append x y (Fin.cast hpm.symm i))) ≤ -1
    rw [sum_fin_cast hpm (fun i => paramCaseField P N (Fin.append x y i))]
    exact hcase
  have hweight := paramCaseField_second_case hP hN0 z hcaseN
  change (∑ i, blaschkeWeight (Fin.append x y (Fin.cast hpm.symm i))) ≤ _ at hweight
  rw [sum_fin_cast hpm (fun i => blaschkeWeight (Fin.append x y i))] at hweight
  let ty : Fin m → Bool := fun j => sel (Fin.natAdd p j) && decide (0 ≤ y j)
  obtain ⟨a, b, hab, e, hleft, hright⟩ := exists_bool_partition ty
  have hyb : ∀ i, y (e (Sum.inr i)) ∈ Ioo (0 : ℝ) 1 := by
    intro i
    have hn : 0 ≤ y (e (Sum.inr i)) := by
      by_contra hh
      have ht := hright i
      simp [ty, hh] at ht
    exact ⟨lt_of_le_of_ne hn (Ne.symm (hy0 _)), (hy _).2⟩
  have hai : Function.Injective (Fin.append x (fun i => y (e (Sum.inl i)))) := by
    have hh := hzi.comp ((marked_selection_equiv (p := p) e).injective.comp
      Sum.inl_injective)
    change Function.Injective
      (fun i : Fin (p + a) => Fin.append x y (marked_selection_equiv e (Sum.inl i))) at hh
    rw [marked_selection_actual_nodes] at hh
    exact hh
  have hbi : Function.Injective (fun i => y (e (Sum.inr i))) := by
    have hh := hzi.comp ((marked_selection_equiv (p := p) e).injective.comp
      Sum.inr_injective)
    change Function.Injective
      (fun i : Fin b => Fin.append x y (marked_selection_equiv (p := p) e (Sum.inr i))) at hh
    rw [marked_selection_near_nodes] at hh
    exact hh
  refine ⟨a, b, hab, e, hyb, hai, hbi, ?_⟩
  have hsel := marked_selected_sheet_le_grouped hP hN0 hpm hab e ty
    hleft hright x y s hx hx0 hy hy0 hs hzi hn48 hng hweight
  have hmat : selectedLaurent (P.g N) (Fin.append x y) (selectedRows x y sel) =
      Matrix.of (fun i r : Fin (p + m) =>
        if (Fin.addCases (fun _ => false) ty i : Bool) then
          Fin.append x y i ^ ((r : ℤ) - P.g N)
        else actualLaurentEntry (P.g N) r (Fin.append x y i)) := by
    ext i r
    simp only [selectedLaurent, selectedRows, Matrix.of_apply, Finset.mem_filter,
      Finset.mem_univ, true_and]
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [ty]
  rw [hmat]
  have hsc : marked_sheet_scalar P N x y s =
      (∏ i, (1 + s i)) ^ m * selectedScalar P N x y s := by
    unfold marked_sheet_scalar selectedScalar
    ring
  rw [hsc] at hsel
  rw [← mul_assoc]
  exact hsel

end
end CatalanMeasure.GenD.Signed.RouteI.CompletedGas




namespace CatalanMeasure.GenD.Signed.RouteI.CompletedGas

open CatalanMeasure.GenD CatalanMeasure.GenD.Analytic CatalanMeasure.Signed
open CatalanMeasure.Parametric OAI.InternalCatalan Set Finset Filter
open CatalanMeasure.GenD.Signed.PhysicalPick
open scoped BigOperators Topology

noncomputable section

/-- The old grouped bound before its budget, at marked fraction `α` and near fraction `β`. -/
def oldBound (P : Parameters) (normCap fieldCap residual nearCap α β : ℝ) : ℝ :=
  (-gC0 P + gC1 P * α - α ^ 2 + β - β ^ 2) * Real.log 2 +
    normCap + (1 - α) * fieldCap + (α - β) * residual + β * nearCap

set_option maxHeartbeats 1600000 in
/-- The factor-free grouped energy with the free-row bracket and the squares kept, before the
budget is applied. -/
theorem second_energy_sq_end {P : Parameters} (hP : CatalanMeasure.Parametric.Admissible P)
    {W : Set ℝ} {Cf : ℕ → ℝ → ℝ} {d : ℝ → ℝ} {target residual nearCap cost : ℝ} {G : ℝ → Prop}
    (D : SecondTrialBoundsEnd P W Cf d target residual nearCap cost G) {δ e : ℝ} (hδ : 0 < δ)
    (he : e ∈ Ioo (0 : ℝ) (1 / 8))
    (hec : e * (4 * (∑' j, |D.p j|) + 4 * (∑' j, |D.v j|) + |D.p 1| + 20) < δ / 2) :
    ∀ᶠ N : ℕ in atTop, ∀ (r a b : ℕ), r + a + b = P.n N →
      ∀ (z : Fin r → ℝ) (x : Fin a → ℝ) (y : Fin b → ℝ) (s : Fin r → ℝ),
      (∀ i, z i ∈ Ioo (-1 : ℝ) 1) → (∀ i, z i ≠ 0) →
      (∀ i, x i ∈ Ioo (-1 : ℝ) 1) → (∀ i, G (x i)) → (∀ i, y i ∈ Ioo (0 : ℝ) 1) →
      (∀ i, G (y i)) →
      (∀ i, s i ∈ Ioo (0 : ℝ) 1) → Function.Injective z →
      Function.Injective (Fin.append z x) → Function.Injective y → Function.Injective s →
      (groupedValueWithFields (P.n N : ℝ) (groupedConstant P N r a b)
        (populationPhysicalFreeField P N) (fun u => groupedMarkedField P N u + d u)
        (fun u => groupedNearField P N u + d u) (Cf N) z x y s +
        bracketSlack (P.n N : ℝ) (D.MX + δ / 4) (fun i => freeRowX P N D.p D.v (z i)) +
        groupedSquares (P.n N : ℝ) e D.p D.p D.v (Fin.append z x) y z s ≤
        oldBound P D.normCap D.fieldCap residual nearCap (((a + b : ℕ) : ℝ) / (P.n N : ℝ))
          ((b : ℝ) / (P.n N : ℝ)) + δ) ∧
      0 ≤ bracketSlack (P.n N : ℝ) (D.MX + δ / 4) (fun i => freeRowX P N D.p D.v (z i)) ∧
      ∀ i, freeRowX P N D.p D.v (z i) ≤ D.MX + δ / 4 := by
  have hε : 0 < δ / 4 := by linarith only [hδ]
  have herr : ∀ᶠ N : ℕ in atTop,
      groupedPopulationError ((P.n0 : ℝ) * N) e D.p D.p D.v ≤ δ / 2 :=
    ((tendsto_order.mp (grouped_error_tendsto hP e D.p D.v)).2 (δ / 2) hec).mono
      (fun _ h => h.le)
  filter_upwards [D.row hε, D.column hε,
      log_reciprocal_eventually hP hε, herr, eventually_gt_atTop (0 : ℕ)]
    with N hrow hcol hsmall herror hN r a b hcount z x y s hz hz0 hx hxG hy hyG hs hzi hxi hyi hsi
  have hν : 0 < (P.n N : ℝ) := by exact_mod_cast n_pos hP hN
  set α : ℝ := ((a + b : ℕ) : ℝ) / (P.n N : ℝ) with hαd
  set β : ℝ := (b : ℝ) / (P.n N : ℝ) with hβd
  have hα : 0 ≤ α := div_nonneg (Nat.cast_nonneg _) hν.le
  have hβ : 0 ≤ β := div_nonneg (Nat.cast_nonneg _) hν.le
  have hfree : (r : ℝ) / (P.n N : ℝ) = 1 - α := by
    have hf := population_fractions hP hN (show r + (a + b) = P.n N by omega)
    linarith only [hf]
  have hmarked : (a : ℝ) / (P.n N : ℝ) = α - β := by
    rw [hαd, hβd, Nat.cast_add, add_div]
    ring
  have hy' : ∀ i, y i ∈ Ioo (-1 : ℝ) 1 := fun i => ⟨by linarith [(hy i).1], (hy i).2⟩
  have hb := grouped_field_caps_bound_sq (constant := groupedConstant P N r a b) hν he
    (by exact_mod_cast (show r + a ≤ P.n N by omega))
    (by exact_mod_cast (show b ≤ P.n N by omega)) z x y s hz hx hy' hs hzi hxi hyi hsi
    D.p D.p D.v D.p_summable D.p_summable D.v_summable
    (populationPhysicalFreeField P N) (fun u => groupedMarkedField P N u + d u)
    (fun u => groupedNearField P N u + d u) (Cf N)
    (D.MX + δ / 4) (residual + δ / 4) (nearCap + δ / 4) (D.MY + δ / 4)
  have hconst := grouped_constant_le hP hN hcount
  have hnorm := D.norm_le
  rw [← n_cast] at herror
  rw [hfree, hmarked] at hb
  rw [hfree] at hconst
  have hXz : ∀ i, freeRowX P N D.p D.v (z i) ≤ D.MX + δ / 4 := by
    intro i
    have hzi' : z i ∈ Ico (-1 : ℝ) 0 ∪ Ioo 0 1 := by
      rcases lt_or_gt_of_ne (hz0 i) with h | h
      · exact Or.inl ⟨(hz i).1.le, h⟩
      · exact Or.inr ⟨h, (hz i).2⟩
    have := hrow (z i) hzi'
    unfold freeRowX
    linarith
  have hM : ∀ i, (groupedMarkedField P N (x i) + d (x i)) - 2 * barrierTrialT D.p (x i) ≤
      residual + δ / 4 := fun i => by
    have := D.marked hN ⟨(hx i).1.le, (hx i).2.le⟩ (hxG i)
    linarith
  have hL : ∀ i, (groupedNearField P N (y i) + d (y i)) - D.p 1 * y i ≤ nearCap + δ / 4 :=
    fun i => by
    have := D.near hN (hy i) (hyG i)
    linarith
  have hC : ∀ i, Cf N (s i) + 2 * barrierTrialT D.v (s i) -
      Real.log (1 - s i) / (P.n N : ℝ) ≤ D.MY + δ / 4 := fun i => hcol (s i) (hs i)
  have hb2 := bracketSlack_nonneg hν hM
  have hb3 := bracketSlack_nonneg hν hL
  have hb4 := bracketSlack_nonneg hν hC
  refine ⟨?_, bracketSlack_nonneg hν hXz, hXz⟩
  unfold groupedSlack at hb
  have hX : bracketSlack (P.n N : ℝ) (D.MX + δ / 4) (fun i => freeRowX P N D.p D.v (z i)) =
      bracketSlack (P.n N : ℝ) (D.MX + δ / 4)
        (fun i => populationPhysicalFreeField P N (z i) - 2 * barrierTrialT D.p (z i) -
          2 * barrierTrialT D.p (z i) - barrierTrialS D.v (z i) -
          Real.log (1 - z i) / (2 * (P.n N : ℝ))) := rfl
  rw [hX]
  have hf2 : (1 - α) * (D.MX + δ / 4 + (D.MY + δ / 4)) =
      (1 - α) * D.fieldCap + (1 - α) * (δ / 2) := by
    rw [← D.field_sum]
    ring
  have hf3 : (α - β) * (residual + δ / 4) + β * (nearCap + δ / 4) =
      (α - β) * residual + β * nearCap + α * (δ / 4) := by ring
  have hαδ : 0 ≤ α * δ := mul_nonneg hα hδ.le
  unfold oldBound
  linarith only [hb, hconst, hnorm, herror, hf2, hf3, hαδ, hb2, hb3, hb4]

/-- A grouped value at most the target gives the selected cap, with the column factor
`(∏ (1 + ζ s))^(a+b)` and the node correction `d` (the value carries the column field
`endpoint + ((a+b)/n) log (1 + ζ s)` and the marked and near fields plus `d`). -/
theorem low_of_value {P : Parameters} (hP : CatalanMeasure.Parametric.Admissible P)
    {N r a b : ℕ} (hN : 0 < N) (hcount : r + a + b = P.n N)
    {target cost' ε ζ : ℝ} (hζ : 0 ≤ ζ) {d : ℝ → ℝ}
    {z : Fin r → ℝ} {x : Fin a → ℝ} {y : Fin b → ℝ} {s : Fin r → ℝ}
    (hz : ∀ i, z i ∈ Ioo (-1 : ℝ) 1) (hz0 : ∀ i, z i ≠ 0)
    (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) (hy : ∀ i, y i ∈ Ioo (0 : ℝ) 1)
    (hs : ∀ i, s i ∈ Ioo (0 : ℝ) 1) (hzi : Function.Injective z)
    (hxi : Function.Injective (Fin.append z x)) (hyi : Function.Injective y)
    (hsi : Function.Injective s)
    (hval : groupedValueWithFields (P.n N : ℝ) (groupedConstant P N r a b)
        (populationPhysicalFreeField P N) (fun u => groupedMarkedField P N u + d u)
        (fun u => groupedNearField P N u + d u)
        (fun u => populationEndpointColumnField P N 0 u +
          (((a + b : ℕ) : ℝ) / (P.n N : ℝ)) * Real.log (1 + ζ * u)) z x y s ≤
      -target + Real.log 2 / 2 + cost' * (((a + b : ℕ) : ℝ) / (P.n N : ℝ)) + ε) :
    (∏ i, (1 + ζ * s i)) ^ (a + b) * groupedProduct P N z x y s ≤
      (∏ i, (1 + s i)) ^ (a + b) *
      Real.exp (((P.n0 : ℝ) * N) ^ 2 * (-target + Real.log 2 / 2 + ε) +
        ((P.n0 : ℝ) * cost') * N * (a + b) - (P.n N : ℝ) * ((∑ i, d (x i)) + ∑ j, d (y j))) := by
  have hy' : ∀ i, y i ∈ Ioo (-1 : ℝ) 1 := fun i => ⟨by linarith [(hy i).1], (hy i).2⟩
  have hy0 : ∀ i, y i ≠ 0 := fun i => (hy i).1.ne'
  have hlog := log_groupedProduct hP hN z x y s hz hx hy' hs hz0 hy0 hzi hxi hyi hsi
  have hn : (P.n N : ℝ) = (P.n0 : ℝ) * N := n_cast P N
  have hn0 : (P.n0 : ℝ) ≠ 0 := (n0_pos hP).ne'
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hνpos : (0 : ℝ) < P.n N := by exact_mod_cast n_pos hP hN
  have hs1 : ∀ i, 0 < 1 + s i := fun i => by linarith [(hs i).1]
  have hsζ : ∀ i, 0 < 1 + ζ * s i := fun i => by
    have := mul_nonneg hζ (hs i).1.le
    linarith
  have hpos : 0 < groupedProduct P N z x y s := by
    have hS : 0 < (∏ i, (1 + s i)) ^ (a + b) :=
      pow_pos (prod_pos fun i _ => hs1 i) _
    have hZ : 0 < ∏ i, |z i| ^ ((P.g N : ℤ) - (P.n N - 1 : ℕ)) :=
      prod_pos fun i _ => zpow_pos (abs_pos.mpr (hz0 i)) _
    have hX : 0 < ∏ i, markedSheetWeight P N (x i) :=
      prod_pos fun i _ => markedSheetWeight_pos P N _
    have hY : 0 < ∏ i, markedSheetWeight P N (y i) *
        |y i| ^ (P.n N - 1 - 2 * P.g N) :=
      prod_pos fun i _ => mul_pos (markedSheetWeight_pos P N _)
        (pow_pos (abs_pos.mpr (hy0 i)) _)
    have hPair := groupedPairProduct_pos (Fin.append z x) y
        (fun i => abs_lt.mpr (Fin.addCases (fun j => by simpa using hz j)
          (fun j => by simpa using hx j) i)) (fun i => abs_lt.mpr (hy' i)) hxi hyi
    exact mul_pos (mul_pos (mul_pos (mul_pos (mul_pos hS hZ) hX) hY) hPair)
      (paramPinPrincipal_pos hP hN z s hz hs hz0 hzi hsi)
  have hprod : ∀ c : ℝ → ℝ, (∀ i, 0 < c (s i)) →
      (∏ i, c (s i)) ^ (a + b) =
        Real.exp (((a + b : ℕ) : ℝ) * ∑ i, Real.log (c (s i))) := by
    intro c hc
    have hp : 0 < ∏ i, c (s i) := prod_pos fun i _ => hc i
    rw [← Real.exp_log (pow_pos hp (a + b)), Real.log_pow,
      Real.log_prod (fun i _ => (hc i).ne')]
  have hphys := grouped_value_physical_eq (P := P) (N := N) z x y s
  have hsplit : groupedValueWithFields (P.n N : ℝ) (groupedConstant P N r a b)
        (populationPhysicalFreeField P N) (fun u => groupedMarkedField P N u + d u)
        (fun u => groupedNearField P N u + d u)
        (fun u => populationEndpointColumnField P N 0 u +
          (((a + b : ℕ) : ℝ) / (P.n N : ℝ)) * Real.log (1 + ζ * u)) z x y s =
      groupedValueWithFields (P.n N : ℝ) (groupedConstant P N r a b)
        (populationPhysicalFreeField P N) (groupedMarkedField P N)
        (groupedNearField P N) (populationEndpointColumnField P N 0) z x y s +
      ((∑ i, d (x i)) + (∑ j, d (y j)) +
        (((a + b : ℕ) : ℝ) / (P.n N : ℝ)) * ∑ i, Real.log (1 + ζ * s i)) / (P.n N : ℝ) := by
    unfold groupedValueWithFields
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    ring
  rw [hsplit] at hval
  have hid : (P.n N : ℝ) ^ 2 *
      (-target + Real.log 2 / 2 + cost' * (((a + b : ℕ) : ℝ) / P.n N) + ε) =
      ((P.n0 : ℝ) * N) ^ 2 * (-target + Real.log 2 / 2 + ε) +
        ((P.n0 : ℝ) * cost') * N * (a + b) := by
    rw [hn, Nat.cast_add]
    field_simp
    ring
  have hbound := mul_le_mul_of_nonneg_left hval (sq_nonneg (P.n N : ℝ))
  have hk1 : (P.n N : ℝ) ^ 2 * (((((a + b : ℕ) : ℝ) / (P.n N : ℝ)) *
      ∑ i, Real.log (1 + s i)) / (P.n N : ℝ)) =
      ((a + b : ℕ) : ℝ) * ∑ i, Real.log (1 + s i) := by
    field_simp
  have hk2 : (P.n N : ℝ) ^ 2 * (((∑ i, d (x i)) + (∑ j, d (y j)) +
      (((a + b : ℕ) : ℝ) / (P.n N : ℝ)) * ∑ i, Real.log (1 + ζ * s i)) / (P.n N : ℝ)) =
      (P.n N : ℝ) * ((∑ i, d (x i)) + ∑ j, d (y j)) +
        ((a + b : ℕ) : ℝ) * ∑ i, Real.log (1 + ζ * s i) := by
    field_simp
  rw [hid, mul_add, hk2] at hbound
  rw [← Real.exp_log hpos, hprod (fun u => 1 + ζ * u) (fun i => hsζ i),
    hprod (fun u => 1 + u) (fun i => hs1 i), ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  rw [hlog, hphys]
  rw [mul_add, hk1]
  linarith only [hbound]

end
end CatalanMeasure.GenD.Signed.RouteI.CompletedGas




namespace CatalanMeasure.GenD.Signed.RouteI.CompletedGas

open CatalanMeasure.GenD CatalanMeasure.GenD.Analytic CatalanMeasure.Signed
open CatalanMeasure.Parametric OAI.InternalCatalan Set Finset Filter
open CatalanMeasure.GenD.Signed.PhysicalPick
open scoped BigOperators Topology

noncomputable section

/-- `Σ_{k ≥ 1} F_k τ^k T_k(w)`. -/
def dampedT (F : ℕ → ℝ) (τ w : ℝ) : ℝ :=
  ∑' k : ℕ, F (k + 1) * (τ ^ (k + 1) * (Polynomial.Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval w)

theorem cheb_abs_le (k : ℕ) {w : ℝ} (hw : w ∈ Icc (-1 : ℝ) 1) :
    |(Polynomial.Chebyshev.T ℝ ((k : ℕ) : ℤ)).eval w| ≤ 1 := by
  rw [← Real.cos_arccos hw.1 hw.2, Polynomial.Chebyshev.T_real_cos]
  exact Real.abs_cos_le_one _

theorem shift_summable {F : ℕ → ℝ} (hF : Summable fun k => |F k|) :
    Summable fun k : ℕ => |F (k + 1)| := (summable_nat_add_iff 1).2 hF

theorem damped_term_bound (F : ℕ → ℝ) {τ w : ℝ} (hτ : |τ| ≤ 1) (hw : w ∈ Icc (-1 : ℝ) 1)
    (k : ℕ) :
    ‖F (k + 1) * (τ ^ (k + 1) * (Polynomial.Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval w)‖ ≤
      |F (k + 1)| := by
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow]
  have h1 : |τ| ^ (k + 1) ≤ 1 := pow_le_one₀ (abs_nonneg _) hτ
  have h2 := cheb_abs_le (k + 1) hw
  have h3 : |τ| ^ (k + 1) * |(Polynomial.Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval w| ≤ 1 :=
    mul_le_one₀ h1 (abs_nonneg _) h2
  calc |F (k + 1)| * (|τ| ^ (k + 1) * |(Polynomial.Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval w|)
      ≤ |F (k + 1)| * 1 := mul_le_mul_of_nonneg_left h3 (abs_nonneg _)
    _ = |F (k + 1)| := mul_one _

theorem damped_summable {F : ℕ → ℝ} (hF : Summable fun k => |F k|) {τ w : ℝ} (hτ : |τ| ≤ 1)
    (hw : w ∈ Icc (-1 : ℝ) 1) :
    Summable fun k : ℕ =>
      F (k + 1) * (τ ^ (k + 1) * (Polynomial.Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval w) :=
  Summable.of_norm_bounded (shift_summable hF) (damped_term_bound F hτ hw)

theorem tau_abs_le {e : ℝ} (he : e ∈ Ioo (0 : ℝ) (1 / 8)) : |realEnergyTau e| ≤ 1 := by
  have : realEnergyTau e = 1 - e := rfl
  rw [this, abs_le]
  constructor <;> linarith [he.1, he.2]

/-- The moment series of a test against a finite population. -/
theorem moment_hasSum {F : ℕ → ℝ} (hF : Summable fun k => |F k|) (ν : ℝ) {e : ℝ}
    (he : e ∈ Ioo (0 : ℝ) (1 / 8)) {p : ℕ} (w : Fin p → ℝ)
    (hw : ∀ i, w i ∈ Ioo (-1 : ℝ) 1) :
    HasSum (fun k : ℕ => F (k + 1) * pinCosineMoment ν e w (k + 1))
      ((∑ i, dampedT F (realEnergyTau e) (w i)) / ν) := by
  have h := hasSum_sum (s := (Finset.univ : Finset (Fin p))) (fun i _ =>
    (damped_summable hF (tau_abs_le he) (Ioo_subset_Icc_self (hw i))).hasSum)
  have h2 := h.div_const ν
  have hfun : (fun k : ℕ => F (k + 1) * pinCosineMoment ν e w (k + 1)) =
      fun k : ℕ => (∑ i, F (k + 1) * (realEnergyTau e ^ (k + 1) *
        (Polynomial.Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval (w i))) / ν := by
    funext k
    unfold pinCosineMoment
    rw [← mul_div_assoc, Finset.mul_sum]
  rw [hfun]
  exact h2

theorem moment_append (ν e : ℝ) {r a : ℕ} (z : Fin r → ℝ) (x : Fin a → ℝ) (k : ℕ) :
    pinCosineMoment ν e (Fin.append z x) k = pinCosineMoment ν e z k + pinCosineMoment ν e x k := by
  unfold pinCosineMoment
  rw [Fin.sum_univ_add, add_div]
  simp only [Fin.append_left, Fin.append_right]

theorem moment_one (ν e : ℝ) {b : ℕ} (y : Fin b → ℝ) :
    pinCosineMoment ν e y 1 = realEnergyTau e * (∑ i, y i) / ν := by
  unfold pinCosineMoment
  simp [Polynomial.Chebyshev.T_one, ← Finset.mul_sum]

/-- The average of the two retained row vectors, with the near moment shift. -/
def retD (ν e : ℝ) (u : ℕ → ℝ) {r a b : ℕ} (z : Fin r → ℝ) (x : Fin a → ℝ) (y : Fin b → ℝ)
    (k : ℕ) : ℝ :=
  (pinCosineMoment ν e z (k + 1) + pinCosineMoment ν e (Fin.append z x) (k + 1)) / 2 - u (k + 1) +
    (if k = 0 then pinCosineMoment ν e y 1 / 4 else 0)

theorem append_mem {r a : ℕ} {z : Fin r → ℝ} {x : Fin a → ℝ} {I : Set ℝ}
    (hz : ∀ i, z i ∈ I) (hx : ∀ i, x i ∈ I) (i : Fin (r + a)) : Fin.append z x i ∈ I := by
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simpa using hz j
  · simpa using hx j

/-- Averaging the two square arguments: the near moment's sign survives. -/
theorem retD_sq {ν e : ℝ} (hν : 0 < ν) (he : e ∈ Ioo (0 : ℝ) (1 / 8)) {r a b : ℕ}
    {z : Fin r → ℝ} {x : Fin a → ℝ} {y : Fin b → ℝ}
    (hz : ∀ i, z i ∈ Ioo (-1 : ℝ) 1) (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1)
    (hy : ∀ i, y i ∈ Ioo (-1 : ℝ) 1) (u : ℕ → ℝ) (hu : Summable fun k => |u k|) :
    ∃ D, HasSum (fun k : ℕ => retD ν e u z x y k ^ 2 / ((k + 1 : ℕ) : ℝ)) D ∧
      D ≤ (sqTail u (pinCosineMoment ν e z) +
        cosineSquares ν e u (Fin.append z x) y) / 2 := by
  have hzx := append_mem hz hx
  set A := pinCosineMoment ν e z with hAd
  set B := pinCosineMoment ν e (Fin.append z x) with hBd
  set C := pinCosineMoment ν e y 1 with hCd
  have hA : HasSum (fun k : ℕ => (u (k + 1) - A (k + 1)) ^ 2 / ((k + 1 : ℕ) : ℝ))
      (sqTail u A) :=
    (completed_square_hasSum u A hu (pin_hasSum_cos_sq_shift hν he hz)).summable.hasSum
  have hB : HasSum (fun k : ℕ => (u (k + 1) - B (k + 1)) ^ 2 / ((k + 1 : ℕ) : ℝ))
      (sqTail u B) :=
    (completed_square_hasSum u B hu (pin_hasSum_cos_sq_shift hν he hzx)).summable.hasSum
  set bb : ℕ → ℝ := fun k => B (k + 1) - u (k + 1) + (if k = 0 then C / 2 else 0) with hbb
  have hb : HasSum (fun k : ℕ => bb k ^ 2 / ((k + 1 : ℕ) : ℝ))
      (sqTail u B + ((B 1 - u 1) * C + C ^ 2 / 4)) := by
    have hi : HasSum (fun k : ℕ => if k = 0 then (B 1 - u 1) * C + C ^ 2 / 4 else 0)
        ((B 1 - u 1) * C + C ^ 2 / 4) := hasSum_ite_eq 0 _
    have h := hB.add hi
    convert h using 1
    funext k
    by_cases hk : k = 0
    · subst hk
      simp only [hbb, if_true, zero_add, Nat.cast_one, div_one]
      ring
    · simp only [hbb, if_neg hk, add_zero]
      ring
  have hle : ∀ k : ℕ, retD ν e u z x y k ^ 2 / ((k + 1 : ℕ) : ℝ) ≤
      ((u (k + 1) - A (k + 1)) ^ 2 / ((k + 1 : ℕ) : ℝ) + bb k ^ 2 / ((k + 1 : ℕ) : ℝ)) / 2 := by
    intro k
    have hd : retD ν e u z x y k = ((A (k + 1) - u (k + 1)) + bb k) / 2 := by
      simp only [retD, hbb, ← hAd, ← hBd, ← hCd]
      split_ifs <;> ring
    have hn : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
    have h4 : (((A (k + 1) - u (k + 1)) + bb k) / 2) ^ 2 ≤
        ((u (k + 1) - A (k + 1)) ^ 2 + bb k ^ 2) / 2 := by
      nlinarith [sq_nonneg ((A (k + 1) - u (k + 1)) - bb k)]
    rw [hd, ← add_div, div_right_comm]
    exact div_le_div_of_nonneg_right h4 hn.le
  have hsum := (hA.add hb).div_const 2
  have hnn : ∀ k : ℕ, 0 ≤ retD ν e u z x y k ^ 2 / ((k + 1 : ℕ) : ℝ) := fun k =>
    div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)
  have hS : Summable fun k : ℕ => retD ν e u z x y k ^ 2 / ((k + 1 : ℕ) : ℝ) :=
    Summable.of_nonneg_of_le hnn hle hsum.summable
  refine ⟨_, hS.hasSum, ?_⟩
  have h1 := hasSum_le hle hS.hasSum hsum
  have h2 : (0 - C) ^ 2 ≤ sqTail (fun _ => 0) (pinCosineMoment ν e y) :=
    first_le_sqTail (fun _ => 0) _ (by simp) (pin_hasSum_cos_sq_shift hν he hy)
  have h3 : cosineSquares ν e u (Fin.append z x) y =
      sqTail u B + sqTail (fun _ => 0) (pinCosineMoment ν e y) + (B 1 - u 1) * C := rfl
  rw [h3]
  nlinarith [h1, h2]

theorem test_trial_summable {F u : ℕ → ℝ} (hF : Summable fun k => |F k|)
    (hu : Summable fun k => |u k|) : Summable fun k : ℕ => F (k + 1) * u (k + 1) := by
  refine Summable.of_norm_bounded ((shift_summable hF).mul_right (∑' j, |u j|)) (fun k => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_left (hu.le_tsum (k + 1) (fun j _ => abs_nonneg _)) (abs_nonneg _)

/-- **Retained-square statistic.**  A test `F` against the measure `free + ½ marked`, with the near
population's first moment kept, is within `√(H Δ/2)` of its trial value. -/
theorem weighted_statistic {ν e : ℝ} (hν : 0 < ν) (he : e ∈ Ioo (0 : ℝ) (1 / 8)) {r a b : ℕ}
    {z : Fin r → ℝ} {x : Fin a → ℝ} {y : Fin b → ℝ}
    (hz : ∀ i, z i ∈ Ioo (-1 : ℝ) 1) (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1)
    (hy : ∀ i, y i ∈ Ioo (-1 : ℝ) 1) (u : ℕ → ℝ) (hu : Summable fun k => |u k|)
    {F : ℕ → ℝ} (hF : Summable fun k => |F k|) {H Δ : ℝ}
    (hH : HasSum (fun k : ℕ => F (k + 1) ^ 2 * ((k + 1 : ℕ) : ℝ)) H)
    (hΔ : sqTail u (pinCosineMoment ν e z) + cosineSquares ν e u (Fin.append z x) y ≤ Δ) :
    (∑' k : ℕ, F (k + 1) * u (k + 1)) - Real.sqrt (H * (Δ / 2)) ≤
      ((∑ i, dampedT F (realEnergyTau e) (z i)) +
        (∑ i, dampedT F (realEnergyTau e) (x i)) / 2 +
        F 1 * realEnergyTau e * (∑ i, y i) / 4) / ν := by
  obtain ⟨D, hD, hDle⟩ := retD_sq hν he hz hx hy u hu
  have hDΔ : D ≤ Δ / 2 := by linarith only [hDle, hΔ]
  have Mz := moment_hasSum hF ν he z hz
  have Mx := moment_hasSum hF ν he x hx
  have hU := (test_trial_summable hF hu).hasSum
  set Sz := ∑ i, dampedT F (realEnergyTau e) (z i)
  set Sx := ∑ i, dampedT F (realEnergyTau e) (x i)
  set U := ∑' k : ℕ, F (k + 1) * u (k + 1)
  set C := pinCosineMoment ν e y 1 with hC
  have hFd : HasSum (fun k : ℕ => F (k + 1) * retD ν e u z x y k)
      (Sz / ν + (Sx / ν) / 2 - U + F 1 * C / 4) := by
    have hi : HasSum (fun k : ℕ => if k = 0 then F 1 * C / 4 else 0) (F 1 * C / 4) :=
      hasSum_ite_eq 0 _
    have h := ((Mz.add (Mx.div_const 2)).sub hU).add hi
    convert h using 1
    funext k
    unfold retD
    rw [moment_append]
    by_cases hk : k = 0
    · subst hk
      simp only [if_true, zero_add, ← hC]
      ring
    · simp only [if_neg hk]
      ring
  have hdev := statistic_dev_le (d := retD ν e u z x y) (F := fun k => F (k + 1))
    (v := fun k => ((k + 1 : ℕ) : ℝ)) (fun k => by positivity) hD hDΔ hH
    (Φ := Sz / ν + (Sx / ν) / 2 + F 1 * C / 4) (c := U) (ε := 0)
    (by
      rw [hFd.tsum_eq]
      have : Sz / ν + Sx / ν / 2 + F 1 * C / 4 - (U + (Sz / ν + Sx / ν / 2 - U + F 1 * C / 4)) = 0 := by
        ring
      rw [this]
      simp)
  have h2 := (abs_le.mp hdev).1
  have hC1 : C = realEnergyTau e * (∑ i, y i) / ν := moment_one ν e y
  have hfin : (Sz + Sx / 2 + F 1 * realEnergyTau e * (∑ i, y i) / 4) / ν =
      Sz / ν + (Sx / ν) / 2 + F 1 * C / 4 := by
    rw [hC1]
    ring
  rw [hfin]
  linarith only [h2]

/-- Removing the damping from a test with absolutely summable coefficients. -/
theorem abel_eventually {F : ℕ → ℝ} (hF : Summable fun k => |F k|) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ e in 𝓝[>] (0 : ℝ), ∀ w ∈ Icc (-1 : ℝ) 1,
      |dampedT F (1 - e) w - dampedT F 1 w| ≤ η := by
  have hT : Tendsto (fun e : ℝ => ∑' k : ℕ, |F (k + 1)| * (1 - (1 - e) ^ (k + 1))) (𝓝[>] 0)
      (𝓝 (∑' _ : ℕ, (0 : ℝ))) := by
    refine tendsto_tsum_of_dominated_convergence (shift_summable hF) (fun k => ?_) ?_
    · have hc : Continuous fun e : ℝ => |F (k + 1)| * (1 - (1 - e) ^ (k + 1)) := by fun_prop
      have h := hc.tendsto 0
      simp only [sub_zero, one_pow, sub_self, mul_zero] at h
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with e he k
      have h0 : 0 ≤ (1 - e) ^ (k + 1) := pow_nonneg (by linarith [he.2]) _
      have h1 : (1 - e) ^ (k + 1) ≤ 1 := pow_le_one₀ (by linarith [he.2]) (by linarith [he.1])
      rw [Real.norm_eq_abs, abs_mul, abs_abs, abs_of_nonneg (show 0 ≤ 1 - (1 - e) ^ (k + 1) by linarith)]
      exact mul_le_of_le_one_right (abs_nonneg _) (by linarith)
  rw [tsum_zero] at hT
  filter_upwards [hT.eventually (Iio_mem_nhds hη),
    Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with e h1 he w hw
  have hτ : |1 - e| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [he.1, he.2]
  have hs1 := damped_summable hF hτ hw
  have hs2 := damped_summable hF (show |(1 : ℝ)| ≤ 1 by simp) hw
  have hpow : ∀ k : ℕ, 0 ≤ (1 - e) ^ (k + 1) ∧ (1 - e) ^ (k + 1) ≤ 1 := fun k =>
    ⟨pow_nonneg (by linarith [he.2]) _, pow_le_one₀ (by linarith [he.2]) (by linarith [he.1])⟩
  have hg : Summable fun k : ℕ => |F (k + 1)| * (1 - (1 - e) ^ (k + 1)) :=
    Summable.of_nonneg_of_le (fun k => mul_nonneg (abs_nonneg _) (by linarith [(hpow k).2]))
      (fun k => mul_le_of_le_one_right (abs_nonneg _) (by linarith [(hpow k).1]))
      (shift_summable hF)
  have hdiff : dampedT F (1 - e) w - dampedT F 1 w = ∑' k : ℕ,
      (F (k + 1) * ((1 - e) ^ (k + 1) * (Polynomial.Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval w) -
        F (k + 1) * ((1 : ℝ) ^ (k + 1) * (Polynomial.Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval w)) :=
    (hs1.tsum_sub hs2).symm
  rw [hdiff, ← Real.norm_eq_abs]
  refine (tsum_of_norm_bounded hg.hasSum (fun k => ?_)).trans h1.le
  have ht := cheb_abs_le (k + 1) hw
  have hid : F (k + 1) * ((1 - e) ^ (k + 1) * (Polynomial.Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval w) -
      F (k + 1) * ((1 : ℝ) ^ (k + 1) * (Polynomial.Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval w) =
      F (k + 1) * (((1 - e) ^ (k + 1) - 1) * (Polynomial.Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval w) := by
    rw [one_pow]
    ring
  rw [hid, Real.norm_eq_abs, abs_mul, abs_mul, abs_sub_comm ((1 - e) ^ (k + 1)) 1, abs_of_nonneg
    (by linarith [(hpow k).2] : 0 ≤ 1 - (1 - e) ^ (k + 1))]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  exact mul_le_of_le_one_right (by linarith [(hpow k).2]) ht

end
end CatalanMeasure.GenD.Signed.RouteI.CompletedGas




namespace CatalanMeasure.GenD.Signed.RouteI.CompletedGas

open CatalanMeasure.GenD CatalanMeasure.GenD.Analytic CatalanMeasure.Signed
open CatalanMeasure.Parametric OAI.InternalCatalan Set Finset Filter
open CatalanMeasure.GenD.Signed.PhysicalPick
open scoped BigOperators Topology

noncomputable section

/-- `h(w) = π/2 - arctan(4 (1 - w)/(1 + w))`, the phase gained by a positive node. -/
def phaseH (w : ℝ) : ℝ := Real.pi / 2 - Real.arctan (4 * ((1 - w) / (1 + w)))

/-- The phase gain, zero at negative nodes. -/
def phasePlus (w : ℝ) : ℝ := if 0 < w then phaseH w else 0

theorem phaseH_nonneg (w : ℝ) : 0 ≤ phaseH w := by
  unfold phaseH
  linarith [Real.arctan_lt_pi_div_two (4 * ((1 - w) / (1 + w)))]

/-- A Chebyshev test: the function `F₀/2 + Σ_{k≥1} F_k T_k` with its three minorant properties
(PROOF-C §§20-21) and the near-row inequality (PROOF-C §34). -/
structure PhaseTest where
  F : ℕ → ℝ
  H : ℝ
  a₀ : ℝ
  h₀ : ℝ
  summable : Summable fun k => |F k|
  energy : HasSum (fun k : ℕ => F (k + 1) ^ 2 * ((k + 1 : ℕ) : ℝ)) H
  h₀_nonneg : 0 ≤ h₀
  pos : ∀ w ∈ Ioo (0 : ℝ) 1, F 0 / 2 + dampedT F 1 w ≤ phaseH w
  mid : ∀ w ∈ Ioo (-a₀) 0, F 0 / 2 + dampedT F 1 w ≤ h₀
  left : ∀ w ∈ Icc (-1 : ℝ) (-a₀), F 0 / 2 + dampedT F 1 w ≤ 0
  near : ∀ y ∈ Ioo (0 : ℝ) 1, F 0 / 4 + |F 1| / 4 * y ≤ phaseH y

/-- The phase sum over a configuration, from the retained squares. -/
theorem phase_sum_lower (T : PhaseTest) {ν e η Δ c : ℝ} (hν : 0 < ν)
    (he : e ∈ Ioo (0 : ℝ) (1 / 8))
    (habel : ∀ w ∈ Icc (-1 : ℝ) 1,
      |dampedT T.F (realEnergyTau e) w - dampedT T.F 1 w| ≤ η)
    {r a b : ℕ} (hcount : (r : ℝ) + a + b = ν)
    {z : Fin r → ℝ} {x : Fin a → ℝ} {y : Fin b → ℝ}
    (hz : ∀ i, z i ∈ Ioo (-1 : ℝ) 1) (hz0 : ∀ i, z i ≠ 0)
    (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) (hx0 : ∀ i, x i ≠ 0)
    (hxneg : ∀ i, x i < 0 → x i ≤ -T.a₀) (hy : ∀ i, y i ∈ Ioo (0 : ℝ) 1)
    (u : ℕ → ℝ) (hu : Summable fun k => |u k|)
    (hΔ : sqTail u (pinCosineMoment ν e z) + cosineSquares ν e u (Fin.append z x) y ≤ Δ)
    (hc : ((Finset.univ.filter (fun i => z i ∈ Ioo (-T.a₀) 0)).card : ℝ) ≤ c) :
    ν * (T.F 0 / 2 + (∑' k : ℕ, T.F (k + 1) * u (k + 1)) - Real.sqrt (T.H * (Δ / 2)) - η) -
        ((a : ℝ) + b) * T.F 0 / 4 - T.h₀ * c ≤
      (∑ i, phasePlus (z i)) + (∑ i, phasePlus (x i)) + ∑ i, phasePlus (y i) := by
  have hη : 0 ≤ η := (abs_nonneg _).trans (habel 0 (by norm_num))
  have hy' : ∀ i, y i ∈ Ioo (-1 : ℝ) 1 := fun i => ⟨by linarith [(hy i).1], (hy i).2⟩
  have hstat := weighted_statistic hν he hz hx hy' u hu T.summable T.energy hΔ
  rw [le_div_iff₀ hν] at hstat
  have hup : ∀ w ∈ Icc (-1 : ℝ) 1,
      dampedT T.F (realEnergyTau e) w ≤ dampedT T.F 1 w + η := fun w hw => by
    have := (abs_le.mp (habel w hw)).2
    linarith
  have P1 : ∀ i, dampedT T.F (realEnergyTau e) (z i) + T.F 0 / 2 ≤
      phasePlus (z i) + η + (if z i ∈ Ioo (-T.a₀) 0 then T.h₀ else 0) := by
    intro i
    have h1 := hup (z i) (Ioo_subset_Icc_self (hz i))
    rcases lt_or_gt_of_ne (hz0 i) with hneg | hpos
    · have hp : phasePlus (z i) = 0 := if_neg (not_lt.2 hneg.le)
      rw [hp]
      by_cases hm : z i ∈ Ioo (-T.a₀) 0
      · rw [if_pos hm]
        have := T.mid _ hm
        linarith
      · rw [if_neg hm]
        have hl : z i ≤ -T.a₀ := by
          by_contra h
          exact hm ⟨not_le.1 h, hneg⟩
        have := T.left (z i) ⟨(hz i).1.le, hl⟩
        linarith
    · have hp : phasePlus (z i) = phaseH (z i) := if_pos hpos
      rw [hp]
      have := T.pos (z i) ⟨hpos, (hz i).2⟩
      split_ifs <;> linarith [T.h₀_nonneg]
  have P2 : ∀ i, dampedT T.F (realEnergyTau e) (x i) / 2 + T.F 0 / 4 ≤
      phasePlus (x i) + η / 2 := by
    intro i
    have h1 := hup (x i) (Ioo_subset_Icc_self (hx i))
    rcases lt_or_gt_of_ne (hx0 i) with hneg | hpos
    · have hp : phasePlus (x i) = 0 := if_neg (not_lt.2 hneg.le)
      rw [hp]
      have := T.left (x i) ⟨(hx i).1.le, hxneg i hneg⟩
      linarith
    · have hp : phasePlus (x i) = phaseH (x i) := if_pos hpos
      rw [hp]
      have := T.pos (x i) ⟨hpos, (hx i).2⟩
      linarith [phaseH_nonneg (x i)]
  have P3 : ∀ i, T.F 1 * realEnergyTau e * y i / 4 + T.F 0 / 4 ≤ phasePlus (y i) := by
    intro i
    have hp : phasePlus (y i) = phaseH (y i) := if_pos (hy i).1
    rw [hp]
    have h1 := T.near (y i) (hy i)
    have h2 : T.F 1 * realEnergyTau e ≤ |T.F 1| := by
      calc T.F 1 * realEnergyTau e ≤ |T.F 1 * realEnergyTau e| := le_abs_self _
        _ = |T.F 1| * |realEnergyTau e| := abs_mul _ _
        _ ≤ |T.F 1| * 1 := mul_le_mul_of_nonneg_left (tau_abs_le he) (abs_nonneg _)
        _ = |T.F 1| := mul_one _
    have h3 := mul_le_mul_of_nonneg_right h2 (hy i).1.le
    linarith
  have S1 := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin r))) => P1 i)
  have S2 := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin a))) => P2 i)
  have S3 := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin b))) => P3 i)
  have hite : (∑ i, if z i ∈ Ioo (-T.a₀) 0 then T.h₀ else 0) =
      ((Finset.univ.filter (fun i => z i ∈ Ioo (-T.a₀) 0)).card : ℝ) * T.h₀ := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, ← Finset.sum_div, ← Finset.mul_sum] at S1 S2 S3
  rw [hite] at S1
  have hch := mul_le_mul_of_nonneg_right hc T.h₀_nonneg
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg _
  have hb : (0 : ℝ) ≤ b := Nat.cast_nonneg _
  have h1 := mul_nonneg ha hη
  have h2 := mul_nonneg hb hη
  subst hcount
  nlinarith only [hstat, S1, S2, S3, hch, h1, h2]

/-- The phase statistic of `PhaseHole` from a lower bound on the phase sum. -/
theorem hstat_of_sum {n : ℕ} {w : Fin n → ℝ} (hw0 : ∀ i, w i ≠ 0) (e : ℕ)
    (hbig : (n : ℝ) * (Real.pi / 2) + Real.pi / 2 +
        (17 / 4) * (n : ℝ) * (1 / 100) ^ 2 / (1 - (1 / 100) ^ 2) - (e : ℝ) * Real.arctan 4 <
      ∑ i, phasePlus (w i)) :
    ((Finset.univ.filter (fun i => w i < 0)).card : ℝ) * Real.pi / 2 + Real.pi / 2 +
        (17 / 4) * ((Finset.univ.filter (fun i => 0 < w i)).card : ℝ) * (1 / 100) ^ 2 /
          (1 - (1 / 100) ^ 2) <
      (e : ℝ) * Real.arctan 4 -
        ∑ i ∈ Finset.univ.filter (fun i => 0 < w i),
          Real.arctan (4 * ((1 - w i) / (1 + w i))) := by
  classical
  have hcard : (Finset.univ.filter (fun i => 0 < w i)).card +
      (Finset.univ.filter (fun i => w i < 0)).card = n := by
    have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
      (fun i => 0 < w i)
    have h2 : Finset.univ.filter (fun i => ¬ 0 < w i) =
        Finset.univ.filter (fun i => w i < 0) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt]
      exact ⟨fun h => lt_of_le_of_ne h (hw0 i), fun h => h.le⟩
    rw [h2] at h
    simpa using h
  have hn : (((Finset.univ.filter (fun i => 0 < w i)).card : ℕ) : ℝ) +
      ((Finset.univ.filter (fun i => w i < 0)).card : ℝ) = n := by exact_mod_cast hcard
  have hsum : ∑ i, phasePlus (w i) =
      ((Finset.univ.filter (fun i => 0 < w i)).card : ℝ) * (Real.pi / 2) -
        ∑ i ∈ Finset.univ.filter (fun i => 0 < w i),
          Real.arctan (4 * ((1 - w i) / (1 + w i))) := by
    unfold phasePlus phaseH
    rw [← Finset.sum_filter, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  rw [hsum, ← hn] at hbig
  have hneg : (0 : ℝ) ≤ ((Finset.univ.filter (fun i => w i < 0)).card : ℝ) := Nat.cast_nonneg _
  norm_num at hbig ⊢
  nlinarith only [hbig, hneg]

theorem onepoint_le {n : ℕ} {w : Fin n → ℝ} (hw : ∀ i, w i ∈ Ioo (-1 : ℝ) 1) :
    ∑ i ∈ Finset.univ.filter (fun i => 0 < w i), (1 - w i ^ 2) / (1 + w i ^ 2) ≤
      ∑ i, (1 - w i ^ 2) := by
  have hsq : ∀ i, 0 ≤ 1 - w i ^ 2 := fun i => by nlinarith [(hw i).1, (hw i).2]
  calc ∑ i ∈ Finset.univ.filter (fun i => 0 < w i), (1 - w i ^ 2) / (1 + w i ^ 2)
      ≤ ∑ i ∈ Finset.univ.filter (fun i => 0 < w i), (1 - w i ^ 2) := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [div_le_iff₀ (by positivity)]
        nlinarith [hsq i, sq_nonneg (w i)]
    _ ≤ ∑ i, (1 - w i ^ 2) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun i _ _ => hsq i

/-- The test `T₂`. -/
def testTwo (k : ℕ) : ℝ := if k = 2 then 1 else 0

theorem testTwo_summable : Summable fun k => |testTwo k| := by
  have h : (fun k => |testTwo k|) = fun k : ℕ => if k = 2 then (1 : ℝ) else 0 := by
    funext k
    unfold testTwo
    split_ifs <;> simp
  rw [h]
  exact (hasSum_ite_eq 2 (1 : ℝ)).summable

theorem testTwo_ne {k : ℕ} (hk : k ≠ 1) : testTwo (k + 1) = 0 := by
  have : k + 1 ≠ 2 := by omega
  simp [testTwo, this]

theorem dampedT_two (τ w : ℝ) : dampedT testTwo τ w = τ ^ 2 * (2 * w ^ 2 - 1) := by
  unfold dampedT
  rw [tsum_eq_single 1 (fun k hk => by rw [testTwo_ne hk, zero_mul])]
  have h1 : (((1 + 1 : ℕ) : ℤ)) = 2 := by norm_num
  rw [h1, Polynomial.Chebyshev.T_two]
  simp [testTwo]

theorem testTwo_energy :
    HasSum (fun k : ℕ => testTwo (k + 1) ^ 2 * ((k + 1 : ℕ) : ℝ)) 2 := by
  have h := hasSum_single (f := fun k : ℕ => testTwo (k + 1) ^ 2 * ((k + 1 : ℕ) : ℝ)) 1
    (fun k hk => by simp only [testTwo_ne hk]; ring)
  have h2 : testTwo (1 + 1) ^ 2 * ((1 + 1 : ℕ) : ℝ) = 2 := by
    simp [testTwo]
  simpa only [h2] using h

theorem testTwo_trial (u : ℕ → ℝ) : (∑' k : ℕ, testTwo (k + 1) * u (k + 1)) = u 2 := by
  rw [tsum_eq_single 1 (fun k hk => by rw [testTwo_ne hk, zero_mul])]
  simp [testTwo]

/-- The second moment of `free + ½ marked`, undamped. -/
theorem onepoint_lower {ν e η Δ : ℝ} (hν : 0 < ν) (he : e ∈ Ioo (0 : ℝ) (1 / 8)) (hη : 2 * e ≤ η)
    {r a b : ℕ} (hcount : (r : ℝ) + a + b = ν)
    {z : Fin r → ℝ} {x : Fin a → ℝ} {y : Fin b → ℝ}
    (hz : ∀ i, z i ∈ Ioo (-1 : ℝ) 1) (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1)
    (hy : ∀ i, y i ∈ Ioo (-1 : ℝ) 1) (u : ℕ → ℝ) (hu : Summable fun k => |u k|)
    (hΔ : sqTail u (pinCosineMoment ν e z) + cosineSquares ν e u (Fin.append z x) y ≤ Δ) :
    ν * (u 2 - Real.sqrt (2 * (Δ / 2)) - η) ≤
      (∑ i, (2 * z i ^ 2 - 1)) + (∑ i, (2 * x i ^ 2 - 1)) / 2 := by
  have hstat := weighted_statistic hν he hz hx hy u hu testTwo_summable testTwo_energy hΔ
  rw [le_div_iff₀ hν, testTwo_trial] at hstat
  simp only [dampedT_two, ← Finset.mul_sum] at hstat
  have h1 : testTwo 1 = 0 := by simp [testTwo]
  rw [h1] at hstat
  set W := (∑ i, (2 * z i ^ 2 - 1)) + (∑ i, (2 * x i ^ 2 - 1)) / 2 with hW
  set τ := realEnergyTau e with hτ
  have hτe : τ = 1 - e := rfl
  have hsz : ∀ {p : ℕ} {w : Fin p → ℝ}, (∀ i, w i ∈ Ioo (-1 : ℝ) 1) →
      -(p : ℝ) ≤ ∑ i, (2 * w i ^ 2 - 1) ∧ ∑ i, (2 * w i ^ 2 - 1) ≤ (p : ℝ) := by
    intro p w hw
    have hl : ∑ _i : Fin p, (-1 : ℝ) ≤ ∑ i, (2 * w i ^ 2 - 1) :=
      Finset.sum_le_sum fun i _ => by nlinarith [sq_nonneg (w i)]
    have hr : ∑ i, (2 * w i ^ 2 - 1) ≤ ∑ _i : Fin p, (1 : ℝ) :=
      Finset.sum_le_sum fun i _ => by nlinarith [(hw i).1, (hw i).2]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_neg, mul_one] at hl hr
    exact ⟨hl, hr⟩
  have hzb := hsz hz
  have hxb := hsz hx
  have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg _
  have hb : (0 : ℝ) ≤ b := Nat.cast_nonneg _
  have hWl : -ν ≤ W := by rw [hW]; linarith only [hzb.1, hxb.1, hcount, ha, hb]
  have hstat2 : (u 2 - Real.sqrt (2 * (Δ / 2))) * ν ≤ τ ^ 2 * W := by
    rw [hW]
    linarith only [hstat]
  have hc0 : 0 ≤ 1 - τ ^ 2 := by
    rw [hτe]
    nlinarith [he.1, he.2]
  have hc1 : 1 - τ ^ 2 ≤ η := by
    rw [hτe]
    nlinarith [he.1, he.2, sq_nonneg e]
  have hp := mul_nonneg hc0 (show 0 ≤ W + ν by linarith only [hWl])
  have hq := mul_le_mul_of_nonneg_right hc1 hν.le
  nlinarith only [hstat2, hp, hq]

end
end CatalanMeasure.GenD.Signed.RouteI.CompletedGas




/-!
# The finite chordal kernel

The finite kernel `K_L` is a negative Gram kernel of bounded features, so the tangent inequality
for a particle list against a reference measure needs only products of bounded integrals.
-/

namespace CatalanMeasure.GenD.Signed.RouteI.CompletedGas

open Finset MeasureTheory Complex
open scoped BigOperators

noncomputable section

/-- A general Gram kernel tangent. -/
theorem gram_kernel_tangent {Φ Y : Type*} [Fintype Φ] [MeasurableSpace Y] (q : Measure Y)
    [IsFiniteMeasure q] (b : Φ → ℝ) (hb : ∀ φ, 0 ≤ b φ) (F : Φ → Y → ℝ)
    (hF : ∀ φ, Integrable (F φ) q) {m : ℕ} (z : Fin m → Y) (n : ℝ) :
    let K : Y → Y → ℝ := fun v w => -∑ φ, b φ * F φ v * F φ w
    ∑ i, ∑ j, K (z i) (z j) ≤
      2 * n * ∑ i, ∫ w, K (z i) w ∂q - n ^ 2 * ∫ v, ∫ w, K v w ∂q ∂q := by
  intro K
  set M : Φ → ℝ := fun φ => ∫ w, F φ w ∂q with hM
  have h1 : ∀ v, ∫ w, K v w ∂q = -∑ φ, b φ * F φ v * M φ := by
    intro v
    simp only [K]
    rw [integral_neg, integral_finset_sum _ fun φ _ => (hF φ).const_mul _]
    simp only [integral_const_mul, hM]
  have h2 : ∫ v, ∫ w, K v w ∂q ∂q = -∑ φ, b φ * M φ * M φ := by
    simp only [h1]
    rw [integral_neg, integral_finset_sum _ fun φ _ =>
      ((hF φ).const_mul _).mul_const _]
    simp only [integral_mul_const, integral_const_mul, hM]
  rw [h2]
  simp only [h1]
  set S : Φ → ℝ := fun φ => ∑ i, F φ (z i) with hSd
  have hS : ∑ i, ∑ j, K (z i) (z j) = -∑ φ, b φ * S φ ^ 2 := by
    have e : ∀ φ, b φ * S φ ^ 2 = ∑ i, ∑ j, b φ * F φ (z i) * F φ (z j) := by
      intro φ
      simp only [hSd]
      rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => by ring
    simp only [e, K, Finset.sum_neg_distrib]
    congr 1
    symm
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
  have hL : ∑ i, -∑ φ, b φ * F φ (z i) * M φ = -∑ φ, b φ * S φ * M φ := by
    simp only [Finset.sum_neg_distrib]
    rw [Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl fun φ _ => ?_
    simp only [hSd, Finset.mul_sum, Finset.sum_mul]
  rw [hS, hL]
  have key : ∀ φ, 0 ≤ b φ * (S φ - n * M φ) ^ 2 := fun φ =>
    mul_nonneg (hb φ) (sq_nonneg _)
  have hsum := Finset.sum_nonneg fun φ (_ : φ ∈ (Finset.univ : Finset Φ)) => key φ
  have expand : ∑ φ, b φ * (S φ - n * M φ) ^ 2 =
      ∑ φ, b φ * S φ ^ 2 - 2 * n * ∑ φ, b φ * S φ * M φ + n ^ 2 * ∑ φ, b φ * M φ * M φ := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun φ _ => by ring
  linarith

/-! ### The chordal features -/

/-- `1+|z|^2`. -/
def cden (z : ℂ) : ℝ := 1 + normSq z

theorem cden_pos (z : ℂ) : 0 < cden z := by
  have := normSq_nonneg z
  unfold cden
  linarith

/-- The four bounded coordinates of stereographic projection. -/
def cfeat (i : Fin 4) (z : ℂ) : ℝ :=
  match i with
  | 0 => 1
  | 1 => z.re / cden z
  | 2 => z.im / cden z
  | 3 => (normSq z - 1) / cden z

/-- Their weights. -/
def cwt (i : Fin 4) : ℝ :=
  match i with
  | 0 => 1 / 2
  | 1 => 2
  | 2 => 2
  | 3 => 1 / 2

theorem cwt_nonneg (i : Fin 4) : 0 ≤ cwt i := by
  fin_cases i <;> simp [cwt]

/-- `1 - d_ch^2`, as a positive kernel. -/
def chordC (z w : ℂ) : ℝ := ∑ i, cwt i * cfeat i z * cfeat i w

/-- The squared chordal distance. -/
def chordD2 (z w : ℂ) : ℝ := normSq (z - w) / (cden z * cden w)

theorem chordC_eq (z w : ℂ) : chordC z w = 1 - chordD2 z w := by
  have h1 := (cden_pos z).ne'
  have h2 := (cden_pos w).ne'
  simp only [chordC, chordD2, Fin.sum_univ_four, cfeat, cwt]
  field_simp
  simp only [cden, normSq_apply, sub_re, sub_im]
  ring

theorem chordC_eq_sq (z w : ℂ) :
    chordC z w = normSq (1 + z * (starRingEnd ℂ) w) / (cden z * cden w) := by
  have h1 := (cden_pos z).ne'
  have h2 := (cden_pos w).ne'
  rw [chordC_eq, chordD2]
  field_simp
  simp only [cden, normSq_apply, sub_re, sub_im, add_re, add_im, mul_re, mul_im, one_re, one_im,
    conj_re, conj_im]
  ring

theorem chordC_nonneg (z w : ℂ) : 0 ≤ chordC z w := by
  rw [chordC_eq_sq]
  exact div_nonneg (normSq_nonneg _) (mul_pos (cden_pos z) (cden_pos w)).le

theorem chordD2_nonneg (z w : ℂ) : 0 ≤ chordD2 z w :=
  div_nonneg (normSq_nonneg _) (mul_pos (cden_pos z) (cden_pos w)).le

theorem chordC_le_one (z w : ℂ) : chordC z w ≤ 1 := by
  rw [chordC_eq]
  linarith [chordD2_nonneg z w]

theorem chordD2_le_one (z w : ℂ) : chordD2 z w ≤ 1 := by
  have := chordC_nonneg z w
  rw [chordC_eq] at this
  linarith

theorem chordD2_self (z : ℂ) : chordD2 z z = 0 := by
  simp [chordD2]

theorem chordD2_pos {z w : ℂ} (h : z ≠ w) : 0 < chordD2 z w :=
  div_pos (normSq_pos.mpr (sub_ne_zero.mpr h)) (mul_pos (cden_pos z) (cden_pos w))

/-- The finite chordal kernel. -/
def chordK (L : ℕ) (z w : ℂ) : ℝ :=
  -(1 / 2) * ∑ j ∈ Finset.range L, chordC z w ^ (j + 1) / ((j : ℝ) + 1)

/-- The logarithm of the chordal distance. -/
def logChord (z w : ℂ) : ℝ := (1 / 2) * Real.log (chordD2 z w)

/-- Harmonic number. -/
def harm (L : ℕ) : ℝ := ∑ j ∈ Finset.range L, 1 / ((j : ℝ) + 1)

theorem chordK_self (L : ℕ) (z : ℂ) : chordK L z z = -(1 / 2) * harm L := by
  have h : chordC z z = 1 := by rw [chordC_eq, chordD2_self, sub_zero]
  simp [chordK, harm, h]

theorem hasSum_chord {z w : ℂ} (h : z ≠ w) :
    HasSum (fun j : ℕ => chordC z w ^ (j + 1) / ((j : ℝ) + 1)) (-Real.log (chordD2 z w)) := by
  have hc0 := chordC_nonneg z w
  have hc1 : chordC z w < 1 := by
    rw [chordC_eq]
    linarith [chordD2_pos h]
  have := Real.hasSum_pow_div_log_of_abs_lt_one (x := chordC z w) (by
    rw [abs_of_nonneg hc0]
    exact hc1)
  have e : 1 - chordC z w = chordD2 z w := by
    rw [chordC_eq]
    ring
  rw [e] at this
  exact this

theorem chord_term_nonneg (z w : ℂ) (j : ℕ) :
    0 ≤ chordC z w ^ (j + 1) / ((j : ℝ) + 1) :=
  div_nonneg (pow_nonneg (chordC_nonneg z w) _) (by positivity)

/-- The logarithm lies below every finite kernel. -/
theorem logChord_le_chordK (L : ℕ) {z w : ℂ} (h : z ≠ w) : logChord z w ≤ chordK L z w := by
  have hs := sum_le_hasSum (Finset.range L) (fun j _ => chord_term_nonneg z w j) (hasSum_chord h)
  unfold logChord chordK
  linarith

theorem chordK_nonpos (L : ℕ) (z w : ℂ) : chordK L z w ≤ 0 := by
  have : 0 ≤ ∑ j ∈ Finset.range L, chordC z w ^ (j + 1) / ((j : ℝ) + 1) :=
    Finset.sum_nonneg fun j _ => chord_term_nonneg z w j
  unfold chordK
  linarith

/-- Tail of the kernel. -/
theorem chordK_sub_log_le {z w : ℂ} {h : ℝ} (h0 : 0 < h) (hd : h ≤ chordD2 z w) (L : ℕ) :
    chordK L z w - logChord z w ≤ (1 - h) ^ (L + 1) / (2 * h) := by
  have hne : z ≠ w := by
    rintro rfl
    rw [chordD2_self] at hd
    linarith
  have hsum := hasSum_chord hne
  have hc0 := chordC_nonneg z w
  have hc1 : chordC z w ≤ 1 - h := by
    rw [chordC_eq]
    linarith
  have h1 : 0 ≤ 1 - h := hc0.trans hc1
  have htail := (hasSum_nat_add_iff' (f := fun j : ℕ => chordC z w ^ (j + 1) / ((j : ℝ) + 1))
    L).mpr hsum
  have hgeo : HasSum (fun j : ℕ => (1 - h) ^ (L + 1) * (1 - h) ^ j)
      ((1 - h) ^ (L + 1) * (1 - (1 - h))⁻¹) := by
    refine (hasSum_geometric_of_lt_one h1 ?_).mul_left _
    linarith
  have hle := hasSum_le (fun j => ?_) htail hgeo
  · have e : chordK L z w - logChord z w =
        (1 / 2) * (-Real.log (chordD2 z w) -
          ∑ j ∈ Finset.range L, chordC z w ^ (j + 1) / ((j : ℝ) + 1)) := by
      unfold chordK logChord
      ring
    rw [e]
    have e2 : (1 - (1 - h))⁻¹ = 1 / h := by
      rw [one_div]
      congr 1
      ring
    rw [e2] at hle
    calc _ ≤ (1 / 2) * ((1 - h) ^ (L + 1) * (1 / h)) := by gcongr
      _ = _ := by field_simp
  · have hj : (1 : ℝ) ≤ ((j + L : ℕ) : ℝ) + 1 := by
      have : (0 : ℝ) ≤ ((j + L : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith
    calc chordC z w ^ (j + L + 1) / (((j + L : ℕ) : ℝ) + 1)
        ≤ chordC z w ^ (j + L + 1) := div_le_self (pow_nonneg hc0 _) hj
      _ ≤ (1 - h) ^ (j + L + 1) := pow_le_pow_left₀ hc0 hc1 _
      _ = (1 - h) ^ (L + 1) * (1 - h) ^ j := by rw [← pow_add]; congr 1; omega

/-! ### Features of the finite kernel -/

/-- The feature index of `K_L`. -/
abbrev ChordIdx (L : ℕ) := Σ j : Fin L, (Fin ((j : ℕ) + 1) → Fin 4)

/-- Feature. -/
def chordF {L : ℕ} (φ : ChordIdx L) (z : ℂ) : ℝ := ∏ l, cfeat (φ.2 l) z

/-- Feature weight. -/
def chordB {L : ℕ} (φ : ChordIdx L) : ℝ :=
  (1 / 2) * (1 / (((φ.1 : ℕ) : ℝ) + 1)) * ∏ l, cwt (φ.2 l)

theorem chordB_nonneg {L : ℕ} (φ : ChordIdx L) : 0 ≤ chordB φ := by
  unfold chordB
  have : 0 ≤ ∏ l, cwt (φ.2 l) := Finset.prod_nonneg fun l _ => cwt_nonneg _
  positivity

theorem chordK_features (L : ℕ) (z w : ℂ) :
    chordK L z w = -∑ φ : ChordIdx L, chordB φ * chordF φ z * chordF φ w := by
  rw [Fintype.sum_sigma]
  unfold chordK
  rw [Finset.sum_range, Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have e : chordC z w ^ ((j : ℕ) + 1) =
      ∑ I : Fin ((j : ℕ) + 1) → Fin 4, ∏ l, (cwt (I l) * cfeat (I l) z * cfeat (I l) w) := by
    rw [chordC, Fintype.sum_pow]
  rw [e, Finset.sum_div, Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun I _ => ?_
  simp only [chordB, chordF, Finset.prod_mul_distrib]
  ring

end
end CatalanMeasure.GenD.Signed.RouteI.CompletedGas




namespace CatalanMeasure.GenD.Signed.RouteI.CompletedGas

open Finset MeasureTheory Complex Filter
open scoped BigOperators ENNReal Topology

noncomputable section

theorem cden_continuous : Continuous cden := by
  unfold cden
  exact continuous_const.add Complex.continuous_normSq

theorem cfeat_continuous (i : Fin 4) : Continuous (cfeat i) := by
  have hd : ∀ z, cden z ≠ 0 := fun z => (cden_pos z).ne'
  fin_cases i
  · exact continuous_const
  · exact Complex.continuous_re.div cden_continuous hd
  · exact Complex.continuous_im.div cden_continuous hd
  · exact (Complex.continuous_normSq.sub continuous_const).div cden_continuous hd

theorem cfeat_abs_le (i : Fin 4) (z : ℂ) : |cfeat i z| ≤ 1 := by
  have hp := cden_pos z
  have hn := normSq_nonneg z
  have hs : normSq z = z.re * z.re + z.im * z.im := normSq_apply z
  fin_cases i
  · simp [cfeat]
  · change |z.re / cden z| ≤ 1
    rw [abs_div, abs_of_pos hp, div_le_one hp, abs_le]
    unfold cden
    constructor <;> nlinarith [sq_nonneg (z.re + 1), sq_nonneg (z.re - 1), mul_self_nonneg z.im]
  · change |z.im / cden z| ≤ 1
    rw [abs_div, abs_of_pos hp, div_le_one hp, abs_le]
    unfold cden
    constructor <;> nlinarith [sq_nonneg (z.im + 1), sq_nonneg (z.im - 1), mul_self_nonneg z.re]
  · change |(normSq z - 1) / cden z| ≤ 1
    rw [abs_div, abs_of_pos hp, div_le_one hp, abs_le]
    unfold cden
    constructor <;> linarith

theorem chordF_continuous {L : ℕ} (φ : ChordIdx L) : Continuous (chordF φ) := by
  unfold chordF
  exact continuous_finset_prod _ fun l _ => cfeat_continuous _

theorem chordF_abs_le {L : ℕ} (φ : ChordIdx L) (z : ℂ) : |chordF φ z| ≤ 1 := by
  unfold chordF
  rw [Finset.abs_prod]
  exact Finset.prod_le_one₀ (fun l _ => abs_nonneg _) fun l _ => cfeat_abs_le _ _

variable (q : Measure ℂ) [IsFiniteMeasure q]

theorem chordF_integrable {L : ℕ} (φ : ChordIdx L) : Integrable (chordF φ) q :=
  Integrable.of_bound (chordF_continuous φ).aestronglyMeasurable 1
    (Eventually.of_forall fun z => by simpa using chordF_abs_le φ z)

theorem chordK_integrable (L : ℕ) (z : ℂ) : Integrable (chordK L z) q := by
  have e : chordK L z = fun w => -∑ φ : ChordIdx L, chordB φ * chordF φ z * chordF φ w := by
    funext w
    exact chordK_features L z w
  rw [e]
  exact (integrable_finset_sum _ fun φ _ => (chordF_integrable q φ).const_mul _).neg

/-- **The finite tangent.** -/
theorem chordK_tangent (L : ℕ) {m : ℕ} (z : Fin m → ℂ) (n : ℝ) :
    ∑ i, ∑ j, chordK L (z i) (z j) ≤
      2 * n * ∑ i, ∫ w, chordK L (z i) w ∂q - n ^ 2 * ∫ v, ∫ w, chordK L v w ∂q ∂q := by
  have h := gram_kernel_tangent q (chordB (L := L)) chordB_nonneg chordF
    (fun φ => chordF_integrable q φ) z n
  simp only [← chordK_features] at h
  exact h

/-- Chordal ball bound with the square-root exponent. -/
def ChordBall (C : ℝ) : Prop :=
  ∀ z : ℂ, ∀ t : ℝ, 0 < t → t ≤ 1 → q {w | chordD2 z w ≤ t ^ 4} ≤ ENNReal.ofReal (C * t)

theorem chordD2_continuous (z : ℂ) : Continuous (chordD2 z) := by
  unfold chordD2
  refine (Complex.continuous_normSq.comp (continuous_const.sub continuous_id)).div
    (continuous_const.mul cden_continuous) fun w => (mul_pos (cden_pos z) (cden_pos w)).ne'

theorem measurableSet_ball (z : ℂ) (r : ℝ) : MeasurableSet {w | chordD2 z w ≤ r} :=
  measurableSet_le (chordD2_continuous z).measurable measurable_const

theorem logChord_measurable (z : ℂ) : Measurable (logChord z) := by
  unfold logChord
  exact ((Real.measurable_log).comp (chordD2_continuous z).measurable).const_mul _

theorem logChord_nonpos (z w : ℂ) : logChord z w ≤ 0 := by
  unfold logChord
  have := Real.log_nonpos (chordD2_nonneg z w) (chordD2_le_one z w)
  linarith

/-- Staircase domination of the logarithm near the centre. -/
theorem log_staircase {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (z w : ℂ) :
    ({w | chordD2 z w ≤ t ^ 4} : Set ℂ).indicator
        (fun w => ENNReal.ofReal (-logChord z w)) w ≤
      ({w | chordD2 z w ≤ t ^ 4} : Set ℂ).indicator (fun _ => ENNReal.ofReal (-2 * Real.log t)) w +
      ∑' j : ℕ, ({w | chordD2 z w ≤ (t / 2 ^ j) ^ 4} : Set ℂ).indicator
        (fun _ => ENNReal.ofReal (2 * Real.log 2)) w := by
  by_cases hS : chordD2 z w ≤ t ^ 4
  swap
  · rw [Set.indicator_of_notMem (by simpa using hS)]
    exact zero_le
  rw [Set.indicator_of_mem (by simpa using hS), Set.indicator_of_mem (by simpa using hS)]
  have hd0 := chordD2_nonneg z w
  rcases hd0.eq_or_lt with h0 | h0
  · have : logChord z w = 0 := by simp [logChord, ← h0]
    simp [this]
  have hex : ∃ j : ℕ, (t / 2 ^ j) ^ 4 < chordD2 z w := by
    obtain ⟨j, hj⟩ := exists_pow_lt_of_lt_one h0 (show (1 / 2 : ℝ) < 1 by norm_num)
    refine ⟨j, lt_of_le_of_lt ?_ hj⟩
    have h1 : t / 2 ^ j ≤ (1 / 2) ^ j := by
      rw [one_div, inv_pow, div_eq_mul_inv]
      have : (0 : ℝ) ≤ (2 ^ j)⁻¹ := by positivity
      nlinarith
    have h2 : 0 ≤ t / 2 ^ j := by positivity
    have h3 : (1 / 2 : ℝ) ^ j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    calc (t / 2 ^ j) ^ 4 ≤ (t / 2 ^ j) ^ 1 :=
          pow_le_pow_of_le_one h2 (h1.trans h3) (by norm_num)
      _ ≤ _ := by simpa using h1
  classical
  set J := Nat.find hex with hJ
  have hJs : (t / 2 ^ J) ^ 4 < chordD2 z w := Nat.find_spec hex
  have hJ0 : J ≠ 0 := by
    intro h
    rw [h] at hJs
    simp at hJs
    linarith
  obtain ⟨I, hI⟩ := Nat.exists_eq_succ_of_ne_zero hJ0
  have hle : ∀ j ≤ I, chordD2 z w ≤ (t / 2 ^ j) ^ 4 := by
    intro j hj
    have := Nat.find_min hex (m := j) (by omega)
    exact not_lt.mp this
  have hsum : ∑ j ∈ Finset.range (I + 1), ({w | chordD2 z w ≤ (t / 2 ^ j) ^ 4} : Set ℂ).indicator
        (fun _ => ENNReal.ofReal (2 * Real.log 2)) w =
      ENNReal.ofReal ((I + 1 : ℕ) * (2 * Real.log 2)) := by
    have hl2 : 0 ≤ 2 * Real.log 2 := by
      have := Real.log_pos (show (1 : ℝ) < 2 by norm_num)
      linarith
    rw [Finset.sum_congr rfl fun j hj => Set.indicator_of_mem
      (show w ∈ {w | chordD2 z w ≤ (t / 2 ^ j) ^ 4} from hle j
        (by have := Finset.mem_range.mp hj; omega)) _]
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  have hbound : -logChord z w ≤ -2 * Real.log t + (I + 1 : ℕ) * (2 * Real.log 2) := by
    have hlog : Real.log ((t / 2 ^ J) ^ 4) ≤ Real.log (chordD2 z w) :=
      Real.log_le_log (by positivity) hJs.le
    rw [Real.log_pow, Real.log_div ht.ne' (by positivity), Real.log_pow, hI] at hlog
    unfold logChord
    push_cast at hlog ⊢
    linarith
  have ht0 : 0 ≤ -2 * Real.log t := by
    have := Real.log_nonpos ht.le ht1
    linarith
  calc ENNReal.ofReal (-logChord z w)
      ≤ ENNReal.ofReal (-2 * Real.log t + (I + 1 : ℕ) * (2 * Real.log 2)) :=
        ENNReal.ofReal_le_ofReal hbound
    _ = ENNReal.ofReal (-2 * Real.log t) + ENNReal.ofReal ((I + 1 : ℕ) * (2 * Real.log 2)) :=
        ENNReal.ofReal_add ht0 (by
          have := Real.log_pos (show (1 : ℝ) < 2 by norm_num)
          positivity)
    _ ≤ _ := by
        gcongr
        rw [← hsum]
        exact ENNReal.sum_le_tsum _

variable {q}

/-- The logarithmic mass of a small chordal ball. -/
theorem log_ball_le {C : ℝ} (hC : 0 ≤ C) (hb : ChordBall q C) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (z : ℂ) :
    ∫⁻ w, ({w | chordD2 z w ≤ t ^ 4} : Set ℂ).indicator
        (fun w => ENNReal.ofReal (-logChord z w)) w ∂q ≤
      ENNReal.ofReal (C * t * (-2 * Real.log t + 4 * Real.log 2)) := by
  have hl2 : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
  have ht0 : 0 ≤ -2 * Real.log t := by
    have := Real.log_nonpos ht.le ht1
    linarith
  have hmeas : ∀ j : ℕ, Measurable (({w | chordD2 z w ≤ (t / 2 ^ j) ^ 4} : Set ℂ).indicator
        (fun _ => ENNReal.ofReal (2 * Real.log 2))) := fun j =>
    measurable_const.indicator (measurableSet_ball z _)
  calc _ ≤ ∫⁻ w, (({w | chordD2 z w ≤ t ^ 4} : Set ℂ).indicator
          (fun _ => ENNReal.ofReal (-2 * Real.log t)) w +
        ∑' j : ℕ, ({w | chordD2 z w ≤ (t / 2 ^ j) ^ 4} : Set ℂ).indicator
          (fun _ => ENNReal.ofReal (2 * Real.log 2)) w) ∂q :=
        lintegral_mono fun w => log_staircase ht ht1 z w
    _ = ENNReal.ofReal (-2 * Real.log t) * q {w | chordD2 z w ≤ t ^ 4} +
        ∑' j : ℕ, ENNReal.ofReal (2 * Real.log 2) * q {w | chordD2 z w ≤ (t / 2 ^ j) ^ 4} := by
        rw [lintegral_add_left (measurable_const.indicator (measurableSet_ball z _)),
          lintegral_indicator_const (measurableSet_ball z _), lintegral_tsum
            (fun j => (hmeas j).aemeasurable)]
        congr 1
        refine tsum_congr fun j => ?_
        rw [lintegral_indicator_const (measurableSet_ball z _)]
    _ ≤ ENNReal.ofReal (-2 * Real.log t) * ENNReal.ofReal (C * t) +
        ∑' j : ℕ, ENNReal.ofReal (2 * Real.log 2) * ENNReal.ofReal (C * t * (1 / 2) ^ j) := by
        gcongr with j
        · exact hb z t ht ht1
        · have h1 : t / 2 ^ j ≤ 1 := by
            rw [div_le_one (by positivity)]
            exact ht1.trans (one_le_pow₀ (by norm_num))
          have := hb z (t / 2 ^ j) (by positivity) h1
          refine this.trans (le_of_eq ?_)
          congr 1
          rw [one_div, inv_pow]
          field_simp
    _ = _ := by
        have hsum : HasSum (fun j : ℕ => 2 * Real.log 2 * (C * t * (1 / 2) ^ j))
            (2 * Real.log 2 * (C * t * 2)) := by
          have := (hasSum_geometric_two).mul_left (2 * Real.log 2 * (C * t))
          convert this using 1
          · funext j
            ring
          · ring
        have hnn : ∀ j : ℕ, 0 ≤ 2 * Real.log 2 * (C * t * (1 / 2) ^ j) := fun j => by positivity
        have ht' : ∑' j : ℕ, ENNReal.ofReal (2 * Real.log 2) *
            ENNReal.ofReal (C * t * (1 / 2) ^ j) =
            ENNReal.ofReal (2 * Real.log 2 * (C * t * 2)) := by
          simp only [← ENNReal.ofReal_mul (show 0 ≤ 2 * Real.log 2 by positivity)]
          rw [← ENNReal.ofReal_tsum_of_nonneg hnn hsum.summable, hsum.tsum_eq]
        rw [ht', ← ENNReal.ofReal_mul ht0, ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

theorem logChord_integrable {C : ℝ} (hC : 0 ≤ C) (hb : ChordBall q C) (z : ℂ) :
    Integrable (logChord z) q := by
  have hneg : Integrable (fun w => -logChord z w) q := by
    refine ⟨(logChord_measurable z).neg.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun w => by
      have := logChord_nonpos z w
      simp only [Pi.zero_apply]
      linarith)]
    have h := log_ball_le hC hb one_pos le_rfl z
    have e : ({w | chordD2 z w ≤ (1 : ℝ) ^ 4} : Set ℂ) = Set.univ := by
      ext w
      simpa using chordD2_le_one z w
    rw [e] at h
    simp only [Set.indicator_univ] at h
    exact lt_of_le_of_lt h ENNReal.ofReal_lt_top
  simpa using hneg.neg

/-- Choice of a small radius. -/
theorem exists_small_radius {C η : ℝ} (hη : 0 < η) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧ C * t * (-2 * Real.log t + 4 * Real.log 2) ≤ η := by
  have hc : Continuous fun t : ℝ => C * (-2 * (t * Real.log t) + t * (4 * Real.log 2)) := by
    have := Real.continuous_mul_log
    fun_prop
  have h0 := hc.tendsto 0
  simp only [zero_mul, mul_zero, add_zero] at h0
  have hev := h0.eventually (gt_mem_nhds hη)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨min (δ / 2) (1 / 2), by positivity, by
    have := min_le_right (δ / 2) (1 / 2 : ℝ)
    linarith, ?_⟩
  have hp : 0 < min (δ / 2) (1 / 2 : ℝ) := by positivity
  have := @hball (min (δ / 2) (1 / 2)) (by
    rw [Real.dist_eq, sub_zero, abs_of_pos hp]
    have := min_le_left (δ / 2) (1 / 2 : ℝ)
    linarith)
  calc _ = C * (-2 * (min (δ / 2) (1 / 2) * Real.log (min (δ / 2) (1 / 2))) +
        min (δ / 2) (1 / 2) * (4 * Real.log 2)) := by ring
    _ ≤ η := this.le

/-- **Uniform reference error.** The finite potentials converge to the logarithmic potential
uniformly in the evaluation point, by the ball bound alone. -/
theorem chord_reference_error {C : ℝ} (hC : 0 ≤ C) (hb : ChordBall q C) {η : ℝ} (hη : 0 < η) :
    ∃ L₀ : ℕ, ∀ L, L₀ ≤ L → ∀ z : ℂ,
      ∫ w, chordK L z w ∂q ≤ ∫ w, logChord z w ∂q + η := by
  obtain ⟨t, ht, ht1, hB⟩ := exists_small_radius (C := C) (η := η / 2) (by positivity)
  set h := t ^ 4 with hh
  have hh0 : 0 < h := by positivity
  have hh1 : h < 1 := pow_lt_one₀ ht.le ht1 (by norm_num)
  set Q := q.real Set.univ with hQ
  have hQ0 : 0 ≤ Q := measureReal_nonneg
  have hlim : Tendsto (fun L : ℕ => (1 - h) ^ (L + 1) / (2 * h) * Q) atTop (𝓝 0) := by
    have h1 := tendsto_pow_atTop_nhds_zero_of_lt_one (show 0 ≤ 1 - h by linarith)
      (show 1 - h < 1 by linarith)
    have h2 := ((tendsto_add_atTop_iff_nat 1).mpr h1).div_const (2 * h)
    have h3 := h2.mul_const Q
    simpa using h3
  obtain ⟨L₀, hL₀⟩ := ((hlim.eventually (gt_mem_nhds (show 0 < η / 2 by positivity)))).exists
  refine ⟨L₀, fun L hL z => ?_⟩
  set T := (1 - h) ^ (L + 1) / (2 * h) with hT
  have hT0 : 0 ≤ T := by
    have : 0 ≤ 1 - h := by linarith
    positivity
  have hTle : T * Q ≤ η / 2 := by
    have h1 : (1 - h) ^ (L + 1) ≤ (1 - h) ^ (L₀ + 1) :=
      pow_le_pow_of_le_one (by linarith) (by linarith) (by omega)
    have h2 : T ≤ (1 - h) ^ (L₀ + 1) / (2 * h) := by
      rw [hT]
      gcongr
    calc T * Q ≤ (1 - h) ^ (L₀ + 1) / (2 * h) * Q := by gcongr
      _ ≤ η / 2 := hL₀.le
  have hlogI := logChord_integrable hC hb z
  set S : Set ℂ := {w | chordD2 z w ≤ h} with hS
  have hSm : MeasurableSet S := measurableSet_ball z h
  set g : ℂ → ℝ := S.indicator fun w => -logChord z w with hg
  have hgI : Integrable g q := hlogI.neg.indicator hSm
  have hg0 : ∀ w, 0 ≤ g w := fun w => by
    refine Set.indicator_nonneg (fun w _ => ?_) w
    have := logChord_nonpos z w
    linarith
  have hpt : ∀ w, chordK L z w - logChord z w ≤ T + g w := by
    intro w
    by_cases hw : w ∈ S
    · have e : g w = -logChord z w := Set.indicator_of_mem hw _
      rw [e]
      linarith [chordK_nonpos L z w]
    · have e : g w = 0 := Set.indicator_of_notMem hw _
      rw [e, add_zero]
      exact chordK_sub_log_le hh0 (le_of_lt (not_le.mp hw)) L
  have hint : ∫ w, (chordK L z w - logChord z w) ∂q ≤ ∫ w, (T + g w) ∂q :=
    integral_mono ((chordK_integrable q L z).sub hlogI) ((integrable_const T).add hgI) hpt
  rw [integral_sub (chordK_integrable q L z) hlogI,
    integral_add (integrable_const T) hgI, integral_const, smul_eq_mul] at hint
  have hgle : ∫ w, g w ∂q ≤ η / 2 := by
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hg0) hgI.aestronglyMeasurable]
    have h1 : ∫⁻ w, ENNReal.ofReal (g w) ∂q ≤
        ENNReal.ofReal (C * t * (-2 * Real.log t + 4 * Real.log 2)) := by
      refine le_trans (lintegral_mono fun w => ?_) (log_ball_le hC hb ht ht1.le z)
      by_cases hw : w ∈ S
      · rw [show g w = -logChord z w from Set.indicator_of_mem hw _,
          Set.indicator_of_mem (show w ∈ {w | chordD2 z w ≤ t ^ 4} from hw)]
      · rw [show g w = 0 from Set.indicator_of_notMem hw _]
        simp
    have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
    have ht0 : 0 ≤ C * t * (-2 * Real.log t + 4 * Real.log 2) := by
      have := Real.log_nonpos ht.le ht1.le
      have hl2 := Real.log_pos (show (1 : ℝ) < 2 by norm_num)
      have : 0 ≤ -2 * Real.log t + 4 * Real.log 2 := by linarith
      positivity
    rw [ENNReal.toReal_ofReal ht0] at h2
    exact h2.trans hB
  have hQe : q.real Set.univ = Q := rfl
  rw [hQe] at hint
  nlinarith

end
end CatalanMeasure.GenD.Signed.RouteI.CompletedGas




namespace CatalanMeasure.GenD.Signed.RouteI.CompletedGas

open Finset MeasureTheory Complex Filter
open scoped BigOperators ENNReal Topology

noncomputable section

/-- Symmetric double sums. -/
theorem sum_sym_pairs {m : ℕ} (g : Fin m → Fin m → ℝ) (hs : ∀ i j, g i j = g j i) :
    ∑ i, ∑ j, g i j = ∑ i, g i i + 2 * ∑ i, ∑ j ∈ Finset.Ioi i, g i j := by
  have hI : ∀ i (f : Fin m → ℝ), ∑ j ∈ Finset.Ioi i, f j = ∑ j, if i < j then f j else 0 := by
    intro i f
    rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext j
    simp
  have h1 : ∀ i, ∑ j, g i j = (∑ j, if j < i then g i j else 0) + g i i +
      ∑ j, if i < j then g i j else 0 := by
    intro i
    have e : ∀ j, g i j = (if j < i then g i j else 0) + (if j = i then g i j else 0) +
        (if i < j then g i j else 0) := by
      intro j
      rcases lt_trichotomy j i with h | h | h
      · simp [h, h.ne, h.le, not_lt.mpr h.le]
      · simp [h]
      · simp [h, h.ne', not_lt.mpr h.le]
    conv_lhs => rw [Finset.sum_congr rfl fun j _ => e j]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    simp
  have h2 : ∑ i, ∑ j, (if j < i then g i j else 0) = ∑ i, ∑ j, if i < j then g i j else 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hs j i]
  simp only [hI, h1, Finset.sum_add_distrib]
  rw [h2]
  ring

/-- The planar self-interaction of a list. -/
def pairLog {m : ℕ} (z : Fin m → ℂ) (i j : Fin m) : ℝ :=
  if i = j then 0 else Real.log ‖z i - z j‖

theorem vandermonde_sq_eq {m : ℕ} {z : Fin m → ℂ} (hz : Function.Injective z) :
    ‖(Matrix.vandermonde z).det‖ ^ 2 = Real.exp (∑ i, ∑ j, pairLog z i j) := by
  have hs : ∀ i j, pairLog z i j = pairLog z j i := by
    intro i j
    unfold pairLog
    by_cases h : i = j
    · simp [h]
    · rw [if_neg h, if_neg (Ne.symm h), norm_sub_rev]
  rw [sum_sym_pairs _ hs]
  have hd : ∀ i, pairLog z i i = 0 := fun i => by simp [pairLog]
  simp only [hd, Finset.sum_const_zero, zero_add]
  rw [Matrix.det_vandermonde, norm_prod]
  have hpos : ∀ i j, i < j → 0 < ‖z j - z i‖ := fun i j h =>
    norm_pos_iff.mpr (sub_ne_zero.mpr (fun e => h.ne (hz e).symm))
  have e : ∏ i, ‖∏ j ∈ Finset.Ioi i, (z j - z i)‖ =
      Real.exp (∑ i, ∑ j ∈ Finset.Ioi i, pairLog z i j) := by
    rw [Real.exp_sum]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [norm_prod, Real.exp_sum]
    refine Finset.prod_congr rfl fun j hj => ?_
    have hij : i < j := Finset.mem_Ioi.mp hj
    have : pairLog z i j = Real.log ‖z j - z i‖ := by
      simp only [pairLog, if_neg hij.ne]
      rw [norm_sub_rev]
    rw [this, Real.exp_log (hpos i j hij)]
  rw [e, ← Real.exp_nat_mul]
  norm_num

/-- `h(z) = (1/2) log(1+|z|^2)`. -/
def chordH (z : ℂ) : ℝ := (1 / 2) * Real.log (cden z)

theorem chordH_nonneg (z : ℂ) : 0 ≤ chordH z := by
  have : 1 ≤ cden z := by
    have := normSq_nonneg z
    unfold cden
    linarith
  have := Real.log_nonneg this
  unfold chordH
  linarith

theorem log_norm_eq_chord {z w : ℂ} (h : z ≠ w) :
    Real.log ‖z - w‖ = logChord z w + chordH z + chordH w := by
  unfold logChord chordH chordD2
  have h1 : normSq (z - w) ≠ 0 := (normSq_pos.mpr (sub_ne_zero.mpr h)).ne'
  have hz := (cden_pos z).ne'
  have hw := (cden_pos w).ne'
  rw [Real.log_div h1 (mul_ne_zero hz hw), Real.log_mul hz hw, normSq_eq_norm_sq, Real.log_pow]
  push_cast
  ring

variable {q : Measure ℂ} [IsFiniteMeasure q]

/-- Planar potential. -/
def planarPot (q : Measure ℂ) (z : ℂ) : ℝ := ∫ w, Real.log ‖z - w‖ ∂q

/-- Planar energy. -/
def planarEnergy (q : Measure ℂ) : ℝ := ∫ v, planarPot q v ∂q

theorem ball_singleton {C : ℝ} (hb : ChordBall q C) (z : ℂ) : q {z} = 0 := by
  have hle : ∀ t : ℝ, 0 < t → t ≤ 1 → q {z} ≤ ENNReal.ofReal (C * t) := by
    intro t ht ht1
    refine (measure_mono ?_).trans (hb z t ht ht1)
    intro w hw
    rw [Set.mem_singleton_iff.mp hw]
    simp only [Set.mem_setOf_eq, chordD2_self]
    positivity
  have hlim : Tendsto (fun t : ℝ => ENNReal.ofReal (C * t)) (𝓝[>] 0) (𝓝 0) := by
    have h1 : Continuous fun t : ℝ => ENNReal.ofReal (C * t) :=
      ENNReal.continuous_ofReal.comp (continuous_const.mul continuous_id)
    have := (h1.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
    simpa using this
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), q {z} ≤ ENNReal.ofReal (C * t) := by
    filter_upwards [Ioc_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
    exact hle t ht.1 ht.2
  exact le_antisymm (ge_of_tendsto hlim hev) zero_le

theorem ae_ne {C : ℝ} (hb : ChordBall q C) (z : ℂ) : ∀ᵐ w ∂q, z ≠ w := by
  have : q {w | ¬ z ≠ w} = 0 := by
    have e : {w | ¬ z ≠ w} = {z} := by
      ext w
      simp [eq_comm]
    rw [e]
    exact ball_singleton hb z
  exact this

theorem logChord_pot_eq {C : ℝ} (hC : 0 ≤ C) (hb : ChordBall q C)
    (hh : Integrable chordH q) (z : ℂ) :
    Integrable (fun w => Real.log ‖z - w‖) q ∧
      ∫ w, logChord z w ∂q = planarPot q z - q.real Set.univ * chordH z - ∫ w, chordH w ∂q := by
  have hl := logChord_integrable hC hb z
  have hae : (fun w => Real.log ‖z - w‖) =ᵐ[q] fun w => logChord z w + chordH z + chordH w := by
    filter_upwards [ae_ne hb z] with w hw
    exact log_norm_eq_chord hw
  have hI : Integrable (fun w => logChord z w + chordH z + chordH w) q :=
    (hl.add (integrable_const _)).add hh
  refine ⟨hI.congr hae.symm, ?_⟩
  unfold planarPot
  have e1 : ∫ w, (logChord z w + chordH z + chordH w) ∂q =
      (∫ w, (logChord z w + chordH z) ∂q) + ∫ w, chordH w ∂q :=
    integral_add (hl.add (integrable_const _)) hh
  have e2 : ∫ w, (logChord z w + chordH z) ∂q =
      (∫ w, logChord z w ∂q) + q.real Set.univ * chordH z := by
    rw [show (∫ w, (logChord z w + chordH z) ∂q) = _ from
      integral_add hl (integrable_const (chordH z)), integral_const, smul_eq_mul]
  rw [integral_congr_ae hae, e1, e2]
  ring

theorem chordPot_measurable :
    Measurable (fun p : ℂ × ℂ => logChord p.1 p.2) := by
  have hc : Continuous fun p : ℂ × ℂ => chordD2 p.1 p.2 := by
    unfold chordD2
    refine (Complex.continuous_normSq.comp (continuous_fst.sub continuous_snd)).div
      ((cden_continuous.comp continuous_fst).mul (cden_continuous.comp continuous_snd))
      fun p => (mul_pos (cden_pos _) (cden_pos _)).ne'
  unfold logChord
  exact (Real.measurable_log.comp hc.measurable).const_mul _

theorem chordPot_integrable {C : ℝ} (hC : 0 ≤ C) (hb : ChordBall q C) :
    Integrable (fun v => ∫ w, logChord v w ∂q) q := by
  have hm : AEStronglyMeasurable (fun v => ∫ w, logChord v w ∂q) q :=
    (chordPot_measurable.stronglyMeasurable.integral_prod_right').aestronglyMeasurable
  refine Integrable.of_bound hm (C * (4 * Real.log 2)) (Eventually.of_forall fun v => ?_)
  have hl := logChord_integrable hC hb v
  have hneg : ∫ w, -logChord v w ∂q ≤ C * (4 * Real.log 2) := by
    have hl' : Integrable (fun w => -logChord v w) q := hl.neg
    rw [integral_eq_lintegral_of_nonneg_ae (f := fun w => -logChord v w)
      (Eventually.of_forall fun w => by
        have := logChord_nonpos v w
        show (0 : ℝ) ≤ -logChord v w
        linarith) hl'.aestronglyMeasurable]
    have h := log_ball_le hC hb one_pos le_rfl v
    have e : ({w | chordD2 v w ≤ (1 : ℝ) ^ 4} : Set ℂ) = Set.univ := by
      ext w
      simpa using chordD2_le_one v w
    rw [e] at h
    simp only [Set.indicator_univ, Real.log_one, mul_zero, zero_add, mul_one] at h
    have hl2 := Real.log_pos (show (1 : ℝ) < 2 by norm_num)
    have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
    rwa [ENNReal.toReal_ofReal (by positivity)] at h2
  have h0 : ∫ w, logChord v w ∂q ≤ 0 :=
    integral_nonpos fun w => logChord_nonpos v w
  rw [Real.norm_eq_abs, abs_of_nonpos h0]
  rw [integral_neg] at hneg
  exact hneg

theorem chordK_energy_ge {C : ℝ} (hC : 0 ≤ C) (hb : ChordBall q C) (L : ℕ) :
    ∫ v, ∫ w, logChord v w ∂q ∂q ≤ ∫ v, ∫ w, chordK L v w ∂q ∂q := by
  have hint : Integrable (fun v => ∫ w, chordK L v w ∂q) q := by
    have e : (fun v => ∫ w, chordK L v w ∂q) = fun v =>
        -∑ φ : ChordIdx L, chordB φ * chordF φ v * ∫ w, chordF φ w ∂q := by
      funext v
      simp only [chordK_features]
      rw [integral_neg, integral_finset_sum _ fun φ _ => (chordF_integrable q φ).const_mul _]
      simp only [integral_const_mul]
    rw [e]
    exact (integrable_finset_sum _ fun φ _ =>
      ((chordF_integrable q φ).const_mul _).mul_const _).neg
  refine integral_mono (chordPot_integrable hC hb) hint fun v => ?_
  refine integral_mono_ae (logChord_integrable hC hb v) (chordK_integrable q L v) ?_
  filter_upwards [ae_ne hb v] with w hw
  exact logChord_le_chordK L hw

/-- **Planar tangent.** The chordal coordinates are gone. The list has exact mass `m = ν q(ℂ)`. -/
theorem planar_tangent {C : ℝ} (hC : 0 ≤ C) (hb : ChordBall q C) (hh : Integrable chordH q)
    {η : ℝ} (hη : 0 < η) :
    ∃ L : ℕ, ∀ (m : ℕ) (ν : ℝ), 0 ≤ ν → ν * q.real Set.univ = m → ∀ z : Fin m → ℂ,
      ‖(Matrix.vandermonde z).det‖ ^ 2 ≤
        Real.exp (2 * ν * ∑ i, planarPot q (z i) - ν ^ 2 * planarEnergy q +
          2 * ν * m * η + m / 2 * harm L) := by
  obtain ⟨L₀, hL⟩ := chord_reference_error hC hb hη
  refine ⟨L₀, fun m ν hν hm z => ?_⟩
  have hLz := hL L₀ le_rfl
  by_cases hz : Function.Injective z
  swap
  · have h0 : (Matrix.vandermonde z).det = 0 := by
      by_contra h
      exact hz (Matrix.det_vandermonde_ne_zero_iff.mp h)
    rw [h0]
    simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    exact (Real.exp_pos _).le
  rw [vandermonde_sq_eq hz]
  apply Real.exp_le_exp.mpr
  set a := q.real Set.univ with ha
  set c := ∫ w, chordH w ∂q with hc
  set K := chordK L₀ with hK
  set Hs := ∑ i, chordH (z i) with hHs
  have hpair : ∀ i j, pairLog z i j ≤
      K (z i) (z j) + chordH (z i) + chordH (z j) -
        (if i = j then K (z i) (z i) + 2 * chordH (z i) else 0) := by
    intro i j
    by_cases hij : i = j
    · subst hij
      simp only [pairLog, if_true]
      linarith
    · have hne : z i ≠ z j := fun e => hij (hz e)
      simp only [pairLog, if_neg hij, sub_zero]
      rw [log_norm_eq_chord hne]
      have := logChord_le_chordK L₀ hne
      linarith
  have hsum : ∑ i, ∑ j, pairLog z i j ≤
      ∑ i, ∑ j, K (z i) (z j) + 2 * m * Hs - ∑ i, (K (z i) (z i) + 2 * chordH (z i)) := by
    calc _ ≤ ∑ i, ∑ j, (K (z i) (z j) + chordH (z i) + chordH (z j) -
          (if i = j then K (z i) (z i) + 2 * chordH (z i) else 0)) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hpair i j
      _ = _ := by
          simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
            Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Finset.sum_ite_eq, Finset.mem_univ,
            if_true, ← Finset.mul_sum, hHs]
          ring
  have hdiag : ∑ i, K (z i) (z i) = -(m / 2 * harm L₀) := by
    simp only [hK, chordK_self, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    ring
  have htan := chordK_tangent q L₀ z ν
  have hU : ∑ i, ∫ w, K (z i) w ∂q ≤
      ∑ i, planarPot q (z i) - a * Hs - m * c + m * η := by
    calc _ ≤ ∑ i, (planarPot q (z i) - a * chordH (z i) - c + η) := by
          refine Finset.sum_le_sum fun i _ => ?_
          have := hLz (z i)
          rw [(logChord_pot_eq hC hb hh (z i)).2] at this
          exact this
      _ = _ := by
          simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
            Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum, hHs]
  have hE : planarEnergy q - 2 * a * c ≤ ∫ v, ∫ w, K v w ∂q ∂q := by
    have h1 := chordK_energy_ge hC hb L₀
    have hpi : Integrable (planarPot q) q := by
      have e : planarPot q = fun v => (∫ w, logChord v w ∂q) + a * chordH v + c := by
        funext v
        rw [(logChord_pot_eq hC hb hh v).2]
        ring
      rw [e]
      exact ((chordPot_integrable hC hb).add (hh.const_mul a)).add (integrable_const c)
    have h2 : ∫ v, ∫ w, logChord v w ∂q ∂q = planarEnergy q - 2 * a * c := by
      have e : (fun v => ∫ w, logChord v w ∂q) = fun v => planarPot q v - a * chordH v - c := by
        funext v
        exact (logChord_pot_eq hC hb hh v).2
      have i1 : Integrable (fun v => planarPot q v - a * chordH v) q :=
        hpi.sub (hh.const_mul a)
      rw [e, show (∫ v, (planarPot q v - a * chordH v - c) ∂q) = _ from
          integral_sub i1 (integrable_const c),
        show (∫ v, (planarPot q v - a * chordH v) ∂q) = _ from
          integral_sub hpi (hh.const_mul a), integral_const_mul, integral_const, smul_eq_mul]
      unfold planarEnergy
      ring
    rw [h2] at h1
    exact h1
  have hHs0 : 0 ≤ Hs := Finset.sum_nonneg fun i _ => chordH_nonneg _
  have hd2 : ∑ i, (K (z i) (z i) + 2 * chordH (z i)) = -(m / 2 * harm L₀) + 2 * Hs := by
    rw [Finset.sum_add_distrib, hdiag, ← Finset.mul_sum]
  rw [hd2] at hsum
  have h3 : 2 * ν * ∑ i, ∫ w, K (z i) w ∂q ≤
      2 * ν * (∑ i, planarPot q (z i) - a * Hs - m * c + m * η) := by gcongr
  have h4 : ν ^ 2 * (planarEnergy q - 2 * a * c) ≤ ν ^ 2 * ∫ v, ∫ w, K v w ∂q ∂q := by gcongr
  have e1 : 2 * ν * (a * Hs) = 2 * m * Hs := by rw [← hm]; ring
  have e2 : ν ^ 2 * (2 * a * c) = 2 * ν * (m * c) := by rw [← hm]; ring
  nlinarith

end
end CatalanMeasure.GenD.Signed.RouteI.CompletedGas





/-!
# Finite determinant inequalities for the completed gas

The finite Andreief identity, Fischer's inequality and the rank-one scaling bound. Fischer's
inequality replaces the exterior-power Cauchy-Schwarz and Jacobi complementary-minor steps of the
paper: applied to the Gram of the two function families it gives their product directly.
-/

namespace CatalanMeasure.GenD.Signed.RouteI.CompletedGas

open Matrix Finset CatalanMeasure.Signed
open scoped BigOperators ComplexOrder

noncomputable section

/-- **Finite Andreief identity**: arbitrary finite point set, any commutative ring. -/
theorem andreief_finite {R : Type*} [CommRing R] {I : Type*} [Fintype I] [DecidableEq I] {k : ℕ}
    (w : I → R) (φ ψ : Fin k → I → R) :
    ∑ t : Fin k → I, (∏ a, w (t a)) *
        ((Matrix.of fun i a => φ i (t a)).det * (Matrix.of fun i a => ψ i (t a)).det) =
      (k.factorial : R) * (Matrix.of fun i j => ∑ x, w x * φ i x * ψ j x).det := by
  classical
  set X : R := ∑ t : Fin k → I, (∏ a, w (t a) * φ a (t a)) *
    (Matrix.of fun i a => ψ i (t a)).det with hX
  have hperm : ∀ (σ : Equiv.Perm (Fin k)) (t : Fin k → I),
      (Matrix.of fun i a => ψ i (t (σ a))).det =
        ((Equiv.Perm.sign σ : ℤ) : R) * (Matrix.of fun i a => ψ i (t a)).det := by
    intro σ t
    have := Matrix.det_permute' σ (Matrix.of fun i a => ψ i (t a))
    simpa [Matrix.submatrix] using this
  have hgram : (Matrix.of fun i j => ∑ x, w x * φ i x * ψ j x).det = X := by
    rw [← Matrix.det_transpose, Matrix.det_apply', hX]
    have h1 : ∀ σ : Equiv.Perm (Fin k),
        ∏ a, (Matrix.of fun i j => ∑ x, w x * φ i x * ψ j x)ᵀ (σ a) a =
          ∑ t : Fin k → I, ∏ a, (w (t a) * φ a (t a) * ψ (σ a) (t a)) := by
      intro σ
      simp only [Matrix.transpose_apply, Matrix.of_apply]
      rw [Finset.prod_univ_sum]
      simp [Fintype.piFinset_univ]
    simp only [h1, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Matrix.det_apply', Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    simp only [Matrix.of_apply, Finset.prod_mul_distrib]
    ring
  have hσ : ∀ σ : Equiv.Perm (Fin k),
      ((Equiv.Perm.sign σ : ℤ) : R) * ∑ t : Fin k → I, (∏ a, w (t a)) *
        ((∏ a, φ (σ a) (t a)) * (Matrix.of fun i a => ψ i (t a)).det) = X := by
    intro σ
    let e : (Fin k → I) ≃ (Fin k → I) :=
      ⟨fun t => t ∘ σ, fun t => t ∘ σ.symm, fun t => by ext; simp, fun t => by ext; simp⟩
    rw [hX, ← Equiv.sum_comp e, Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    have e1 : (∏ a, w ((e t) a)) = ∏ a, w (t a) := Equiv.prod_comp σ (fun a => w (t a))
    have e2 : (∏ a, φ (σ a) ((e t) a)) = ∏ a, φ a (t a) :=
      Equiv.prod_comp σ (fun a => φ a (t a))
    have e3 : (Matrix.of fun i a => ψ i ((e t) a)).det =
        ((Equiv.Perm.sign σ : ℤ) : R) * (Matrix.of fun i a => ψ i (t a)).det := hperm σ t
    have e4 : (∏ a, w (t a) * φ a (t a)) = (∏ a, w (t a)) * ∏ a, φ a (t a) :=
      Finset.prod_mul_distrib
    have e5 : ((Equiv.Perm.sign σ : ℤ) : R) * ((Equiv.Perm.sign σ : ℤ) : R) = 1 := by
      rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]
      simp
    rw [e1, e2, e3, e4]
    linear_combination ((∏ a, w (t a)) * (∏ a, φ a (t a)) *
      (Matrix.of fun i a => ψ i (t a)).det) * e5
  rw [hgram]
  have hL : ∑ t : Fin k → I, (∏ a, w (t a)) *
      ((Matrix.of fun i a => φ i (t a)).det * (Matrix.of fun i a => ψ i (t a)).det) =
      ∑ σ : Equiv.Perm (Fin k), ((Equiv.Perm.sign σ : ℤ) : R) *
        ∑ t : Fin k → I, (∏ a, w (t a)) *
          ((∏ a, φ (σ a) (t a)) * (Matrix.of fun i a => ψ i (t a)).det) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Matrix.det_apply' (Matrix.of fun i a => φ i (t a)), Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    simp only [Matrix.of_apply]
    ring
  rw [hL, Finset.sum_congr rfl fun σ _ => hσ σ, Finset.sum_const, Finset.card_univ,
    Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]

theorem norm_eq_re_of_pos {z : ℂ} (h : 0 ≤ z) : ‖z‖ = z.re := by
  obtain ⟨h1, h2⟩ := Complex.le_def.mp h
  have e : z = (z.re : ℂ) := Complex.ext (by simp) (by simpa using h2.symm)
  rw [e, Complex.norm_real, Complex.ofReal_re, Real.norm_eq_abs, abs_of_nonneg (by simpa using h1)]

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- **Fischer's inequality**, Hermitian blocks. -/
theorem det_fischer {A : Matrix ι ι ℂ} {B : Matrix ι κ ℂ} {D : Matrix κ κ ℂ}
    (hY : (Matrix.fromBlocks A B Bᴴ D).PosSemidef) :
    (Matrix.fromBlocks A B Bᴴ D).det.re ≤ A.det.re * D.det.re := by
  have hA : A.PosSemidef := by
    have := hY.submatrix (Sum.inl : ι → ι ⊕ κ)
    have e : (Matrix.fromBlocks A B Bᴴ D).submatrix (Sum.inl : ι → ι ⊕ κ) Sum.inl = A := by
      ext i j; simp
    rwa [e] at this
  have hD : D.PosSemidef := by
    have := hY.submatrix (Sum.inr : κ → ι ⊕ κ)
    have e : (Matrix.fromBlocks A B Bᴴ D).submatrix (Sum.inr : κ → ι ⊕ κ) Sum.inr = D := by
      ext i j; simp
    rwa [e] at this
  have hreg : ∀ t : ℝ, 0 < t →
      (Matrix.fromBlocks (A + (t : ℂ) • (1 : Matrix ι ι ℂ)) B Bᴴ
        (D + (t : ℂ) • (1 : Matrix κ κ ℂ))).det.re ≤
        (A + (t : ℂ) • (1 : Matrix ι ι ℂ)).det.re * (D + (t : ℂ) • (1 : Matrix κ κ ℂ)).det.re := by
    intro t ht
    have hpt : (0 : ℂ) < (t : ℂ) := Complex.zero_lt_real.mpr ht
    have hAt : (A + (t : ℂ) • (1 : Matrix ι ι ℂ)).PosDef := by
      have hh : ((t : ℂ) • (1 : Matrix ι ι ℂ)).PosDef := Matrix.PosDef.one.smul hpt
      rw [add_comm]; exact hh.add_posSemidef hA
    have hDt : (D + (t : ℂ) • (1 : Matrix κ κ ℂ)).PosDef := by
      have hh : ((t : ℂ) • (1 : Matrix κ κ ℂ)).PosDef := Matrix.PosDef.one.smul hpt
      rw [add_comm]; exact hh.add_posSemidef hD
    set At := A + (t : ℂ) • (1 : Matrix ι ι ℂ) with hAtd
    set Dt := D + (t : ℂ) • (1 : Matrix κ κ ℂ) with hDtd
    have hYt : (Matrix.fromBlocks At B Bᴴ Dt).PosSemidef := by
      have e : Matrix.fromBlocks At B Bᴴ Dt = Matrix.fromBlocks A B Bᴴ D +
          (t : ℂ) • (1 : Matrix (ι ⊕ κ) (ι ⊕ κ) ℂ) := by
        rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_smul, Matrix.fromBlocks_add]
        simp [hAtd, hDtd]
      rw [e]
      exact hY.add (PosSemidef.one.smul hpt.le)
    haveI : Invertible At := (Matrix.isUnit_iff_isUnit_det _).mp hAt.isUnit |>.invertible.1 |> fun _ =>
      Matrix.invertibleOfIsUnitDet At ((Matrix.isUnit_iff_isUnit_det _).mp hAt.isUnit)
    have hS : (Dt - Bᴴ * At⁻¹ * B).PosSemidef :=
      (PosDef.fromBlocks₁₁ B Dt hAt).mp hYt
    have hP : (Bᴴ * At⁻¹ * B).PosSemidef := hAt.inv.posSemidef.conjTranspose_mul_mul_same B
    have hdet : (Matrix.fromBlocks At B Bᴴ Dt).det = At.det * (Dt - Bᴴ * At⁻¹ * B).det := by
      rw [Matrix.det_fromBlocks₁₁, Matrix.invOf_eq_nonsing_inv]
    have hb := norm_det_le_of_loewner_gram (r := 1) hDt hS.1
      (by
        have e : ((1 : ℝ) : ℂ) • Dt - (Dt - Bᴴ * At⁻¹ * B) = Bᴴ * At⁻¹ * B := by simp
        rwa [e])
      (by
        have e : ((1 : ℝ) : ℂ) • Dt + (Dt - Bᴴ * At⁻¹ * B) =
            Dt + (Dt - Bᴴ * At⁻¹ * B) := by simp
        rw [e]
        exact hDt.posSemidef.add hS)
    rw [one_pow, one_mul] at hb
    have hApos : 0 < At.det := hAt.det_pos
    rw [hdet]
    calc (At.det * (Dt - Bᴴ * At⁻¹ * B).det).re
        ≤ ‖At.det * (Dt - Bᴴ * At⁻¹ * B).det‖ := Complex.re_le_norm _
      _ = At.det.re * ‖(Dt - Bᴴ * At⁻¹ * B).det‖ := by
        rw [norm_mul, norm_eq_re_of_pos hApos.le]
      _ ≤ At.det.re * Dt.det.re := by
        have : 0 ≤ At.det.re := (norm_eq_re_of_pos hApos.le) ▸ norm_nonneg _
        gcongr
  have cY : Continuous fun t : ℝ => (Matrix.fromBlocks (A + (t : ℂ) • (1 : Matrix ι ι ℂ)) B Bᴴ
        (D + (t : ℂ) • (1 : Matrix κ κ ℂ))).det.re := by
    have : Continuous fun t : ℝ => Matrix.fromBlocks (A + (t : ℂ) • (1 : Matrix ι ι ℂ)) B Bᴴ
        (D + (t : ℂ) • (1 : Matrix κ κ ℂ)) := by
      refine Continuous.matrix_fromBlocks ?_ continuous_const continuous_const ?_ <;> fun_prop
    exact Complex.continuous_re.comp this.matrix_det
  have cA : Continuous fun t : ℝ => (A + (t : ℂ) • (1 : Matrix ι ι ℂ)).det.re := by
    have : Continuous fun t : ℝ => A + (t : ℂ) • (1 : Matrix ι ι ℂ) := by fun_prop
    exact Complex.continuous_re.comp this.matrix_det
  have cD : Continuous fun t : ℝ => (D + (t : ℂ) • (1 : Matrix κ κ ℂ)).det.re := by
    have : Continuous fun t : ℝ => D + (t : ℂ) • (1 : Matrix κ κ ℂ) := by fun_prop
    exact Complex.continuous_re.comp this.matrix_det
  have h0 := (cY.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
  have h1 := ((cA.mul cD).tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
  have hle := le_of_tendsto_of_tendsto h0 h1
    (Filter.eventually_of_mem self_mem_nhdsWithin fun t ht => hreg t ht)
  simpa using hle

/-- A real rank-one update: `X - z zᵀ ⪰ 0` makes the update at most multiply by `1 + β`. -/
theorem det_rank_one_le {X : Matrix ι ι ℝ} {z : ι → ℝ} {β : ℝ} (hβ : 0 ≤ β)
    (hX : X.PosSemidef)
    (hz : (X - Matrix.replicateCol Unit z * Matrix.replicateRow Unit z).PosSemidef) :
    (X + β • (Matrix.replicateCol Unit z * Matrix.replicateRow Unit z)).det ≤ (1 + β) * X.det := by
  set Z := Matrix.replicateCol Unit z * Matrix.replicateRow Unit z with hZ
  have hreg : ∀ t : ℝ, 0 < t →
      (X + t • (1 : Matrix ι ι ℝ) + β • Z).det ≤ (1 + β) * (X + t • (1 : Matrix ι ι ℝ)).det := by
    intro t ht
    have hPD : (X + t • (1 : Matrix ι ι ℝ)).PosDef := by
      have hh : (t • (1 : Matrix ι ι ℝ)).PosDef := Matrix.PosDef.one.smul ht
      rw [add_comm]; exact hh.add_posSemidef hX
    set Xt := X + t • (1 : Matrix ι ι ℝ) with hXt
    have hU : IsUnit Xt.det := hPD.det_pos.ne'.isUnit
    have hdp : 0 < Xt.det := hPD.det_pos
    have e1 := Matrix.det_add_replicateCol_mul_replicateRow hU (β • z) z (ι := Unit)
    have e2 := Matrix.det_add_replicateCol_mul_replicateRow hU (-z) z (ι := Unit)
    have hc1 : Matrix.replicateCol Unit (β • z) * Matrix.replicateRow Unit z = β • Z := by
      ext i j
      simp [hZ, Matrix.mul_apply, mul_assoc]
    have hc2 : Matrix.replicateCol Unit (-z) * Matrix.replicateRow Unit z = -Z := by
      ext i j
      simp [hZ, Matrix.mul_apply]
    set q : ℝ := (Matrix.replicateRow Unit z * Xt⁻¹ * Matrix.replicateCol Unit z) () () with hq
    have d1 : (1 + Matrix.replicateRow Unit z * Xt⁻¹ * Matrix.replicateCol Unit (β • z)).det =
        1 + β * q := by
      rw [Matrix.det_unique]
      simp [hq, Matrix.mul_apply, Finset.mul_sum, mul_left_comm]
    have d2 : (1 + Matrix.replicateRow Unit z * Xt⁻¹ * Matrix.replicateCol Unit (-z)).det =
        1 - q := by
      rw [Matrix.det_unique]
      simp [hq, Matrix.mul_apply, Finset.sum_neg_distrib, sub_eq_add_neg]
    rw [hc1, d1] at e1
    rw [hc2, d2] at e2
    have hmin : (Xt - Z).PosSemidef := by
      have e : Xt - Z = (X - Z) + t • (1 : Matrix ι ι ℝ) := by rw [hXt]; abel
      rw [e]
      exact hz.add (PosSemidef.one.smul ht.le)
    have hnn : 0 ≤ (Xt - Z).det := hmin.det_nonneg
    have e3 : (Xt - Z).det = Xt.det * (1 - q) := by
      rw [sub_eq_add_neg]
      exact e2
    have hq1 : q ≤ 1 := by
      rw [e3] at hnn
      by_contra hc
      have : 1 - q < 0 := by linarith [not_le.mp hc]
      exact absurd hnn (not_le.mpr (mul_neg_of_pos_of_neg hdp this))
    rw [e1]
    have : Xt.det * (β * q) ≤ Xt.det * β := by
      apply mul_le_mul_of_nonneg_left _ hdp.le
      nlinarith
    nlinarith
  have cL : Continuous fun t : ℝ => (X + t • (1 : Matrix ι ι ℝ) + β • Z).det := by
    have : Continuous fun t : ℝ => X + t • (1 : Matrix ι ι ℝ) + β • Z := by fun_prop
    exact this.matrix_det
  have cR : Continuous fun t : ℝ => (1 + β) * (X + t • (1 : Matrix ι ι ℝ)).det := by
    have : Continuous fun t : ℝ => X + t • (1 : Matrix ι ι ℝ) := by fun_prop
    exact continuous_const.mul this.matrix_det
  have h0 := (cL.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
  have h1 := (cR.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
  have hle := le_of_tendsto_of_tendsto h0 h1
    (Filter.eventually_of_mem self_mem_nhdsWithin fun t ht => hreg t ht)
  simpa using hle

/-- The weighted Gram `Bᵀ diag(a) B`. -/
def wGram (B : Matrix κ ι ℝ) (a : κ → ℝ) : Matrix ι ι ℝ :=
  Matrix.of fun i j => ∑ c, a c * B c i * B c j

theorem wGram_posSemidef (B : Matrix κ ι ℝ) {a : κ → ℝ} (ha : ∀ c, 0 ≤ a c) :
    (wGram B a).PosSemidef := by
  have e : wGram B a = Bᵀ * Matrix.diagonal a * B := by
    ext i j
    simp only [wGram, Matrix.of_apply]
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Matrix.mul_diagonal, Matrix.transpose_apply]
    ring
  rw [e]
  have hd : (Matrix.diagonal a).PosSemidef := Matrix.posSemidef_diagonal_iff.mpr ha
  simpa using hd.conjTranspose_mul_mul_same B

/-- **Diagonal scaling.** Raising the weights by factors `θ ≥ 1` raises the Gram determinant by
at most the product of those factors, whatever the rank of `B`. -/
theorem wGram_det_scale (B : Matrix κ ι ℝ) {a θ : κ → ℝ} (ha : ∀ c, 0 ≤ a c)
    (hθ : ∀ c, 1 ≤ θ c) :
    (wGram B fun c => a c * θ c).det ≤ (∏ c, θ c) * (wGram B a).det := by
  classical
  have key : ∀ S : Finset κ,
      (wGram B fun c => a c * (if c ∈ S then θ c else 1)).det ≤
        (∏ c ∈ S, θ c) * (wGram B a).det := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp
    | insert c S hc ih =>
      set a0 : κ → ℝ := fun d => a d * (if d ∈ S then θ d else 1) with ha0
      have ha0n : ∀ d, 0 ≤ a0 d := fun d => by
        refine mul_nonneg (ha d) ?_
        split_ifs
        · linarith [hθ d]
        · norm_num
      have hac : a0 c = a c := by simp [ha0, hc]
      set z : ι → ℝ := fun i => √(a c) * B c i with hz
      have hZ : ∀ i j, (Matrix.replicateCol Unit z * Matrix.replicateRow Unit z) i j =
          a c * B c i * B c j := by
        intro i j
        have := Real.mul_self_sqrt (ha c)
        simp only [Matrix.mul_apply, Matrix.replicateCol_apply, Matrix.replicateRow_apply,
          Finset.univ_unique, Finset.sum_singleton, hz]
        linear_combination (B c i * B c j) * this
      have hsplit : (wGram B a0) -
          Matrix.replicateCol Unit z * Matrix.replicateRow Unit z =
          wGram B (fun d => if d = c then 0 else a0 d) := by
        ext i j
        rw [Matrix.sub_apply, hZ]
        simp only [wGram, Matrix.of_apply]
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ c),
          ← Finset.add_sum_erase (a := c) Finset.univ
            (fun d => (if d = c then 0 else a0 d) * B d i * B d j) (Finset.mem_univ c), hac]
        simp only [if_true, zero_mul, zero_add]
        have : ∀ d ∈ Finset.univ.erase c,
            (if d = c then 0 else a0 d) * B d i * B d j = a0 d * B d i * B d j := by
          intro d hd
          rw [if_neg (Finset.ne_of_mem_erase hd)]
        rw [Finset.sum_congr rfl this]
        ring
      have hPS : (wGram B a0 -
          Matrix.replicateCol Unit z * Matrix.replicateRow Unit z).PosSemidef := by
        rw [hsplit]
        apply wGram_posSemidef
        intro d
        split_ifs
        · exact le_rfl
        · exact ha0n d
      have hb := det_rank_one_le (β := θ c - 1) (by linarith [hθ c])
        (wGram_posSemidef B ha0n) hPS
      have heq : (wGram B fun d => a d * (if d ∈ insert c S then θ d else 1)) =
          wGram B a0 + (θ c - 1) • (Matrix.replicateCol Unit z * Matrix.replicateRow Unit z) := by
        ext i j
        rw [Matrix.add_apply, Matrix.smul_apply, hZ, smul_eq_mul]
        simp only [wGram, Matrix.of_apply]
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ c),
          ← Finset.add_sum_erase (a := c) Finset.univ
            (fun d => a0 d * B d i * B d j) (Finset.mem_univ c), hac]
        have : ∀ d ∈ Finset.univ.erase c,
            a d * (if d ∈ insert c S then θ d else 1) * B d i * B d j = a0 d * B d i * B d j := by
          intro d hd
          have hne := Finset.ne_of_mem_erase hd
          simp [ha0, hne]
        rw [Finset.sum_congr rfl this]
        simp only [Finset.mem_insert, true_or, if_true]
        ring
      rw [heq, Finset.prod_insert hc]
      have h1 : 0 ≤ θ c := by linarith [hθ c]
      calc _ ≤ (1 + (θ c - 1)) * (wGram B a0).det := hb
        _ = θ c * (wGram B a0).det := by ring
        _ ≤ θ c * ((∏ d ∈ S, θ d) * (wGram B a).det) := by gcongr
        _ = _ := by ring
  have h := key Finset.univ
  simpa using h

end
end CatalanMeasure.GenD.Signed.RouteI.CompletedGas





namespace CatalanMeasure.GenD.Signed.RouteI.CompletedGas

open Matrix Finset CatalanMeasure.Signed Polynomial
open scoped BigOperators ComplexOrder

noncomputable section

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem posSemidef_ofReal {X : Matrix ι ι ℝ} (h : X.PosSemidef) :
    (X.map fun r : ℝ => (r : ℂ)).PosSemidef := by
  have hs : ∀ a b, X a b = X b a := fun a b => by
    have := congrFun (congrFun h.1 b) a
    simpa [Matrix.conjTranspose_apply] using this
  refine posSemidef_map_ofReal X hs fun u => ?_
  have := (Matrix.posSemidef_iff_dotProduct_mulVec.mp h).2 u
  simp only [dotProduct, mulVec, star_trivial, Pi.star_apply, Finset.mul_sum] at this
  convert this using 2 with a
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

/-- Fischer's inequality, real blocks. -/
theorem det_fischer_real {A : Matrix ι ι ℝ} {B : Matrix ι κ ℝ} {D : Matrix κ κ ℝ}
    (hY : (Matrix.fromBlocks A B Bᵀ D).PosSemidef) :
    (Matrix.fromBlocks A B Bᵀ D).det ≤ A.det * D.det := by
  have h := posSemidef_ofReal hY
  have e : (Matrix.fromBlocks A B Bᵀ D).map (fun r : ℝ => (r : ℂ)) =
      Matrix.fromBlocks (A.map fun r : ℝ => (r : ℂ)) (B.map fun r : ℝ => (r : ℂ))
        (B.map fun r : ℝ => (r : ℂ))ᴴ (D.map fun r : ℝ => (r : ℂ)) := by
    rw [Matrix.fromBlocks_map]
    congr 1
    ext i j
    simp [Matrix.conjTranspose_apply]
  have hf := det_fischer (e ▸ h)
  rw [← e, det_map_ofReal, det_map_ofReal, det_map_ofReal] at hf
  simpa using hf

/-- Loewner monotonicity of the determinant, real and possibly singular. -/
theorem det_le_of_loewner {X Z : Matrix ι ι ℝ} (hX : X.PosSemidef) (hd : (Z - X).PosSemidef) :
    X.det ≤ Z.det := by
  have hZ : Z.PosSemidef := by
    have := hX.add hd
    simpa using this
  have hreg : ∀ t : ℝ, 0 < t → X.det ≤ (Z + t • (1 : Matrix ι ι ℝ)).det := by
    intro t ht
    have hPD : (Z + t • (1 : Matrix ι ι ℝ)).PosDef := by
      have hh : (t • (1 : Matrix ι ι ℝ)).PosDef := Matrix.PosDef.one.smul ht
      rw [add_comm]; exact hh.add_posSemidef hZ
    have hPSD : (Z + t • (1 : Matrix ι ι ℝ)).PosSemidef := hPD.posSemidef
    have hPDc : ((Z + t • (1 : Matrix ι ι ℝ)).map fun r : ℝ => (r : ℂ)).PosDef := by
      have hc : ((Z + t • (1 : Matrix ι ι ℝ)).map fun r : ℝ => (r : ℂ)) =
          (Z.map fun r : ℝ => (r : ℂ)) + (t : ℂ) • (1 : Matrix ι ι ℂ) := by
        ext i j
        by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
      rw [hc, add_comm]
      exact (Matrix.PosDef.one.smul (Complex.zero_lt_real.mpr ht)).add_posSemidef
        (posSemidef_ofReal hZ)
    have q1 : (((1 : ℝ) : ℂ) • ((Z + t • (1 : Matrix ι ι ℝ)).map fun r : ℝ => (r : ℂ)) -
        (X.map fun r : ℝ => (r : ℂ))).PosSemidef := by
      have h := posSemidef_ofReal (hd.add (PosSemidef.one.smul ht.le) :
        (Z - X + t • (1 : Matrix ι ι ℝ)).PosSemidef)
      convert h using 1
      ext i j
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij] <;> ring
    have q2 : (((1 : ℝ) : ℂ) • ((Z + t • (1 : Matrix ι ι ℝ)).map fun r : ℝ => (r : ℂ)) +
        (X.map fun r : ℝ => (r : ℂ))).PosSemidef := by
      have h := posSemidef_ofReal (hPSD.add hX)
      convert h using 1
      ext i j
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
    have hb := norm_det_le_of_loewner_gram hPDc (posSemidef_ofReal hX).1 q1 q2
    rw [one_pow, one_mul, det_map_ofReal, det_map_ofReal, Complex.norm_real,
      Complex.ofReal_re] at hb
    exact (le_abs_self _).trans hb
  have c : Continuous fun t : ℝ => (Z + t • (1 : Matrix ι ι ℝ)).det := by
    have : Continuous fun t : ℝ => Z + t • (1 : Matrix ι ι ℝ) := by fun_prop
    exact this.matrix_det
  have h0 := (c.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
  have hle := ge_of_tendsto h0
    (Filter.eventually_of_mem self_mem_nhdsWithin fun t ht => hreg t ht)
  simpa using hle


/-- **Two-family Gram inequality.** It replaces the projection and complementary-minor steps: the
second family annihilates the evaluation matrix, and Fischer applied to the joint Gram gives the
product of the two Gram determinants. -/
theorem two_family_gram {k s : ℕ} (C : Matrix (Fin k) (Fin k ⊕ Fin s) ℝ)
    (Nn : Matrix (Fin s) (Fin k ⊕ Fin s) ℝ) (Tm : Matrix (Fin k ⊕ Fin s) (Fin k) ℝ)
    (E : Matrix (Fin k ⊕ Fin s) (Fin s) ℝ) (hNT : Nn * Tm = 0) {G : Fin k ⊕ Fin s → ℝ}
    (hG : ∀ a, 0 ≤ G a) :
    ((C * Tm).det * (Nn * E).det) ^ 2 * ∏ a, G a ≤
      (Matrix.fromCols Tm E).det ^ 2 * ((wGram Cᵀ G).det * (wGram Nnᵀ G).det) := by
  set S := Matrix.fromRows C Nn with hS
  set Q := Matrix.fromCols Tm E with hQ
  have hSQ : S * Q = Matrix.fromBlocks (C * Tm) (C * E) (Nn * Tm) (Nn * E) := by
    rw [hS, hQ, Matrix.fromRows_mul_fromCols]
  have hdet : S.det * Q.det = (C * Tm).det * (Nn * E).det := by
    rw [← Matrix.det_mul, hSQ, hNT, Matrix.det_fromBlocks_zero₂₁]
  set X : Matrix (Fin k) (Fin s) ℝ := Matrix.of fun i j => ∑ c, G c * C i c * Nn j c with hX
  have hY : S * Matrix.diagonal G * Sᵀ = Matrix.fromBlocks (wGram Cᵀ G) X Xᵀ (wGram Nnᵀ G) := by
    ext i j
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Matrix.transpose_apply]
    rcases i with i | i <;> rcases j with j | j <;>
      simp only [hS, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr,
        Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
        Matrix.fromBlocks_apply₂₂, wGram, hX, Matrix.of_apply, Matrix.transpose_apply] <;>
      refine Finset.sum_congr rfl fun c _ => by ring
  have hPSD : (S * Matrix.diagonal G * Sᵀ).PosSemidef := by
    have hd : (Matrix.diagonal G).PosSemidef := Matrix.posSemidef_diagonal_iff.mpr hG
    simpa using hd.mul_mul_conjTranspose_same S
  have hF := det_fischer_real (hY ▸ hPSD)
  rw [← hY, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal] at hF
  rw [← hdet]
  have hq : 0 ≤ Q.det ^ 2 := sq_nonneg _
  calc (S.det * Q.det) ^ 2 * ∏ a, G a = Q.det ^ 2 * (S.det * (∏ a, G a) * S.det) := by ring
    _ ≤ _ := by gcongr

/-! ### The Laurent factorization -/

variable {kp k : ℕ}

/-- Degree of a column in the split index. -/
def colDeg : Fin kp ⊕ Fin k → ℕ
  | Sum.inl j => j
  | Sum.inr i => kp + i

/-- Monic polynomial with the positive sheet locations as roots. -/
def omegaPoly (ξ : Fin kp → ℝ) : ℝ[X] := ∏ p, (X - C (ξ p))

theorem omegaPoly_monic (ξ : Fin kp → ℝ) : (omegaPoly ξ).Monic :=
  monic_prod_of_monic _ _ fun p _ => monic_X_sub_C _

theorem omegaPoly_natDegree (ξ : Fin kp → ℝ) : (omegaPoly ξ).natDegree = kp := by
  unfold omegaPoly
  rw [natDegree_prod_of_monic _ _ fun p _ => monic_X_sub_C _]
  simp

/-- `X^i ω`. -/
def gasPoly (ξ : Fin kp → ℝ) (i : ℕ) : ℝ[X] := X ^ i * omegaPoly ξ

theorem gasPoly_monic (ξ : Fin kp → ℝ) (i : ℕ) : (gasPoly ξ i).Monic :=
  (monic_X_pow i).mul (omegaPoly_monic ξ)

theorem gasPoly_natDegree (ξ : Fin kp → ℝ) (i : ℕ) : (gasPoly ξ i).natDegree = i + kp := by
  unfold gasPoly
  rw [(monic_X_pow i).natDegree_mul (omegaPoly_monic ξ), natDegree_X_pow, omegaPoly_natDegree]

/-- The sum over the split index is a sum over `range (kp+k)`. -/
theorem sum_colDeg {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    ∑ a : Fin kp ⊕ Fin k, f (colDeg a) = ∑ d ∈ Finset.range (kp + k), f d := by
  simp only [Fintype.sum_sum_type, colDeg]
  rw [Finset.sum_range_add, Fin.sum_univ_eq_sum_range (fun j => f j) kp,
    Fin.sum_univ_eq_sum_range (fun i => f (kp + i)) k]

theorem eval_gasPoly_sum (ξ : Fin kp → ℝ) (i : Fin k) (y : ℝ) :
    ∑ a : Fin kp ⊕ Fin k, (gasPoly ξ i).coeff (colDeg a) * y ^ colDeg a =
      (gasPoly ξ i).eval y := by
  rw [sum_colDeg (fun d => (gasPoly ξ i).coeff d * y ^ d)]
  have hd : (gasPoly ξ i).natDegree < kp + k := by
    rw [gasPoly_natDegree]
    have := i.isLt
    omega
  rw [Polynomial.eval_eq_sum_range' hd]

/-- The column operation: unit columns then the coefficients of `X^i ω`. -/
def laurentW (ξ : Fin kp → ℝ) : Matrix (Fin kp ⊕ Fin k) (Fin kp ⊕ Fin k) ℝ :=
  Matrix.fromBlocks 1 (Matrix.of fun j i => (gasPoly ξ i).coeff j)
    0 (Matrix.of fun i' i => (gasPoly ξ i).coeff (kp + i'))

theorem laurentW_det (ξ : Fin kp → ℝ) : (laurentW (k := k) ξ).det = 1 := by
  unfold laurentW
  rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul,
    Matrix.det_of_upperTriangular]
  · refine Finset.prod_eq_one fun i _ => ?_
    have := (gasPoly_monic ξ i).coeff_natDegree
    rw [gasPoly_natDegree] at this
    simpa [Matrix.of_apply, add_comm] using this
  · intro i' i hlt
    apply coeff_eq_zero_of_natDegree_lt
    rw [gasPoly_natDegree]
    have : (i : ℕ) < i' := hlt
    omega

/-- The rows of the comparison matrix in split form. -/
def laurentM (sh : ℤ) (ξ : Fin kp → ℝ) (x : Fin k → ℝ) :
    Matrix (Fin kp ⊕ Fin k) (Fin kp ⊕ Fin k) ℝ :=
  Matrix.of fun r a => match r with
    | Sum.inl p => ξ p ^ ((colDeg a : ℤ) + sh)
    | Sum.inr b => (1 / 2 : ℝ) * x b ^ ((colDeg a : ℤ) + sh) +
        (1 / 2 : ℝ) * x b ^ (-((colDeg a : ℤ) + sh))

/-- The folded evaluation of the `i`-th gas function at `x`. -/
def foldEval (sh : ℤ) (ξ : Fin kp → ℝ) (i : ℕ) (y : ℝ) : ℝ :=
  (1 / 2 : ℝ) * (y ^ sh * (gasPoly ξ i).eval y + y⁻¹ ^ sh * (gasPoly ξ i).eval y⁻¹)

/-- **Laurent factorization.** The comparison determinant is the positive Vandermonde times the
folded determinant of the gas functions, with no integral and no projection. -/
theorem laurent_split (sh : ℤ) (ξ : Fin kp → ℝ) (x : Fin k → ℝ) (hξ : ∀ p, ξ p ≠ 0)
    (hx : ∀ b, x b ≠ 0) :
    (laurentM sh ξ x).det = (∏ p, ξ p ^ sh) * (Matrix.vandermonde ξ).det *
      (Matrix.of fun b i : Fin k => foldEval sh ξ i (x b)).det := by
  have hmul : laurentM sh ξ x * laurentW ξ =
      Matrix.fromBlocks (Matrix.of fun p j : Fin kp => ξ p ^ ((j : ℤ) + sh)) 0
        (Matrix.of fun (b : Fin k) (j : Fin kp) => (1 / 2 : ℝ) * x b ^ ((j : ℤ) + sh) +
          (1 / 2 : ℝ) * x b ^ (-((j : ℤ) + sh)))
        (Matrix.of fun b i : Fin k => foldEval sh ξ i (x b)) := by
    have hWu : ∀ (a : Fin kp ⊕ Fin k) (j : Fin kp),
        laurentW (k := k) ξ a (Sum.inl j) = if a = Sum.inl j then 1 else 0 := by
      intro a j
      rcases a with a | a <;> simp [laurentW, Matrix.one_apply]
    have hWc : ∀ (a : Fin kp ⊕ Fin k) (i : Fin k),
        laurentW (k := k) ξ a (Sum.inr i) = (gasPoly ξ i).coeff (colDeg a) := by
      intro a i
      rcases a with a | a <;> simp [laurentW, colDeg]
    ext r c
    rw [Matrix.mul_apply]
    rcases c with j | i
    · simp only [hWu, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rcases r with p | b <;> simp [laurentM, colDeg]
    · simp only [hWc]
      rcases r with p | b
      · have e : ∀ a : Fin kp ⊕ Fin k, laurentM sh ξ x (Sum.inl p) a *
            (gasPoly ξ i).coeff (colDeg a) =
            ξ p ^ sh * ((gasPoly ξ i).coeff (colDeg a) * ξ p ^ colDeg a) := by
          intro a
          simp only [laurentM, Matrix.of_apply]
          rw [zpow_add₀ (hξ p), _root_.zpow_natCast]
          ring
        simp only [e]
        rw [← Finset.mul_sum, eval_gasPoly_sum]
        have h0 : (gasPoly ξ i).eval (ξ p) = 0 := by
          simp only [gasPoly, omegaPoly, eval_mul, eval_prod, eval_sub, eval_X, eval_C]
          rw [Finset.prod_eq_zero (Finset.mem_univ p) (by simp), mul_zero]
        rw [h0, mul_zero]
        simp
      · have e : ∀ a : Fin kp ⊕ Fin k, laurentM sh ξ x (Sum.inr b) a *
            (gasPoly ξ i).coeff (colDeg a) =
            (1 / 2 : ℝ) * (x b ^ sh * ((gasPoly ξ i).coeff (colDeg a) * x b ^ colDeg a) +
              (x b)⁻¹ ^ sh * ((gasPoly ξ i).coeff (colDeg a) * (x b)⁻¹ ^ colDeg a)) := by
          intro a
          simp only [laurentM, Matrix.of_apply]
          rw [zpow_add₀ (hx b), _root_.zpow_natCast, _root_.zpow_neg, zpow_add₀ (hx b), _root_.zpow_natCast,
            mul_inv, _root_.inv_zpow, inv_pow]
          ring
        simp only [e]
        rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
          eval_gasPoly_sum, eval_gasPoly_sum]
        simp [foldEval]
  have hV : (Matrix.of fun p j : Fin kp => ξ p ^ ((j : ℤ) + sh)).det =
      (∏ p, ξ p ^ sh) * (Matrix.vandermonde ξ).det := by
    have e : (Matrix.of fun p j : Fin kp => ξ p ^ ((j : ℤ) + sh)) =
        Matrix.diagonal (fun p => ξ p ^ sh) * Matrix.vandermonde ξ := by
      ext p j
      rw [Matrix.diagonal_mul, Matrix.vandermonde_apply, Matrix.of_apply,
        zpow_add₀ (hξ p), _root_.zpow_natCast]
      ring
    rw [e, Matrix.det_mul, Matrix.det_diagonal]
  have h := congrArg Matrix.det hmul
  rw [Matrix.det_mul, laurentW_det, mul_one, Matrix.det_fromBlocks_zero₁₂, hV] at h
  exact h

end
end CatalanMeasure.GenD.Signed.RouteI.CompletedGas




namespace CatalanMeasure.GenD.Signed.RouteI.CompletedGas

open Matrix Finset Polynomial
open scoped BigOperators

noncomputable section

local notation "Tp" => (fun K a => Polynomial.Chebyshev.T K ((a : ℕ) : ℤ))

/-- The Joukowski evaluation of a Chebyshev polynomial, over any field. -/
theorem cheb_joukowski {K : Type*} [Field K] [CharZero K] {z : K} (hz : z ≠ 0) (n : ℕ) :
    (Polynomial.Chebyshev.T K (n : ℤ)).eval ((z + z⁻¹) / 2) = (z ^ n + z⁻¹ ^ n) / 2 := by
  have hzy : z * z⁻¹ = 1 := mul_inv_cancel₀ hz
  generalize z⁻¹ = y at hzy ⊢
  induction n using Nat.twoStepInduction with
  | zero =>
    simp only [Nat.cast_zero, Polynomial.Chebyshev.T_zero, eval_one, pow_zero]
    norm_num
  | one =>
    simp
  | more n h0 h1 =>
    have e : ((n + 2 : ℕ) : ℤ) = (n : ℤ) + 2 := by push_cast; ring
    have e1 : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by push_cast; ring
    rw [e, Polynomial.Chebyshev.T_add_two]
    rw [e1] at h1
    simp only [eval_sub, eval_mul, eval_ofNat, eval_X, h0, h1]
    linear_combination ((z ^ n + y ^ n) / 2) * hzy

/-- The leading coefficient of `T_a`. -/
def chebLead (a : ℕ) : ℝ := (Polynomial.Chebyshev.T ℝ (a : ℤ)).leadingCoeff

theorem chebLead_pos (a : ℕ) : 0 < chebLead a := by
  unfold chebLead
  rw [Polynomial.Chebyshev.leadingCoeff_T]
  positivity

theorem chebT_natDegree (a : ℕ) : (Polynomial.Chebyshev.T ℝ (a : ℤ)).natDegree = a := by
  rw [Polynomial.Chebyshev.natDegree_T]
  simp

/-- **Chebyshev expansion** with control of the top coefficient. -/
theorem cheb_expand (d : ℕ) (p : ℝ[X]) (hp : p.natDegree < d) :
    ∃ c : ℕ → ℝ, p = ∑ a ∈ Finset.range d, C (c a) * Polynomial.Chebyshev.T ℝ (a : ℤ) ∧
      (∀ a, p.natDegree < a → c a = 0) ∧ c p.natDegree = p.leadingCoeff / chebLead p.natDegree := by
  induction d generalizing p with
  | zero => exact absurd hp (Nat.not_lt_zero _)
  | succ d ih =>
    by_cases hm : p.natDegree < d
    · obtain ⟨c, h1, h2, h3⟩ := ih p hm
      refine ⟨c, ?_, h2, h3⟩
      rw [Finset.sum_range_succ, h2 d hm]
      simpa using h1
    · have hmd : p.natDegree = d := by omega
      have hl := chebLead_pos d
      set b := p.leadingCoeff / chebLead d with hb
      set q := p - C b * Polynomial.Chebyshev.T ℝ (d : ℤ) with hq
      by_cases hd0 : d = 0
      · subst hd0
        have hc : p = C (p.coeff 0) := eq_C_of_natDegree_eq_zero hmd
        refine ⟨fun a => if a = 0 then p.coeff 0 else 0, ?_, ?_, ?_⟩
        · simpa using hc
        · intro a ha
          have h0 : a ≠ 0 := by omega
          simp [h0]
        · rw [hmd]
          have h1 : chebLead 0 = 1 := by simp [chebLead]
          have h2 : p.leadingCoeff = p.coeff 0 := by rw [Polynomial.leadingCoeff, hmd]
          rw [h1, div_one, h2]
          simp
      · have hqd : q.natDegree < d := by
          have hT : (C b * Polynomial.Chebyshev.T ℝ (d : ℤ)).natDegree = d := by
            rw [natDegree_C_mul, chebT_natDegree]
            intro h0
            have hb0 : p.leadingCoeff = 0 := by
              rw [hb, div_eq_zero_iff] at h0
              rcases h0 with h0 | h0
              · exact h0
              · exact absurd h0 hl.ne'
            have : p = 0 := leadingCoeff_eq_zero.mp hb0
            rw [this] at hmd
            simp at hmd
            exact hd0 hmd.symm
          have hlc : (C b * Polynomial.Chebyshev.T ℝ (d : ℤ)).leadingCoeff = p.leadingCoeff := by
            rw [leadingCoeff_mul, leadingCoeff_C]
            change b * chebLead d = _
            rw [hb]
            field_simp
          have hdeg : (C b * Polynomial.Chebyshev.T ℝ (d : ℤ)).degree = p.degree := by
            rw [degree_eq_natDegree (by
              intro h0
              rw [h0] at hT
              simp at hT
              exact hd0 hT.symm), degree_eq_natDegree (by
              intro h0
              rw [h0] at hmd
              simp at hmd
              exact hd0 hmd.symm), hT, hmd]
          have h1 := degree_sub_lt hdeg.symm (by
            intro h0
            rw [h0] at hmd
            simp at hmd
            exact hd0 hmd.symm) hlc.symm
          by_cases hq0 : q = 0
          · rw [hq0]
            simp
            omega
          · have h2 := (natDegree_lt_natDegree_iff hq0).mpr h1
            omega
        obtain ⟨c, h1, h2, -⟩ := ih q hqd
        refine ⟨fun a => if a = d then b else c a, ?_, ?_, ?_⟩
        · rw [Finset.sum_range_succ]
          have e : ∑ a ∈ Finset.range d, C (if a = d then b else c a) *
              Polynomial.Chebyshev.T ℝ (a : ℤ) =
              ∑ a ∈ Finset.range d, C (c a) * Polynomial.Chebyshev.T ℝ (a : ℤ) := by
            refine Finset.sum_congr rfl fun a ha => ?_
            rw [if_neg (Finset.mem_range.mp ha).ne]
          rw [e, ← h1]
          simp only [↓reduceIte, hq]
          ring
        · intro a ha
          rw [hmd] at ha
          have h0 : a ≠ d := by omega
          simp only [h0, if_false]
          exact h2 a (by omega)
        · rw [hmd]
          simp [hb]

/-- `T_a` evaluated at points has determinant the leading coefficients times Vandermonde. -/
theorem cheb_det_vandermonde {k : ℕ} (u : Fin k → ℝ) :
    (Matrix.of fun (b a : Fin k) => (Polynomial.Chebyshev.T ℝ ((a : ℕ) : ℤ)).eval (u b)).det =
      (∏ a : Fin k, chebLead a) * (Matrix.vandermonde u).det := by
  let p : Fin k → ℝ[X] := fun a => C (chebLead a)⁻¹ * Polynomial.Chebyshev.T ℝ ((a : ℕ) : ℤ)
  have hl : ∀ a : Fin k, (chebLead a)⁻¹ ≠ 0 := fun a => (inv_pos.mpr (chebLead_pos a)).ne'
  have hd : ∀ a : Fin k, (p a).natDegree = a := fun a => by
    simp only [p]
    rw [natDegree_C_mul (hl a), chebT_natDegree]
  have hm : ∀ a : Fin k, Monic (p a) := fun a => by
    simp only [p, Monic, leadingCoeff_mul, leadingCoeff_C]
    exact inv_mul_cancel₀ (chebLead_pos a).ne'
  rw [Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde u p hd hm]
  have e : (Matrix.of fun (b a : Fin k) =>
      (Polynomial.Chebyshev.T ℝ ((a : ℕ) : ℤ)).eval (u b)) =
      (Matrix.of fun (b a : Fin k) => (p a).eval (u b)) *
        Matrix.diagonal fun a : Fin k => chebLead a := by
    ext b a
    rw [Matrix.mul_diagonal]
    simp only [Matrix.of_apply, p, eval_mul, eval_C]
    field_simp [(chebLead_pos a).ne']
  rw [e, Matrix.det_mul, Matrix.det_diagonal]
  ring

end
end CatalanMeasure.GenD.Signed.RouteI.CompletedGas




namespace CatalanMeasure.GenD.Signed.RouteI.CompletedGas

open Matrix Finset CatalanMeasure.Signed
open scoped BigOperators ComplexOrder ComplexConjugate

noncomputable section

variable {ι α δ X : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]
  [Fintype δ] [DecidableEq δ] [Fintype X] [DecidableEq X]

theorem wGram_quad (B : Matrix δ ι ℝ) (a : δ → ℝ) (v : ι → ℝ) :
    star v ⬝ᵥ (wGram B a *ᵥ v) = ∑ c, a c * (∑ i, v i * B c i) ^ 2 := by
  simp only [dotProduct, mulVec, wGram, Matrix.of_apply, star_trivial, Pi.star_apply]
  have h : ∀ c, a c * (∑ i, v i * B c i) ^ 2 =
      ∑ i, ∑ j, v i * (a c * B c i * B c j * v j) := by
    intro c
    rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => by ring
  simp only [h]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_mul, Finset.mul_sum]

theorem sq_sum_le_inv_mul (s : Finset δ) (q W : δ → ℝ) (hW : ∀ d, 0 < W d) :
    (∑ d ∈ s, q d) ^ 2 ≤ (∑ d ∈ s, (W d)⁻¹) * ∑ d ∈ s, W d * q d ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq s (fun d => √(W d)⁻¹) (fun d => √(W d) * q d)
  have e1 : ∀ d, √(W d)⁻¹ * (√(W d) * q d) = q d := by
    intro d
    rw [← mul_assoc, ← Real.sqrt_mul (inv_nonneg.mpr (hW d).le),
      inv_mul_cancel₀ (hW d).ne', Real.sqrt_one, one_mul]
  have e2 : ∀ d, √(W d)⁻¹ ^ 2 = (W d)⁻¹ := fun d =>
    Real.sq_sqrt (inv_nonneg.mpr (hW d).le)
  have e3 : ∀ d, (√(W d) * q d) ^ 2 = W d * q d ^ 2 := fun d => by
    rw [mul_pow, Real.sq_sqrt (hW d).le]
  simpa only [e1, e2, e3] using h

/-- **Fold domination.** A fold of coefficient coordinates is dominated by a diagonal form as soon
as the fibre weights satisfy one scalar inequality. No eigenvalue analysis is needed. -/
theorem fold_loewner (f : δ → α) (P : Matrix δ ι ℝ) (G : α → ℝ) (W : δ → ℝ)
    (hW : ∀ d, 0 < W d) (hG : ∀ a, 0 ≤ G a)
    (h : ∀ a, G a * ∑ d ∈ Finset.univ.filter (fun d => f d = a), (W d)⁻¹ ≤ 1) :
    (wGram P W -
      wGram (Matrix.of fun a i => ∑ d ∈ Finset.univ.filter (fun d => f d = a), P d i) G
        ).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨(wGram_posSemidef P fun d => (hW d).le).1.sub (wGram_posSemidef _ hG).1, fun v => ?_⟩
  rw [Matrix.sub_mulVec, dotProduct_sub, wGram_quad, wGram_quad, sub_nonneg]
  set q : δ → ℝ := fun d => ∑ i, v i * P d i with hq
  have e1 : ∀ a, ∑ i, v i * (Matrix.of fun a i =>
      ∑ d ∈ Finset.univ.filter (fun d => f d = a), P d i) a i =
      ∑ d ∈ Finset.univ.filter (fun d => f d = a), q d := by
    intro a
    simp only [Matrix.of_apply, hq, Finset.mul_sum]
    rw [Finset.sum_comm]
  simp only [e1]
  rw [← Finset.sum_fiberwise Finset.univ f (fun d => W d * q d ^ 2)]
  refine Finset.sum_le_sum fun a _ => ?_
  set s := Finset.univ.filter (fun d => f d = a) with hs
  have hT : 0 ≤ ∑ d ∈ s, W d * q d ^ 2 :=
    Finset.sum_nonneg fun d _ => mul_nonneg (hW d).le (sq_nonneg _)
  calc G a * (∑ d ∈ s, q d) ^ 2
      ≤ G a * ((∑ d ∈ s, (W d)⁻¹) * ∑ d ∈ s, W d * q d ^ 2) := by
        gcongr
        · exact hG a
        · exact sq_sum_le_inv_mul s q W hW
    _ = (G a * ∑ d ∈ s, (W d)⁻¹) * ∑ d ∈ s, W d * q d ^ 2 := by ring
    _ ≤ 1 * ∑ d ∈ s, W d * q d ^ 2 := by gcongr; exact h a
    _ = _ := one_mul _

/-- The Gram matrix of a real combination of an orthogonal family. -/
theorem gram_expansion (w : X → ℝ) (e : δ → X → ℂ) (A : δ → ℝ)
    (hO : ∀ d d', ∑ x, (w x : ℂ) * e d x * conj (e d' x) = if d = d' then (A d : ℂ) else 0)
    (B : Matrix δ ι ℝ) :
    (Matrix.of fun i j => ∑ x, (w x : ℂ) * (∑ d, (B d i : ℂ) * e d x) *
        conj (∑ d, (B d j : ℂ) * e d x)) = (wGram B A).map fun r : ℝ => (r : ℂ) := by
  ext i j
  simp only [Matrix.of_apply, Matrix.map_apply, wGram, map_sum, map_mul, Complex.conj_ofReal]
  have h1 : ∀ x, (w x : ℂ) * (∑ d, (B d i : ℂ) * e d x) * (∑ d, (B d j : ℂ) * conj (e d x)) =
      ∑ d, ∑ d', ((B d i : ℂ) * (B d' j : ℂ)) * ((w x : ℂ) * e d x * conj (e d' x)) := by
    intro x
    rw [mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun d' _ => by ring
  simp only [h1]
  rw [Finset.sum_comm]
  push_cast
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, hO, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  ring

/-- Real form of the finite Andreief identity for the Gram of complex functions. -/
theorem gram_andreief {k : ℕ} (w : X → ℝ) (φ : Fin k → X → ℂ) (M : Matrix (Fin k) (Fin k) ℝ)
    (hM : (Matrix.of fun i j => ∑ x, (w x : ℂ) * φ i x * conj (φ j x)) =
      M.map fun r : ℝ => (r : ℂ)) :
    (k.factorial : ℝ) * M.det =
      ∑ t : Fin k → X, (∏ a, w (t a)) * ‖(Matrix.of fun i a => φ i (t a)).det‖ ^ 2 := by
  have h := andreief_finite (fun x => (w x : ℂ)) φ (fun i x => conj (φ i x))
  rw [hM, det_map_ofReal] at h
  have e : ∀ t : Fin k → X, (∏ a, (w (t a) : ℂ)) *
      ((Matrix.of fun i a => φ i (t a)).det * (Matrix.of fun i a => conj (φ i (t a))).det) =
      (((∏ a, w (t a)) * ‖(Matrix.of fun i a => φ i (t a)).det‖ ^ 2 : ℝ) : ℂ) := by
    intro t
    have hc : (Matrix.of fun i a => conj (φ i (t a))).det =
        conj (Matrix.of fun i a => φ i (t a)).det := by
      rw [RingHom.map_det]
      rfl
    rw [hc, Complex.mul_conj']
    push_cast
    rfl
  rw [Finset.sum_congr rfl fun t _ => e t, ← Complex.ofReal_sum] at h
  have h' : (∑ t : Fin k → X, (∏ a, w (t a)) * ‖(Matrix.of fun i a => φ i (t a)).det‖ ^ 2 : ℝ) =
      (k.factorial : ℝ) * M.det := by
    exact_mod_cast h
  exact h'.symm

end
end CatalanMeasure.GenD.Signed.RouteI.CompletedGas




namespace CatalanMeasure.GenD.Signed.RouteI.CompletedGas

open Matrix Finset Polynomial CatalanMeasure.Signed
open scoped BigOperators ComplexOrder ComplexConjugate

noncomputable section

variable {kp k s : ℕ}

/-! ### Fold coordinates -/

theorem colDeg_eq (a : Fin k ⊕ Fin s) : colDeg a = (finSumFinEquiv a : Fin (k + s)) := by
  rcases a with a | a <;> simp [colDeg]

theorem colDeg_lt (a : Fin k ⊕ Fin s) : colDeg a < k + s := by
  rw [colDeg_eq]
  exact Fin.isLt _

theorem colDeg_injective : Function.Injective (colDeg : Fin k ⊕ Fin s → ℕ) := by
  intro a b h
  rw [colDeg_eq, colDeg_eq] at h
  exact finSumFinEquiv.injective (Fin.ext h)

/-- The folded index of a Laurent degree. -/
def foldTo (D : ℕ) (hD : k + s = D + 1) (hn : kp + k ≤ 2 * D + 1) (d : Fin (kp + k)) :
    Fin k ⊕ Fin s :=
  finSumFinEquiv.symm ⟨((d : ℤ) - D).natAbs, by have := d.isLt; omega⟩

theorem colDeg_foldTo (D : ℕ) (hD : k + s = D + 1) (hn : kp + k ≤ 2 * D + 1)
    (d : Fin (kp + k)) : colDeg (foldTo D hD hn d) = ((d : ℤ) - D).natAbs := by
  rw [colDeg_eq]
  simp [foldTo]

/-- Coefficient matrix of the gas functions. -/
def gasCoeff (ξ : Fin kp → ℝ) : Matrix (Fin (kp + k)) (Fin k) ℝ :=
  Matrix.of fun d i => (gasPoly ξ i).coeff d

/-- The folded coefficient matrix. -/
def foldCoeff (D : ℕ) (hD : k + s = D + 1) (hn : kp + k ≤ 2 * D + 1) (ξ : Fin kp → ℝ) :
    Matrix (Fin k ⊕ Fin s) (Fin k) ℝ :=
  Matrix.of fun a i => ∑ d ∈ Finset.univ.filter (fun d => foldTo D hD hn d = a),
    gasCoeff ξ d i

/-- Chebyshev evaluation matrix. -/
def chebM (u : Fin k → ℝ) : Matrix (Fin k ⊕ Fin s) (Fin k) ℝ :=
  Matrix.of fun a b => (Polynomial.Chebyshev.T ℝ (colDeg a : ℤ)).eval (u b)

theorem cheb_natAbs {K : Type*} [Field K] [CharZero K] {z : K} (hz : z ≠ 0) (c : ℤ) :
    (Polynomial.Chebyshev.T K (c.natAbs : ℤ)).eval ((z + z⁻¹) / 2) = (z ^ c + z ^ (-c)) / 2 := by
  rw [cheb_joukowski hz]
  obtain ⟨m, rfl | rfl⟩ := c.eq_nat_or_neg
  · simp [_root_.zpow_neg]
  · simp [_root_.zpow_neg, add_comm]

theorem gas_eval_fin (ξ : Fin kp → ℝ) (i : Fin k) (y : ℝ) :
    (gasPoly ξ i).eval y = ∑ d : Fin (kp + k), gasCoeff ξ d i * y ^ (d : ℕ) := by
  have hd : (gasPoly ξ i).natDegree < kp + k := by
    rw [gasPoly_natDegree]
    have := i.isLt
    omega
  rw [Polynomial.eval_eq_sum_range' hd, Finset.sum_range]
  rfl

theorem foldEval_sum (D : ℕ) (ξ : Fin kp → ℝ) (i : Fin k) {y : ℝ} (hy : y ≠ 0) :
    foldEval (-(D : ℤ)) ξ i y =
      ∑ d : Fin (kp + k), gasCoeff ξ d i * ((y ^ ((d : ℤ) - D) + y ^ (-((d : ℤ) - D))) / 2) := by
  have h1 : ∀ (t : ℝ), t ≠ 0 → ∀ d : Fin (kp + k),
      t ^ ((d : ℤ) - D) = t ^ (-(D : ℤ)) * t ^ (d : ℕ) := by
    intro t ht d
    rw [sub_eq_neg_add, zpow_add₀ ht, _root_.zpow_natCast]
  have h2 : ∀ d : Fin (kp + k), y ^ (-((d : ℤ) - D)) =
      y⁻¹ ^ (-(D : ℤ)) * y⁻¹ ^ (d : ℕ) := by
    intro d
    rw [← h1 _ (inv_ne_zero hy), _root_.inv_zpow']
  unfold foldEval
  rw [show (gasPoly ξ ↑i).eval y = _ from gas_eval_fin ξ i y,
    show (gasPoly ξ ↑i).eval y⁻¹ = _ from gas_eval_fin ξ i y⁻¹, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [h1 y hy d, h2 d]
  ring

theorem foldCoeff_mul_chebM (D : ℕ) (hD : k + s = D + 1) (hn : kp + k ≤ 2 * D + 1)
    (ξ : Fin kp → ℝ) (x : Fin k → ℝ) (hx : ∀ b, x b ≠ 0) :
    (foldCoeff D hD hn ξ)ᵀ * chebM (s := s) (fun b => (x b + (x b)⁻¹) / 2) =
      (Matrix.of fun b i : Fin k => foldEval (-(D : ℤ)) ξ i (x b))ᵀ := by
  ext i b
  rw [Matrix.mul_apply]
  simp only [Matrix.transpose_apply, Matrix.of_apply, foldCoeff, chebM, Finset.sum_mul]
  rw [foldEval_sum D ξ i (hx b)]
  rw [← Finset.sum_fiberwise Finset.univ (foldTo D hD hn)
    (fun d => gasCoeff ξ d i * ((x b ^ ((d : ℤ) - D) + x b ^ (-((d : ℤ) - D))) / 2))]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun d hd => ?_
  have ha : foldTo D hD hn d = a := (Finset.mem_filter.mp hd).2
  rw [← ha, colDeg_foldTo, cheb_natAbs (hx b)]

/-! ### The second family -/

/-- The unit columns at the high degrees. -/
def unitE : Matrix (Fin k ⊕ Fin s) (Fin s) ℝ :=
  Matrix.of fun a j => if a = Sum.inr j then 1 else 0

theorem chebM_fromCols_det (u : Fin k → ℝ) :
    (Matrix.fromCols (chebM (s := s) u) unitE).det =
      (∏ a : Fin k, chebLead a) * (Matrix.vandermonde u).det := by
  have e : Matrix.fromCols (chebM (s := s) u) unitE =
      Matrix.fromBlocks
        (Matrix.of fun (a b : Fin k) => (Polynomial.Chebyshev.T ℝ ((a : ℕ) : ℤ)).eval (u b)) 0
        (Matrix.of fun (j : Fin s) (b : Fin k) =>
          (Polynomial.Chebyshev.T ℝ ((k + j : ℕ) : ℤ)).eval (u b)) 1 := by
    ext r c
    rcases r with r | r <;> rcases c with c | c <;>
      simp [chebM, unitE, colDeg, Matrix.one_apply]
  rw [e, Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, mul_one, ← cheb_det_vandermonde,
    ← Matrix.det_transpose]
  rfl

/-- Chebyshev coordinates of `X^i π_u`. -/
theorem second_family (u : Fin k → ℝ) :
    ∃ Nn : Matrix (Fin s) (Fin k ⊕ Fin s) ℝ,
      (∀ i : Fin s, gasPoly u i = ∑ a : Fin k ⊕ Fin s, C (Nn i a) *
          Polynomial.Chebyshev.T ℝ (colDeg a : ℤ)) ∧
      Nn * chebM (s := s) u = 0 ∧ (Nn * unitE).det = ∏ i : Fin s, (chebLead (k + i))⁻¹ := by
  have hc : ∀ i : Fin s, ∃ c : ℕ → ℝ,
      gasPoly u i = ∑ a ∈ Finset.range (k + s), C (c a) * Polynomial.Chebyshev.T ℝ (a : ℤ) ∧
      (∀ a, (gasPoly u i).natDegree < a → c a = 0) ∧
      c (gasPoly u i).natDegree =
        (gasPoly u i).leadingCoeff / chebLead (gasPoly u i).natDegree := by
    intro i
    refine cheb_expand (k + s) (gasPoly u i) ?_
    rw [gasPoly_natDegree]
    have := i.isLt
    omega
  choose c h1 h2 h3 using hc
  refine ⟨Matrix.of fun i a => c i (colDeg a), ?_, ?_, ?_⟩
  · intro i
    conv_lhs => rw [h1 i]
    exact (sum_colDeg (fun d => C (c i d) * Polynomial.Chebyshev.T ℝ (d : ℤ))).symm
  · ext i b
    rw [Matrix.mul_apply]
    simp only [Matrix.of_apply, chebM, Matrix.zero_apply]
    rw [sum_colDeg (fun d => c i d * (Polynomial.Chebyshev.T ℝ (d : ℤ)).eval (u b))]
    have h0 : (gasPoly u i).eval (u b) = 0 := by
      simp only [gasPoly, omegaPoly, eval_mul, eval_prod, eval_sub, eval_X, eval_C]
      rw [Finset.prod_eq_zero (Finset.mem_univ b) (by simp), mul_zero]
    rw [h1 i] at h0
    simpa [eval_finset_sum] using h0
  · have e : ∀ i j : Fin s, (((Matrix.of fun (i : Fin s) (a : Fin k ⊕ Fin s) => c i (colDeg a)) :
        Matrix (Fin s) (Fin k ⊕ Fin s) ℝ) * (unitE : Matrix (Fin k ⊕ Fin s) (Fin s) ℝ)) i j =
        c i (k + j) := by
      intro i j
      rw [Matrix.mul_apply]
      simp [unitE, colDeg]
    rw [Matrix.det_of_lowerTriangular]
    · refine Finset.prod_congr rfl fun i _ => ?_
      rw [e]
      have h := h3 i
      rw [(gasPoly_monic u i).leadingCoeff, gasPoly_natDegree, add_comm (i : ℕ) k] at h
      rw [h, one_div]
    · intro i j hlt
      rw [e]
      have hij : (i : ℕ) < j := hlt
      apply h2
      rw [gasPoly_natDegree]
      omega

/-! ### Two Gram evaluations -/

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- Diagonal of the Joukowski Gram. -/
def foldG (A : ℤ → ℝ) (a : ℕ) : ℝ := if a = 0 then A 0 else (A a + A (-(a : ℤ))) / 4

theorem foldG_pos {A : ℤ → ℝ} (hA : ∀ c, 0 < A c) (a : ℕ) : 0 < foldG A a := by
  unfold foldG
  split_ifs
  · exact hA 0
  · have := hA a
    have := hA (-(a : ℤ))
    positivity

/-- The Laurent orthogonality given by the quadrature. -/
def LaurentOrtho (D : ℕ) (w : X → ℝ) (γ : X → ℂ) (A : ℤ → ℝ) : Prop :=
  ∀ c c' : ℤ, |c| ≤ D → |c'| ≤ D →
    ∑ x, (w x : ℂ) * γ x ^ c * conj (γ x ^ c') = if c = c' then (A c : ℂ) else 0

theorem joukowski_ortho {D : ℕ} {w : X → ℝ} {γ : X → ℂ} {A : ℤ → ℝ}
    (hO : LaurentOrtho D w γ A) {a b : ℕ} (ha : a ≤ D) (hb : b ≤ D) :
    ∑ x, (w x : ℂ) * ((γ x ^ (a : ℤ) + γ x ^ (-(a : ℤ))) / 2) *
        conj ((γ x ^ (b : ℤ) + γ x ^ (-(b : ℤ))) / 2) =
      if a = b then (foldG A a : ℂ) else 0 := by
  have hexp : ∀ x, (w x : ℂ) * ((γ x ^ (a : ℤ) + γ x ^ (-(a : ℤ))) / 2) *
      conj ((γ x ^ (b : ℤ) + γ x ^ (-(b : ℤ))) / 2) =
      (1 / 4 : ℂ) * ((w x : ℂ) * γ x ^ (a : ℤ) * conj (γ x ^ (b : ℤ)) +
        (w x : ℂ) * γ x ^ (a : ℤ) * conj (γ x ^ (-(b : ℤ))) +
        (w x : ℂ) * γ x ^ (-(a : ℤ)) * conj (γ x ^ (b : ℤ)) +
        (w x : ℂ) * γ x ^ (-(a : ℤ)) * conj (γ x ^ (-(b : ℤ)))) := by
    intro x
    rw [map_div₀, map_add]
    simp only [map_ofNat]
    ring
  have a1 : |(a : ℤ)| ≤ D := by rw [Nat.abs_cast]; exact_mod_cast ha
  have a2 : |(-(a : ℤ))| ≤ D := by rw [abs_neg]; exact a1
  have b1 : |(b : ℤ)| ≤ D := by rw [Nat.abs_cast]; exact_mod_cast hb
  have b2 : |(-(b : ℤ))| ≤ D := by rw [abs_neg]; exact b1
  simp only [hexp]
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
    hO _ _ a1 b1, hO _ _ a1 b2, hO _ _ a2 b1, hO _ _ a2 b2]
  by_cases hab : a = b
  · subst hab
    by_cases h0 : a = 0
    · subst h0
      simp [foldG]
      ring
    · have hne : (a : ℤ) ≠ -(a : ℤ) := by omega
      have hne' : -(a : ℤ) ≠ (a : ℤ) := by omega
      simp only [if_true, if_neg hne, if_neg hne', foldG, if_neg h0]
      push_cast
      ring
  · have n1 : (a : ℤ) ≠ b := by omega
    have n4 : -(a : ℤ) ≠ -(b : ℤ) := by omega
    by_cases h0 : (a : ℤ) = -(b : ℤ)
    · exfalso
      omega
    · have n3 : -(a : ℤ) ≠ (b : ℤ) := by omega
      rw [if_neg n1, if_neg n4, if_neg h0, if_neg n3, if_neg hab]
      simp

/-- `z^i c` columns form a scaled Vandermonde. -/
theorem det_scaled_vandermonde (z c : Fin k → ℂ) :
    (Matrix.of fun (i a : Fin k) => z a ^ (i : ℕ) * c a).det =
      (∏ a, c a) * (Matrix.vandermonde z).det := by
  have e : (Matrix.of fun (i a : Fin k) => z a ^ (i : ℕ) * c a) =
      (Matrix.vandermonde z)ᵀ * Matrix.diagonal c := by
    ext i a
    rw [Matrix.mul_diagonal]
    simp [Matrix.vandermonde_apply]
  rw [e, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal]
  ring

/-- The positive Laurent functions on the quadrature. -/
theorem pos_function (D : ℕ) (ξ : Fin kp → ℝ) (i : Fin k) {z : ℂ} (hz : z ≠ 0) :
    ∑ d : Fin (kp + k), ((gasCoeff ξ d i : ℝ) : ℂ) * z ^ ((d : ℤ) - D) =
      z ^ (i : ℕ) * (z ^ (-(D : ℤ)) * aeval z (omegaPoly ξ)) := by
  have hd : (gasPoly ξ i).natDegree < kp + k := by
    rw [gasPoly_natDegree]
    have := i.isLt
    omega
  have h := Polynomial.aeval_eq_sum_range' (R := ℝ) hd z
  rw [Finset.sum_range] at h
  have e : aeval z (gasPoly ξ i) = z ^ (i : ℕ) * aeval z (omegaPoly ξ) := by
    simp [gasPoly]
  rw [mul_left_comm, ← e, h, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [sub_eq_neg_add, zpow_add₀ hz, _root_.zpow_natCast, Complex.real_smul]
  simp only [gasCoeff, Matrix.of_apply]
  ring

theorem aeval_cheb (a : ℕ) {z : ℂ} (hz : z ≠ 0) :
    aeval ((z + z⁻¹) / 2) (Polynomial.Chebyshev.T ℝ (a : ℤ)) =
      (z ^ (a : ℤ) + z ^ (-(a : ℤ))) / 2 := by
  rw [aeval_def, ← eval_map, Polynomial.Chebyshev.map_T]
  have := cheb_natAbs hz (a : ℤ)
  simpa using this

end
end CatalanMeasure.GenD.Signed.RouteI.CompletedGas




namespace CatalanMeasure.GenD.Signed.RouteI.CompletedGas

open Matrix Finset Polynomial CatalanMeasure.Signed
open scoped BigOperators ComplexOrder ComplexConjugate

noncomputable section

variable {kp k s : ℕ} {X : Type*} [Fintype X] [DecidableEq X]

/-- Joukowski map. -/
def joukowski (z : ℂ) : ℂ := (z + z⁻¹) / 2

/-- The positive tuple sum, before dividing by `k!`. -/
def posGas (k D : ℕ) (w : X → ℝ) (γ : X → ℂ) (ξ : Fin kp → ℝ) : ℝ :=
  ∑ t : Fin k → X, (∏ a, w (t a)) *
    (‖∏ a, (γ (t a) ^ (-(D : ℤ)) * aeval (γ (t a)) (omegaPoly ξ))‖ ^ 2 *
      ‖(Matrix.vandermonde fun a => γ (t a)).det‖ ^ 2)

/-- The negative tuple sum, before dividing by `s!`. -/
def negGas (s : ℕ) (w : X → ℝ) (γ : X → ℂ) (u : Fin k → ℝ) : ℝ :=
  ∑ t : Fin s → X, (∏ a, w (t a)) *
    (‖∏ a, aeval (joukowski (γ (t a))) (omegaPoly u)‖ ^ 2 *
      ‖(Matrix.vandermonde fun a => joukowski (γ (t a))).det‖ ^ 2)

theorem pos_gram (D : ℕ) (hkn : kp + k ≤ 2 * D + 1) {w : X → ℝ} {γ : X → ℂ} {A : ℤ → ℝ}
    (hγ : ∀ x, γ x ≠ 0) (hO : LaurentOrtho D w γ A) (ξ : Fin kp → ℝ) :
    (k.factorial : ℝ) *
        (wGram (gasCoeff (k := k) ξ) fun d : Fin (kp + k) => A ((d : ℤ) - D)).det =
      posGas k D w γ ξ := by
  have hOd : ∀ d d' : Fin (kp + k),
      ∑ x, (w x : ℂ) * γ x ^ ((d : ℤ) - D) * conj (γ x ^ ((d' : ℤ) - D)) =
        if d = d' then (A ((d : ℤ) - D) : ℂ) else 0 := by
    intro d d'
    have hb : ∀ d : Fin (kp + k), |(d : ℤ) - D| ≤ D := by
      intro d
      have := d.isLt
      rw [abs_le]
      constructor <;> omega
    rw [hO _ _ (hb d) (hb d')]
    by_cases h : d = d'
    · simp [h]
    · have : (d : ℤ) - D ≠ (d' : ℤ) - D := by
        intro h'
        apply h
        apply Fin.ext
        omega
      simp [h, this]
  have hg := gram_expansion w (fun (d : Fin (kp + k)) x => γ x ^ ((d : ℤ) - D))
    (fun d => A ((d : ℤ) - D)) hOd (gasCoeff (k := k) ξ)
  rw [gram_andreief w (fun i x => ∑ d, ((gasCoeff (k := k) ξ d i : ℝ) : ℂ) *
    γ x ^ ((d : ℤ) - D)) _ hg]
  unfold posGas
  refine Finset.sum_congr rfl fun t _ => ?_
  congr 1
  have e : (Matrix.of fun (i a : Fin k) => ∑ d, ((gasCoeff (k := k) ξ d i : ℝ) : ℂ) *
      γ (t a) ^ ((d : ℤ) - D)) =
      Matrix.of fun (i a : Fin k) => (γ (t a)) ^ (i : ℕ) *
        (γ (t a) ^ (-(D : ℤ)) * aeval (γ (t a)) (omegaPoly ξ)) := by
    ext i a
    simp only [Matrix.of_apply]
    exact pos_function D ξ i (hγ _)
  rw [e, det_scaled_vandermonde (fun a => γ (t a))
    (fun a => γ (t a) ^ (-(D : ℤ)) * aeval (γ (t a)) (omegaPoly ξ)), norm_mul, mul_pow]

theorem neg_gram (D : ℕ) (hD : k + s = D + 1) {w : X → ℝ} {γ : X → ℂ} {A : ℤ → ℝ}
    (hγ : ∀ x, γ x ≠ 0) (hO : LaurentOrtho D w γ A) (u : Fin k → ℝ)
    (Nn : Matrix (Fin s) (Fin k ⊕ Fin s) ℝ)
    (hN : ∀ i : Fin s, gasPoly u i = ∑ a : Fin k ⊕ Fin s, C (Nn i a) *
      Polynomial.Chebyshev.T ℝ (colDeg a : ℤ)) :
    (s.factorial : ℝ) * (wGram Nnᵀ fun a => foldG A (colDeg a)).det = negGas s w γ u := by
  have hOd : ∀ a b : Fin k ⊕ Fin s,
      ∑ x, (w x : ℂ) * ((γ x ^ ((colDeg a : ℕ) : ℤ) + γ x ^ (-((colDeg a : ℕ) : ℤ))) / 2) *
        conj ((γ x ^ ((colDeg b : ℕ) : ℤ) + γ x ^ (-((colDeg b : ℕ) : ℤ))) / 2) =
        if a = b then (foldG A (colDeg a) : ℂ) else 0 := by
    intro a b
    have ha := colDeg_lt a
    have hb := colDeg_lt b
    rw [joukowski_ortho hO (by omega) (by omega)]
    by_cases h : a = b
    · simp [h]
    · have : colDeg a ≠ colDeg b := fun h' => h (colDeg_injective h')
      simp [h, this]
  have hg := gram_expansion w
    (fun (a : Fin k ⊕ Fin s) x => (γ x ^ ((colDeg a : ℕ) : ℤ) + γ x ^ (-((colDeg a : ℕ) : ℤ))) / 2)
    (fun a => foldG A (colDeg a)) hOd Nnᵀ
  rw [gram_andreief w (fun i x => ∑ a, ((Nnᵀ a i : ℝ) : ℂ) *
    ((γ x ^ ((colDeg a : ℕ) : ℤ) + γ x ^ (-((colDeg a : ℕ) : ℤ))) / 2)) _ hg]
  unfold negGas
  refine Finset.sum_congr rfl fun t _ => ?_
  congr 1
  have e : (Matrix.of fun (i a : Fin s) => ∑ b, ((Nnᵀ b i : ℝ) : ℂ) *
      ((γ (t a) ^ ((colDeg b : ℕ) : ℤ) + γ (t a) ^ (-((colDeg b : ℕ) : ℤ))) / 2)) =
      Matrix.of fun (i a : Fin s) => (joukowski (γ (t a))) ^ (i : ℕ) *
        aeval (joukowski (γ (t a))) (omegaPoly u) := by
    ext i a
    simp only [Matrix.of_apply, Matrix.transpose_apply]
    have h1 : aeval (joukowski (γ (t a))) (gasPoly u i) =
        (joukowski (γ (t a))) ^ (i : ℕ) * aeval (joukowski (γ (t a))) (omegaPoly u) := by
      simp [gasPoly]
    rw [← h1, hN i, map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_mul, aeval_C, joukowski, aeval_cheb _ (hγ _)]
    rfl
  rw [e, det_scaled_vandermonde (fun a => joukowski (γ (t a)))
    (fun a => aeval (joukowski (γ (t a))) (omegaPoly u)), norm_mul, mul_pow]

/-- **Finite Gram bound.** No projection, no Jacobi, no rectangular Cauchy-Binet. -/
theorem finite_gram (D : ℕ) (hD : k + s = D + 1) (hn : kp + k ≤ 2 * D + 1)
    (ξ : Fin kp → ℝ) (x : Fin k → ℝ) (hξ : ∀ p, ξ p ≠ 0) (hx : ∀ b, x b ≠ 0)
    {w : X → ℝ} {γ : X → ℂ} {A : ℤ → ℝ} (hγ : ∀ x, γ x ≠ 0) (hA : ∀ c, 0 < A c)
    (hO : LaurentOrtho D w γ A) (θ : Fin (kp + k) → ℝ) (hθ : ∀ d, 1 ≤ θ d)
    (hfold : ∀ a : ℕ, a ≤ D → foldG A a *
      ∑ d ∈ Finset.univ.filter (fun d : Fin (kp + k) => ((d : ℤ) - D).natAbs = a),
        (A ((d : ℤ) - D) * θ d)⁻¹ ≤ 1) :
    (laurentM (-(D : ℤ)) ξ x).det ^ 2 * (∏ a : Fin k ⊕ Fin s, foldG A (colDeg a)) *
        ((k.factorial : ℝ) * (s.factorial : ℝ)) ≤
      ((∏ p, ξ p ^ (-(D : ℤ))) * (Matrix.vandermonde ξ).det) ^ 2 *
        ((∏ a : Fin k ⊕ Fin s, chebLead (colDeg a)) *
          (Matrix.vandermonde fun b => (x b + (x b)⁻¹) / 2).det) ^ 2 *
        (∏ d, θ d) * posGas k D w γ ξ * negGas s w γ (fun b => (x b + (x b)⁻¹) / 2) := by
  set u : Fin k → ℝ := fun b => (x b + (x b)⁻¹) / 2 with hu
  obtain ⟨Nn, hN1, hN2, hN3⟩ := second_family (s := s) u
  set G : Fin k ⊕ Fin s → ℝ := fun a => foldG A (colDeg a) with hGd
  have hGp : ∀ a, 0 < G a := fun a => foldG_pos hA _
  have hGn : ∀ a, 0 ≤ G a := fun a => (hGp a).le
  have h2 := two_family_gram (foldCoeff D hD hn ξ)ᵀ Nn (chebM u) unitE hN2 hGn
  rw [foldCoeff_mul_chebM D hD hn ξ x hx, Matrix.det_transpose, hN3, chebM_fromCols_det,
    Matrix.transpose_transpose] at h2
  set F := (Matrix.of fun b i : Fin k => foldEval (-(D : ℤ)) ξ i (x b)).det with hF
  set Aδ : Fin (kp + k) → ℝ := fun d => A ((d : ℤ) - D) with hAδ
  have hAδp : ∀ d, 0 < Aδ d := fun d => hA _
  have hW : ∀ d, 0 < Aδ d * θ d := fun d => mul_pos (hAδp d) (by linarith [hθ d])
  have hfib : ∀ a, G a * ∑ d ∈ Finset.univ.filter (fun d => foldTo D hD hn d = a),
      (Aδ d * θ d)⁻¹ ≤ 1 := by
    intro a
    have hset : Finset.univ.filter (fun d => foldTo D hD hn d = a) =
        Finset.univ.filter (fun d : Fin (kp + k) => ((d : ℤ) - D).natAbs = colDeg a) := by
      ext d
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [← colDeg_foldTo D hD hn d]
      exact ⟨fun h => by rw [h], fun h => colDeg_injective h⟩
    rw [hset]
    have := colDeg_lt a
    exact hfold (colDeg a) (by omega)
  have hL := fold_loewner (foldTo D hD hn) (gasCoeff (k := k) ξ) G (fun d => Aδ d * θ d) hW hGn hfib
  have hP : (wGram (foldCoeff D hD hn ξ) G).det ≤
      (∏ d, θ d) * (wGram (gasCoeff (k := k) ξ) Aδ).det :=
    (det_le_of_loewner (wGram_posSemidef _ hGn) hL).trans
      (wGram_det_scale _ (fun d => (hAδp d).le) hθ)
  have hPos := pos_gram (k := k) D hn hγ hO ξ
  have hNeg := neg_gram D hD hγ hO u Nn hN1
  have hNd : 0 ≤ (wGram Nnᵀ G).det := (wGram_posSemidef _ hGn).det_nonneg
  have hPw : 0 ≤ (wGram (gasCoeff (k := k) ξ) Aδ).det :=
    (wGram_posSemidef _ fun d => (hAδp d).le).det_nonneg
  have hsplit := laurent_split (-(D : ℤ)) ξ x hξ hx
  set S := (∏ p, ξ p ^ (-(D : ℤ))) * (Matrix.vandermonde ξ).det with hS
  rw [hsplit, ← hPos, ← hNeg]
  set L1 := ∏ a : Fin k, chebLead a with hL1
  set L2 := ∏ i : Fin s, chebLead (k + i) with hL2
  have hLL : (∏ a : Fin k ⊕ Fin s, chebLead (colDeg a)) = L1 * L2 := by
    rw [Fintype.prod_sum_type]
    rfl
  have hL2i : (∏ i : Fin s, (chebLead (k + i))⁻¹) * L2 = 1 := by
    rw [hL2, ← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun i _ => inv_mul_cancel₀ (chebLead_pos _).ne'
  rw [hLL]
  set V := (Matrix.vandermonde u).det with hV
  set Li := ∏ i : Fin s, (chebLead (k + i))⁻¹ with hLi
  set Pd := (wGram (foldCoeff D hD hn ξ) G).det with hPd
  set Nd := (wGram Nnᵀ G).det with hNdd
  set Pw := (wGram (gasCoeff (k := k) ξ) Aδ).det with hPwd
  set Θ := ∏ d, θ d with hΘ
  set PG := ∏ a, G a with hPG
  have h3 : F ^ 2 * PG ≤ (L1 * L2 * V) ^ 2 * (Pd * Nd) := by
    have h4 : (F * Li) ^ 2 * PG * L2 ^ 2 ≤ (L1 * V) ^ 2 * (Pd * Nd) * L2 ^ 2 :=
      mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
    have e1 : (F * Li) ^ 2 * PG * L2 ^ 2 = F ^ 2 * PG * (Li * L2) ^ 2 := by ring
    rw [e1, hL2i] at h4
    calc F ^ 2 * PG = F ^ 2 * PG * 1 ^ 2 := by ring
      _ ≤ _ := h4
      _ = _ := by ring
  have h5 : (L1 * L2 * V) ^ 2 * (Pd * Nd) ≤ (L1 * L2 * V) ^ 2 * ((Θ * Pw) * Nd) := by
    gcongr
  have hkf : (0 : ℝ) ≤ (k.factorial : ℝ) := by positivity
  have hsf : (0 : ℝ) ≤ (s.factorial : ℝ) := by positivity
  calc (S * F) ^ 2 * PG * ((k.factorial : ℝ) * (s.factorial : ℝ))
      = S ^ 2 * (F ^ 2 * PG) * ((k.factorial : ℝ) * (s.factorial : ℝ)) := by ring
    _ ≤ S ^ 2 * ((L1 * L2 * V) ^ 2 * ((Θ * Pw) * Nd)) *
          ((k.factorial : ℝ) * (s.factorial : ℝ)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (h3.trans h5) (sq_nonneg S))
          (by positivity)
    _ = _ := by ring

end
end CatalanMeasure.GenD.Signed.RouteI.CompletedGas





namespace CatalanMeasure.GenD.Signed.RouteI.CompletedGas

open Finset Polynomial CatalanMeasure.Signed
open scoped BigOperators ComplexOrder ComplexConjugate

noncomputable section

/-! ### Radial quadrature on roots of unity -/

/-- The root of unity of order `L`. -/
def rootZ (L : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / L)

theorem rootZ_primitive {L : ℕ} (hL : L ≠ 0) : IsPrimitiveRoot (rootZ L) L :=
  Complex.isPrimitiveRoot_exp L hL

theorem rootZ_norm {L : ℕ} (hL : L ≠ 0) : ‖rootZ L‖ = 1 :=
  (rootZ_primitive hL).norm'_eq_one hL

theorem rootZ_ne_zero {L : ℕ} (hL : L ≠ 0) : rootZ L ≠ 0 :=
  (rootZ_primitive hL).ne_zero hL

/-- Sum of an integer power over the roots of unity. -/
theorem root_sum_zpow {L : ℕ} (hL : L ≠ 0) {m : ℤ} (hm : m ≠ 0) (hmL : |m| < L) :
    ∑ l : Fin L, (rootZ L ^ m) ^ (l : ℕ) = 0 := by
  have hp := rootZ_primitive hL
  have h1 : rootZ L ^ m ≠ 1 := by
    intro h
    have := (hp.zpow_eq_one_iff_dvd m).mp h
    have h2 := Int.eq_zero_of_abs_lt_dvd this hmL
    exact hm h2
  have h2 : (rootZ L ^ m) ^ L = 1 := by
    rw [← _root_.zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, _root_.zpow_natCast,
      hp.pow_eq_one, one_zpow]
  have h3 := mul_neg_geom_sum (rootZ L ^ m) L
  rw [h2, sub_self] at h3
  have h4 : (1 - rootZ L ^ m) ≠ 0 := sub_ne_zero.mpr h1.symm
  have h5 : ∑ l ∈ Finset.range L, (rootZ L ^ m) ^ l = 0 :=
    (mul_eq_zero.mp h3).resolve_left h4
  rw [← h5, Finset.sum_range]

variable {J : ℕ}

/-- Quadrature nodes. -/
def quadNode (L : ℕ) (r : Fin J → ℝ) (p : Fin J × Fin L) : ℂ :=
  (r p.1 : ℂ) * rootZ L ^ (p.2 : ℕ)

/-- Quadrature weights. -/
def quadWeight (L : ℕ) (ρ : Fin J → ℝ) (p : Fin J × Fin L) : ℝ := ρ p.1 / L

/-- The radial moments `A(c)`. -/
def radialA2 (r ρ : Fin J → ℝ) (c : ℤ) : ℝ := ∑ j, ρ j * r j ^ (2 * c)

theorem quadNode_ne_zero {L : ℕ} (hL : L ≠ 0) {r : Fin J → ℝ} (hr : ∀ j, 0 < r j)
    (p : Fin J × Fin L) : quadNode L r p ≠ 0 :=
  mul_ne_zero (by exact_mod_cast (hr p.1).ne') (pow_ne_zero _ (rootZ_ne_zero hL))

theorem quad_ortho {L D : ℕ} (hL : 2 * D < L) (r ρ : Fin J → ℝ) (hr : ∀ j, 0 < r j) :
    LaurentOrtho D (quadWeight L ρ) (quadNode L r) (radialA2 r ρ) := by
  intro c c' hc hc'
  have hL0 : L ≠ 0 := by omega
  have hζ := rootZ_ne_zero hL0
  have hnorm := rootZ_norm hL0
  have hconj : conj (rootZ L) = (rootZ L)⁻¹ := by
    rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hnorm]
    simp
  have hterm : ∀ (j : Fin J) (l : Fin L),
      ((quadWeight L ρ (j, l) : ℝ) : ℂ) * quadNode L r (j, l) ^ c *
        conj (quadNode L r (j, l) ^ c') =
      ((ρ j / L * r j ^ (c + c') : ℝ) : ℂ) * (rootZ L ^ (c - c')) ^ (l : ℕ) := by
    intro j l
    have hrj : ((r j : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (hr j).ne'
    set η := rootZ L ^ (l : ℕ) with hηd
    have hη0 : η ≠ 0 := pow_ne_zero _ hζ
    have hη : conj η = η⁻¹ := by rw [hηd, map_pow, hconj, inv_pow]
    have hz : (rootZ L ^ (c - c')) ^ (l : ℕ) = η ^ (c - c') := by
      rw [hηd, ← _root_.zpow_natCast (rootZ L ^ (c - c')), zpow_comm, _root_.zpow_natCast]
    simp only [quadWeight, quadNode]
    rw [map_zpow₀, map_mul, Complex.conj_ofReal, ← hηd, hη, mul_zpow, mul_zpow,
      _root_.inv_zpow', hz]
    push_cast
    rw [zpow_add₀ hrj, zpow_sub₀ hη0, _root_.zpow_neg]
    ring
  rw [Fintype.sum_prod_type]
  simp only [hterm]
  by_cases hcc : c = c'
  · subst hcc
    rw [if_pos rfl]
    simp only [sub_self, zpow_zero, one_pow, mul_one, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    unfold radialA2
    push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    have : (L : ℂ) ≠ 0 := by exact_mod_cast hL0
    rw [two_mul]
    field_simp
  · rw [if_neg hcc]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [← Finset.mul_sum, root_sum_zpow hL0 (sub_ne_zero.mpr hcc), mul_zero]
    have h1 := abs_sub c c'
    have h2 : |c - c'| ≤ |c| + |c'| := h1
    have h3 : (2 * D : ℤ) < L := by exact_mod_cast hL
    linarith

/-- The fold weights. -/
def foldTheta (A : ℤ → ℝ) (g c : ℤ) : ℝ :=
  if 1 ≤ c ∧ c ≤ g then (A c + A (-c)) / (2 * A c) else 1

theorem foldTheta_ge_one {A : ℤ → ℝ} (hA : ∀ c, 0 < A c) (hm : ∀ c : ℤ, 0 ≤ c → A c ≤ A (-c))
    (g c : ℤ) : 1 ≤ foldTheta A g c := by
  unfold foldTheta
  split_ifs with h
  · have h1 := hA c
    have h2 := hm c (by omega)
    rw [le_div_iff₀ (by positivity)]
    linarith
  · exact le_rfl

/-- A fibre of the absolute degree has at most two points. -/
theorem fibre_sum_le {n D a : ℕ} (F : ℤ → ℝ) (hF : ∀ c, 0 ≤ F c) (T : Finset ℤ)
    (hT : ∀ d : Fin n, ((d : ℤ) - D).natAbs = a → (d : ℤ) - D ∈ T) :
    ∑ d ∈ Finset.univ.filter (fun d : Fin n => ((d : ℤ) - D).natAbs = a), F ((d : ℤ) - D) ≤
      ∑ c ∈ T, F c := by
  have hinj : Set.InjOn (fun d : Fin n => (d : ℤ) - D)
      (Finset.univ.filter (fun d : Fin n => ((d : ℤ) - D).natAbs = a) : Finset (Fin n)) := by
    intro d _ d' _ h
    apply Fin.ext
    simp only at h
    omega
  rw [← Finset.sum_image (f := F) hinj]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun c _ _ => hF c
  intro c hc
  obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hc
  exact hT d (Finset.mem_filter.mp hd).2

/-- The fibre inequality for the explicit fold weights. -/
theorem foldTheta_fibre {A : ℤ → ℝ} (hA : ∀ c, 0 < A c) (hm : ∀ c : ℤ, 0 ≤ c → A c ≤ A (-c))
    {n D g : ℕ} (hn : n = D + g + 1) (a : ℕ) :
    foldG A a * ∑ d ∈ Finset.univ.filter (fun d : Fin n => ((d : ℤ) - D).natAbs = a),
        (A ((d : ℤ) - D) * foldTheta A g ((d : ℤ) - D))⁻¹ ≤ 1 := by
  set F : ℤ → ℝ := fun c => (A c * foldTheta A g c)⁻¹ with hFd
  have hθp : ∀ c, 0 < foldTheta A g c := fun c =>
    lt_of_lt_of_le one_pos (foldTheta_ge_one hA hm g c)
  have hFp : ∀ c, 0 ≤ F c := fun c => (inv_pos.mpr (mul_pos (hA c) (hθp c))).le
  have hG : 0 < foldG A a := foldG_pos hA a
  by_cases h0 : a = 0
  · subst h0
    have h1 := fibre_sum_le (n := n) (D := D) (a := 0) F hFp {0} (fun d hd => by
      simp only [Finset.mem_singleton]
      omega)
    rw [Finset.sum_singleton] at h1
    have e : foldG A 0 * F 0 = 1 := by
      simp only [foldG, if_true, hFd, foldTheta]
      norm_num
      exact mul_inv_cancel₀ (hA 0).ne'
    calc _ ≤ foldG A 0 * F 0 := by gcongr
      _ = 1 := e
  · have hna : (a : ℤ) ≠ 0 := by omega
    have hGa : foldG A a = (A a + A (-(a : ℤ))) / 4 := by simp [foldG, h0]
    have hneg : F (-(a : ℤ)) = (A (-(a : ℤ)))⁻¹ := by
      have : foldTheta A g (-(a : ℤ)) = 1 := by
        unfold foldTheta
        rw [if_neg (by omega)]
      simp [hFd, this]
    have p1 := hA a
    have p2 := hA (-(a : ℤ))
    have hle := hm a (by omega)
    by_cases hg : a ≤ g
    · have h1 := fibre_sum_le (n := n) (D := D) (a := a) F hFp {(a : ℤ), -(a : ℤ)} (fun d hd => by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        omega)
      rw [Finset.sum_pair (by omega)] at h1
      have hpos : F a = 2 / (A a + A (-(a : ℤ))) := by
        have : foldTheta A g a = (A a + A (-(a : ℤ))) / (2 * A a) := by
          unfold foldTheta
          rw [if_pos ⟨by omega, by omega⟩]
        simp only [hFd, this]
        field_simp
      calc _ ≤ foldG A a * (F a + F (-(a : ℤ))) := by gcongr
        _ ≤ 1 := by
          rw [hGa, hneg, hpos]
          have e : (A a + A (-(a : ℤ))) / 4 * (2 / (A a + A (-(a : ℤ))) + (A (-(a : ℤ)))⁻¹) =
              1 / 2 + (A a + A (-(a : ℤ))) / (4 * A (-(a : ℤ))) := by
            field_simp
            ring
          rw [e]
          have : (A a + A (-(a : ℤ))) / (4 * A (-(a : ℤ))) ≤ 1 / 2 := by
            rw [div_le_iff₀ (by positivity)]
            linarith
          linarith
    · have h1 := fibre_sum_le (n := n) (D := D) (a := a) F hFp {-(a : ℤ)} (fun d hd => by
        have := d.isLt
        simp only [Finset.mem_singleton]
        omega)
      rw [Finset.sum_singleton] at h1
      calc _ ≤ foldG A a * F (-(a : ℤ)) := by gcongr
        _ ≤ 1 := by
          rw [hGa, hneg]
          have e : (A a + A (-(a : ℤ))) / 4 * (A (-(a : ℤ)))⁻¹ =
              (A a + A (-(a : ℤ))) / (4 * A (-(a : ℤ))) := by
            field_simp
          rw [e, div_le_one (by positivity)]
          linarith

end
end CatalanMeasure.GenD.Signed.RouteI.CompletedGas




namespace CatalanMeasure.GenD.Signed.RouteI.CompletedGas

open Finset MeasureTheory Complex Filter Polynomial
open scoped BigOperators ENNReal Topology

noncomputable section

variable {a b : ℕ}

theorem pairLog_symm {m : ℕ} (z : Fin m → ℂ) (i j : Fin m) : pairLog z i j = pairLog z j i := by
  unfold pairLog
  by_cases h : i = j
  · simp [h]
  · rw [if_neg h, if_neg (Ne.symm h), norm_sub_rev]

/-- Vandermonde of a concatenated list. -/
theorem vandermonde_append (x : Fin a → ℂ) (y : Fin b → ℂ) :
    ‖(Matrix.vandermonde (Fin.append x y)).det‖ ^ 2 =
      ‖(Matrix.vandermonde x).det‖ ^ 2 * ‖(Matrix.vandermonde y).det‖ ^ 2 *
        ‖∏ j, ∏ i, (y j - x i)‖ ^ 2 := by
  by_cases hz : Function.Injective (Fin.append x y)
  · have hx : Function.Injective x := by
      intro i j h
      have := @hz (Fin.castAdd b i) (Fin.castAdd b j) (by simpa using h)
      exact Fin.castAdd_injective _ _ this
    have hy : Function.Injective y := by
      intro i j h
      have := @hz (Fin.natAdd a i) (Fin.natAdd a j) (by simpa using h)
      exact Fin.natAdd_injective _ _ this
    have hxy : ∀ i j, y j - x i ≠ 0 := by
      intro i j h
      have := @hz (Fin.castAdd b i) (Fin.natAdd a j) (by
        simpa using (sub_eq_zero.mp h).symm)
      have h1 : ((Fin.castAdd b i : Fin (a + b)) : ℕ) = ((Fin.natAdd a j : Fin (a + b)) : ℕ) :=
        congrArg Fin.val this
      simp at h1
      have := i.isLt
      omega
    rw [vandermonde_sq_eq hz, vandermonde_sq_eq hx, vandermonde_sq_eq hy]
    have e1 : ∀ (i j : Fin a), pairLog (Fin.append x y) (Fin.castAdd b i) (Fin.castAdd b j) =
        pairLog x i j := by
      intro i j
      simp [pairLog, Fin.ext_iff]
    have e2 : ∀ (i j : Fin b), pairLog (Fin.append x y) (Fin.natAdd a i) (Fin.natAdd a j) =
        pairLog y i j := by
      intro i j
      simp [pairLog, Fin.ext_iff]
    have e3 : ∀ (i : Fin a) (j : Fin b),
        pairLog (Fin.append x y) (Fin.natAdd a j) (Fin.castAdd b i) = Real.log ‖y j - x i‖ := by
      intro i j
      have hne : (Fin.natAdd a j : Fin (a + b)) ≠ Fin.castAdd b i := by
        intro h
        have h1 := congrArg Fin.val h
        simp at h1
        have := i.isLt
        omega
      simp only [pairLog, if_neg hne, Fin.append_right, Fin.append_left]
    have hsum : ∑ i, ∑ j, pairLog (Fin.append x y) i j =
        ∑ i, ∑ j, pairLog x i j + ∑ i, ∑ j, pairLog y i j +
          2 * ∑ j, ∑ i, Real.log ‖y j - x i‖ := by
      simp only [Fin.sum_univ_add, Finset.sum_add_distrib, e1, e2]
      have e4 : ∑ i : Fin a, ∑ j : Fin b, pairLog (Fin.append x y) (Fin.castAdd b i)
          (Fin.natAdd a j) = ∑ j : Fin b, ∑ i : Fin a, Real.log ‖y j - x i‖ := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
        rw [pairLog_symm, e3]
      have e5 : ∑ i : Fin b, ∑ j : Fin a, pairLog (Fin.append x y) (Fin.natAdd a i)
          (Fin.castAdd b j) = ∑ j : Fin b, ∑ i : Fin a, Real.log ‖y j - x i‖ :=
        Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => e3 i j
      rw [e4, e5]
      ring
    rw [hsum, Real.exp_add, Real.exp_add]
    congr 1
    have hn : ‖∏ j, ∏ i, (y j - x i)‖ = Real.exp (∑ j, ∑ i, Real.log ‖y j - x i‖) := by
      rw [norm_prod, Real.exp_sum]
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [norm_prod, Real.exp_sum]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [Real.exp_log (norm_pos_iff.mpr (hxy i j))]
    rw [hn, ← Real.exp_nat_mul]
    norm_num
  · have h0 : (Matrix.vandermonde (Fin.append x y)).det = 0 := by
      by_contra h
      exact hz (Matrix.det_vandermonde_ne_zero_iff.mp h)
    rw [h0]
    obtain ⟨i, j, hij, hne⟩ : ∃ i j, Fin.append x y i = Fin.append x y j ∧ i ≠ j := by
      simpa [Function.Injective] using hz
    have hVx : ∀ i j : Fin a, x i = x j → i ≠ j → (Matrix.vandermonde x).det = 0 := by
      intro i j h hn
      by_contra hd
      exact hn (Matrix.det_vandermonde_ne_zero_iff.mp hd h)
    have hVy : ∀ i j : Fin b, y i = y j → i ≠ j → (Matrix.vandermonde y).det = 0 := by
      intro i j h hn
      by_contra hd
      exact hn (Matrix.det_vandermonde_ne_zero_iff.mp hd h)
    have hC : ∀ (i : Fin a) (j : Fin b), x i = y j → ∏ j, ∏ i, (y j - x i) = 0 := by
      intro i j h
      refine Finset.prod_eq_zero (Finset.mem_univ j) (Finset.prod_eq_zero (Finset.mem_univ i) ?_)
      rw [h, sub_self]
    have hz0 : ‖(Matrix.vandermonde x).det‖ ^ 2 * ‖(Matrix.vandermonde y).det‖ ^ 2 *
        ‖∏ j, ∏ i, (y j - x i)‖ ^ 2 = 0 := by
      revert hij hne
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
        refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;> intro hij hne
      · simp only [Fin.append_left] at hij
        rw [hVx i j hij (fun e => hne (by rw [e]))]
        simp
      · simp only [Fin.append_left, Fin.append_right] at hij
        rw [hC i j hij]
        simp
      · simp only [Fin.append_left, Fin.append_right] at hij
        rw [hC j i hij.symm]
        simp
      · simp only [Fin.append_right] at hij
        rw [hVy i j hij (fun e => hne (by rw [e]))]
        simp
    rw [hz0]
    simp

/-- The tuple sum of a gas with a fixed base list. -/
def tupleGas {X : Type*} [Fintype X] (c : ℕ) (wt : X → ℝ) (Z : X → ℂ) (base : Fin a → ℂ) : ℝ :=
  ∑ t : Fin c → X, (∏ l, wt (t l)) *
    (‖∏ l, ∏ i, (Z (t l) - base i)‖ ^ 2 * ‖(Matrix.vandermonde fun l => Z (t l)).det‖ ^ 2)

/-- **Completed gas bound.** The base Vandermonde is completed by the integrated particles, and the
tangent separates base and integrated particles. -/
theorem completed_gas {q : Measure ℂ} [IsFiniteMeasure q] {C : ℝ} (hC : 0 ≤ C)
    (hb : ChordBall q C) (hh : Integrable chordH q) {η : ℝ} (hη : 0 < η) :
    ∃ L : ℕ, ∀ (a c : ℕ) (ν : ℝ), 0 ≤ ν → ν * q.real Set.univ = ((a + c : ℕ) : ℝ) →
      ∀ {X : Type*} [Fintype X] (wt : X → ℝ), (∀ x, 0 ≤ wt x) → ∀ (Z : X → ℂ) (base : Fin a → ℂ),
      ‖(Matrix.vandermonde base).det‖ ^ 2 * tupleGas c wt Z base ≤
        Real.exp (2 * ν * ∑ i, planarPot q (base i) - ν ^ 2 * planarEnergy q +
          2 * ν * ((a + c : ℕ) : ℝ) * η + ((a + c : ℕ) : ℝ) / 2 * harm L) *
        (∑ x, wt x * Real.exp (2 * ν * planarPot q (Z x))) ^ c := by
  obtain ⟨L, hL⟩ := planar_tangent hC hb hh hη
  refine ⟨L, fun a c ν hν hm X _ wt hwt Z base => ?_⟩
  classical
  set Err := 2 * ν * ∑ i, planarPot q (base i) - ν ^ 2 * planarEnergy q +
    2 * ν * ((a + c : ℕ) : ℝ) * η + ((a + c : ℕ) : ℝ) / 2 * harm L with hErr
  have hpt : ∀ t : Fin c → X,
      ‖(Matrix.vandermonde base).det‖ ^ 2 * ((∏ l, wt (t l)) *
        (‖∏ l, ∏ i, (Z (t l) - base i)‖ ^ 2 * ‖(Matrix.vandermonde fun l => Z (t l)).det‖ ^ 2)) ≤
      Real.exp Err * ∏ l, (wt (t l) * Real.exp (2 * ν * planarPot q (Z (t l)))) := by
    intro t
    have h1 := hL (a + c) ν hν hm (Fin.append base fun l => Z (t l))
    rw [vandermonde_append] at h1
    have hsum : ∑ i, planarPot q (Fin.append base (fun l => Z (t l)) i) =
        ∑ i, planarPot q (base i) + ∑ l, planarPot q (Z (t l)) := by
      rw [Fin.sum_univ_add]
      simp
    rw [hsum] at h1
    have hexp : Real.exp (2 * ν * (∑ i, planarPot q (base i) + ∑ l, planarPot q (Z (t l))) -
        ν ^ 2 * planarEnergy q + 2 * ν * ((a + c : ℕ) : ℝ) * η +
        ((a + c : ℕ) : ℝ) / 2 * harm L) =
        Real.exp Err * ∏ l, Real.exp (2 * ν * planarPot q (Z (t l))) := by
      rw [← Real.exp_sum, ← Real.exp_add, hErr, ← Finset.mul_sum]
      congr 1
      ring
    rw [hexp] at h1
    have hw0 : 0 ≤ ∏ l, wt (t l) := Finset.prod_nonneg fun l _ => hwt _
    calc _ = (∏ l, wt (t l)) * (‖(Matrix.vandermonde base).det‖ ^ 2 *
          ‖(Matrix.vandermonde fun l => Z (t l)).det‖ ^ 2 *
          ‖∏ l, ∏ i, (Z (t l) - base i)‖ ^ 2) := by ring
      _ ≤ (∏ l, wt (t l)) * (Real.exp Err * ∏ l, Real.exp (2 * ν * planarPot q (Z (t l)))) :=
          mul_le_mul_of_nonneg_left h1 hw0
      _ = _ := by rw [Finset.prod_mul_distrib]; ring
  unfold tupleGas
  rw [Finset.mul_sum]
  calc _ ≤ ∑ t : Fin c → X, Real.exp Err *
        ∏ l, (wt (t l) * Real.exp (2 * ν * planarPot q (Z (t l)))) :=
        Finset.sum_le_sum fun t _ => hpt t
    _ = _ := by
        rw [← Finset.mul_sum]
        congr 1
        have := Finset.prod_univ_sum (fun _ : Fin c => (Finset.univ : Finset X))
          (fun _ x => wt x * Real.exp (2 * ν * planarPot q (Z x)))
        simp only [Fintype.piFinset_univ, Finset.prod_const, Finset.card_univ,
          Fintype.card_fin] at this
        exact this.symm

end
end CatalanMeasure.GenD.Signed.RouteI.CompletedGas




namespace CatalanMeasure.GenD.Signed.RouteI.CompletedGas

open Finset MeasureTheory Complex Filter Polynomial
open scoped BigOperators ENNReal Topology

noncomputable section

variable {kp k s : ℕ}

theorem aeval_omegaPoly (ξ : Fin kp → ℝ) (z : ℂ) :
    aeval z (omegaPoly ξ) = ∏ p, (z - (ξ p : ℂ)) := by
  simp [omegaPoly, map_prod, aeval_X, aeval_C]

theorem real_vandermonde_sq (ξ : Fin kp → ℝ) :
    (Matrix.vandermonde ξ).det ^ 2 =
      ‖(Matrix.vandermonde fun p => (ξ p : ℂ)).det‖ ^ 2 := by
  have e : (Matrix.vandermonde fun p => (ξ p : ℂ)) =
      (Complex.ofRealHom).mapMatrix (Matrix.vandermonde ξ) := by
    ext i j
    simp [Matrix.vandermonde_apply]
  rw [e, ← RingHom.map_det]
  simp only [ofRealHom_eq_coe, norm_real, Real.norm_eq_abs, sq_abs]

variable {X : Type*} [Fintype X] [DecidableEq X]

theorem posGas_eq_tuple (D : ℕ) (w : X → ℝ) (γ : X → ℂ) (ξ : Fin kp → ℝ) :
    posGas k D w γ ξ = tupleGas k (fun x => w x * ‖γ x ^ (-(D : ℤ))‖ ^ 2) γ
      (fun p => (ξ p : ℂ)) := by
  unfold posGas tupleGas
  refine Finset.sum_congr rfl fun t _ => ?_
  simp only [aeval_omegaPoly, Finset.prod_mul_distrib, norm_mul, mul_pow, norm_prod,
    Finset.prod_pow]
  ring

theorem negGas_eq_tuple (w : X → ℝ) (γ : X → ℂ) (u : Fin k → ℝ) :
    negGas s w γ u = tupleGas s w (fun x => joukowski (γ x)) (fun p => (u p : ℂ)) := by
  unfold negGas tupleGas
  refine Finset.sum_congr rfl fun t _ => ?_
  simp only [aeval_omegaPoly]

/-- **The gas determinant bound.** -/
theorem gas_det_bound {qp qm : Measure ℂ} [IsFiniteMeasure qp] [IsFiniteMeasure qm]
    {Cp Cm : ℝ} (hCp : 0 ≤ Cp) (hCm : 0 ≤ Cm) (hbp : ChordBall qp Cp) (hbm : ChordBall qm Cm)
    (hhp : Integrable chordH qp) (hhm : Integrable chordH qm) {η : ℝ} (hη : 0 < η) :
    ∃ Lp Lm : ℕ, ∀ (kp k s D : ℕ) (ν : ℝ), 0 ≤ ν →
      ν * qp.real Set.univ = ((kp + k : ℕ) : ℝ) → ν * qm.real Set.univ = ((k + s : ℕ) : ℝ) →
      ∀ (hD : k + s = D + 1) (hn : kp + k ≤ 2 * D + 1)
      (ξ : Fin kp → ℝ) (x : Fin k → ℝ), (∀ p, ξ p ≠ 0) → (∀ b, x b ≠ 0) →
      ∀ {X : Type*} [Fintype X] [DecidableEq X] {w : X → ℝ} {γ : X → ℂ} {A : ℤ → ℝ},
      (∀ x, 0 ≤ w x) → (∀ x, γ x ≠ 0) → (∀ c, 0 < A c) → LaurentOrtho D w γ A →
      ∀ (θ : Fin (kp + k) → ℝ), (∀ d, 1 ≤ θ d) →
      (∀ a : ℕ, a ≤ D → foldG A a *
        ∑ d ∈ Finset.univ.filter (fun d : Fin (kp + k) => ((d : ℤ) - D).natAbs = a),
          (A ((d : ℤ) - D) * θ d)⁻¹ ≤ 1) →
      (laurentM (-(D : ℤ)) ξ x).det ^ 2 * (∏ a : Fin k ⊕ Fin s, foldG A (colDeg a)) *
          ((k.factorial : ℝ) * (s.factorial : ℝ)) ≤
        (∏ p, ξ p ^ (-(D : ℤ))) ^ 2 * (∏ a : Fin k ⊕ Fin s, chebLead (colDeg a)) ^ 2 *
          (∏ d, θ d) *
          (Real.exp (2 * ν * ∑ p, planarPot qp (ξ p) - ν ^ 2 * planarEnergy qp +
              2 * ν * ((kp + k : ℕ) : ℝ) * η + ((kp + k : ℕ) : ℝ) / 2 * harm Lp) *
            (∑ y, (w y * ‖γ y ^ (-(D : ℤ))‖ ^ 2) * Real.exp (2 * ν * planarPot qp (γ y))) ^ k) *
          (Real.exp (2 * ν * ∑ b, planarPot qm (((x b + (x b)⁻¹) / 2 : ℝ) : ℂ) -
              ν ^ 2 * planarEnergy qm +
              2 * ν * ((k + s : ℕ) : ℝ) * η + ((k + s : ℕ) : ℝ) / 2 * harm Lm) *
            (∑ y, w y * Real.exp (2 * ν * planarPot qm (joukowski (γ y)))) ^ s) := by
  obtain ⟨Lp, hLp⟩ := completed_gas hCp hbp hhp hη
  obtain ⟨Lm, hLm⟩ := completed_gas hCm hbm hhm hη
  refine ⟨Lp, Lm, fun kp k s D ν hν hmp hmm hD hn ξ x hξ hx X _ _ w γ A hw hγ hA hO θ hθ hfold => ?_⟩
  have hF := finite_gram (s := s) D hD hn ξ x hξ hx hγ hA hO θ hθ hfold
  have hP := hLp kp k ν hν hmp (fun y => w y * ‖γ y ^ (-(D : ℤ))‖ ^ 2)
    (fun y => mul_nonneg (hw y) (sq_nonneg _)) γ (fun p => (ξ p : ℂ))
  have hM := hLm k s ν hν hmm w hw (fun y => joukowski (γ y))
    (fun b => (((x b + (x b)⁻¹) / 2 : ℝ) : ℂ))
  rw [← posGas_eq_tuple, ← real_vandermonde_sq] at hP
  rw [← negGas_eq_tuple w γ (fun b => (x b + (x b)⁻¹) / 2),
    ← real_vandermonde_sq (fun b => (x b + (x b)⁻¹) / 2)] at hM
  set VP := (Matrix.vandermonde ξ).det ^ 2 with hVP
  set VM := (Matrix.vandermonde fun b => (x b + (x b)⁻¹) / 2).det ^ 2 with hVM
  set PG := posGas k D w γ ξ with hPG
  set NG := negGas s w γ (fun b => (x b + (x b)⁻¹) / 2) with hNG
  set S := (∏ p, ξ p ^ (-(D : ℤ))) with hS
  set Le := (∏ a : Fin k ⊕ Fin s, chebLead (colDeg a)) with hLe
  set Θ := ∏ d, θ d with hΘ
  have hΘ0 : 0 ≤ Θ := Finset.prod_nonneg fun d _ => by linarith [hθ d]
  have hNG0 : 0 ≤ VM * NG := by
    have h1 : 0 ≤ VM := sq_nonneg _
    have h2 : 0 ≤ NG := by
      refine Finset.sum_nonneg fun t _ => mul_nonneg
        (Finset.prod_nonneg fun a _ => hw _) (by positivity)
    exact mul_nonneg h1 h2
  have hc0 : 0 ≤ S ^ 2 * Le ^ 2 * Θ := by positivity
  calc _ ≤ ((S * (Matrix.vandermonde ξ).det) ^ 2) *
        ((Le * (Matrix.vandermonde fun b => (x b + (x b)⁻¹) / 2).det) ^ 2) * Θ * PG * NG := hF
    _ = S ^ 2 * Le ^ 2 * Θ * (VP * PG) * (VM * NG) := by
        rw [hVP, hVM]
        ring
    _ ≤ _ := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left hP hc0) hM hNG0 ?_
        have h2 : 0 ≤ VP * PG := by
          have h3 : 0 ≤ PG := by
            refine Finset.sum_nonneg fun t _ => mul_nonneg
              (Finset.prod_nonneg fun a _ => hw _) (by positivity)
          exact mul_nonneg (sq_nonneg _) h3
        have h4 := mul_le_mul_of_nonneg_left hP hc0
        exact (mul_nonneg hc0 h2).trans h4

end
end CatalanMeasure.GenD.Signed.RouteI.CompletedGas




namespace CatalanMeasure.GenD.Signed.RouteI.CompletedGas

open Finset MeasureTheory Complex Filter Set
open scoped BigOperators ENNReal Topology

noncomputable section

/-! ### Good reference measures -/

/-- A finite reference with a square-root ball bound and integrable chordal height. -/
def GoodRef (q : Measure ℂ) : Prop :=
  IsFiniteMeasure q ∧ (∃ C, 0 ≤ C ∧ ChordBall q C) ∧ Integrable chordH q

theorem GoodRef.zero : GoodRef 0 :=
  ⟨inferInstance, ⟨0, le_rfl, fun z t _ _ => by simp⟩, integrable_zero_measure⟩

theorem GoodRef.add {q₁ q₂ : Measure ℂ} (h₁ : GoodRef q₁) (h₂ : GoodRef q₂) :
    GoodRef (q₁ + q₂) := by
  obtain ⟨f₁, ⟨C₁, hC₁, b₁⟩, i₁⟩ := h₁
  obtain ⟨f₂, ⟨C₂, hC₂, b₂⟩, i₂⟩ := h₂
  refine ⟨inferInstance, ⟨C₁ + C₂, add_nonneg hC₁ hC₂, fun z t ht ht1 => ?_⟩, i₁.add_measure i₂⟩
  rw [Measure.add_apply, add_mul, ENNReal.ofReal_add (by positivity) (by positivity)]
  exact add_le_add (b₁ z t ht ht1) (b₂ z t ht ht1)

/-- Euclidean form of the ball bound, with bounded support. -/
def EuclBall (q : Measure ℂ) (C R : ℝ) : Prop :=
  (∀ (z : ℂ) (ρ : ℝ), 0 < ρ → q (Metric.closedBall z ρ) ≤ ENNReal.ofReal (C * √ρ)) ∧
    ∀ᵐ w ∂q, ‖w‖ ≤ R

theorem cden_eq_norm (z : ℂ) : cden z = 1 + ‖z‖ ^ 2 := by
  rw [cden, normSq_eq_norm_sq]

theorem goodRef_of_eucl {q : Measure ℂ} [IsFiniteMeasure q] {C R : ℝ} (hC : 0 ≤ C) (hR : 0 ≤ R)
    (h : EuclBall q C R) : GoodRef q := by
  refine ⟨inferInstance, ?_, ?_⟩
  swap
  · have hc : Continuous chordH := by
      unfold chordH
      exact continuous_const.mul (cden_continuous.log fun z => (cden_pos z).ne')
    refine Integrable.of_bound hc.aestronglyMeasurable ((1 / 2) * Real.log (1 + R ^ 2)) ?_
    filter_upwards [h.2] with w hw
    rw [Real.norm_eq_abs, abs_of_nonneg (chordH_nonneg w)]
    unfold chordH
    have h1 : cden w ≤ 1 + R ^ 2 := by
      rw [cden_eq_norm]
      have := pow_le_pow_left₀ (norm_nonneg w) hw 2
      linarith
    have := Real.log_le_log (cden_pos w) h1
    linarith
  set B := 1 + R ^ 2 with hB
  have hB1 : 1 ≤ B := by nlinarith [sq_nonneg R]
  set Z := 1 + (2 * R + 1) ^ 2 with hZ
  have hZ0 : 0 < Z := by positivity
  set K := √(Z * B) with hK
  have hK0 : 0 ≤ K := Real.sqrt_nonneg _
  set M := q.real Set.univ with hM
  have hM0 : 0 ≤ M := measureReal_nonneg
  refine ⟨C * √K + 8 * B * M, by positivity, fun z t ht ht1 => ?_⟩
  by_cases hz : ‖z‖ ≤ 2 * R + 1
  · have hsub : ∀ᵐ w ∂q, w ∈ {w | chordD2 z w ≤ t ^ 4} → w ∈ Metric.closedBall z (t ^ 2 * K) := by
      filter_upwards [h.2] with w hw hS
      have hS' : chordD2 z w ≤ t ^ 4 := hS
      unfold chordD2 at hS'
      rw [div_le_iff₀ (mul_pos (cden_pos z) (cden_pos w)), normSq_eq_norm_sq] at hS'
      have h1 : cden z ≤ Z := by
        rw [cden_eq_norm, hZ]
        have := pow_le_pow_left₀ (norm_nonneg z) hz 2
        linarith
      have h2 : cden w ≤ B := by
        rw [cden_eq_norm, hB]
        have := pow_le_pow_left₀ (norm_nonneg w) hw 2
        linarith
      have h3 : ‖z - w‖ ^ 2 ≤ (t ^ 2 * K) ^ 2 := by
        have hKK : K ^ 2 = Z * B := Real.sq_sqrt (by positivity)
        calc ‖z - w‖ ^ 2 ≤ t ^ 4 * (cden z * cden w) := hS'
          _ ≤ t ^ 4 * (Z * B) := by
              have := mul_le_mul h1 h2 (cden_pos w).le hZ0.le
              gcongr
          _ = _ := by rw [mul_pow, hKK]; ring
      rw [Metric.mem_closedBall, dist_comm, dist_eq_norm]
      exact abs_le_of_sq_le_sq' h3 (by positivity) |>.2
    by_cases hKp : K = 0
    · exfalso
      have : 0 < Z * B := by positivity
      have := Real.sqrt_pos.mpr this
      exact this.ne' hKp
    have hKpos : 0 < K := lt_of_le_of_ne hK0 (Ne.symm hKp)
    calc q {w | chordD2 z w ≤ t ^ 4} ≤ q (Metric.closedBall z (t ^ 2 * K)) :=
          measure_mono_ae hsub
      _ ≤ ENNReal.ofReal (C * √(t ^ 2 * K)) := h.1 z _ (by positivity)
      _ ≤ _ := by
          apply ENNReal.ofReal_le_ofReal
          rw [Real.sqrt_mul (by positivity), Real.sqrt_sq ht.le]
          have : 0 ≤ 8 * B * M * t := by positivity
          nlinarith
  · have hz' : 2 * R + 1 < ‖z‖ := not_le.mp hz
    have hz1 : 1 ≤ ‖z‖ := by linarith
    have hfar : ∀ᵐ w ∂q, 1 / (8 * B) ≤ chordD2 z w := by
      filter_upwards [h.2] with w hw
      unfold chordD2
      rw [div_le_div_iff₀ (by positivity) (mul_pos (cden_pos z) (cden_pos w)),
        normSq_eq_norm_sq]
      have h1 : ‖z‖ / 2 ≤ ‖z - w‖ := by
        have := norm_sub_norm_le z w
        linarith
      have h2 : (‖z‖ / 2) ^ 2 ≤ ‖z - w‖ ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
      have h3 : cden z ≤ 2 * ‖z‖ ^ 2 := by
        rw [cden_eq_norm]
        nlinarith
      have h4 : cden w ≤ B := by
        rw [cden_eq_norm, hB]
        have := pow_le_pow_left₀ (norm_nonneg w) hw 2
        linarith
      have h5 : cden z * cden w ≤ 2 * ‖z‖ ^ 2 * B :=
        mul_le_mul h3 h4 (cden_pos w).le (by positivity)
      nlinarith
    by_cases hsmall : t ^ 4 < 1 / (8 * B)
    · have : q {w | chordD2 z w ≤ t ^ 4} = 0 := by
        refine measure_eq_zero_iff_ae_notMem.mpr ?_
        filter_upwards [hfar] with w hw hS
        have hS' : chordD2 z w ≤ t ^ 4 := hS
        linarith
      rw [this]
      exact zero_le
    · have ht4 : 1 / (8 * B) ≤ t := by
        have h1 : t ^ 4 ≤ t := by
          calc t ^ 4 ≤ t ^ 1 := pow_le_pow_of_le_one ht.le ht1 (by norm_num)
            _ = t := pow_one t
        linarith [not_lt.mp hsmall]
      have h8 : 1 ≤ 8 * B * t := by
        rw [div_le_iff₀ (by positivity)] at ht4
        linarith
      calc q {w | chordD2 z w ≤ t ^ 4} ≤ q Set.univ := measure_mono (Set.subset_univ _)
        _ = ENNReal.ofReal M := by
            rw [hM, Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _)]
        _ ≤ _ := by
            apply ENNReal.ofReal_le_ofReal
            have h9 : 0 ≤ C * √K * t := by positivity
            nlinarith

end
end CatalanMeasure.GenD.Signed.RouteI.CompletedGas




namespace CatalanMeasure.GenD.Signed.RouteI.CompletedGas

open Filter Set MeasureTheory OAI.InternalCatalan Topology
open scoped BigOperators ComplexConjugate

noncomputable section

local notation "Tc" k => (Polynomial.Chebyshev.T ℝ ((k : ℕ) : ℤ))

theorem cosineKernel_le_log_two {r u v : ℝ} (hr : r ∈ Ioo (0:ℝ) 1)
    (hu : u ∈ Icc (-1:ℝ) 1) (hv : v ∈ Icc (-1:ℝ) 1) :
    realEnergyCosineKernel r u v ≤ Real.log 2 := by
  have hn1 : ‖realEnergyCirclePoint u * realEnergyCirclePoint v‖ = 1 := by
    rw [Complex.norm_mul, realEnergyCirclePoint_norm hu, realEnergyCirclePoint_norm hv, one_mul]
  have hn2 : ‖realEnergyCirclePoint u * conj (realEnergyCirclePoint v)‖ = 1 := by
    rw [Complex.norm_mul, Complex.norm_conj,
      realEnergyCirclePoint_norm hu, realEnergyCirclePoint_norm hv, one_mul]
  have key : ∀ z : ℂ, ‖z‖ = 1 → Real.log ‖(1:ℂ) - (r:ℂ)*z‖ ≤ Real.log 2 := by
    intro z hz
    have hlow : 0 < ‖(1:ℂ) - (r:ℂ)*z‖ := by
      have hne : (1:ℂ) - (r:ℂ)*z ≠ 0 := by
        intro h0
        have h1 : (r:ℂ)*z = 1 := by linear_combination -h0
        have h2 := congrArg norm h1
        simp only [Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs, hz, mul_one, norm_one,
          abs_of_pos hr.1] at h2
        linarith [hr.2]
      exact norm_pos_iff.mpr hne
    apply Real.log_le_log hlow
    calc ‖(1:ℂ) - (r:ℂ)*z‖ ≤ ‖(1:ℂ)‖ + ‖(r:ℂ)*z‖ := norm_sub_le _ _
      _ = 1 + r := by
        simp only [Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs, hz, mul_one, norm_one,
          abs_of_pos hr.1]
      _ ≤ 2 := by linarith [hr.2]
  have h1 := key _ hn1
  have h2 := key _ hn2
  unfold realEnergyCosineKernel
  linarith only [h1, h2]

theorem cosineKernel_tendsto {u v : ℝ} (hu : u ∈ Icc (-1:ℝ) 1) (hv : v ∈ Icc (-1:ℝ) 1)
    (huv : u ≠ v) :
    Tendsto (fun r : ℝ => realEnergyCosineKernel r u v) (𝓝 1) (𝓝 (Real.log |u - v|)) := by
  rw [← realEnergyCosineKernel_one hu hv huv]
  have hp := realEnergy_cosine_chord_product hu hv
  have hpne : ‖(1:ℂ) - realEnergyCirclePoint u * realEnergyCirclePoint v‖ *
      ‖(1:ℂ) - realEnergyCirclePoint u * conj (realEnergyCirclePoint v)‖ ≠ 0 := by
    rw [hp]
    have : 0 < |u - v| := abs_pos.mpr (sub_ne_zero.mpr huv)
    positivity
  have h1 := left_ne_zero_of_mul hpne
  have h2 := right_ne_zero_of_mul hpne
  have hc : ∀ z : ℂ, ‖(1:ℂ) - z‖ ≠ 0 → ContinuousAt (fun r : ℝ => Real.log ‖(1:ℂ) - (r:ℂ)*z‖) 1 := by
    intro z hz
    have hcont : Continuous fun r : ℝ => ‖(1:ℂ) - (r:ℂ)*z‖ := by fun_prop
    refine ContinuousAt.log hcont.continuousAt ?_
    simpa using hz
  have c1 := hc _ h1
  have c2 := hc _ h2
  have h : ContinuousAt (fun r : ℝ => realEnergyCosineKernel r u v) 1 := by
    unfold realEnergyCosineKernel
    exact (continuousAt_const.add c1).add c2
  exact h.tendsto

theorem chebT_measurable (k : ℕ) : Continuous fun t : ℝ => (Tc k).eval t :=
  Polynomial.continuous _

/-- **Integrated logarithmic kernel.** For a finite measure carried by `[-1,1]`, with moments
whose `1/k` series converges absolutely, the logarithmic potential is the Chebyshev series.
The singular diagonal enters only under the integral: no pointwise series at `t = x` is used. -/
theorem cosine_potential_identity {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] (τ : α → ℝ) (hτ : Measurable τ) (hτ1 : ∀ᵐ y ∂μ, τ y ∈ Icc (-1:ℝ) 1)
    {x : ℝ} (hx : x ∈ Icc (-1:ℝ) 1) (hne : ∀ᵐ y ∂μ, x ≠ τ y)
    (hint : Integrable (fun y => Real.log |x - τ y|) μ) (A : ℕ → ℝ)
    (hA : ∀ k, A k = ∫ y, (Tc k).eval (τ y) ∂μ)
    (hsum : Summable (fun n => |A (n+1)| / ((n+1:ℕ):ℝ))) :
    ∫ y, Real.log |x - τ y| ∂μ = -(μ.real univ) * Real.log 2 - 2 * barrierTrialT A x := by
  have hTm : ∀ k, Measurable fun y => (Tc k).eval (τ y) := fun k =>
    (chebT_measurable k).measurable.comp hτ
  have hTb : ∀ k, ∀ᵐ y ∂μ, |(Tc k).eval (τ y)| ≤ 1 := fun k => by
    filter_upwards [hτ1] with y hy
    exact Polynomial.Chebyshev.abs_eval_T_real_le_one (k:ℤ) (abs_le.mpr hy)
  have hTx : ∀ k : ℕ, |(Tc k).eval x| ≤ 1 := fun k =>
    Polynomial.Chebyshev.abs_eval_T_real_le_one (k:ℤ) (abs_le.mpr hx)
  have hTi : ∀ k, Integrable (fun y => (Tc k).eval (τ y)) μ := fun k =>
    Integrable.of_bound (hTm k).aestronglyMeasurable 1 (by simpa [Real.norm_eq_abs] using hTb k)
  -- the regularised identity
  have hreg : ∀ r : ℝ, r ∈ Ioo (0:ℝ) 1 →
      HasSum (fun k : ℕ => 2 * r^k * (Tc k).eval x * A k / (k:ℝ))
        (-(∫ y, realEnergyCosineKernel r x (τ y) ∂μ) - μ.real univ * Real.log 2) := by
    intro r hr
    have hrI : r ∈ Ico (0:ℝ) 1 := ⟨hr.1.le, hr.2⟩
    have hKi : Integrable (fun y => realEnergyCosineKernel r x (τ y)) μ := by
      refine Integrable.of_bound ?_ (|(-Real.log 2 + 2 * Real.log (1 - r))| + Real.log 2) ?_
      · have hm : Measurable fun y => realEnergyCosineKernel r x (τ y) := by
          have hc : Measurable fun t : ℝ => realEnergyCosineKernel r x t := by
            unfold realEnergyCosineKernel realEnergyCirclePoint
            fun_prop
          exact hc.comp hτ
        exact hm.aestronglyMeasurable
      · filter_upwards [hτ1] with y hy
        have h1 := realEnergyCosineKernel_lower hr hx hy
        have h2 := cosineKernel_le_log_two hr hx hy
        have h3 := neg_abs_le (-Real.log 2 + 2 * Real.log (1 - r))
        have h4 := Real.log_pos (by norm_num : (1:ℝ) < 2)
        rw [Real.norm_eq_abs, abs_le]
        constructor <;> linarith [abs_nonneg (-Real.log 2 + 2 * Real.log (1 - r))]
    have h := hasSum_integral_of_dominated_convergence (μ := μ)
      (F := fun (k : ℕ) y => 2 * r^k * (Tc k).eval x * (Tc k).eval (τ y) / (k:ℝ))
      (f := fun y => -realEnergyCosineKernel r x (τ y) - Real.log 2)
      (fun k _ => 2 * r^k) (fun k => by
        have hc : Measurable fun y => 2 * r^k * (Tc k).eval x * (Tc k).eval (τ y) / (k:ℝ) :=
          ((hTm k).const_mul _).div_const _
        exact hc.aestronglyMeasurable)
      (fun k => by
        filter_upwards [hTb k] with y hy
        have hb : |(Tc k).eval x * (Tc k).eval (τ y)| ≤ 1 := by
          rw [abs_mul]
          exact mul_le_one₀ (hTx k) (abs_nonneg _) hy
        have hk : |(k:ℝ)⁻¹| ≤ 1 := by
          rcases Nat.eq_zero_or_pos k with rfl | hk
          · simp
          · rw [abs_of_nonneg (by positivity)]
            exact inv_le_one_of_one_le₀ (by exact_mod_cast hk)
        have hr0 : 0 ≤ r^k := pow_nonneg hr.1.le k
        rw [Real.norm_eq_abs, show 2 * r^k * (Tc k).eval x * (Tc k).eval (τ y) / (k:ℝ) =
          (2 * r^k) * ((Tc k).eval x * (Tc k).eval (τ y)) * (k:ℝ)⁻¹ by
            rw [div_eq_mul_inv]; ring, abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2*r^k)]
        calc 2*r^k * |(Tc k).eval x * (Tc k).eval (τ y)| * |(k:ℝ)⁻¹| ≤ 2*r^k * 1 * 1 := by gcongr
          _ = 2*r^k := by ring)
      (Eventually.of_forall fun y =>
        (summable_geometric_of_lt_one hr.1.le hr.2).mul_left 2)
      (integrable_const _)
      (by
        filter_upwards [hτ1] with y hy
        exact energy_hasSum_cosine_kernel hrI hx hy)
    convert h using 1
    · funext k
      rw [hA k]
      have : (fun y => 2 * r^k * (Tc k).eval x * (Tc k).eval (τ y) / (k:ℝ)) =
          fun y => (2 * r^k * (Tc k).eval x / (k:ℝ)) * (Tc k).eval (τ y) := by
        funext y; ring
      rw [this, integral_const_mul]
      ring
    · have e := integral_sub (μ := μ) (f := fun y => -realEnergyCosineKernel r x (τ y))
        (g := fun _ => Real.log 2) hKi.neg (integrable_const _)
      rw [e, integral_neg, integral_const, smul_eq_mul]
  -- pass to the limit along `r_j = 1 - 1/(j+2)`
  let rj : ℕ → ℝ := fun j => 1 - 1/((j:ℝ)+2)
  have hrj : ∀ j, rj j ∈ Ioo (0:ℝ) 1 := fun j => by
    have h2 : (0:ℝ) < (j:ℝ)+2 := by positivity
    have h3 : 1/((j:ℝ)+2) ≤ 1/2 := by
      apply one_div_le_one_div_of_le (by norm_num)
      have : (0:ℝ) ≤ j := Nat.cast_nonneg j
      linarith
    exact ⟨by dsimp [rj]; linarith, by dsimp [rj]; linarith [one_div_pos.mpr h2]⟩
  have hrhalf : ∀ j, 1/2 ≤ rj j := fun j => by
    have h3 : 1/((j:ℝ)+2) ≤ 1/2 := by
      apply one_div_le_one_div_of_le (by norm_num)
      have : (0:ℝ) ≤ j := Nat.cast_nonneg j
      linarith
    dsimp [rj]; linarith
  have hrlim : Tendsto rj atTop (𝓝 1) := by
    have h : Tendsto (fun j : ℕ => 1/((j:ℝ)+2)) atTop (𝓝 0) := by
      have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
      have h2 := (tendsto_add_atTop_iff_nat 1).mpr this
      refine h2.congr fun j => ?_
      push_cast
      ring_nf
    simpa [rj] using (tendsto_const_nhds (x := (1:ℝ))).sub h
  have hlog2 := Real.log_pos (by norm_num : (1:ℝ) < 2)
  have hI : Tendsto (fun j => ∫ y, realEnergyCosineKernel (rj j) x (τ y) ∂μ) atTop
      (𝓝 (∫ y, Real.log |x - τ y| ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence
      (fun y => |(Real.log |x - τ y|)| + 2 * Real.log 2) (fun j => ?_) ?_ (fun j => ?_) ?_
    · have hc : Measurable fun t : ℝ => realEnergyCosineKernel (rj j) x t := by
        unfold realEnergyCosineKernel realEnergyCirclePoint
        fun_prop
      exact (hc.comp hτ).aestronglyMeasurable
    · exact hint.abs.add (integrable_const _)
    · filter_upwards [hτ1, hne] with y hy hxy
      have h1 := realEnergyCosineKernel_compare hx hy hxy (hrj j).1
      have h2 := cosineKernel_le_log_two (hrj j) hx hy
      have h3 : -Real.log 2 ≤ Real.log (rj j) := by
        have := Real.log_le_log (by norm_num) (hrhalf j)
        rwa [one_div, Real.log_inv] at this
      have h4 : Real.log (rj j) ≤ 0 := Real.log_nonpos (hrj j).1.le (hrj j).2.le
      have h5 := neg_abs_le (Real.log |x - τ y|)
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> linarith [abs_nonneg (Real.log |x - τ y|)]
    · filter_upwards [hτ1, hne] with y hy hxy
      exact (cosineKernel_tendsto hx hy hxy).comp hrlim
  have hS : Tendsto (fun j => ∑' k : ℕ, 2 * (rj j)^k * (Tc k).eval x * A k / (k:ℝ)) atTop
      (𝓝 (∑' k : ℕ, 2 * (Tc k).eval x * A k / (k:ℝ))) := by
    have hbound : Summable (fun k : ℕ => 2 * (|A k| / (k:ℝ))) := by
      apply Summable.mul_left
      apply (summable_nat_add_iff 1).mp
      simpa using hsum
    refine tendsto_tsum_of_dominated_convergence hbound (fun k => ?_) (Eventually.of_forall
      fun j k => ?_)
    · have hp : Tendsto (fun j => (rj j)^k) atTop (𝓝 1) := by
        simpa using hrlim.pow k
      have := ((hp.const_mul 2).mul_const ((Tc k).eval x)).mul_const (A k) |>.div_const (k:ℝ)
      simpa using this
    · have hr0 : 0 ≤ (rj j)^k := pow_nonneg (hrj j).1.le k
      have hr1 : (rj j)^k ≤ 1 := pow_le_one₀ (hrj j).1.le (hrj j).2.le
      rw [Real.norm_eq_abs, abs_div, abs_mul, abs_mul, abs_mul, Nat.abs_cast,
        abs_of_nonneg hr0, abs_of_pos (by norm_num : (0:ℝ) < 2)]
      have hk : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
      calc 2 * (rj j)^k * |(Tc k).eval x| * |A k| / (k:ℝ) ≤ 2 * 1 * 1 * |A k| / (k:ℝ) := by
            gcongr
            exact hTx k
        _ = 2 * (|A k| / (k:ℝ)) := by ring
  have heq : ∀ j, ∑' k : ℕ, 2 * (rj j)^k * (Tc k).eval x * A k / (k:ℝ) =
      -(∫ y, realEnergyCosineKernel (rj j) x (τ y) ∂μ) - μ.real univ * Real.log 2 :=
    fun j => (hreg (rj j) (hrj j)).tsum_eq
  have hlim := tendsto_nhds_unique (hS.congr heq)
    ((hI.neg).sub_const (μ.real univ * Real.log 2))
  have htail : (∑' k : ℕ, 2 * (Tc k).eval x * A k / (k:ℝ)) = 2 * barrierTrialT A x := by
    have hs0 : Summable (fun k : ℕ => 2 * (Tc k).eval x * A k / (k:ℝ)) := by
      have hb : Summable (fun k : ℕ => 2 * (|A k| / (k:ℝ))) := by
        apply Summable.mul_left
        apply (summable_nat_add_iff 1).mp
        simpa using hsum
      refine Summable.of_norm_bounded hb fun k => ?_
      rw [Real.norm_eq_abs, abs_div, abs_mul, abs_mul, Nat.abs_cast,
        abs_of_pos (by norm_num : (0:ℝ) < 2)]
      have hk : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
      calc 2 * |(Tc k).eval x| * |A k| / (k:ℝ) ≤ 2 * 1 * |A k| / (k:ℝ) := by
            gcongr
            exact hTx k
        _ = 2 * (|A k| / (k:ℝ)) := by ring
    rw [hs0.tsum_eq_zero_add]
    unfold barrierTrialT
    rw [← tsum_mul_left]
    simp only [Nat.cast_zero, div_zero, zero_add]
    congr 1
    funext n
    ring
  rw [htail] at hlim
  linarith only [hlim]

end
end CatalanMeasure.GenD.Signed.RouteI.CompletedGas





namespace CatalanMeasure.GenD.Signed.RouteI.CompletedGas

open Filter Set MeasureTheory OAI.InternalCatalan Topology
open scoped BigOperators

noncomputable section

local notation "Tc" k => (Polynomial.Chebyshev.T ℝ ((k : ℕ) : ℤ))

open CapFields CapFields.YCell

theorem physX_neg_arg {Y : ℝ} (hY : Y < 0) : physX Y = -physX (-Y) := by
  have h1 : ¬ 0 ≤ Y := not_le.mpr hY
  have h2 : 0 ≤ -Y := by linarith
  unfold physX
  rw [if_neg h1, if_pos h2]
  simp

theorem physX_spec_pos {Y : ℝ} (h : 2 ≤ Y) :
    0 < physX Y ∧ physX Y ≤ 1 ∧ physX Y + 1 / physX Y = Y := by
  have hY : 0 ≤ Y := by linarith
  have hr0 : 0 ≤ √(Y^2-4) := Real.sqrt_nonneg _
  have hr2 : √(Y^2-4)^2 = Y^2-4 := Real.sq_sqrt (by nlinarith)
  set r := √(Y^2-4)
  have hs : 0 < Y + r := by linarith
  have ht : physX Y = 2 / (Y + r) := by
    unfold physX
    rw [if_pos hY]
  rw [ht]
  refine ⟨by positivity, ?_, ?_⟩
  · rw [div_le_one hs]; linarith
  · field_simp
    nlinarith

theorem physX_spec_neg {Y : ℝ} (h : Y ≤ -2) :
    physX Y < 0 ∧ -1 ≤ physX Y ∧ physX Y + 1 / physX Y = Y := by
  obtain ⟨h1, h2, h3⟩ := physX_spec_pos (Y := -Y) (by linarith)
  rw [physX_neg_arg (by linarith : Y < 0)]
  refine ⟨by linarith, by linarith, ?_⟩
  have : -physX (-Y) + 1 / -physX (-Y) = -(physX (-Y) + 1 / physX (-Y)) := by
    rw [one_div, one_div, inv_neg]; ring
  rw [this, h3]; ring

theorem physX_of_pos {t : ℝ} (h0 : 0 < t) (h1 : t ≤ 1) : physX (t + 1 / t) = t := by
  have hY : 0 ≤ t + 1 / t := by positivity
  have hq : 1 ≤ 1 / t := (one_le_div h0).mpr h1
  have hs : √((t + 1 / t)^2 - 4) = 1 / t - t := by
    have : (t + 1 / t)^2 - 4 = (1 / t - t)^2 := by
      field_simp
      ring
    rw [this]
    exact Real.sqrt_sq (by linarith)
  unfold physX
  rw [if_pos hY, hs]
  field_simp
  ring

theorem physX_of_neg {t : ℝ} (h0 : t < 0) (h1 : -1 ≤ t) : physX (t + 1 / t) = t := by
  have hp := physX_of_pos (t := -t) (by linarith) (by linarith)
  have hneg : t + 1 / t < 0 := by
    have : 1 / t < 0 := one_div_neg.mpr h0
    linarith
  rw [physX_neg_arg hneg]
  have e : -(t + 1 / t) = -t + 1 / -t := by
    rw [one_div, one_div, inv_neg]; ring
  rw [e, hp]; ring

theorem physX_continuousOn_pos : ContinuousOn physX (Ici 2) := by
  have h : ContinuousOn (fun Y : ℝ => 2 / (Y + √(Y^2-4))) (Ici 2) := by
    apply ContinuousOn.div continuousOn_const (by fun_prop)
    intro Y hY
    have : (2:ℝ) ≤ Y := hY
    have := Real.sqrt_nonneg (Y^2-4)
    linarith
  refine h.congr fun Y hY => ?_
  have : (0:ℝ) ≤ Y := le_trans (by norm_num) hY
  simp only [physX, if_pos this]

theorem physX_continuousOn_neg : ContinuousOn physX (Iic (-2)) := by
  have h : ContinuousOn (fun Y : ℝ => -physX (-Y)) (Iic (-2)) := by
    apply ContinuousOn.neg
    apply physX_continuousOn_pos.comp continuousOn_neg
    intro Y hY
    have : Y ≤ -2 := hY
    simp only [mem_Ici]
    linarith
  refine h.congr fun Y hY => ?_
  have : Y ≤ -2 := hY
  exact physX_neg_arg (by linarith)

theorem physX_measurable : Measurable physX := by
  unfold physX
  refine Measurable.ite measurableSet_Ici ?_ ?_ <;> fun_prop

/-- A row cell lies on one side of `[-2,2]`. -/
def RowCell (c : YCell) : Prop := 2 ≤ c.lo ∨ c.hi ≤ -2

/-- The inverse branch on the side of the cell, as one statement for both signs. -/
theorem physX_mem {c : YCell} (hc : RowCell c) {Y : ℝ} (hY : Y ∈ Icc c.lo c.hi) :
    physX Y ≠ 0 ∧ |physX Y| ≤ 1 ∧ physX Y + 1 / physX Y = Y := by
  rcases hc with h | h
  · obtain ⟨h1, h2, h3⟩ := physX_spec_pos (h.trans hY.1)
    exact ⟨h1.ne', by rw [abs_of_pos h1]; exact h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := physX_spec_neg (hY.2.trans h)
    exact ⟨h1.ne, by rw [abs_of_neg h1]; linarith, h3⟩

/-- The derivative of `Y(t)=t+1/t`. -/
def yDer (t : ℝ) : ℝ := 1 - 1 / t^2

theorem yDer_hasDeriv {t : ℝ} (ht : t ≠ 0) : HasDerivAt (fun t : ℝ => t + 1 / t) (yDer t) t := by
  have h := (hasDerivAt_id' t).fun_add (hasDerivAt_inv ht)
  have e : (fun t : ℝ => t + 1 / t) = fun t => t + t⁻¹ := by
    funext u
    rw [one_div]
  rw [e]
  unfold yDer
  convert h using 1
  rw [one_div]
  ring

theorem yDer_hasDeriv2 {t : ℝ} (ht : t ≠ 0) : HasDerivAt yDer (2 / t^3) t := by
  have h := ((hasDerivAt_inv ht).fun_pow 2).const_sub 1
  have e : yDer = fun u : ℝ => 1 - (u⁻¹)^2 := by
    funext u
    unfold yDer
    rw [inv_pow, one_div]
  rw [e]
  convert h using 1
  simp only [Nat.cast_ofNat, Nat.add_one_sub_one, show (2:ℕ) - 1 = 1 from rfl, pow_one]
  field_simp

/-- Change of variable from `Y` to `t = X(Y)` on one cell, with the nonsingular map `t ↦ t+1/t`:
the square-root endpoint of `X` never appears. -/
theorem cell_change_of_variable {c : YCell} (hc : RowCell c) {F : ℝ → ℝ} (hF : Continuous F) :
    ∫ Y in c.lo..c.hi, F (physX Y) =
      ∫ t in physX c.lo..physX c.hi, F t * yDer t := by
  have hlo := physX_mem hc (left_mem_Icc.mpr c.lo_lt.le)
  have hhi := physX_mem hc (right_mem_Icc.mpr c.lo_lt.le)
  rcases hc with h | h
  · obtain ⟨a0, a1, a2⟩ := physX_spec_pos h
    obtain ⟨b0, b1, b2⟩ := physX_spec_pos (h.trans c.lo_lt.le)
    have hI : ∀ t ∈ uIcc (physX c.lo) (physX c.hi), 0 < t ∧ t ≤ 1 := fun t ht => by
      have h1 : min (physX c.lo) (physX c.hi) ≤ t := ht.1
      have h2 : t ≤ max (physX c.lo) (physX c.hi) := ht.2
      exact ⟨lt_of_lt_of_le (lt_min a0 b0) h1, h2.trans (max_le a1 b1)⟩
    have key := intervalIntegral.integral_comp_mul_deriv'
      (a := physX c.lo) (b := physX c.hi) (f := fun t => t + 1 / t) (f' := yDer)
      (g := fun Y => F (physX Y))
      (fun t ht => by
        have ht0 := (hI t ht).1.ne'
        exact yDer_hasDeriv ht0)
      (by
        apply ContinuousOn.sub continuousOn_const
        apply ContinuousOn.div continuousOn_const (by fun_prop)
        intro t ht
        exact pow_ne_zero 2 (hI t ht).1.ne')
      (by
        apply hF.comp_continuousOn
        apply physX_continuousOn_pos.mono
        rintro _ ⟨t, ht, rfl⟩
        obtain ⟨t0, t1⟩ := hI t ht
        have : 2 ≤ t + 1 / t := by
          have h3 : t + 1 / t - 2 = (1 - t)^2 / t := by field_simp; ring
          have h4 : 0 ≤ (1 - t)^2 / t := by positivity
          linarith
        exact this)
    simp only [a2, b2] at key
    rw [← key]
    apply intervalIntegral.integral_congr
    intro t ht
    simp only [Function.comp, physX_of_pos (hI t ht).1 (hI t ht).2]
  · have hlo' : c.lo ≤ -2 := c.lo_lt.le.trans h
    obtain ⟨a0, a1, a2⟩ := physX_spec_neg hlo'
    obtain ⟨b0, b1, b2⟩ := physX_spec_neg h
    have hI : ∀ t ∈ uIcc (physX c.lo) (physX c.hi), t < 0 ∧ -1 ≤ t := fun t ht => by
      have h1 : min (physX c.lo) (physX c.hi) ≤ t := ht.1
      have h2 : t ≤ max (physX c.lo) (physX c.hi) := ht.2
      exact ⟨lt_of_le_of_lt h2 (max_lt a0 b0), (le_min a1 b1).trans h1⟩
    have key := intervalIntegral.integral_comp_mul_deriv'
      (a := physX c.lo) (b := physX c.hi) (f := fun t => t + 1 / t) (f' := yDer)
      (g := fun Y => F (physX Y))
      (fun t ht => by
        have ht0 := (hI t ht).1.ne
        exact yDer_hasDeriv ht0)
      (by
        apply ContinuousOn.sub continuousOn_const
        apply ContinuousOn.div continuousOn_const (by fun_prop)
        intro t ht
        exact pow_ne_zero 2 (hI t ht).1.ne)
      (by
        apply hF.comp_continuousOn
        apply physX_continuousOn_neg.mono
        rintro _ ⟨t, ht, rfl⟩
        obtain ⟨t0, t1⟩ := hI t ht
        have : t + 1 / t ≤ -2 := by
          have tn := t0.ne
          have h3 : t + 1 / t + 2 = (1 + t)^2 / t := by field_simp; ring
          have h4 : (1 + t)^2 / t ≤ 0 := div_nonpos_of_nonneg_of_nonpos (by positivity) t0.le
          linarith
        exact this)
    simp only [a2, b2] at key
    rw [← key]
    apply intervalIntegral.integral_congr
    intro t ht
    simp only [Function.comp, physX_of_neg (hI t ht).1 (hI t ht).2]

/-- **Primitive bound on one cell.** Any continuous function with a primitive bounded by `B` on
`[-1,1]` integrates to `O(B)` against the cell, with a constant depending only on the cell. -/
theorem cell_primitive_bound {c : YCell} (hc : RowCell c) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (F G : ℝ → ℝ) (B : ℝ), Continuous F → (∀ t, HasDerivAt G (F t) t) →
      (∀ t ∈ Icc (-1:ℝ) 1, |G t| ≤ B) →
      |∫ Y in c.lo..c.hi, F (physX Y)| ≤ B * K := by
  set a := physX c.lo with ha
  set b := physX c.hi with hb
  have hlo := physX_mem hc (left_mem_Icc.mpr c.lo_lt.le)
  have hhi := physX_mem hc (right_mem_Icc.mpr c.lo_lt.le)
  have hI : ∀ t ∈ uIcc a b, t ≠ 0 ∧ t ∈ Icc (-1:ℝ) 1 := fun t ht => by
    have h1 : min a b ≤ t := ht.1
    have h2 : t ≤ max a b := ht.2
    rcases hc with h | h
    · obtain ⟨a0, a1, -⟩ := physX_spec_pos h
      obtain ⟨b0, b1, -⟩ := physX_spec_pos (h.trans c.lo_lt.le)
      have h3 : 0 < t := lt_of_lt_of_le (lt_min a0 b0) h1
      exact ⟨h3.ne', by linarith, h2.trans (max_le a1 b1)⟩
    · obtain ⟨a0, a1, -⟩ := physX_spec_neg (c.lo_lt.le.trans h)
      obtain ⟨b0, b1, -⟩ := physX_spec_neg h
      have h3 : t < 0 := lt_of_le_of_lt h2 (max_lt a0 b0)
      exact ⟨h3.ne, (le_min a1 b1).trans h1, by linarith⟩
  let d : ℝ → ℝ := fun t => 2 / t^3
  have hdc : ContinuousOn d (uIcc a b) := by
    apply ContinuousOn.div continuousOn_const (by fun_prop)
    intro t ht
    exact pow_ne_zero 3 (hI t ht).1
  have hyc : ContinuousOn yDer (uIcc a b) := by
    apply ContinuousOn.sub continuousOn_const
    apply ContinuousOn.div continuousOn_const (by fun_prop)
    intro t ht
    exact pow_ne_zero 2 (hI t ht).1
  obtain ⟨D, hD⟩ := isCompact_uIcc.exists_bound_of_continuousOn hdc
  have hD0 : 0 ≤ D := (norm_nonneg _).trans (hD a left_mem_uIcc)
  refine ⟨|yDer a| + |yDer b| + D * |b - a|, by positivity, ?_⟩
  intro F G B hF hG hB
  rw [cell_change_of_variable hc hF]
  have hder : ∀ t ∈ uIcc a b, HasDerivAt yDer (d t) t := fun t ht => by
    have ht0 := (hI t ht).1
    exact yDer_hasDeriv2 ht0
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := a) (b := b)
    (u := yDer) (v := G) (u' := d) (v' := F) hder (fun t _ => hG t)
    hdc.intervalIntegrable (hF.intervalIntegrable _ _)
  have hcomm : ∫ t in a..b, F t * yDer t = ∫ t in a..b, yDer t * F t := by
    apply intervalIntegral.integral_congr
    intro t _
    exact mul_comm _ _
  rw [hcomm, hibp]
  have hGa := hB a (hI a left_mem_uIcc).2
  have hGb := hB b (hI b right_mem_uIcc).2
  have hB0 : 0 ≤ B := (abs_nonneg _).trans hGa
  have hint : |∫ t in a..b, d t * G t| ≤ B * D * |b - a| := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b)
      (f := fun t => d t * G t) (C := B * D) (fun t ht => by
        have ht' : t ∈ uIcc a b := uIoc_subset_uIcc ht
        rw [norm_mul, Real.norm_eq_abs (G t), mul_comm]
        exact mul_le_mul (hB t (hI t ht').2) (hD t ht') (norm_nonneg _) hB0)
    simpa [Real.norm_eq_abs] using this
  have e1 : |yDer b * G b| ≤ B * |yDer b| := by
    rw [abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right hGb (abs_nonneg _)
  have e2 : |yDer a * G a| ≤ B * |yDer a| := by
    rw [abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right hGa (abs_nonneg _)
  calc |yDer b * G b - yDer a * G a - ∫ t in a..b, d t * G t|
      ≤ |yDer b * G b| + |yDer a * G a| + |∫ t in a..b, d t * G t| := by
        refine (abs_sub _ _).trans ?_
        gcongr
        exact abs_sub _ _
    _ ≤ B * (|yDer a| + |yDer b| + D * |b - a|) := by nlinarith

/-- The Chebyshev primitive. -/
def chebPrim (n : ℕ) (t : ℝ) : ℝ :=
  ((Tc (n+3)).eval t / ((n:ℝ)+3) - (Tc (n+1)).eval t / ((n:ℝ)+1)) / 2

theorem chebPrim_hasDeriv (n : ℕ) (t : ℝ) :
    HasDerivAt (chebPrim n) ((Tc (n+2)).eval t) t := by
  have hd : ∀ m : ℕ, HasDerivAt (fun t => (Tc (m+1)).eval t)
      (((m:ℝ)+1) * (Polynomial.Chebyshev.U ℝ (m:ℤ)).eval t) t := fun m => by
    have h := (Polynomial.Chebyshev.T ℝ ((m+1:ℕ):ℤ)).hasDerivAt t
    rw [Polynomial.Chebyshev.T_derivative_eq_U] at h
    convert h using 1
    push_cast
    simp
  have h3 := hd (n+2)
  have h1 := hd n
  have hU := congrArg (Polynomial.eval t) (Polynomial.Chebyshev.two_mul_T_eq_U_sub_U ℝ (n:ℤ))
  have hn1 : ((n:ℝ)+1) ≠ 0 := by positivity
  have hn3 : ((n:ℝ)+3) ≠ 0 := by positivity
  have := ((h3.div_const ((n:ℝ)+3)).sub (h1.div_const ((n:ℝ)+1))).div_const 2
  unfold chebPrim
  convert this using 1
  have e2 : ((n+2:ℕ):ℝ) + 1 = (n:ℝ) + 3 := by push_cast; ring
  rw [e2]
  simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_ofNat] at hU
  have c1 : (((n+2:ℕ):ℤ)) = (n:ℤ) + 2 := by push_cast; ring
  rw [c1]
  field_simp
  linarith only [hU]

theorem chebPrim_abs_le (n : ℕ) {t : ℝ} (ht : t ∈ Icc (-1:ℝ) 1) :
    |chebPrim n t| ≤ 1 / ((n:ℝ)+1) := by
  have h3 : |(Tc (n+3)).eval t| ≤ 1 :=
    Polynomial.Chebyshev.abs_eval_T_real_le_one _ (abs_le.mpr ht)
  have h1 : |(Tc (n+1)).eval t| ≤ 1 :=
    Polynomial.Chebyshev.abs_eval_T_real_le_one _ (abs_le.mpr ht)
  have hn1 : (0:ℝ) < (n:ℝ)+1 := by positivity
  have hn3 : (0:ℝ) < (n:ℝ)+3 := by positivity
  have q : 1 / ((n:ℝ)+3) ≤ 1 / ((n:ℝ)+1) :=
    one_div_le_one_div_of_le hn1 (by linarith)
  have e3 : |(Tc (n+3)).eval t / ((n:ℝ)+3)| ≤ 1 / ((n:ℝ)+1) := by
    rw [abs_div, abs_of_pos hn3]
    exact (div_le_div_of_nonneg_right h3 hn3.le).trans q
  have e1 : |(Tc (n+1)).eval t / ((n:ℝ)+1)| ≤ 1 / ((n:ℝ)+1) := by
    rw [abs_div, abs_of_pos hn1]
    exact div_le_div_of_nonneg_right h1 hn1.le
  unfold chebPrim
  rw [abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2)]
  have := abs_sub (((Tc (n+3)).eval t / ((n:ℝ)+3))) (((Tc (n+1)).eval t / ((n:ℝ)+1)))
  rw [div_le_iff₀ (by norm_num)]
  linarith

/-- `T_k` has a primitive bounded by `2/k` on `[-1,1]`, for every `k ≠ 0`. -/
theorem cheb_primitive (k : ℕ) (hk : k ≠ 0) :
    ∃ G : ℝ → ℝ, (∀ t, HasDerivAt G ((Tc k).eval t) t) ∧
      ∀ t ∈ Icc (-1:ℝ) 1, |G t| ≤ 2 / (k:ℝ) := by
  rcases k with _ | _ | n
  · exact (hk rfl).elim
  · refine ⟨fun t => t^2/2, fun t => ?_, fun t ht => ?_⟩
    · have : (Tc (0+1)).eval t = t := by simp
      rw [this]
      have := (hasDerivAt_pow 2 t).div_const 2
      convert this using 1
      simp
    · have h1 : t^2 ≤ 1 := by nlinarith [ht.1, ht.2]
      rw [abs_of_nonneg (by positivity)]
      norm_num
      linarith
  · refine ⟨chebPrim n, chebPrim_hasDeriv n, fun t ht => (chebPrim_abs_le n ht).trans ?_⟩
    push_cast
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : (0:ℝ) ≤ n := Nat.cast_nonneg n
    linarith

/-- `t^k` has a primitive bounded by `1/k`. -/
theorem pow_primitive (k : ℕ) (hk : k ≠ 0) :
    ∃ G : ℝ → ℝ, (∀ t, HasDerivAt G (t^k) t) ∧ ∀ t ∈ Icc (-1:ℝ) 1, |G t| ≤ 2 / (k:ℝ) := by
  have hk0 : (0:ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
  refine ⟨fun t => t^(k+1)/((k:ℝ)+1), fun t => ?_, fun t ht => ?_⟩
  · have := (hasDerivAt_pow (k+1) t).div_const ((k:ℝ)+1)
    convert this using 1
    have : ((k:ℝ)+1) ≠ 0 := by positivity
    push_cast
    field_simp
  · have h1 : |t|^(k+1) ≤ 1 := pow_le_one₀ (abs_nonneg t) (abs_le.mpr ht)
    rw [abs_div, abs_pow, abs_of_pos (by positivity : (0:ℝ) < (k:ℝ)+1)]
    calc |t|^(k+1)/((k:ℝ)+1) ≤ 1/((k:ℝ)+1) := by gcongr
      _ ≤ 2/(k:ℝ) := by
        rw [div_le_div_iff₀ (by positivity) hk0]
        linarith

end
end CatalanMeasure.GenD.Signed.RouteI.CompletedGas




namespace CatalanMeasure.GenD.Signed.RouteI.CompletedGas

open Filter Set MeasureTheory OAI.InternalCatalan Topology
open scoped BigOperators
open CapFields CapFields.YCell

noncomputable section

local notation "Tc" k => (Polynomial.Chebyshev.T ℝ ((k : ℕ) : ℤ))

/-- The measure of one cell. -/
def cellM (c : YCell) : Measure ℝ :=
  ENNReal.ofReal (c.w / (c.hi - c.lo)) • volume.restrict (Ioc c.lo c.hi)

instance (c : YCell) : IsFiniteMeasure (cellM c) := by
  unfold cellM
  exact Measure.smul_finite _ ENNReal.ofReal_ne_top

theorem cell_scale_nonneg (c : YCell) : 0 ≤ c.w / (c.hi - c.lo) :=
  div_nonneg c.w_nonneg (sub_pos.mpr c.lo_lt).le

theorem cell_avg_eq (c : YCell) (f : ℝ → ℝ) : c.avg f = ∫ y, f y ∂cellM c := by
  unfold YCell.avg cellM
  rw [integral_smul_measure, ENNReal.toReal_ofReal (cell_scale_nonneg c),
    intervalIntegral.integral_of_le c.lo_lt.le, smul_eq_mul]

theorem cellM_real_univ (c : YCell) : (cellM c).real univ = c.w := by
  have h := cell_avg_eq c (fun _ => 1)
  rw [integral_const, smul_eq_mul, mul_one] at h
  rw [← h]
  unfold YCell.avg
  have : c.hi - c.lo ≠ 0 := (sub_pos.mpr c.lo_lt).ne'
  simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one]
  field_simp

theorem cell_ae_mem (c : YCell) : ∀ᵐ y ∂cellM c, y ∈ Icc c.lo c.hi := by
  unfold cellM
  apply Measure.ae_smul_measure
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
  exact ⟨hy.1.le, hy.2⟩

theorem cell_ac (c : YCell) : cellM c ≪ volume := by
  unfold cellM
  exact (Measure.absolutelyContinuous_of_le Measure.restrict_le_self).smul_left _

theorem cell_ae_ne (c : YCell) (a : ℝ) : ∀ᵐ y ∂cellM c, y ≠ a := by
  apply (cell_ac c).ae_le
  have h := measure_eq_zero_iff_ae_notMem.mp (measure_singleton (μ := (volume : Measure ℝ)) a)
  filter_upwards [h] with y hy
  simpa using hy

theorem cell_integrable_of_continuousOn (c : YCell) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc c.lo c.hi)) : Integrable f (cellM c) := by
  unfold cellM
  apply Integrable.smul_measure _ ENNReal.ofReal_ne_top
  exact (hf.integrableOn_Icc).mono_set Ioc_subset_Icc_self

theorem cell_integrable_log (c : YCell) (a : ℝ) :
    Integrable (fun Y => Real.log |a - Y|) (cellM c) := by
  unfold cellM
  apply Integrable.smul_measure _ ENNReal.ofReal_ne_top
  have h := (intervalIntegral.intervalIntegrable_log' (a := a - c.lo) (b := a - c.hi)).comp_sub_left a
  simp only [sub_sub_cancel] at h
  have h2 : IntegrableOn (fun Y => Real.log (a - Y)) (Ioc c.lo c.hi) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le c.lo_lt.le).mp h
  have e : (fun Y => Real.log |a - Y|) = fun Y => Real.log (a - Y) := by
    funext Y
    rw [Real.log_abs]
  rw [e]
  exact h2

theorem physX_continuousOn_cell {c : YCell} (hc : RowCell c) :
    ContinuousOn physX (Icc c.lo c.hi) := by
  rcases hc with h | h
  · exact physX_continuousOn_pos.mono fun Y hY => h.trans hY.1
  · exact physX_continuousOn_neg.mono fun Y hY => hY.2.trans h

/-- The Chebyshev kernel identity behind `(R)`. -/
theorem row_kernel {x t : ℝ} (hx : x ≠ 0) (ht : t ≠ 0) (hxt : x ≠ t) (h1 : 1 - x * t ≠ 0) :
    Real.log |(x + 1 / x) - (t + 1 / t)| + Real.log |t| =
      Real.log |x - t| + Real.log |1 - x * t| - Real.log |x| := by
  have e : (x + 1 / x) - (t + 1 / t) = -((x - t) * (1 - x * t) / (x * t)) := by
    field_simp
    ring
  have hxt' : x - t ≠ 0 := sub_ne_zero.mpr hxt
  rw [e, abs_neg, abs_div, abs_mul, abs_mul,
    Real.log_div (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity)]
  ring

theorem cross_abs_kernel {x s : ℝ} (hx : x ≠ 0) (h1 : 1 - 2 * x * s + x^2 ≠ 0) :
    Real.log |(x + 1 / x) - 2 * s| = Real.log |1 - 2 * x * s + x^2| - Real.log |x| := by
  have e : (x + 1 / x) - 2 * s = (1 - 2 * x * s + x^2) / x := by
    field_simp
    ring
  rw [e, abs_div, Real.log_div (by positivity) (by positivity)]

theorem abs_mul_lt_one {x t : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) (ht : |t| ≤ 1) : |x * t| < 1 := by
  rw [abs_mul]
  have h1 : |x| < 1 := abs_lt.mpr hx
  calc |x| * |t| ≤ |x| * 1 := by gcongr
    _ < 1 := by linarith

theorem one_sub_mul_ne {x t : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) (ht : |t| ≤ 1) : 1 - x * t ≠ 0 := by
  have := abs_lt.mp (abs_mul_lt_one hx ht)
  linarith [this.2]

/-- Row-side cell identity before the series: the singular logarithm is integrable and the
cell's `log|t|` and `Y`-potential recombine into the two `t`-logarithms. -/
theorem cell_row_recombine {c : YCell} (hc : RowCell c) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1)
    (hx0 : x ≠ 0) :
    Integrable (fun Y => Real.log |x - physX Y|) (cellM c) ∧
    c.phys (fun u => Real.log |u|) + c.pot (x + 1 / x) =
      (∫ Y, Real.log |x - physX Y| ∂cellM c) + (∫ Y, Real.log |1 - x * physX Y| ∂cellM c) -
        c.w * Real.log |x| := by
  have hcont := physX_continuousOn_cell hc
  have i1 := cell_integrable_log c (x + 1 / x)
  have i2 : Integrable (fun Y => Real.log |physX Y|) (cellM c) := by
    apply cell_integrable_of_continuousOn
    apply ContinuousOn.log hcont.abs
    intro Y hY
    exact abs_ne_zero.mpr (physX_mem hc hY).1
  have i3 : Integrable (fun Y => Real.log |1 - x * physX Y|) (cellM c) := by
    apply cell_integrable_of_continuousOn
    apply ContinuousOn.log (ContinuousOn.abs (continuousOn_const.sub (continuousOn_const.mul hcont)))
    intro Y hY
    exact abs_ne_zero.mpr (one_sub_mul_ne hx (physX_mem hc hY).2.1)
  have hae : ∀ᵐ Y ∂cellM c, Real.log |x - physX Y| =
      Real.log |(x + 1 / x) - Y| + Real.log |physX Y| - Real.log |1 - x * physX Y| +
        Real.log |x| := by
    filter_upwards [cell_ae_mem c, cell_ae_ne c (x + 1 / x)] with Y hY hne
    obtain ⟨h0, h1, h2⟩ := physX_mem hc hY
    have hxt : x ≠ physX Y := by
      intro h
      apply hne
      rw [← h2, ← h]
    have := row_kernel hx0 h0 hxt (one_sub_mul_ne hx h1)
    rw [h2] at this
    linarith only [this]
  have i4 : Integrable (fun Y => Real.log |x - physX Y|) (cellM c) :=
    (((i1.add i2).sub i3).add (integrable_const (Real.log |x|))).congr
      (by filter_upwards [hae] with Y hY; simp [hY])
  refine ⟨i4, ?_⟩
  have h4 := integral_congr_ae hae
  have hcalc : (∫ Y, (Real.log |(x + 1 / x) - Y| + Real.log |physX Y| -
      Real.log |1 - x * physX Y| + Real.log |x|) ∂cellM c) =
      (∫ Y, Real.log |(x + 1 / x) - Y| ∂cellM c) + (∫ Y, Real.log |physX Y| ∂cellM c) -
        (∫ Y, Real.log |1 - x * physX Y| ∂cellM c) + c.w * Real.log |x| := by
    have a1 := integral_add (μ := cellM c)
      (f := fun Y => Real.log |(x + 1 / x) - Y| + Real.log |physX Y| -
        Real.log |1 - x * physX Y|) (g := fun _ => Real.log |x|)
      ((i1.add i2).sub i3) (integrable_const _)
    have a2 := integral_sub (μ := cellM c)
      (f := fun Y => Real.log |(x + 1 / x) - Y| + Real.log |physX Y|)
      (g := fun Y => Real.log |1 - x * physX Y|) (i1.add i2) i3
    have a3 := integral_add (μ := cellM c)
      (f := fun Y => Real.log |(x + 1 / x) - Y|) (g := fun Y => Real.log |physX Y|) i1 i2
    rw [a1, a2, a3, integral_const, smul_eq_mul, cellM_real_univ]
  rw [hcalc] at h4
  unfold YCell.phys YCell.pot
  rw [cell_avg_eq, cell_avg_eq]
  linarith only [h4]

/-- A geometric-majorant series integrates termwise on a finite measure. -/
theorem hasSum_integral_geometric {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] (F : ℕ → α → ℝ) (f : α → ℝ) {ρ K : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hm : ∀ n, AEStronglyMeasurable (F n) μ)
    (hb : ∀ n, ∀ᵐ a ∂μ, ‖F n a‖ ≤ K * ρ^n)
    (hl : ∀ᵐ a ∂μ, HasSum (fun n => F n a) (f a)) :
    HasSum (fun n => ∫ a, F n a ∂μ) (∫ a, f a ∂μ) :=
  hasSum_integral_of_dominated_convergence (fun n _ => K * ρ^n) hm hb
    (Eventually.of_forall fun _ => (summable_geometric_of_lt_one hρ0 hρ1).mul_left K)
    (integrable_const _) hl

theorem cheb_measurable (k : ℕ) : Measurable fun t : ℝ => (Tc k).eval t :=
  (chebT_measurable k).measurable

/-- The reflection logarithm of one cell is the power-moment series. -/
theorem cell_reflection {c : YCell} (hc : RowCell c) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    HasSum (fun n : ℕ => (c.phys fun u => u^(n+1)) * x^(n+1) / ((n+1:ℕ):ℝ))
      (-∫ Y, Real.log |1 - x * physX Y| ∂cellM c) := by
  have hx1 : |x| < 1 := abs_lt.mpr hx
  have h := hasSum_integral_geometric (cellM c)
    (fun n Y => (x * physX Y)^(n+1) / ((n+1:ℕ):ℝ))
    (fun Y => -Real.log |1 - x * physX Y|) (ρ := |x|) (K := 1) (abs_nonneg x) hx1
    (fun n => by
      have : Measurable fun Y => (x * physX Y)^(n+1) / ((n+1:ℕ):ℝ) :=
        ((physX_measurable.const_mul x).pow_const _).div_const _
      exact this.aestronglyMeasurable)
    (fun n => by
      filter_upwards [cell_ae_mem c] with Y hY
      have ht := (physX_mem hc hY).2.1
      have hk : (1:ℝ) ≤ ((n+1:ℕ):ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
      rw [Real.norm_eq_abs, abs_div, abs_pow, abs_mul, Nat.abs_cast, one_mul]
      have h1 : (|x| * |physX Y|)^(n+1) ≤ |x|^(n+1) := by
        gcongr
        calc |x| * |physX Y| ≤ |x| * 1 := by gcongr
          _ = |x| := mul_one _
      have h2 : |x|^(n+1) ≤ |x|^n := pow_le_pow_of_le_one (abs_nonneg x) hx1.le (Nat.le_succ n)
      calc (|x| * |physX Y|)^(n+1) / ((n+1:ℕ):ℝ) ≤ (|x| * |physX Y|)^(n+1) :=
            div_le_self (by positivity) hk
        _ ≤ |x|^n := h1.trans h2)
    (by
      filter_upwards [cell_ae_mem c] with Y hY
      have ht := (physX_mem hc hY).2.1
      have h3 := Real.hasSum_pow_div_log_of_abs_lt_one (abs_mul_lt_one hx ht)
      rw [Real.log_abs]
      convert h3 using 2
      push_cast
      ring_nf)
  rw [integral_neg] at h
  convert h using 2 with n
  unfold YCell.phys
  rw [cell_avg_eq]
  have : (fun Y => (x * physX Y)^(n+1) / ((n+1:ℕ):ℝ)) =
      fun Y => (x^(n+1) / ((n+1:ℕ):ℝ)) * physX Y^(n+1) := by
    funext Y
    rw [mul_pow]
    ring
  rw [this, integral_const_mul]
  ring

/-- Column cells lie in `[-1,1]`. -/
def ColCell (c : YCell) : Prop := -1 ≤ c.lo ∧ c.hi ≤ 1

theorem dil2_pot (c : YCell) (y : ℝ) :
    (dil2 c).pot y = c.avg fun s => Real.log |y - 2 * s| := by
  unfold YCell.pot YCell.avg dil2
  have h := intervalIntegral.integral_comp_mul_left (a := c.lo) (b := c.hi)
    (fun u => Real.log |y - u|) (c := 2) (by norm_num)
  simp only [smul_eq_mul] at h
  have hd : c.hi - c.lo ≠ 0 := (sub_pos.mpr c.lo_lt).ne'
  simp only
  rw [h]
  have : 2 * c.hi - 2 * c.lo = 2 * (c.hi - c.lo) := by ring
  rw [this]
  field_simp

theorem cross_pos' {x s : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) (hs : s ∈ Icc (-1:ℝ) 1) :
    0 < 1 - 2 * x * s + x^2 := by
  have h1 : |x| < 1 := abs_lt.mpr hx
  have h2 : |x * s| ≤ |x| := by
    rw [abs_mul]
    calc |x| * |s| ≤ |x| * 1 := by gcongr; exact abs_le.mpr hs
      _ = |x| := mul_one _
  have h3 := (abs_le.mp h2).2
  have h4 := sq_abs x
  nlinarith [abs_nonneg x, le_abs_self (x * s)]

/-- The doubled column cell at the point `Y(x)`. -/
theorem cell_cross {c : YCell} (hc : ColCell c) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) (hx0 : x ≠ 0) :
    HasSum (fun n : ℕ => 2 * (c.avg fun s => (Tc (n+1)).eval s) * x^(n+1) / ((n+1:ℕ):ℝ))
      (-((dil2 c).pot (x + 1 / x)) - c.w * Real.log |x|) := by
  have hx1 : |x| < 1 := abs_lt.mpr hx
  have hmem : ∀ᵐ s ∂cellM c, s ∈ Icc (-1:ℝ) 1 := by
    filter_upwards [cell_ae_mem c] with s hs
    exact ⟨hc.1.trans hs.1, hs.2.trans hc.2⟩
  have h := hasSum_integral_geometric (cellM c)
    (fun n s => 2 * x^(n+1) * (Tc (n+1)).eval s / ((n+1:ℕ):ℝ))
    (fun s => -Real.log (1 - 2 * x * s + x^2)) (ρ := |x|) (K := 2) (abs_nonneg x) hx1
    (fun n => by
      have : Measurable fun s => 2 * x^(n+1) * (Tc (n+1)).eval s / ((n+1:ℕ):ℝ) :=
        ((cheb_measurable (n+1)).const_mul _).div_const _
      exact this.aestronglyMeasurable)
    (fun n => by
      filter_upwards [hmem] with s hs
      have hT : |(Tc (n+1)).eval s| ≤ 1 :=
        Polynomial.Chebyshev.abs_eval_T_real_le_one _ (abs_le.mpr hs)
      have hk : (1:ℝ) ≤ ((n+1:ℕ):ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
      have h2 : |x|^(n+1) ≤ |x|^n := pow_le_pow_of_le_one (abs_nonneg x) hx1.le (Nat.le_succ n)
      rw [Real.norm_eq_abs, abs_div, abs_mul, abs_mul, abs_pow, Nat.abs_cast,
        abs_of_pos (by norm_num : (0:ℝ) < 2)]
      calc 2 * |x|^(n+1) * |(Tc (n+1)).eval s| / ((n+1:ℕ):ℝ)
          ≤ 2 * |x|^(n+1) * |(Tc (n+1)).eval s| := div_le_self (by positivity) hk
        _ ≤ 2 * |x|^n * 1 := by gcongr
        _ = 2 * |x|^n := mul_one _)
    (by
      filter_upwards [hmem] with s hs
      have h3 := energy_hasSum_cross_kernel hx hs
      have h4 := (hasSum_nat_add_iff' 1).mpr h3
      simpa using h4)
  have ev : ∫ s, -Real.log (1 - 2 * x * s + x^2) ∂cellM c =
      -((dil2 c).pot (x + 1 / x)) - c.w * Real.log |x| := by
    rw [dil2_pot, cell_avg_eq]
    have hae : ∀ᵐ s ∂cellM c, -Real.log (1 - 2 * x * s + x^2) =
        -Real.log |(x + 1 / x) - 2 * s| - Real.log |x| := by
      filter_upwards [hmem] with s hs
      have hp := cross_pos' hx hs
      rw [cross_abs_kernel hx0 hp.ne', abs_of_pos hp]
      ring
    rw [integral_congr_ae hae]
    have i1 : Integrable (fun s => Real.log |(x + 1 / x) - 2 * s|) (cellM c) := by
      have i0 := cell_integrable_log c ((x + 1 / x) / 2)
      refine (i0.add (integrable_const (Real.log 2))).congr ?_
      filter_upwards [cell_ae_ne c ((x + 1 / x) / 2)] with s hs
      have hne : (x + 1 / x) / 2 - s ≠ 0 := sub_ne_zero.mpr hs.symm
      have e : (x + 1 / x) - 2 * s = 2 * ((x + 1 / x) / 2 - s) := by ring
      simp only [Pi.add_apply]
      rw [e, abs_mul, abs_two, Real.log_mul (by norm_num) (abs_ne_zero.mpr hne)]
      ring
    have a1 := integral_sub (μ := cellM c)
      (f := fun s => -Real.log |(x + 1 / x) - 2 * s|) (g := fun _ => Real.log |x|)
      i1.neg (integrable_const _)
    rw [a1, integral_neg, integral_const, smul_eq_mul, cellM_real_univ]
  rw [ev] at h
  convert h using 2 with n
  rw [cell_avg_eq]
  have : (fun s => 2 * x^(n+1) * (Tc (n+1)).eval s / ((n+1:ℕ):ℝ)) =
      fun s => (2 * x^(n+1) / ((n+1:ℕ):ℝ)) * (Tc (n+1)).eval s := by
    funext s
    ring
  rw [this, integral_const_mul]
  ring

end
end CatalanMeasure.GenD.Signed.RouteI.CompletedGas




namespace CatalanMeasure.GenD.Signed.RouteI.CompletedGas

open Finset MeasureTheory Complex Filter Set
open scoped BigOperators ENNReal Topology
open CapFields CapFields.YCell

noncomputable section

theorem sqrt_ball_bound {a b ρ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hρ : 0 < ρ) {m : ℝ≥0∞}
    (h1 : m ≤ ENNReal.ofReal (a * ρ)) (h2 : m ≤ ENNReal.ofReal b) :
    m ≤ ENNReal.ofReal ((a + b) * √ρ) := by
  by_cases h : ρ ≤ 1
  · refine h1.trans (ENNReal.ofReal_le_ofReal ?_)
    have h3 : ρ ≤ √ρ := (Real.le_sqrt' hρ).mpr (by nlinarith)
    have : 0 ≤ b * √ρ := by positivity
    nlinarith
  · refine h2.trans (ENNReal.ofReal_le_ofReal ?_)
    have h3 : 1 ≤ √ρ := by
      rw [Real.one_le_sqrt]
      linarith
    have : 0 ≤ a * √ρ := by positivity
    nlinarith

/-- A cell pushed by a map with Lipschitz inverse. -/
theorem cell_eucl (c : YCell) {f : ℝ → ℝ} (hf : Measurable f) {K R : ℝ} (hK : 0 ≤ K)
    (hlip : ∀ Y ∈ Icc c.lo c.hi, ∀ Y' ∈ Icc c.lo c.hi, |Y - Y'| ≤ K * |f Y - f Y'|)
    (hb : ∀ Y ∈ Icc c.lo c.hi, |f Y| ≤ R) :
    EuclBall ((cellM c).map fun Y => (f Y : ℂ)) (4 * (c.w / (c.hi - c.lo)) * K + c.w) R := by
  have hg : Measurable fun Y => (f Y : ℂ) := Complex.measurable_ofReal.comp hf
  set s := c.w / (c.hi - c.lo) with hs
  have hs0 : 0 ≤ s := cell_scale_nonneg c
  constructor
  · intro z ρ hρ
    rw [Measure.map_apply hg Metric.isClosed_closedBall.measurableSet]
    set P := (fun Y => (f Y : ℂ)) ⁻¹' Metric.closedBall z ρ with hP
    have hPm : MeasurableSet P := hg Metric.isClosed_closedBall.measurableSet
    have htot : cellM c P ≤ ENNReal.ofReal c.w := by
      have h1 : cellM c P ≤ cellM c Set.univ := measure_mono (Set.subset_univ _)
      have h2 : cellM c Set.univ = ENNReal.ofReal c.w := by
        rw [← cellM_real_univ, Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _)]
      rwa [h2] at h1
    have hlin : cellM c P ≤ ENNReal.ofReal (4 * s * K * ρ) := by
      unfold cellM
      rw [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hPm, ← hs]
      by_cases hne : (P ∩ Ioc c.lo c.hi).Nonempty
      · obtain ⟨Y₀, h₀, h₀'⟩ := hne
        have hsub : P ∩ Ioc c.lo c.hi ⊆ Icc (Y₀ - 2 * K * ρ) (Y₀ + 2 * K * ρ) := by
          rintro Y ⟨h1, h1'⟩
          have m1 : Y ∈ Icc c.lo c.hi := ⟨h1'.1.le, h1'.2⟩
          have m0 : Y₀ ∈ Icc c.lo c.hi := ⟨h₀'.1.le, h₀'.2⟩
          have d1 : ‖(f Y : ℂ) - z‖ ≤ ρ := by
            simpa [dist_eq_norm] using (Metric.mem_closedBall.mp h1)
          have d0 : ‖(f Y₀ : ℂ) - z‖ ≤ ρ := by
            simpa [dist_eq_norm] using (Metric.mem_closedBall.mp h₀)
          have d2 : |f Y - f Y₀| ≤ 2 * ρ := by
            have : ‖(f Y : ℂ) - (f Y₀ : ℂ)‖ ≤ ‖(f Y : ℂ) - z‖ + ‖(f Y₀ : ℂ) - z‖ := by
              have := norm_sub_le ((f Y : ℂ) - z) ((f Y₀ : ℂ) - z)
              simpa using this
            have e : ‖(f Y : ℂ) - (f Y₀ : ℂ)‖ = |f Y - f Y₀| := by
              rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
            rw [e] at this
            linarith
          have d3 : |Y - Y₀| ≤ 2 * K * ρ := by
            calc |Y - Y₀| ≤ K * |f Y - f Y₀| := hlip Y m1 Y₀ m0
              _ ≤ K * (2 * ρ) := by gcongr
              _ = _ := by ring
          have := abs_le.mp d3
          constructor <;> linarith [this.1, this.2]
        have hv : volume (P ∩ Ioc c.lo c.hi) ≤ ENNReal.ofReal (4 * K * ρ) := by
          refine (measure_mono hsub).trans (le_of_eq ?_)
          rw [Real.volume_Icc]
          congr 1
          ring
        calc ENNReal.ofReal s * volume (P ∩ Ioc c.lo c.hi)
            ≤ ENNReal.ofReal s * ENNReal.ofReal (4 * K * ρ) := by gcongr
          _ = _ := by
              rw [← ENNReal.ofReal_mul hs0]
              congr 1
              ring
      · rw [Set.not_nonempty_iff_eq_empty.mp hne]
        simp
    have := sqrt_ball_bound (a := 4 * s * K) (b := c.w) (by positivity) c.w_nonneg hρ hlin htot
    exact this
  · rw [ae_map_iff hg.aemeasurable (measurableSet_le measurable_norm measurable_const)]
    filter_upwards [cell_ae_mem c] with Y hY
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact hb Y hY

/-! ### Measures on circles -/

/-- A density on the angle interval. -/
def arcM (f : ℝ → ℝ) : Measure ℝ :=
  (volume.restrict (Ioc (-Real.pi) Real.pi)).withDensity fun φ => ENNReal.ofReal (f φ)

/-- The circle of radius `r`. -/
def circ (r φ : ℝ) : ℂ := (r : ℂ) * Complex.exp (φ * I)

theorem circ_continuous (r : ℝ) : Continuous (circ r) := by
  unfold circ
  fun_prop

theorem circ_norm {r : ℝ} (hr : 0 ≤ r) (φ : ℝ) : ‖circ r φ‖ = r := by
  unfold circ
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hr]

theorem circ_sub_norm {r : ℝ} (hr : 0 ≤ r) (φ φ₀ : ℝ) :
    ‖circ r φ - circ r φ₀‖ = 2 * r * |Real.sin ((φ - φ₀) / 2)| := by
  have e : circ r φ - circ r φ₀ =
      circ r φ₀ * (Complex.exp (I * ((φ - φ₀ : ℝ) : ℂ)) - 1) := by
    unfold circ
    have : Complex.exp ((φ : ℂ) * I) =
        Complex.exp ((φ₀ : ℂ) * I) * Complex.exp (I * ((φ - φ₀ : ℝ) : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [this]
    ring
  rw [e, norm_mul, circ_norm hr, Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs, abs_mul]
  norm_num
  ring

/-- Two angles of a small arc are close modulo the period. -/
theorem sin_half_small {δ a : ℝ} (hδ : |δ| < Real.pi) (ha : |Real.sin δ| ≤ 2 / Real.pi * a) :
    |δ| ≤ a ∨ Real.pi - |δ| ≤ a := by
  have hpi := Real.pi_pos
  set d := |δ| with hd
  have hd0 : 0 ≤ d := abs_nonneg _
  have hs : |Real.sin δ| = Real.sin d := by
    rcases abs_cases δ with ⟨h, _⟩ | ⟨h, _⟩
    · rw [hd, h, abs_of_nonneg]
      exact Real.sin_nonneg_of_nonneg_of_le_pi (by rw [← h]; exact hd0) (by rw [← h]; exact hδ.le)
    · rw [hd, h, Real.sin_neg, abs_of_nonpos]
      have : 0 ≤ Real.sin (-δ) :=
        Real.sin_nonneg_of_nonneg_of_le_pi (by rw [← h]; exact hd0) (by rw [← h]; exact hδ.le)
      rw [Real.sin_neg] at this
      linarith
  rw [hs] at ha
  have h2 : 0 < 2 / Real.pi := by positivity
  by_cases h : d ≤ Real.pi / 2
  · left
    have := Real.mul_le_sin hd0 h
    exact le_of_mul_le_mul_left (this.trans ha) h2
  · right
    have h3 : 0 ≤ Real.pi - d := by linarith
    have h4 : Real.pi - d ≤ Real.pi / 2 := by linarith [not_le.mp h]
    have := Real.mul_le_sin h3 h4
    rw [Real.sin_pi_sub] at this
    exact le_of_mul_le_mul_left (this.trans ha) h2

theorem arc_volume {r : ℝ} (hr : 0 < r) (z : ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    volume ({φ | ‖circ r φ - z‖ ≤ ρ} ∩ Ioc (-Real.pi) Real.pi) ≤
      ENNReal.ofReal (6 * Real.pi * ρ / r) := by
  by_cases hne : ({φ | ‖circ r φ - z‖ ≤ ρ} ∩ Ioc (-Real.pi) Real.pi).Nonempty
  swap
  · rw [Set.not_nonempty_iff_eq_empty.mp hne]
    simp
  obtain ⟨φ₀, h₀, h₀'⟩ := hne
  have hpi := Real.pi_pos
  set a := Real.pi / 2 * (ρ / r) with ha
  have ha0 : 0 ≤ a := by positivity
  have hsub : {φ | ‖circ r φ - z‖ ≤ ρ} ∩ Ioc (-Real.pi) Real.pi ⊆
      (Icc (φ₀ - 2 * a) (φ₀ + 2 * a) ∪
        Icc (φ₀ + 2 * Real.pi - 2 * a) (φ₀ + 2 * Real.pi + 2 * a)) ∪
        Icc (φ₀ - 2 * Real.pi - 2 * a) (φ₀ - 2 * Real.pi + 2 * a) := by
    rintro φ ⟨h1, h1'⟩
    have d1 : ‖circ r φ - z‖ ≤ ρ := h1
    have d0 : ‖circ r φ₀ - z‖ ≤ ρ := h₀
    have d2 : ‖circ r φ - circ r φ₀‖ ≤ 2 * ρ := by
      have := norm_sub_le (circ r φ - z) (circ r φ₀ - z)
      simp only [sub_sub_sub_cancel_right] at this
      linarith
    rw [circ_sub_norm hr.le] at d2
    set δ := (φ - φ₀) / 2 with hδ
    have hs : |Real.sin δ| ≤ 2 / Real.pi * a := by
      have e : 2 / Real.pi * a = ρ / r := by
        rw [ha]
        field_simp
      rw [e, le_div_iff₀ hr]
      nlinarith
    have hlt : |δ| < Real.pi := by
      rw [abs_lt]
      have := h1'.1
      have := h1'.2
      have := h₀'.1
      have := h₀'.2
      constructor <;> rw [hδ] <;> linarith
    have hφ : φ = φ₀ + 2 * δ := by
      rw [hδ]
      ring
    rcases sin_half_small hlt hs with h | h
    · left
      left
      have := abs_le.mp h
      constructor <;> linarith [this.1, this.2]
    · rcases abs_cases δ with ⟨e, _⟩ | ⟨e, _⟩
      · left
        right
        rw [e] at h
        have := abs_lt.mp hlt
        constructor <;> linarith [this.1, this.2]
      · right
        rw [e] at h
        have := abs_lt.mp hlt
        constructor <;> linarith [this.1, this.2]
  refine (measure_mono hsub).trans ?_
  refine (measure_union_le _ _).trans ?_
  have e1 := (measure_union_le (μ := (volume : Measure ℝ)) (Icc (φ₀ - 2 * a) (φ₀ + 2 * a))
    (Icc (φ₀ + 2 * Real.pi - 2 * a) (φ₀ + 2 * Real.pi + 2 * a)))
  rw [Real.volume_Icc, Real.volume_Icc] at e1
  rw [Real.volume_Icc]
  have e2 : φ₀ + 2 * a - (φ₀ - 2 * a) = 4 * a := by ring
  have e3 : φ₀ + 2 * Real.pi + 2 * a - (φ₀ + 2 * Real.pi - 2 * a) = 4 * a := by ring
  have e4 : φ₀ - 2 * Real.pi + 2 * a - (φ₀ - 2 * Real.pi - 2 * a) = 4 * a := by ring
  rw [e2, e3] at e1
  rw [e4]
  calc _ ≤ ENNReal.ofReal (4 * a) + ENNReal.ofReal (4 * a) + ENNReal.ofReal (4 * a) := by gcongr
    _ = _ := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        rw [ha]
        ring

theorem arc_set_measurable (r : ℝ) (z : ℂ) (ρ : ℝ) : MeasurableSet {φ | ‖circ r φ - z‖ ≤ ρ} :=
  measurableSet_le (((circ_continuous r).sub continuous_const).norm.measurable) measurable_const

theorem arcM_le {f : ℝ → ℝ} {F : ℝ} (hF : ∀ φ, f φ ≤ F) {S : Set ℝ} (hS : MeasurableSet S) :
    arcM f S ≤ ENNReal.ofReal F * volume (S ∩ Ioc (-Real.pi) Real.pi) := by
  unfold arcM
  rw [withDensity_apply _ hS]
  calc _ ≤ ∫⁻ _ in S, ENNReal.ofReal F ∂(volume.restrict (Ioc (-Real.pi) Real.pi)) :=
        lintegral_mono fun φ => ENNReal.ofReal_le_ofReal (hF φ)
    _ = _ := by
        rw [setLIntegral_const, Measure.restrict_apply hS]

theorem arcM_ball {f : ℝ → ℝ} {F : ℝ} (hF0 : 0 ≤ F) (hF : ∀ φ, f φ ≤ F) {r : ℝ} (hr : 0 < r)
    (z : ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    arcM f {φ | ‖circ r φ - z‖ ≤ ρ} ≤ ENNReal.ofReal (F * (6 * Real.pi / r) * ρ) := by
  refine (arcM_le hF (arc_set_measurable r z ρ)).trans ?_
  calc _ ≤ ENNReal.ofReal F * ENNReal.ofReal (6 * Real.pi * ρ / r) := by
        gcongr
        exact arc_volume hr z hρ
    _ = _ := by
        rw [← ENNReal.ofReal_mul hF0]
        congr 1
        ring

theorem arcM_total {f : ℝ → ℝ} {F : ℝ} (hF0 : 0 ≤ F) (hF : ∀ φ, f φ ≤ F) :
    arcM f Set.univ ≤ ENNReal.ofReal (F * (2 * Real.pi)) := by
  refine (arcM_le hF MeasurableSet.univ).trans ?_
  rw [Set.univ_inter, Real.volume_Ioc, ← ENNReal.ofReal_mul hF0]
  apply ENNReal.ofReal_le_ofReal
  have : Real.pi - -Real.pi = 2 * Real.pi := by ring
  rw [this]

theorem arcM_finite {f : ℝ → ℝ} {F : ℝ} (hF0 : 0 ≤ F) (hF : ∀ φ, f φ ≤ F) :
    IsFiniteMeasure (arcM f) :=
  ⟨lt_of_le_of_lt (arcM_total hF0 hF) ENNReal.ofReal_lt_top⟩

/-- A density on a circle. -/
theorem circ_eucl {f : ℝ → ℝ} {F : ℝ} (hF0 : 0 ≤ F) (hF : ∀ φ, f φ ≤ F) {r : ℝ} (hr : 0 < r) :
    EuclBall ((arcM f).map (circ r)) (F * (6 * Real.pi / r) + F * (2 * Real.pi)) r := by
  have hm := (circ_continuous r).measurable
  constructor
  · intro z ρ hρ
    rw [Measure.map_apply hm Metric.isClosed_closedBall.measurableSet]
    have e : circ r ⁻¹' Metric.closedBall z ρ = {φ | ‖circ r φ - z‖ ≤ ρ} := by
      ext φ
      simp [dist_eq_norm]
    rw [e]
    exact sqrt_ball_bound (by positivity) (by positivity) hρ (arcM_ball hF0 hF hr z hρ)
      ((measure_mono (Set.subset_univ _)).trans (arcM_total hF0 hF))
  · rw [ae_map_iff hm.aemeasurable (measurableSet_le measurable_norm measurable_const)]
    exact Eventually.of_forall fun φ => (circ_norm hr.le φ).le

theorem joukowski_factor {z t : ℂ} (hz : z ≠ 0) (ht : t ≠ 0) :
    joukowski z - joukowski t = (z - t) * (z - t⁻¹) / (2 * z) := by
  unfold joukowski
  field_simp
  ring

theorem exists_joukowski_root (c : ℂ) : ∃ t : ℂ, t ≠ 0 ∧ joukowski t = c := by
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (k := ℂ) (c ^ 2 - 1) (show 0 < 2 by norm_num)
  have h0 : c + s ≠ 0 := by
    intro h
    have hs' : s = -c := by linear_combination h
    rw [hs'] at hs
    have : (1 : ℂ) = 0 := by linear_combination hs
    exact one_ne_zero this
  refine ⟨c + s, h0, ?_⟩
  unfold joukowski
  field_simp
  linear_combination hs

/-- The Joukowski image of a density on a circle. -/
theorem jcirc_eucl {f : ℝ → ℝ} {F : ℝ} (hF0 : 0 ≤ F) (hF : ∀ φ, f φ ≤ F) {r : ℝ} (hr : 0 < r) :
    EuclBall ((arcM f).map fun φ => joukowski (circ r φ))
      (2 * (F * (6 * Real.pi / r)) * √(2 * r)) ((r + r⁻¹) / 2) := by
  have hc : Continuous fun φ => circ r φ := circ_continuous r
  have hne : ∀ φ, circ r φ ≠ 0 := fun φ => by
    rw [← norm_pos_iff, circ_norm hr.le]
    exact hr
  have hjc : Continuous fun φ => joukowski (circ r φ) := by
    unfold joukowski
    exact (hc.add (hc.inv₀ hne)).div_const _
  have hm := hjc.measurable
  constructor
  · intro c ρ hρ
    rw [Measure.map_apply hm Metric.isClosed_closedBall.measurableSet]
    obtain ⟨t, ht, rfl⟩ := exists_joukowski_root c
    set ρ' := √(2 * r) * √ρ with hρ'
    have hρ'0 : 0 < ρ' := by positivity
    have hsq : ρ' ^ 2 = 2 * ρ * r := by
      rw [hρ', mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt hρ.le]
      ring
    have hsub : (fun φ => joukowski (circ r φ)) ⁻¹' Metric.closedBall (joukowski t) ρ ⊆
        {φ | ‖circ r φ - t‖ ≤ ρ'} ∪ {φ | ‖circ r φ - t⁻¹‖ ≤ ρ'} := by
      intro φ hφ
      have h1 : ‖joukowski (circ r φ) - joukowski t‖ ≤ ρ := by
        simpa [dist_eq_norm] using hφ
      rw [joukowski_factor (hne φ) ht, norm_div, norm_mul, norm_mul, circ_norm hr.le,
        div_le_iff₀ (by simp; positivity)] at h1
      simp only [Complex.norm_ofNat] at h1
      by_contra hcon
      simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_le] at hcon
      have := mul_lt_mul'' hcon.1 hcon.2 hρ'0.le hρ'0.le
      nlinarith
    refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
    have b1 := arcM_ball hF0 hF hr t hρ'0
    have b2 := arcM_ball hF0 hF hr t⁻¹ hρ'0
    calc _ ≤ ENNReal.ofReal (F * (6 * Real.pi / r) * ρ') +
          ENNReal.ofReal (F * (6 * Real.pi / r) * ρ') := add_le_add b1 b2
      _ = _ := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1
          rw [hρ']
          ring
  · rw [ae_map_iff hm.aemeasurable (measurableSet_le measurable_norm measurable_const)]
    refine Eventually.of_forall fun φ => ?_
    unfold joukowski
    rw [norm_div, Complex.norm_ofNat]
    have := norm_add_le (circ r φ) (circ r φ)⁻¹
    rw [norm_inv, circ_norm hr.le] at this
    linarith

end
end CatalanMeasure.GenD.Signed.RouteI.CompletedGas
#print axioms CatalanMeasure.GenD.Signed.RouteI.selectedFree_of_lowOrPick
#print axioms CatalanMeasure.GenD.Signed.RouteI.CompletedGas.low_of_value
#print axioms CatalanMeasure.GenD.Signed.RouteI.CompletedGas.second_energy_sq_end
