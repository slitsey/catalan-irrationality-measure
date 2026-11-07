module
public import CatalanMeasure.GenD.Signed.RouteI.Literals
public import CatalanMeasure.GenD.Signed.Data.S1.TrialEnd
public import CatalanMeasure.GenD.Analytic.WeightedAtom

@[expose] public section
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 0

namespace CatalanMeasure.GenD.Signed.RouteI
open CatalanMeasure.GenD D58 Analytic Budget Filter Set Polynomial CatalanMeasure.Parametric
open OAI.InternalCatalan Finset
open scoped BigOperators
noncomputable section

/-! The endpoint wrappers of the 296 design (`firstEnd_budget_FK`, `first296`, `second296`,
`second198`, `freeLarge198`) fixed one K590 trial and the old gain; the cell builders of
`RouteI.Family` replace them.  What remains is the selected-sheet consumer, with the column factor
`Z = (∏ (1 + ζ s))^m` and the node correction `δ`. -/

private theorem marked_weighted_laurent_expansion {n g : ℕ}
    (z : Fin n → ℝ) (marked : Fin n → Bool) {w M : ℝ}
    (hw : 0 ≤ w) (hM : 0 ≤ M)
    (hV : ∀ t : Fin n → Bool,
      w * |(Matrix.of fun i r : Fin n =>
        if t i && marked i && decide (0 ≤ z i) then z i ^ ((r : ℤ) - g)
        else actualLaurentEntry g r (z i)).det| ≤ M) :
    w * |(markedLaurentMatrix g z marked).det| ≤
      M * ∏ i, (if marked i then (5 : ℝ) else 1) := by
  by_cases hw0 : w = 0
  · simp only [hw0, zero_mul]
    exact mul_nonneg hM (prod_nonneg fun i _ => by split_ifs <;> norm_num)
  have hwpos : 0 < w := lt_of_le_of_ne hw (Ne.symm hw0)
  have hb := marked_laurent_det_bound z marked (M := M / w) (div_nonneg hM hw)
    (fun t => (le_div_iff₀ hwpos).mpr (by simpa [mul_comm] using hV t))
  have hh := mul_le_mul_of_nonneg_left hb hw
  change w * |(markedLaurentMatrix g z marked).det| ≤ _ at hh
  calc
    _ ≤ w * (M / w * ∏ i, (if marked i then (5 : ℝ) else 1)) := hh
    _ = _ := by field_simp

private theorem marked_sheet_product_uncast {P : Parameters} {N p m : ℕ}
    (hpm : p + m = P.n N) (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ) :
    markedSheetProduct P N hpm x y s =
      ((∏ i, (1 + s i)) ^ m * (∏ j, paramRowNodeWeight P N (y j)) *
        paramPinPrincipal P N x s /
          ∏ j, |(rowCommonFactor P N).eval (realCoordinateInv (y j))|) *
      |(markedLaurentMatrix (P.g N) (Fin.append x y)
        (Fin.addCases (fun _ => false) (fun _ => true))).det| := by
  let z : Fin (P.n N) → ℝ := fun i => Fin.append x y (Fin.cast hpm.symm i)
  let marked : Fin (P.n N) → Bool := fun i =>
    Fin.addCases (fun _ => false) (fun _ => true) (Fin.cast hpm.symm i)
  have hm : (markedLaurentMatrix (P.g N) z marked).submatrix
      (finCongr hpm) (finCongr hpm) =
      markedLaurentMatrix (P.g N) (Fin.append x y)
        (Fin.addCases (fun _ => false) (fun _ => true)) := by
    ext i r
    simp [markedLaurentMatrix, z, marked]
  have hd := Matrix.abs_det_submatrix_equiv_equiv (finCongr hpm) (finCongr hpm)
    (markedLaurentMatrix (P.g N) z marked)
  rw [hm] at hd
  unfold markedSheetProduct
  change _ * |(markedLaurentMatrix (P.g N) z marked).det| * _ * _ / _ = _
  rw [← hd]
  ring


/-! Selected determinant input, BEFORE expansion, with the column factor `Z` and the node field `δ`
(GP §11.1).  Q can contain actual node restrictions and the small marked-fraction condition. This
never assumes an unsigned grouped-product estimate for the signed determinant. -/
def SelectedFreeProductCostOnRestr (P : Parameters) (ζ : ℝ) (δ : ℝ → ℝ) (target cost : ℝ)
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
    (∏ l, (1 + ζ * s l)) ^ m *
    (((∏ j, paramRowNodeWeight P N (y j))*paramPinPrincipal P N x s /
      ∏ j, |(rowCommonFactor P N).eval (realCoordinateInv (y j))|) *
      |(Matrix.of fun i r : Fin (p+m) =>
        if sel i && (Fin.addCases (fun _ => false) (fun _ => true) i) &&
            decide (0≤Fin.append x y i) then
          Fin.append x y i ^ ((r:ℤ)-P.g N)
        else actualLaurentEntry (P.g N) r (Fin.append x y i)).det|) ≤
      (1+10*Real.exp 12*(P.n N:ℝ))^P.n N *
        Real.exp (((P.n0:ℝ)*N)^2*(-target+Real.log 2/2+ε)+cost*N*m -
          N * ∑ j, δ (realCoordinateInv (y j)))

/-- The factor-free marked sheet from the selected bound (expansion over the selectors), generic in
the configuration predicate `Q'`: `Z · markedSheetFree ≤ 5^m (1 + 10 e¹² n)^n exp(… − N ∑ δ(t(y_j)))`. -/
theorem free_of_selected {P : Parameters} {G : ℝ → Prop} {target cost ζ : ℝ} {δ : ℝ → ℝ}
    (hζ : 0 ≤ ζ) {Q' : ∀ (N m : ℕ), (Fin m → ℝ) → Prop}
    (hselected : SelectedFreeProductCostOnRestr P ζ δ target cost G (fun N _ m _ y _ => Q' N m y)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ (p m : ℕ) (hpm : p + m = P.n N)
      (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ),
      (∀ i, x i ∈ Ioo (-1 : ℝ) 1) → (∀ i, x i ≠ 0) →
      (∀ j, y j ∈ Ioo (-1 : ℝ) 1) → (∀ j, y j ≠ 0) → (∀ j, G (y j)) → Q' N m y →
      (∀ i, s i ∈ Ioo (0 : ℝ) 1) → Function.Injective (Fin.append x y) → Function.Injective s →
      (∑ i : Fin (p + m), paramCaseField P N (Fin.append x y i)) ≤ -1 →
      (∏ l, (1 + ζ * s l)) ^ m * markedSheetFree P N hpm x y s ≤
        5 ^ m * (1 + 10 * Real.exp 12 * (P.n N : ℝ)) ^ P.n N *
          Real.exp (((P.n0 : ℝ) * N) ^ 2 * (-target + Real.log 2 / 2 + ε) + cost * N * m -
            N * ∑ j, δ (realCoordinateInv (y j))) := by
  intro ε hε
  filter_upwards [hselected ε hε] with N he
  intro p m hpm x y s hx hx0 hy hy0 hyG hQ hs hzi hsi hcase
  classical
  let w : ℝ := (∏ j, paramRowNodeWeight P N (y j))*paramPinPrincipal P N x s /
    ∏ j, |(rowCommonFactor P N).eval (realCoordinateInv (y j))|
  let Z : ℝ := (∏ l, (1 + ζ * s l)) ^ m
  let marked : Fin (p+m) → Bool := Fin.addCases (fun _ => false) (fun _ => true)
  let M := (1+10*Real.exp 12*(P.n N:ℝ))^P.n N *
    Real.exp (((P.n0:ℝ)*N)^2*(-target+Real.log 2/2+ε)+cost*N*m -
      N * ∑ j, δ (realCoordinateInv (y j)))
  have hw : 0≤w := by
    dsimp only [w]
    exact div_nonneg (mul_nonneg
      (prod_nonneg fun i _ => paramRowNodeWeight_nonneg P N (hy i))
      (paramPinPrincipal_nonneg P N x s hx hs))
      (prod_nonneg fun i _ => abs_nonneg _)
  have hZ : 0 < Z :=
    pow_pos (prod_pos fun i _ => by nlinarith [(hs i).1, (hs i).2]) _
  have hM : 0≤M := by dsimp [M]; positivity
  have hV : ∀ sel : Fin (p+m) → Bool,
      (Z*w)*|(Matrix.of fun i r : Fin (p+m) =>
        if sel i && marked i && decide (0≤Fin.append x y i) then
          Fin.append x y i ^ ((r:ℤ)-P.g N)
        else actualLaurentEntry (P.g N) r (Fin.append x y i)).det|≤M := fun sel => by
    have := he p m hpm x y s hx hx0 hy hy0 hyG hs hzi hsi hcase hQ sel
    rw [mul_assoc]
    exact this
  have hbound := marked_weighted_laurent_expansion (Fin.append x y) marked
    (mul_nonneg hZ.le hw) hM hV
  have hcost : (∏ i : Fin (p+m), if marked i then (5:ℝ) else 1)=5^m := by
    simp [marked,Fin.prod_univ_add]
  rw [hcost] at hbound
  have hSpos : 0<(∏ i,(1+s i))^m :=
    pow_pos (prod_pos fun i _ => by linarith [(hs i).1]) _
  have hfree : markedSheetFree P N hpm x y s =
      w*|(markedLaurentMatrix (P.g N) (Fin.append x y) marked).det| := by
    apply mul_left_cancel₀ hSpos.ne'
    rw [←markedSheetProduct_eq_pow_mul_free,marked_sheet_product_uncast]
    dsimp only [w]
    ring
  rw [hfree]
  calc
    _ = (Z*w)*|(markedLaurentMatrix (P.g N) (Fin.append x y) marked).det| := by
        dsimp only [Z]; ring
    _ ≤ M*5^m := hbound
    _ = _ := by dsimp [M]; ring

theorem hnear296 {P : Parameters} {G : ℝ → Prop}
    {Nd : ∀ (N m : ℕ), (Fin m → ℝ) → Prop} {target cost α1 ζ : ℝ} {δ : ℝ → ℝ} (hζ : 0 ≤ ζ)
    (hselected : SelectedFreeProductCostOnRestr P ζ δ target cost G
      (fun N _ m _ y _ => (m:ℝ)≤α1*(P.n N:ℝ) ∧ Nd N m y)) :
    FreeNearBoundZ P G Nd ζ δ target cost α1 := by
  intro ε hε
  filter_upwards [free_of_selected hζ hselected ε hε] with N he
  intro p m hpm x y s hm hx hx0 hy hy0 hyG hNd hs hzi hsi hcase
  exact he p m hpm x y s hx hx0 hy hy0 hyG ⟨hm, hNd⟩ hs hzi hsi hcase

/-- The large-`m` bound `FreeLargeBoundZ` from the selected bound on the class `α1 n ≤ m`. -/
theorem hlarge296 {P : Parameters} {G : ℝ → Prop} {target cost α1 ζ : ℝ} {δ : ℝ → ℝ}
    (hζ : 0 ≤ ζ)
    (hselected : SelectedFreeProductCostOnRestr P ζ δ target cost G
      (fun N _ m _ _ _ => α1 * (P.n N : ℝ) ≤ (m : ℝ))) :
    FreeLargeBoundZ P G ζ δ target cost α1 := by
  intro ε hε
  filter_upwards [free_of_selected (Q' := fun N m _ => α1 * (P.n N : ℝ) ≤ (m : ℝ)) hζ hselected ε hε]
    with N he
  intro p m hpm x y s hm hx hx0 hy hy0 hyG hs hzi hsi hcase
  exact he p m hpm x y s hx hx0 hy hy0 hyG hm hs hzi hsi hcase

end
end CatalanMeasure.GenD.Signed.RouteI
#print axioms CatalanMeasure.GenD.Signed.RouteI.free_of_selected
#print axioms CatalanMeasure.GenD.Signed.RouteI.hnear296
#print axioms CatalanMeasure.GenD.Signed.RouteI.hlarge296
