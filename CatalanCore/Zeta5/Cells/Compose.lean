module

public import CatalanCore.Zeta5.Cells.Vfield
public import CatalanMeasure.GenD.Signed.TaylorCell

@[expose] public section

/-!
# Z5-CELLS, part 2: composition of a field with a smooth change of variable (ZD20)

`fdb D Y j` is the Faà di Bruno polynomial of order `j ≤ 5`: if `D k` stands for `V^{(k)}(y(x))`
and `Y i` for `y^{(i)}(x)`, then `fdb D Y j` is `(V ∘ y)^{(j)}(x)`.  The derivative tower of the
composite is proved once, abstractly (`hasDerivAt_fdb`, ring identities for `j = 0..4`), and the
remainder polynomial `fdb D Y 5` is bounded from `|D k| ≤ Dm k` and `|Y i| ≤ Ym i`
(`abs_fdb5_le`), which is exactly the Faà di Bruno majorant of ledger ZD20.
-/

namespace CatalanCore.Zeta5.Cells

noncomputable section

/-- the Faà di Bruno polynomials of orders `0..5`. -/
def fdb {R : Type*} [CommRing R] (D Y : ℕ → R) : ℕ → R
  | 0 => D 0
  | 1 => D 1 * Y 1
  | 2 => D 2 * Y 1 ^ 2 + D 1 * Y 2
  | 3 => D 3 * Y 1 ^ 3 + 3 * D 2 * Y 1 * Y 2 + D 1 * Y 3
  | 4 => D 4 * Y 1 ^ 4 + 6 * D 3 * Y 1 ^ 2 * Y 2 + D 2 * (3 * Y 2 ^ 2 + 4 * Y 1 * Y 3)
      + D 1 * Y 4
  | 5 => D 5 * Y 1 ^ 5 + 10 * D 4 * Y 1 ^ 3 * Y 2
      + D 3 * (15 * Y 1 * Y 2 ^ 2 + 10 * Y 1 ^ 2 * Y 3)
      + D 2 * (10 * Y 2 * Y 3 + 5 * Y 1 * Y 4) + D 1 * Y 5
  | _ => 0

/-- **The derivative tower of a composite.**  `Dc k` is `V^{(k)} ∘ y` with
`(Dc k)' = Dc (k+1) · Yc 1` and `Yc i` is `y^{(i)}` with `(Yc i)' = Yc (i+1)`. -/
theorem hasDerivAt_fdb {Dc Yc : ℕ → ℝ → ℝ} {x : ℝ}
    (hD : ∀ k < 5, HasDerivAt (Dc k) (Dc (k + 1) x * Yc 1 x) x)
    (hY : ∀ i < 5, HasDerivAt (Yc i) (Yc (i + 1) x) x) (j : ℕ) (hj : j < 5) :
    HasDerivAt (fun z => fdb (fun k => Dc k z) (fun i => Yc i z) j)
      (fdb (fun k => Dc (k) x) (fun i => Yc i x) (j + 1)) x := by
  have d0 := hD 0 (by norm_num)
  have d1 := hD 1 (by norm_num)
  have d2 := hD 2 (by norm_num)
  have d3 := hD 3 (by norm_num)
  have d4 := hD 4 (by norm_num)
  have y1 := hY 1 (by norm_num)
  have y2 := hY 2 (by norm_num)
  have y3 := hY 3 (by norm_num)
  have y4 := hY 4 (by norm_num)
  simp only [Nat.reduceAdd] at d0 d1 d2 d3 d4 y1 y2 y3 y4
  interval_cases j
  · exact d0.congr_deriv (by simp only [fdb, Nat.reduceAdd])
  · have h := d1.fun_mul y1
    exact h.congr_deriv (by simp only [fdb, Nat.reduceAdd]; ring)
  · have h := (d2.fun_mul (y1.fun_pow 2)).fun_add (d1.fun_mul y2)
    exact h.congr_deriv (by simp only [fdb, Nat.reduceAdd]; ring)
  · have h := ((d3.fun_mul (y1.fun_pow 3)).fun_add
      (((d2.const_mul 3).fun_mul y1).fun_mul y2)).fun_add (d1.fun_mul y3)
    exact h.congr_deriv (by simp only [fdb, Nat.reduceAdd]; ring)
  · have h := (((d4.fun_mul (y1.fun_pow 4)).fun_add
      (((d3.const_mul 6).fun_mul (y1.fun_pow 2)).fun_mul y2)).fun_add
      (d2.fun_mul (((y2.fun_pow 2).const_mul 3).fun_add ((y1.const_mul 4).fun_mul y3)))).fun_add
      (d1.fun_mul y4)
    exact h.congr_deriv (by simp only [fdb, Nat.reduceAdd]; ring)

/-- the majorant of `fdb D Y 5` from `|D k| ≤ Dm k`, `|Y i| ≤ Ym i`. -/
def fdbBound {R : Type*} [CommRing R] (Dm Ym : ℕ → R) : R :=
  Dm 5 * Ym 1 ^ 5 + 10 * Dm 4 * Ym 1 ^ 3 * Ym 2
    + Dm 3 * (15 * Ym 1 * Ym 2 ^ 2 + 10 * Ym 1 ^ 2 * Ym 3)
    + Dm 2 * (10 * Ym 2 * Ym 3 + 5 * Ym 1 * Ym 4) + Dm 1 * Ym 5

theorem abs_mul_le_mul' {x y X Y : ℝ} (hx : |x| ≤ X) (hy : |y| ≤ Y) : |x * y| ≤ X * Y := by
  rw [abs_mul]; exact mul_le_mul hx hy (abs_nonneg _) ((abs_nonneg _).trans hx)

theorem abs_pow_le' {x X : ℝ} (hx : |x| ≤ X) (n : ℕ) : |x ^ n| ≤ X ^ n := by
  rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) hx n

theorem abs_cmul_le' (c : ℝ) {x X : ℝ} (hc : 0 ≤ c) (hx : |x| ≤ X) : |c * x| ≤ c * X := by
  rw [abs_mul, abs_of_nonneg hc]; exact mul_le_mul_of_nonneg_left hx hc

/-- **The Faà di Bruno majorant (ZD20, remainder).** -/
theorem abs_fdb5_le (D Y Dm Ym : ℕ → ℝ) (hD : ∀ k, 1 ≤ k → k ≤ 5 → |D k| ≤ Dm k)
    (hY : ∀ i, 1 ≤ i → i ≤ 5 → |Y i| ≤ Ym i) : |fdb D Y 5| ≤ fdbBound Dm Ym := by
  have y1 := hY 1 (by norm_num) (by norm_num)
  have y2 := hY 2 (by norm_num) (by norm_num)
  have y3 := hY 3 (by norm_num) (by norm_num)
  have y4 := hY 4 (by norm_num) (by norm_num)
  have y5 := hY 5 (by norm_num) (by norm_num)
  have d1 := hD 1 (by norm_num) (by norm_num)
  have d2 := hD 2 (by norm_num) (by norm_num)
  have d3 := hD 3 (by norm_num) (by norm_num)
  have d4 := hD 4 (by norm_num) (by norm_num)
  have d5 := hD 5 (by norm_num) (by norm_num)
  have t1 : |D 5 * Y 1 ^ 5| ≤ Dm 5 * Ym 1 ^ 5 := abs_mul_le_mul' d5 (abs_pow_le' y1 5)
  have t2 : |10 * D 4 * Y 1 ^ 3 * Y 2| ≤ 10 * Dm 4 * Ym 1 ^ 3 * Ym 2 :=
    abs_mul_le_mul' (abs_mul_le_mul' (abs_cmul_le' 10 (by norm_num) d4) (abs_pow_le' y1 3)) y2
  have i3 : |15 * Y 1 * Y 2 ^ 2 + 10 * Y 1 ^ 2 * Y 3| ≤
      15 * Ym 1 * Ym 2 ^ 2 + 10 * Ym 1 ^ 2 * Ym 3 := by
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · exact abs_mul_le_mul' (abs_cmul_le' 15 (by norm_num) y1) (abs_pow_le' y2 2)
    · exact abs_mul_le_mul' (abs_cmul_le' 10 (by norm_num) (abs_pow_le' y1 2)) y3
  have t3 := abs_mul_le_mul' d3 i3
  have i4 : |10 * Y 2 * Y 3 + 5 * Y 1 * Y 4| ≤ 10 * Ym 2 * Ym 3 + 5 * Ym 1 * Ym 4 := by
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · exact abs_mul_le_mul' (abs_cmul_le' 10 (by norm_num) y2) y3
    · exact abs_mul_le_mul' (abs_cmul_le' 5 (by norm_num) y1) y4
  have t4 := abs_mul_le_mul' d2 i4
  have t5 := abs_mul_le_mul' d1 y5
  have e : fdb D Y 5 = D 5 * Y 1 ^ 5 + 10 * D 4 * Y 1 ^ 3 * Y 2
      + D 3 * (15 * Y 1 * Y 2 ^ 2 + 10 * Y 1 ^ 2 * Y 3)
      + D 2 * (10 * Y 2 * Y 3 + 5 * Y 1 * Y 4) + D 1 * Y 5 := rfl
  rw [e]
  unfold fdbBound
  obtain ⟨a1, b1⟩ := abs_le.mp t1
  obtain ⟨a2, b2⟩ := abs_le.mp t2
  obtain ⟨a3, b3⟩ := abs_le.mp t3
  obtain ⟨a4, b4⟩ := abs_le.mp t4
  obtain ⟨a5, b5⟩ := abs_le.mp t5
  rw [abs_le]
  constructor <;> linarith

/-- `fdb` is affine in the slot `D 1` with coefficient `Y j`. -/
theorem fdb_affine {R : Type*} [CommRing R] (D D' Y : ℕ → R) (j : ℕ) (hj1 : 1 ≤ j) (hj5 : j ≤ 5)
    (h : ∀ k, 2 ≤ k → k ≤ 5 → D k = D' k) : fdb D Y j = fdb D' Y j + (D 1 - D' 1) * Y j := by
  have h2 := h 2 (by norm_num) (by norm_num)
  have h3 := h 3 (by norm_num) (by norm_num)
  have h4 := h 4 (by norm_num) (by norm_num)
  have h5 := h 5 (by norm_num) (by norm_num)
  interval_cases j <;> simp only [fdb, h2, h3, h4, h5] <;> ring

/-- `fdb j` depends on `Y i` for `i ≤ j` only. -/
theorem fdb_congr_Y {R : Type*} [CommRing R] (D Y Y' : ℕ → R) (j : ℕ) (hj : j ≤ 5)
    (h : ∀ i, 1 ≤ i → i ≤ 5 → Y i = Y' i) : fdb D Y j = fdb D Y' j := by
  have h1 := h 1 (by norm_num) (by norm_num)
  have h2 := h 2 (by norm_num) (by norm_num)
  have h3 := h 3 (by norm_num) (by norm_num)
  have h4 := h 4 (by norm_num) (by norm_num)
  have h5 := h 5 (by norm_num) (by norm_num)
  interval_cases j <;> simp only [fdb, h1, h2, h3, h4, h5]

/-- casting `fdb` from `ℚ` to `ℝ`. -/
theorem fdb_cast (D Y : ℕ → ℚ) (j : ℕ) :
    ((fdb D Y j : ℚ) : ℝ) = fdb (fun k => (D k : ℝ)) (fun i => (Y i : ℝ)) j := by
  rcases j with _ | _ | _ | _ | _ | _ | j <;> simp [fdb]

theorem fdbBound_cast (D Y : ℕ → ℚ) :
    ((fdbBound D Y : ℚ) : ℝ) = fdbBound (fun k => (D k : ℝ)) (fun i => (Y i : ℝ)) := by
  simp [fdbBound]

end

end CatalanCore.Zeta5.Cells
