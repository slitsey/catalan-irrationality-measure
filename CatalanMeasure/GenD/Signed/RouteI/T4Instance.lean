module

public import CatalanMeasure.GenD.Signed.RouteI.CompletedGasTangent
public import CatalanMeasure.GenD.Signed.RouteI.CapSourceData
public import CatalanMeasure.GenD.Signed.RouteI.InterceptSource
public import CatalanMeasure.GenD.Signed.RouteI.Literals
public import CatalanMeasure.GenD.DesignInstance.PositiveCert.Data
public import CatalanMeasure.GenD.Signed.RouteI.GasEnergyHi

@[expose] public section

/-!
# Route I `T4Instance`: `selected_free_product` at `capSource`

The concrete test and the instance of the near bound at the source record of `CapSourceData`.

* A polynomial phase test of Chebyshev degree `32` with `a₀ = h₀ = 0`: the test is nonpositive on
  all of `[-1,0]`, so the negative mid zone and its drop certificate do not arise.  Its three
  minorants are certified by an exact integer subdivision check (`checkZ`).
* `anchorIntercept_refQuad`: PROOF-RI 12.26, the anchor intercept in moment form is
  `- refQuad`.
* Design C (G27, 7 Nov 2026): the 295 proof shape (`phaseDelta`, `delta_bound`, `phase_margin`,
  `one_margin`, `budget_anchor0`, `selected_free_capSource`, `freeNear_capSource`; archived in
  `archive/CatalanArchive/GenD/Signed/RouteI/T4Instance295.lean.txt`) is replaced by the cover of
  GP §9: `QP`/`PolyNonneg`/`polyNonneg_of_ints` (a leaf proves `checkZ zs f 0 0 = true` by a kernel decision on an integer list),
  `net_cells` (Lemma 8.1), and the discharges `sig_cells1/2`, `hbud_of_sigV`, `hI_of_moves` (a),
  `wV_cells`, `oldBound_budget_of_wV`, `first_budget_of_wV` (b), (e), `phys_cells`, `hphase_arith`,
  `hone_arith` (c), (d).  Every literal is a parameter.
-/

namespace CatalanMeasure.GenD.Signed.RouteI.T4Instance

open Finset

noncomputable section

/-! ### Integer polynomials as lists, and a subdivision positivity check -/

/-- Horner value of a coefficient list. -/
def evalZ : List ℤ → ℝ → ℝ
  | [], _ => 0
  | a :: p, x => (a : ℝ) + x * evalZ p x

/-- Coefficientwise sum. -/
def addL : List ℤ → List ℤ → List ℤ
  | [], q => q
  | a :: p, [] => a :: p
  | a :: p, b :: q => (a + b) :: addL p q

/-- Scalar multiple. -/
def smulL (c : ℤ) (p : List ℤ) : List ℤ := p.map (c * ·)

/-- `(A + X) q`. -/
def mulLin (A : ℤ) (q : List ℤ) : List ℤ := addL (smulL A q) (0 :: q)

theorem evalZ_addL (p q : List ℤ) (x : ℝ) : evalZ (addL p q) x = evalZ p x + evalZ q x := by
  induction p generalizing q with
  | nil => simp [addL, evalZ]
  | cons a p ih =>
    cases q with
    | nil => simp [addL, evalZ]
    | cons b q =>
      simp only [addL, evalZ, ih]
      push_cast
      ring

theorem evalZ_smulL (c : ℤ) (p : List ℤ) (x : ℝ) : evalZ (smulL c p) x = c * evalZ p x := by
  induction p with
  | nil => simp [smulL, evalZ]
  | cons a p ih =>
    simp only [smulL, List.map_cons, evalZ] at ih ⊢
    rw [ih]
    push_cast
    ring

theorem evalZ_mulLin (A : ℤ) (q : List ℤ) (x : ℝ) :
    evalZ (mulLin A q) x = (A + x) * evalZ q x := by
  unfold mulLin
  rw [evalZ_addL, evalZ_smulL]
  simp only [evalZ]
  push_cast
  ring

/-- The polynomial of `u ↦ Bd ^ (len p - 1) p ((A + u) / Bd)`. -/
def taylorZ (A Bd : ℤ) : List ℤ → List ℤ
  | [] => []
  | a :: p => addL [a * Bd ^ p.length] (mulLin A (taylorZ A Bd p))

theorem evalZ_taylorZ (A Bd : ℤ) (hB : (Bd : ℝ) ≠ 0) (p : List ℤ) (u : ℝ) :
    evalZ (taylorZ A Bd p) u * Bd = (Bd : ℝ) ^ p.length * evalZ p ((A + u) / Bd) := by
  induction p with
  | nil => simp [taylorZ, evalZ]
  | cons a p ih =>
    simp only [taylorZ, evalZ_addL, evalZ_mulLin, evalZ, List.length_cons]
    push_cast
    have h2 : (A : ℝ) + u = Bd * (((A : ℝ) + u) / Bd) := by field_simp
    linear_combination ((A : ℝ) + u) * ih +
      (Bd : ℝ) ^ p.length * evalZ p (((A : ℝ) + u) / Bd) * h2

/-- `Σ |a_j|`. -/
def l1Z : List ℤ → ℤ
  | [] => 0
  | a :: p => (a.natAbs : ℤ) + l1Z p

theorem abs_evalZ_le (p : List ℤ) {u : ℝ} (hu : |u| ≤ 1) : |evalZ p u| ≤ (l1Z p : ℝ) := by
  induction p with
  | nil => simp [evalZ, l1Z]
  | cons a p ih =>
    simp only [evalZ, l1Z]
    rw [Int.natCast_natAbs]
    push_cast
    calc |(a : ℝ) + u * evalZ p u| ≤ |(a : ℝ)| + |u * evalZ p u| := abs_add_le _ _
      _ = |(a : ℝ)| + |u| * |evalZ p u| := by rw [abs_mul]
      _ ≤ |(a : ℝ)| + 1 * (l1Z p : ℝ) := by
          gcongr
      _ = _ := by ring

/-- One cell passes when the constant term dominates. -/
def headDom : List ℤ → Bool
  | [] => true
  | a :: p => decide (l1Z p ≤ a)

theorem evalZ_nonneg_of_headDom {q : List ℤ} (h : headDom q = true) {u : ℝ} (hu : |u| ≤ 1) :
    0 ≤ evalZ q u := by
  cases q with
  | nil => simp [evalZ]
  | cons a p =>
    have h1 : l1Z p ≤ a := by simpa [headDom] using h
    have h2 : (l1Z p : ℝ) ≤ a := by exact_mod_cast h1
    have h3 := abs_evalZ_le p hu
    have h4 : |u * evalZ p u| ≤ (l1Z p : ℝ) := by
      rw [abs_mul]
      calc |u| * |evalZ p u| ≤ 1 * |evalZ p u| := by gcongr
        _ ≤ _ := by linarith
    have h5 := (abs_le.mp h4).1
    simp only [evalZ]
    linarith

/-- The cell `[m/2^s, (m+1)/2^s]`. -/
def cellOK (p : List ℤ) (m : ℤ) (s : ℕ) : Bool :=
  headDom (taylorZ (2 * m + 1) (2 ^ (s + 1)) p)

/-- Recursive subdivision. -/
def checkZ (p : List ℤ) : ℕ → ℤ → ℕ → Bool
  | 0, m, s => cellOK p m s
  | f + 1, m, s => cellOK p m s || (checkZ p f (2 * m) (s + 1) && checkZ p f (2 * m + 1) (s + 1))

theorem cell_sound {p : List ℤ} {m : ℤ} {s : ℕ} (h : cellOK p m s = true) {w : ℝ}
    (h1 : (m : ℝ) / 2 ^ s ≤ w) (h2 : w ≤ ((m : ℝ) + 1) / 2 ^ s) : 0 ≤ evalZ p w := by
  have hs : (0 : ℝ) < 2 ^ s := by positivity
  have hBz : (((2 ^ (s + 1) : ℤ)) : ℝ) = 2 * 2 ^ s := by push_cast; ring
  have hA : (((2 * m + 1 : ℤ)) : ℝ) = 2 * m + 1 := by push_cast; ring
  rw [div_le_iff₀ hs] at h1
  rw [le_div_iff₀ hs] at h2
  set u : ℝ := w * (2 * 2 ^ s) - (2 * m + 1) with hu
  have hu1 : |u| ≤ 1 := by
    rw [abs_le]
    constructor <;> rw [hu] <;> linarith
  have hq := evalZ_nonneg_of_headDom h hu1
  have ht := evalZ_taylorZ (2 * m + 1) (2 ^ (s + 1)) (by rw [hBz]; positivity) p u
  have hw : (((2 * m + 1 : ℤ) : ℝ) + u) / ((2 ^ (s + 1) : ℤ) : ℝ) = w := by
    rw [hA, hBz, hu]
    field_simp
    ring
  rw [hw, hBz] at ht
  have hpos : 0 < (2 * 2 ^ s : ℝ) ^ p.length := by positivity
  by_contra hneg
  have : (2 * 2 ^ s : ℝ) ^ p.length * evalZ p w < 0 :=
    mul_neg_of_pos_of_neg hpos (not_le.mp hneg)
  have h3 : 0 ≤ evalZ (taylorZ (2 * m + 1) (2 ^ (s + 1)) p) u * (2 * 2 ^ s) := by positivity
  linarith

theorem checkZ_sound {p : List ℤ} {f : ℕ} : ∀ {m : ℤ} {s : ℕ}, checkZ p f m s = true → ∀ {w : ℝ},
    (m : ℝ) / 2 ^ s ≤ w → w ≤ ((m : ℝ) + 1) / 2 ^ s → 0 ≤ evalZ p w := by
  induction f with
  | zero => intro m s h w h1 h2; exact cell_sound h h1 h2
  | succ f ih =>
    intro m s h w h1 h2
    simp only [checkZ, Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with h | ⟨ha, hb⟩
    · exact cell_sound h h1 h2
    · have hs : (0 : ℝ) < 2 ^ s := by positivity
      rcases le_total w ((2 * (m : ℝ) + 1) / 2 ^ (s + 1)) with hw | hw
      · refine ih ha ?_ ?_
        · push_cast
          rw [pow_succ]
          calc 2 * (m : ℝ) / (2 ^ s * 2) = (m : ℝ) / 2 ^ s := by field_simp
            _ ≤ w := h1
        · push_cast
          exact hw
      · refine ih hb ?_ ?_
        · push_cast
          exact hw
        · push_cast
          rw [pow_succ]
          calc w ≤ ((m : ℝ) + 1) / 2 ^ s := h2
            _ = (2 * (m : ℝ) + 1 + 1) / (2 ^ s * 2) := by field_simp; ring

/-- Derivative of a coefficient list. -/
def derivZ : List ℤ → List ℤ
  | [] => []
  | _ :: p => addL p (0 :: derivZ p)

theorem hasDerivAt_evalZ (p : List ℤ) (x : ℝ) : HasDerivAt (evalZ p) (evalZ (derivZ p) x) x := by
  induction p with
  | nil =>
    have : evalZ [] = fun _ : ℝ => (0 : ℝ) := by funext y; simp [evalZ]
    rw [this]
    simpa [derivZ, evalZ] using hasDerivAt_const x (0 : ℝ)
  | cons a p ih =>
    have e : evalZ (a :: p) = fun y => (a : ℝ) + y * evalZ p y := by funext y; simp [evalZ]
    rw [e]
    have h := ((hasDerivAt_id' x).mul ih).const_add (a : ℝ)
    have e2 : evalZ (derivZ (a :: p)) x = 1 * evalZ p x + x * evalZ (derivZ p) x := by
      simp only [derivZ, evalZ_addL, evalZ]
      push_cast
      ring
    rw [e2]
    exact h

/-- One Chebyshev step `2 X b - a`. -/
def chebStep (a b : List ℤ) : List ℤ := addL (0 :: smulL 2 b) (smulL (-1) a)

/-- `Σ c_i T_{n+i}` from the pair `T_n, T_{n+1}`. -/
def chebSum : List ℤ → List ℤ → List ℤ → List ℤ
  | [], _, _ => []
  | c :: cs, a, b => addL (smulL c a) (chebSum cs b (chebStep a b))

theorem evalZ_chebStep (a b : List ℤ) (x : ℝ) :
    evalZ (chebStep a b) x = 2 * x * evalZ b x - evalZ a x := by
  simp only [chebStep, evalZ_addL, evalZ_smulL, evalZ]
  push_cast
  ring

theorem evalZ_chebSum (cs : List ℤ) : ∀ (n : ℕ) (a b : List ℤ) (x : ℝ),
    evalZ a x = (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval x →
    evalZ b x = (Polynomial.Chebyshev.T ℝ ((n + 1 : ℕ) : ℤ)).eval x →
    evalZ (chebSum cs a b) x = ∑ i ∈ range cs.length,
      (cs.getD i 0 : ℝ) * (Polynomial.Chebyshev.T ℝ ((n + i : ℕ) : ℤ)).eval x := by
  induction cs with
  | nil => intro n a b x _ _; simp [chebSum, evalZ]
  | cons c cs ih =>
    intro n a b x ha hb
    have hstep : evalZ (chebStep a b) x =
        (Polynomial.Chebyshev.T ℝ ((n + 1 + 1 : ℕ) : ℤ)).eval x := by
      rw [evalZ_chebStep, ha, hb]
      have := Polynomial.Chebyshev.T_add_two ℝ (n : ℤ)
      push_cast
      rw [show (n : ℤ) + 1 + 1 = (n : ℤ) + 2 by ring, this]
      simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_ofNat,
        Polynomial.eval_X]
    simp only [chebSum, evalZ_addL, evalZ_smulL, List.length_cons]
    rw [ih (n + 1) b (chebStep a b) x hb hstep, sum_range_succ', ha]
    simp only [List.getD_cons_succ, List.getD_cons_zero, Nat.add_zero]
    rw [add_comm]
    congr 1
    refine sum_congr rfl fun i _ => ?_
    rw [show n + 1 + i = n + (i + 1) by ring]

end
end CatalanMeasure.GenD.Signed.RouteI.T4Instance

namespace CatalanMeasure.GenD.Signed.RouteI.T4Instance

open Finset CatalanMeasure.GenD.Signed.RouteI.CompletedGas

noncomputable section

/-! ### Arctangent bounds -/

theorem arctan_ge_cubic {x : ℝ} (hx : 0 ≤ x) : x - x ^ 3 / 3 ≤ Real.arctan x := by
  have hm : MonotoneOn (fun t : ℝ => Real.arctan t - (t - t ^ 3 / 3)) (Set.Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) ?_ ?_ ?_
    · exact (Real.continuous_arctan.sub (by fun_prop)).continuousOn
    · exact (Real.differentiable_arctan.sub (by fun_prop)).differentiableOn
    · intro t _
      have h : HasDerivAt (fun t : ℝ => Real.arctan t - (t - t ^ 3 / 3))
          (1 / (1 + t ^ 2) - (1 - t ^ 2)) t := by
        have h1 := Real.hasDerivAt_arctan t
        have h2 : HasDerivAt (fun t : ℝ => t - t ^ 3 / 3) (1 - t ^ 2) t := by
          have := (hasDerivAt_id' t).sub (((hasDerivAt_id' t).pow 3).div_const 3)
          exact this.congr_deriv (by norm_num; try ring)
        exact h1.sub h2
      rw [h.deriv]
      have hp : 0 < 1 + t ^ 2 := by positivity
      rw [sub_nonneg, le_div_iff₀ hp]
      nlinarith [sq_nonneg (t ^ 2)]
  have := hm (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hx) hx
  simp only [Real.arctan_zero] at this
  linarith

theorem arctan_le_quintic {x : ℝ} (hx : 0 ≤ x) : Real.arctan x ≤ x - x ^ 3 / 3 + x ^ 5 / 5 := by
  have hm : MonotoneOn (fun t : ℝ => (t - t ^ 3 / 3 + t ^ 5 / 5) - Real.arctan t) (Set.Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) ?_ ?_ ?_
    · exact ((by fun_prop : Continuous fun t : ℝ => t - t ^ 3 / 3 + t ^ 5 / 5).sub
        Real.continuous_arctan).continuousOn
    · exact ((by fun_prop : Differentiable ℝ fun t : ℝ => t - t ^ 3 / 3 + t ^ 5 / 5).sub
        Real.differentiable_arctan).differentiableOn
    · intro t _
      have h : HasDerivAt (fun t : ℝ => (t - t ^ 3 / 3 + t ^ 5 / 5) - Real.arctan t)
          ((1 - t ^ 2 + t ^ 4) - 1 / (1 + t ^ 2)) t := by
        have h1 := Real.hasDerivAt_arctan t
        have h2 : HasDerivAt (fun t : ℝ => t - t ^ 3 / 3 + t ^ 5 / 5) (1 - t ^ 2 + t ^ 4) t := by
          have := ((hasDerivAt_id' t).sub (((hasDerivAt_id' t).pow 3).div_const 3)).add
            (((hasDerivAt_id' t).pow 5).div_const 5)
          exact this.congr_deriv (by norm_num; try ring)
        exact h2.sub h1
      rw [h.deriv]
      have hp : 0 < 1 + t ^ 2 := by positivity
      rw [sub_nonneg, div_le_iff₀ hp]
      nlinarith [sq_nonneg (t ^ 3)]
  have := hm (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hx) hx
  simp only [Real.arctan_zero] at this
  linarith

theorem arctan_quarter_ge : (1 : ℝ) / 4 - 1 / 192 ≤ Real.arctan (1 / 4) := by
  have := arctan_ge_cubic (x := 1 / 4) (by norm_num)
  norm_num at this ⊢
  linarith

theorem arctan_quarter_le : Real.arctan (1 / 4) ≤ 24499 / 100000 := by
  have := arctan_le_quintic (x := 1 / 4) (by norm_num)
  norm_num at this ⊢
  linarith

theorem arctan_four : Real.arctan 4 = Real.pi / 2 - Real.arctan (1 / 4) := by
  have h := Real.arctan_inv_of_pos (x := 4) (by norm_num)
  rw [show (4 : ℝ)⁻¹ = 1 / 4 by norm_num] at h
  linarith

/-! ### The test -/

/-- `2^31` times the Chebyshev coefficients of the test, constant term first. -/
def Cl : List ℤ := [992223195, 1572501258, 694157164, 54489394, -79944576, 8707318, 4646156, -68344628, -59744406, 7203904, 10140334, -40511734, -44934400, -1785648, 6395776, -26648082, -33410324, -4130338, 5027056, -16327448, -23083202, -3844254, 3906634, -8948844, -14344364, -2564734, 2665864, -4010182, -7584828, -1167144, 1359958, -1136496, -3025640]

/-- `2^44` times the monomial coefficients of the lower bound of `phaseH` on `[0,1]`. -/
def Gl : List ℤ := [4306402949936, 8278668498148, 7302146673370, 5975159923080, 647252134698, 48480419288449, -389680930542744, 2200952896427515, -8651881045792319, 24249968968644468, -49077543596064112, 71678709695492376, -74632640367983696, 53815904330016688, -25426588365815872, 7054098186591636, -868659404126457]

/-- The test polynomial, scaled by `2^31`. -/
def PL : List ℤ := chebSum Cl [1] [0, 1]

/-- The quadratic `17 - 30 X + 17 X²` times `q`. -/
def quadMul (q : List ℤ) : List ℤ :=
  addL (addL (smulL 17 q) (0 :: smulL (-30) q)) (0 :: 0 :: smulL 17 q)

theorem evalZ_quadMul (q : List ℤ) (x : ℝ) :
    evalZ (quadMul q) x = (17 * x ^ 2 - 30 * x + 17) * evalZ q x := by
  simp only [quadMul, evalZ_addL, evalZ_smulL, evalZ]
  push_cast
  ring

def D1 : List ℤ := smulL (-1) PL
def D2 : List ℤ := addL Gl (smulL (-8192) PL)
def D3 : List ℤ := addL [8 * 2 ^ 44] (smulL (-1) (quadMul (derivZ Gl)))
def D4 : List ℤ := addL Gl [-(Cl.getD 0 0) * 4096, -(Cl.getD 1 0) * 2048]

-- kcost: 192 Taylor shifts, degree <= 32, about 1.0e5 integer operations in total.
theorem D1_ok : checkZ D1 12 (-1) 0 = true := by decide +kernel
theorem D2_ok : checkZ D2 12 0 0 = true := by decide +kernel
theorem D3_ok : checkZ D3 12 0 0 = true := by decide +kernel
theorem D4_ok : checkZ D4 12 0 0 = true := by decide +kernel

/-- The test coefficients. -/
def testF (k : ℕ) : ℝ := (if k = 0 then 2 else 1) * (Cl.getD k 0 : ℝ) / 2 ^ 31

theorem testF_zero {k : ℕ} (hk : 33 ≤ k) : testF k = 0 := by
  have h : Cl.getD k 0 = 0 := List.getD_eq_default _ _ (by simpa [Cl] using hk)
  unfold testF
  rw [h]
  simp

theorem dampedT_test (w : ℝ) : testF 0 / 2 + dampedT testF 1 w = evalZ PL w / 2 ^ 31 := by
  have h0 : evalZ [1] w = (Polynomial.Chebyshev.T ℝ ((0 : ℕ) : ℤ)).eval w := by simp [evalZ]
  have h1 : evalZ [0, 1] w = (Polynomial.Chebyshev.T ℝ ((0 + 1 : ℕ) : ℤ)).eval w := by
    simp [evalZ]
  have hs := evalZ_chebSum Cl 0 [1] [0, 1] w h0 h1
  have hl : Cl.length = 32 + 1 := by simp [Cl]
  unfold dampedT
  rw [tsum_eq_sum (s := range 32) (fun k hk => by
    rw [testF_zero (by simpa using hk)]; simp)]
  unfold PL
  rw [hs, hl, sum_range_succ' _ 32, add_div, sum_div, add_comm]
  congr 1
  · refine sum_congr rfl fun k _ => ?_
    simp only [testF, Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false, one_mul, one_pow,
      Nat.zero_add]
    ring
  · have e : testF 0 = 2 * (Cl.getD 0 0 : ℝ) / 2 ^ 31 := by simp [testF]
    rw [e]
    simp only [Nat.add_zero, Nat.cast_zero, Polynomial.Chebyshev.T_zero, Polynomial.eval_one,
      mul_one]
    ring

theorem hasDerivAt_phaseH {w : ℝ} (hw : 0 ≤ w) :
    HasDerivAt phaseH (8 / (17 * w ^ 2 - 30 * w + 17)) w := by
  have hw1 : (1 + w) ≠ 0 := by positivity
  have hq : 0 < 17 * w ^ 2 - 30 * w + 17 := by nlinarith [sq_nonneg (w - 15 / 17)]
  have h1 : HasDerivAt (fun x : ℝ => 1 - x) (-1) w := by
    simpa using (hasDerivAt_id w).const_sub 1
  have h2 : HasDerivAt (fun x : ℝ => 1 + x) 1 w := by
    simpa using (hasDerivAt_id w).const_add 1
  have h3 := ((h1.div h2 hw1).const_mul 4).arctan
  have h4 := h3.const_sub (Real.pi / 2)
  have hq' : (1 + w) ^ 2 + 16 * (1 - w) ^ 2 = 17 * w ^ 2 - 30 * w + 17 := by ring
  have hq2 : (1 + w) ^ 2 + 16 * (1 - w) ^ 2 ≠ 0 := by rw [hq']; exact hq.ne'
  have e0 : 1 + (4 * ((1 - w) / (1 + w))) ^ 2 =
      ((1 + w) ^ 2 + 16 * (1 - w) ^ 2) / (1 + w) ^ 2 := by
    field_simp
    ring
  refine h4.congr_deriv ?_
  simp only [Pi.div_apply]
  rw [e0, ← hq']
  field_simp
  ring

theorem G_le_phaseH {w : ℝ} (h0 : 0 ≤ w) (h1 : w ≤ 1) : evalZ Gl w / 2 ^ 44 ≤ phaseH w := by
  have hder : ∀ x ∈ Set.Icc (0 : ℝ) 1, HasDerivAt (fun t => phaseH t - evalZ Gl t / 2 ^ 44)
      (8 / (17 * x ^ 2 - 30 * x + 17) - evalZ (derivZ Gl) x / 2 ^ 44) x :=
    fun x hx => (hasDerivAt_phaseH hx.1).sub ((hasDerivAt_evalZ Gl x).div_const _)
  have hm : MonotoneOn (fun t => phaseH t - evalZ Gl t / 2 ^ 44) (Set.Icc 0 1) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 1) ?_ ?_ ?_
    · exact fun x hx => (hder x hx).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      exact (hder x ⟨hx.1.le, hx.2.le⟩).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      rw [(hder x ⟨hx.1.le, hx.2.le⟩).deriv]
      have hq : 0 < 17 * x ^ 2 - 30 * x + 17 := by nlinarith [sq_nonneg (x - 15 / 17)]
      have h3 := checkZ_sound D3_ok (w := x) (by norm_num; exact hx.1.le)
        (by norm_num; exact hx.2.le)
      simp only [D3, evalZ_addL, evalZ_smulL, evalZ_quadMul, evalZ] at h3
      push_cast at h3
      rw [sub_nonneg, le_div_iff₀ hq]
      have h4 : (evalZ (derivZ Gl) x / 2 ^ 44) * (17 * x ^ 2 - 30 * x + 17) =
          ((17 * x ^ 2 - 30 * x + 17) * evalZ (derivZ Gl) x) / 2 ^ 44 := by ring
      rw [h4, div_le_iff₀ (by positivity)]
      linarith
  have h := hm (Set.left_mem_Icc.mpr zero_le_one) ⟨h0, h1⟩ h0
  have hG0 : evalZ Gl 0 / 2 ^ 44 ≤ phaseH 0 := by
    have e : phaseH 0 = Real.arctan (1 / 4) := by
      unfold phaseH
      norm_num
      rw [arctan_four]
      norm_num
    rw [e]
    refine le_trans ?_ arctan_quarter_ge
    simp only [Gl, evalZ]
    norm_num
  simp only at h
  linarith

/-- The concrete test: no negative mid zone. -/
def testT : PhaseTest where
  F := testF
  H := ∑ k ∈ range 32, testF (k + 1) ^ 2 * ((k + 1 : ℕ) : ℝ)
  a₀ := 0
  h₀ := 0
  summable := summable_of_ne_finset_zero (s := range 33) fun k hk => by
    rw [testF_zero (by simpa using hk)]; simp
  energy := hasSum_sum_of_ne_finset_zero fun k hk => by
    rw [testF_zero (by simpa using hk)]; simp
  h₀_nonneg := le_rfl
  pos := fun w hw => by
    rw [dampedT_test]
    have h2 := checkZ_sound D2_ok (w := w) (by norm_num; exact hw.1.le)
      (by norm_num; exact hw.2.le)
    simp only [D2, evalZ_addL, evalZ_smulL] at h2
    push_cast at h2
    refine le_trans ?_ (G_le_phaseH hw.1.le hw.2.le)
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  mid := fun w hw => by simp at hw
  left := fun w hw => by
    rw [dampedT_test]
    have h1 := checkZ_sound D1_ok (w := w) (by norm_num; exact hw.1) (by norm_num; simpa using hw.2)
    simp only [D1, evalZ_smulL] at h1
    push_cast at h1
    apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
    linarith
  near := fun y hy => by
    have h4 := checkZ_sound D4_ok (w := y) (by norm_num; exact hy.1.le)
      (by norm_num; exact hy.2.le)
    simp only [D4, evalZ_addL, evalZ] at h4
    push_cast at h4
    have e0 : testF 0 = 2 * (Cl.getD 0 0 : ℝ) / 2 ^ 31 := by simp [testF]
    have e1 : testF 1 = (Cl.getD 1 0 : ℝ) / 2 ^ 31 := by simp [testF]
    have hc1 : (0 : ℝ) ≤ (Cl.getD 1 0 : ℝ) := by
      have : (0 : ℤ) ≤ Cl.getD 1 0 := by decide +kernel
      exact_mod_cast this
    have e2 : |testF 1| = testF 1 := by
      rw [e1]; exact abs_of_nonneg (by positivity)
    refine le_trans ?_ (G_le_phaseH hy.1.le hy.2.le)
    rw [e2, e0, e1, le_div_iff₀ (by positivity)]
    nlinarith

end
end CatalanMeasure.GenD.Signed.RouteI.T4Instance

namespace CatalanMeasure.GenD.Signed.RouteI.T4Instance

open Finset CatalanMeasure.GenD.Signed.RouteI.CompletedGas CatalanMeasure.CellCert
open CatalanMeasure.Cert OAI.InternalCatalan CatalanMeasure.GenD.D58

noncomputable section

/-! ### Exact finite sums of a scaled trial sequence -/

/-- Complex product on rational pairs. -/
def cmulQ (z w : ℚ × ℚ) : ℚ × ℚ := (z.1 * w.1 - z.2 * w.2, z.1 * w.2 + z.2 * w.1)

/-- The complex number of a rational pair. -/
def cQ (z : ℚ × ℚ) : ℂ := barrierComplex z.1 z.2

theorem cQ_mul (z w : ℚ × ℚ) : cQ (cmulQ z w) = cQ z * cQ w := by
  apply Complex.ext <;> simp [cQ, cmulQ, barrierComplex]

theorem cQ_re (z : ℚ × ℚ) : (cQ z).re = (z.1 : ℝ) := by simp [cQ, barrierComplex]

/-- `Σ_i c_i Re (w z^i)`, carrying the power. -/
def tailPart : List ℚ → ℚ × ℚ → ℚ × ℚ → ℚ
  | [], _, _ => 0
  | c :: cs, z, w => c * w.1 + tailPart cs z (cmulQ w z)

theorem tailPart_eq (cs : List ℚ) (z : ℚ × ℚ) : ∀ w : ℚ × ℚ,
    ((tailPart cs z w : ℚ) : ℝ) =
      ∑ i ∈ range cs.length, (cs.getD i 0 : ℝ) * (cQ w * cQ z ^ i).re := by
  induction cs with
  | nil => intro w; simp [tailPart]
  | cons c cs ih =>
    intro w
    simp only [tailPart, List.length_cons]
    rw [sum_range_succ']
    push_cast
    rw [ih (cmulQ w z), cQ_mul, add_comm]
    congr 1
    · refine sum_congr rfl fun i _ => ?_
      simp only [List.getD_cons_succ]
      rw [pow_succ', mul_assoc]
    · simp [cQ_re]

/-- The tail contribution of a tail list. -/
def allTails (cs : List ℚ) : List TailQ → ℚ
  | [] => 0
  | t :: ts => tailPart cs (t.zr, t.zi) (cmulQ (t.rr, t.ri) (t.zr, t.zi)) + allTails cs ts

theorem allTails_eq (cs : List ℚ) (tl : List TailQ) :
    ((allTails cs tl : ℚ) : ℝ) = ∑ i ∈ range cs.length, (cs.getD i 0 : ℝ) *
      (((tl.map TailQ.toC).map (fun zr : ℂ × ℂ => zr.2 * zr.1 ^ (i + 1))).sum).re := by
  induction tl with
  | nil => simp [allTails]
  | cons t ts ih =>
    simp only [allTails, List.map_cons, List.sum_cons, Complex.add_re, mul_add, sum_add_distrib]
    push_cast
    rw [ih, tailPart_eq, cQ_mul]
    congr 1
    refine sum_congr rfl fun i _ => ?_
    congr 2
    simp only [TailQ.toC, cQ]
    rw [pow_succ']
    ring

/-- The finite contribution, from index `n`. -/
def finPart (Pc : List ℤ) : List ℚ → ℕ → ℚ
  | [], _ => 0
  | c :: cs, n => c * ((Pc.getD n 0 : ℚ) / 1099511627776) + finPart Pc cs (n + 1)

theorem finPart_eq (Pc : List ℤ) (cs : List ℚ) : ∀ n : ℕ,
    ((finPart Pc cs n : ℚ) : ℝ) =
      ∑ i ∈ range cs.length, (cs.getD i 0 : ℝ) * ((Pc.getD (n + i) 0 : ℝ) / 1099511627776) := by
  induction cs with
  | nil => intro n; simp [finPart]
  | cons c cs ih =>
    intro n
    simp only [finPart, List.length_cons]
    rw [sum_range_succ']
    push_cast
    rw [ih (n + 1), add_comm]
    congr 1
    refine sum_congr rfl fun i _ => ?_
    simp only [List.getD_cons_succ]
    rw [show n + 1 + i = n + (i + 1) by ring]

theorem trial_sum (Pc : List ℤ) (tl : List TailQ) (cs : List ℚ) :
    ∑ i ∈ range cs.length, (cs.getD i 0 : ℝ) * trialSeqS Pc tl (i + 1) =
      ((finPart Pc cs 0 + allTails cs tl : ℚ) : ℝ) := by
  push_cast
  rw [finPart_eq, allTails_eq, ← sum_add_distrib]
  refine sum_congr rfl fun i _ => ?_
  simp only [trialSeqS, finCoeffS, Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false,
    Nat.add_sub_cancel, Nat.zero_add]
  ring

/-- The test coefficients of positive index, scaled by `2^31`. -/
def ClQ : List ℚ := Cl.tail.map fun c => (c : ℚ)

theorem ClQ_length : ClQ.length = 32 := by simp [ClQ, Cl]

theorem getD_cast (l : List ℤ) (k : ℕ) :
    (l.map fun c => (c : ℚ)).getD k 0 = ((l.getD k 0 : ℤ) : ℚ) := by
  induction l generalizing k with
  | nil => simp
  | cons a l ih => cases k <;> simp_all

theorem ClQ_getD (k : ℕ) : (ClQ.getD k 0 : ℝ) = (Cl.getD (k + 1) 0 : ℝ) := by
  have h : Cl.tail.getD k 0 = Cl.getD (k + 1) 0 := by
    unfold Cl
    simp
  unfold ClQ
  rw [getD_cast, h]
  push_cast
  rfl

-- kcost: 75 tails x 32 complex products over Q, about 1.0e4 rational operations.
theorem U_num : (879 / 10000 : ℚ) * 2 ^ 31 ≤ finPart Cert590.Pc ClQ 0 + allTails ClQ Cert590.P := by
  decide +kernel

theorem u2_num :
    (-187 / 1000 : ℚ) ≤ finPart Cert590.Pc [0, 1] 0 + allTails [0, 1] Cert590.P := by
  decide +kernel

/-- The phase moment of the retained trial. -/
theorem U_lower : (879 / 10000 : ℝ) ≤
    ∑' k : ℕ, testF (k + 1) * trialSeqS Cert590.Pc Cert590.P (k + 1) := by
  rw [tsum_eq_sum (s := range 32) (fun k hk => by
    rw [testF_zero (by simpa using hk)]; simp)]
  have h := trial_sum Cert590.Pc Cert590.P ClQ
  rw [ClQ_length] at h
  have e : ∑ k ∈ range 32, testF (k + 1) * trialSeqS Cert590.Pc Cert590.P (k + 1) =
      (∑ i ∈ range 32, (ClQ.getD i 0 : ℝ) * trialSeqS Cert590.Pc Cert590.P (i + 1)) / 2 ^ 31 := by
    rw [sum_div]
    refine sum_congr rfl fun k hk => ?_
    rw [ClQ_getD]
    simp only [testF, Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false, one_mul]
    ring
  rw [e, h, le_div_iff₀ (by positivity)]
  have := U_num
  have h2 : (((879 / 10000 : ℚ) * 2 ^ 31 : ℚ) : ℝ) ≤
      ((finPart Cert590.Pc ClQ 0 + allTails ClQ Cert590.P : ℚ) : ℝ) := by exact_mod_cast this
  push_cast at h2 ⊢
  exact h2

theorem u2_lower : (-187 / 1000 : ℝ) ≤ trialSeqS Cert590.Pc Cert590.P 2 := by
  have h := trial_sum Cert590.Pc Cert590.P [0, 1]
  have h2 : (((-187 / 1000 : ℚ)) : ℝ) ≤
      ((finPart Cert590.Pc [0, 1] 0 + allTails [0, 1] Cert590.P : ℚ) : ℝ) := by
    exact_mod_cast u2_num
  rw [← h] at h2
  simp [sum_range_succ] at h2
  norm_num at h2 ⊢
  exact h2

end
end CatalanMeasure.GenD.Signed.RouteI.T4Instance

namespace CatalanMeasure.GenD.Signed.RouteI.T4Instance

open Finset MeasureTheory Filter Set CatalanMeasure.GenD.Signed.RouteI.CompletedGas
open CatalanMeasure.GenD.Signed.RouteI.CapFields CatalanMeasure.GenD.Signed.RouteI.InterceptSource
open OAI.InternalCatalan YCell

noncomputable section

local notation "Tc" k => (Polynomial.Chebyshev.T ℝ ((k : ℕ) : ℤ))

/-! ### Termwise integration of the moment series -/

section series

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ] {g : α → ℝ}
  {u : ℕ → ℝ} {K : ℝ}

/-- A series of bounded measurable terms with summable bounds: integrable, integrated termwise. -/
theorem series_integral {F : ℕ → α → ℝ} {b : ℕ → ℝ} (hF : ∀ n, Measurable (F n))
    (hb : Summable b) (hle : ∀ n, ∀ᵐ y ∂μ, |F n y| ≤ b n)
    (hs : ∀ᵐ y ∂μ, Summable fun n => F n y) :
    Integrable (fun y => ∑' n, F n y) μ ∧
      HasSum (fun n => ∫ y, F n y ∂μ) (∫ y, ∑' n, F n y ∂μ) := by
  have hint : ∀ n, Integrable (F n) μ := fun n =>
    Integrable.of_bound (hF n).aestronglyMeasurable (b n) (by
      filter_upwards [hle n] with y hy
      simpa [Real.norm_eq_abs] using hy)
  have hb0 : ∀ n, 0 ≤ ∫ y, ‖F n y‖ ∂μ := fun n => integral_nonneg fun y => norm_nonneg _
  have hbn : ∀ n, ∫ y, ‖F n y‖ ∂μ ≤ μ.real univ * b n := by
    intro n
    have h1 : ∫ y, ‖F n y‖ ∂μ ≤ ∫ _y, b n ∂μ := by
      refine integral_mono_ae (hint n).norm (integrable_const _) ?_
      filter_upwards [hle n] with y hy
      simpa [Real.norm_eq_abs] using hy
    simpa [integral_const, smul_eq_mul] using h1
  have hsum : Summable fun n => ∫ y, ‖F n y‖ ∂μ :=
    Summable.of_nonneg_of_le hb0 hbn (hb.mul_left _)
  refine ⟨?_, hasSum_integral_of_summable_integral_norm hint hsum⟩
  have hm : AEStronglyMeasurable (fun y => ∑' n, F n y) μ := by
    refine aestronglyMeasurable_of_tendsto_ae atTop
      (f := fun N y => ∑ n ∈ range N, F n y) (fun N => ?_) ?_
    · exact (Finset.measurable_fun_sum _ fun n _ => hF n).aestronglyMeasurable
    · filter_upwards [hs] with y hy
      exact hy.hasSum.tendsto_sum_nat
  refine Integrable.of_bound hm (∑' n, b n) ?_
  have hall : ∀ᵐ y ∂μ, ∀ n, |F n y| ≤ b n := ae_all_iff.mpr hle
  filter_upwards [hall, hs] with y hy hsy
  rw [Real.norm_eq_abs]
  have h1 : Summable fun n => |F n y| := Summable.of_nonneg_of_le (fun _ => abs_nonneg _) hy hb
  calc |∑' n, F n y| ≤ ∑' n, |F n y| := by
        simpa [Real.norm_eq_abs] using norm_tsum_le_tsum_norm (f := fun n => F n y) h1
    _ ≤ ∑' n, b n := h1.tsum_le_tsum hy hb

theorem trialT_integral (hg : Measurable g) (hgI : ∀ᵐ y ∂μ, g y ∈ Icc (-1 : ℝ) 1)
    (hu : ∀ k, k ≠ 0 → |u k| ≤ K / k) :
    Integrable (fun y => barrierTrialT u (g y)) μ ∧
      HasSum (fun n => u (n + 1) * (∫ y, (Tc (n + 1)).eval (g y) ∂μ) / ((n + 1 : ℕ) : ℝ))
        (∫ y, barrierTrialT u (g y) ∂μ) := by
  have h := series_integral (μ := μ) (F := fun n y => termT u (g y) n)
    (b := fun n => |u (n + 1)| / ((n + 1 : ℕ) : ℝ))
    (fun n => by
      unfold termT
      exact (((chebT_measurable (n + 1)).measurable.comp hg).const_mul _).div_const _)
    (summable_of_moment_bound hu).1
    (fun n => by
      filter_upwards [hgI] with y hy
      have hT : |(Tc (n + 1)).eval (g y)| ≤ 1 :=
        Polynomial.Chebyshev.abs_eval_T_real_le_one _ (abs_le.mpr hy)
      unfold termT
      rw [abs_div, abs_mul, Nat.abs_cast]
      gcongr
      calc |u (n + 1)| * |(Tc (n + 1)).eval (g y)| ≤ |u (n + 1)| * 1 := by gcongr
        _ = _ := mul_one _)
    (by
      filter_upwards [hgI] with y hy
      exact termT_summable hu hy)
  refine ⟨h.1, ?_⟩
  have e : (fun n => ∫ y, termT u (g y) n ∂μ) =
      fun n => u (n + 1) * (∫ y, (Tc (n + 1)).eval (g y) ∂μ) / ((n + 1 : ℕ) : ℝ) := by
    funext n
    unfold termT
    rw [integral_div, integral_const_mul]
  rw [e] at h
  exact h.2

theorem trialS_integral (hg : Measurable g) (hgI : ∀ᵐ y ∂μ, g y ∈ Icc (-1 : ℝ) 1)
    (hu : ∀ k, k ≠ 0 → |u k| ≤ K / k) :
    Integrable (fun y => barrierTrialS u (g y)) μ ∧
      HasSum (fun n => u (n + 1) * (∫ y, (g y) ^ (n + 1) ∂μ) / ((n + 1 : ℕ) : ℝ))
        (∫ y, barrierTrialS u (g y) ∂μ) := by
  have h := series_integral (μ := μ) (F := fun n y => termS u (g y) n)
    (b := fun n => |u (n + 1)| / ((n + 1 : ℕ) : ℝ))
    (fun n => by
      unfold termS
      exact ((hg.pow_const (n + 1)).const_mul _).div_const _)
    (summable_of_moment_bound hu).1
    (fun n => by
      filter_upwards [hgI] with y hy
      have hT : |(g y) ^ (n + 1)| ≤ 1 := by
        rw [abs_pow]
        exact pow_le_one₀ (abs_nonneg _) (abs_le.mpr hy)
      unfold termS
      rw [abs_div, abs_mul, Nat.abs_cast]
      gcongr
      calc |u (n + 1)| * |(g y) ^ (n + 1)| ≤ |u (n + 1)| * 1 := by gcongr
        _ = _ := mul_one _)
    (by
      filter_upwards [hgI] with y hy
      exact termS_summable hu hy)
  refine ⟨h.1, ?_⟩
  have e : (fun n => ∫ y, termS u (g y) n ∂μ) =
      fun n => u (n + 1) * (∫ y, (g y) ^ (n + 1) ∂μ) / ((n + 1 : ℕ) : ℝ) := by
    funext n
    unfold termS
    rw [integral_div, integral_const_mul]
  rw [e] at h
  exact h.2

end series

/-! ### Cell facts -/

theorem row_ae {c : YCell} (hc : RowCell c) :
    ∀ᵐ Y ∂cellM c, physX Y ∈ Ioo (-1 : ℝ) 1 ∧ physX Y ≠ 0 ∧ physX Y + 1 / physX Y = Y := by
  filter_upwards [cell_ae_mem c, cell_ae_ne c 2, cell_ae_ne c (-2)] with Y hY h2 hm2
  obtain ⟨h0, h1, h3⟩ := physX_mem hc hY
  refine ⟨?_, h0, h3⟩
  have hne : |physX Y| ≠ 1 := by
    intro h
    rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp h with e | e
    · rw [e] at h3
      apply h2
      rw [← h3]
      norm_num
    · rw [e] at h3
      apply hm2
      rw [← h3]
      norm_num
  exact abs_lt.mp (lt_of_le_of_ne h1 hne)

theorem row_ae_I {c : YCell} (hc : RowCell c) : ∀ᵐ Y ∂cellM c, physX Y ∈ Icc (-1 : ℝ) 1 := by
  filter_upwards [row_ae hc] with Y h
  exact ⟨h.1.1.le, h.1.2.le⟩

theorem col_ae_I {c : YCell} (hc : ColCell c) : ∀ᵐ s ∂cellM c, id s ∈ Icc (-1 : ℝ) 1 := by
  filter_upwards [cell_ae_mem c] with s hs
  exact ⟨hc.1.trans hs.1, hs.2.trans hc.2⟩

theorem row_log_integrable {c : YCell} (hc : RowCell c) :
    Integrable (fun Y => Real.log |physX Y|) (cellM c) := by
  apply cell_integrable_of_continuousOn
  apply ContinuousOn.log (physX_continuousOn_cell hc).abs
  intro Y hY
  exact abs_ne_zero.mpr (physX_mem hc hY).1

theorem avg_congr {c : YCell} {f g : ℝ → ℝ} (h : ∀ᵐ Y ∂cellM c, f Y = g Y) : c.avg f = c.avg g := by
  rw [cell_avg_eq, cell_avg_eq]
  exact integral_congr_ae h

theorem cellM_integral_const (c : YCell) (a : ℝ) : ∫ _y, a ∂cellM c = c.w * a := by
  simp [integral_const, cellM_real_univ, smul_eq_mul]

/-! ### Moment sums over a list -/

theorem physL_T {L : List YCell} (hL : ∀ c ∈ L, RowCell c) {u : ℕ → ℝ} {K : ℝ}
    (hu : ∀ k, k ≠ 0 → |u k| ≤ K / k) :
    HasSum (fun n => u (n + 1) * rowT L (n + 1) / ((n + 1 : ℕ) : ℝ))
      (physL L (barrierTrialT u)) := by
  induction L with
  | nil => simpa [rowT, physL] using hasSum_zero
  | cons c L ih =>
    have h1 := (trialT_integral physX_measurable (row_ae_I (hL c (by simp))) hu).2
    have h2 := ih fun d hd => hL d (by simp [hd])
    have h3 := h1.add h2
    convert h3 using 1
    · funext n
      simp only [rowT, physL_cons, phys, cell_avg_eq]
      ring
    · rw [physL_cons, phys, cell_avg_eq]

theorem physL_S {L : List YCell} (hL : ∀ c ∈ L, RowCell c) {u : ℕ → ℝ} {K : ℝ}
    (hu : ∀ k, k ≠ 0 → |u k| ≤ K / k) :
    HasSum (fun n => u (n + 1) * rowB L (n + 1) / ((n + 1 : ℕ) : ℝ))
      (physL L (barrierTrialS u)) := by
  induction L with
  | nil => simpa [rowB, physL] using hasSum_zero
  | cons c L ih =>
    have h1 := (trialS_integral physX_measurable (row_ae_I (hL c (by simp))) hu).2
    have h2 := ih fun d hd => hL d (by simp [hd])
    have h3 := h1.add h2
    convert h3 using 1
    · funext n
      simp only [rowB, physL_cons, phys, cell_avg_eq]
      ring
    · rw [physL_cons, phys, cell_avg_eq]

/-- The column average of a function. -/
def colAvg (L : List YCell) (f : ℝ → ℝ) : ℝ := (L.map fun c => c.avg f).sum

theorem colAvg_T {L : List YCell} (hL : ∀ c ∈ L, ColCell c) {u : ℕ → ℝ} {K : ℝ}
    (hu : ∀ k, k ≠ 0 → |u k| ≤ K / k) :
    HasSum (fun n => u (n + 1) * colT L (n + 1) / ((n + 1 : ℕ) : ℝ))
      (colAvg L (barrierTrialT u)) := by
  induction L with
  | nil => simpa [colT, colAvg] using hasSum_zero
  | cons c L ih =>
    have h1 := (trialT_integral (g := id) measurable_id (col_ae_I (hL c (by simp))) hu).2
    have h2 := ih fun d hd => hL d (by simp [hd])
    have h3 := h1.add h2
    convert h3 using 1
    · funext n
      simp only [colT_cons, cell_avg_eq, id]
      ring
    · simp only [colAvg, List.map_cons, List.sum_cons, cell_avg_eq, id]

/-! ### The three energies in moments -/

theorem energy_cross {L G : List YCell} (hL : ∀ c ∈ L, RowCell c) (hG : ∀ c ∈ G, ColCell c) :
    energy L (dilL G) = -massL G * physL L (fun u => Real.log |u|) -
      2 * physL L (barrierTrialS (colT G)) := by
  obtain ⟨K, -, hK⟩ := col_moment_bound hG
  induction L with
  | nil => simp [energy, physL]
  | cons c L ih =>
    have hc := hL c (by simp)
    have i1 := (trialS_integral physX_measurable (row_ae_I hc) hK).1
    have i2 := row_log_integrable hc
    have hae : ∀ᵐ Y ∂cellM c, potL (dilL G) Y =
        -massL G * Real.log |physX Y| - 2 * barrierTrialS (colT G) (physX Y) := by
      filter_upwards [row_ae hc] with Y ⟨hx, hx0, hY⟩
      have h1 := list_cross_series hG hx hx0
      have h2 := (termS_summable hK ⟨hx.1.le, hx.2.le⟩).hasSum.mul_left 2
      rw [← barrierTrialS_eq] at h2
      have h3 := h2.unique h1
      rw [hY] at h3
      unfold dilL
      linarith only [h3]
    have e : c.avg (potL (dilL G)) = -massL G * c.phys (fun u => Real.log |u|) -
        2 * c.phys (barrierTrialS (colT G)) := by
      rw [avg_congr hae, cell_avg_eq, integral_sub (i2.const_mul _) (i1.const_mul _),
        integral_const_mul, integral_const_mul]
      simp only [phys, cell_avg_eq]
    have ih' := ih fun d hd => hL d (by simp [hd])
    simp only [energy, List.map_cons, List.sum_cons] at ih' ⊢
    rw [e, ih', physL_cons, physL_cons]
    ring

theorem energy_row {L R : List YCell} (hL : ∀ c ∈ L, RowCell c) (hR : ∀ c ∈ R, RowCell c) :
    energy L R = -massL L * physL R (fun u => Real.log |u|) -
      massL L * massL R * Real.log 2 - massL R * physL L (fun u => Real.log |u|) -
      2 * physL L (barrierTrialT (rowT R)) - physL L (barrierTrialS (rowB R)) := by
  obtain ⟨K, -, hK⟩ := row_moment_bound hR
  induction L with
  | nil => simp [energy, physL, massL]
  | cons c L ih =>
    have hc := hL c (by simp)
    have i1 := (trialT_integral physX_measurable (row_ae_I hc) fun k hk => (hK k hk).1).1
    have i2 := (trialS_integral physX_measurable (row_ae_I hc) fun k hk => (hK k hk).2).1
    have i3 := row_log_integrable hc
    have hae : ∀ᵐ Y ∂cellM c, potL R Y = (-physL R (fun u => Real.log |u|) -
        massL R * Real.log 2) - massL R * Real.log |physX Y| -
        2 * barrierTrialT (rowT R) (physX Y) - barrierTrialS (rowB R) (physX Y) := by
      filter_upwards [row_ae hc] with Y ⟨hx, hx0, hY⟩
      have h1 := list_row_series hR hx hx0
      have hxI : physX Y ∈ Icc (-1 : ℝ) 1 := ⟨hx.1.le, hx.2.le⟩
      have hT := (termT_summable (fun k hk => (hK k hk).1) hxI).hasSum
      have hS := (termS_summable (fun k hk => (hK k hk).2) hxI).hasSum
      rw [← barrierTrialT_eq] at hT
      rw [← barrierTrialS_eq] at hS
      have h3 := ((hT.mul_left 2).add hS).unique h1
      rw [hY] at h3
      linarith only [h3]
    have e : c.avg (potL R) = c.w * (-physL R (fun u => Real.log |u|) - massL R * Real.log 2) -
        massL R * c.phys (fun u => Real.log |u|) - 2 * c.phys (barrierTrialT (rowT R)) -
        c.phys (barrierTrialS (rowB R)) := by
      set A : ℝ := -physL R (fun u => Real.log |u|) - massL R * Real.log 2
      have j1 : Integrable (fun Y => A - massL R * Real.log |physX Y|) (cellM c) :=
        (integrable_const A).sub (i3.const_mul _)
      have j2 : Integrable (fun Y => A - massL R * Real.log |physX Y| -
          2 * barrierTrialT (rowT R) (physX Y)) (cellM c) := j1.sub (i1.const_mul 2)
      have e1 : ∫ Y, (A - massL R * Real.log |physX Y| - 2 * barrierTrialT (rowT R) (physX Y) -
          barrierTrialS (rowB R) (physX Y)) ∂cellM c =
          (∫ Y, (A - massL R * Real.log |physX Y| - 2 * barrierTrialT (rowT R) (physX Y)) ∂cellM c) -
            ∫ Y, barrierTrialS (rowB R) (physX Y) ∂cellM c := integral_sub j2 i2
      have e2 : ∫ Y, (A - massL R * Real.log |physX Y| - 2 * barrierTrialT (rowT R) (physX Y))
          ∂cellM c = (∫ Y, (A - massL R * Real.log |physX Y|) ∂cellM c) -
            ∫ Y, 2 * barrierTrialT (rowT R) (physX Y) ∂cellM c := integral_sub j1 (i1.const_mul 2)
      have e3 : ∫ Y, (A - massL R * Real.log |physX Y|) ∂cellM c =
          (∫ _Y, A ∂cellM c) - ∫ Y, massL R * Real.log |physX Y| ∂cellM c :=
        integral_sub (integrable_const A) (i3.const_mul _)
      rw [avg_congr hae, cell_avg_eq, e1, e2, e3, cellM_integral_const, integral_const_mul,
        integral_const_mul]
      simp only [phys, cell_avg_eq]
    have ih' := ih fun d hd => hL d (by simp [hd])
    simp only [energy, List.map_cons, List.sum_cons] at ih' ⊢
    rw [e, ih', physL_cons, physL_cons, physL_cons, massL_cons]
    ring

theorem energy_col {L G : List YCell} (hL : ∀ c ∈ L, ColCell c) (hG : ∀ c ∈ G, ColCell c) :
    energy L G = -massL L * massL G * Real.log 2 - 2 * colAvg L (barrierTrialT (colT G)) := by
  obtain ⟨K, -, hK⟩ := col_moment_bound hG
  induction L with
  | nil => simp [energy, colAvg, massL]
  | cons c L ih =>
    have hc := hL c (by simp)
    have i1 := (trialT_integral (g := id) measurable_id (col_ae_I hc) hK).1
    have hae : ∀ᵐ s ∂cellM c, potL G s =
        -massL G * Real.log 2 - 2 * barrierTrialT (colT G) (id s) := by
      filter_upwards [col_ae_I hc] with s hs
      have h1 := list_col_self hG hs
      have h2 := (termT_summable hK hs).hasSum
      rw [← barrierTrialT_eq] at h2
      have h3 := h2.unique h1
      simp only [id] at h3 ⊢
      linarith only [h3]
    have e : c.avg (potL G) = c.w * (-massL G * Real.log 2) -
        2 * c.avg (barrierTrialT (colT G)) := by
      have e1 : ∫ s, (-massL G * Real.log 2 - 2 * barrierTrialT (colT G) (id s)) ∂cellM c =
          (∫ _s, -massL G * Real.log 2 ∂cellM c) -
            ∫ s, 2 * barrierTrialT (colT G) (id s) ∂cellM c :=
        integral_sub (integrable_const _) (i1.const_mul 2)
      rw [avg_congr hae, cell_avg_eq, e1, cellM_integral_const, integral_const_mul, cell_avg_eq]
      rfl
    have ih' := ih fun d hd => hL d (by simp [hd])
    simp only [energy, colAvg, List.map_cons, List.sum_cons] at ih' ⊢
    rw [e, ih', massL_cons]
    ring

/-- **PROOF-RI 12.26.**  The anchor intercept in moment form is minus the reference quadratic. -/
theorem anchorIntercept_eq {R C : List YCell} (hR : ∀ c ∈ R, RowCell c)
    (hC : ∀ c ∈ C, ColCell c) (hm : massL R = massL C) :
    anchorIntercept (massL R) (rowT R) (anchorV R C) =
      -(energy R R / 2 + energy C C - energy R (dilL C)) := by
  obtain ⟨K1, -, h1⟩ := row_moment_bound hR
  obtain ⟨K2, -, h2⟩ := col_moment_bound hC
  have sA := physL_T hR (fun k hk => (h1 k hk).1)
  have sB := physL_S hR (fun k hk => (h1 k hk).2)
  have sC := colAvg_T hC h2
  have sM := physL_S hR h2
  have eA : barrierTrialNormSq (rowT R) = physL R (barrierTrialT (rowT R)) := by
    rw [← sA.tsum_eq]
    unfold barrierTrialNormSq
    exact tsum_congr fun n => by ring
  have eV : barrierTrialNormSq (anchorV R C) =
      physL R (barrierTrialS (rowB R)) - 4 * physL R (barrierTrialS (colT C)) +
        4 * colAvg C (barrierTrialT (colT C)) := by
    have hs := (sB.sub (sM.mul_left 4)).add (sC.mul_left 4)
    rw [← hs.tsum_eq]
    unfold barrierTrialNormSq
    refine tsum_congr fun n => ?_
    simp only [anchorV]
    ring
  rw [energy_row hR hR, energy_col hC hC, energy_cross hR hC]
  unfold anchorIntercept
  rw [eA, eV, ← hm]
  ring

/-- The identification at the source record. -/
theorem anchorIntercept_refQuad {S : CapSource} (hS : S.Admissible)
    (hcol : ∀ a, ∀ c ∈ S.refCol a, ColCell c) (a : Fin 2) :
    anchorIntercept (aB S a) (aT S a) (aV S a) = -refQuad S a := by
  have hm : massL (S.refRow a) = massL (S.refCol a) := by
    fin_cases a
    · simpa using hS.ref_row_mass0.trans hS.ref_col_mass0.symm
    · simpa using hS.ref_row_mass1.trans hS.ref_col_mass1.symm
  exact anchorIntercept_eq (hS.ref_away a) (hcol a) hm

end
end CatalanMeasure.GenD.Signed.RouteI.T4Instance

namespace CatalanMeasure.GenD.Signed.RouteI.T4Instance

open Finset Filter CatalanMeasure.GenD.Signed.RouteI.CompletedGas CatalanMeasure.CellCert
open CatalanMeasure.GenD CatalanMeasure.GenD.D58 CatalanMeasure.GenD.Analytic
open CatalanMeasure.GenD.Signed.RouteI.CapFields CatalanMeasure.GenD.Signed.RouteI.CapSourceData

noncomputable section

/-! ### The seed and the column cells of `capSource` -/

theorem sig_rad_dom : ∀ n < 16, 10 * sigN.getD n 0 ≤ radN.getD n 0 := by decide +kernel
theorem sig_zero : sigN.getD 0 0 = 0 := by decide +kernel
theorem rad_zero : radN.getD 0 0 = 0 := by decide +kernel

theorem foldSeed_capSource : FoldSeed capSource where
  atom := by
    refine ⟨0, by norm_num [capSource], ?_, ?_⟩
    · change sigmaF 0 = 0
      simp only [sigmaF, Nat.zero_min, sig_zero]
      simp
    · change radialF 0 = 0
      simp only [radialF, Nat.zero_min, rad_zero]
      simp
  dom := by
    intro j hj
    have hj' : j < 16 := by simpa [capSource] using hj
    change 10 * sigmaF j ≤ radialF j
    simp only [sigmaF, radialF]
    rw [min_eq_left (by omega)]
    have h : ((10 * sigN.getD j 0 : ℤ) : ℝ) ≤ (radN.getD j 0 : ℝ) := by
      exact_mod_cast sig_rad_dom j hj'
    push_cast at h
    have hp : (0 : ℝ) < 10 ^ 17 := by positivity
    rw [← mul_div_assoc]
    gcongr

theorem col0_in : ∀ t ∈ col0, -1000000000000 ≤ t.1 ∧ t.2.1 ≤ 1000000000000 := by decide +kernel
theorem col1_in : ∀ t ∈ col1, -1000000000000 ≤ t.1 ∧ t.2.1 ≤ 1000000000000 := by decide +kernel

theorem colCell_mk {m : ℝ} {T : ℤ} {t : Tr} (hv : t.1 < t.2.1 ∧ 0 ≤ t.2.2) (hT : 0 ≤ T)
    (hm : 0 ≤ m) (h : -1000000000000 ≤ t.1 ∧ t.2.1 ≤ 1000000000000) :
    ColCell (mkCell m T t) := by
  obtain ⟨e1, e2, -⟩ := mkCell_eq hv hT hm
  have h1 : (-1000000000000 : ℝ) ≤ t.1 := by exact_mod_cast h.1
  have h2 : (t.2.1 : ℝ) ≤ 1000000000000 := by exact_mod_cast h.2
  constructor
  · rw [e1, le_div_iff₀ (by positivity)]
    norm_num
    linarith
  · rw [e2, div_le_iff₀ (by positivity)]
    norm_num
    linarith

theorem colCell_capSource : ∀ a, ∀ c ∈ capSource.refCol a, ColCell c := by
  intro a c hc
  change c ∈ refColF a at hc
  unfold refColF at hc
  split_ifs at hc
  · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hc
    exact colCell_mk (col0_ok t ht) col0_tot.le zero_le_one (col0_in t ht)
  · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hc
    exact colCell_mk (col1_ok t ht) col1_tot.le (by norm_num) (col1_in t ht)

theorem aB_zero : aB capSource 0 = 1 := by
  change massL (refRowF 0) = 1
  have h := massL_map_mkCell (m := 1) row0_tot.le zero_le_one row0 row0_ok
  have hne : (sumP row0 : ℝ) ≠ 0 := by exact_mod_cast row0_tot.ne'
  simp only [refRowF, if_true]
  rw [h]
  field_simp

theorem testF_zero_val : testF 0 = 992223195 / 2 ^ 30 := by
  have e : Cl.getD 0 0 = 992223195 := by decide +kernel
  simp only [testF, if_true, e]
  norm_num

theorem testH_le : testT.H ≤ 7877 / 10000 := by
  -- kcost: under 1 s measured 6 Nov (32 squares; the whole module compiles in 45 s wall)
  change ∑ k ∈ range 32, testF (k + 1) ^ 2 * ((k + 1 : ℕ) : ℝ) ≤ _
  have e : ∑ k ∈ range 32, testF (k + 1) ^ 2 * ((k + 1 : ℕ) : ℝ) =
      ((∑ k ∈ range 32, (Cl.getD (k + 1) 0) ^ 2 * ((k + 1 : ℕ) : ℤ) : ℤ) : ℝ) / 2 ^ 62 := by
    push_cast
    rw [sum_div]
    refine sum_congr rfl fun k _ => ?_
    simp only [testF, Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false, one_mul]
    ring
  have hz : (∑ k ∈ range 32, (Cl.getD (k + 1) 0) ^ 2 * ((k + 1 : ℕ) : ℤ)) * 10000 ≤
      7877 * 2 ^ 62 := by decide +kernel
  have hz' : (((∑ k ∈ range 32, (Cl.getD (k + 1) 0) ^ 2 * ((k + 1 : ℕ) : ℤ)) * 10000 : ℤ) : ℝ) ≤
      ((7877 * 2 ^ 62 : ℤ) : ℝ) := by exact_mod_cast hz
  rw [e, div_le_iff₀ (by positivity)]
  push_cast at hz' ⊢
  linarith

theorem testH_nonneg : 0 ≤ testT.H := by
  change 0 ≤ ∑ k ∈ range 32, testF (k + 1) ^ 2 * ((k + 1 : ℕ) : ℝ)
  exact sum_nonneg fun k _ => by positivity

theorem phase_rhs_le : Real.arctan (1 / 4) + 5 / 29 * Real.arctan 4 +
      (17 / 4) * (1 / 100) ^ 2 / (1 - (1 / 100) ^ 2) + 1 / 1000 ≤ 4752 / 10000 := by
  rw [arctan_four]
  have h1 := arctan_quarter_le
  have h2 := Real.pi_lt_d4
  norm_num
  linarith

/-- `G58` inside `[-1,1]`. -/
def G58in (y : ℝ) : Prop := G58 y ∧ y ∈ Set.Icc (-1 : ℝ) 1

theorem G58in_ord (y : ℝ) (h : G58in y) :
    (0 < y → y ∈ CapSource.ordDom Sign.pos) ∧ (y < 0 → -y ∈ CapSource.ordDom Sign.neg) := by
  obtain ⟨hg, h1, h2⟩ := h
  constructor
  · intro hy
    refine ⟨?_, h2⟩
    rcases hg with hg | hg
    · linarith
    · exact hg
  · intro hy
    refine ⟨?_, by linarith⟩
    rcases hg with hg | hg
    · linarith
    · linarith

theorem selected_restrict {P : CatalanMeasure.Parametric.Parameters} {ζ : ℝ} {δ : ℝ → ℝ}
    {target cost : ℝ} {G G' : ℝ → Prop}
    {Q : ∀ (N p m : ℕ), (Fin p → ℝ) → (Fin m → ℝ) → (Fin p → ℝ) → Prop}
    (h : ∀ y ∈ Set.Ioo (-1 : ℝ) 1, G y → G' y)
    (hs : SelectedFreeProductCostOnRestr P ζ δ target cost G' Q) :
    SelectedFreeProductCostOnRestr P ζ δ target cost G Q := by
  intro ε hε
  filter_upwards [hs ε hε] with N hN
  intro p m hpm x y s hx hx0 hy hy0 hyG hs' hzi hsi hcase hQ sel
  exact hN p m hpm x y s hx hx0 hy hy0 (fun j => h _ (hy j) (hyG j)) hs' hzi hsi hcase hQ sel

/-- The intercept of the completed gas at the two anchors. -/
def anchorVal (a : Fin 2) : ℝ := anchorIntercept (aB capSource a) (aT capSource a) (aV capSource a)


/-! ### Design-C T4 cover, layer 1: rational polynomials, a cover check, and the cell net

`QP` is a rational polynomial (constant term first).  `polyNonneg_of_ints` is what a leaf
module uses: it rescales `p` on `[A, B]` to `[0, 1]`, clears denominators in Python (integer list
`zs`) and runs `checkZ` from the root cell.  `net_cells` is Lemma 8.1 of the package in the form the cells of
`Family` need: a finite partition on which the diagonal check survives at the right end. -/


section CoverLayer
open Set

abbrev QP := List ℚ

def evalQ : QP → ℝ → ℝ
  | [], _ => 0
  | a :: p, x => (a : ℝ) + x * evalQ p x

def addQ : QP → QP → QP
  | [], q => q
  | a :: p, [] => a :: p
  | a :: p, b :: q => (a + b) :: addQ p q

def smulQ (c : ℚ) (p : QP) : QP := p.map (c * ·)

def mulQ : QP → QP → QP
  | [], _ => []
  | a :: p, q => addQ (smulQ a q) (0 :: mulQ p q)

/-- `p (A + B w)`. -/
def compQ (A B : ℚ) : QP → QP
  | [] => []
  | a :: p => addQ [a] (mulQ [A, B] (compQ A B p))

@[simp] theorem evalQ_nil (x : ℝ) : evalQ [] x = 0 := rfl
@[simp] theorem evalQ_cons (a : ℚ) (p : QP) (x : ℝ) : evalQ (a :: p) x = (a : ℝ) + x * evalQ p x := rfl

theorem evalQ_addQ (p q : QP) (x : ℝ) : evalQ (addQ p q) x = evalQ p x + evalQ q x := by
  induction p generalizing q with
  | nil => simp [addQ]
  | cons a p ih =>
    cases q with
    | nil => simp [addQ]
    | cons b q => simp only [addQ, evalQ_cons, ih]; push_cast; ring

theorem evalQ_smulQ (c : ℚ) (p : QP) (x : ℝ) : evalQ (smulQ c p) x = c * evalQ p x := by
  induction p with
  | nil => simp [smulQ]
  | cons a p ih =>
    simp only [smulQ, List.map_cons, evalQ_cons] at ih ⊢
    rw [ih]; push_cast; ring

theorem evalQ_mulQ (p q : QP) (x : ℝ) : evalQ (mulQ p q) x = evalQ p x * evalQ q x := by
  induction p with
  | nil => simp [mulQ]
  | cons a p ih =>
    simp only [mulQ, evalQ_addQ, evalQ_smulQ, evalQ_cons, ih]; ring

theorem evalQ_compQ (A B : ℚ) (p : QP) (w : ℝ) : evalQ (compQ A B p) w = evalQ p (A + B * w) := by
  induction p with
  | nil => simp [compQ]
  | cons a p ih =>
    simp only [compQ, evalQ_addQ, evalQ_mulQ, evalQ_cons, ih, evalQ_nil]; ring

/-- The statement a leaf proves. -/
def PolyNonneg (p : QP) (A B : ℚ) : Prop := ∀ x : ℝ, (A : ℝ) ≤ x → x ≤ B → 0 ≤ evalQ p x

/-- A leaf.  `zs` is the integer list of `w ↦ D · p (A + (B - A) w)` (the identity `hz` is proved by
`norm_num` on the coefficients; the kernel never does rational arithmetic, which it cannot
normalise in this setting), and `checkZ zs f 0 0` is the kernel check from the root cell. -/
theorem polyNonneg_of_ints {p : QP} {A B D : ℚ} (hAB : A < B) (hD : 0 < D) {zs : List ℤ} {f : ℕ}
    (hz : ∀ w : ℝ, evalZ zs w = D * evalQ p (A + (B - A) * w))
    (h : checkZ zs f 0 0 = true) : PolyNonneg p A B := by
  intro x hx1 hx2
  have hBA : (0 : ℝ) < (B : ℝ) - A := by
    have : (A : ℝ) < B := by exact_mod_cast hAB
    linarith
  set w : ℝ := (x - A) / ((B : ℝ) - A) with hw
  have hw0 : (0 : ℝ) / 2 ^ 0 ≤ w := by
    simp only [pow_zero, div_one, zero_div]; exact div_nonneg (by linarith) hBA.le
  have hw1 : w ≤ (((0 : ℤ) : ℝ) + 1) / 2 ^ 0 := by
    simp only [Int.cast_zero, zero_add, pow_zero, div_one]
    rw [hw, div_le_one hBA]; linarith
  have hz0 := checkZ_sound (m := 0) (s := 0) h (by simpa using hw0) hw1
  rw [hz] at hz0
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have hx : (A : ℝ) + ((B : ℝ) - A) * w = x := by
    rw [hw]; field_simp; ring
  rw [hx] at hz0
  by_contra hneg
  have := mul_neg_of_pos_of_neg hD' (not_le.mp hneg)
  linarith

/-- **Lemma 8.1, strict form.**  If `S` is continuous and positive on the diagonal of `[A, B]`,
the uniform partition into `n` cells has `S α b_i ≥ 0` for every `α` of the cell `i` (right end
`b_i`). -/
theorem net_cells {A B : ℝ} (hAB : A < B) {S : ℝ → ℝ → ℝ}
    (hS : ContinuousOn (fun q : ℝ × ℝ => S q.1 q.2) (Icc A B ×ˢ Icc A B))
    (hdiag : ∀ α ∈ Icc A B, 0 < S α α) :
    ∃ n : ℕ, 0 < n ∧ ∀ i : ℕ, i < n →
      ∀ α ∈ Icc (A + (B - A) * i / n) (A + (B - A) * (i + 1) / n),
        0 ≤ S α (A + (B - A) * (i + 1) / n) := by
  have hK : IsCompact (Icc A B) := isCompact_Icc
  have hd : ContinuousOn (fun α => S α α) (Icc A B) :=
    hS.comp (continuousOn_id.prodMk continuousOn_id) (fun α hα => ⟨hα, hα⟩)
  obtain ⟨α0, hα0, hmin⟩ := hK.exists_isMinOn ⟨A, left_mem_Icc.mpr hAB.le⟩ hd
  set η := S α0 α0 with hη
  have hηpos : 0 < η := hdiag α0 hα0
  have hKK : IsCompact (Icc A B ×ˢ Icc A B) := hK.prod hK
  have huc := hKK.uniformContinuousOn_of_continuous hS
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδ, hu⟩ := huc η hηpos
  obtain ⟨n, hn⟩ := exists_nat_gt ((B - A) / δ)
  have hn0 : 0 < n := by
    have : 0 < (B - A) / δ := div_pos (by linarith) hδ
    exact_mod_cast this.trans hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  refine ⟨n, hn0, fun i hi α hα => ?_⟩
  set h : ℝ := (B - A) / n with hh
  have hhδ : h < δ := by
    rw [hh, div_lt_iff₀ hnR]
    have := (div_lt_iff₀ hδ).mp hn
    linarith
  have hiR : (i : ℝ) + 1 ≤ n := by exact_mod_cast hi
  have hhpos : 0 < h := div_pos (by linarith) hnR
  have e1 : A + (B - A) * (i : ℝ) / n = A + h * i := by rw [hh]; ring
  have e2 : A + (B - A) * ((i : ℝ) + 1) / n = A + h * ((i : ℝ) + 1) := by rw [hh]; ring
  rw [e1, e2] at hα
  rw [e2]
  have hbB : A + h * ((i : ℝ) + 1) ≤ B := by
    have : h * ((i : ℝ) + 1) ≤ h * n := mul_le_mul_of_nonneg_left hiR hhpos.le
    have e : h * (n : ℝ) = B - A := by rw [hh]; field_simp
    linarith
  have hbA : A ≤ A + h * ((i : ℝ) + 1) := by
    have : 0 ≤ h * ((i : ℝ) + 1) := by positivity
    linarith
  have hαm : α ∈ Icc A B := ⟨by
    have : 0 ≤ h * (i : ℝ) := by positivity
    linarith [hα.1], by linarith [hα.2]⟩
  have hdist : dist (α, α) (α, A + h * ((i : ℝ) + 1)) < δ := by
    rw [Prod.dist_eq]
    simp only [dist_self, Real.dist_eq]
    refine max_lt hδ ?_
    rw [abs_of_nonpos (by linarith [hα.2])]
    have : h * ((i : ℝ) + 1) - h * (i : ℝ) = h := by ring
    linarith [hα.1]
  have hk := hu (α, α) ⟨hαm, hαm⟩ (α, A + h * ((i : ℝ) + 1)) ⟨hαm, hbA, hbB⟩ hdist
  rw [Real.dist_eq] at hk
  have h1 := (abs_lt.mp hk).2
  have h2 : η ≤ S α α := hmin hαm
  simp only at h1
  linarith

end CoverLayer

/-! ### Layer 2: GP §9(a), the signed budget on `[0, α₁]`

The literals of the signed cover (`SigLits`) are parameters: the cap literals `c₀ᴿ … c₂ᶜ` are F until
the certified row, `I₁` is `GasEnergyHi.hi_final`, and `L₀ … Q₁₁` are the moved-intercept moments of
`anchorIntercept_move` (E2).  The check polynomials `sigP1`, `sigP2` are `σ α − η − V` for the two
pieces `[0, α_e]` (with `t = α/α_e`) and `[α_e, α₁]`; a leaf proves `PolyNonneg` of each by
`polyNonneg_of_ints`. -/

section SignedCover
open Set CatalanMeasure.GenD CatalanMeasure.GenD.D58

def hiQ : ℚ := 6931471808 / 10000000000
def tQ : ℚ := 563964709 / 250000000 + (616 / 25) / 3364
def c2Q : ℚ := 3596893 / 1000000
def MQ : ℚ := -976 / 1000
def aeQ : ℚ := 1 / 25
def a1Q : ℚ := 51 / 500

structure SigLits where
  σ : ℚ
  η : ℚ
  I1 : ℚ
  L0 : ℚ
  L1 : ℚ
  Q00 : ℚ
  Q01 : ℚ
  Q11 : ℚ
  c0R : ℚ
  c1R : ℚ
  c0C : ℚ
  c1C : ℚ
  c2C : ℚ

theorem T296_eq' : T296 = (tQ : ℝ) := by
  norm_num [T296, K590.target, shift296, tQ]

/-- `V_S = Bud − σ α` at the cell constants (`J` the intercept plus gas constant, `r`, `c` the row and
column caps), with `log 2` replaced by its upper bound and the marked cap by `-976/1000`. -/
def sigV (J r c α : ℝ) : ℝ :=
  J - 3 / 2 * α ^ 2 * hiQ + (1 - α) * (r + c) + α * MQ +
    hiQ * (75 / 58 * (1 - α) + (1 - α) ^ 2 / 2 + 53 / 58 * α) + tQ - hiQ / 2 - c2Q * α

/-- Piece 1, `α ∈ [0, α_e]`, `t = β / α_e`. -/
def sigJ1 (l : SigLits) (β : ℝ) : ℝ :=
  (l.I1 + l.L0 + l.Q00) + (β / aeQ) * (l.L1 + 2 * l.Q01) + (β / aeQ) ^ 2 * l.Q11
def sigR1 (l : SigLits) (β : ℝ) : ℝ := l.c0R + (β / aeQ) * (l.c1R - l.c0R)
def sigC1 (l : SigLits) (β : ℝ) : ℝ := l.c0C + (β / aeQ) * (l.c1C - l.c0C)
/-- Piece 2, `α ∈ [α_e, α₁]`, `τ = 1`, `u = (β - α_e) / (α₁ - α_e)`. -/
def sigJ2 (l : SigLits) : ℝ := l.I1 + l.L0 + l.Q00 + l.L1 + 2 * l.Q01 + l.Q11
def sigC2 (l : SigLits) (β : ℝ) : ℝ := l.c1C + ((β - aeQ) / (a1Q - aeQ)) * (l.c2C - l.c1C)

/-- The polynomial `α ↦ V_S(α)` of the two pieces, as `QP`. -/
def sigVq (J r c : QP) : QP :=
  addQ J (addQ (smulQ (-(3 / 2) * hiQ) (mulQ [0, 1] [0, 1]))
    (addQ (mulQ [1, -1] (addQ r c))
      (addQ (smulQ MQ [0, 1])
        (addQ (smulQ hiQ (addQ (smulQ (75 / 58) [1, -1]) (addQ (smulQ (1 / 2) (mulQ [1, -1] [1, -1]))
          (smulQ (53 / 58) [0, 1]))))
          [tQ - hiQ / 2, -c2Q]))))

theorem evalQ_sigVq (J r c : QP) (α : ℝ) :
    evalQ (sigVq J r c) α = sigV (evalQ J α) (evalQ r α) (evalQ c α) α := by
  simp only [sigVq, sigV, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil]
  push_cast
  ring

def sigJ1q (l : SigLits) : QP :=
  [l.I1 + l.L0 + l.Q00, 25 * (l.L1 + 2 * l.Q01), 625 * l.Q11]
def sigR1q (l : SigLits) : QP := [l.c0R, 25 * (l.c1R - l.c0R)]
def sigC1q (l : SigLits) : QP := [l.c0C, 25 * (l.c1C - l.c0C)]
def sigC2q (l : SigLits) : QP :=
  [l.c1C - aeQ / (a1Q - aeQ) * (l.c2C - l.c1C), (l.c2C - l.c1C) / (a1Q - aeQ)]

/-- The check polynomial of piece 1: `σ α − η − V_S`. -/
def sigP1 (l : SigLits) : QP :=
  addQ [-l.η] (addQ (smulQ l.σ [0, 1]) (smulQ (-1) (sigVq (sigJ1q l) (sigR1q l) (sigC1q l))))
def sigP2 (l : SigLits) : QP :=
  addQ [-l.η] (addQ (smulQ l.σ [0, 1]) (smulQ (-1) (sigVq [l.I1 + l.L0 + l.Q00 + l.L1 + 2 * l.Q01 + l.Q11]
    [l.c1R] (sigC2q l))))

theorem sigP1_eval (l : SigLits) (α : ℝ) :
    evalQ (sigP1 l) α = l.σ * α - l.η - sigV (sigJ1 l α) (sigR1 l α) (sigC1 l α) α := by
  simp only [sigP1, evalQ_addQ, evalQ_smulQ, evalQ_sigVq, evalQ_cons, evalQ_nil, sigJ1q, sigR1q,
    sigC1q, sigJ1, sigR1, sigC1, aeQ]
  push_cast
  ring_nf

theorem sigP2_eval (l : SigLits) (α : ℝ) :
    evalQ (sigP2 l) α = l.σ * α - l.η - sigV (sigJ2 l) l.c1R (sigC2 l α) α := by
  simp only [sigP2, evalQ_addQ, evalQ_smulQ, evalQ_sigVq, evalQ_cons, evalQ_nil, sigC2q, sigC2,
    sigJ2, aeQ, a1Q]
  push_cast
  ring_nf

/-- **Piece 1 of GP §9(a).**  The check on `[0, α_e]` gives a partition on which the budget polynomial
at the cell constants (taken at the right end `b_i`, `τ_i = b_i / α_e`, `γ_i = b_i`) is `≤ σ α`. -/
theorem sig_cells1 (l : SigLits) (hη : 0 < l.η) (hP : PolyNonneg (sigP1 l) 0 aeQ) :
    ∃ n : ℕ, 0 < n ∧ ∀ i : ℕ, i < n →
      ∀ α ∈ Icc (0 + ((aeQ : ℝ) - 0) * i / n) (0 + ((aeQ : ℝ) - 0) * (i + 1) / n),
        sigV (sigJ1 l (0 + ((aeQ : ℝ) - 0) * (i + 1) / n)) (sigR1 l (0 + ((aeQ : ℝ) - 0) * (i + 1) / n))
          (sigC1 l (0 + ((aeQ : ℝ) - 0) * (i + 1) / n)) α ≤ l.σ * α := by
  have hae : (0 : ℝ) < aeQ := by norm_num [aeQ]
  obtain ⟨n, hn, h⟩ := net_cells (A := 0) (B := (aeQ : ℝ)) hae
    (S := fun α β => l.σ * α - sigV (sigJ1 l β) (sigR1 l β) (sigC1 l β) α)
    (by unfold sigV sigJ1 sigR1 sigC1; fun_prop)
    (fun α hα => by
      have := hP α (by simpa using hα.1) (by exact hα.2)
      rw [sigP1_eval] at this
      beta_reduce
      have hη' : (0 : ℝ) < l.η := by exact_mod_cast hη
      linarith)
  exact ⟨n, hn, fun i hi α hα => by have := h i hi α hα; beta_reduce at this; linarith⟩

theorem sig_cells2 (l : SigLits) (hη : 0 < l.η) (hP : PolyNonneg (sigP2 l) aeQ a1Q) :
    ∃ n : ℕ, 0 < n ∧ ∀ i : ℕ, i < n →
      ∀ α ∈ Icc ((aeQ : ℝ) + ((a1Q : ℝ) - aeQ) * i / n) ((aeQ : ℝ) + ((a1Q : ℝ) - aeQ) * (i + 1) / n),
        sigV (sigJ2 l) l.c1R (sigC2 l ((aeQ : ℝ) + ((a1Q : ℝ) - aeQ) * (i + 1) / n)) α ≤ l.σ * α := by
  have hae : (aeQ : ℝ) < a1Q := by norm_num [aeQ, a1Q]
  obtain ⟨n, hn, h⟩ := net_cells (A := (aeQ : ℝ)) (B := (a1Q : ℝ)) hae
    (S := fun α β => l.σ * α - sigV (sigJ2 l) l.c1R (sigC2 l β) α)
    (by unfold sigV sigC2; fun_prop)
    (fun α hα => by
      have := hP α hα.1 hα.2
      rw [sigP2_eval] at this
      beta_reduce
      have hη' : (0 : ℝ) < l.η := by exact_mod_cast hη
      linarith)
  exact ⟨n, hn, fun i hi α hα => by have := h i hi α hα; beta_reduce at this; linarith⟩

/-- From `V_S ≤ σ α` to the budget of `capBudget` at `b = 1`. -/
theorem budget_of_sigV {ℓ J M r c α I gI σ : ℝ} (hlo : 6931471803 / 10000000000 < ℓ)
    (hhi : ℓ < 6931471808 / 10000000000) (hα0 : 0 ≤ α) (hα1 : α ≤ 51 / 500)
    (hM : M ≤ -976 / 1000) (hJ : I + gI ≤ J) (hV : sigV J r c α ≤ σ * α) :
    I - 3 / 2 * (1 - α - 1) ^ 2 * ℓ + (1 - α) * (r + c) + α * M +
        ℓ * (75 / 58 * (1 - α) + (1 - α) ^ 2 / 2 + 53 / 58 * α) + gI ≤
      -((tQ : ℝ)) + ℓ / 2 + (c2Q + σ) * α := by
  unfold sigV at hV
  have hκ : 0 ≤ -(3 / 2) * α ^ 2 + 75 / 58 * (1 - α) + (1 - α) ^ 2 / 2 + 53 / 58 * α - 1 / 2 := by
    nlinarith
  have h1 : (ℓ - hiQ) * (-(3 / 2) * α ^ 2 + 75 / 58 * (1 - α) + (1 - α) ^ 2 / 2 + 53 / 58 * α - 1 / 2) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by norm_num [hiQ] at *; linarith) hκ
  have h2 : α * M ≤ α * MQ := mul_le_mul_of_nonneg_left (by norm_num [MQ]; linarith) hα0
  norm_num [hiQ, MQ, c2Q] at h1 h2 hV ⊢
  nlinarith [h1, h2, hV, hJ]

end SignedCover

/-! ### Layer 3: the unsigned cells, GP §9(b), (c), (d), (e)

All four are one real function.  With the cell constants `nC` (norm cap), `fC` (field cap), `rs`
(residual), `np` (`NP = ℓ + nearCap`) and `ℓ ≥ lo`,
`wV nC fC rs np α = (coefficient of log 2)·lo + T′ − c₂ α + nC + (1−α) fC + α rs + (np − rs)²/(4 lo)`
bounds the budget minus `(c₂ + σ) α − ℓ/2` for every `t` (AM-GM in `t`).  The first-case budget
(e) is the instance `np = rs = M₁`.  The check polynomials are built from `QP`s that give the four
constants as polynomials in the variable (`τ(α)` and `Ŷ(α)` are polynomials on a piece). -/

section UnsignedCover
open Set CatalanMeasure.GenD CatalanMeasure.GenD.D58 CatalanMeasure.GenD.Analytic CatalanMeasure.Parametric
  CatalanMeasure.GenD.Signed.RouteI.CompletedGas

def loQ : ℚ := 6931471803 / 10000000000

theorem continuous_evalQ (p : QP) : Continuous (evalQ p) := by
  induction p with
  | nil => simpa [evalQ] using continuous_const
  | cons a p ih =>
    have e : evalQ (a :: p) = fun x => (a : ℝ) + x * evalQ p x := rfl
    rw [e]; exact continuous_const.add (continuous_id.mul ih)

/-- The diagonal function of §9(b), (c), (e). -/
def wV (nC fC rs np α : ℝ) : ℝ :=
  (-(6 / 29) - 1 / 2 + 47 / 29 * α - α ^ 2) * loQ + tQ - c2Q * α + nC + (1 - α) * fC + α * rs +
    (np - rs) ^ 2 / (4 * loQ)

def wVq (nC fC rs np : QP) : QP :=
  addQ [(-(6 / 29) - 1 / 2) * loQ + tQ, (47 / 29 * loQ - c2Q), -loQ]
    (addQ nC (addQ (mulQ [1, -1] fC) (addQ (mulQ [0, 1] rs)
      (smulQ (1 / (4 * loQ)) (mulQ (addQ np (smulQ (-1) rs)) (addQ np (smulQ (-1) rs)))))))

theorem evalQ_wVq (nC fC rs np : QP) (α : ℝ) :
    evalQ (wVq nC fC rs np) α = wV (evalQ nC α) (evalQ fC α) (evalQ rs α) (evalQ np α) α := by
  simp only [wVq, wV, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil]
  push_cast
  field_simp
  ring

/-- The check polynomial of a piece: `σ α + Δ − η − wV`. -/
def wPq (σ η Δ : ℚ) (nC fC rs np : QP) : QP :=
  addQ [Δ - η] (addQ (smulQ σ [0, 1]) (smulQ (-1) (wVq nC fC rs np)))

theorem wPq_eval (σ η Δ : ℚ) (nC fC rs np : QP) (α : ℝ) :
    evalQ (wPq σ η Δ nC fC rs np) α =
      σ * α + Δ - η - wV (evalQ nC α) (evalQ fC α) (evalQ rs α) (evalQ np α) α := by
  simp only [wPq, evalQ_addQ, evalQ_smulQ, evalQ_wVq, evalQ_cons, evalQ_nil]
  push_cast
  ring

/-- **A piece of the unsigned cover.**  The check on `[A, B]` gives a partition on which `wV` at the
cell constants (evaluated at the right end `b_i`) is `≤ σ α + Δ`. -/
theorem wV_cells {A B : ℚ} (hAB : A < B) {σ η Δ : ℚ} (hη : 0 < η) {nC fC rs np : QP}
    (hP : PolyNonneg (wPq σ η Δ nC fC rs np) A B) :
    ∃ n : ℕ, 0 < n ∧ ∀ i : ℕ, i < n →
      ∀ α ∈ Icc ((A : ℝ) + ((B : ℝ) - A) * i / n) ((A : ℝ) + ((B : ℝ) - A) * (i + 1) / n),
        wV (evalQ nC ((A : ℝ) + ((B : ℝ) - A) * (i + 1) / n))
          (evalQ fC ((A : ℝ) + ((B : ℝ) - A) * (i + 1) / n))
          (evalQ rs ((A : ℝ) + ((B : ℝ) - A) * (i + 1) / n))
          (evalQ np ((A : ℝ) + ((B : ℝ) - A) * (i + 1) / n)) α ≤ σ * α + Δ := by
  have hAB' : (A : ℝ) < B := by exact_mod_cast hAB
  have hη' : (0 : ℝ) < η := by exact_mod_cast hη
  obtain ⟨n, hn, h⟩ := net_cells hAB' (S := fun α β => σ * α + Δ -
      wV (evalQ nC β) (evalQ fC β) (evalQ rs β) (evalQ np β) α)
    (by
      unfold wV
      have := continuous_evalQ nC; have := continuous_evalQ fC
      have := continuous_evalQ rs; have := continuous_evalQ np
      fun_prop)
    (fun α hα => by
      have := hP α hα.1 hα.2
      rw [wPq_eval] at this
      beta_reduce
      linarith)
  exact ⟨n, hn, fun i hi α hα => by have := h i hi α hα; beta_reduce at this; linarith⟩

/-- `wV ≤ σ α + Δ` gives the second-case budget / the `hΔ` of the window: for every `t` (`β`). -/
theorem oldBound_budget_of_wV {P : Parameters} (hg0 : gC0 P = 6 / 29) (hg1 : gC1 P = 47 / 29)
    {ℓ nC fC rs np α β σ Δ : ℝ} (hℓd : ℓ = Real.log 2) (hlo : (loQ : ℝ) < ℓ)
    (hV : wV nC fC rs np α ≤ σ * α + Δ) :
    oldBound P nC fC rs (np - ℓ) α β ≤ -(tQ : ℝ) + ℓ / 2 + (c2Q + σ) * α + Δ := by
  have hlo0 : (0 : ℝ) < loQ := by norm_num [loQ]
  have hℓ : 0 < ℓ := hlo0.trans hlo
  unfold oldBound
  rw [hg0, hg1, ← hℓd]
  have hco : -(6 / 29 : ℝ) - 1 / 2 + 47 / 29 * α - α ^ 2 ≤ 0 := by nlinarith [sq_nonneg (α - 47 / 58)]
  have h1 : (-(6 / 29 : ℝ) - 1 / 2 + 47 / 29 * α - α ^ 2) * ℓ ≤
      (-(6 / 29 : ℝ) - 1 / 2 + 47 / 29 * α - α ^ 2) * loQ :=
    mul_le_mul_of_nonpos_left hlo.le hco
  have hc : (np - rs) ^ 2 / (4 * ℓ) ≤ (np - rs) ^ 2 / (4 * loQ) :=
    div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by linarith)
  have hq : 0 ≤ (np - rs - 2 * β * ℓ) ^ 2 / (4 * ℓ) := by positivity
  have he : (np - rs - 2 * β * ℓ) ^ 2 / (4 * ℓ) =
      (np - rs) ^ 2 / (4 * ℓ) - β * (np - rs) + β ^ 2 * ℓ := by
    field_simp; ring
  unfold wV at hV
  linarith [h1, hc, hq, he, hV]

/-- The first-case budget (e) from `wV` with `np = rs = M₁`. -/
theorem first_budget_of_wV {P : Parameters} (hg0 : gC0 P = 6 / 29) (hg1 : gC1 P = 47 / 29)
    {ℓ nC fC M1 α σ : ℝ} (hlo : (loQ : ℝ) < ℓ)
    (hV : wV nC fC M1 M1 α ≤ σ * α + 0) :
    (-gC0 P + gC1 P * α - α ^ 2) * ℓ + nC + (1 - α) * fC + α * M1 ≤
      -(tQ : ℝ) + ℓ / 2 + (c2Q + σ) * α := by
  rw [hg0, hg1]
  have hco : -(6 / 29 : ℝ) - 1 / 2 + 47 / 29 * α - α ^ 2 ≤ 0 := by nlinarith [sq_nonneg (α - 47 / 58)]
  have h1 : (-(6 / 29 : ℝ) - 1 / 2 + 47 / 29 * α - α ^ 2) * ℓ ≤
      (-(6 / 29 : ℝ) - 1 / 2 + 47 / 29 * α - α ^ 2) * loQ :=
    mul_le_mul_of_nonpos_left hlo.le hco
  unfold wV at hV
  simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div,
    add_zero] at hV
  nlinarith [h1, hV]

end UnsignedCover

/-! ### Layer 4: the physical window, GP §9(c), (d): the three consumer hypotheses on one cell

On a step `[a, b]` of the 64-step cover of `[0, α₁]` the deficit is the constant `Δ` and the trial
parameter of a cell is `τ = b_i / α₁`.  One partition serves `hΔ` (through `wV`), `hphase` and
`hone`: the slack of each is continuous, positive on the diagonal, and the three are
combined by `min`. -/

section PhysicalCover
open Set CatalanMeasure.GenD CatalanMeasure.GenD.D58 CatalanMeasure.GenD.Analytic
  CatalanMeasure.Parametric CatalanMeasure.GenD.Signed.RouteI.CompletedGas

/-- Phase slack at the cell: `F₀/2 − F₀ α/4 + U + τ·FU − s − .4752`, `τ = β/α₁`. -/
def phiS (F0 U FU s : ℝ) (α β : ℝ) : ℝ :=
  F0 / 2 - F0 * α / 4 + U + (β / a1Q) * FU - s - 4752 / 10000

/-- `hone` slack: `5/6·48/58 − [1 − (1 − α + p₂ − s')/2 + 1/1000]`, `p₂ = p₀₂ + τ du₂`. -/
def omS (p2 du2 s' : ℝ) (α β : ℝ) : ℝ :=
  5 / 6 * (48 / 58) - (1 - (1 - α + (p2 + (β / a1Q) * du2) - s') / 2 + 1 / 1000)

def phiQ (F0 U FU s : ℚ) : QP := [F0 / 2 + U - s - 4752 / 10000, -F0 / 4 + FU / a1Q]
def omQ (p2 du2 s' : ℚ) : QP :=
  [5 / 6 * (48 / 58) - 1 + (1 + p2 - s') / 2 - 1 / 1000, (-1 + du2 / a1Q) / 2]

theorem evalQ_phiQ (F0 U FU s : ℚ) (α : ℝ) :
    evalQ (phiQ F0 U FU s) α = phiS F0 U FU s α α := by
  simp only [phiQ, phiS, evalQ_cons, evalQ_nil]; push_cast; ring

theorem evalQ_omQ (p2 du2 s' : ℚ) (α : ℝ) :
    evalQ (omQ p2 du2 s') α = omS p2 du2 s' α α := by
  simp only [omQ, omS, evalQ_cons, evalQ_nil]; push_cast; ring

/-- **One step of the physical window.**  `PolyNonneg` of the three diagonal polynomials on `[A, B]`
gives one partition with `hΔ` (as `wV`), `hphase` and `hone` slacks nonnegative at the cell
constants, each `α` of the cell, `τ_i = b_i / α₁`. -/
theorem phys_cells {A B : ℚ} (hAB : A < B) {σ η Δ : ℚ} (hη : 0 < η) {nC fC rs np : QP}
    {F0 U FU s p2 du2 s' : ℚ}
    (hP : PolyNonneg (wPq σ η Δ nC fC rs np) A B)
    (hφ : PolyNonneg (addQ [-η] (phiQ F0 U FU s)) A B)
    (hω : PolyNonneg (addQ [-η] (omQ p2 du2 s')) A B) :
    ∃ n : ℕ, 0 < n ∧ ∀ i : ℕ, i < n →
      ∀ α ∈ Icc ((A : ℝ) + ((B : ℝ) - A) * i / n) ((A : ℝ) + ((B : ℝ) - A) * (i + 1) / n),
        wV (evalQ nC ((A : ℝ) + ((B : ℝ) - A) * (i + 1) / n))
          (evalQ fC ((A : ℝ) + ((B : ℝ) - A) * (i + 1) / n))
          (evalQ rs ((A : ℝ) + ((B : ℝ) - A) * (i + 1) / n))
          (evalQ np ((A : ℝ) + ((B : ℝ) - A) * (i + 1) / n)) α ≤ σ * α + Δ ∧
        0 ≤ phiS F0 U FU s α ((A : ℝ) + ((B : ℝ) - A) * (i + 1) / n) ∧
        0 ≤ omS p2 du2 s' α ((A : ℝ) + ((B : ℝ) - A) * (i + 1) / n) := by
  have hAB' : (A : ℝ) < B := by exact_mod_cast hAB
  have hη' : (0 : ℝ) < η := by exact_mod_cast hη
  have ha1 : (a1Q : ℝ) ≠ 0 := by norm_num [a1Q]
  obtain ⟨n, hn, h⟩ := net_cells hAB'
    (S := fun α β => min (σ * α + Δ - wV (evalQ nC β) (evalQ fC β) (evalQ rs β) (evalQ np β) α)
      (min (phiS F0 U FU s α β) (omS p2 du2 s' α β)))
    (by
      unfold wV phiS omS
      have := continuous_evalQ nC; have := continuous_evalQ fC
      have := continuous_evalQ rs; have := continuous_evalQ np
      fun_prop)
    (fun α hα => by
      have h1 := hP α hα.1 hα.2
      rw [wPq_eval] at h1
      have h2 := hφ α hα.1 hα.2
      rw [evalQ_addQ, evalQ_phiQ] at h2
      have h3 := hω α hα.1 hα.2
      rw [evalQ_addQ, evalQ_omQ] at h3
      simp only [evalQ_cons, evalQ_nil, mul_zero, add_zero] at h2 h3
      push_cast at h2 h3
      beta_reduce
      refine lt_min (by linarith) (lt_min (by linarith) (by linarith)))
  refine ⟨n, hn, fun i hi α hα => ?_⟩
  have := h i hi α hα
  beta_reduce at this
  have h1 := (le_min_iff.mp this).1
  have h2 := (le_min_iff.mp (le_min_iff.mp this).2).1
  have h3 := (le_min_iff.mp (le_min_iff.mp this).2).2
  exact ⟨by linarith, h2, h3⟩

/-- `hphase` from the slack: the arithmetic of `T4Instance.phase_margin` with the constants of a cell.
`Ssum` is `∑' F_{k+1} p(k+1)` (at least `U + τ·FU`) and `sqrt (H Δ / 2) ≤ s`. -/
theorem hphase_arith {F0 U FU s τ α Hh Δ Ssum : ℝ} (hS : U + τ * FU ≤ Ssum)
    (hs : Real.sqrt (Hh * (Δ / 2)) ≤ s)
    (hsl : 0 ≤ F0 / 2 - F0 * α / 4 + U + τ * FU - s - 4752 / 10000) {RHS : ℝ}
    (hR : RHS ≤ 4752 / 10000) :
    RHS ≤ F0 / 2 + Ssum - Real.sqrt (Hh * (Δ / 2)) - α * F0 / 4 - 0 * (Δ / 1) := by
  linarith

/-- `hone` from the slack. -/
theorem hone_arith {α p2 Δ s' : ℝ} {p2lo : ℝ} (hp : p2lo ≤ p2) (hs : Real.sqrt (2 * (Δ / 2)) ≤ s')
    (hsl : 0 ≤ 5 / 6 * (48 / 58) - (1 - (1 - α + p2lo - s') / 2 + 1 / 1000)) :
    1 - (1 - α + p2 - Real.sqrt (2 * (Δ / 2))) / 2 + 1 / 1000 ≤ 5 / 6 * (48 / 58) := by
  linarith

end PhysicalCover

/-! ### Layer 5: the signed cell against the built consumer `selected_comparison`

`hbud_of_sigV` is the `hbud` of `selected_comparison` / `selected_free_product` for one cell, from
the diagonal polynomial bound `sigV ≤ σ α` of `sig_cells1/2`; `hI_of_moves` is its `hI` at the moved
anchor `(a + da⁰ + τ da¹, v + dv⁰ + τ dv¹)` from the E2 moment bounds.  The cell constants are
`J` (intercept cap plus gas constant), `r`, `c` (chord caps of `chord_row`, `chord_col`,
`chord_col_gamma`). -/

section SignedConsumer
open Set CatalanMeasure.GenD.Signed.RouteI.CompletedGas CatalanMeasure.GenD.Signed.RouteI.CapFields

theorem hbud_of_sigV {S : CapSource} {d : ℝ → ℝ} {G : ℝ → Prop} {gasI : ℝ} {anchI : Fin 2 → ℝ}
    (B : S.CapBundle Trunc.exact d G gasI anchI) {b I r c J α σ : ℝ} (hb : b = 1)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 51 / 500) (hM : markCap B ≤ -976 / 1000)
    (hJ : I + B.gasICap ≤ J) (hV : sigV J r c α ≤ σ * α) :
    capBudget B b I r c α ≤ -(tQ : ℝ) + Real.log 2 / 2 + (c2Q + σ) * α := by
  subst hb
  have hlo := Real.log_two_gt_d9
  have hhi := Real.log_two_lt_d9
  unfold capBudget
  exact budget_of_sigV (by norm_num at hlo ⊢; linarith) (by norm_num at hhi ⊢; linarith)
    hα0 hα1 hM hJ hV

/-- The moved intercept (GP Lemma 5.1) against the E2 bounds. -/
theorem hI_of_moves (b : ℝ) {a v da0 da1 dv0 dv1 : ℕ → ℝ} {K : ℕ}
    (ha : Summable (fun k : ℕ => a (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)))
    (hv : Summable (fun k : ℕ => v (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)))
    (ha0 : ∀ k, K ≤ k → da0 k = 0) (ha1 : ∀ k, K ≤ k → da1 k = 0)
    (hv0 : ∀ k, K ≤ k → dv0 k = 0) (hv1 : ∀ k, K ≤ k → dv1 k = 0)
    {L0 L1 Q00 Q01 Q11 τ : ℝ} (hτ : 0 ≤ τ)
    (hL0 : 2 * barrierInner a da0 + barrierInner v dv0 ≤ L0)
    (hL1 : 2 * barrierInner a da1 + barrierInner v dv1 ≤ L1)
    (hQ00 : barrierInner da0 da0 + barrierInner dv0 dv0 / 2 = Q00)
    (hQ01 : barrierInner da0 da1 + barrierInner dv0 dv1 / 2 = Q01)
    (hQ11 : barrierInner da1 da1 + barrierInner dv1 dv1 / 2 = Q11) :
    anchorIntercept b (fun k => a k + (da0 k + τ * da1 k)) (fun k => v k + (dv0 k + τ * dv1 k)) ≤
      anchorIntercept b a v + (L0 + Q00) + τ * (L1 + 2 * Q01) + τ ^ 2 * Q11 := by
  rw [anchorIntercept_move b ha hv ha0 ha1 hv0 hv1 τ, hQ00, hQ11]
  have : τ * (2 * barrierInner a da1 + barrierInner v dv1 + 2 * (barrierInner da0 da1 + barrierInner dv0 dv1 / 2)) ≤
      τ * (L1 + 2 * Q01) := by
    rw [hQ01]; exact mul_le_mul_of_nonneg_left (by linarith) hτ
  nlinarith [this]

end SignedConsumer

/-! ### The design-C instance helpers

`I1_cap` is `GasEnergyHi.hi_final` in the form `selected_comparison` consumes (`hI`, `hgas`):
the intercept of the source anchor plus the gas constant is at most `2366997/10^6`.  `bundle0`
packages the anchor-`0` caps with the cap bundle of design C (`d`, `G`). -/

theorem I1_cap : anchorVal 0 + gasConst capSource ≤ 2366997 / 1000000 := by
  have e : anchorVal 0 = -CatalanMeasure.GenD.Signed.RouteI.InterceptSource.refQuad capSource 0 :=
    anchorIntercept_refQuad capSource_admissible colCell_capSource 0
  rw [e]
  exact CatalanMeasure.GenD.Signed.RouteI.GasEnergy.hi_final

theorem row_cap_exists (a : Fin 2) : ∃ c, capSource.FreeRowCap Trunc.exact a c := by
  obtain ⟨H, hH⟩ := free_row_bounded colCell_capSource capSource_admissible a
  refine ⟨max (H + 3 / 29 * Real.log 2) (capSource.freeRow Trunc.exact a (-1)), fun x hx => ?_⟩
  by_cases hm : x = -1
  · rw [hm]
    exact le_max_right _ _
  refine le_trans ?_ (le_max_left _ _)
  have hx1 : x ∈ Set.Ioo (-1 : ℝ) 1 := by
    rcases hx with h | h
    · exact ⟨lt_of_le_of_ne h.1 (Ne.symm hm), by linarith [h.2]⟩
    · exact ⟨by linarith [h.1], h.2⟩
  have hx0 : x ≠ 0 := by
    rcases hx with h | h
    · exact h.2.ne
    · exact h.1.ne'
  have h := hH x hx1 hx0
  have l1 : Real.log (1 - x) ≤ Real.log 2 :=
    Real.log_le_log (by linarith [hx1.2]) (by linarith [hx1.1])
  have l2 : Real.log |x| ≤ 0 :=
    Real.log_nonpos (abs_nonneg x) (abs_le.mpr ⟨hx1.1.le, hx1.2.le⟩)
  linarith

theorem col_cap_exists (a : Fin 2) : ∃ c, capSource.FreeColCap a c := by
  obtain ⟨H, hH⟩ := free_col_bounded colCell_capSource capSource_admissible a
  refine ⟨H, fun s hs => ?_⟩
  have h := hH s hs
  have l : Real.log (1 - s) ≤ 0 :=
    Real.log_nonpos (by linarith [hs.2]) (by linarith [hs.1])
  linarith

/-- The cap bundle from the anchor-`0` caps.  The intercept caps are the intercepts. -/
def bundle0 {d : ℝ → ℝ} {G : ℝ → Prop} {R C nc : ℝ} {oc : Sign → ℝ}
    (hR : capSource.FreeRowCap Trunc.exact 0 R)
    (hC : capSource.FreeColCap 0 C) (ho : ∀ σ, capSource.OrdCap Trunc.exact σ d G (oc σ))
    (hn : capSource.NearCap Trunc.exact d G nc)
    (ha : ∀ σ, capSource.AngCap Trunc.exact σ (kappa σ)) :
    capSource.CapBundle Trunc.exact d G (gasConst capSource) anchorVal where
  rowCap := ![R, Classical.choose (row_cap_exists 1)]
  colCap := ![C, Classical.choose (col_cap_exists 1)]
  ordCap := oc
  nearCap := nc
  angCap := kappa
  gasICap := gasConst capSource
  anchICap := anchorVal
  row a := by
    fin_cases a
    · exact hR
    · exact Classical.choose_spec (row_cap_exists 1)
  col a := by
    fin_cases a
    · exact hC
    · exact Classical.choose_spec (col_cap_exists 1)
  ord := ho
  near := hn
  ang := ha
  gasI_le := le_rfl
  anchI_le _ := le_rfl


end
end CatalanMeasure.GenD.Signed.RouteI.T4Instance

#print axioms CatalanMeasure.GenD.Signed.RouteI.T4Instance.sig_cells1
#print axioms CatalanMeasure.GenD.Signed.RouteI.T4Instance.sig_cells2
#print axioms CatalanMeasure.GenD.Signed.RouteI.T4Instance.hbud_of_sigV
#print axioms CatalanMeasure.GenD.Signed.RouteI.T4Instance.hI_of_moves
#print axioms CatalanMeasure.GenD.Signed.RouteI.T4Instance.wV_cells
#print axioms CatalanMeasure.GenD.Signed.RouteI.T4Instance.oldBound_budget_of_wV
#print axioms CatalanMeasure.GenD.Signed.RouteI.T4Instance.first_budget_of_wV
#print axioms CatalanMeasure.GenD.Signed.RouteI.T4Instance.phys_cells
#print axioms CatalanMeasure.GenD.Signed.RouteI.T4Instance.I1_cap
#print axioms CatalanMeasure.GenD.Signed.RouteI.T4Instance.anchorIntercept_refQuad
