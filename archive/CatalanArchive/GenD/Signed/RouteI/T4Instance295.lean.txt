module

public import CatalanMeasure.GenD.Signed.RouteI.CompletedGasTangent
public import CatalanMeasure.GenD.Signed.RouteI.CapSourceData
public import CatalanMeasure.GenD.Signed.RouteI.InterceptSource
public import CatalanMeasure.GenD.Signed.RouteI.Literals
public import CatalanMeasure.GenD.DesignInstance.PositiveCert.Data

@[expose] public section

/-!
# Route I `T4Instance`: `selected_free_product` at `capSource`

The concrete test and the instance of the near bound at the source record of `CapSourceData`.

* A polynomial phase test of Chebyshev degree `32` with `a₀ = h₀ = 0`: the test is nonpositive on
  all of `[-1,0]`, so the negative mid zone and its drop certificate do not arise.  Its three
  minorants are certified by an exact integer subdivision check (`checkZ`).
* `anchorIntercept_refQuad`: PROOF-RI 12.26, the anchor intercept in moment form is
  `- refQuad`.
* `selected_free_capSource`, `freeNear_capSource`: the instance.  The budget uses anchor `0` alone,
  with the retained mass square.
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

/-! ### The deficit -/

/-- The piecewise deficit. -/
def phaseDelta (α : ℝ) : ℝ := if α ≤ 143 / 2000 then 11 / 1600 else 177 / 50000

theorem T296_eq : T296 = 563964709 / 250000000 + 57783 / 2500 / 58 ^ 2 := by
  norm_num [T296, K590.target, shift296]

theorem delta_bound {Nc Fc r nc α β : ℝ} (hN : Nc ≤ 1547241039 / 2000000000)
    (hF : Fc ≤ -253949899 / 100000000) (hr : r ≤ -315531 / 5000000) (hn : nc ≤ -7563 / 10000)
    (hα : α ∈ Set.Icc (0 : ℝ) (51 / 500)) (hβ : β ∈ Set.Icc (0 : ℝ) α) :
    oldBound P58 Nc Fc r nc α β ≤
      -T296 + Real.log 2 / 2 + 58 * cost296 / 58 * α + phaseDelta α := by
  obtain ⟨hα0, hα1⟩ := hα
  obtain ⟨hβ0, hβ1⟩ := hβ
  have g0 : gC0 P58 = 6 / 29 := Instances.d58_gC0
  have g1 : gC1 P58 = 47 / 29 := Instances.d58_gC1
  have hlo := Real.log_two_gt_d9
  have hhi := Real.log_two_lt_d9
  unfold oldBound
  rw [g0, g1, T296_eq]
  set L := Real.log 2
  have a1 : (1 - α) * Fc ≤ (1 - α) * (-253949899 / 100000000) :=
    mul_le_mul_of_nonneg_left hF (by linarith)
  have a2 : (α - β) * r ≤ (α - β) * (-315531 / 5000000) :=
    mul_le_mul_of_nonneg_left hr (by linarith)
  have a3 : β * nc ≤ β * (-7563 / 10000) := mul_le_mul_of_nonneg_left hn hβ0
  have b0 : (1 - β) * L + 315531 / 5000000 - 7563 / 10000 ≤ 0 := by nlinarith
  have b1 : β * ((1 - β) * L + 315531 / 5000000 - 7563 / 10000) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hβ0 b0
  have c1 : α * L ≤ α * 0.6931471808 := mul_le_mul_of_nonneg_left hhi.le hα0
  have c2 : α ^ 2 * 0.6931471803 ≤ α ^ 2 * L :=
    mul_le_mul_of_nonneg_left hlo.le (by positivity)
  have ec : 58 * cost296 / 58 = 3596893 / 1000000 := by norm_num [cost296]
  rw [ec]
  unfold phaseDelta
  split_ifs with hc
  · nlinarith [sq_nonneg (α - 1 / 480)]
  · have hc' : 143 / 2000 < α := not_le.mp hc
    nlinarith [mul_nonneg hα0 (sub_nonneg.mpr hc'.le)]

/-! ### Phase margins -/

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

theorem phase_margin {p : ℕ → ℝ} (hp : p = trialSeqS Cert590.Pc Cert590.P) {α : ℝ}
    (hα : α ∈ Set.Icc (0 : ℝ) (51 / 500)) :
    Real.arctan (1 / 4) + 5 / 29 * Real.arctan 4 +
        (17 / 4) * (1 / 100) ^ 2 / (1 - (1 / 100) ^ 2) + 1 / 1000 ≤
      testF 0 / 2 + (∑' k : ℕ, testF (k + 1) * p (k + 1)) -
        Real.sqrt (testT.H * (phaseDelta α / 2)) - α * testF 0 / 4 -
          (0 : ℝ) * (phaseDelta α / 1) := by
  have hU := U_lower
  rw [← hp] at hU
  have hH := testH_le
  have hH0 := testH_nonneg
  have h0 := phase_rhs_le
  obtain ⟨hα0, hα1⟩ := hα
  rw [testF_zero_val]
  unfold phaseDelta
  split_ifs with hc
  · have hs : Real.sqrt (testT.H * (11 / 1600 / 2)) ≤ 521 / 10000 := by
      rw [Real.sqrt_le_iff]
      constructor
      · norm_num
      · nlinarith
    norm_num at hs ⊢
    nlinarith
  · have hs : Real.sqrt (testT.H * (177 / 50000 / 2)) ≤ 374 / 10000 := by
      rw [Real.sqrt_le_iff]
      constructor
      · norm_num
      · nlinarith
    norm_num at hs ⊢
    nlinarith

theorem one_margin {p : ℕ → ℝ} (hp : p = trialSeqS Cert590.Pc Cert590.P) {α : ℝ}
    (hα : α ∈ Set.Icc (0 : ℝ) (51 / 500)) :
    1 - (1 - α + p 2 - Real.sqrt (2 * (phaseDelta α / 2))) / 2 + 1 / 1000 ≤ 5 / 6 * (48 / 58) := by
  have hu := u2_lower
  rw [← hp] at hu
  obtain ⟨hα0, hα1⟩ := hα
  unfold phaseDelta
  split_ifs with hc
  · have hs : Real.sqrt (2 * (11 / 1600 / 2)) ≤ 83 / 1000 := by
      rw [Real.sqrt_le_iff]
      norm_num
    norm_num at hs ⊢
    linarith
  · have hs : Real.sqrt (2 * (177 / 50000 / 2)) ≤ 6 / 100 := by
      rw [Real.sqrt_le_iff]
      norm_num
    norm_num at hs ⊢
    linarith

/-! ### The budget, from the caps at anchor `0` -/

theorem budget_anchor0 {gasI : ℝ} {anchI : Fin 2 → ℝ}
    (B : capSource.CapBundle Trunc.exact gasI anchI)
    (hrc : B.rowCap 0 + B.colCap 0 ≤ -5526387 / 1000000)
    (hm : markCap B ≤ -976 / 1000) (hi : B.anchICap 0 + B.gasICap ≤ 2367346 / 1000000) :
    ∀ α ∈ Set.Icc (0 : ℝ) (51 / 500), ∃ a, capBudget B a α ≤
      -T296 + Real.log 2 / 2 + 58 * cost296 * α / 58 := by
  intro α hα
  refine ⟨0, ?_⟩
  obtain ⟨hα0, hα1⟩ := hα
  unfold capBudget
  rw [aB_zero, T296_eq]
  have hlo := Real.log_two_gt_d9
  have hhi := Real.log_two_lt_d9
  set L := Real.log 2
  have a1 : (1 - α) * (B.rowCap 0 + B.colCap 0) ≤ (1 - α) * (-5526387 / 1000000) :=
    mul_le_mul_of_nonneg_left hrc (by linarith)
  have a2 : α * markCap B ≤ α * (-976 / 1000) := mul_le_mul_of_nonneg_left hm hα0
  have c1 : α * 0.6931471803 ≤ α * L := mul_le_mul_of_nonneg_left hlo.le hα0
  have c2 : 0 ≤ α ^ 2 * L := by positivity
  have ec : 58 * cost296 * α / 58 = 3596893 / 1000000 * α := by
    norm_num [cost296]
    ring
  rw [ec]
  nlinarith

/-! ### The instance -/

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

/-- The retained second bounds on the smaller set. -/
def restrictG {P : CatalanMeasure.Parametric.Parameters} {α1 t r nc c : ℝ} {G G' : ℝ → Prop}
    (h : ∀ y, G' y → G y) (D : SecondTrialBoundsEnd P α1 t r nc c G) :
    SecondTrialBoundsEnd P α1 t r nc c G' :=
  { D with marked := fun {_} hN {_} hx hg => D.marked hN hx (h _ hg) }

theorem selected_restrict {P : CatalanMeasure.Parametric.Parameters} {t c : ℝ} {G G' : ℝ → Prop}
    {Q : ∀ (N p m : ℕ), (Fin p → ℝ) → (Fin m → ℝ) → (Fin p → ℝ) → Prop}
    (h : ∀ y ∈ Set.Ioo (-1 : ℝ) 1, G y → G' y)
    (hs : SelectedFreeProductCostOnRestr P t c G' Q) : SelectedFreeProductCostOnRestr P t c G Q := by
  intro ε hε
  filter_upwards [hs ε hε] with N hN
  intro p m hpm x y s hx hx0 hy hy0 hyG
  exact hN p m hpm x y s hx hx0 hy hy0 fun j => h _ (hy j) (hyG j)

/-- The intercept of the completed gas at the two anchors. -/
def anchorVal (a : Fin 2) : ℝ := anchorIntercept (aB capSource a) (aT capSource a) (aV capSource a)

/-- **`selected_free_product` at `capSource`.**  What remains: the caps of `B` with the three
scalar values at anchor `0`, the retained second bounds with the K590 values, and `PhaseHole`. -/
theorem selected_free_capSource
    (B : capSource.CapBundle Trunc.exact (gasConst capSource) anchorVal)
    (hang : ∀ σ, B.angCap σ ≤ kappa σ)
    (hrc : B.rowCap 0 + B.colCap 0 ≤ -5526387 / 1000000)
    (hm : markCap B ≤ -976 / 1000) (hi : B.anchICap 0 + B.gasICap ≤ 2367346 / 1000000)
    {t₀ residual nearCap c₀ : ℝ}
    (D : SecondTrialBoundsEnd P58 alpha296 t₀ residual nearCap c₀ G58)
    (hDp : D.p = trialSeqS Cert590.Pc Cert590.P)
    (hDn : D.normCap ≤ 1547241039 / 2000000000) (hDf : D.fieldCap ≤ -253949899 / 100000000)
    (hres : residual ≤ -315531 / 5000000) (hnear : nearCap ≤ -7563 / 10000)
    {Q : ∀ (N p m : ℕ), (Fin p → ℝ) → (Fin m → ℝ) → (Fin p → ℝ) → Prop}
    (hQ : ∀ N p m x y s, Q N p m x y s → (m : ℝ) ≤ alpha296 * (P58.n N : ℝ))
    (hole : CatalanMeasure.GenD.Signed.PhysicalPick.PhaseHole) :
    SelectedFreeProductCostOnRestr P58 T296 (58 * cost296) G58 Q := by
  refine selected_restrict (G' := G58in) (fun y hy hg => ⟨hg, hy.1.le, hy.2.le⟩) ?_
  let D' := restrictG (G' := G58in) (fun y h => h.1) D
  exact selected_free_product capSource_admissible foldSeed_capSource colCell_capSource B hang
    le_rfl (fun _ => le_rfl) (budget_anchor0 B hrc hm hi) G58in_ord D' testT
    (ξ := 1 / 1000) (d := 1) (Δ := phaseDelta) (by norm_num) one_pos
    (fun α hα β hβ => delta_bound hDn hDf hres hnear hα hβ)
    (fun α hα => phase_margin hDp hα) (fun α hα => one_margin hDp hα)
    (Filter.Eventually.of_forall fun N x hx => by simp [testT] at hx)
    (fun y _ hy => by simpa [testT] using hy.le) hQ
    (fun w e hinj h0 h1 _ hstat =>
      CatalanMeasure.GenD.Signed.PhysicalPick.pickWindow_of_phaseHole hole hinj h0 h1 e hstat)

/-- The near bound of `Theorem296`, for any node restriction. -/
theorem freeNear_capSource
    (B : capSource.CapBundle Trunc.exact (gasConst capSource) anchorVal)
    (hang : ∀ σ, B.angCap σ ≤ kappa σ)
    (hrc : B.rowCap 0 + B.colCap 0 ≤ -5526387 / 1000000)
    (hm : markCap B ≤ -976 / 1000) (hi : B.anchICap 0 + B.gasICap ≤ 2367346 / 1000000)
    {t₀ residual nearCap c₀ : ℝ}
    (D : SecondTrialBoundsEnd P58 alpha296 t₀ residual nearCap c₀ G58)
    (hDp : D.p = trialSeqS Cert590.Pc Cert590.P)
    (hDn : D.normCap ≤ 1547241039 / 2000000000) (hDf : D.fieldCap ≤ -253949899 / 100000000)
    (hres : residual ≤ -315531 / 5000000) (hnear : nearCap ≤ -7563 / 10000)
    (Nd : ∀ (N m : ℕ), (Fin m → ℝ) → Prop)
    (hole : CatalanMeasure.GenD.Signed.PhysicalPick.PhaseHole) :
    FreeNearBound P58 G58 Nd T296 (58 * cost296) alpha296 :=
  hnear296 (selected_free_capSource B hang hrc hm hi D hDp hDn hDf hres hnear
    (fun _ _ _ _ _ _ h => h.1) hole)

end
end CatalanMeasure.GenD.Signed.RouteI.T4Instance

namespace CatalanMeasure.GenD.Signed.RouteI.T4Instance

open Finset Filter CatalanMeasure.GenD.Signed.RouteI.CompletedGas CatalanMeasure.CellCert
open CatalanMeasure.GenD CatalanMeasure.GenD.D58 CatalanMeasure.GenD.Analytic
open CatalanMeasure.GenD.Signed.RouteI.CapFields CatalanMeasure.GenD.Signed.RouteI.CapSourceData
open CatalanMeasure.GenD.Signed.RouteI.InterceptSource

noncomputable section

/-! ### Anchor `1` needs no data

The budget uses anchor `0` alone, so the anchor-`1` entries of `CapBundle` only have to exist.  The
free fields are bounded above at every anchor; no value is needed. -/

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
def bundle0 {R C nc : ℝ} {oc : Sign → ℝ} (hR : capSource.FreeRowCap Trunc.exact 0 R)
    (hC : capSource.FreeColCap 0 C) (ho : ∀ σ, capSource.OrdCap Trunc.exact σ (oc σ))
    (hn : capSource.NearCap Trunc.exact nc)
    (ha : ∀ σ, capSource.AngCap Trunc.exact σ (kappa σ)) :
    capSource.CapBundle Trunc.exact (gasConst capSource) anchorVal where
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

/-- The near bound from the anchor-`0` caps alone. -/
theorem freeNear_anchor0 {R C nc : ℝ} {oc : Sign → ℝ}
    (hR : capSource.FreeRowCap Trunc.exact 0 R) (hC : capSource.FreeColCap 0 C)
    (ho : ∀ σ, capSource.OrdCap Trunc.exact σ (oc σ)) (hn : capSource.NearCap Trunc.exact nc)
    (ha : ∀ σ, capSource.AngCap Trunc.exact σ (kappa σ))
    (hrc : R + C ≤ -5526387 / 1000000) (hoc : ∀ σ, oc σ ≤ -976 / 1000) (hnc : nc ≤ -976 / 1000)
    (hi : -refQuad capSource 0 + gasConst capSource ≤ 2367346 / 1000000)
    {t₀ residual nearCap c₀ : ℝ}
    (D : SecondTrialBoundsEnd P58 alpha296 t₀ residual nearCap c₀ G58)
    (hDp : D.p = trialSeqS Cert590.Pc Cert590.P)
    (hDn : D.normCap ≤ 1547241039 / 2000000000) (hDf : D.fieldCap ≤ -253949899 / 100000000)
    (hres : residual ≤ -315531 / 5000000) (hnear : nearCap ≤ -7563 / 10000)
    (Nd : ∀ (N m : ℕ), (Fin m → ℝ) → Prop)
    (hole : CatalanMeasure.GenD.Signed.PhysicalPick.PhaseHole) :
    FreeNearBound P58 G58 Nd T296 (58 * cost296) alpha296 := by
  refine freeNear_capSource (bundle0 hR hC ho hn ha) (fun _ => le_rfl) hrc ?_ ?_ D hDp hDn hDf
    hres hnear Nd hole
  · exact max_le (max_le (hoc _) (hoc _)) hnc
  · have e : anchorVal 0 = -refQuad capSource 0 :=
      anchorIntercept_refQuad capSource_admissible colCell_capSource 0
    change anchorVal 0 + gasConst capSource ≤ _
    rw [e]
    exact hi

end
end CatalanMeasure.GenD.Signed.RouteI.T4Instance

#print axioms CatalanMeasure.GenD.Signed.RouteI.T4Instance.freeNear_anchor0
#print axioms CatalanMeasure.GenD.Signed.RouteI.T4Instance.selected_free_capSource
#print axioms CatalanMeasure.GenD.Signed.RouteI.T4Instance.freeNear_capSource
#print axioms CatalanMeasure.GenD.Signed.RouteI.T4Instance.anchorIntercept_refQuad
