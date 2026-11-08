module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
public import CatalanMeasure.GenD.Signed.ChebSquare

@[expose] public section

/-!
# Cell lower bound of a Chebyshev trial sum (G32d)

`lowT c h a` is a rational lower bound of `∑ a_i T_{i+1}(x)` on `|x - c| ≤ h`: the sum is recomposed exactly
as a Chebyshev list `b` in `y = (x - c)/h` (`compose`), and `|T_j y - T_j 0| ≤ w_j` (`w_0 = 0`, `w_1 = 1`,
`w_j = 2`) gives `qSum b 0 y ≥ qSum b 0 0 - ∑ w_j |b_j|`.  The list machinery (`qSum`, `addQ`, `compose`,
`qZero`) is self-contained so that this module does not depend on the log-series band modules.
-/

namespace CatalanMeasure.GenD.Cert.TrialCell
open Set Polynomial

/-! ### Chebyshev lists over `ℚ`: addition, multiplication by `y`, composition with `x = m + h y` -/

open CatalanMeasure.Signed.ChebSquare in
noncomputable def qSum : List ℚ → ℕ → ℝ → ℝ
  | [], _, _ => 0
  | a :: t, k, x => (a : ℝ) * basis k x + qSum t (k + 1) x

def addQ : List ℚ → List ℚ → List ℚ
  | [], b => b
  | a, [] => a
  | x :: s, y :: t => (x + y) :: addQ s t

def smulQ (a : ℚ) (l : List ℚ) : List ℚ := l.map (a * ·)

section
open CatalanMeasure.Signed.ChebSquare

@[simp] theorem qSum_nil (k : ℕ) (x : ℝ) : qSum [] k x = 0 := rfl
@[simp] theorem qSum_cons (a : ℚ) (t : List ℚ) (k : ℕ) (x : ℝ) :
    qSum (a :: t) k x = (a : ℝ) * basis k x + qSum t (k + 1) x := rfl

theorem qSum_addQ (a b : List ℚ) (k : ℕ) (x : ℝ) : qSum (addQ a b) k x = qSum a k x + qSum b k x := by
  induction a generalizing b k with
  | nil => simp [addQ]
  | cons u s ih =>
    cases b with
    | nil => simp [addQ]
    | cons v t =>
      simp only [addQ, qSum_cons, ih]
      push_cast; ring

theorem qSum_smulQ (a : ℚ) (l : List ℚ) (k : ℕ) (x : ℝ) : qSum (smulQ a l) k x = a * qSum l k x := by
  induction l generalizing k with
  | nil => simp [smulQ]
  | cons u s ih =>
    simp only [smulQ, List.map_cons, qSum_cons] at ih ⊢
    rw [ih]; push_cast; ring

def downQ : List ℚ → List ℚ
  | [] => []
  | [a] => [0, a]
  | a :: b :: rest => b :: (a + rest.headD 0) :: rest.tail

def mulYQ (l : List ℚ) : List ℚ := smulQ (1 / 2) (addQ (0 :: l) (downQ l))

noncomputable def sdSum : ℕ → List ℚ → ℝ → ℝ
  | _, [], _ => 0
  | j, a :: t, x => (a : ℝ) * basis ((1 : ℤ) - j).natAbs x + sdSum (j + 1) t x

theorem mulY_aux (l : List ℚ) (j : ℕ) (x : ℝ) : 2 * x * qSum l j x = qSum l (j + 1) x + sdSum j l x := by
  induction l generalizing j with
  | nil => simp [sdSum]
  | cons a t ih =>
    have h := basis_mul 1 j x
    have h1 : basis 1 x = x := by simp [basis]
    rw [h1] at h
    have e : ((1 : ℕ) : ℤ) - j = (1 : ℤ) - j := by simp
    simp only [qSum_cons, sdSum]
    have ih' := ih (j + 1)
    rw [add_comm 1 j] at h
    simp only [Nat.cast_one] at h
    have : 2 * x * ((a : ℝ) * basis j x + qSum t (j + 1) x) =
        (a : ℝ) * (2 * x * basis j x) + 2 * x * qSum t (j + 1) x := by ring
    rw [this, h, ih']
    ring

theorem sd_shift (l : List ℚ) (j : ℕ) (hj : 2 ≤ j) (x : ℝ) : sdSum j l x = qSum l (j - 1) x := by
  induction l generalizing j with
  | nil => simp [sdSum]
  | cons a t ih =>
    simp only [sdSum, qSum_cons]
    have e : ((1 : ℤ) - j).natAbs = j - 1 := by omega
    rw [e, ih (j + 1) (by omega)]
    have : j + 1 - 1 = (j - 1) + 1 := by omega
    rw [this]

theorem down_eval (l : List ℚ) (x : ℝ) : qSum (downQ l) 0 x = sdSum 0 l x := by
  match l with
  | [] => simp [downQ, sdSum]
  | [a] => simp [downQ, sdSum, basis]
  | a :: b :: rest =>
    simp only [downQ, qSum_cons, sdSum]
    have e1 : ((1 : ℤ) - ((0 : ℕ) : ℤ)).natAbs = 1 := by norm_num
    have e2 : ((1 : ℤ) - (((0 + 1 : ℕ)) : ℤ)).natAbs = 0 := by norm_num
    rw [e1, e2]
    match rest with
    | [] => simp [sdSum, basis]; ring
    | c :: r' =>
      simp only [List.headD_cons, List.tail_cons, qSum_cons, sdSum]
      have e3 : ((1 : ℤ) - (((0 + 1 + 1 : ℕ)) : ℤ)).natAbs = 1 := by norm_num
      rw [e3, sd_shift r' (0 + 1 + 1 + 1) (by omega) x]
      simp only [basis, zero_add]
      push_cast
      ring

theorem mulY_eval (l : List ℚ) (x : ℝ) : qSum (mulYQ l) 0 x = x * qSum l 0 x := by
  unfold mulYQ
  rw [qSum_smulQ, qSum_addQ, down_eval]
  have h := mulY_aux l 0 x
  have : qSum (0 :: l) 0 x = qSum l 1 x := by simp
  rw [this]
  push_cast
  linarith

end

section
open CatalanMeasure.Signed.ChebSquare

def nextT (m h : ℚ) (P Q : List ℚ) : List ℚ :=
  addQ (smulQ 2 (addQ (smulQ m Q) (smulQ h (mulYQ Q)))) (smulQ (-1) P)

def composeGo (m h : ℚ) : List ℚ → List ℚ → List ℚ → List ℚ
  | [], _, _ => []
  | a :: t, P, Q => addQ (smulQ a Q) (composeGo m h t Q (nextT m h P Q))

/-- `Σ_i a_i T_{i+1}(m + h y)` as a Chebyshev list in `y` -/
def compose (m h : ℚ) (a : List ℚ) : List ℚ := composeGo m h a [1] [m, h]

theorem nextT_eval (m h : ℚ) (P Q : List ℚ) (n : ℕ) (y : ℝ)
    (hP : qSum P 0 y = basis n ((m : ℝ) + h * y)) (hQ : qSum Q 0 y = basis (n + 1) ((m : ℝ) + h * y)) :
    qSum (nextT m h P Q) 0 y = basis (n + 2) ((m : ℝ) + h * y) := by
  unfold nextT
  rw [qSum_addQ, qSum_smulQ, qSum_addQ, qSum_smulQ, qSum_smulQ, mulY_eval, qSum_smulQ, hP, hQ]
  have := Polynomial.Chebyshev.T_add_two ℝ (n : ℤ)
  have h2 := congrArg (Polynomial.eval ((m : ℝ) + h * y)) this
  simp only [basis]
  push_cast at h2 ⊢
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_ofNat] at h2
  rw [h2]
  simp only [basis] at *
  ring

theorem composeGo_eval (m h : ℚ) (y : ℝ) (a : List ℚ) : ∀ (P Q : List ℚ) (n : ℕ),
    qSum P 0 y = basis n ((m : ℝ) + h * y) → qSum Q 0 y = basis (n + 1) ((m : ℝ) + h * y) →
    qSum (composeGo m h a P Q) 0 y = qSum a (n + 1) ((m : ℝ) + h * y) := by
  induction a with
  | nil => intros; simp [composeGo]
  | cons u t ih =>
    intro P Q n hP hQ
    simp only [composeGo, qSum_cons]
    rw [qSum_addQ, qSum_smulQ, hQ, ih Q (nextT m h P Q) (n + 1) hQ (nextT_eval m h P Q n y hP hQ)]

theorem compose_eval (m h : ℚ) (a : List ℚ) (y : ℝ) :
    qSum (compose m h a) 0 y = qSum a 1 ((m : ℝ) + h * y) := by
  unfold compose
  refine composeGo_eval m h y a [1] [m, h] 0 ?_ ?_
  · simp [basis]
  · simp [basis, Polynomial.Chebyshev.T_one]

/-- `Σ_j l_j T_j(0)`, by the recurrence `T_{j+2}(0) = -T_j(0)` -/
def qZeroGo : List ℚ → ℚ → ℚ → ℚ
  | [], _, _ => 0
  | a :: r, t0, t1 => a * t0 + qZeroGo r t1 (-t0)

theorem basis_add_two_zero (j : ℕ) : basis (j + 2) 0 = - basis j 0 := by
  have := Polynomial.Chebyshev.T_add_two ℝ (j : ℤ)
  have h2 := congrArg (Polynomial.eval (0 : ℝ)) this
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_ofNat, mul_zero,
    zero_mul, zero_sub] at h2
  simp only [basis]
  push_cast
  exact h2

theorem qZeroGo_eval (l : List ℚ) : ∀ (j : ℕ) (t0 t1 : ℚ), (t0 : ℝ) = basis j 0 → (t1 : ℝ) = basis (j + 1) 0 →
    (qZeroGo l t0 t1 : ℝ) = qSum l j 0 := by
  induction l with
  | nil => intros; simp [qZeroGo]
  | cons a r ih =>
    intro j t0 t1 h0 h1
    simp only [qZeroGo, qSum_cons]
    push_cast
    rw [h0, ih (j + 1) t1 (-t0) h1 (by push_cast; rw [h0]; exact (basis_add_two_zero j).symm)]

def qZero (l : List ℚ) : ℚ := qZeroGo l 1 0

theorem qZero_eval (l : List ℚ) : (qZero l : ℝ) = qSum l 0 0 :=
  qZeroGo_eval l 0 1 0 (by simp [basis]) (by simp [basis, Polynomial.Chebyshev.T_one])

end

/-- `∑_{j} w_j |l_j|` with `w_0 = 0`, `w_1 = 1`, `w_j = 2` (index shifted by `k`) -/
def lowDev : List ℚ → ℕ → ℚ
  | [], _ => 0
  | a :: t, k => (if k = 0 then 0 else if k = 1 then |a| else 2 * |a|) + lowDev t (k + 1)

section
open CatalanMeasure.Signed.ChebSquare

theorem basis_dev_one {y : ℝ} (hy : y ∈ Icc (-1 : ℝ) 1) : |basis 1 y - basis 1 0| ≤ 1 := by
  have hy' := abs_le.mpr ⟨hy.1, hy.2⟩
  simpa [basis, Polynomial.Chebyshev.T_one] using hy'

theorem basis_dev_two (k : ℕ) {y : ℝ} (hy : y ∈ Icc (-1 : ℝ) 1) : |basis k y - basis k 0| ≤ 2 := by
  have h0 : (0 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have a1 := abs_basis_le_one k hy
  have a2 := abs_basis_le_one k h0
  calc |basis k y - basis k 0| ≤ |basis k y| + |basis k 0| := abs_sub _ _
    _ ≤ 1 + 1 := add_le_add a1 a2
    _ = 2 := by norm_num

theorem qSum_dev (l : List ℚ) : ∀ (k : ℕ) {y : ℝ}, y ∈ Icc (-1 : ℝ) 1 →
    |qSum l k y - qSum l k 0| ≤ (lowDev l k : ℝ) := by
  induction l with
  | nil => intro k y hy; simp [lowDev]
  | cons a t ih =>
    intro k y hy
    simp only [qSum_cons, lowDev]
    have h1 := ih (k + 1) hy
    have e : (a : ℝ) * basis k y + qSum t (k + 1) y - ((a : ℝ) * basis k 0 + qSum t (k + 1) 0) =
        (a : ℝ) * (basis k y - basis k 0) + (qSum t (k + 1) y - qSum t (k + 1) 0) := by ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    have habs : |(a : ℝ)| = ((|a| : ℚ) : ℝ) := by push_cast; rfl
    have h3 : |(a : ℝ) * (basis k y - basis k 0)| ≤
        (((if k = 0 then 0 else if k = 1 then |a| else 2 * |a| : ℚ)) : ℝ) := by
      rw [abs_mul]
      have ha := abs_nonneg (a : ℝ)
      by_cases hk0 : k = 0
      · subst hk0
        simp
      by_cases hk1 : k = 1
      · subst hk1
        have h2 := basis_dev_one hy
        have e1 : (if (1 : ℕ) = 0 then (0 : ℚ) else if (1 : ℕ) = 1 then |a| else 2 * |a|) = |a| := by simp
        rw [e1, ← habs]
        nlinarith [mul_le_mul_of_nonneg_left h2 ha]
      · have h2 := basis_dev_two k hy
        have e1 : (if k = 0 then (0 : ℚ) else if k = 1 then |a| else 2 * |a|) = 2 * |a| := by simp [hk0, hk1]
        rw [e1]
        push_cast
        rw [habs]
        nlinarith [mul_le_mul_of_nonneg_left h2 ha]
    push_cast at h3 ⊢
    linarith

theorem low_le (l : List ℚ) {y : ℝ} (hy : y ∈ Icc (-1 : ℝ) 1) :
    ((qZero l - lowDev l 0 : ℚ) : ℝ) ≤ qSum l 0 y := by
  have h := qSum_dev l 0 hy
  have hz := qZero_eval l
  push_cast
  have := (abs_le.mp h).1
  linarith

end

/-- the lower bound of `∑ a_i T_{i+1}` on the cell `|x - c| ≤ h` -/
def lowT (c h : ℚ) (a : List ℚ) : ℚ := qZero (compose c h a) - lowDev (compose c h a) 0

theorem lowT_le (c h : ℚ) (hh : 0 < h) (a : List ℚ) {x : ℝ} (hx : |x - (c : ℝ)| ≤ (h : ℝ)) :
    (lowT c h a : ℝ) ≤ qSum a 1 x := by
  have hh' : (0 : ℝ) < h := by exact_mod_cast hh
  set y := (x - c) / h with hy
  have hyI : y ∈ Icc (-1 : ℝ) 1 := by
    rw [hy, mem_Icc, le_div_iff₀ hh', div_le_iff₀ hh']
    have := abs_le.mp hx
    constructor <;> linarith [this.1, this.2]
  have hxy : x = (c : ℝ) + h * y := by rw [hy]; field_simp; ring
  have h1 := low_le (compose c h a) hyI
  rw [compose_eval] at h1
  rw [hxy]
  exact h1


/-! ### Integer-scaled composition (G32d)

`accZ cc hh T w` is `∑_i w_i T^{n-1-i} V_{i+1}` where `V_n = T^n T_n(cc/T + (hh/T) y)` as an integer Chebyshev list in
`y` (recurrence `V_{n+1} = 2 cc V_n + hh (2 y V_n) - T² V_{n-1}`).  It equals `T^n ∑ w_i T_{i+1}(x)` and avoids all
rational normalisation: only big-integer additions and small-by-big products. -/

def addZ : List ℤ → List ℤ → List ℤ
  | [], b => b
  | a, [] => a
  | x :: s, y :: t => (x + y) :: addZ s t

def smulZ (c : ℤ) (l : List ℤ) : List ℤ := l.map (c * ·)

def downZ : List ℤ → List ℤ
  | [] => []
  | [a] => [0, a]
  | a :: b :: rest => b :: (a + rest.headD 0) :: rest.tail

/-- `2 y · l` in the Chebyshev basis -/
def mulY2Z (l : List ℤ) : List ℤ := addZ (0 :: l) (downZ l)

def castL (l : List ℤ) : List ℚ := l.map (Int.cast : ℤ → ℚ)

theorem castL_addZ (a b : List ℤ) : castL (addZ a b) = addQ (castL a) (castL b) := by
  induction a generalizing b with
  | nil => simp [addZ, addQ, castL]
  | cons u s ih =>
    cases b with
    | nil => simp [addZ, addQ, castL]
    | cons v t => simp only [addZ, addQ, castL, List.map_cons] at ih ⊢; rw [ih]; push_cast; rfl

theorem castL_smulZ (c : ℤ) (l : List ℤ) : castL (smulZ c l) = smulQ (c : ℚ) (castL l) := by
  induction l with
  | nil => simp [smulZ, smulQ, castL]
  | cons u s ih =>
    simp only [smulZ, smulQ, castL, List.map_cons] at ih ⊢
    rw [ih]; push_cast; rfl

theorem castL_downZ (l : List ℤ) : castL (downZ l) = downQ (castL l) := by
  match l with
  | [] => simp [downZ, downQ, castL]
  | [a] => simp [downZ, downQ, castL]
  | a :: b :: rest =>
    cases rest with
    | nil => simp [downZ, downQ, castL]
    | cons c r => simp [downZ, downQ, castL]

section
open CatalanMeasure.Signed.ChebSquare

theorem mulY2Z_eval (l : List ℤ) (x : ℝ) : qSum (castL (mulY2Z l)) 0 x = 2 * x * qSum (castL l) 0 x := by
  unfold mulY2Z
  rw [castL_addZ, qSum_addQ, castL_downZ, down_eval]
  have h := mulY_aux (castL l) 0 x
  have : castL (0 :: l) = 0 :: castL l := by simp [castL]
  rw [this]
  have h0 : qSum (0 :: castL l) 0 x = qSum (castL l) 1 x := by simp
  rw [h0]
  push_cast at h
  linarith

def nextV (cc hh T : ℤ) (Vp Vc : List ℤ) : List ℤ :=
  addZ (addZ (smulZ (2 * cc) Vc) (smulZ hh (mulY2Z Vc))) (smulZ (-(T * T)) Vp)

theorem nextV_eval (cc hh T : ℤ) (hT : T ≠ 0) (Vp Vc : List ℤ) (n : ℕ) (y : ℝ)
    (hp : qSum (castL Vp) 0 y = (T : ℝ) ^ n * basis n ((cc : ℝ) / T + ((hh : ℝ) / T) * y))
    (hc : qSum (castL Vc) 0 y = (T : ℝ) ^ (n + 1) * basis (n + 1) ((cc : ℝ) / T + ((hh : ℝ) / T) * y)) :
    qSum (castL (nextV cc hh T Vp Vc)) 0 y =
      (T : ℝ) ^ (n + 2) * basis (n + 2) ((cc : ℝ) / T + ((hh : ℝ) / T) * y) := by
  unfold nextV
  rw [castL_addZ, castL_addZ, castL_smulZ, castL_smulZ, castL_smulZ, qSum_addQ, qSum_addQ, qSum_smulQ,
    qSum_smulQ, qSum_smulQ, mulY2Z_eval, hp, hc]
  have hT' : (T : ℝ) ≠ 0 := by exact_mod_cast hT
  have := Polynomial.Chebyshev.T_add_two ℝ (n : ℤ)
  have h2 := congrArg (Polynomial.eval ((cc : ℝ) / T + ((hh : ℝ) / T) * y)) this
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_ofNat] at h2
  simp only [basis]
  push_cast at h2 ⊢
  rw [h2]
  field_simp
  ring

def goZ (cc hh T : ℤ) : List ℤ → List ℤ → List ℤ → List ℤ → List ℤ
  | _, _, acc, [] => acc
  | Vp, Vc, acc, w :: ws => goZ cc hh T Vc (nextV cc hh T Vp Vc) (addZ (smulZ T acc) (smulZ w Vc)) ws

theorem goZ_eval (cc hh T : ℤ) (hT : T ≠ 0) (y : ℝ) (ws : List ℤ) :
    ∀ (n : ℕ) (Vp Vc acc : List ℤ),
    qSum (castL Vp) 0 y = (T : ℝ) ^ n * basis n ((cc : ℝ) / T + ((hh : ℝ) / T) * y) →
    qSum (castL Vc) 0 y = (T : ℝ) ^ (n + 1) * basis (n + 1) ((cc : ℝ) / T + ((hh : ℝ) / T) * y) →
    qSum (castL (goZ cc hh T Vp Vc acc ws)) 0 y =
      (T : ℝ) ^ ws.length * qSum (castL acc) 0 y +
        (T : ℝ) ^ (n + ws.length) * qSum (castL ws) (n + 1) ((cc : ℝ) / T + ((hh : ℝ) / T) * y) := by
  induction ws with
  | nil => intro n Vp Vc acc hp hc; simp [goZ, castL]
  | cons w ws ih =>
    intro n Vp Vc acc hp hc
    simp only [goZ]
    rw [ih (n + 1) Vc (nextV cc hh T Vp Vc) (addZ (smulZ T acc) (smulZ w Vc)) hc (nextV_eval cc hh T hT Vp Vc n y hp hc)]
    rw [castL_addZ, castL_smulZ, castL_smulZ, qSum_addQ, qSum_smulQ, qSum_smulQ, hc]
    have e : castL (w :: ws) = (w : ℚ) :: castL ws := by simp [castL]
    rw [e, qSum_cons]
    simp only [List.length_cons, castL, List.map_cons, qSum_cons]
    push_cast
    have e2 : n + (ws.length + 1) = n + 1 + ws.length := by omega
    rw [e2]
    ring

/-- the accumulated integer list for the weights `w` -/
def accZ (cc hh T : ℤ) (w : List ℤ) : List ℤ := goZ cc hh T [1] [cc, hh] [] w

theorem accZ_eval (cc hh T : ℤ) (hT : T ≠ 0) (w : List ℤ) (y : ℝ) :
    qSum (castL (accZ cc hh T w)) 0 y =
      (T : ℝ) ^ w.length * qSum (castL w) 1 ((cc : ℝ) / T + ((hh : ℝ) / T) * y) := by
  have hT' : (T : ℝ) ≠ 0 := by exact_mod_cast hT
  have := goZ_eval cc hh T hT y w 0 [1] [cc, hh] []
    (by simp [castL, basis]) (by simp [castL, basis, Polynomial.Chebyshev.T_one]; field_simp)
  unfold accZ
  rw [this]
  simp [castL]

end

/-- integer-scaled lower bound: `∑ w_i T_{i+1} / D0` on the cell `|x - cc/T| ≤ hh/T` -/
def lowTI (cc hh T : ℤ) (w : List ℤ) (D0 : ℚ) : ℚ :=
  (qZero (castL (accZ cc hh T w)) - lowDev (castL (accZ cc hh T w)) 0) / (D0 * (T : ℚ) ^ w.length)

theorem lowTI_le (cc hh T : ℤ) (hT : 0 < T) (hh0 : 0 < hh) (w : List ℤ) (D0 : ℚ) (hD : 0 < D0) {x : ℝ}
    (hx : |x - (cc : ℝ) / T| ≤ (hh : ℝ) / T) :
    (lowTI cc hh T w D0 : ℝ) ≤ (1 / (D0 : ℝ)) * qSum (castL w) 1 x := by
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have hhr : (0 : ℝ) < hh := by exact_mod_cast hh0
  have hDr : (0 : ℝ) < D0 := by exact_mod_cast hD
  have hh' : (0 : ℝ) < (hh : ℝ) / T := div_pos hhr hTr
  set y := (x - (cc : ℝ) / T) / ((hh : ℝ) / T) with hy
  have hyI : y ∈ Icc (-1 : ℝ) 1 := by
    rw [hy, mem_Icc, le_div_iff₀ hh', div_le_iff₀ hh']
    have := abs_le.mp hx
    constructor <;> linarith [this.1, this.2]
  have hxy : x = (cc : ℝ) / T + ((hh : ℝ) / T) * y := by rw [hy]; field_simp; ring
  have h1 := low_le (castL (accZ cc hh T w)) hyI
  rw [accZ_eval cc hh T hT.ne' w y, ← hxy] at h1
  unfold lowTI
  push_cast
  have hpow : (0 : ℝ) < (T : ℝ) ^ w.length := by positivity
  rw [div_le_iff₀ (by positivity)]
  have : (1 / (D0 : ℝ)) * qSum (castL w) 1 x * ((D0 : ℝ) * (T : ℝ) ^ w.length) =
      (T : ℝ) ^ w.length * qSum (castL w) 1 x := by field_simp
  rw [this]
  push_cast at h1
  exact h1

theorem qSum_mapDiv (D : ℚ) (l : List ℚ) (k : ℕ) (x : ℝ) :
    qSum (l.map (fun q => q / D)) k x = qSum l k x / (D : ℝ) := by
  induction l generalizing k with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, qSum_cons, ih]
    push_cast
    ring

end CatalanMeasure.GenD.Cert.TrialCell
#print axioms CatalanMeasure.GenD.Cert.TrialCell.lowT_le
#print axioms CatalanMeasure.GenD.Cert.TrialCell.lowTI_le
#print axioms CatalanMeasure.GenD.Cert.TrialCell.qSum_mapDiv
