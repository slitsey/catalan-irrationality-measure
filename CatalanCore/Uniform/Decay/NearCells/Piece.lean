module

public import CatalanCore.Uniform.Decay.NearCells.Coef
public import CatalanCore.Uniform.Decay.Tools.BernsteinList

@[expose] public section

/-!
# The order-`n` model of one segment's potential on a line cell (lane D, package D6b)

`piece_model`: for `s` real with `|s| ≤ h`, the potential of the segment `(A, B, a)` at
`z = zc + s dd` equals `mass · log‖B - A‖ + ∑_{m<n} c_m s^m` up to `jbQ PA + jbQ PB`, where
`c_m = Re (PA_m L₁ + PB_m L₀ + R_m + jet_m)`, `L₁ = Log(1 - ζ₀)`, `L₀ = Log(-ζ₀)`.
All inputs are Gaussian rationals; the only transcendental data are `L₀, L₁`.
-/

namespace CatalanCore.Uniform.Decay.NearCells

open Finset Complex CatalanCore.Uniform.Decay.Tools

/-- `‖c‖ ≤ |Re c| + |Im c|` as a rational. -/
def nrmQ (c : CQ) : ℚ := |c.re| + |c.im|

theorem nrmQ_nonneg (c : CQ) : 0 ≤ nrmQ c := add_nonneg (abs_nonneg _) (abs_nonneg _)

theorem norm_le_nrmQ (c : CQ) : ‖c.toC‖ ≤ (nrmQ c : ℝ) := by
  have h := Complex.norm_le_abs_re_add_abs_im c.toC
  unfold nrmQ; push_cast; exact h

/-- Rational remainder bound of the order-`n` jet of `∑ P_j s^j Log(1 - q s)`, `‖q‖ h ≤ r < 1`. -/
def jbQ (P : ℕ → CQ) (n : ℕ) (r h : ℚ) : ℚ :=
  lsum (fun j => nrmQ (P j) * h ^ j * (r ^ (n - j) / (((n - j : ℕ) : ℚ) * (1 - r)))) n

theorem jetBound_le_jbQ (P : ℕ → CQ) (n : ℕ) {q : ℂ} {r h : ℚ} (hh : 0 ≤ h)
    (hq : ‖q‖ * h ≤ (r : ℝ)) (hr1 : r < 1) :
    jetBound n (fun j => (P j).toC) q (h : ℝ) ≤ (jbQ P n r h : ℝ) := by
  unfold jetBound jbQ
  rw [lsum_eq]; push_cast
  refine Finset.sum_le_sum fun j hj => ?_
  have hjn : j < n := Finset.mem_range.1 hj
  have hk : (0 : ℝ) < ((n - j : ℕ) : ℝ) := by exact_mod_cast Nat.sub_pos_of_lt hjn
  have hr1' : (r : ℝ) < 1 := by exact_mod_cast hr1
  have hhR : (0 : ℝ) ≤ h := by exact_mod_cast hh
  have hx0 : 0 ≤ ‖q‖ * (h : ℝ) := mul_nonneg (norm_nonneg _) hhR
  have h1 : ‖(P j).toC‖ * (h : ℝ) ^ j ≤ (nrmQ (P j) : ℝ) * (h : ℝ) ^ j :=
    mul_le_mul_of_nonneg_right (norm_le_nrmQ _) (by positivity)
  have h2 : (‖q‖ * h) ^ (n - j) / (((n - j : ℕ) : ℝ) * (1 - ‖q‖ * h))
      ≤ (r : ℝ) ^ (n - j) / (((n - j : ℕ) : ℝ) * (1 - r)) := by
    have hrn : (0 : ℝ) ≤ (r : ℝ) ^ (n - j) := pow_nonneg (hx0.trans hq) _
    have hd1 : 0 < ((n - j : ℕ) : ℝ) * (1 - (r : ℝ)) := mul_pos hk (by linarith)
    exact div_le_div₀ hrn (pow_le_pow_left₀ hx0 hq _) hd1
      (mul_le_mul_of_nonneg_left (by linarith) hk.le)
  calc ‖(P j).toC‖ * (h : ℝ) ^ j * ((‖q‖ * h) ^ (n - j) / (((n - j : ℕ) : ℝ) * (1 - ‖q‖ * h)))
      ≤ (nrmQ (P j) : ℝ) * (h : ℝ) ^ j * ((r : ℝ) ^ (n - j) / (((n - j : ℕ) : ℝ) * (1 - r))) := by
        apply mul_le_mul h1 h2 (by
          apply div_nonneg (pow_nonneg hx0 _)
          apply mul_nonneg hk.le; nlinarith [hq]) (by
          apply mul_nonneg (by exact_mod_cast (nrmQ_nonneg (P j))) (pow_nonneg hhR _))
    _ = _ := by push_cast; ring

/-- Point `z₀ = (zc - A)/(B - A)`. -/
def z0of (A B zc : CQ) : CQ := CQ.div (CQ.sub zc A) (CQ.sub B A)
/-- `e = dd/(B - A)`. -/
def eof (A B dd : CQ) : CQ := CQ.div dd (CQ.sub B A)
def q0of (z0 e : CQ) : CQ := CQ.neg (CQ.div e z0)
def q1of (z0 e : CQ) : CQ := CQ.div e (CQ.sub CQ.one z0)

/-- Imaginary part of `ζ(s)` keeps the sign of `Im ζ₀` (rational sufficient test), or the whole
line is real (`ζ₀`, `e` real: field points on the support line). -/
def sideOk (z0 e : CQ) (h : ℚ) : Bool :=
  decide (h * |e.im| < |z0.im|) || (decide (z0.im = 0) && decide (e.im = 0))

theorem sideOk_sound {z0 e : CQ} {h : ℚ} (hs : sideOk z0 e h = true) (s : ℝ) (hs' : |s| ≤ h) :
    0 < (z0.im : ℝ) * (z0.toC + e.toC * (s : ℂ)).im ∨
      ((z0.im : ℝ) = 0 ∧ (z0.toC + e.toC * (s : ℂ)).im = 0) := by
  have him : (z0.toC + e.toC * (s : ℂ)).im = (z0.im : ℝ) + s * (e.im : ℝ) := by
    simp [CQ.toC]; ring
  simp only [sideOk, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hs
  rcases hs with hs | ⟨h0, h1⟩
  · left
    have hs2 : (h : ℝ) * |(e.im : ℝ)| < |(z0.im : ℝ)| := by exact_mod_cast hs
    rw [him]
    have h1 : |s * (e.im : ℝ)| < |(z0.im : ℝ)| := by
      rw [abs_mul]
      calc |s| * |(e.im : ℝ)| ≤ (h : ℝ) * |(e.im : ℝ)| :=
            mul_le_mul_of_nonneg_right hs' (abs_nonneg _)
        _ < _ := hs2
    have h2 : 0 < |(z0.im : ℝ)| := lt_of_le_of_lt (abs_nonneg _) h1
    rcases lt_or_gt_of_ne (abs_pos.1 h2) with hn | hp
    · rw [abs_of_neg hn] at h1
      have := (abs_lt.1 h1)
      nlinarith
    · rw [abs_of_pos hp] at h1
      have := (abs_lt.1 h1)
      nlinarith
  · right
    refine ⟨by exact_mod_cast h0, ?_⟩
    rw [him]
    have h0' : (z0.im : ℝ) = 0 := by exact_mod_cast h0
    have h1' : (e.im : ℝ) = 0 := by exact_mod_cast h1
    rw [h0', h1']; ring

end CatalanCore.Uniform.Decay.NearCells
