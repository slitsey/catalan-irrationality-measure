module

public import CatalanMeasure.GenD.Analytic.GapWeights
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# Analytic layer (CIRC): a piece cover proves `GapCircleBound`, any design

Generic form of `Parametric.GapCirclePieces`/`GapCircleCover` without logarithms.  Data: a radius
`r`, gap parameter `a` (rationals), exponents `d = n0 - g0`, `m = h0 + q0`, a rational `E` and a
list of pieces `(lo, hi, b1, b2, H, base)` of `|Re z|`.  A piece is `ok` when
`|z^2-1| <= b1`, `|z^2-a^2| <= b2`, `(b1+b2)/(1-a^2) <= H`, `H + sqrt(H^2-1) <= base`,
`base <= Csq`, and `base^d * (r^2+1+2 hi)^m <= E`.  The cover then gives
`|T_K(arg z)| |1-z|^(h+q) <= C exp(wc N)` for `K = (d N + 1)/2`, whenever `E <= exp(2 wc)` and
`Csq <= C^2`.  Squaring keeps the exponent `d N / 2` of the odd case exact (constant factor `base`).
-/

namespace CatalanMeasure.GenD
namespace Analytic

open Polynomial Polynomial.Chebyshev OAI.InternalCatalan CatalanMeasure.Parametric

noncomputable section

theorem gcg_norm_sq (z : ℂ) (c : ℝ) :
    ‖z ^ 2 - (c : ℂ) ^ 2‖ ^ 2 = (‖z‖ ^ 2 + c ^ 2) ^ 2 - 4 * c ^ 2 * z.re ^ 2 := by
  rw [Complex.sq_norm, Complex.sq_norm]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, pow_two,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem gcg_arg_eval (a : ℝ) (z : ℂ) :
    ((gapArgument a).map (algebraMap ℝ ℂ)).eval z =
      (2 * z ^ 2 - (1 + (a : ℂ) ^ 2)) / (1 - (a : ℂ) ^ 2) := by
  simp only [gapArgument, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C,
    Polynomial.map_pow, Polynomial.map_X, eval_sub, eval_mul, eval_C, eval_pow, eval_X,
    Complex.coe_algebraMap, Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_add,
    Complex.ofReal_pow, Complex.ofReal_one, Complex.ofReal_ofNat]
  ring

theorem gcg_arg_dist {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (z : ℂ) :
    ‖((gapArgument a).map (algebraMap ℝ ℂ)).eval z - 1‖ = 2 * ‖z ^ 2 - 1‖ / (1 - a ^ 2) ∧
    ‖((gapArgument a).map (algebraMap ℝ ℂ)).eval z + 1‖ =
      2 * ‖z ^ 2 - (a : ℂ) ^ 2‖ / (1 - a ^ 2) := by
  have hd : 0 < 1 - a ^ 2 := by
    have hh := mul_pos (sub_pos.mpr ha1) (by linarith only [ha0] : 0 < 1 + a)
    nlinarith only [hh]
  have hdc : (1 : ℂ) - (a : ℂ) ^ 2 ≠ 0 := by exact_mod_cast hd.ne'
  have hnorm : ‖(1 : ℂ) - (a : ℂ) ^ 2‖ = 1 - a ^ 2 := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_one, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd]
  rw [gcg_arg_eval]
  constructor
  · have he : (2 * z ^ 2 - (1 + (a : ℂ) ^ 2)) / (1 - (a : ℂ) ^ 2) - 1 =
        2 * (z ^ 2 - 1) / (1 - (a : ℂ) ^ 2) := by field_simp; ring
    rw [he, norm_div, norm_mul, Complex.norm_ofNat, hnorm]
  · have he : (2 * z ^ 2 - (1 + (a : ℂ) ^ 2)) / (1 - (a : ℂ) ^ 2) + 1 =
        2 * (z ^ 2 - (a : ℂ) ^ 2) / (1 - (a : ℂ) ^ 2) := by field_simp; ring
    rw [he, norm_div, norm_mul, Complex.norm_ofNat, hnorm]

theorem gcg_caps {a radius lo b1 b2 : ℝ}
    (hlo : 0 ≤ lo) (ha : 0 ≤ a) (hb1 : 0 ≤ b1) (hb2 : 0 ≤ b2)
    (hcap1 : (radius ^ 2 + 1) ^ 2 - 4 * lo ^ 2 ≤ b1 ^ 2)
    (hcap2 : (radius ^ 2 + a ^ 2) ^ 2 - 4 * a ^ 2 * lo ^ 2 ≤ b2 ^ 2)
    (z : ℂ) (hz : ‖z‖ = radius) (hs : lo ≤ |z.re|) :
    ‖z ^ 2 - 1‖ ≤ b1 ∧ ‖z ^ 2 - (a : ℂ) ^ 2‖ ≤ b2 := by
  have hsq : lo ^ 2 ≤ z.re ^ 2 := by simpa only [sq_abs] using pow_le_pow_left₀ hlo hs 2
  have h1 := gcg_norm_sq z 1
  have h2 := gcg_norm_sq z a
  rw [hz] at h1 h2
  norm_num only [Complex.ofReal_one, one_pow, mul_one] at h1
  constructor
  · nlinarith only [h1, hcap1, hsq, norm_nonneg (z ^ 2 - 1), hb1]
  · have hh := mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ 4 * a ^ 2)
    nlinarith only [h2, hcap2, hh, norm_nonneg (z ^ 2 - (a : ℂ) ^ 2), hb2]

theorem gcg_filter {radius hi : ℝ} (z : ℂ) (hz : ‖z‖ = radius) (hs : |z.re| ≤ hi) :
    ‖(1 : ℂ) - z‖ ^ 2 ≤ radius ^ 2 + 1 + 2 * hi := by
  have hnorm := Complex.sq_norm_sub_sq_re z
  rw [hz] at hnorm
  have he : ‖(1 : ℂ) - z‖ ^ 2 = (1 - z.re) ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
    ring
  rw [he]
  have hh := (abs_le.mp hs).1
  nlinarith only [hnorm, hh]

structure CircPiece where
  lo : ℚ
  hi : ℚ
  b1 : ℚ
  b2 : ℚ
  H : ℚ
  base : ℚ

def CircPiece.ok (a r E Csq : ℚ) (d m : ℕ) (p : CircPiece) : Bool :=
  decide (0 ≤ p.lo ∧ p.lo ≤ p.hi ∧ p.hi ≤ r ∧ 0 ≤ p.b1 ∧ 0 ≤ p.b2 ∧ 0 ≤ p.H ∧ p.H ≤ p.base ∧
    1 ≤ p.base ∧ p.base ≤ Csq ∧
    (r ^ 2 + 1) ^ 2 - 4 * p.lo ^ 2 ≤ p.b1 ^ 2 ∧
    (r ^ 2 + a ^ 2) ^ 2 - 4 * a ^ 2 * p.lo ^ 2 ≤ p.b2 ^ 2 ∧
    p.b1 + p.b2 ≤ p.H * (1 - a ^ 2) ∧ p.H ^ 2 - 1 ≤ (p.base - p.H) ^ 2 ∧
    p.base ^ d * (r ^ 2 + 1 + 2 * p.hi) ^ m ≤ E)

def circCover (a r E Csq : ℚ) (d m : ℕ) : ℚ → List CircPiece → Bool
  | c, [] => decide (c = r)
  | c, p :: l => decide (p.lo = c) && p.ok a r E Csq d m && circCover a r E Csq d m p.hi l

theorem circCover_exists {a r E Csq : ℚ} {d m : ℕ} {c : ℚ} {l : List CircPiece}
    (h : circCover a r E Csq d m c l = true) {s : ℝ} (hs : (c : ℝ) ≤ s) (hs2 : s ≤ (r : ℝ))
    (hne : (c : ℝ) < s ∨ l ≠ []) :
    ∃ p ∈ l, p.ok a r E Csq d m = true ∧ (p.lo : ℝ) ≤ s ∧ s ≤ (p.hi : ℝ) := by
  induction l generalizing c with
  | nil =>
    simp only [circCover, decide_eq_true_eq] at h
    subst h
    rcases hne with h1 | h1
    · exact absurd hs2 (not_le.mpr h1)
    · exact absurd rfl h1
  | cons p l ih =>
    simp only [circCover, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hc, hp⟩, hrest⟩ := h
    by_cases hs1 : s ≤ (p.hi : ℝ)
    · exact ⟨p, by simp, hp, by rw [hc]; exact hs, hs1⟩
    · obtain ⟨q, hq, hq2⟩ := ih hrest (le_of_lt (not_le.mp hs1)) (Or.inl (not_le.mp hs1))
      exact ⟨q, List.mem_cons_of_mem _ hq, hq2⟩

theorem CircPiece.bound {a r E Csq : ℚ} {d m : ℕ} (ha0 : (0 : ℝ) < a) (ha1 : (a : ℝ) < 1)
    (p : CircPiece) (hp : p.ok a r E Csq d m = true) (N : ℕ) (z : ℂ) (hz : ‖z‖ = (r : ℝ))
    (hs : |z.re| ∈ Set.Icc (p.lo : ℝ) p.hi) :
    (‖((gapPolyK (a : ℝ) ((d * N + 1) / 2)).map (algebraMap ℝ ℂ)).eval z‖ *
      ‖(1 : ℂ) - z‖ ^ (m * N)) ^ 2 ≤ (Csq : ℝ) * (E : ℝ) ^ N := by
  obtain ⟨hlo, hlh, hhr, hb1, hb2, hH0, hHB, hB1, hBR, hc1, hc2, hHC, hBC, hE⟩ :=
    of_decide_eq_true hp
  have hd : (0 : ℝ) < 1 - (a : ℝ) ^ 2 := by
    have hh := mul_pos (sub_pos.mpr ha1) (by linarith only [ha0] : (0 : ℝ) < 1 + a)
    nlinarith only [hh]
  have hc1R : ((r : ℝ) ^ 2 + 1) ^ 2 - 4 * (p.lo : ℝ) ^ 2 ≤ (p.b1 : ℝ) ^ 2 := by
    exact_mod_cast hc1
  have hc2R : ((r : ℝ) ^ 2 + (a : ℝ) ^ 2) ^ 2 - 4 * (a : ℝ) ^ 2 * (p.lo : ℝ) ^ 2 ≤
      (p.b2 : ℝ) ^ 2 := by exact_mod_cast hc2
  have hc := gcg_caps (a := (a : ℝ)) (radius := (r : ℝ)) (lo := (p.lo : ℝ))
    (b1 := (p.b1 : ℝ)) (b2 := (p.b2 : ℝ)) (by exact_mod_cast hlo) ha0.le
    (by exact_mod_cast hb1) (by exact_mod_cast hb2) hc1R hc2R z hz hs.1
  have hdist := gcg_arg_dist ha0 ha1 z
  set w : ℂ := ((gapArgument (a : ℝ)).map (algebraMap ℝ ℂ)).eval z with hw
  set H : ℝ := (‖w - 1‖ + ‖w + 1‖) / 2 with hHdef
  have hH0' : 0 ≤ H := by positivity
  have hHR : (p.b1 : ℝ) + p.b2 ≤ (p.H : ℝ) * (1 - (a : ℝ) ^ 2) := by exact_mod_cast hHC
  have hHi : H ≤ (p.H : ℝ) := by
    rw [hHdef, hdist.1, hdist.2]
    have : (2 * ‖z ^ 2 - 1‖ / (1 - (a : ℝ) ^ 2) +
        2 * ‖z ^ 2 - ((a : ℝ) : ℂ) ^ 2‖ / (1 - (a : ℝ) ^ 2)) / 2 =
        (‖z ^ 2 - 1‖ + ‖z ^ 2 - ((a : ℝ) : ℂ) ^ 2‖) / (1 - (a : ℝ) ^ 2) := by ring
    rw [this, div_le_iff₀ hd]
    nlinarith only [hc.1, hc.2, hHR]
  have hbr : (0 : ℝ) ≤ (p.base : ℝ) - p.H := by exact_mod_cast sub_nonneg.mpr hHB
  have hroot : Real.sqrt (H ^ 2 - 1) ≤ (p.base : ℝ) - (p.H : ℝ) := by
    rw [Real.sqrt_le_left hbr]
    have hnum : (p.H : ℝ) ^ 2 - 1 ≤ ((p.base : ℝ) - (p.H : ℝ)) ^ 2 := by exact_mod_cast hBC
    have hHsq := pow_le_pow_left₀ hH0' hHi 2
    linarith only [hHsq, hnum]
  have hbase1 : (1 : ℝ) ≤ p.base := by exact_mod_cast hB1
  set K : ℕ := (d * N + 1) / 2 with hK
  have hT : ‖(T ℂ (K : ℤ)).eval w‖ ≤ (p.base : ℝ) ^ K := by
    apply (CatalanMeasure.norm_T_eval_le K w).trans
    apply pow_le_pow_left₀ (by positivity)
    change H + Real.sqrt (H ^ 2 - 1) ≤ (p.base : ℝ)
    linarith only [hHi, hroot]
  have he : ‖((gapPolyK (a : ℝ) K).map (algebraMap ℝ ℂ)).eval z‖ = ‖(T ℂ (K : ℤ)).eval w‖ := by
    rw [gapPolyK, Polynomial.map_comp, Chebyshev.map_T, eval_comp]
  have hT2 : ‖((gapPolyK (a : ℝ) K).map (algebraMap ℝ ℂ)).eval z‖ ^ 2 ≤
      (p.base : ℝ) ^ (d * N + 1) := by
    rw [he]
    calc _ ≤ ((p.base : ℝ) ^ K) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hT 2
      _ = (p.base : ℝ) ^ (2 * K) := by rw [← pow_mul, mul_comm]
      _ ≤ (p.base : ℝ) ^ (d * N + 1) := pow_le_pow_right₀ hbase1 (by omega)
  have hf := gcg_filter (hi := (p.hi : ℝ)) z hz hs.2
  have hhi0 : (0 : ℝ) ≤ p.hi := by exact_mod_cast (le_trans hlo hlh)
  have hF0 : (0 : ℝ) ≤ (r : ℝ) ^ 2 + 1 + 2 * (p.hi : ℝ) := by positivity
  have hf2 : (‖(1 : ℂ) - z‖ ^ (m * N)) ^ 2 ≤ (((r : ℝ) ^ 2 + 1 + 2 * (p.hi : ℝ)) ^ m) ^ N := by
    calc (‖(1 : ℂ) - z‖ ^ (m * N)) ^ 2 = (‖(1 : ℂ) - z‖ ^ 2) ^ (m * N) := by
          rw [← pow_mul, ← pow_mul, mul_comm]
      _ ≤ ((r : ℝ) ^ 2 + 1 + 2 * (p.hi : ℝ)) ^ (m * N) := pow_le_pow_left₀ (sq_nonneg _) hf _
      _ = (((r : ℝ) ^ 2 + 1 + 2 * (p.hi : ℝ)) ^ m) ^ N := by rw [pow_mul]
  have hER : (p.base : ℝ) ^ d * ((r : ℝ) ^ 2 + 1 + 2 * (p.hi : ℝ)) ^ m ≤ (E : ℝ) := by
    exact_mod_cast hE
  have hBR' : (p.base : ℝ) ≤ (Csq : ℝ) := by exact_mod_cast hBR
  have hbase0 : (0 : ℝ) ≤ p.base := by linarith only [hbase1]
  have hE0 : (0 : ℝ) ≤ (p.base : ℝ) ^ d * ((r : ℝ) ^ 2 + 1 + 2 * (p.hi : ℝ)) ^ m := by
    positivity
  rw [mul_pow]
  calc _ ≤ (p.base : ℝ) ^ (d * N + 1) * (((r : ℝ) ^ 2 + 1 + 2 * (p.hi : ℝ)) ^ m) ^ N :=
        mul_le_mul hT2 hf2 (by positivity) (by positivity)
    _ = (p.base : ℝ) * ((p.base : ℝ) ^ d * ((r : ℝ) ^ 2 + 1 + 2 * (p.hi : ℝ)) ^ m) ^ N := by
        rw [mul_pow, ← pow_mul, pow_succ]; ring
    _ ≤ (Csq : ℝ) * (E : ℝ) ^ N :=
        mul_le_mul hBR' (pow_le_pow_left₀ hE0 hER N) (by positivity)
          (by linarith only [hBR', hbase1])

/-- A piece cover certifies the circle estimate `GapCircleBound` (any design with
`n0 - g0 = d`, `h0 + q0 = m`). -/
theorem gapCircleBound_of_cover (P : Parameters) {d m : ℕ} (hd : P.n0 - P.g0 = d)
    (hm : P.h0 + P.q0 = m) {a r E Csq : ℚ} {pieces : List CircPiece}
    (ha0 : (0 : ℝ) < a) (ha1 : (a : ℝ) < 1)
    (hE0 : (0 : ℝ) ≤ E) (hne : pieces ≠ []) (hcov : circCover a r E Csq d m 0 pieces = true)
    {C wc : ℝ} (hC : 0 ≤ C) (hCsq : (Csq : ℝ) ≤ C ^ 2) (hEw : (E : ℝ) ≤ Real.exp (2 * wc)) :
    GapCircleBound P (a : ℝ) (r : ℝ) C wc := by
  intro N z hN hz
  have hs0 : |z.re| ≤ (r : ℝ) := by simpa only [hz] using Complex.abs_re_le_norm z
  obtain ⟨p, hpm, hpok, hlo, hhi⟩ :=
    circCover_exists hcov (by simp) hs0 (Or.inr hne)
  have hb := CircPiece.bound ha0 ha1 p hpok N z hz ⟨hlo, hhi⟩
  have hmN : P.h N + P.q N = m * N := by
    simp only [Parameters.h, Parameters.q]
    rw [← add_mul, hm]
  rw [hmN, hd]
  have hexp : (Real.exp (2 * wc)) ^ N = Real.exp (wc * N) ^ 2 := by
    rw [← Real.exp_nat_mul, sq, ← Real.exp_add]; congr 1; ring
  have hmain : (‖((gapPolyK (a : ℝ) ((d * N + 1) / 2)).map (algebraMap ℝ ℂ)).eval z‖ *
      ‖(1 : ℂ) - z‖ ^ (m * N)) ^ 2 ≤ (C * Real.exp (wc * N)) ^ 2 := by
    calc _ ≤ (Csq : ℝ) * (E : ℝ) ^ N := hb
      _ ≤ C ^ 2 * (Real.exp (2 * wc)) ^ N := by
          exact mul_le_mul hCsq (pow_le_pow_left₀ hE0 hEw N) (pow_nonneg hE0 N) (sq_nonneg C)
      _ = _ := by rw [hexp, mul_pow]
  exact le_of_pow_le_pow_left₀ two_ne_zero (by positivity) hmain

end

end Analytic
end CatalanMeasure.GenD
