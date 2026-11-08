module

public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.Convex.Slope
public import Mathlib.Analysis.SpecialFunctions.Arcosh
public import CatalanMeasure.GenD.Signed.LogEval
public import CatalanMeasure.GenD.Signed.RouteI.IntervalNodesData
public import CatalanMeasure.GenD.Signed.DesignConst

@[expose] public section

set_option Elab.async false

/-!
# Route I `HCirc`: the contour hypotheses (hcirc) and (hseg) of the terminal (ledger G34, GP Prop. 4.4, C10 and E8)

`hcirc_d` and `hseg_d` are exactly the hypotheses `hcirc`, `hseg` of `TerminalC.hweights_d`
(`ivlL` of the 106 intervals of design C, `D = 3.2506`, `ζ = 3/4`).

* (hcirc).  On `|z| = 3/4` write `z = (3/4)(s + i √(1-s²))`.  Every `|z - t|²` is the affine function
  `qq t s = 9/16 + t² - (3/2) t s` of `s`, so `6 log|1-z| + ivlL z = FF s` with
  `FF s = 3 log (qq 1 s) + ½ Σ_n (arcosh (HH_n s) + log (w_n/4))`, `HH_n s = (√qq lo_n + √qq hi_n)/w_n`.
  `FF` is concave on `[-1, 1]` (`concaveOn_FF`: logs and square roots of affine functions are concave, `arcosh`
  is concave and monotone, via convexity of `cosh`).  A concave function lies below its secants outside the
  secant's range (`concave_three`), so three values `FF p0, FF p1, FF p2` at points around the maximum
  bound `FF` on all of `[-1, 1]` (`FF_le`).  The three values are enclosed in the kernel from the interval
  ends already in `IntervalNodesData`: checked integer square roots (`isqrt`/`sqB`), exact rational running
  product (`prodB`) and one `logQ` per bound (`encF`).  No certificate data.
* (hseg).  Closed form: `exp(G_c + log(w_c/4)) ≤ max(w_c, X_c)/2`, product over the 106 intervals (`segP`),
  one `logQ` per side (`segChk`).  Room 25.9 (right) and 12.7 (left).
-/
namespace CatalanMeasure.GenD.Signed.RouteI.HCirc

open Set Real Finset
open CatalanMeasure.GenD.Analytic CatalanMeasure.GenD.Signed.RouteI CatalanMeasure.GenD.Signed.RouteI.IntervalNodesData CatalanMeasure.GenD.Signed.LogEval

noncomputable section

/-! ### Concavity in `s = cos θ` -/

/-- Squared distance from the point of abscissa `3s/4` on the circle `|z| = 3/4` to `t`. -/
def qq (t s : ℝ) : ℝ := 9 / 16 + t ^ 2 - 3 / 2 * t * s

theorem qq_nonneg (t : ℝ) {s : ℝ} (hs : |s| ≤ 1) : 0 ≤ qq t s := by
  have h1 : s ^ 2 ≤ 1 := by
    have := abs_le.mp hs
    nlinarith
  unfold qq
  nlinarith [sq_nonneg (t - 3 * s / 4)]

theorem qq_affine (t x y a b : ℝ) (hab : a + b = 1) :
    qq t (a * x + b * y) = a * qq t x + b * qq t y := by
  unfold qq
  have : b = 1 - a := by linarith
  subst this
  ring

theorem concaveOn_sqrt_qq (t : ℝ) : ConcaveOn ℝ (Icc (-1 : ℝ) 1) (fun s => √(qq t s)) := by
  refine ⟨convex_Icc _ _, ?_⟩
  intro x hx y hy a b ha hb hab
  have hx' : |x| ≤ 1 := abs_le.mpr ⟨hx.1, hx.2⟩
  have hy' : |y| ≤ 1 := abs_le.mpr ⟨hy.1, hy.2⟩
  have hu := qq_nonneg t hx'
  have hv := qq_nonneg t hy'
  simp only [smul_eq_mul]
  rw [qq_affine t x y a b hab]
  have su := Real.sq_sqrt hu
  have sv := Real.sq_sqrt hv
  have h0 : 0 ≤ a * √(qq t x) + b * √(qq t y) :=
    add_nonneg (mul_nonneg ha (Real.sqrt_nonneg _)) (mul_nonneg hb (Real.sqrt_nonneg _))
  apply Real.le_sqrt_of_sq_le
  have hb' : b = 1 - a := by linarith
  subst hb'
  nlinarith [mul_nonneg (mul_nonneg ha hb) (sq_nonneg (√(qq t x) - √(qq t y)))]

theorem concaveOn_log_qq1 : ConcaveOn ℝ (Icc (-1 : ℝ) 1) (fun s => Real.log (qq 1 s)) := by
  refine ⟨convex_Icc _ _, ?_⟩
  intro x hx y hy a b ha hb hab
  have px : 0 < qq 1 x := by unfold qq; linarith [hx.2]
  have py : 0 < qq 1 y := by unfold qq; linarith [hy.2]
  have h := strictConcaveOn_log_Ioi.concaveOn.2 (show qq 1 x ∈ Ioi (0:ℝ) from px)
    (show qq 1 y ∈ Ioi (0:ℝ) from py) ha hb hab
  simp only [smul_eq_mul] at h ⊢
  rw [qq_affine 1 x y a b hab]
  exact h

theorem cosh_convex_comb (x y a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    Real.cosh (a * x + b * y) ≤ a * Real.cosh x + b * Real.cosh y := by
  have h1 := convexOn_exp.2 (Set.mem_univ x) (Set.mem_univ y) ha hb hab
  have h2 := convexOn_exp.2 (Set.mem_univ (-x)) (Set.mem_univ (-y)) ha hb hab
  simp only [smul_eq_mul] at h1 h2
  rw [Real.cosh_eq, Real.cosh_eq, Real.cosh_eq]
  have e : -(a * x + b * y) = a * (-x) + b * (-y) := by ring
  rw [e]
  linarith

theorem concaveOn_arcosh_comp {s : Set ℝ} {H : ℝ → ℝ} (hs : Convex ℝ s) (hH : ConcaveOn ℝ s H)
    (h1 : ∀ x ∈ s, 1 ≤ H x) : ConcaveOn ℝ s (fun x => Real.arcosh (H x)) := by
  refine ⟨hs, ?_⟩
  intro x hx y hy a b ha hb hab
  simp only [smul_eq_mul]
  have hm : 0 ≤ a * Real.arcosh (H x) + b * Real.arcosh (H y) :=
    add_nonneg (mul_nonneg ha (Real.arcosh_nonneg (h1 x hx)))
      (mul_nonneg hb (Real.arcosh_nonneg (h1 y hy)))
  have hc := cosh_convex_comb (Real.arcosh (H x)) (Real.arcosh (H y)) a b ha hb hab
  rw [Real.cosh_arcosh (h1 x hx), Real.cosh_arcosh (h1 y hy)] at hc
  have hHm := hH.2 hx hy ha hb hab
  simp only [smul_eq_mul] at hHm
  have hmix : 1 ≤ H (a * x + b * y) := h1 _ (hs hx hy ha hb hab)
  have hle : Real.cosh (a * Real.arcosh (H x) + b * Real.arcosh (H y)) ≤ H (a * x + b * y) :=
    hc.trans hHm
  have := (Real.arcosh_le_arcosh (by positivity : 0 < Real.cosh (a * Real.arcosh (H x) + b * Real.arcosh (H y)))
    (by linarith : 0 < H (a * x + b * y))).mpr hle
  rwa [Real.arcosh_cosh hm] at this

theorem concaveOn_finset_sum {ι : Type*} {s : Set ℝ} (hs : Convex ℝ s) (u : Finset ι) (f : ι → ℝ → ℝ)
    (h : ∀ i ∈ u, ConcaveOn ℝ s (f i)) : ConcaveOn ℝ s (fun x => ∑ i ∈ u, f i x) := by
  classical
  induction u using Finset.induction_on with
  | empty => simpa using concaveOn_const (0 : ℝ) hs
  | insert i u hi ih =>
    have h1 := h i (Finset.mem_insert_self _ _)
    have h2 := ih fun j hj => h j (Finset.mem_insert_of_mem hj)
    refine ⟨hs, ?_⟩
    intro x hx y hy a b ha hb hab
    have e1 := h1.2 hx hy ha hb hab
    have e2 := h2.2 hx hy ha hb hab
    simp only [smul_eq_mul, Finset.sum_insert hi] at e1 e2 ⊢
    linarith

/-! ### Three-point bound for a concave function -/

theorem concave_three {f : ℝ → ℝ} {s : Set ℝ} (hf : ConcaveOn ℝ s f) {p0 p1 p2 : ℝ}
    (h01 : p0 < p1) (h12 : p1 < p2) (m0 : p0 ∈ s) (m1 : p1 ∈ s) (m2 : p2 ∈ s) {x : ℝ} (hx : x ∈ s) :
    (x ≤ p1 → f x ≤ f p1 + (f p2 - f p1) / (p2 - p1) * (x - p1)) ∧
    (p1 ≤ x → x ≤ p2 → f x ≤ f p1 + (f p1 - f p0) / (p1 - p0) * (x - p1)) ∧
    (p2 ≤ x → f x ≤ f p2 + (f p2 - f p1) / (p2 - p1) * (x - p2)) := by
  refine ⟨fun h => ?_, fun h h' => ?_, fun h => ?_⟩
  · rcases h.eq_or_lt with rfl | h
    · simp
    · have := hf.slope_anti_adjacent hx m2 h h12
      have hpos : 0 < p1 - x := by linarith
      rw [div_le_div_iff₀ (by linarith) hpos] at this
      have e : (f p2 - f p1) / (p2 - p1) * (x - p1) = -((f p2 - f p1) / (p2 - p1) * (p1 - x)) := by ring
      rw [e]
      have h3 : (f p2 - f p1) / (p2 - p1) * (p1 - x) ≤ f p1 - f x := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
        nlinarith
      linarith
  · rcases h.eq_or_lt with rfl | h
    · simp
    · have := hf.slope_anti_adjacent m0 hx h01 h
      have hpos : 0 < x - p1 := by linarith
      rw [div_le_div_iff₀ hpos (by linarith)] at this
      have h3 : f x - f p1 ≤ (f p1 - f p0) / (p1 - p0) * (x - p1) := by
        rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
        nlinarith
      linarith
  · rcases h.eq_or_lt with rfl | h
    · simp
    · have := hf.slope_anti_adjacent m1 hx h12 h
      have hpos : 0 < x - p2 := by linarith
      rw [div_le_div_iff₀ hpos (by linarith)] at this
      have h3 : f x - f p2 ≤ (f p2 - f p1) / (p2 - p1) * (x - p2) := by
        rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
        nlinarith
      linarith

/-! ### The circle point and the link to `ivlL` -/

/-- The point of the circle `|z| = 3/4` with abscissa `3s/4` and nonnegative ordinate. -/
def zc (s : ℝ) : ℂ := ⟨3 * s / 4, 3 / 4 * √(1 - s ^ 2)⟩

theorem norm_sub_real {z : ℂ} (hz : ‖z‖ = 3 / 4) (t : ℝ) :
    ‖z - (t : ℂ)‖ = √(qq t (4 * z.re / 3)) := by
  rw [Complex.norm_def, Complex.normSq_apply]
  congr 1
  have h2 := Complex.sq_norm_sub_sq_re z
  rw [hz] at h2
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, sub_zero]
  unfold qq
  nlinarith [h2]

theorem abs_re_le_of_norm {z : ℂ} (hz : ‖z‖ = 3 / 4) : |4 * z.re / 3| ≤ 1 := by
  have h : |z.re| ≤ 3 / 4 := hz ▸ Complex.abs_re_le_norm z
  rw [abs_div, abs_mul]
  norm_num
  linarith

theorem norm_zc {s : ℝ} (hs : |s| ≤ 1) : ‖zc s‖ = 3 / 4 := by
  have h1 : s ^ 2 ≤ 1 := by
    have := abs_le.mp hs
    nlinarith
  rw [Complex.norm_def, Complex.normSq_apply]
  have : (zc s).re * (zc s).re + (zc s).im * (zc s).im = (3 / 4) ^ 2 := by
    simp only [zc]
    have := Real.sq_sqrt (show 0 ≤ 1 - s ^ 2 by linarith)
    nlinarith [this]
  rw [this, Real.sqrt_sq (by norm_num)]

theorem re_zc (s : ℝ) : 4 * (zc s).re / 3 = s := by simp only [zc]; ring

/-- Green function of an interval in terms of the distances. -/
theorem ivlGreen_eq {lo hi : ℝ} (hlt : lo < hi) (z : ℂ) :
    ivlGreen lo hi z = Real.arcosh ((‖z - (lo : ℂ)‖ + ‖z - (hi : ℂ)‖) / (hi - lo)) := by
  have hne : ((hi - lo : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (sub_pos.mpr hlt).ne'
  have hpos : (0 : ℝ) < hi - lo := sub_pos.mpr hlt
  unfold ivlGreen ellipseLog ellipseH ivlCoord
  congr 1
  have e1 : (2 * z - ((lo + hi : ℝ) : ℂ)) / ((hi - lo : ℝ) : ℂ) - 1 =
      ((2 / ((hi - lo : ℝ) : ℂ)) : ℂ) * (z - (hi : ℂ)) := by
    push_cast at hne ⊢
    field_simp
    ring
  have e2 : (2 * z - ((lo + hi : ℝ) : ℂ)) / ((hi - lo : ℝ) : ℂ) + 1 =
      ((2 / ((hi - lo : ℝ) : ℂ)) : ℂ) * (z - (lo : ℂ)) := by
    push_cast at hne ⊢
    field_simp
    ring
  rw [e1, e2, norm_mul, norm_mul]
  have hn : ‖(2 / ((hi - lo : ℝ) : ℂ) : ℂ)‖ = 2 / (hi - lo) := by
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hpos.le]
    simp
  rw [hn]
  field_simp
  ring

def HH (l h s : ℝ) : ℝ := (√(qq l s) + √(qq h s)) / (h - l)

theorem HH_ge_one {l h : ℝ} (hlt : l < h) {s : ℝ} (hs : |s| ≤ 1) : 1 ≤ HH l h s := by
  have hz := norm_zc hs
  have e1 := norm_sub_real hz l
  have e2 := norm_sub_real hz h
  rw [re_zc] at e1 e2
  have tri : ‖(h : ℂ) - (l : ℂ)‖ ≤ ‖zc s - (l : ℂ)‖ + ‖zc s - (h : ℂ)‖ := by
    have := norm_sub_le (zc s - (l : ℂ)) (zc s - (h : ℂ))
    rw [show zc s - (l : ℂ) - (zc s - (h : ℂ)) = (h : ℂ) - (l : ℂ) by ring] at this
    exact this
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_of_nonneg (sub_pos.mpr hlt).le, e1, e2] at tri
  unfold HH
  rw [le_div_iff₀ (sub_pos.mpr hlt)]
  linarith

theorem concaveOn_HH {l h : ℝ} (hlt : l < h) :
    ConcaveOn ℝ (Icc (-1 : ℝ) 1) (HH l h) := by
  refine ⟨convex_Icc _ _, ?_⟩
  intro x hx y hy a b ha hb hab
  have c1 := (concaveOn_sqrt_qq l).2 hx hy ha hb hab
  have c2 := (concaveOn_sqrt_qq h).2 hx hy ha hb hab
  simp only [smul_eq_mul] at c1 c2 ⊢
  have hd : 0 < h - l := sub_pos.mpr hlt
  unfold HH
  rw [← mul_div_assoc, ← mul_div_assoc, ← add_div, div_le_div_iff_of_pos_right hd]
  linarith

theorem concaveOn_arcosh_HH {l h : ℝ} (hlt : l < h) :
    ConcaveOn ℝ (Icc (-1 : ℝ) 1) (fun s => Real.arcosh (HH l h s)) :=
  concaveOn_arcosh_comp (convex_Icc _ _) (concaveOn_HH hlt)
    (fun s hs => HH_ge_one hlt (abs_le.mpr ⟨hs.1, hs.2⟩))

/-! ### The function `FF` -/

def loN (n : ℕ) : ℝ := ((ivlAN.getD n 0 : ℤ) : ℝ) / 2 ^ 40
def hiN (n : ℕ) : ℝ := ((ivlBN.getD n 0 : ℤ) : ℝ) / 2 ^ 40

theorem loN_lt {n : ℕ} (hn : n < 106) : loN n < hiN n := loF_lt ⟨n, hn⟩

/-- the `n`-th term `G_n(s) + log(w_n/4)` -/
def gt (n : ℕ) (s : ℝ) : ℝ := Real.arcosh (HH (loN n) (hiN n) s) + Real.log ((hiN n - loN n) / 4)

def FF (s : ℝ) : ℝ := 3 * Real.log (qq 1 s) + (1 / 2) * ∑ n ∈ range 106, gt n s

theorem concaveOn_gt {n : ℕ} (hn : n < 106) : ConcaveOn ℝ (Icc (-1 : ℝ) 1) (gt n) := by
  have h := concaveOn_arcosh_HH (loN_lt hn)
  refine ⟨convex_Icc _ _, ?_⟩
  intro x hx y hy a b ha hb hab
  have := h.2 hx hy ha hb hab
  simp only [smul_eq_mul] at this ⊢
  unfold gt
  have : a * Real.log ((hiN n - loN n) / 4) + b * Real.log ((hiN n - loN n) / 4) =
      Real.log ((hiN n - loN n) / 4) := by rw [← add_mul, hab, one_mul]
  nlinarith [this]

theorem concaveOn_FF : ConcaveOn ℝ (Icc (-1 : ℝ) 1) FF := by
  have hs := concaveOn_finset_sum (convex_Icc (-1 : ℝ) 1) (range 106) gt
    (fun n hn => concaveOn_gt (Finset.mem_range.mp hn))
  refine ⟨convex_Icc _ _, ?_⟩
  intro x hx y hy a b ha hb hab
  have e1 := concaveOn_log_qq1.2 hx hy ha hb hab
  have e2 := hs.2 hx hy ha hb hab
  simp only [smul_eq_mul] at e1 e2 ⊢
  unfold FF
  nlinarith [e1, e2]

/-- `ivlL` on the circle is `FF`. -/
theorem ivlL_eq {z : ℂ} (hz : ‖z‖ = 3 / 4) :
    ivlL ivlLo ivlHi z = (1 / 2) * ∑ n ∈ range 106, gt n (4 * z.re / 3) := by
  have h1 : ∀ c : Fin 53 × Fin 2, ivlGreen (ivlLo c) (ivlHi c) z + Real.log ((ivlHi c - ivlLo c) / 4) =
      gt (finProdFinEquiv c : ℕ) (4 * z.re / 3) := by
    intro c
    have hlt := ivlLo_lt c
    rw [ivlGreen_eq hlt, norm_sub_real hz, norm_sub_real hz, gt, HH]
    unfold ivlLo ivlHi loF hiF loN hiN
    rfl
  have h2 : ∑ c : Fin 53 × Fin 2, (ivlGreen (ivlLo c) (ivlHi c) z + Real.log ((ivlHi c - ivlLo c) / 4)) =
      ∑ n ∈ range 106, gt n (4 * z.re / 3) := by
    rw [Finset.sum_congr rfl (fun c _ => h1 c)]
    rw [Fintype.sum_equiv finProdFinEquiv _ (fun i : Fin (53 * 2) => gt (i : ℕ) (4 * z.re / 3)) (fun c => rfl)]
    exact Fin.sum_univ_eq_sum_range (fun n => gt n (4 * z.re / 3)) (53 * 2)
  unfold ivlL
  rw [h2]

/-! ### The verified evaluation (integer square roots by Newton, checked) -/

def isqrtAux : ℕ → ℕ → ℕ → ℕ
  | 0, _, x => x
  | k + 1, n, x => isqrtAux k n ((x + n / x) / 2)

/-- Candidate integer square root; only its check `r² ≤ n < (r+1)²` is used. -/
def isqrt (n : ℕ) : ℕ :=
  let x := isqrtAux 40 n (2 ^ (n.log2 / 2 + 1))
  if x * x ≤ n then x else x - 1

/-- `r` with `r² ≤ ⌊q 4^P⌋ < (r+1)²` (flag), for `q ≥ 0`. -/
def sqB (P : ℕ) (q : ℚ) : ℕ × Bool :=
  let n := q.num.toNat * 4 ^ P / q.den
  let r := isqrt n
  (r, decide (r * r ≤ n) && decide (n < (r + 1) * (r + 1)))

theorem sqB_spec {P : ℕ} {q : ℚ} (hq : 0 ≤ q) (h : (sqB P q).2 = true) :
    (((sqB P q).1 : ℕ) : ℝ) / 2 ^ P ≤ √(q : ℝ) ∧ √(q : ℝ) ≤ ((((sqB P q).1 : ℕ) : ℝ) + 1) / 2 ^ P := by
  unfold sqB at h ⊢
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h
  generalize hn : q.num.toNat * 4 ^ P / q.den = n at h1 h2 ⊢
  obtain ⟨r, hr⟩ : ∃ r, isqrt n = r := ⟨_, rfl⟩
  rw [hr] at h1 h2
  show ((isqrt n : ℕ) : ℝ) / 2 ^ P ≤ √(q : ℝ) ∧ √(q : ℝ) ≤ (((isqrt n : ℕ) : ℝ) + 1) / 2 ^ P
  rw [hr]
  have hden : (0 : ℝ) < q.den := by exact_mod_cast q.den_pos
  have hnum : (q.num.toNat : ℝ) = (q.num : ℝ) := by
    have : (q.num.toNat : ℤ) = q.num := Int.toNat_of_nonneg (Rat.num_nonneg.mpr hq)
    exact_mod_cast this
  have hqR : (q : ℝ) = (q.num.toNat : ℝ) / q.den := by
    rw [hnum]; exact_mod_cast Rat.num_div_den q |>.symm
  have hd0 : 0 < q.den := q.den_pos
  have e1 : n * q.den ≤ q.num.toNat * 4 ^ P := by
    rw [← hn]; exact Nat.div_mul_le_self _ _
  have e2 : q.num.toNat * 4 ^ P < q.den * (n + 1) := by
    rw [← hn]; exact Nat.lt_mul_div_succ _ hd0
  have f1 : (n : ℝ) ≤ (q : ℝ) * 4 ^ P := by
    rw [hqR, div_mul_eq_mul_div, le_div_iff₀ hden]
    exact_mod_cast e1
  have f2 : (q : ℝ) * 4 ^ P < n + 1 := by
    rw [hqR, div_mul_eq_mul_div, div_lt_iff₀ hden]
    have : ((q.num.toNat * 4 ^ P : ℕ) : ℝ) < ((q.den * (n + 1) : ℕ) : ℝ) := by exact_mod_cast e2
    push_cast at this
    linarith
  have g1 : (r : ℝ) * r ≤ n := by exact_mod_cast h1
  have g2 : (n : ℝ) + 1 ≤ (r + 1) * (r + 1) := by
    have : n + 1 ≤ (r + 1) * (r + 1) := h2
    exact_mod_cast this
  have h4 : (0 : ℝ) < 4 ^ P := by positivity
  have h2P : (0 : ℝ) < 2 ^ P := by positivity
  have h4e : ((2 : ℝ) ^ P) ^ 2 = 4 ^ P := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  constructor
  · apply Real.le_sqrt_of_sq_le
    rw [div_pow, h4e, div_le_iff₀ h4]
    nlinarith
  · rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    rw [div_pow, h4e, le_div_iff₀ h4]
    nlinarith

/-- Bounds `ρ⁻ ≤ H + √(H²-1) ≤ ρ⁺` for `H = (√ql + √qh)/h`, with the flag of all root checks. -/
def rhoB (P : ℕ) (ql qh h : ℚ) : ℚ × ℚ × Bool :=
  let a := sqB P ql
  let b := sqB P qh
  let Hl : ℚ := ((a.1 + b.1 : ℕ) : ℚ) / (2 ^ P * h)
  let Hu : ℚ := ((a.1 + b.1 + 2 : ℕ) : ℚ) / (2 ^ P * h)
  let c := sqB P (Hl ^ 2 - 1)
  let d := sqB P (Hu ^ 2 - 1)
  (Hl + (c.1 : ℚ) / 2 ^ P, Hu + ((d.1 : ℚ) + 1) / 2 ^ P,
    a.2 && b.2 && c.2 && d.2 && decide (1 ≤ Hl) && decide (0 < h))

theorem rho_spec' {P : ℕ} {ql qh h : ℚ} (hql : 0 ≤ ql) (hqh : 0 ≤ qh) (hh : 0 < h)
    (Hl Hu : ℚ)
    (hHl : Hl = (((sqB P ql).1 + (sqB P qh).1 : ℕ) : ℚ) / (2 ^ P * h))
    (hHu : Hu = (((sqB P ql).1 + (sqB P qh).1 + 2 : ℕ) : ℚ) / (2 ^ P * h))
    (ha : (sqB P ql).2 = true) (hb : (sqB P qh).2 = true)
    (hc : (sqB P (Hl ^ 2 - 1)).2 = true) (hd : (sqB P (Hu ^ 2 - 1)).2 = true) (h1 : 1 ≤ Hl) :
    ((Hl + ((sqB P (Hl ^ 2 - 1)).1 : ℚ) / 2 ^ P : ℚ) : ℝ) ≤
        Real.exp (Real.arcosh ((√(ql : ℝ) + √(qh : ℝ)) / (h : ℝ))) ∧
    Real.exp (Real.arcosh ((√(ql : ℝ) + √(qh : ℝ)) / (h : ℝ))) ≤
        ((Hu + (((sqB P (Hu ^ 2 - 1)).1 : ℚ) + 1) / 2 ^ P : ℚ) : ℝ) ∧
    (1 : ℝ) ≤ ((Hl + ((sqB P (Hl ^ 2 - 1)).1 : ℚ) / 2 ^ P : ℚ) : ℝ) := by
  have s1 := sqB_spec hql ha
  have s2 := sqB_spec hqh hb
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  have h2P : (0 : ℝ) < 2 ^ P := by positivity
  have hHlu : Hl ≤ Hu := by
    rw [hHl, hHu]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast Nat.le_add_right _ _
  have hHu1 : 1 ≤ Hu := h1.trans hHlu
  have hc0 : 0 ≤ Hl ^ 2 - 1 := by nlinarith
  have hd0 : 0 ≤ Hu ^ 2 - 1 := by nlinarith
  have s3 := sqB_spec hc0 hc
  have s4 := sqB_spec hd0 hd
  set A := ((sqB P ql).1 : ℝ) with hA
  set B := ((sqB P qh).1 : ℝ) with hB
  set Cc := ((sqB P (Hl ^ 2 - 1)).1 : ℝ) with hC
  set Dd := ((sqB P (Hu ^ 2 - 1)).1 : ℝ) with hD
  set H : ℝ := (√(ql : ℝ) + √(qh : ℝ)) / (h : ℝ) with hH
  have hHlR : (Hl : ℝ) = (A + B) / (2 ^ P * h) := by
    rw [hHl]; push_cast; rfl
  have hHuR : (Hu : ℝ) = (A + B + 2) / (2 ^ P * h) := by
    rw [hHu]; push_cast; rfl
  have hlH : (Hl : ℝ) ≤ H := by
    have e : (Hl : ℝ) = ((A + B) / 2 ^ P) / h := by rw [hHlR]; field_simp
    rw [e, hH]
    apply div_le_div_of_nonneg_right _ hhR.le
    rw [add_div]
    linarith [s1.1, s2.1]
  have hHu' : H ≤ (Hu : ℝ) := by
    have e : (Hu : ℝ) = ((A + B + 2) / 2 ^ P) / h := by rw [hHuR]; field_simp
    rw [e, hH]
    apply div_le_div_of_nonneg_right _ hhR.le
    have : (A + B + 2) / 2 ^ P = (A + 1) / 2 ^ P + (B + 1) / 2 ^ P := by ring
    rw [this]
    linarith [s1.2, s2.2]
  have h1R : (1 : ℝ) ≤ Hl := by exact_mod_cast h1
  have hH1 : 1 ≤ H := h1R.trans hlH
  have hexp : Real.exp (Real.arcosh H) = H + √(H ^ 2 - 1) := Real.exp_arcosh hH1
  rw [hexp]
  have c3 : Cc / 2 ^ P ≤ √((Hl : ℝ) ^ 2 - 1) := by
    have := s3.1; push_cast at this; exact this
  have c4 : √((Hu : ℝ) ^ 2 - 1) ≤ (Dd + 1) / 2 ^ P := by
    have := s4.2; push_cast at this; exact this
  refine ⟨?_, ?_, ?_⟩
  · push_cast
    have : √((Hl : ℝ) ^ 2 - 1) ≤ √(H ^ 2 - 1) := Real.sqrt_le_sqrt (by nlinarith)
    linarith
  · push_cast
    have : √(H ^ 2 - 1) ≤ √((Hu : ℝ) ^ 2 - 1) := Real.sqrt_le_sqrt (by nlinarith)
    linarith
  · push_cast
    have : (0:ℝ) ≤ Cc / 2 ^ P := div_nonneg (by rw [hC]; exact Nat.cast_nonneg _) h2P.le
    linarith

theorem rhoB_spec {P : ℕ} {ql qh h : ℚ} (hql : 0 ≤ ql) (hqh : 0 ≤ qh)
    (ok : (rhoB P ql qh h).2.2 = true) :
    (((rhoB P ql qh h).1 : ℚ) : ℝ) ≤ Real.exp (Real.arcosh ((√(ql : ℝ) + √(qh : ℝ)) / (h : ℝ))) ∧
    Real.exp (Real.arcosh ((√(ql : ℝ) + √(qh : ℝ)) / (h : ℝ))) ≤ (((rhoB P ql qh h).2.1 : ℚ) : ℝ) ∧
    (1 : ℝ) ≤ (((rhoB P ql qh h).1 : ℚ) : ℝ) := by
  unfold rhoB at ok ⊢
  simp only [Bool.and_eq_true, decide_eq_true_eq] at ok
  obtain ⟨⟨⟨⟨⟨ha, hb⟩, hc⟩, hd⟩, hH⟩, hh⟩ := ok
  exact rho_spec' hql hqh hh _ _ rfl rfl ha hb hc hd hH

def qqQ (t s : ℚ) : ℚ := 9 / 16 + t ^ 2 - 3 / 2 * t * s
def loQ (n : ℕ) : ℚ := ((ivlAN.getD n 0 : ℤ) : ℚ) / 2 ^ 40
def hiQ (n : ℕ) : ℚ := ((ivlBN.getD n 0 : ℤ) : ℚ) / 2 ^ 40

theorem qqQ_cast (t s : ℚ) : ((qqQ t s : ℚ) : ℝ) = qq (t : ℝ) (s : ℝ) := by
  unfold qqQ qq; push_cast; ring
theorem loQ_cast (n : ℕ) : ((loQ n : ℚ) : ℝ) = loN n := by
  unfold loQ loN; push_cast; rfl
theorem hiQ_cast (n : ℕ) : ((hiQ n : ℚ) : ℝ) = hiN n := by
  unfold hiQ hiN; push_cast; rfl

/-- Running enclosure `(Wl, Wh, ok)` of `q₁(s)^6 ∏_{k<n} exp(g_k(s))`. -/
def prodB (P : ℕ) (s : ℚ) : ℕ → ℚ × ℚ × Bool
  | 0 => (qqQ 1 s ^ 6, qqQ 1 s ^ 6, true)
  | n + 1 =>
    let r := prodB P s n
    let x := rhoB P (qqQ (loQ n) s) (qqQ (hiQ n) s) (hiQ n - loQ n)
    (r.1 * (x.1 * ((hiQ n - loQ n) / 4)), r.2.1 * (x.2.1 * ((hiQ n - loQ n) / 4)),
      r.2.2 && x.2.2)

theorem exp_gt {n : ℕ} (hn : n < 106) (s : ℝ) :
    Real.exp (gt n s) = Real.exp (Real.arcosh (HH (loN n) (hiN n) s)) * ((hiN n - loN n) / 4) := by
  unfold gt
  rw [Real.exp_add, Real.exp_log (by have := loN_lt hn; linarith)]

theorem prodB_spec {P : ℕ} {s : ℚ} (hs : |(s : ℝ)| ≤ 1) :
    ∀ n, n ≤ 106 → (prodB P s n).2.2 = true →
      (((prodB P s n).1 : ℚ) : ℝ) ≤ qq 1 s ^ 6 * ∏ k ∈ range n, Real.exp (gt k s) ∧
      qq 1 s ^ 6 * ∏ k ∈ range n, Real.exp (gt k s) ≤ (((prodB P s n).2.1 : ℚ) : ℝ) := by
  intro n
  induction n with
  | zero =>
    intro _ _
    simp only [prodB, Finset.range_zero, Finset.prod_empty, mul_one]
    push_cast
    have : ((qqQ 1 s : ℚ) : ℝ) = qq 1 s := by rw [qqQ_cast]; simp
    rw [this]
    exact ⟨le_refl _, le_refl _⟩
  | succ n ih =>
    intro hn ok
    have hn' : n < 106 := by omega
    simp only [prodB, Bool.and_eq_true] at ok
    obtain ⟨ok1, ok2⟩ := ok
    have ih' := ih (by omega) ok1
    have hlt := loN_lt hn'
    have hq1 : 0 ≤ qq (loN n) (s : ℝ) := qq_nonneg _ hs
    have hq2 : 0 ≤ qq (hiN n) (s : ℝ) := qq_nonneg _ hs
    have hr := rhoB_spec (P := P) (ql := qqQ (loQ n) s) (qh := qqQ (hiQ n) s) (h := hiQ n - loQ n)
      (by have : (0:ℝ) ≤ ((qqQ (loQ n) s : ℚ) : ℝ) := by rw [qqQ_cast, loQ_cast]; exact qq_nonneg _ hs
          exact_mod_cast this)
      (by have : (0:ℝ) ≤ ((qqQ (hiQ n) s : ℚ) : ℝ) := by rw [qqQ_cast, hiQ_cast]; exact qq_nonneg _ hs
          exact_mod_cast this) ok2
    have e1 : ((qqQ (loQ n) s : ℚ) : ℝ) = qq (loN n) (s : ℝ) := by rw [qqQ_cast, loQ_cast]
    have e2 : ((qqQ (hiQ n) s : ℚ) : ℝ) = qq (hiN n) (s : ℝ) := by rw [qqQ_cast, hiQ_cast]
    have e3 : (((hiQ n - loQ n : ℚ)) : ℝ) = hiN n - loN n := by push_cast; rw [loQ_cast, hiQ_cast]
    rw [e1, e2, e3] at hr
    have hH : (√(qq (loN n) (s : ℝ)) + √(qq (hiN n) (s : ℝ))) / (hiN n - loN n) =
        HH (loN n) (hiN n) s := rfl
    rw [hH] at hr
    rw [Finset.prod_range_succ, exp_gt hn']
    have hw : (0 : ℝ) < (hiN n - loN n) / 4 := by linarith
    have hpos : 0 ≤ qq 1 s ^ 6 * ∏ k ∈ range n, Real.exp (gt k s) :=
      mul_nonneg (by positivity) (Finset.prod_nonneg fun k _ => (Real.exp_pos _).le)
    simp only [prodB]
    push_cast
    simp only [loQ_cast, hiQ_cast]
    constructor
    · have := mul_le_mul ih'.1 (mul_le_mul_of_nonneg_right hr.1 hw.le)
        (mul_nonneg (by linarith [hr.2.2]) hw.le) hpos
      calc _ ≤ _ := this
        _ = _ := by ring
    · have := mul_le_mul ih'.2 (mul_le_mul_of_nonneg_right hr.2.1 hw.le)
        (mul_nonneg (Real.exp_pos _).le hw.le) (le_trans hpos ih'.2)
      calc _ = _ := by ring
        _ ≤ _ := this

theorem exp_two_FF {s : ℝ} (hs : |s| ≤ 1) :
    Real.exp (2 * FF s) = qq 1 s ^ 6 * ∏ k ∈ range 106, Real.exp (gt k s) := by
  have hq : 0 < qq 1 s := by
    have := abs_le.mp hs
    unfold qq; linarith [this.2]
  have : 2 * FF s = ((6 : ℕ) : ℝ) * Real.log (qq 1 s) + ∑ k ∈ range 106, gt k s := by
    unfold FF; push_cast; ring
  rw [this, Real.exp_add, Real.exp_nat_mul, Real.exp_log hq, Real.exp_sum]

/-- Enclosure of `FF` from the two running bounds, by `logQ`. -/
def encW (nl : ℕ) (W : ℚ × ℚ × Bool) : Option (ℚ × ℚ) :=
  if W.2.2 = true then
    match logQ nl W.1, logQ nl W.2.1 with
    | some (v1, e1), some (v2, e2) => some ((v1 - e1) / 2, (v2 + e2) / 2)
    | _, _ => none
  else none

def encF (P nl : ℕ) (s : ℚ) : Option (ℚ × ℚ) := encW nl (prodB P s 106)

theorem encW_spec {nl : ℕ} {W : ℚ × ℚ × Bool} {X F : ℝ} {lo hi : ℚ}
    (hl : (W.1 : ℝ) ≤ X) (hh : X ≤ (W.2.1 : ℝ)) (hX : X = Real.exp (2 * F))
    (h : encW nl W = some (lo, hi)) (hok : W.2.2 = true) :
    (lo : ℝ) ≤ F ∧ F ≤ (hi : ℝ) := by
  unfold encW at h
  rw [if_pos hok] at h
  split at h
  · rename_i v1 e1 v2 e2 hl1 hl2
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    obtain ⟨hpl, h1⟩ := logQ_spec hl1
    obtain ⟨hph, h2⟩ := logQ_spec hl2
    have hXp : 0 < X := by rw [hX]; exact Real.exp_pos _
    have a1 := Real.log_le_log (by exact_mod_cast hpl) hl
    have a2 := Real.log_le_log hXp hh
    have hlx : Real.log X = 2 * F := by rw [hX, Real.log_exp]
    rw [hlx] at a1 a2
    unfold Enc at h1 h2
    have b1 := abs_le.mp h1
    have b2 := abs_le.mp h2
    push_cast
    constructor <;> linarith [b1.1, b1.2, b2.1, b2.2]
  · simp at h

theorem encW_ok {nl : ℕ} {W : ℚ × ℚ × Bool} {o : ℚ × ℚ} (h : encW nl W = some o) : W.2.2 = true := by
  unfold encW at h
  by_cases hb : W.2.2 = true
  · exact hb
  · rw [if_neg hb] at h; exact absurd h (by simp)

theorem encF_spec {P nl : ℕ} {s lo hi : ℚ} (hs : |(s : ℝ)| ≤ 1) (h : encF P nl s = some (lo, hi)) :
    (lo : ℝ) ≤ FF s ∧ FF s ≤ (hi : ℝ) := by
  have hok : (prodB P s 106).2.2 = true := encW_ok h
  have sp := prodB_spec (P := P) hs 106 le_rfl hok
  rw [← exp_two_FF hs] at sp
  exact encW_spec sp.1 sp.2 rfl h hok

/-- The check on an enclosure. -/
def chkW (L U : ℚ) : Option (ℚ × ℚ) → Bool
  | some (l, u) => decide (L ≤ l) && decide (u ≤ U)
  | none => false

theorem chkW_spec {L U : ℚ} {o : Option (ℚ × ℚ)} {F : ℝ}
    (h : chkW L U o = true) (hF : ∀ lo hi : ℚ, o = some (lo, hi) → (lo : ℝ) ≤ F ∧ F ≤ (hi : ℝ)) :
    (L : ℝ) ≤ F ∧ F ≤ (U : ℝ) := by
  cases o with
  | none => simp [chkW] at h
  | some p =>
    obtain ⟨l, u⟩ := p
    simp only [chkW, Bool.and_eq_true, decide_eq_true_eq] at h
    have := hF l u rfl
    exact ⟨le_trans (by exact_mod_cast h.1) this.1, le_trans this.2 (by exact_mod_cast h.2)⟩

/-- A point check: the enclosure lies inside `[L, U]`. -/
def chkPt (s L U : ℚ) : Bool := chkW L U (encF 64 12 s)

theorem chkPt_spec {s L U : ℚ} (hs : |(s : ℝ)| ≤ 1)
    (h : chkPt s L U = true) : (L : ℝ) ≤ FF s ∧ FF s ≤ (U : ℝ) :=
  chkW_spec h (fun lo hi e => encF_spec hs e)

def p0 : ℚ := -699447 / 4000000
def p1 : ℚ := -697447 / 4000000
def p2 : ℚ := -695447 / 4000000

theorem chk_p0 : chkPt p0 (3250522177992 / 10 ^ 12) (3250522177995 / 10 ^ 12) = true := by
  decide +kernel -- kcost: 3.7 s measured (profiler, Elab.async false, 7 Nov): 106 intervals x 4 checked integer square roots, exact rational product, one logQ per bound
theorem chk_p1 : chkPt p1 (3250528922124 / 10 ^ 12) (3250528922127 / 10 ^ 12) = true := by
  decide +kernel -- kcost: 4.8 s measured (profiler, Elab.async false, 7 Nov): 106 intervals x 4 checked integer square roots, exact rational product, one logQ per bound
theorem chk_p2 : chkPt p2 (3250528922266 / 10 ^ 12) (3250528922269 / 10 ^ 12) = true := by
  decide +kernel -- kcost: 7.5 s measured (profiler, Elab.async false, 7 Nov): 106 intervals x 4 checked integer square roots, exact rational product, one logQ per bound

theorem FF_le : ∀ s ∈ Icc (-1 : ℝ) 1, FF s ≤ 32506 / 10000 := by
  intro x hx
  have e0 : ((p0 : ℚ) : ℝ) = -699447 / 4000000 := by norm_num [p0]
  have e1 : ((p1 : ℚ) : ℝ) = -697447 / 4000000 := by norm_num [p1]
  have e2 : ((p2 : ℚ) : ℝ) = -695447 / 4000000 := by norm_num [p2]
  have a0 := chkPt_spec (by rw [e0]; rw [abs_le]; constructor <;> norm_num) chk_p0
  have a1 := chkPt_spec (by rw [e1]; rw [abs_le]; constructor <;> norm_num) chk_p1
  have a2 := chkPt_spec (by rw [e2]; rw [abs_le]; constructor <;> norm_num) chk_p2
  rw [e0] at a0; rw [e1] at a1; rw [e2] at a2
  push_cast at a0 a1 a2
  have hc := concaveOn_FF
  have m0 : (-699447 / 4000000 : ℝ) ∈ Icc (-1 : ℝ) 1 := by constructor <;> norm_num
  have m1 : (-697447 / 4000000 : ℝ) ∈ Icc (-1 : ℝ) 1 := by constructor <;> norm_num
  have m2 : (-695447 / 4000000 : ℝ) ∈ Icc (-1 : ℝ) 1 := by constructor <;> norm_num
  obtain ⟨c1, c2, c3⟩ := concave_three hc (by norm_num : (-699447 / 4000000 : ℝ) < -697447 / 4000000)
    (by norm_num : (-697447 / 4000000 : ℝ) < -695447 / 4000000) m0 m1 m2 hx
  set f0 := FF (-699447 / 4000000) with hf0
  set f1 := FF (-697447 / 4000000) with hf1
  set f2 := FF (-695447 / 4000000) with hf2
  obtain ⟨hx1, hx2⟩ := hx
  rcases le_total x (-697447 / 4000000) with h | h
  · have k := c1 h
    have : (f2 - f1) / (-695447 / 4000000 - -697447 / 4000000) * (x - -697447 / 4000000) =
        2000 * (f2 - f1) * (x - -697447 / 4000000) := by ring
    rw [this] at k
    by_cases hs : f1 - f2 ≤ 0
    · nlinarith [a1.2, mul_nonneg (by linarith : (0:ℝ) ≤ -697447 / 4000000 - x) (by linarith : (0:ℝ) ≤ -(f1 - f2))]
    · push_neg at hs
      nlinarith [a1.2, a2.1, mul_nonneg (by linarith : (0:ℝ) ≤ x + 1) hs.le]
  · rcases le_total x (-695447 / 4000000) with h' | h'
    · have k := c2 h h'
      have : (f1 - f0) / (-697447 / 4000000 - -699447 / 4000000) * (x - -697447 / 4000000) =
          2000 * (f1 - f0) * (x - -697447 / 4000000) := by ring
      rw [this] at k
      by_cases hs : f1 - f0 ≤ 0
      · nlinarith [a1.2, mul_nonneg (by linarith : (0:ℝ) ≤ x - -697447 / 4000000) (by linarith : (0:ℝ) ≤ -(f1 - f0))]
      · push_neg at hs
        nlinarith [a1.2, a0.1, mul_nonneg (by linarith : (0:ℝ) ≤ -695447 / 4000000 - x) hs.le]
    · have k := c3 h'
      have : (f2 - f1) / (-695447 / 4000000 - -697447 / 4000000) * (x - -695447 / 4000000) =
          2000 * (f2 - f1) * (x - -695447 / 4000000) := by ring
      rw [this] at k
      by_cases hs : f2 - f1 ≤ 0
      · nlinarith [a2.2, mul_nonneg (by linarith : (0:ℝ) ≤ x - -695447 / 4000000) (by linarith : (0:ℝ) ≤ -(f2 - f1))]
      · push_neg at hs
        nlinarith [a2.2, a1.1, mul_nonneg (by linarith : (0:ℝ) ≤ 1 - x) hs.le]

theorem norm_real_sub (x t : ℝ) : ‖(x : ℂ) - (t : ℂ)‖ = |x - t| := by
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]

theorem ivlL_real_eq (x : ℝ) :
    ivlL ivlLo ivlHi (x : ℂ) = (1 / 2) * ∑ n ∈ range 106,
      (Real.arcosh ((|x - loN n| + |x - hiN n|) / (hiN n - loN n)) + Real.log ((hiN n - loN n) / 4)) := by
  have h1 : ∀ c : Fin 53 × Fin 2, ivlGreen (ivlLo c) (ivlHi c) (x : ℂ) + Real.log ((ivlHi c - ivlLo c) / 4) =
      (Real.arcosh ((|x - loN (finProdFinEquiv c : ℕ)| + |x - hiN (finProdFinEquiv c : ℕ)|) /
        (hiN (finProdFinEquiv c : ℕ) - loN (finProdFinEquiv c : ℕ))) +
        Real.log ((hiN (finProdFinEquiv c : ℕ) - loN (finProdFinEquiv c : ℕ)) / 4)) := by
    intro c
    have hlt := ivlLo_lt c
    rw [ivlGreen_eq hlt, norm_real_sub, norm_real_sub]
    unfold ivlLo ivlHi loF hiF loN hiN
    rfl
  have h2 : ∑ c : Fin 53 × Fin 2, (ivlGreen (ivlLo c) (ivlHi c) (x : ℂ) + Real.log ((ivlHi c - ivlLo c) / 4)) =
      ∑ n ∈ range 106, (Real.arcosh ((|x - loN n| + |x - hiN n|) / (hiN n - loN n)) +
        Real.log ((hiN n - loN n) / 4)) := by
    rw [Finset.sum_congr rfl (fun c _ => h1 c)]
    rw [Fintype.sum_equiv finProdFinEquiv _ (fun i : Fin (53 * 2) =>
      (Real.arcosh ((|x - loN (i : ℕ)| + |x - hiN (i : ℕ)|) / (hiN (i : ℕ) - loN (i : ℕ))) +
        Real.log ((hiN (i : ℕ) - loN (i : ℕ)) / 4))) (fun c => rfl)]
    exact Fin.sum_univ_eq_sum_range (fun n => (Real.arcosh ((|x - loN n| + |x - hiN n|) / (hiN n - loN n)) +
        Real.log ((hiN n - loN n) / 4))) (53 * 2)
  unfold ivlL
  rw [h2]

theorem term_le {lo hi x X : ℝ} (hlt : lo < hi) (hX : |2 * x - lo - hi| ≤ X) :
    Real.arcosh ((|x - lo| + |x - hi|) / (hi - lo)) + Real.log ((hi - lo) / 4) ≤
      Real.log (max (hi - lo) X / 2) := by
  have hh : 0 < hi - lo := sub_pos.mpr hlt
  set H := (|x - lo| + |x - hi|) / (hi - lo) with hHdef
  have hsum : |x - lo| + |x - hi| ≤ max (hi - lo) X := by
    have key : |x - lo| + |x - hi| ≤ max (hi - lo) |2 * x - lo - hi| := by
      rcases le_total x lo with h1 | h1
      · rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
        exact le_max_of_le_right (by linarith)
      · rcases le_total x hi with h2 | h2
        · rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]
          exact le_max_of_le_left (by linarith)
        · rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
          exact le_max_of_le_right (by linarith)
    exact key.trans (max_le_max le_rfl hX)
  have hH1 : 1 ≤ H := by
    rw [hHdef, le_div_iff₀ hh]
    have := abs_sub_abs_le_abs_sub (hi - x) (lo - x)
    have e : |x - lo| + |x - hi| = |lo - x| + |hi - x| := by rw [abs_sub_comm x lo, abs_sub_comm x hi]
    rw [e]
    have := abs_add_le (hi - x) (x - lo)
    rw [show hi - x + (x - lo) = hi - lo by ring, abs_of_pos hh] at this
    rw [abs_sub_comm lo x, abs_sub_comm hi x] at *
    linarith [abs_sub_comm hi x]
  have hexp : Real.exp (Real.arcosh H) = H + √(H ^ 2 - 1) := Real.exp_arcosh hH1
  have hsq : √(H ^ 2 - 1) ≤ H := by
    rw [Real.sqrt_le_left (by linarith)]; nlinarith
  have h4 : 0 < (hi - lo) / 4 := by linarith
  have hHh : H * (hi - lo) = |x - lo| + |x - hi| := by rw [hHdef]; field_simp
  have hmaxpos : 0 < max (hi - lo) X := lt_of_lt_of_le hh (le_max_left _ _)
  have hlog : Real.arcosh H = Real.log (Real.exp (Real.arcosh H)) := (Real.log_exp _).symm
  rw [hlog, ← Real.log_mul (Real.exp_pos _).ne' h4.ne']
  apply Real.log_le_log (mul_pos (Real.exp_pos _) h4)
  rw [hexp]
  nlinarith [hHh, hsum, hsq]

def segX (right : Bool) (n : ℕ) : ℚ :=
  if right then max |3 / 2 - (loQ n + hiQ n)| |2 - (loQ n + hiQ n)|
  else max |2 + (loQ n + hiQ n)| |3 / 2 + (loQ n + hiQ n)|

def segY (right : Bool) (n : ℕ) : ℚ := max (hiQ n - loQ n) (segX right n) / 2

def segP (right : Bool) : ℕ → ℚ
  | 0 => 1
  | n + 1 => segP right n * segY right n

def segC (right : Bool) : ℚ := if right then 1 / 4 else 2

def segR (right : Bool) : ℚ := segC right ^ 12 * segP right 106 * (4 / 3) ^ 20

def segChk (right : Bool) : Bool :=
  match logQ 12 (segR right) with
  | some (v, e) => decide (v + e ≤ 2 * (32506 / 10000))
  | none => false

theorem segChk_right : segChk true = true := by decide +kernel -- kcost: 1.0 s measured: 106 exact rational products and one logQ
theorem segChk_left : segChk false = true := by decide +kernel -- kcost: 1.0 s measured: 106 exact rational products and one logQ

theorem segP_cast (right : Bool) (n : ℕ) :
    ((segP right n : ℚ) : ℝ) = ∏ k ∈ range n, ((segY right k : ℚ) : ℝ) := by
  induction n with
  | zero => simp [segP]
  | succ n ih => rw [Finset.prod_range_succ, ← ih]; simp [segP]

theorem segY_pos {n : ℕ} (hn : n < 106) (right : Bool) : (0 : ℝ) < ((segY right n : ℚ) : ℝ) := by
  have hlt := loN_lt hn
  unfold segY
  push_cast
  rw [loQ_cast, hiQ_cast]
  have : (0 : ℝ) < max (hiN n - loN n) ((segX right n : ℚ) : ℝ) :=
    lt_of_lt_of_le (by linarith) (le_max_left _ _)
  linarith

theorem ivlL_seg_le (right : Bool) (x : ℝ)
    (hX : ∀ n < 106, |2 * x - loN n - hiN n| ≤ ((segX right n : ℚ) : ℝ)) :
    ivlL ivlLo ivlHi (x : ℂ) ≤ (1 / 2) * Real.log ((segP right 106 : ℚ) : ℝ) := by
  rw [ivlL_real_eq, segP_cast, Real.log_prod (fun n hn => (segY_pos (Finset.mem_range.mp hn) right).ne')]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Finset.sum_le_sum
  intro n hn
  have hn' := Finset.mem_range.mp hn
  have := term_le (loN_lt hn') (hX n hn')
  refine this.trans (le_of_eq ?_)
  unfold segY
  push_cast
  rw [loQ_cast, hiQ_cast]

theorem seg_core (right : Bool) (hchk : segChk right = true) (x : ℝ)
    (hx0 : 0 < |1 - x|) (hx1 : |1 - x| ≤ ((segC right : ℚ) : ℝ))
    (hX : ∀ n < 106, |2 * x - loN n - hiN n| ≤ ((segX right n : ℚ) : ℝ)) :
    6 * Real.log |1 - x| + ivlL ivlLo ivlHi (x : ℂ) + 10 * Real.log (4 / 3) ≤ 32506 / 10000 := by
  have hl := ivlL_seg_le right x hX
  have hP : (0 : ℝ) < ((segP right 106 : ℚ) : ℝ) := by
    rw [segP_cast]
    exact Finset.prod_pos fun n hn => segY_pos (Finset.mem_range.mp hn) right
  have hc0 : (0 : ℝ) < ((segC right : ℚ) : ℝ) := by
    cases right <;> norm_num [segC]
  have hlog1 : Real.log |1 - x| ≤ Real.log ((segC right : ℚ) : ℝ) := Real.log_le_log hx0 hx1
  have hRcast : ((segR right : ℚ) : ℝ) = ((segC right : ℚ) : ℝ) ^ 12 * ((segP right 106 : ℚ) : ℝ) * (4 / 3) ^ 20 := by
    unfold segR; push_cast; ring
  have hlogR : Real.log ((segR right : ℚ) : ℝ) =
      12 * Real.log ((segC right : ℚ) : ℝ) + Real.log ((segP right 106 : ℚ) : ℝ) + 20 * Real.log (4 / 3) := by
    rw [hRcast, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) hP.ne',
      Real.log_pow, Real.log_pow]
    push_cast; ring
  unfold segChk at hchk
  split at hchk
  · rename_i v e hv
    simp only [decide_eq_true_eq] at hchk
    obtain ⟨_, henc⟩ := logQ_spec hv
    unfold Enc at henc
    have hb := (abs_le.mp henc).2
    rw [hlogR] at hb
    have hq : ((v + e : ℚ) : ℝ) ≤ 2 * (32506 / 10000) := by
      have : ((v + e : ℚ) : ℝ) ≤ ((2 * (32506 / 10000) : ℚ) : ℝ) := by exact_mod_cast hchk
      simpa using this
    push_cast at hq
    simp only at hb
    linarith
  · simp at hchk

theorem hseg_d : ∀ x : ℝ, 3 / 4 ≤ |x| → |x| < 1 →
    ((CatalanMeasure.GenD.Signed.dc58.toParameters.h0 + CatalanMeasure.GenD.Signed.dc58.toParameters.q0 : ℕ) : ℝ) *
        Real.log ‖(1 : ℂ) - (x : ℂ)‖ + ivlL ivlLo ivlHi (x : ℂ) -
      2 * (CatalanMeasure.GenD.Signed.dc58.toParameters.g0 : ℝ) * Real.log (3 / 4) ≤ 32506 / 10000 := by
  intro x h1 h2
  have h6 : ((CatalanMeasure.GenD.Signed.dc58.toParameters.h0 +
      CatalanMeasure.GenD.Signed.dc58.toParameters.q0 : ℕ) : ℝ) = 6 := by
    norm_num [CatalanMeasure.GenD.Signed.dc58_h0, CatalanMeasure.GenD.Signed.dc58_q0]
  have hg : ((CatalanMeasure.GenD.Signed.dc58.toParameters.g0 : ℕ) : ℝ) = 5 := by
    norm_num [CatalanMeasure.GenD.Signed.dc58_g0]
  have hn1 : ‖(1 : ℂ) - (x : ℂ)‖ = |1 - x| := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have hl34 : Real.log (3 / 4) = -Real.log (4 / 3) := by
    rw [show (3 / 4 : ℝ) = (4 / 3)⁻¹ by norm_num, Real.log_inv]
  rw [h6, hg, hn1, hl34]
  have hxlt := abs_lt.mp h2
  rcases le_or_gt 0 x with hx | hx
  · rw [abs_of_nonneg hx] at h1
    have hpos : 0 < |1 - x| := by rw [abs_of_pos (by linarith)]; linarith
    have hle : |1 - x| ≤ ((segC true : ℚ) : ℝ) := by
      rw [abs_of_pos (by linarith)]; norm_num [segC]; linarith
    have hX : ∀ n < 106, |2 * x - loN n - hiN n| ≤ ((segX true n : ℚ) : ℝ) := by
      intro n _
      unfold segX
      simp only [ite_true]
      push_cast
      rw [loQ_cast, hiQ_cast]
      have := abs_le_max_abs_abs (a := 3 / 2 - (loN n + hiN n)) (b := 2 * x - loN n - hiN n)
        (c := 2 - (loN n + hiN n)) (by linarith) (by linarith)
      exact this
    have := seg_core true segChk_right x hpos hle hX
    linarith
  · rw [abs_of_neg hx] at h1
    have hpos : 0 < |1 - x| := by rw [abs_of_pos (by linarith)]; linarith
    have hle : |1 - x| ≤ ((segC false : ℚ) : ℝ) := by
      rw [abs_of_pos (by linarith)]; norm_num [segC]; linarith
    have hX : ∀ n < 106, |2 * x - loN n - hiN n| ≤ ((segX false n : ℚ) : ℝ) := by
      intro n _
      unfold segX
      simp only [Bool.false_eq_true, ite_false]
      push_cast
      rw [loQ_cast, hiQ_cast]
      have := abs_le_max_abs_abs (a := -2 - (loN n + hiN n)) (b := 2 * x - loN n - hiN n)
        (c := -3 / 2 - (loN n + hiN n)) (by linarith) (by linarith)
      have e1 : |(-2 : ℝ) - (loN n + hiN n)| = |2 + (loN n + hiN n)| := by
        rw [← abs_neg]; ring_nf
      have e2 : |(-3 / 2 : ℝ) - (loN n + hiN n)| = |3 / 2 + (loN n + hiN n)| := by
        rw [← abs_neg]; ring_nf
      rwa [e1, e2] at this
    have := seg_core false segChk_left x hpos hle hX
    linarith

/-- **(hcirc)** on `|z| = 3/4` at `D = 3.2506` for `ivlL` of the 106 intervals of design C. -/
theorem hcirc_d : ∀ z : ℂ, ‖z‖ = 3 / 4 →
    ((CatalanMeasure.GenD.Signed.dc58.toParameters.h0 + CatalanMeasure.GenD.Signed.dc58.toParameters.q0 : ℕ) : ℝ) *
        Real.log ‖(1 : ℂ) - z‖ + ivlL ivlLo ivlHi z ≤ 32506 / 10000 := by
  intro z hz
  have hs := abs_re_le_of_norm hz
  have h6 : ((CatalanMeasure.GenD.Signed.dc58.toParameters.h0 +
      CatalanMeasure.GenD.Signed.dc58.toParameters.q0 : ℕ) : ℝ) = 6 := by
    norm_num [CatalanMeasure.GenD.Signed.dc58_h0, CatalanMeasure.GenD.Signed.dc58_q0]
  have hn : ‖(1 : ℂ) - z‖ = √(qq 1 (4 * z.re / 3)) := by
    rw [norm_sub_rev]
    have := norm_sub_real hz 1
    simpa using this
  have hq : 0 ≤ qq 1 (4 * z.re / 3) := qq_nonneg 1 hs
  rw [h6, hn, Real.log_sqrt hq, ivlL_eq hz]
  have := FF_le (4 * z.re / 3) ⟨(abs_le.mp hs).1, (abs_le.mp hs).2⟩
  unfold FF at this
  linarith

end

end CatalanMeasure.GenD.Signed.RouteI.HCirc
