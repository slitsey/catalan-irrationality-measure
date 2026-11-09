module

public import CatalanCore.Uniform.Decay.Jet.PoleContour
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.PSeries

@[expose] public section
set_option Elab.async false
open Finset MeasureTheory Set Filter Complex
namespace CatalanCore.Uniform.Decay.Jet

/-! Exact natural-tail telescoping at every pole order.  The harmonic case is
handled as a convergent difference throughout: no divergent tsums are split. -/

theorem hasSum_shift_difference (f : ℕ → ℝ) (hf : Antitone f)
    (hf0 : ∀ n, 0 ≤ f n) (hlim : Tendsto f atTop (nhds 0)) (c : ℕ) :
    HasSum (fun m : ℕ => f m - f (m + c)) (∑ j ∈ Finset.range c, f j) := by
  have hs : Summable (fun m : ℕ => f m - f (m + c)) := by
    apply summable_of_sum_range_le (c := ∑ j ∈ Finset.range c, f j)
    · intro m
      exact sub_nonneg.mpr (hf (Nat.le_add_right m c))
    · intro M
      rw [CatalanCore.Frame.telescope]
      exact sub_le_self _ (Finset.sum_nonneg fun j _ => hf0 _)
  have ht : Tendsto (fun M : ℕ => ∑ m ∈ Finset.range M, (f m - f (m + c)))
      atTop (nhds (∑ j ∈ Finset.range c, f j)) := by
    have he : (fun M : ℕ => ∑ m ∈ Finset.range M, (f m - f (m + c))) =
        fun M => (∑ j ∈ Finset.range c, f j) - ∑ j ∈ Finset.range c, f (M + j) := by
      funext M
      exact CatalanCore.Frame.telescope f c M
    rw [he]
    have ht0 : Tendsto (fun M : ℕ => ∑ j ∈ Finset.range c, f (M + j)) atTop (nhds 0) := by
      convert tendsto_finsetSum (Finset.range c)
        (fun j _ => hlim.comp (tendsto_add_atTop_nat j)) using 1 <;> simp
    simpa using tendsto_const_nhds.sub ht0
  have he := tendsto_nhds_unique hs.hasSum.tendsto_sum_nat ht
  rw [← he]
  exact hs.hasSum

noncomputable def polePower (j : ℕ) (s : ℝ) (n : ℕ) : ℝ :=
  1 / ((n : ℝ) + s) ^ j

theorem polePower_nonneg (j : ℕ) {s : ℝ} (hs : 0 < s) (n : ℕ) :
    0 ≤ polePower j s n := by
  dsimp [polePower]
  positivity

theorem polePower_antitone (j : ℕ) {s : ℝ} (hs : 0 < s) :
    Antitone (polePower j s) := by
  intro m n hmn
  dsimp [polePower]
  apply one_div_le_one_div_of_le (by positivity)
  exact pow_le_pow_left₀ (by positivity) (show (m : ℝ) + s ≤ (n : ℝ) + s by gcongr) _

theorem tendsto_polePower (j : ℕ) (hj : 0 < j) (s : ℝ) :
    Tendsto (polePower j s) atTop (nhds 0) := by
  have ht : Tendsto (fun n : ℕ => (n : ℝ) + s) atTop atTop :=
    tendsto_atTop_add_const_right _ s tendsto_natCast_atTop_atTop
  have hp := (tendsto_pow_atTop (by omega : j ≠ 0)).comp ht
  exact tendsto_const_nhds.div_atTop hp

theorem hasSum_polePower_difference (j : ℕ) (hj : 0 < j) {s : ℝ} (hs : 0 < s)
    (a c : ℕ) :
    HasSum (fun m : ℕ => polePower j s (a + m) - polePower j s (a + m + c))
      (∑ i ∈ Finset.range c, polePower j s (a + i)) := by
  have hm : Antitone (fun n => polePower j s (a + n)) :=
    (polePower_antitone j hs).comp_monotone (fun _ _ h => Nat.add_le_add_left h a)
  have ht : Tendsto (fun n => polePower j s (a + n)) atTop (nhds 0) := by
    exact (tendsto_polePower j hj s).comp (by simpa only [Nat.add_comm] using tendsto_add_atTop_nat a)
  simpa only [Nat.add_assoc] using hasSum_shift_difference
    (fun n => polePower j s (a + n)) hm (fun _ => polePower_nonneg j hs _) ht c

theorem summable_polePower (j : ℕ) (hj : 2 ≤ j) {s : ℝ} (hs : 0 < s) :
    Summable (polePower j s) := by
  have hjr : (2 : ℝ) ≤ j := by exact_mod_cast hj
  have h := (Real.summable_one_div_nat_add_rpow s (j : ℝ)).mpr (by linarith)
  apply h.congr
  intro n
  simp only [polePower, Real.rpow_natCast, abs_of_pos (show (0 : ℝ) < (n : ℝ) + s by positivity)]

noncomputable def poleAtom (j : ℕ) (s : ℝ) (x y n : ℕ) : ℝ :=
  if x = y then (j : ℝ) * polePower (j + 1) s (n + x)
  else (polePower j s (n + x) - polePower j s (n + y)) / ((y : ℝ) - x)

theorem poleAtom_comm (j : ℕ) (s : ℝ) (x y n : ℕ) :
    poleAtom j s x y n = poleAtom j s y x n := by
  by_cases h : x = y
  · subst y; rfl
  · simp only [poleAtom, if_neg h, if_neg (Ne.symm h)]
    rw [show ((x : ℝ) - y) = -((y : ℝ) - x) by ring,
      show polePower j s (n + y) - polePower j s (n + x) =
        -(polePower j s (n + x) - polePower j s (n + y)) by ring]
    exact (neg_div_neg_eq _ _).symm

theorem hasSum_poleAtom_lt (j : ℕ) (hj : 0 < j) {s : ℝ} (hs : 0 < s)
    (x y : ℕ) (hxy : x < y) :
    HasSum (poleAtom j s x y)
      ((∑ t ∈ Finset.Ico x y, polePower j s t) / ((y : ℝ) - x)) := by
  obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le hxy.le
  have hh := (hasSum_polePower_difference j hj hs x c).div_const ((y : ℝ) - x)
  have he : (∑ i ∈ Finset.range c, polePower j s (x + i)) =
      ∑ t ∈ Finset.Ico x y, polePower j s t := by
    rw [hc, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
  rw [he] at hh
  have hc0 : c ≠ 0 := by omega
  apply hh.congr_fun
  intro n
  simp [poleAtom, hxy.ne, hc, hc0, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

theorem summable_poleAtom (j : ℕ) (hj : 0 < j) {s : ℝ} (hs : 0 < s) (x y : ℕ) :
    Summable (poleAtom j s x y) := by
  rcases lt_trichotomy x y with h | h | h
  · exact (hasSum_poleAtom_lt j hj hs x y h).summable
  · subst y
    have ht := ((summable_nat_add_iff x).mpr (summable_polePower (j + 1) (by omega) hs)).mul_left (j : ℝ)
    apply ht.congr
    intro n
    simp [poleAtom]
  · exact ((hasSum_poleAtom_lt j hj hs y x h).summable).congr fun n =>
      poleAtom_comm j s y x n

theorem tsum_poleAtom_diag (j : ℕ) (hj : 0 < j) {s : ℝ} (hs : 0 < s) (x : ℕ) :
    (∑' n : ℕ, poleAtom j s x x n) =
      (j : ℝ) * ((∑' n : ℕ, polePower (j + 1) s n) -
        ∑ n ∈ Finset.range x, polePower (j + 1) s n) := by
  have ht := (summable_polePower (j + 1) (by omega) hs).sum_add_tsum_nat_add x
  rw [show poleAtom j s x x = (fun n : ℕ => (j : ℝ) * polePower (j + 1) s (n + x)) by
    funext n; simp [poleAtom]]
  rw [tsum_mul_left]
  congr 1
  linarith

noncomputable def poleGeom {K : Type*} [Field K] (j : ℕ) (A B : K) : K :=
  ∑ i ∈ Finset.range j, (A⁻¹) ^ (i + 1) * (B⁻¹) ^ (j - i)

theorem poleGeom_factor {K : Type*} [Field K] (j : ℕ) (A B : K) :
    poleGeom j A B = A⁻¹ * B⁻¹ *
      ∑ i ∈ Finset.range j, (A⁻¹) ^ i * (B⁻¹) ^ (j - 1 - i) := by
  rw [poleGeom, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have he : j - i = (j - 1 - i) + 1 := by have := Finset.mem_range.mp hi; omega
  rw [he, pow_succ, pow_succ]
  ring

theorem poleGeom_difference {K : Type*} [Field K] (j : ℕ) {A B : K}
    (ha : A ≠ 0) (hb : B ≠ 0) :
    (B - A) * poleGeom j A B = (A⁻¹) ^ j - (B⁻¹) ^ j := by
  have he : (B - A) * A⁻¹ * B⁻¹ = A⁻¹ - B⁻¹ := by field_simp
  rw [poleGeom_factor]
  calc
    _ = (∑ i ∈ Finset.range j, (A⁻¹) ^ i * (B⁻¹) ^ (j - 1 - i)) *
        ((B - A) * A⁻¹ * B⁻¹) := by ring
    _ = _ := by rw [he]; exact geom_sum₂_mul A⁻¹ B⁻¹ j

theorem poleGeom_self {K : Type*} [Field K] (j : ℕ) (A : K) :
    poleGeom j A A = (j : K) * (A⁻¹) ^ (j + 1) := by
  unfold poleGeom
  calc
    _ = ∑ _i ∈ Finset.range j, (A⁻¹) ^ (j + 1) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [← pow_add]
      congr 1
      have := Finset.mem_range.mp hi
      omega
    _ = _ := by simp

theorem poleAtom_eq_geom (j : ℕ) {s : ℝ} (hs : 0 < s) (x y n : ℕ) :
    poleAtom j s x y n = poleGeom j ((n : ℝ) + s + x) ((n : ℝ) + s + y) := by
  have ha : (n : ℝ) + s + x ≠ 0 := by positivity
  have hb : (n : ℝ) + s + y ≠ 0 := by positivity
  by_cases hxy : x = y
  · subst y
    simp [poleAtom, poleGeom_self, polePower, Nat.cast_add, one_div, inv_pow, add_comm, add_left_comm, add_assoc]
  · simp only [poleAtom, if_neg hxy, polePower, Nat.cast_add, one_div, inv_pow]
    have hne : (y : ℝ) - x ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast (Ne.symm hxy))
    apply (div_eq_iff hne).mpr
    have he := poleGeom_difference j ha hb
    rw [show ((n : ℝ) + s + y) - ((n : ℝ) + s + x) = (y : ℝ) - x by ring] at he
    convert he.symm using 1 <;> ring


/-! Real restrictions and normalized Cauchy-kernel derivatives at every order. -/

theorem iteratedDeriv_restrict_real {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f U) (n : ℕ) {p : ℝ} (hp : (p : ℂ) ∈ U) :
    iteratedDeriv n (fun q : ℝ => f q) p = iteratedDeriv n f (p : ℂ) := by
  have hdiff : ∀ j : ℕ, DifferentiableOn ℂ (iteratedDeriv j f) U := by
    intro j
    induction j with
    | zero => simpa only [iteratedDeriv_zero] using hf
    | succ j ih => rw [iteratedDeriv_succ]; exact ih.deriv hU
  induction n generalizing p with
  | zero => rfl
  | succ n ih =>
      have hev : iteratedDeriv n (fun q : ℝ => f q) =ᶠ[nhds p]
          fun q : ℝ => iteratedDeriv n f (q : ℂ) := by
        filter_upwards [(Complex.continuous_ofReal.tendsto p).eventually (hU.mem_nhds hp)] with q hq
        exact ih hq
      rw [iteratedDeriv_succ, iteratedDeriv_succ]
      exact hev.deriv_eq.trans (((hdiff n).differentiableAt (hU.mem_nhds hp)).hasDerivAt.comp_ofReal.deriv)

theorem iteratedDeriv_inv_sub (n : ℕ) (a : ℂ) {z : ℂ} (hz : z ≠ a) :
    iteratedDeriv n (fun w : ℂ => (w - a)⁻¹) z =
      (-1 : ℂ) ^ n * (n.factorial : ℂ) * ((z - a)⁻¹) ^ (n + 1) := by
  induction n generalizing z with
  | zero => simp
  | succ n ih =>
      have hev : iteratedDeriv n (fun w : ℂ => (w - a)⁻¹) =ᶠ[nhds z]
          fun w : ℂ => (-1 : ℂ) ^ n * (n.factorial : ℂ) * ((w - a)⁻¹) ^ (n + 1) := by
        filter_upwards [isOpen_ne.mem_nhds hz] with w hw
        exact ih hw
      have hd := (((hasDerivAt_id z).sub_const a).inv (sub_ne_zero.mpr hz)).pow (n + 1)
      have hd' := hd.const_mul ((-1 : ℂ) ^ n * (n.factorial : ℂ))
      rw [iteratedDeriv_succ, hev.deriv_eq]
      have hdv := hd'.deriv
      simp only [id_eq, Pi.pow_apply, Pi.inv_apply] at hdv
      rw [hdv]
      rw [neg_div, one_div, ← inv_pow (z - a) 2]
      simp only [Nat.factorial_succ, Nat.cast_mul, Nat.add_sub_cancel, pow_succ]
      ring

theorem iteratedDeriv_cauchy_kernel (n : ℕ) (a b : ℂ) {z : ℂ}
    (ha : z ≠ a) (hb : z ≠ b) :
    iteratedDeriv n (fun w : ℂ => (w - a)⁻¹ * (w - b)⁻¹) z =
      ((-1 : ℂ) ^ n * (n.factorial : ℂ)) *
        ∑ j ∈ Finset.range (n + 1), ((z - a)⁻¹) ^ (j + 1) *
          ((z - b)⁻¹) ^ (n - j + 1) := by
  have hca : ContDiffAt ℂ n (fun w : ℂ => (w - a)⁻¹) z :=
    (contDiffAt_id.sub contDiffAt_const).inv (sub_ne_zero.mpr ha)
  have hcb : ContDiffAt ℂ n (fun w : ℂ => (w - b)⁻¹) z :=
    (contDiffAt_id.sub contDiffAt_const).inv (sub_ne_zero.mpr hb)
  rw [iteratedDeriv_fun_mul hca hcb, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjn : j ≤ n := by exact Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  rw [iteratedDeriv_inv_sub j a ha, iteratedDeriv_inv_sub (n - j) b hb]
  have hc : (n.choose j : ℂ) * (j.factorial : ℂ) * ((n - j).factorial : ℂ) = n.factorial := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hjn
  have hp : (-1 : ℂ) ^ j * (-1 : ℂ) ^ (n - j) = (-1 : ℂ) ^ n := by
    rw [← pow_add, Nat.add_sub_of_le hjn]
  calc
    _ = ((n.choose j : ℂ) * (j.factorial : ℂ) * ((n - j).factorial : ℂ)) *
        ((-1 : ℂ) ^ j * (-1 : ℂ) ^ (n - j)) *
        (((z - a)⁻¹) ^ (j + 1) * ((z - b)⁻¹) ^ (n - j + 1)) := by ring
    _ = _ := by rw [hc, hp]; ring

theorem poleKernel_iteratedDeriv (n : ℕ) (a b : ℝ) {p : ℝ}
    (ha : p ≠ a) (hb : p ≠ b) :
    iteratedDeriv n (poleKernel a b) p =
      iteratedDeriv n (fun z : ℂ => (z - (a : ℂ))⁻¹ * (z - (b : ℂ))⁻¹) (p : ℂ) := by
  let U : Set ℂ := {z | z ≠ (a : ℂ) ∧ z ≠ (b : ℂ)}
  have hU : IsOpen U := isOpen_ne.inter isOpen_ne
  have hdiff : DifferentiableOn ℂ (fun z : ℂ => (z - (a : ℂ))⁻¹ * (z - (b : ℂ))⁻¹) U := by
    intro z hz
    have ha' : DifferentiableAt ℂ (fun z : ℂ => (z - (a : ℂ))⁻¹) z :=
      ((hasDerivAt_id z).sub_const (a : ℂ)).inv (sub_ne_zero.mpr hz.1) |>.differentiableAt
    have hb' : DifferentiableAt ℂ (fun z : ℂ => (z - (b : ℂ))⁻¹) z :=
      ((hasDerivAt_id z).sub_const (b : ℂ)).inv (sub_ne_zero.mpr hz.2) |>.differentiableAt
    exact (ha'.mul hb').differentiableWithinAt
  have he : poleKernel a b = fun p : ℝ => ((p : ℂ) - (a : ℂ))⁻¹ * ((p : ℂ) - (b : ℂ))⁻¹ := by
    funext p
    simp only [poleKernel, one_div, mul_inv_rev]
    ring
  rw [he]
  exact iteratedDeriv_restrict_real hU hdiff n ⟨by exact_mod_cast ha, by exact_mod_cast hb⟩

set_option maxRecDepth 2000 in
theorem normalized_kernel_atom (n : ℕ) {s : ℝ} (hs : 0 < s) (x y m : ℕ) :
    ((n.factorial : ℂ)⁻¹) *
      iteratedDeriv n (fun z : ℂ => (z - (x : ℂ))⁻¹ * (z - (y : ℂ))⁻¹)
        (-(m : ℂ) - (s : ℂ)) = (poleAtom (n + 1) s x y m : ℂ) := by
  have hx : -(m : ℂ) - (s : ℂ) ≠ (x : ℂ) := by
    intro h
    have he := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.neg_re, Complex.natCast_re, Complex.ofReal_re] at he
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
    have hx : (0 : ℝ) ≤ x := Nat.cast_nonneg _
    linarith
  have hy : -(m : ℂ) - (s : ℂ) ≠ (y : ℂ) := by
    intro h
    have he := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.neg_re, Complex.natCast_re, Complex.ofReal_re] at he
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
    have hy : (0 : ℝ) ≤ y := Nat.cast_nonneg _
    linarith
  rw [iteratedDeriv_cauchy_kernel n _ _ hx hy, poleAtom_eq_geom (n + 1) hs x y m]
  have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have he : (n.factorial : ℂ)⁻¹ * ((-1 : ℂ) ^ n * (n.factorial : ℂ)) = (-1 : ℂ) ^ n := by
    field_simp
  rw [← mul_assoc, he, Finset.mul_sum]
  simp only [poleGeom, Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_pow,
    Complex.ofReal_inv, Complex.ofReal_add, Complex.ofReal_natCast]
  apply Finset.sum_congr rfl
  intro j hj
  have hjn : j ≤ n := by have := Finset.mem_range.mp hj; omega
  have hpx : (-(m : ℂ) - (s : ℂ) - (x : ℂ))⁻¹ = -((m : ℂ) + (s : ℂ) + (x : ℂ))⁻¹ := by
    rw [← inv_neg]
    congr 1
    ring
  have hpy : (-(m : ℂ) - (s : ℂ) - (y : ℂ))⁻¹ = -((m : ℂ) + (s : ℂ) + (y : ℂ))⁻¹ := by
    rw [← inv_neg]
    congr 1
    ring
  rw [hpx, hpy]
  rw [neg_pow (((m : ℂ) + (s : ℂ) + (x : ℂ))⁻¹) (j + 1),
    neg_pow (((m : ℂ) + (s : ℂ) + (y : ℂ))⁻¹) (n - j + 1)]
  have hsign : (-1 : ℂ) ^ n * (-1 : ℂ) ^ (j + 1) * (-1 : ℂ) ^ (n - j + 1) = 1 := by
    rw [← pow_add, ← pow_add, show n + (j + 1) + (n - j + 1) = 2 * (n + 1) by omega,
      pow_mul]
    norm_num
  rw [show n + 1 - j = n - j + 1 by omega]
  calc
    _ = ((-1 : ℂ) ^ n * (-1 : ℂ) ^ (j + 1) * (-1 : ℂ) ^ (n - j + 1)) *
      (((m : ℂ) + (s : ℂ) + (x : ℂ))⁻¹ ^ (j + 1) *
        ((m : ℂ) + (s : ℂ) + (y : ℂ))⁻¹ ^ (n - j + 1)) := by ring
    _ = _ := by rw [hsign, one_mul]


#print axioms hasSum_shift_difference
#print axioms hasSum_poleAtom_lt
#print axioms summable_poleAtom
#print axioms tsum_poleAtom_diag
#print axioms poleAtom_eq_geom
#print axioms iteratedDeriv_restrict_real
#print axioms iteratedDeriv_inv_sub
#print axioms iteratedDeriv_cauchy_kernel
#print axioms poleKernel_iteratedDeriv
#print axioms normalized_kernel_atom

end CatalanCore.Uniform.Decay.Jet
