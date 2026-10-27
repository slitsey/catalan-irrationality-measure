module

public import CatalanCore.Measure.Sep
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

@[expose] public section

/-!# Characteristic-zero selection and the measure theorem at an independent scale

`PolyFamily.deg` bounds the denominator exponent, whereas `scale` is the
asymptotic parameter. Keeping them separate retains degree gamma*r+O(1).
The provider hypotheses concern the same admissible members throughout.
-/
set_option maxHeartbeats 1200000
namespace CatalanCore.Uniform
open Real

/-- At every sufficiently large integer scale, a member avoids every rational input. -/
def HasNV0 (Fam : PolyFamily) (scale : Fam.ι → ℕ) : Prop :=
  ∃ R0 : ℕ, ∀ r : ℕ, R0 ≤ r → ∀ x : ℚ,
    ∃ n, Fam.Adm n ∧ scale n = r ∧ Fam.evalQ n x ≠ 0

/-- Coefficient clearing with growth measured at `scale`, not at the degree bound. -/
def HasScaledContent (Fam : PolyFamily) (scale : Fam.ι → ℕ) (Λ : ℝ) : Prop :=
  ∃ den : Fam.ι → ℕ, (∀ n, 0 < den n) ∧
    (∀ n, Fam.Adm n → ∀ p q : ℤ, 0 < q →
      ∃ z : ℤ, (q : ℚ) ^ Fam.deg n * den n * Fam.evalQ n (p / q) = z) ∧
    (∀ ε > 0, ∃ R0 : ℕ, ∀ n, Fam.Adm n → R0 ≤ scale n →
      Real.log (den n) ≤ (Λ + ε) * (scale n : ℝ) ^ 2)

/-- The paper's epsilon window contract, uniform over every admissible member. -/
def HasScaledDecay (Fam : PolyFamily) (scale : Fam.ι → ℕ) (D c : ℝ) : Prop :=
  ∀ ε > 0, ∃ R0 : ℕ, ∀ n, Fam.Adm n → R0 ≤ scale n → ∀ t : ℝ,
    |t| ≤ Real.exp (-(c + ε) * (scale n : ℝ)) →
      |Fam.evalR n (Fam.const + t)| ≤ Real.exp (-(D - ε) * (scale n : ℝ) ^ 2)

/-- Finite-place integrality plus the analytic window give the quadratic separation. -/
theorem scaled_sep (Fam : PolyFamily) (scale : Fam.ι → ℕ) {Λ D c θ ε : ℝ}
    (hΛ : HasScaledContent Fam scale Λ) (hD : HasScaledDecay Fam scale D c)
    (he : 0 < ε) (hbudget : θ + 2 * ε ≤ D - Λ) :
    ∃ R0 : ℕ, ∀ n, Fam.Adm n → R0 ≤ scale n → ∀ p q : ℤ, 0 < q →
      Fam.evalQ n (p / q) ≠ 0 →
      |Fam.const - (p : ℝ) / q| ≤ Real.exp (-(c + ε) * (scale n : ℝ)) →
      θ * (scale n : ℝ) ^ 2 ≤ (Fam.deg n : ℝ) * Real.log q := by
  obtain ⟨R2, h2⟩ := hD ε he
  obtain ⟨den, hdpos, hint, hlog⟩ := hΛ
  obtain ⟨R1, h1⟩ := hlog ε he
  refine ⟨max R1 R2, ?_⟩
  intro n hn hr p q hq hP hclose
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hdR : (0 : ℝ) < den n := by exact_mod_cast hdpos n
  have hup := h2 n hn (le_trans (le_max_right _ _) hr)
    ((p : ℝ) / q - Fam.const) (by simpa [abs_sub_comm] using hclose)
  have hcast : Fam.const + ((p : ℝ) / q - Fam.const) = ((p / q : ℚ) : ℝ) := by
    push_cast; ring
  rw [hcast, CatalanCore.Measure.evalR_cast] at hup
  obtain ⟨z, hz⟩ := hint n hn p q hq
  have hz0 : z ≠ 0 := by
    intro hz0
    have hprod : (q : ℚ) ^ Fam.deg n * den n ≠ 0 := by
      have : (0 : ℚ) < q := by exact_mod_cast hq
      have : (0 : ℚ) < den n := by exact_mod_cast hdpos n
      positivity
    rw [hz0] at hz
    exact hP ((mul_eq_zero.mp hz).resolve_left hprod)
  have hz1 : (1 : ℝ) ≤ |(z : ℝ)| := by exact_mod_cast Int.one_le_abs hz0
  have hzR : (q : ℝ) ^ Fam.deg n * den n * ((Fam.evalQ n (p / q) : ℚ) : ℝ) = z := by
    exact_mod_cast hz
  have hA : (0 : ℝ) < (q : ℝ) ^ Fam.deg n * den n := by positivity
  have hone : (1 : ℝ) ≤ (q : ℝ) ^ Fam.deg n * den n *
      Real.exp (-(D - ε) * (scale n : ℝ) ^ 2) := by
    calc
      1 ≤ |(z : ℝ)| := hz1
      _ = (q : ℝ) ^ Fam.deg n * den n * |((Fam.evalQ n (p / q) : ℚ) : ℝ)| := by
        rw [← hzR, abs_mul, abs_of_pos hA]
      _ ≤ _ := mul_le_mul_of_nonneg_left hup hA.le
  have hl := Real.log_le_log one_pos hone
  rw [Real.log_one, Real.log_mul hA.ne' (Real.exp_pos _).ne',
    Real.log_mul (by positivity) hdR.ne', Real.log_pow, Real.log_exp] at hl
  have hd := h1 n hn (le_trans (le_max_left _ _) hr)
  have hs := sq_nonneg (scale n : ℝ)
  nlinarith

/-- Full characteristic-zero GMT, including affine degree bounds gamma*r+K. -/
theorem measure_of_family_nv0 (Fam : PolyFamily) (scale : Fam.ι → ℕ)
    {Λ D c γ K : ℝ} (hΛ : HasScaledContent Fam scale Λ)
    (hD : HasScaledDecay Fam scale D c) (hη : Λ < D) (hc : 0 < c)
    (hγ : 0 < γ) (hK : 0 ≤ K)
    (hdeg : ∀ n, Fam.Adm n → (Fam.deg n : ℝ) ≤ γ * scale n + K)
    (hnv : HasNV0 Fam scale) : Fam.MeasureLB (γ * c / (D - Λ)) := by
  intro e he
  let ν := γ * c / (D - Λ) + e
  have hη0 : 0 < D - Λ := sub_pos.mpr hη
  have hν0 : 0 < ν := by dsimp [ν]; positivity
  have hgap : γ / (D - Λ) < ν / c := by
    dsimp [ν]
    apply (lt_div_iff₀ hc).mpr
    have heq : γ / (D - Λ) * c = γ * c / (D - Λ) := by ring
    rw [heq]; linarith
  obtain ⟨a, ha1, ha2⟩ := exists_between hgap
  have ha : 0 < a := lt_trans (by positivity) ha1
  have hηa : γ / a < D - Λ := by
    apply (div_lt_iff₀ ha).mpr
    have := (div_lt_iff₀ hη0).mp ha1
    nlinarith
  obtain ⟨θ, hθ1, hθ2⟩ := exists_between hηa
  have hθ0 : 0 < θ := lt_trans (by positivity) hθ1
  have hθa : γ < θ * a := by exact (div_lt_iff₀ ha).mp hθ1
  let ε := min ((D - Λ - θ) / 3) ((ν / a - c) / 2)
  have hca : c * a < ν := by
    have := (lt_div_iff₀ hc).mp ha2
    nlinarith
  have hε0 : 0 < ε := by
    apply lt_min
    · linarith
    · have : c < ν / a := (lt_div_iff₀ ha).mpr (by nlinarith)
      linarith
  have hbudget : θ + 2 * ε ≤ D - Λ := by
    have := min_le_left ((D - Λ - θ) / 3) ((ν / a - c) / 2)
    change ε ≤ (D - Λ - θ) / 3 at this
    linarith
  have hwindow : (c + ε) * a < ν := by
    have hle := min_le_right ((D - Λ - θ) / 3) ((ν / a - c) / 2)
    change ε ≤ (ν / a - c) / 2 at hle
    have hdiv : ν / a * a = ν := div_mul_cancel₀ _ ha.ne'
    nlinarith
  obtain ⟨Rsep, hsep⟩ := scaled_sep Fam scale hΛ hD hε0 hbudget
  obtain ⟨Rnv, hnv⟩ := hnv
  let R := max Rsep Rnv
  let B := max (((R : ℝ) + 1) / a)
    (max ((c + ε) / (ν - (c + ε) * a)) ((K + 1) / (a * (θ * a - γ))))
  refine ⟨⌈Real.exp (B + 1)⌉₊, ?_⟩
  intro p q hq _
  have hqe : Real.exp (B + 1) ≤ q :=
    (Nat.le_ceil _).trans (by exact_mod_cast hq)
  have hqpos : (0 : ℝ) < q := (Real.exp_pos _).trans_le hqe
  have hqN : 0 < q := by exact_mod_cast hqpos
  have hL : B + 1 ≤ Real.log q := (Real.le_log_iff_exp_le hqpos).mpr hqe
  let L := Real.log (q : ℝ)
  have hLB1 : ((R : ℝ) + 1) / a < L := by
    have hb : ((R : ℝ) + 1) / a ≤ B := le_max_left _ _
    dsimp [L]; linarith
  have hLB2 : (c + ε) / (ν - (c + ε) * a) < L := by
    have hb : (c + ε) / (ν - (c + ε) * a) ≤ B :=
      (le_max_left _ _).trans (le_max_right _ _)
    dsimp [L]; linarith
  have hLB3 : (K + 1) / (a * (θ * a - γ)) < L := by
    have hb : (K + 1) / (a * (θ * a - γ)) ≤ B :=
      (le_max_right _ _).trans (le_max_right _ _)
    dsimp [L]; linarith
  have hL0 : 0 < L := lt_trans (by positivity) hLB1
  let r := ⌈a * L⌉₊
  have hrlo : a * L ≤ (r : ℝ) := Nat.le_ceil _
  have hrhi : (r : ℝ) < a * L + 1 := Nat.ceil_lt_add_one (by positivity)
  have hrR : R ≤ r := by
    have := (div_lt_iff₀ ha).mp hLB1
    have : (R : ℝ) ≤ r := by nlinarith
    exact_mod_cast this
  obtain ⟨n, hn, hnr, hne⟩ := hnv r ((le_max_right _ _).trans hrR) (p / q)
  have hrpos : (0 : ℝ) < r := lt_of_lt_of_le (by positivity) hrlo
  by_contra hcon
  have hclose : |Fam.const - (p : ℝ) / q| ≤ (q : ℝ) ^ (-ν) := le_of_not_gt hcon
  have hwin : |Fam.const - (p : ℝ) / q| ≤ Real.exp (-(c + ε) * (scale n : ℝ)) := by
    apply hclose.trans
    rw [Real.rpow_def_of_pos hqpos, hnr]
    apply Real.exp_le_exp.mpr
    have h2 := (div_lt_iff₀ (sub_pos.mpr hwindow)).mp hLB2
    have hcp : 0 < c + ε := add_pos hc hε0
    have hr' := mul_lt_mul_of_pos_left hrhi hcp
    dsimp [L] at h2
    dsimp [L] at hr'
    nlinarith only [h2, hr']
  have hsep' := hsep n hn (by rw [hnr]; exact (le_max_left _ _).trans hrR)
    p (q : ℤ) (by exact_mod_cast hqN) (by simpa using hne) (by simpa using hwin)
  simp only [Int.cast_natCast, hnr] at hsep'
  have hdeg' := hdeg n hn
  rw [hnr] at hdeg'
  have hup : θ * (r : ℝ) ^ 2 ≤ (γ * (r : ℝ) + K) * L :=
    hsep'.trans (mul_le_mul_of_nonneg_right hdeg' hL0.le)
  have hbudget' : K + 1 < a * (θ * a - γ) * L :=
    by simpa [mul_comm] using (div_lt_iff₀ (mul_pos ha (sub_pos.mpr hθa))).mp hLB3
  have hrlarge : K < (θ * a - γ) * (r : ℝ) := by
    have := mul_le_mul_of_nonneg_left hrlo (sub_pos.mpr hθa).le
    nlinarith only [hbudget', this]
  have hscaled : a * L * (r : ℝ) ≤ (r : ℝ) ^ 2 := by
    nlinarith only [mul_le_mul_of_nonneg_right hrlo hrpos.le]
  have hθscaled := mul_le_mul_of_nonneg_left hscaled hθ0.le
  have hlast := mul_lt_mul_of_pos_right hrlarge hL0
  nlinarith only [hup, hθscaled, hlast]

/-- The same providers prove irrationality directly; it is not assumed by GMT. -/
theorem irrational_of_family_nv0 (Fam : PolyFamily) (scale : Fam.ι → ℕ)
    {Λ D c γ K : ℝ} (hΛ : HasScaledContent Fam scale Λ)
    (hD : HasScaledDecay Fam scale D c) (hη : Λ < D)
    (hγ : 0 < γ) (hK : 0 ≤ K)
    (hdeg : ∀ n, Fam.Adm n → (Fam.deg n : ℝ) ≤ γ * scale n + K)
    (hnv : HasNV0 Fam scale) : Irrational Fam.const := by
  rintro ⟨x, hx⟩
  let θ := (D - Λ) / 2
  let ε := (D - Λ) / 8
  have hθ : 0 < θ := by dsimp [θ]; linarith
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hbudget : θ + 2 * ε ≤ D - Λ := by dsimp [θ, ε]; linarith
  obtain ⟨Rsep, hsep⟩ := scaled_sep Fam scale hΛ hD hε hbudget
  obtain ⟨Rnv, hnv⟩ := hnv
  obtain ⟨N, hN⟩ := exists_nat_gt ((γ + K) * Real.log (x.den : ℝ) / θ)
  let r := max (max Rsep Rnv) (N + 1)
  have hrN : N < r := lt_of_lt_of_le (Nat.lt_succ_self N) (le_max_right _ _)
  have hrposN : 1 ≤ r := (show 1 ≤ N + 1 by omega).trans (le_max_right _ _)
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hrposN
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hrposN
  obtain ⟨n, hn, hnr, hne⟩ := hnv r
    ((le_max_right Rsep Rnv).trans (le_max_left _ _)) x
  have hxrat : ((x.num : ℚ) / (x.den : ℚ)) = x := Rat.num_div_den x
  have hxreal : (x.num : ℝ) / (x.den : ℝ) = Fam.const := by
    rw [← hx]
    exact (Rat.cast_def x).symm
  have hclose : |Fam.const - (x.num : ℝ) / (x.den : ℝ)| ≤
      Real.exp (-(c + ε) * (scale n : ℝ)) := by
    rw [hxreal, sub_self, abs_zero]
    exact (Real.exp_pos _).le
  have key := hsep n hn
    (by rw [hnr]; exact (le_max_left Rsep Rnv).trans (le_max_left _ _))
    x.num (x.den : ℤ) (by exact_mod_cast x.den_pos)
    (by simpa [hxrat] using hne) (by simpa using hclose)
  simp only [Int.cast_natCast, hnr] at key
  have hq1 : (1 : ℝ) ≤ x.den := by exact_mod_cast x.den_pos
  have hlog : 0 ≤ Real.log (x.den : ℝ) := Real.log_nonneg hq1
  have hd := hdeg n hn
  rw [hnr] at hd
  have hd' : (Fam.deg n : ℝ) ≤ (γ + K) * r := by nlinarith
  have hup := key.trans (mul_le_mul_of_nonneg_right hd' hlog)
  have hbig : (γ + K) * Real.log (x.den : ℝ) < θ * r := by
    have hrN' : (N : ℝ) < r := by exact_mod_cast hrN
    have hNr := hN.trans hrN'
    exact (div_lt_iff₀ hθ).mp hNr |>.trans_eq (mul_comm _ _)
  have := mul_lt_mul_of_pos_right hbig hrpos
  nlinarith

/-- Existing degree-indexed content is a special case of the scale contract. -/
theorem HasScaledContent.of_content (Fam : PolyFamily) {Λ : ℝ}
    (h : HasContent Fam Λ) : HasScaledContent Fam Fam.deg Λ := h

/-- The old exact c-window implies the paper's epsilon-window contract. -/
theorem HasScaledDecay.of_decay (Fam : PolyFamily) {D c : ℝ}
    (h : HasDecay Fam D c) : HasScaledDecay Fam Fam.deg D c := by
  intro ε hε
  obtain ⟨R0, hR⟩ := h ε hε
  refine ⟨R0, ?_⟩
  intro n hn hr t ht
  apply hR n hn hr t
  apply ht.trans (Real.exp_le_exp.mpr ?_)
  have : (0 : ℝ) ≤ Fam.deg n := Nat.cast_nonneg _
  nlinarith

/-- Unit degree-scale specialization in the established family API. -/
theorem measure_of_family_nv0_degree (Fam : PolyFamily) {Λ D c : ℝ}
    (hΛ : HasContent Fam Λ) (hD : HasDecay Fam D c) (hη : Λ < D) (hc : 0 < c)
    (hnv : HasNV0 Fam Fam.deg) : Fam.MeasureLB (c / (D - Λ)) := by
  simpa using measure_of_family_nv0 Fam Fam.deg
    (HasScaledContent.of_content Fam hΛ) (HasScaledDecay.of_decay Fam hD) hη hc
    (γ := 1) (K := 0) (by norm_num) (by norm_num) (by intro n hn; simp) hnv

end CatalanCore.Uniform



