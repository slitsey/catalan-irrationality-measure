module

public import CatalanCore.Zeta5.Content.Weights
public import CatalanCore.Zeta5.Port.Degree

@[expose] public section

/-!
# ZC32: the content limit `Λ = 1288003/10⁶` (signed normaliser, parity gain as `hpar`)

With `K = 40 n`, `M = M(K) = max 40 ⌊√⌊√K⌋⌋` and the fixed tail cut `T = 10⁸`:

* `pt_bound`: `(-L_p^C) log p ≤ φ(p)`, where `φ` is the sum of the band terms (small primes,
  inner tail, inner main term, inner error, parity gain, outer main term, outer saving, outer
  error);
* `log_mC_le`: `log m_C ≤` the band sums, each bounded by ZC29 or written as `K² psum`;
* `intRT`: `∫₃^T R/x³ ≤ I200 − 103109/24·10⁶ + 22/T`;
* `zc32_signed`: given `hpar : ParityGain`, for all large `n` the positive rational `m_C` has
  `q^{37n} m_C F_n(p/q) ∈ ℤ` and `log m_C ≤ (1288003/10⁶) (40 n)²`.

The normaliser is a positive rational, not a natural number; `HasScaledContent` takes
`den : ℕ → ℕ`, and the signed form is the input of ZA17.
-/

open Filter MeasureTheory Polynomial
open scoped Topology

set_option linter.deprecated false

namespace CatalanCore.Zeta5.Content

open Apery CatalanCore.Zeta5.CostOut CatalanCore.Zeta5.Profile CatalanCore.Zeta5.Sum

/-! ### The inner cut-off `M` -/

/-- `M(K) = max 40 ⌊√⌊√K⌋⌋`. -/
def Mf (K : ℕ) : ℕ := max 40 (Nat.sqrt (Nat.sqrt K))

lemma sqsq_le (K : ℕ) :
    Nat.sqrt (Nat.sqrt K) * Nat.sqrt (Nat.sqrt K) * (Nat.sqrt (Nat.sqrt K) * Nat.sqrt (Nat.sqrt K))
      ≤ K :=
  calc _ ≤ Nat.sqrt K * Nat.sqrt K := Nat.mul_le_mul (Nat.sqrt_le _) (Nat.sqrt_le _)
    _ ≤ K := Nat.sqrt_le K

lemma Mf_ge (b K : ℕ) (hK : b * b * (b * b) ≤ K) : b ≤ Mf K :=
  le_max_of_le_right (Nat.le_sqrt.mpr (Nat.le_sqrt.mpr hK))

lemma Mf_eq {K : ℕ} (hK : 40 ^ 4 ≤ K) : Mf K = Nat.sqrt (Nat.sqrt K) :=
  max_eq_right (Nat.le_sqrt.mpr (Nat.le_sqrt.mpr (by norm_num at hK ⊢; omega)))

lemma Mf_tendsto : Tendsto (fun K : ℕ => (Mf K : ℝ)) atTop atTop := by
  rw [tendsto_natCast_atTop_iff, tendsto_atTop_atTop]
  exact fun b => ⟨b * b * (b * b), fun K hK => Mf_ge b K hK⟩

lemma Mf_cube : Tendsto (fun K : ℕ => (Mf K : ℝ) ^ 3 / K) atTop (𝓝 0) := by
  have h1 : Tendsto (fun K : ℕ => 1 / (Mf K : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Mf_tendsto
  refine squeeze_zero' ?_ ?_ h1
  · filter_upwards with K
    positivity
  · filter_upwards [eventually_ge_atTop (40 ^ 4)] with K hK
    have h4 := sqsq_le K
    rw [← Mf_eq hK] at h4
    have hM40 : 40 ≤ Mf K := le_max_left _ _
    have hM : (0 : ℝ) < Mf K := by exact_mod_cast (by omega : 0 < Mf K)
    have h4' : (Mf K : ℝ) ^ 4 ≤ K := by
      have : Mf K ^ 4 ≤ K := by
        rw [show Mf K ^ 4 = Mf K * Mf K * (Mf K * Mf K) by ring]; exact h4
      exact_mod_cast this
    have hK0 : (0 : ℝ) < K := lt_of_lt_of_le (pow_pos hM 4) h4'
    rw [div_le_div_iff₀ hK0 hM]
    nlinarith

lemma Mf_R1 {K : ℕ} (hK : 40 ^ 4 ≤ K) : 200 * Mf K ^ 2 ≤ K := by
  rw [Mf_eq hK]
  have a := Nat.sqrt_le (Nat.sqrt K)
  have b := Nat.sqrt_le K
  have c : 1600 ≤ Nat.sqrt K := Nat.le_sqrt.mpr (by norm_num at hK ⊢; omega)
  calc 200 * Nat.sqrt (Nat.sqrt K) ^ 2
      = 200 * (Nat.sqrt (Nat.sqrt K) * Nat.sqrt (Nat.sqrt K)) := by ring
    _ ≤ 200 * Nat.sqrt K := Nat.mul_le_mul_left _ a
    _ ≤ Nat.sqrt K * Nat.sqrt K := Nat.mul_le_mul_right _ (by omega)
    _ ≤ K := b

/-! ### Bands -/

lemma mem_band {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) {p : ℕ} :
    p ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊ ↔ a < p ∧ (p : ℝ) ≤ b := by
  rw [Finset.mem_Ioc, Nat.floor_lt ha, Nat.le_floor_iff hb]

lemma mem_band0 {b : ℝ} (hb : 0 ≤ b) {p : ℕ} :
    p ∈ Finset.Ioc 0 ⌊b⌋₊ ↔ 0 < p ∧ (p : ℝ) ≤ b := by
  rw [Finset.mem_Ioc, Nat.le_floor_iff hb]

/-- The majorant `φ(p)` of `(-L_p^C) log p`, band by band. -/
noncomputable def phi (M n : ℕ) (T : ℝ) (p : ℕ) : ℝ :=
  (if p ∈ Finset.Ioc 0 ⌊((40 * n : ℕ) : ℝ) / M⌋₊ then |(LpC M n p : ℝ)| * Real.log p else 0)
  + (if p ∈ Finset.Ioc ⌊((40 * n : ℕ) : ℝ) / M⌋₊ ⌊((40 * n : ℕ) : ℝ) / T⌋₊ then
      |(p : ℝ) * Rg (((40 * n : ℕ) : ℝ) / p)| * Real.log p else 0)
  + (if p ∈ Finset.Ioc ⌊((40 * n : ℕ) : ℝ) / T⌋₊ ⌊((40 * n : ℕ) : ℝ) / 3⌋₊ then
      (p : ℝ) * Rg (((40 * n : ℕ) : ℝ) / p) * Real.log p else 0)
  + (if p ∈ Finset.Ioc ⌊((40 * n : ℕ) : ℝ) / M⌋₊ ⌊((40 * n : ℕ) : ℝ) / 3⌋₊ then
      (190 * (M : ℝ) ^ 3 + 30 * M) * Real.log p else 0)
  - (if p ∈ Finset.Ioc ⌊((40 * n : ℕ) : ℝ) / 200⌋₊ ⌊((40 * n : ℕ) : ℝ) / 3⌋₊ then
      (p : ℝ) * gref (((40 * n : ℕ) : ℝ) / p) * Real.log p else 0)
  + (if p ∈ Finset.Ioc ⌊((40 * n : ℕ) : ℝ) / 3⌋₊ ⌊((40 * n : ℕ) : ℝ) / (20 / 37)⌋₊ then
      (p : ℝ) * Ex (((40 * n : ℕ) : ℝ) / p) * Real.log p else 0)
  - (if p ∈ Finset.Ioc ⌊((40 * n : ℕ) : ℝ) / 3⌋₊ ⌊((40 * n : ℕ) : ℝ) / 1⌋₊ then
      (p : ℝ) * max 0 (Ex (((40 * n : ℕ) : ℝ) / p) - Rg (((40 * n : ℕ) : ℝ) / p)) * Real.log p
      else 0)
  + (if p ∈ Finset.Ioc ⌊((40 * n : ℕ) : ℝ) / 3⌋₊ ⌊((40 * n : ℕ) : ℝ) / (20 / 37)⌋₊ then
      86 * Real.log p else 0)

/-- **Pointwise majorant.** -/
theorem pt_bound {M n : ℕ} {T : ℝ} (hT : 200 ≤ T) (hTM : T ≤ M) (hM : 40 ≤ M)
    (hK : 200 * M ^ 2 ≤ 40 * n) (hn : 8 ≤ n) {p : ℕ} (hp : p.Prime) (hp74 : p ≤ 2 * (37 * n)) :
    -(LpC M n p : ℝ) * Real.log p ≤ phi M n T p := by
  have hlog : 0 ≤ Real.log p := Real.log_natCast_nonneg p
  have hP : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hR : (0 : ℝ) ≤ ((40 * n : ℕ) : ℝ) := Nat.cast_nonneg _
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hT0 : (0 : ℝ) < T := by linarith
  have o1 : ((40 * n : ℕ) : ℝ) / M ≤ ((40 * n : ℕ) : ℝ) / T :=
    div_le_div_of_nonneg_left hR hT0 hTM
  have o2 : ((40 * n : ℕ) : ℝ) / T ≤ ((40 * n : ℕ) : ℝ) / 200 :=
    div_le_div_of_nonneg_left hR (by norm_num) hT
  have o3 : ((40 * n : ℕ) : ℝ) / 200 ≤ ((40 * n : ℕ) : ℝ) / 3 :=
    div_le_div_of_nonneg_left hR (by norm_num) (by norm_num)
  have o4 : ((40 * n : ℕ) : ℝ) / 3 ≤ ((40 * n : ℕ) : ℝ) / 1 :=
    div_le_div_of_nonneg_left hR (by norm_num) (by norm_num)
  have o5 : (p : ℝ) ≤ ((40 * n : ℕ) : ℝ) / (20 / 37) := by
    have : (p : ℝ) ≤ ((2 * (37 * n) : ℕ) : ℝ) := by exact_mod_cast hp74
    have e : ((40 * n : ℕ) : ℝ) / (20 / 37) = ((2 * (37 * n) : ℕ) : ℝ) := by push_cast; ring
    rw [e]; exact this
  have hR1 : ((40 * n : ℕ) : ℝ) / 1 = ((40 * n : ℕ) : ℝ) := div_one _
  -- non-membership helpers
  have nlo : ∀ {a b : ℝ}, 0 ≤ a → 0 ≤ b → ¬ (a < p) → p ∉ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊ :=
    fun ha hb h hm => h ((mem_band ha hb).mp hm).1
  have nhi : ∀ {a b : ℝ}, 0 ≤ a → 0 ≤ b → ¬ ((p : ℝ) ≤ b) → p ∉ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊ :=
    fun ha hb h hm => h ((mem_band ha hb).mp hm).2
  have yes : ∀ {a b : ℝ}, 0 ≤ a → 0 ≤ b → a < p → (p : ℝ) ≤ b → p ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊ :=
    fun ha hb h1 h2 => (mem_band ha hb).mpr ⟨h1, h2⟩
  have hRM : (0 : ℝ) ≤ ((40 * n : ℕ) : ℝ) / M := by positivity
  have hRT : (0 : ℝ) ≤ ((40 * n : ℕ) : ℝ) / T := by positivity
  have hR3 : (0 : ℝ) ≤ ((40 * n : ℕ) : ℝ) / 3 := by positivity
  have hR200 : (0 : ℝ) ≤ ((40 * n : ℕ) : ℝ) / 200 := by positivity
  have hR1' : (0 : ℝ) ≤ ((40 * n : ℕ) : ℝ) / 1 := by positivity
  have hR2 : (0 : ℝ) ≤ ((40 * n : ℕ) : ℝ) / (20 / 37) := by positivity
  unfold phi
  by_cases h1 : (p : ℝ) ≤ ((40 * n : ℕ) : ℝ) / M
  · -- small primes
    have hs : p * M ≤ 40 * n := by
      rw [le_div_iff₀ hM0] at h1; exact_mod_cast h1
    rw [if_pos ((mem_band0 hRM).mpr ⟨hp.pos, h1⟩),
      if_neg (nlo hRM hRT (by linarith)), if_neg (nlo hRT hR3 (by linarith)),
      if_neg (nlo hRM hR3 (by linarith)), if_neg (nlo hR200 hR3 (by linarith)),
      if_neg (nlo hR3 hR2 (by linarith)), if_neg (nlo hR3 hR1' (by linarith)),
      if_neg (nlo hR3 hR2 (by linarith))]
    have := mul_le_mul_of_nonneg_right (neg_le_abs (LpC M n p : ℝ)) hlog
    linarith
  have h1' : ((40 * n : ℕ) : ℝ) / M < p := lt_of_not_ge h1
  have hpM : 40 * n < p * M := by
    rw [div_lt_iff₀ hM0] at h1'; exact_mod_cast h1'
  have nA : p ∉ Finset.Ioc 0 ⌊((40 * n : ℕ) : ℝ) / M⌋₊ := fun hm => h1 ((mem_band0 hRM).mp hm).2
  by_cases h3 : (p : ℝ) ≤ ((40 * n : ℕ) : ℝ) / 3
  · -- inner primes
    have hp3 : 3 * p ≤ 40 * n := by
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 3)] at h3
      have : ((3 * p : ℕ) : ℝ) ≤ ((40 * n : ℕ) : ℝ) := by push_cast at h3 ⊢; linarith
      exact_mod_cast this
    have hin := LpC_inner hp hM hK hpM hp3
    rw [if_neg nA, if_pos (yes hRM hR3 h1' h3), if_neg (nlo hR3 hR2 (by linarith)),
      if_neg (nlo hR3 hR1' (by linarith)), if_neg (nlo hR3 hR2 (by linarith))]
    by_cases h4 : (p : ℝ) ≤ ((40 * n : ℕ) : ℝ) / T
    · have h200 : ¬ 40 * n < 200 * p := by
        intro h
        have : ((40 * n : ℕ) : ℝ) < ((200 * p : ℕ) : ℝ) := by exact_mod_cast h
        push_cast at this
        have : (p : ℝ) ≤ ((40 * n : ℕ) : ℝ) / 200 := le_trans h4 o2
        rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 200)] at this
        push_cast at this
        linarith
      rw [if_neg h200] at hin
      rw [if_pos (yes hRM hRT h1' h4), if_neg (nlo hRT hR3 (by linarith)),
        if_neg (nlo hR200 hR3 (by linarith))]
      have a1 := mul_le_mul_of_nonneg_right hin hlog
      have a2 := mul_le_mul_of_nonneg_right
        (le_abs_self ((p : ℝ) * Rg (((40 * n : ℕ) : ℝ) / p))) hlog
      linarith
    · have h4' : ((40 * n : ℕ) : ℝ) / T < p := lt_of_not_ge h4
      rw [if_neg (nhi hRM hRT h4), if_pos (yes hRT hR3 h4' h3)]
      by_cases h5 : ((40 * n : ℕ) : ℝ) / 200 < p
      · have h200 : 40 * n < 200 * p := by
          rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 200)] at h5
          have : ((40 * n : ℕ) : ℝ) < ((200 * p : ℕ) : ℝ) := by push_cast at h5 ⊢; linarith
          exact_mod_cast this
        rw [if_pos h200] at hin
        rw [if_pos (yes hR200 hR3 h5 h3)]
        have a1 := mul_le_mul_of_nonneg_right hin hlog
        linarith
      · have h200 : ¬ 40 * n < 200 * p := by
          intro h
          have : ((40 * n : ℕ) : ℝ) < ((200 * p : ℕ) : ℝ) := by exact_mod_cast h
          push_cast at this
          apply h5
          rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 200)]
          push_cast
          linarith
        rw [if_neg h200] at hin
        rw [if_neg (nlo hR200 hR3 h5)]
        have a1 := mul_le_mul_of_nonneg_right hin hlog
        linarith
  · -- outer primes
    have h3' : ((40 * n : ℕ) : ℝ) / 3 < p := lt_of_not_ge h3
    have h40 : 40 * n < 3 * p := by
      rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 3)] at h3'
      have : ((40 * n : ℕ) : ℝ) < ((3 * p : ℕ) : ℝ) := by push_cast at h3' ⊢; linarith
      exact_mod_cast this
    have hout := LpC_outer (M := M) hp (by omega) (by omega) (by omega) h40 hp74
    rw [if_neg nA, if_neg (nhi hRM hRT (by linarith)), if_neg (nhi hRT hR3 h3),
      if_neg (nhi hRM hR3 h3), if_neg (nhi hR200 hR3 h3), if_pos (yes hR3 hR2 h3' o5),
      if_pos (yes hR3 hR2 h3' o5)]
    by_cases h6 : p ≤ 40 * n
    · have h6' : (p : ℝ) ≤ ((40 * n : ℕ) : ℝ) / 1 := by rw [hR1]; exact_mod_cast h6
      rw [if_pos h6] at hout
      rw [if_pos (yes hR3 hR1' h3' h6')]
      have a1 := mul_le_mul_of_nonneg_right hout hlog
      linarith
    · have h6' : ¬ (p : ℝ) ≤ ((40 * n : ℕ) : ℝ) / 1 := by
        rw [hR1]; intro h; exact h6 (by exact_mod_cast h)
      rw [if_neg h6] at hout
      rw [if_neg (nhi hR3 hR1' h6')]
      have a1 := mul_le_mul_of_nonneg_right hout hlog
      linarith

/-! ### The band sums -/

lemma sum_band {n : ℕ} (f : ℕ → ℝ) {I : Finset ℕ} (hI : ∀ p ∈ I, p ≤ 2 * (37 * n)) :
    ∑ p ∈ (Finset.range (2 * (37 * n) + 1)).filter Nat.Prime, (if p ∈ I then f p else 0)
      = ∑ p ∈ I.filter Nat.Prime, f p := by
  rw [Finset.sum_ite_mem]
  congr 1
  ext p
  simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨⟨_, hp⟩, hpI⟩; exact ⟨hpI, hp⟩
  · rintro ⟨hpI, hp⟩; exact ⟨⟨by have := hI p hpI; omega, hp⟩, hpI⟩

lemma band_le {n : ℕ} {a b : ℝ} (hb : b ≤ ((40 * n : ℕ) : ℝ) / (20 / 37)) :
    ∀ p ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, p ≤ 2 * (37 * n) := by
  intro p hp
  have e : ((40 * n : ℕ) : ℝ) / (20 / 37) = ((2 * (37 * n) : ℕ) : ℝ) := by push_cast; ring
  rw [e] at hb
  exact (Finset.mem_Ioc.mp hp).2.trans (Nat.floor_le_of_le hb)

lemma psum_eq (H : ℝ → ℝ) {a b R : ℝ} (hR : 0 < R) :
    ∑ p ∈ (Finset.Ioc ⌊R / b⌋₊ ⌊R / a⌋₊).filter Nat.Prime, (p : ℝ) * H (R / p) * Real.log p
      = R ^ 2 * psum H a b R := by
  unfold psum
  field_simp

lemma Rg_lin (x : ℝ) (hx : 1 ≤ x) : |Rg x| ≤ 22 * (x + 1) := by
  have hx0 : 0 < x := by linarith
  have h := Rg_bound x hx
  rw [abs_div, abs_of_pos (pow_pos hx0 3), div_le_div_iff₀ (pow_pos hx0 3) (pow_pos hx0 2)] at h
  have hx2 : 0 < x ^ 2 := by positivity
  have : |Rg x| ≤ 22 * x := by
    by_contra hc
    push_neg at hc
    have := mul_lt_mul_of_pos_right hc hx2
    nlinarith
  linarith

/-- **The cost bound.** `log m_C` is at most the band sums. -/
theorem log_mC_le {M n : ℕ} {T : ℝ} (hT : 200 ≤ T) (hTM : T ≤ M) (hM : 40 ≤ M)
    (hK : 200 * M ^ 2 ≤ 40 * n) (hn : 8 ≤ n) :
    Real.log (mC M n) ≤
      7 * ((40 * n : ℕ) : ℝ) * (Real.log 4 * (((40 * n : ℕ) : ℝ) / M)
          + Real.sqrt ((5 * (40 * n) : ℕ) : ℝ) * Real.log ((5 * (40 * n) : ℕ) : ℝ))
      + 2 * 22 * Real.log 4 * (((40 * n : ℕ) : ℝ) ^ 2 / T)
      + ((40 * n : ℕ) : ℝ) ^ 2 * psum Rg 3 T ((40 * n : ℕ) : ℝ)
      + (220 * (M : ℝ) ^ 3) * (Real.log 4 * (((40 * n : ℕ) : ℝ) / 3))
      - ((40 * n : ℕ) : ℝ) ^ 2 * psum gref 3 200 ((40 * n : ℕ) : ℝ)
      + ((40 * n : ℕ) : ℝ) ^ 2 * psum Ex (20 / 37) 3 ((40 * n : ℕ) : ℝ)
      - ((40 * n : ℕ) : ℝ) ^ 2 * psum (fun t => max 0 (Ex t - Rg t)) 1 3 ((40 * n : ℕ) : ℝ)
      + 86 * (Real.log 4 * ((37 / 20) * ((40 * n : ℕ) : ℝ))) := by
  set R : ℝ := ((40 * n : ℕ) : ℝ) with hRdef
  have hR0 : 0 < R := by rw [hRdef]; push_cast; positivity
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hT0 : (0 : ℝ) < T := by linarith
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast (by omega : 1 ≤ M)
  have hl4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have e2037 : R / (20 / 37) = 37 / 20 * R := by ring
  -- step 1: the pointwise majorant
  have hsum : Real.log (mC M n) ≤
      ∑ p ∈ (Finset.range (2 * (37 * n) + 1)).filter Nat.Prime, phi M n T p := by
    rw [log_mC, ← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro p hp
    rw [Finset.mem_filter, Finset.mem_range] at hp
    have := pt_bound hT hTM hM hK hn hp.2 (by omega)
    linarith
  -- step 2: split into bands
  have c1 : R / M ≤ R / (20 / 37) :=
    div_le_div_of_nonneg_left hR0.le (by norm_num) (by linarith)
  have c2 : R / T ≤ R / (20 / 37) :=
    div_le_div_of_nonneg_left hR0.le (by norm_num) (by linarith)
  have c3 : R / 3 ≤ R / (20 / 37) :=
    div_le_div_of_nonneg_left hR0.le (by norm_num) (by norm_num)
  have c4 : R / 1 ≤ R / (20 / 37) :=
    div_le_div_of_nonneg_left hR0.le (by norm_num) (by norm_num)
  have hA := sum_band (n := n) (fun p => |(LpC M n p : ℝ)| * Real.log p)
    (I := Finset.Ioc 0 ⌊R / M⌋₊) (by
      intro p hp
      have := band_le (n := n) (a := 0) c1 p (by rw [Nat.floor_zero]; exact hp)
      exact this)
  have hB1 := sum_band (n := n) (fun p => |(p : ℝ) * Rg (R / p)| * Real.log p)
    (band_le (n := n) (a := R / M) c2)
  have hB2 := sum_band (n := n) (fun p => (p : ℝ) * Rg (R / p) * Real.log p)
    (band_le (n := n) (a := R / T) c3)
  have hBin := sum_band (n := n) (fun p => (190 * (M : ℝ) ^ 3 + 30 * M) * Real.log p)
    (band_le (n := n) (a := R / M) c3)
  have hG := sum_band (n := n) (fun p => (p : ℝ) * gref (R / p) * Real.log p)
    (band_le (n := n) (a := R / 200) c3)
  have hO := sum_band (n := n) (fun p => (p : ℝ) * Ex (R / p) * Real.log p)
    (band_le (n := n) (a := R / 3) (b := R / (20 / 37)) le_rfl)
  have hO1 := sum_band (n := n)
    (fun p => (p : ℝ) * max 0 (Ex (R / p) - Rg (R / p)) * Real.log p)
    (band_le (n := n) (a := R / 3) c4)
  have hOl := sum_band (n := n) (fun p => 86 * Real.log p)
    (band_le (n := n) (a := R / 3) (b := R / (20 / 37)) le_rfl)
  have hsplit : ∑ p ∈ (Finset.range (2 * (37 * n) + 1)).filter Nat.Prime, phi M n T p
      = (∑ p ∈ (Finset.Ioc 0 ⌊R / M⌋₊).filter Nat.Prime, |(LpC M n p : ℝ)| * Real.log p)
        + (∑ p ∈ (Finset.Ioc ⌊R / M⌋₊ ⌊R / T⌋₊).filter Nat.Prime,
            |(p : ℝ) * Rg (R / p)| * Real.log p)
        + (∑ p ∈ (Finset.Ioc ⌊R / T⌋₊ ⌊R / 3⌋₊).filter Nat.Prime,
            (p : ℝ) * Rg (R / p) * Real.log p)
        + (∑ p ∈ (Finset.Ioc ⌊R / M⌋₊ ⌊R / 3⌋₊).filter Nat.Prime,
            (190 * (M : ℝ) ^ 3 + 30 * M) * Real.log p)
        - (∑ p ∈ (Finset.Ioc ⌊R / 200⌋₊ ⌊R / 3⌋₊).filter Nat.Prime,
            (p : ℝ) * gref (R / p) * Real.log p)
        + (∑ p ∈ (Finset.Ioc ⌊R / 3⌋₊ ⌊R / (20 / 37)⌋₊).filter Nat.Prime,
            (p : ℝ) * Ex (R / p) * Real.log p)
        - (∑ p ∈ (Finset.Ioc ⌊R / 3⌋₊ ⌊R / 1⌋₊).filter Nat.Prime,
            (p : ℝ) * max 0 (Ex (R / p) - Rg (R / p)) * Real.log p)
        + (∑ p ∈ (Finset.Ioc ⌊R / 3⌋₊ ⌊R / (20 / 37)⌋₊).filter Nat.Prime, 86 * Real.log p) := by
    unfold phi
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [hA, hB1, hB2, hBin, hG, hO, hO1, hOl]
  -- step 3: each band
  have bA : (∑ p ∈ (Finset.Ioc 0 ⌊R / M⌋₊).filter Nat.Prime, |(LpC M n p : ℝ)| * Real.log p)
      ≤ 7 * R * (Real.log 4 * (R / M)
          + Real.sqrt ((5 * (40 * n) : ℕ) : ℝ) * Real.log ((5 * (40 * n) : ℕ) : ℝ)) :=
    small_primes_bound (w := fun p => (LpC M n p : ℝ)) (c := 7) (C := 5) (K := 40 * n)
      (by norm_num) (by omega) (by positivity) (fun p hp hpy => by
        have hs : p * M ≤ 40 * n := by
          rw [le_div_iff₀ hM0, hRdef] at hpy; exact_mod_cast hpy
        exact LpC_small hp (by omega) hs)
  have bB1 : (∑ p ∈ (Finset.Ioc ⌊R / M⌋₊ ⌊R / T⌋₊).filter Nat.Prime,
      |(p : ℝ) * Rg (R / p)| * Real.log p) ≤ 2 * 22 * Real.log 4 * (R ^ 2 / T) := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.filter_subset_filter _
        (show Finset.Ioc ⌊R / M⌋₊ ⌊R / T⌋₊ ⊆ Finset.Ioc 0 ⌊R / T⌋₊ from ?_))
      (fun i _ _ => mul_nonneg (abs_nonneg _) (Real.log_natCast_nonneg i))) ?_
    · intro p hp
      rw [Finset.mem_Ioc] at hp ⊢
      exact ⟨by omega, hp.2⟩
    · exact inner_tail_bound (R := Rg) (C₁ := 22) (K := 40 * n) (by norm_num) Rg_lin
        (by linarith)
  have eB2 := psum_eq Rg (a := 3) (b := T) hR0
  have bBin : (∑ p ∈ (Finset.Ioc ⌊R / M⌋₊ ⌊R / 3⌋₊).filter Nat.Prime,
      (190 * (M : ℝ) ^ 3 + 30 * M) * Real.log p) ≤ (220 * (M : ℝ) ^ 3) * (Real.log 4 * (R / 3)) := by
    rw [← Finset.mul_sum]
    have hb := band_log_sum_le (y₁ := R / M) (y₂ := R / 3) (by
      rw [div_le_div_iff₀ hM0 (by norm_num)]; nlinarith) (by positivity)
    have hM3 : (M : ℝ) ≤ (M : ℝ) ^ 3 := le_self_pow₀ hM1 (by norm_num)
    have hE : 190 * (M : ℝ) ^ 3 + 30 * M ≤ 220 * (M : ℝ) ^ 3 := by linarith
    have hE0 : 0 ≤ 190 * (M : ℝ) ^ 3 + 30 * M := by positivity
    calc (190 * (M : ℝ) ^ 3 + 30 * M) * ∑ p ∈ (Finset.Ioc ⌊R / M⌋₊ ⌊R / 3⌋₊).filter Nat.Prime,
          Real.log p ≤ (190 * (M : ℝ) ^ 3 + 30 * M) * (Real.log 4 * (R / 3)) :=
          mul_le_mul_of_nonneg_left hb hE0
      _ ≤ (220 * (M : ℝ) ^ 3) * (Real.log 4 * (R / 3)) :=
          mul_le_mul_of_nonneg_right hE (by positivity)
  have eG := psum_eq gref (a := 3) (b := 200) hR0
  have eO := psum_eq Ex (a := 20 / 37) (b := 3) hR0
  have eO1 := psum_eq (fun t => max 0 (Ex t - Rg t)) (a := 1) (b := 3) hR0
  have bOl : (∑ p ∈ (Finset.Ioc ⌊R / 3⌋₊ ⌊R / (20 / 37)⌋₊).filter Nat.Prime, 86 * Real.log p)
      ≤ 86 * (Real.log 4 * ((37 / 20) * R)) := by
    rw [← Finset.mul_sum]
    have hb := band_log_sum_le (y₁ := R / 3) (y₂ := R / (20 / 37)) c3 (by positivity)
    rw [e2037] at hb ⊢
    linarith
  rw [hsplit] at hsum
  linarith

/-! ### The constant -/

lemma tail_T {T : ℝ} (hT : 40 ≤ T) : -(∫ x in Set.Ioi T, Rg x / x ^ 3) ≤ 22 / T := by
  have hT0 : 0 < T := by linarith
  have hint : IntegrableOn (fun x : ℝ => Rg x / x ^ 3) (Set.Ioi T) :=
    integrableOn_Rg.mono_set (Set.Ioi_subset_Ioi hT)
  have hg : IntegrableOn (fun x : ℝ => 22 * x ^ (-2 : ℝ)) (Set.Ioi T) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) hT0).const_mul 22
  have h1 : -(∫ x in Set.Ioi T, Rg x / x ^ 3) ≤ ∫ x in Set.Ioi T, |Rg x / x ^ 3| :=
    (neg_le_abs _).trans abs_integral_le_integral_abs
  have h2 : ∫ x in Set.Ioi T, |Rg x / x ^ 3| ≤ ∫ x in Set.Ioi T, 22 * x ^ (-2 : ℝ) := by
    apply setIntegral_mono_on (Integrable.abs hint) hg measurableSet_Ioi
    intro x hx
    have hx0 : 0 < x := lt_trans hT0 hx
    have := Rg_bound x (by linarith [show T < x from hx])
    rw [Real.rpow_neg hx0.le, Real.rpow_two]
    calc |Rg x / x ^ 3| ≤ 22 / x ^ 2 := this
      _ = 22 * (x ^ 2)⁻¹ := by ring
  have h3 : ∫ x in Set.Ioi T, 22 * x ^ (-2 : ℝ) = 22 / T := by
    rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hT0]
    have e : (-2 : ℝ) + 1 = -1 := by norm_num
    rw [e, Real.rpow_neg_one]
    field_simp
  linarith

lemma intRT {T : ℝ} (hT : 200 ≤ T) :
    ∫ x in (3 : ℝ)..T, Rg x / x ^ 3 ≤ (I200 : ℝ) + (-103109 / 24000000) + 22 / T := by
  have i1 := (rg_psum (a := 3) (b := 200) (by norm_num) (by norm_num)).1
  have i2 := (rg_psum (a := 200) (b := T) (by norm_num) hT).1
  rw [← intervalIntegral.integral_add_adjacent_intervals i1 i2, zc36]
  have hsplit : ∫ x in Set.Ioi (200 : ℝ), Rg x / x ^ 3
      = (∫ x in (200 : ℝ)..T, Rg x / x ^ 3) + ∫ x in Set.Ioi T, Rg x / x ^ 3 := by
    have h1 : IntegrableOn (fun x : ℝ => Rg x / x ^ 3) (Set.Ioc 200 T) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).1 i2
    have h2 : IntegrableOn (fun x : ℝ => Rg x / x ^ 3) (Set.Ioi T) :=
      integrableOn_Rg.mono_set (Set.Ioi_subset_Ioi (by linarith))
    rw [← Set.Ioc_union_Ioi_eq_Ioi hT,
      setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi h1 h2,
      intervalIntegral.integral_of_le hT]
  have h37 := zc37
  have ht := tail_T (T := T) (by linarith)
  linarith

/-! ### ZC32 -/

lemma int_eval {Q : ℤ[X]} {d : ℕ} (hd : Q.natDegree ≤ d) (p q : ℤ) (hq : 0 < q) :
    ∃ z : ℤ, (q : ℚ) ^ d * (Q.map (Int.castRingHom ℚ)).eval ((p : ℚ) / q) = z := by
  refine ⟨∑ i ∈ Finset.range (d + 1), Q.coeff i * p ^ i * q ^ (d - i), ?_⟩
  have hd' : (Q.map (Int.castRingHom ℚ)).natDegree < d + 1 := by
    rw [natDegree_map_eq_of_injective (RingHom.injective_int _)]; omega
  rw [Polynomial.eval_eq_sum_range' hd', Finset.mul_sum]
  push_cast
  refine Finset.sum_congr rfl fun i hi => ?_
  have hid : i ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hqne : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne'
  have hqd : (q : ℚ) ^ d = q ^ i * q ^ (d - i) := by rw [← pow_add]; congr 1; omega
  rw [Polynomial.coeff_map, eq_intCast, hqd, div_pow]
  field_simp

/-- The ZC32 normaliser at index `n`: `m_C` with `M = M(40 n)`. -/
noncomputable def mZ (n : ℕ) : ℚ := mC (Mf (40 * n)) n

/-- **ZC32 (signed form).** Given the parity gain `hpar`, for all large `n` the positive
rational `m_n = m_C` satisfies `q^{37n} m_n F_n(p/q) ∈ ℤ` and
`log m_n ≤ (1288003/10⁶) (40 n)²`. -/
theorem zc32_signed (hpar : ParityGain) :
    ∃ N0 : ℕ, ∀ n, N0 ≤ n → 0 < mZ n ∧
      (∀ p q : ℤ, 0 < q → ∃ z : ℤ, (q : ℚ) ^ (37 * n) * mZ n * (F n).eval ((p : ℚ) / q) = z) ∧
      Real.log (mZ n) ≤ 1288003 / 10 ^ 6 * ((40 * n : ℕ) : ℝ) ^ 2 := by
  set T : ℝ := 10 ^ 8 with hTdef
  have hT200 : (200 : ℝ) ≤ T := by rw [hTdef]; norm_num
  have hKn : Tendsto (fun n : ℕ => 40 * n) atTop atTop :=
    tendsto_atTop_atTop.mpr fun b => ⟨b, fun a ha => by omega⟩
  have hRn : Tendsto (fun n : ℕ => ((40 * n : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hKn
  -- limits
  have t1 := (rg_psum (a := 3) (b := T) (by norm_num) (by linarith)).2.comp hRn
  have t2 := (gref_psum (a := 3) (b := 200) (by norm_num) (by norm_num)).2.comp hRn
  have t3 := ex_psum.comp hRn
  have t4 := hp_psum.comp hRn
  have t5 := (small_primes_o (c := 7) (C := 5) (by norm_num) Mf_tendsto).comp hKn
  have t6 := (inner_error_o (c := 220) Mf_cube).comp hKn
  have t7 := (outer_error_o 86 (37 / 20)).comp hKn
  set δ : ℝ := 1 / 10 ^ 7 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; norm_num
  have e1 := t1.eventually (gt_mem_nhds (show (∫ x in (3 : ℝ)..T, Rg x / x ^ 3) < (∫ x in (3 : ℝ)..T, Rg x / x ^ 3) + δ by linarith))
  have e2 := t2.eventually (lt_mem_nhds (show (∫ x in (3 : ℝ)..200, gref x / x ^ 3) - δ < (∫ x in (3 : ℝ)..200, gref x / x ^ 3) by linarith))
  have e3 := t3.eventually (gt_mem_nhds (show (127751 / 96000 : ℝ) < 127751 / 96000 + δ by linarith))
  have e4 := t4.eventually (lt_mem_nhds (show (3203 / 163200 : ℝ) - δ < 3203 / 163200 by linarith))
  have e5 := t5.eventually (gt_mem_nhds hδ0)
  have e6 := t6.eventually (gt_mem_nhds hδ0)
  have e7 := t7.eventually (gt_mem_nhds hδ0)
  have e8 := (Mf_tendsto.comp hKn).eventually (eventually_ge_atTop T)
  obtain ⟨N0, hN0⟩ := eventually_atTop.mp
    ((((((((e1.and e2).and e3).and e4).and e5).and e6).and e7).and e8).and
      (eventually_ge_atTop (40 ^ 4)))
  refine ⟨N0, fun n hn => ?_⟩
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨f1, f2⟩, f3⟩, f4⟩, f5⟩, f6⟩, f7⟩, f8⟩, f9⟩ := hN0 n hn
  simp only [Function.comp_apply] at f1 f2 f3 f4 f5 f6 f7 f8
  set M : ℕ := Mf (40 * n) with hMdef
  have hM : 40 ≤ M := le_max_left _ _
  have hK : 200 * M ^ 2 ≤ 40 * n := Mf_R1 (by omega)
  have hn8 : 8 ≤ n := by omega
  have hnorm := zc32_normaliser hpar hM hK
  refine ⟨hnorm.1, ?_, ?_⟩
  · -- integrality
    obtain ⟨Q, hQ⟩ := hnorm.2
    intro p q hq
    have hdeg : Q.natDegree ≤ 37 * n := by
      have h1 : (Q.map (Int.castRingHom ℚ)).natDegree ≤ 37 * n := by
        rw [hQ]
        exact (natDegree_C_mul_le _ _).trans (natDegree_F n).le
      rwa [natDegree_map_eq_of_injective (RingHom.injective_int _)] at h1
    obtain ⟨z, hz⟩ := int_eval hdeg p q hq
    refine ⟨z, ?_⟩
    rw [← hz, hQ, eval_mul, eval_C]
    unfold mZ
    ring
  · -- the log bound
    have hlog := log_mC_le (M := M) (n := n) hT200 f8 hM hK hn8
    set R : ℝ := ((40 * n : ℕ) : ℝ) with hRdef
    have hR0 : 0 < R := by rw [hRdef]; push_cast; positivity
    have hR2 : 0 < R ^ 2 := by positivity
    -- divide the error terms by `R²`
    have k5 : 7 * R * (Real.log 4 * (R / M)
          + Real.sqrt ((5 * (40 * n) : ℕ) : ℝ) * Real.log ((5 * (40 * n) : ℕ) : ℝ))
        = R ^ 2 * (7 * R * (Real.log 4 * (R / M)
          + Real.sqrt ((5 * (40 * n) : ℕ) : ℝ) * Real.log ((5 * (40 * n) : ℕ) : ℝ)) / R ^ 2) := by
      field_simp
    have k6 : (220 * (M : ℝ) ^ 3) * (Real.log 4 * (R / 3))
        = R ^ 2 * ((220 * (M : ℝ) ^ 3) * (Real.log 4 * (R / 3)) / R ^ 2) := by
      field_simp
    have k7 : 86 * (Real.log 4 * ((37 / 20) * R))
        = R ^ 2 * (86 * (Real.log 4 * ((37 / 20) * R)) / R ^ 2) := by
      field_simp
    have k8 : 2 * 22 * Real.log 4 * (R ^ 2 / T) = R ^ 2 * (2 * 22 * Real.log 4 / T) := by ring
    rw [k5, k6, k7, k8] at hlog
    -- the constant
    have hI1 := intRT hT200
    have h38 := zc38
    have hl4 : Real.log 4 ≤ 3 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4); linarith
    have hl40 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    have hQv : ((lambdaQ : ℚ) : ℝ) < 1287995332 / 1000000000 := by
      have := lambdaQ_value.2
      have h := (Rat.cast_lt (K := ℝ)).mpr this
      simpa using h
    have hQe : ((lambdaQ : ℚ) : ℝ) = 127751 / 96000 - 3203 / 163200 + (I200 : ℝ)
        - 103109 / 24000000 - 5847 / 1000000 := by
      unfold lambdaQ; push_cast; ring
    have hTl : 2 * 22 * Real.log 4 / T ≤ 132 / T := by
      apply div_le_div_of_nonneg_right _ (by linarith); linarith
    have hT1 : (132 : ℝ) / T = 132 / 10 ^ 8 := by rw [hTdef]
    have hT2 : (22 : ℝ) / T = 22 / 10 ^ 8 := by rw [hTdef]
    have hS : 7 * R * (Real.log 4 * (R / M)
          + Real.sqrt ((5 * (40 * n) : ℕ) : ℝ) * Real.log ((5 * (40 * n) : ℕ) : ℝ)) / R ^ 2
        + 2 * 22 * Real.log 4 / T + psum Rg 3 T R
        + (220 * (M : ℝ) ^ 3) * (Real.log 4 * (R / 3)) / R ^ 2
        - psum gref 3 200 R + psum Ex (20 / 37) 3 R
        - psum (fun t => max 0 (Ex t - Rg t)) 1 3 R
        + 86 * (Real.log 4 * ((37 / 20) * R)) / R ^ 2 ≤ 1288003 / 10 ^ 6 := by
      rw [hδ] at f1 f2 f3 f4 f5 f6 f7
      linarith
    have := mul_le_mul_of_nonneg_left hS hR2.le
    show Real.log (mC M n) ≤ 1288003 / 10 ^ 6 * R ^ 2
    linarith

end CatalanCore.Zeta5.Content

#print axioms Apery.kpar_ge
#print axioms CatalanCore.Zeta5.Content.zc32_normaliser
#print axioms CatalanCore.Zeta5.Content.log_mC_le
#print axioms CatalanCore.Zeta5.Content.zc32_signed
