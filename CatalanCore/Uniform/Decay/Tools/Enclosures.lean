module
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.Analysis.SpecificLimits.Normed
@[expose] public section

/-!
# Integer-scaled enclosures of `log` and `arctan` (generic scale, ratio, length)

For naturals `a < b`, a scale `S`, and `N` terms put
`scTerm S a b k = ⌊S a^(2k+1) / ((2k+1) b^(2k+1))⌋` (natural-number division).
* `scAtanh S a b N = ∑_{k<N} scTerm`  encloses `S · artanh (a/b)`:
  `|scAtanh − S artanh(a/b)| ≤ N + S u^(2N+1)/(1-u²)`, `u = a/b`.
* `scLog S p q N = 2 · scAtanh S (p-q) (p+q) N` encloses `S log (p/q)`.
* `scAtan S a b (2K) = ∑_{k<2K} (-1)^k scTerm` encloses `S arctan(a/b)`:
  `|scAtan − S arctan(a/b)| ≤ 2K + S u^(2N+1)/(2N+1)`.
-/

namespace CatalanCore.Uniform.Decay.Tools

open Finset

/-- One floor term of the scaled odd-power series. -/
def scTerm (S a b k : ℕ) : ℕ := S * a ^ (2 * k + 1) / (b ^ (2 * k + 1) * (2 * k + 1))

/-- The exact real value whose floor `scTerm` is. -/
noncomputable def scReal (S a b : ℕ) (k : ℕ) : ℝ :=
  (S : ℝ) * (((a : ℝ) / b) ^ (2 * k + 1) / (2 * (k : ℝ) + 1))

theorem scTerm_floor (S a b k : ℕ) (hb : 0 < b) :
    ((scTerm S a b k : ℕ) : ℝ) ≤ scReal S a b k ∧ scReal S a b k < (scTerm S a b k : ℕ) + 1 := by
  have hd : 0 < b ^ (2 * k + 1) * (2 * k + 1) := by positivity
  have hdR : (0 : ℝ) < ((b ^ (2 * k + 1) * (2 * k + 1) : ℕ) : ℝ) := by exact_mod_cast hd
  have e : scReal S a b k
      = ((S * a ^ (2 * k + 1) : ℕ) : ℝ) / ((b ^ (2 * k + 1) * (2 * k + 1) : ℕ) : ℝ) := by
    unfold scReal
    push_cast
    have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
    rw [div_pow]
    field_simp
  rw [e]
  unfold scTerm
  constructor
  · rw [le_div_iff₀ hdR]
    exact_mod_cast Nat.div_mul_le_self _ _
  · rw [div_lt_iff₀ hdR]
    have := Nat.lt_mul_div_succ (S * a ^ (2 * k + 1)) hd
    have h2 : (S * a ^ (2 * k + 1) : ℕ) <
        (S * a ^ (2 * k + 1) / (b ^ (2 * k + 1) * (2 * k + 1)) + 1) *
          (b ^ (2 * k + 1) * (2 * k + 1)) := by
      exact this.trans_eq (Nat.mul_comm _ _)
    exact_mod_cast h2

/-- Scaled `artanh` partial sum. -/
def scAtanh (S a b N : ℕ) : ℕ := ∑ k ∈ range N, scTerm S a b k

/-- Scaled `arctan` partial sum. -/
def scAtan (S a b N : ℕ) : ℤ := ∑ k ∈ range N, (-1 : ℤ) ^ k * (scTerm S a b k : ℤ)

/-- Floor error of a sum of `N` terms: `sum floors ≤ sum reals < sum floors + N`. -/
theorem scAtanh_floor (S a b N : ℕ) (hb : 0 < b) :
    ((scAtanh S a b N : ℕ) : ℝ) ≤ ∑ k ∈ range N, scReal S a b k ∧
    ∑ k ∈ range N, scReal S a b k ≤ (scAtanh S a b N : ℕ) + N := by
  unfold scAtanh
  push_cast
  constructor
  · exact Finset.sum_le_sum fun k _ => (scTerm_floor S a b k hb).1
  · by_cases hN : N = 0
    · subst hN; simp
    · have : ∑ k ∈ range N, scReal S a b k < ∑ k ∈ range N, (((scTerm S a b k : ℕ) : ℝ) + 1) :=
        Finset.sum_lt_sum_of_nonempty (Finset.nonempty_range_iff.mpr hN)
          fun k _ => (scTerm_floor S a b k hb).2
      rw [Finset.sum_add_distrib] at this
      simpa using this.le

theorem scReal_sum (S a b N : ℕ) :
    ∑ k ∈ range N, scReal S a b k
      = (S : ℝ) * ∑ k ∈ range N, ((a : ℝ) / b) ^ (2 * k + 1) / (2 * (k : ℝ) + 1) := by
  unfold scReal; rw [Finset.mul_sum]

/-- **Scaled artanh enclosure**: `u = a/b ∈ [0,1)`. -/
theorem scAtanh_enclosure (S a b N : ℕ) (hb : 0 < b) (hab : a < b) :
    |((scAtanh S a b N : ℕ) : ℝ) -
        (S : ℝ) * (1 / 2 * Real.log ((1 + (a : ℝ) / b) / (1 - (a : ℝ) / b)))|
      ≤ N + (S : ℝ) * (((a : ℝ) / b) ^ (2 * N + 1) / (1 - ((a : ℝ) / b) ^ 2)) := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hu0 : 0 ≤ (a : ℝ) / b := by positivity
  have hu1 : (a : ℝ) / b < 1 := by rw [div_lt_one hbR]; exact_mod_cast hab
  have hS : (0 : ℝ) ≤ S := Nat.cast_nonneg _
  obtain ⟨h1, h2⟩ := scAtanh_floor S a b N hb
  rw [scReal_sum] at h1 h2
  have hlow := Real.sum_range_le_log_div hu0 hu1 N
  have hup := Real.sum_range_sub_log_div_le (x := (a : ℝ) / b)
    (by rw [abs_of_nonneg hu0]; exact hu1) N
  rw [abs_of_nonneg hu0] at hup
  have hup' := (abs_le.mp hup).2
  have hlow' := mul_le_mul_of_nonneg_left hlow hS
  have hup'' := mul_le_mul_of_nonneg_left hup' hS
  rw [abs_le]
  constructor
  · have hnn : 0 ≤ (S : ℝ) * (((a : ℝ) / b) ^ (2 * N + 1) / (1 - ((a : ℝ) / b) ^ 2)) :=
      mul_nonneg hS (div_nonneg (pow_nonneg hu0 _) (by nlinarith))
    nlinarith
  · nlinarith

/-- Scaled logarithm of `p/q`, `q ≤ p`. -/
def scLog (S p q N : ℕ) : ℕ := 2 * scAtanh S (p - q) (p + q) N

/-- **Scaled log enclosure**: for `0 < q ≤ p`, with `u = (p-q)/(p+q)`:
`|scLog − S log (p/q)| ≤ 2N + 2 S u^(2N+1)/(1-u²)`. -/
theorem scLog_enclosure (S p q N : ℕ) (hq : 0 < q) (hqp : q ≤ p) :
    |((scLog S p q N : ℕ) : ℝ) - (S : ℝ) * Real.log ((p : ℝ) / q)|
      ≤ 2 * N + 2 * ((S : ℝ) * ((((p - q : ℕ) : ℝ) / ((p + q : ℕ) : ℝ)) ^ (2 * N + 1) /
          (1 - (((p - q : ℕ) : ℝ) / ((p + q : ℕ) : ℝ)) ^ 2))) := by
  have hpq : p - q < p + q := by omega
  have h := scAtanh_enclosure S (p - q) (p + q) N (by omega) hpq
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hpR : (q : ℝ) ≤ p := by exact_mod_cast hqp
  have hsum : (0 : ℝ) < (p : ℝ) + q := by linarith
  have e : (1 + ((p - q : ℕ) : ℝ) / ((p + q : ℕ) : ℝ)) /
      (1 - ((p - q : ℕ) : ℝ) / ((p + q : ℕ) : ℝ)) = (p : ℝ) / q := by
    have hqne : (q : ℝ) ≠ 0 := hqR.ne'
    have hsne : (p : ℝ) + q ≠ 0 := hsum.ne'
    push_cast [Nat.cast_sub hqp]
    have h1 : 1 + ((p : ℝ) - q) / ((p : ℝ) + q) = 2 * p / ((p : ℝ) + q) := by
      field_simp; ring
    have h2 : 1 - ((p : ℝ) - q) / ((p : ℝ) + q) = 2 * q / ((p : ℝ) + q) := by
      field_simp; ring
    rw [h1, h2]
    field_simp
  rw [e] at h
  unfold scLog
  push_cast at h ⊢
  have : |2 * (scAtanh S (p - q) (p + q) N : ℝ) - (S : ℝ) * Real.log ((p : ℝ) / q)|
      = 2 * |(scAtanh S (p - q) (p + q) N : ℝ) -
          (S : ℝ) * (1 / 2 * Real.log ((p : ℝ) / q))| := by
    rw [← abs_two, ← abs_mul]; congr 1; ring
  rw [this]
  linarith

/-- Alternating scaled series enclosure for `arctan (a/b)`, `a < b`, even length `N = 2K`. -/
theorem scAtan_enclosure (S a b K : ℕ) (hb : 0 < b) (hab : a < b) :
    |((scAtan S a b (2 * K) : ℤ) : ℝ) - (S : ℝ) * Real.arctan ((a : ℝ) / b)|
      ≤ (2 * K : ℕ) +
        (S : ℝ) * (((a : ℝ) / b) ^ (2 * (2 * K) + 1) / (2 * ((2 * K : ℕ) : ℝ) + 1)) := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hu0 : 0 ≤ (a : ℝ) / b := by positivity
  have hu1 : (a : ℝ) / b < 1 := by rw [div_lt_one hbR]; exact_mod_cast hab
  set u : ℝ := (a : ℝ) / b with hu
  have hS : (0 : ℝ) ≤ S := Nat.cast_nonneg _
  set f : ℕ → ℝ := fun i => u ^ (2 * i + 1) / (2 * (i : ℝ) + 1) with hf
  have hs := Real.hasSum_arctan (x := u) (by rwa [Real.norm_eq_abs, abs_of_nonneg hu0])
  have hs' : HasSum (fun n : ℕ => (-1 : ℝ) ^ n * f n) (Real.arctan u) := by
    convert hs using 1
    ext n; simp only [hf]; push_cast; ring
  have hlim := hs'.tendsto_sum_nat
  have hanti : Antitone f := by
    refine antitone_nat_of_succ_le fun i => ?_
    simp only [hf]
    have h1 : u ^ (2 * (i + 1) + 1) ≤ u ^ (2 * i + 1) :=
      pow_le_pow_of_le_one hu0 hu1.le (by omega)
    push_cast
    calc u ^ (2 * (i + 1) + 1) / (2 * ((i : ℝ) + 1) + 1)
        ≤ u ^ (2 * i + 1) / (2 * ((i : ℝ) + 1) + 1) :=
          div_le_div_of_nonneg_right h1 (by positivity)
      _ ≤ _ := div_le_div_of_nonneg_left (pow_nonneg hu0 _) (by positivity) (by linarith)
  have hlo := Antitone.alternating_series_le_tendsto hlim hanti K
  have hhi := Antitone.tendsto_le_alternating_series hlim hanti K
  rw [Finset.sum_range_succ] at hhi
  have hpar : (-1 : ℝ) ^ (2 * K) = 1 := by rw [pow_mul]; simp
  rw [hpar, one_mul] at hhi
  have hterm : ∀ k, |(((-1 : ℤ) ^ k * (scTerm S a b k : ℤ) : ℤ) : ℝ) -
      (-1) ^ k * scReal S a b k| < 1 := by
    intro k
    obtain ⟨l1, l2⟩ := scTerm_floor S a b k hb
    have : |(((-1 : ℤ) ^ k * (scTerm S a b k : ℤ) : ℤ) : ℝ) - (-1) ^ k * scReal S a b k|
        = |((scTerm S a b k : ℕ) : ℝ) - scReal S a b k| := by
      push_cast
      rw [← mul_sub, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    rw [this, abs_lt]; constructor <;> linarith
  have hsumerr : |((scAtan S a b (2 * K) : ℤ) : ℝ) -
      (S : ℝ) * ∑ i ∈ range (2 * K), (-1) ^ i * f i| ≤ (2 * K : ℕ) := by
    have e : (S : ℝ) * ∑ i ∈ range (2 * K), (-1) ^ i * f i
        = ∑ i ∈ range (2 * K), (-1 : ℝ) ^ i * scReal S a b i := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_
      simp only [hf, scReal]; ring
    rw [e]
    unfold scAtan
    push_cast
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc _ ≤ ∑ i ∈ range (2 * K), (1 : ℝ) := Finset.sum_le_sum fun i _ => by
            have := hterm i; push_cast at this; exact this.le
      _ = 2 * (K : ℝ) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]; push_cast; ring
  have hf2 : f (2 * K) = u ^ (2 * (2 * K) + 1) / (2 * ((2 * K : ℕ) : ℝ) + 1) := by
    simp only [hf]
  have hf0 : 0 ≤ f (2 * K) := by simp only [hf]; positivity
  rw [← hf2]
  have key : (S : ℝ) * ∑ i ∈ range (2 * K), (-1) ^ i * f i ≤ (S : ℝ) * Real.arctan u :=
    mul_le_mul_of_nonneg_left hlo hS
  have key2 : (S : ℝ) * Real.arctan u ≤
      (S : ℝ) * (∑ i ∈ range (2 * K), (-1) ^ i * f i + f (2 * K)) :=
    mul_le_mul_of_nonneg_left hhi hS
  rw [abs_le] at hsumerr ⊢
  have hSf : 0 ≤ (S : ℝ) * f (2 * K) := mul_nonneg hS hf0
  constructor <;> nlinarith [hsumerr.1, hsumerr.2]

end CatalanCore.Uniform.Decay.Tools
