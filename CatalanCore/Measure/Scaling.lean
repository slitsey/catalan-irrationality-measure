module

public import CatalanCore.Measure.Statements
public import Mathlib.NumberTheory.Transcendental.Liouville.LiouvilleWith

@[expose] public section

/-!
# Generic rational affine scaling of irrationality measures

For real `x` and rational `a ≠ 0`, `b`: irrationality and the measure bound transfer from `x`
to `a * x + b` with the same exponent (strict slack absorbs the constants).
Replaces the legacy `double_79` (which lost one unit of exponent).
Convention: `IsCoprime p q` as in `PolyFamily.MeasureLB`; `Nat.Coprime p.natAbs q` variants below.
-/

namespace CatalanCore.Measure

/-- The measure statement for a real number (cf. `PolyFamily.MeasureLB`, which is this at
`Fam.const`). -/
def MeasureLBAt (x E : ℝ) : Prop :=
  ∀ e > 0, ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), q₀ ≤ q → IsCoprime p (q : ℤ) →
    (q : ℝ) ^ (-(E + e)) < |x - (p : ℝ) / q|

theorem MeasureLB_iff (Fam : PolyFamily) (E : ℝ) : Fam.MeasureLB E ↔ MeasureLBAt Fam.const E :=
  Iff.rfl

theorem MeasureLBAt.mono {x E E' : ℝ} (hE : E ≤ E') (h : MeasureLBAt x E) : MeasureLBAt x E' := by
  intro e he
  obtain ⟨q₀, H⟩ := h (e + (E' - E)) (by linarith)
  refine ⟨max q₀ 1, fun p q hq hc => ?_⟩
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast le_trans (le_max_right _ _) hq
  refine lt_of_le_of_lt ?_ (H p q (le_trans (le_max_left _ _) hq) hc)
  exact Real.rpow_le_rpow_of_exponent_le hq1 (by linarith)

theorem isCoprime_iff_natCoprime (p : ℤ) (q : ℕ) :
    IsCoprime p (q : ℤ) ↔ Nat.Coprime p.natAbs q := by
  rw [Int.isCoprime_iff_gcd_eq_one]; rfl

/-! ### Bridge to Mathlib's `LiouvilleWith`

`MeasureLBAt x E` says exactly that `x` is not `LiouvilleWith r` for any `r > E`
(for `0 ≤ E`; no irrationality hypothesis is needed).  Rational scaling then follows from
Mathlib's `LiouvilleWith.rat_mul_iff` / `LiouvilleWith.add_rat_iff`. -/

/-- Away from `y`, an integer is at distance at least some `ε > 0` from `y`. -/
theorem exists_gap (y : ℝ) : ∃ ε > 0, ∀ p : ℤ, y ≠ p → ε ≤ |y - p| := by
  by_cases h : y = round y
  · refine ⟨1, one_pos, fun p hp => ?_⟩
    have hne : round y ≠ p := fun e => hp (h.trans (by exact_mod_cast e))
    have h1 : (1 : ℤ) ≤ |round y - p| := Int.one_le_abs (sub_ne_zero.2 hne)
    have h2 : (1 : ℝ) ≤ |((round y : ℤ) : ℝ) - p| := by exact_mod_cast h1
    rwa [← h] at h2
  · exact ⟨|y - round y|, abs_pos.2 (sub_ne_zero.2 h), fun p _ => round_le y p⟩

/-- Every `m/n` equals a coprime fraction with denominator `≤ n`. -/
theorem exists_coprime_rep (m : ℤ) (n : ℕ) :
    ∃ (p : ℤ) (q : ℕ), IsCoprime p (q : ℤ) ∧ 0 < q ∧ (0 < n → q ≤ n) ∧
      (m : ℝ) / n = (p : ℝ) / q := by
  set r : ℚ := (m : ℚ) / n with hr
  refine ⟨r.num, r.den, (isCoprime_iff_natCoprime _ _).2 r.reduced, r.den_pos, fun hn => ?_, ?_⟩
  · have h := Rat.den_dvd m (n : ℤ)
    rw [Rat.divInt_eq_div] at h
    simp only [Int.cast_natCast] at h
    exact Nat.le_of_dvd hn (Int.natCast_dvd_natCast.mp h)
  · have h1 : ((r : ℚ) : ℝ) = (r.num : ℝ) / r.den := Rat.cast_def r
    have h2 : ((r : ℚ) : ℝ) = (m : ℝ) / n := by simp [hr]
    exact h2.symm.trans h1

/-- `MeasureLBAt x E` excludes `LiouvilleWith r x` for every `r > E`. -/
theorem MeasureLBAt.not_liouvilleWith {x E r : ℝ} (hE : 0 ≤ E) (h : MeasureLBAt x E) (hr : E < r) :
    ¬ LiouvilleWith r x := by
  intro hL
  set s := (E + r) / 2 with hs
  have hEs : E < s := by linarith
  have hsr : s < r := by linarith
  obtain ⟨q₀, H⟩ := h (s - E) (by linarith)
  have hF := hL.frequently_lt_rpow_neg hsr
  -- the finitely many small denominators stay at positive distance from `x`
  have hsmall : ∀ᶠ n : ℕ in Filter.atTop, ∀ q ∈ Finset.range q₀, 0 < q →
      ∀ p : ℤ, x ≠ (p : ℝ) / q → (n : ℝ) ^ (-s) < |x - (p : ℝ) / q| := by
    refine (Filter.eventually_all_finset _).2 fun q _ => ?_
    by_cases hq : 0 < q
    · obtain ⟨ε, hε, hg⟩ := exists_gap (q * x)
      have hqr : (0 : ℝ) < q := by exact_mod_cast hq
      have hlim : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ (-s)) Filter.atTop (nhds 0) :=
        (tendsto_rpow_neg_atTop (by linarith)).comp tendsto_natCast_atTop_atTop
      filter_upwards [hlim.eventually (gt_mem_nhds (div_pos hε hqr))] with n hn _ p hp
      refine hn.trans_le ?_
      rw [div_le_iff₀ hqr]
      have := hg p (fun e => hp (by field_simp; linarith))
      calc ε ≤ |q * x - p| := this
        _ = |x - p / q| * q := by
          rw [show (q : ℝ) * x - p = (x - p / q) * q by field_simp, abs_mul, abs_of_pos hqr]
    · exact Filter.Eventually.of_forall fun _ h => absurd h hq
  obtain ⟨n, ⟨hsm, hn⟩, m, hne, hlt⟩ :=
    ((hsmall.and (Filter.eventually_ge_atTop 1)).and_frequently hF).exists
  obtain ⟨p, q, hc, hq, hqn, he⟩ := exists_coprime_rep m n
  rw [he] at hne hlt
  have hqn := hqn hn
  by_cases hq0 : q < q₀
  · exact absurd hlt (not_lt.2 (hsm q (Finset.mem_range.2 hq0) hq p hne).le)
  · have h1 := H p q (not_lt.1 hq0) hc
    have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
    have h2 : (n : ℝ) ^ (-s) ≤ (q : ℝ) ^ (-s) :=
      Real.rpow_le_rpow_of_nonpos hqpos (by exact_mod_cast hqn) (by linarith)
    rw [show E + (s - E) = s by ring] at h1
    linarith

/-- Converse: if no exponent `r > E` is Liouville for `x`, then `MeasureLBAt x E`. -/
theorem measureLBAt_of_not_liouvilleWith {x E : ℝ} (h : ∀ r, E < r → ¬ LiouvilleWith r x) :
    MeasureLBAt x E := by
  by_contra hcon
  unfold MeasureLBAt at hcon
  push Not at hcon
  obtain ⟨e, he, H⟩ := hcon
  -- a coprime fraction equal to `x` has bounded denominator
  obtain ⟨B, hB⟩ : ∃ B : ℕ, ∀ (p : ℤ) (q : ℕ), IsCoprime p (q : ℤ) → 0 < q →
      x = (p : ℝ) / q → q ≤ B := by
    by_cases hx : Irrational x
    · exact ⟨0, fun p q _ hq e => absurd ⟨(p : ℚ) / q, by push_cast; exact e.symm⟩ hx⟩
    · obtain ⟨r, hr⟩ := exists_rat_of_not_irrational hx
      refine ⟨r.den, fun p q hc hq e => ?_⟩
      have hrq : r = (p : ℚ) / ((q : ℤ) : ℚ) := by
        apply Rat.cast_injective (α := ℝ); push_cast; rw [← hr]; exact e
      have key := Rat.den_div_eq_of_coprime (a := p) (b := q) (by exact_mod_cast hq)
        ((isCoprime_iff_natCoprime _ _).1 hc)
      rw [← hrq] at key
      exact_mod_cast key.ge
  refine h (E + e / 2) (by linarith) ⟨1, Filter.frequently_atTop.2 fun N => ?_⟩
  obtain ⟨p, q, hq, hc, hle⟩ := H (max (max N 2) (B + 1))
  have hN : N ≤ q := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hq
  have h2 : 2 ≤ q := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hq
  have hB1 : B + 1 ≤ q := le_trans (le_max_right _ _) hq
  have hq1 : (1 : ℝ) < q := by exact_mod_cast h2
  refine ⟨q, hN, p, fun hx => ?_, ?_⟩
  · have := hB p q hc (by omega) hx
    omega
  · refine hle.trans_lt ?_
    rw [one_div, ← Real.rpow_neg (by linarith)]
    exact Real.rpow_lt_rpow_of_exponent_lt hq1 (by linarith)

theorem MeasureLBAt.neg {x E : ℝ} (h : MeasureLBAt x E) : MeasureLBAt (-x) E := by
  intro e he
  obtain ⟨q₀, H⟩ := h e he
  refine ⟨q₀, fun p q hq hc => ?_⟩
  have := H (-p) q hq hc.neg_left
  rw [show |-x - (p : ℝ) / q| = |x - ((-p : ℤ) : ℝ) / q| by
    rw [← abs_neg]; push_cast; ring_nf]
  exact this

/-- **Affine transfer of the measure bound** (same exponent). Needs `0 ≤ E`. -/
theorem MeasureLBAt.affine {x E : ℝ} (hE : 0 ≤ E) (h : MeasureLBAt x E) (a b : ℚ) (ha : a ≠ 0) :
    MeasureLBAt ((a : ℝ) * x + b) E :=
  measureLBAt_of_not_liouvilleWith fun _ hr hL =>
    h.not_liouvilleWith hE hr (by rwa [LiouvilleWith.add_rat_iff, LiouvilleWith.rat_mul_iff ha] at hL)

theorem irrational_affine {x : ℝ} (hx : Irrational x) (a b : ℚ) (ha : a ≠ 0) :
    Irrational ((a : ℝ) * x + b) :=
  (hx.ratCast_mul ha).add_ratCast b

/-- Strict-slack (fixed exponent) form: `E < E'` turns the `∀ e` statement into a plain bound. -/
theorem MeasureLBAt.round {x E E' : ℝ} (h : MeasureLBAt x E) (hlt : E < E') :
    ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), q₀ ≤ q → IsCoprime p (q : ℤ) →
      (q : ℝ) ^ (-E') < |x - (p : ℝ) / q| := by
  obtain ⟨q₀, H⟩ := h (E' - E) (by linarith)
  exact ⟨q₀, fun p q hq hc => by simpa using H p q hq hc⟩

/-- Generic replacement of `double_79`: if `x` has measure exponent `E < E'`, so does
`a * x + b`, in the plain form with `Nat.Coprime p.natAbs q`. -/
theorem affine_round {x E E' : ℝ} (hE : 0 ≤ E) (hlt : E < E') (h : MeasureLBAt x E)
    (a b : ℚ) (ha : a ≠ 0) :
    ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), Nat.Coprime p.natAbs q → q₀ ≤ q →
      (q : ℝ) ^ (-E') < |(a : ℝ) * x + b - (p : ℝ) / q| := by
  obtain ⟨q₀, H⟩ := (h.affine hE a b ha).round hlt
  exact ⟨q₀, fun p q hc hq => H p q hq ((isCoprime_iff_natCoprime p q).2 hc)⟩

/-- `λ`-corollary: `λ = G/2 - 5π²/96` with exponent `31682445459/409965000 < 78` gives
`G - 5π²/48 = 2λ` with round exponent `78`. -/
theorem double_78 {x : ℝ} (h : MeasureLBAt x (((31682445459 / 409965000 : ℚ)) : ℝ)) :
    ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), Nat.Coprime p.natAbs q → q₀ ≤ q →
      (q : ℝ) ^ (-(78 : ℝ)) < |2 * x - (p : ℝ) / q| := by
  have := affine_round (E' := 78) (by norm_num) (by norm_num) h 2 0 (by norm_num)
  simpa using this

theorem catalan_sub_78 {G : ℝ}
    (h : MeasureLBAt (G / 2 - 5 * Real.pi ^ 2 / 96) (((31682445459 / 409965000 : ℚ)) : ℝ)) :
    ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), Nat.Coprime p.natAbs q → q₀ ≤ q →
      (q : ℝ) ^ (-(78 : ℝ)) < |(G - 5 * Real.pi ^ 2 / 48) - (p : ℝ) / q| := by
  obtain ⟨q₀, H⟩ := double_78 h
  refine ⟨q₀, fun p q hc hq => ?_⟩
  have := H p q hc hq
  rwa [show 2 * (G / 2 - 5 * Real.pi ^ 2 / 96) = G - 5 * Real.pi ^ 2 / 48 by ring] at this

/-- Mirror: `λ' = G/2 + 5π²/96` gives `G + 5π²/48 = 2λ'` with exponent `78`. -/
theorem catalan_add_78 {G : ℝ}
    (h : MeasureLBAt (G / 2 + 5 * Real.pi ^ 2 / 96) (((31682445459 / 409965000 : ℚ)) : ℝ)) :
    ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), Nat.Coprime p.natAbs q → q₀ ≤ q →
      (q : ℝ) ^ (-(78 : ℝ)) < |(G + 5 * Real.pi ^ 2 / 48) - (p : ℝ) / q| := by
  obtain ⟨q₀, H⟩ := double_78 h
  refine ⟨q₀, fun p q hc hq => ?_⟩
  have := H p q hc hq
  rwa [show 2 * (G / 2 + 5 * Real.pi ^ 2 / 96) = G + 5 * Real.pi ^ 2 / 48 by ring] at this

end CatalanCore.Measure
