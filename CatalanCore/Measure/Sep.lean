module

public import CatalanCore.Frame.Spec
public import Mathlib.NumberTheory.Real.Irrational

@[expose] public section

/-!
# Separation core for a polynomial family

Generic form of `CatalanLambda.Measure.sep_core`: a nonvanishing `Q_n(p/q)` very close to the
constant forces `θ deg n ≤ log q`.  Uses only `HasContent` (integrality and the size of `Dden`)
and `HasDecay` (the window bound).
-/

namespace CatalanCore

/-- The prime window of design 2.4 / BN: hypothesis of the measure theorem.  For `0 < a`,
`a + R.s < b` and all large `q` there is a prime `l ≡ R.r (mod R.m)` in `(a log q, b log q]`
with `¬ R.Bad l q`.  Proved elsewhere (PNT in arithmetic progressions). -/
def PrimeRule.HasWindow (R : PrimeRule) : Prop :=
  ∀ a b : ℝ, 0 < a → a + (R.s : ℝ) < b →
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∃ l : ℕ, l.Prime ∧ (l : ZMod R.m) = R.r ∧
      a * Real.log q < l ∧ (l : ℝ) ≤ b * Real.log q ∧ ¬ R.Bad l q

namespace Measure

lemma evalR_cast (Fam : PolyFamily) (n : Fam.ι) (x : ℚ) :
    Fam.evalR n (x : ℝ) = ((Fam.evalQ n x : ℚ) : ℝ) := by
  unfold PolyFamily.evalR PolyFamily.evalQ
  exact Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval x (Fam.Q n)

/-- **Separation core.**  If `0 < θ < D - Λ`, then for admissible `n` of large degree, whenever
`Q_n(p/q) ≠ 0` and `|const - p/q| ≤ exp(-c deg n)`, we get `θ deg n ≤ log q`. -/
theorem sep_core (Fam : PolyFamily) {Λ D c : ℝ} (hΛ : HasContent Fam Λ) (hD : HasDecay Fam D c)
    {θ : ℝ} (_hθ0 : 0 < θ) (hθ : θ < D - Λ) :
    ∃ N₀ : ℕ, ∀ n, Fam.Adm n → N₀ ≤ Fam.deg n → ∀ p q : ℤ, 0 < q →
      Fam.evalQ n (p / q) ≠ 0 → |Fam.const - (p : ℝ) / q| ≤ Real.exp (-c * Fam.deg n) →
      θ * Fam.deg n ≤ Real.log q := by
  set e : ℝ := (D - Λ - θ) / 3 with he
  have he0 : 0 < e := by rw [he]; linarith
  obtain ⟨N₂, H2⟩ := hD e he0
  obtain ⟨Dden, hDpos, hint, hlogD⟩ := hΛ
  obtain ⟨N₁, H1⟩ := hlogD e he0
  refine ⟨max (max N₁ N₂) 1, fun n hn hdeg p q hq hP hclose => ?_⟩
  have hh1 : N₁ ≤ Fam.deg n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hdeg
  have hh2 : N₂ ≤ Fam.deg n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hdeg
  have hhpos : (0 : ℝ) < Fam.deg n := by
    have : 1 ≤ Fam.deg n := le_trans (le_max_right _ _) hdeg
    exact_mod_cast this
  set h := Fam.deg n with hh
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  -- upper bound
  have hup := H2 n hn hh2 ((p : ℝ) / q - Fam.const) (by rw [abs_sub_comm]; exact hclose)
  have hrat : Fam.const + ((p : ℝ) / q - Fam.const) = (((p : ℚ) / q : ℚ) : ℝ) := by
    push_cast; ring
  rw [hrat, evalR_cast] at hup
  -- lower bound
  obtain ⟨z, hz⟩ := hint n hn p q hq
  have hDp : (0 : ℝ) < (Dden n : ℝ) := by exact_mod_cast hDpos n
  have hqQ : (0 : ℚ) < q := by exact_mod_cast hq
  have hz0 : z ≠ 0 := by
    intro h0
    rw [h0] at hz
    have h1 : ((q : ℚ) ^ h * (Dden n : ℚ)) ≠ 0 := by
      have := hDpos n
      positivity
    have : Fam.evalQ n ((p : ℚ) / q) = 0 := by
      rcases mul_eq_zero.1 (hz.trans (by simp)) with h2 | h2
      · exact absurd h2 h1
      · exact h2
    exact hP this
  have hz1 : (1 : ℝ) ≤ |(z : ℝ)| := by
    have : (1 : ℤ) ≤ |z| := Int.one_le_abs hz0
    exact_mod_cast this
  have hzR : (q : ℝ) ^ h * (Dden n : ℝ) * ((Fam.evalQ n ((p : ℚ) / q) : ℚ) : ℝ) = z := by
    have := congrArg (Rat.cast : ℚ → ℝ) hz
    push_cast at this
    exact this
  have hA : (0 : ℝ) < (q : ℝ) ^ h * (Dden n : ℝ) := by positivity
  have h1le : (1 : ℝ) ≤ (q : ℝ) ^ h * (Dden n : ℝ) *
      Real.exp (-(D - e) * (h : ℝ) ^ 2) := by
    calc (1 : ℝ) ≤ |(z : ℝ)| := hz1
      _ = (q : ℝ) ^ h * (Dden n : ℝ) * |((Fam.evalQ n ((p : ℚ) / q) : ℚ) : ℝ)| := by
          rw [← hzR, abs_mul, abs_of_pos hA]
      _ ≤ _ := by gcongr
  have hlog := Real.log_le_log one_pos h1le
  rw [Real.log_one, Real.log_mul hA.ne' (Real.exp_pos _).ne', Real.log_mul (by positivity) hDp.ne',
    Real.log_pow, Real.log_exp] at hlog
  have hD' := H1 n hn hh1
  have hmain : (θ + e) * (h : ℝ) ^ 2 ≤ (h : ℝ) * Real.log q := by
    have : e = (D - Λ - θ) / 3 := he
    nlinarith
  have hfin : (θ + e) * (h : ℝ) ≤ Real.log q := by
    by_contra hcon
    push Not at hcon
    nlinarith
  nlinarith

end Measure
end CatalanCore
