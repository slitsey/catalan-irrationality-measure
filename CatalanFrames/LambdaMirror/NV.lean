module

public import CatalanFrames.LambdaMirror.Content
public import CatalanLambda.Mirror.Lemma3
public import CatalanLambda.Mirror.Irrational

/-!
# Mirror nonvanishing: `HasNV (ofFrame mirFrame) mirRule (3/4) 1`

Legacy `exists_h_nonvanishing` (ℓ ∤ q) plus Lemma 3 (`lemma3_pq`), primes `ℓ ≡ 1 (mod 4)`.
-/

@[expose] public section

open CatalanCore

namespace CatalanFrames.LambdaMirror

/-- Primes `ℓ ≡ 1 (mod 4)`; `ℓ` is bad for `q` iff `ℓ² ∥ q`. -/
def mirRule : PrimeRule where
  m := 4
  r := 1
  hr := isUnit_one
  Bad := fun l q => l ^ 2 ∣ q ∧ ¬ l ^ 3 ∣ q
  weight := 1 / 2

theorem mirRule_s : mirRule.s = 1 := by
  unfold PrimeRule.s mirRule
  have : Nat.totient 4 = 2 := by decide
  simp [this]

theorem hasNV : HasNV (PolyFamily.ofFrame mirFrame) mirRule (3 / 4) 1 := by
  refine ⟨1, 13, fun l hl hl13 hmod p q hq hcop hbad => ?_⟩
  have h1 : l % 4 = 1 := by
    have h := (ZMod.natCast_eq_natCast_iff' l 1 4).1 (by exact_mod_cast (hmod : (l : ZMod 4) = 1))
    simpa using h
  haveI : Fact l.Prime := ⟨hl⟩
  lift q to ℕ using hq.le
  have hq0 : 0 < q := by exact_mod_cast hq
  have hcop' : Nat.Coprime p.natAbs q := by
    have := Int.isCoprime_iff_gcd_eq_one.1 hcop
    simpa [Int.gcd] using this
  simp only [Int.natAbs_natCast] at hbad
  have key : ∀ n : ℕ, (3 * l - 3) / 4 ≤ n → n ≤ l - 1 →
      CatalanLambda.Mirror.Pbar n ((p : ℚ) / q) ≠ 0 →
      ∃ n : ℕ, True ∧ 3 / 4 * (l : ℝ) - 1 ≤ (n : ℝ) ∧ (n : ℝ) ≤ 1 * (l : ℝ) + 1 ∧
        (PolyFamily.ofFrame mirFrame).evalQ n ((p : ℚ) / q) ≠ 0 := by
    intro n h1 h2 hP
    refine ⟨n, trivial, ?_, ?_, by rw [evalQ_eq]; exact hP⟩
    · have : 3 * l ≤ 4 * n + 4 := by omega
      have : (3 * l : ℝ) ≤ 4 * n + 4 := by exact_mod_cast this
      linarith
    · have : n ≤ l := by omega
      have : (n : ℝ) ≤ l := by exact_mod_cast this
      linarith
  by_cases hdv : l ∣ q
  · exact key _ le_rfl (by omega)
      (CatalanLambda.Mirror.lemma3_pq l h1 hl13 p q hq0 hcop' hdv hbad)
  · obtain ⟨h, hh1, hh2, hP⟩ := CatalanLambda.Mirror.exists_h_nonvanishing l h1 hl13 p (q : ℤ)
      (by simpa using hdv)
    exact key h hh1 hh2 (by simpa using hP)

end CatalanFrames.LambdaMirror
