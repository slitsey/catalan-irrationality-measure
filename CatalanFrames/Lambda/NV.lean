module

public import CatalanFrames.Lambda.Content
public import CatalanLambda.Measure.Lemma3
public import CatalanLambda.Measure.Irrational

/-!
# λ nonvanishing: `HasNV (ofFrame lamFrame) lamRule (3/4) 1`

The legacy weak nonvanishing (`exists_h_nonvanishing`, ℓ ∤ q) together with Lemma 3
(`lemma3_pq`, ℓ ∣ q but not `ℓ² ∥ q`).  The prime rule is `ℓ ≡ 3 (mod 4)`, bad primes are those
with `ℓ² ∥ q`, so `weight = 1/2` and `s = (1/2) φ(4) = 1`.
-/

@[expose] public section

open CatalanCore

namespace CatalanFrames.Lambda

/-- Primes `ℓ ≡ 3 (mod 4)`; `ℓ` is bad for `q` iff `ℓ² ∥ q`; the product of bad primes is
`≤ q^{1/2}`. -/
def lamRule : PrimeRule where
  m := 4
  r := 3
  hr := by
    exact ⟨⟨3, 3, by decide, by decide⟩, rfl⟩
  Bad := fun l q => l ^ 2 ∣ q ∧ ¬ l ^ 3 ∣ q
  weight := 1 / 2

theorem lamRule_s : lamRule.s = 1 := by
  unfold PrimeRule.s lamRule
  have : Nat.totient 4 = 2 := by decide
  simp [this]

theorem hasNV : HasNV (PolyFamily.ofFrame lamFrame) lamRule (3 / 4) 1 := by
  refine ⟨1, 7, fun l hl hl7 hmod p q hq hcop hbad => ?_⟩
  have h3 : l % 4 = 3 := by
    have h := (ZMod.natCast_eq_natCast_iff' l 3 4).1 (by exact_mod_cast (hmod : (l : ZMod 4) = 3))
    simpa using h
  haveI : Fact l.Prime := ⟨hl⟩
  lift q to ℕ using hq.le
  have hq0 : 0 < q := by exact_mod_cast hq
  have hcop' : Nat.Coprime p.natAbs q := by
    have := Int.isCoprime_iff_gcd_eq_one.1 hcop
    simpa [Int.gcd] using this
  simp only [Int.natAbs_natCast] at hbad
  have key : ∀ n : ℕ, (3 * l - 1) / 4 ≤ n → n ≤ l - 1 → CatalanLambda.P n ((p : ℚ) / q) ≠ 0 →
      ∃ n : ℕ, True ∧ 3 / 4 * (l : ℝ) - 1 ≤ (n : ℝ) ∧ (n : ℝ) ≤ 1 * (l : ℝ) + 1 ∧
        (PolyFamily.ofFrame lamFrame).evalQ n ((p : ℚ) / q) ≠ 0 := by
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
      (CatalanLambda.Measure.lemma3_pq l h3 hl7 p q hq0 hcop' hdv hbad)
  · obtain ⟨h, hh1, hh2, hP⟩ := CatalanLambda.Measure.exists_h_nonvanishing l h3 hl7 p (q : ℤ)
      (by simpa using hdv)
    exact key h hh1 hh2 (by simpa using hP)

end CatalanFrames.Lambda
