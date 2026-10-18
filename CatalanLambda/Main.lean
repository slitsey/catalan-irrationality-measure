import CatalanLambda.Assembly

namespace CatalanLambda

/-- **Theorem 1 (AX).**  Let `ℓ ≡ 3 (mod 4)` be a prime, `ℓ ≥ 7`, and `r ∈ ℚ` with `ℓ ∤ den r`.
Then at least one of `P_{ℓ-1}(r)`, `P_{ℓ-2}(r)`, `P_{(3ℓ-1)/4}(r)` is nonzero,
where `P_h(X) = det (X I + M0)`. -/
theorem lambda_nonvanishing (ℓ : ℕ) [Fact ℓ.Prime] (h3 : ℓ % 4 = 3) (h7 : 7 ≤ ℓ) (r : ℚ)
    (hr : ¬ ℓ ∣ r.den) :
    P (ℓ - 1) r ≠ 0 ∨ P (ℓ - 2) r ≠ 0 ∨ P ((3 * ℓ - 1) / 4) r ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨c1, c2, c3⟩ := hcon
  obtain ⟨K, hK⟩ : ∃ K, ℓ + 1 = 4 * K := ⟨(ℓ + 1) / 4, by omega⟩
  have hrS : r ∈ S ℓ := hr
  have k1 := key_det hK (by omega) (h := ℓ - 1) (by omega) (by omega) hrS c1
  have k2 := key_det hK (by omega) (h := ℓ - 2) (by omega) (by omega) hrS c2
  have k3 := key_det hK (by omega) (h := (3 * ℓ - 1) / 4) (by omega) (by omega) hrS c3
  have e1 : ℓ - (ℓ - 1) = 1 := by omega
  have e2 : ℓ - (ℓ - 2) = 2 := by omega
  have e3 : ℓ - (3 * ℓ - 1) / 4 = K := by omega
  rw [e1] at k1
  rw [e2] at k2
  rw [e3] at k3
  exact no_triple K (by omega) (by omega) (by omega) _ k1 k2 k3

end CatalanLambda
