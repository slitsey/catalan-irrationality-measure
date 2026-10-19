module

public import CatalanCore.Bordered.Z1.Chain

/-!
# Z1.3: `(θ + c)^{chainOrd} ∣ u(X′, e_s)`
-/

@[expose] public section

open Finset Matrix Polynomial

namespace CatalanCore.Bordered.Z1

/-- Order of vanishing of the chain product at `θ = -c`: `c` if `c ≤ s-1`, `0` if `s ≤ c ≤ K`,
`c - K` if `K < c < K + s`, `0` otherwise (`K = s + m`). -/
def chainOrd (s m c : ℕ) : ℕ :=
  if c + 1 ≤ s then c else if s + m < c ∧ c < s + m + s then c - (s + m) else 0

lemma Xup_dvd_of_eq (s m i : ℕ) (c : ℚ) (h : (i : ℚ[X]) + 1 + X = X + C c ∨
    (i : ℚ[X]) + 1 + X + ((s + m : ℕ) : ℚ[X]) = X + C c) :
    (X + C c) ∣ Xup s m (X : ℚ[X]) i := by
  unfold Xup
  refine (dvd_neg.2 ?_).mul_right _
  rcases h with h | h
  · exact ((dvd_mul_of_dvd_right (dvd_of_eq h.symm) _).mul_right _).mul_right _
  · exact (dvd_mul_of_dvd_right (dvd_of_eq h.symm) _).mul_right _

theorem chain_dvd (s m c : ℕ) (hc : 1 ≤ c) :
    (X + C (c : ℚ)) ^ chainOrd s m c ∣
      ∏ j ∈ range s, (Xup s m (X : ℚ[X]) (s - 1 - (j + 1))) ^ (s - 1 - j) := by
  unfold chainOrd
  by_cases hA : c + 1 ≤ s
  · rw [if_pos hA]
    obtain ⟨i, rfl⟩ : ∃ i, c = i + 1 := ⟨c - 1, by omega⟩
    have hd : (X + C ((i + 1 : ℕ) : ℚ)) ∣ Xup s m (X : ℚ[X]) i :=
      Xup_dvd_of_eq s m i _ (Or.inl (by push_cast; simp; ring))
    have hmem : s - 2 - i ∈ range s := mem_range.2 (by omega)
    have e1 : s - 1 - (s - 2 - i + 1) = i := by omega
    have e2 : s - 1 - (s - 2 - i) = i + 1 := by omega
    refine dvd_trans ?_ (Finset.dvd_prod_of_mem _ hmem)
    rw [e1, e2]
    exact pow_dvd_pow_of_dvd hd _
  · rw [if_neg hA]
    by_cases hB : s + m < c ∧ c < s + m + s
    · rw [if_pos hB]
      obtain ⟨i, hi⟩ : ∃ i, c = s + m + i + 1 := ⟨c - (s + m) - 1, by omega⟩
      have hd : (X + C (c : ℚ)) ∣ Xup s m (X : ℚ[X]) i :=
        Xup_dvd_of_eq s m i _ (Or.inr (by rw [hi]; push_cast; simp; ring))
      have hmem : s - 2 - i ∈ range s := mem_range.2 (by omega)
      have e1 : s - 1 - (s - 2 - i + 1) = i := by omega
      have e2 : s - 1 - (s - 2 - i) = i + 1 := by omega
      have e3 : c - (s + m) = i + 1 := by omega
      refine dvd_trans ?_ (Finset.dvd_prod_of_mem _ hmem)
      rw [e1, e2, e3]
      exact pow_dvd_pow_of_dvd hd _
    · rw [if_neg hB, pow_zero]
      exact one_dvd _

end CatalanCore.Bordered.Z1
