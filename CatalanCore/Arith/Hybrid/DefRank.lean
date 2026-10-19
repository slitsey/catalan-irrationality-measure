module

public import CatalanCore.Arith.Hybrid.RankGLE
public import CatalanCore.Arith.Hybrid.Deficit

@[expose] public section

/-!
# From a rank bound at one prime to the additive deficit interface (`DefHyp`)

* `defAt_of_rank` : at a prime `p`, integral weights `(u, v)` that are tropically optimal
  (`∑u + ∑v ≤ tropExp p`) and a reduction `B̄` of the scaled matrix of rank `≤ r + m - k` give
  `k ≤ tropExp p ∧ GLE p (tropExp p - k) fullPoly`, the per-prime conclusion of `DefHyp` with
  `δ p = k` (assuming `k ≤ ∑u + ∑v`).
* `defHyp_of_local` : a deficit that is `0` outside a set `S` of primes and given by the local
  conclusion on `S` is a `DefHyp` family.
-/

open Polynomial CatalanCore.Basic

namespace CatalanCore.Arith.Hybrid

variable {Fr : Frame} (I : HybInst Fr) (r m : ℕ)

/-- Per-prime rank principle for `Full`, in the form of the `DefHyp` conclusion. -/
theorem defAt_of_rank (p : ℕ) [Fact p.Prime] (u v : Fin r ⊕ Fin m → ℕ)
    (hopt : ∑ a, u a + ∑ b, v b ≤ tropExp I r m p)
    (Bbar : Matrix (Fin r ⊕ Fin m) (Fin r ⊕ Fin m) (RatFunc (ZMod p)))
    (hB : ∀ a b, ∃ g : (LocRing p)[X],
      toQ p g = C ((p : ℚ) ^ (u a + v b)) * fullEntry Fr r m a b ∧ phiP p g = Bbar a b)
    (k : ℕ) (hk : k ≤ ∑ a, u a + ∑ b, v b) (hrk : Bbar.rank + k ≤ r + m) :
    k ≤ tropExp I r m p ∧ GLE p (tropExp I r m p - k) (Fr.fullPoly r m) := by
  refine ⟨hk.trans hopt, ?_⟩
  have := gle_full_of_rank p Fr r m u v Bbar hB k hrk
  exact this.mono (by omega)

/-- Assemble a `DefHyp` family from local conclusions on a set `S` of primes. -/
theorem defHyp_of_local (δ : ℕ → ℕ) (S : ℕ → Prop) (hδ : ∀ p, ¬ S p → δ p = 0)
    (hS : ∀ p : ℕ, p.Prime → p < Bnd I r m → S p →
      δ p ≤ tropExp I r m p ∧ ∀ [Fact p.Prime], GLE p (tropExp I r m p - δ p) (Fr.fullPoly r m)) :
    DefHyp I r m δ := by
  intro p hp hb
  by_cases h : S p
  · exact hS p hp hb h
  · rw [hδ p h]
    refine ⟨Nat.zero_le _, fun [Fact p.Prime] => ?_⟩
    simpa using fullPoly_gle I p r m

end CatalanCore.Arith.Hybrid
