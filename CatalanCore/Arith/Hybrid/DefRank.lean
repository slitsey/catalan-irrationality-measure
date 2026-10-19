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


/-! ### Deficits relative to a dual value `T ≥ tropExp`

The rank principle bounds `det Full` by the *dual* value `τ' = ∑u + ∑v ≥ tropExp` (weak duality).
Stating the deficit relative to any `T p` (e.g. the dual value of the potentials used in the
upper-bound tables) avoids the primal-optimality statement `tropExp ≥ τ'`.  This is
`DefHyp` with `tropExp` replaced by `T`; it carries the same integrality and log formulas. -/

/-- A deficit family relative to an exponent function `T`. -/
def DefHypT (T δ : ℕ → ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p < Bnd I r m →
    δ p ≤ T p ∧ ∀ [Fact p.Prime], GLE p (T p - δ p) (Fr.fullPoly r m)

/-- The denominator `∏_{p < Bnd} p^{T p - δ p}`. -/
noncomputable def DhybT (T δ : ℕ → ℕ) : ℕ :=
  ∏ p ∈ (Finset.range (Bnd I r m)).filter Nat.Prime, p ^ (T p - δ p)

/-- Integrality of `DhybT T δ · det Full(X)`. -/
theorem DhybT_integral {T δ : ℕ → ℕ} (hδ : DefHypT I r m T δ) (i : ℕ) :
    ∃ z : ℤ, (DhybT I r m T δ : ℚ) * (Fr.fullPoly r m).coeff i = z := by
  apply int_of_forall_locRing
  intro p hp
  by_cases hb : p < Bnd I r m
  · have hmem : p ∈ (Finset.range (Bnd I r m)).filter Nat.Prime :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hb, hp.out⟩
    have hgle := (hδ p hp.out hb).2 i
    have hD : (DhybT I r m T δ : ℚ) = (p : ℚ) ^ (T p - δ p) *
        ((∏ q ∈ ((Finset.range (Bnd I r m)).filter Nat.Prime).erase p,
          q ^ (T q - δ q) : ℕ) : ℚ) := by
      unfold DhybT
      rw [← Nat.cast_pow, ← Nat.cast_mul,
        Finset.mul_prod_erase _ (fun q => q ^ (T q - δ q)) hmem]
    rw [hD]
    have hR := int_mem_locRing (ℓ := p)
      ((∏ q ∈ ((Finset.range (Bnd I r m)).filter Nat.Prime).erase p,
          q ^ (T q - δ q) : ℕ) : ℤ)
    have := (LocRing p).mul_mem hgle (by simpa using hR)
    convert this using 1; push_cast; ring
  · have h0 := tropExp_eq_zero I r m p hp.out (by omega)
    have hgle := fullPoly_gle I p r m i
    rw [h0] at hgle
    simp only [pow_zero, one_mul] at hgle
    rw [mul_comm]
    exact (LocRing p).mul_mem hgle (by exact_mod_cast int_mem_locRing (ℓ := p) (DhybT I r m T δ : ℤ))

lemma log_DhybT {T δ : ℕ → ℕ} (hδ : DefHypT I r m T δ) :
    Real.log (DhybT I r m T δ) =
      ∑ p ∈ (Finset.range (Bnd I r m)).filter Nat.Prime, (T p : ℝ) * Real.log p -
      ∑ p ∈ (Finset.range (Bnd I r m)).filter Nat.Prime, (δ p : ℝ) * Real.log p := by
  unfold DhybT
  rw [Nat.cast_prod, Real.log_prod, ← Finset.sum_sub_distrib]
  · apply Finset.sum_congr rfl
    intro p hp
    have hh := hδ p (Finset.mem_filter.mp hp).2 (Finset.mem_range.mp (Finset.mem_filter.mp hp).1)
    rw [Nat.cast_pow, Real.log_pow, Nat.cast_sub hh.1]; ring
  · intro p hp
    have := (Finset.mem_filter.mp hp).2.pos
    positivity

/-- A `DefHyp` family is a `DefHypT` family with `T = tropExp`. -/
lemma DefHyp.toT {δ : ℕ → ℕ} (h : DefHyp I r m δ) : DefHypT I r m (tropExp I r m) δ := h

/-- Assemble a `DefHypT` family from local conclusions. -/
theorem defHypT_of_local (T δ : ℕ → ℕ) (hT : ∀ p, p.Prime → p < Bnd I r m → tropExp I r m p ≤ T p)
    (S : ℕ → Prop) (hδ : ∀ p, ¬ S p → δ p = 0)
    (hS : ∀ p : ℕ, p.Prime → p < Bnd I r m → S p →
      δ p ≤ T p ∧ ∀ [Fact p.Prime], GLE p (T p - δ p) (Fr.fullPoly r m)) :
    DefHypT I r m T δ := by
  intro p hp hb
  by_cases h : S p
  · exact hS p hp hb h
  · rw [hδ p h]
    refine ⟨Nat.zero_le _, fun [Fact p.Prime] => ?_⟩
    simpa using (fullPoly_gle I p r m).mono (hT p hp hb)

end CatalanCore.Arith.Hybrid
