module

public import CatalanCore.Star.Leonard.ThetaZeroKgen
public import CatalanCore.Star.Leonard.KappaS
public import CatalanCore.Star.SumEc

/-!
# Interface for `kgen_LU`: the generic closed form gives the `ℓ`-unit at `θ = 0`

Assume the (Leonard-route) generic closed form
`kgen K m S θ = ± κ_S / ∏_{c=1}^{S+K+m-1} (θ+c)^{e_c}` for all rationals `0 < θ < 1`
(`e_c = ec K m S c` of `SumEc`).  Then at `θ = 0` the value is an `ℓ`-unit:
regularity (`ThetaZeroKgen`) + `kappaS_LU` + all bases `c ≤ S+K+m-1 < ℓ`.
The only missing input of the full `kgen_LU` is this generic closed form (H7 bookkeeping (B1)/(B2)).
-/

@[expose] public section

open Finset Filter Topology CatalanCore.ThmA

namespace CatalanCore.Star

open CatalanCore.Star.Leonard

/-- the GI closed form, with `ℤ`-valued exponents `ec` -/
noncomputable def Fclosed (K m S : ℕ) (θ : ℚ) : ℚ :=
  kappaS K m S / ∏ c ∈ Icc 1 (S + K + m - 1), (θ + (c : ℚ)) ^ (ec K m S (c : ℤ))

lemma LU_zpow {ℓ : ℕ} [Fact ℓ.Prime] {q : ℚ} (h : LU ℓ q) (z : ℤ) : LU ℓ (q ^ z) := by
  rcases Int.eq_nat_or_neg z with ⟨n, rfl | rfl⟩
  · simpa using h.pow n
  · simpa [zpow_neg] using (h.pow n).inv

theorem cA_Fclosed (K m S : ℕ) : ContinuousAt (Fclosed K m S) 0 := by
  unfold Fclosed
  refine continuousAt_const.div ?_ ?_
  · have : ContinuousAt (fun θ : ℚ => ∏ c ∈ Icc 1 (S + K + m - 1), (θ + (c : ℚ)) ^ (ec K m S (c : ℤ))) 0 := by
      apply tendsto_finset_prod
      intro c hc
      have hc1 := (Finset.mem_Icc.1 hc).1
      refine ContinuousAt.tendsto ?_
      refine ContinuousAt.zpow₀ (by fun_prop) _ (Or.inl ?_)
      simp only [zero_add]; exact_mod_cast (by omega : c ≠ 0)
    exact this
  · refine Finset.prod_ne_zero_iff.2 fun c hc => ?_
    have hc1 := (Finset.mem_Icc.1 hc).1
    refine zpow_ne_zero _ ?_
    simp only [zero_add]; exact_mod_cast (by omega : c ≠ 0)

theorem Fclosed_zero_LU {ℓ : ℕ} [Fact ℓ.Prime] (K m S : ℕ) (hmK : m < K) (hS : K - m ≤ S)
    (hl : S + K + 2 * m ≤ ℓ) : LU ℓ (Fclosed K m S 0) := by
  unfold Fclosed
  refine LU.div (kappaS_LU K m S hmK hS hl) ?_
  refine LU.prod _ _ fun c hc => ?_
  have hc' := Finset.mem_Icc.1 hc
  refine LU_zpow ?_ _
  simp only [zero_add]
  exact LU_natCast_lt (by omega) (by omega)

/-- **`kgen_LU` modulo the generic closed form.** -/
theorem kgen_LU_of_formula {ℓ : ℕ} [Fact ℓ.Prime] (K m S : ℕ) (hmK : m < K) (hS : K - m ≤ S)
    (hl : S + K + 2 * m ≤ ℓ) (σ : ℚ) (hσ : σ = 1 ∨ σ = -1)
    (hgen : ∀ θ : ℚ, 0 < θ → θ < 1 → kgen K m S θ = σ * Fclosed K m S θ) :
    LU ℓ (kgen K m S (0 : ℚ)) := by
  have h0 := kgenR_zero_of_generic K m S (by omega) (by omega) (by omega)
    (fun θ => σ * Fclosed K m S θ) (continuousAt_const.mul (cA_Fclosed K m S)) hgen
  rw [h0]
  have hσ' : LU ℓ σ := by rcases hσ with rfl | rfl; exact LU.one; exact LU.one.neg
  exact hσ'.mul (Fclosed_zero_LU K m S hmK hS hl)

end CatalanCore.Star
