module

public import CatalanCore.Star.Leonard.KgenLU
public import CatalanCore.Star.Leonard.HnUnit
public import CatalanCore.Star.Pencil

/-!
# `kgenL` at `θ = 0`: `ℓ`-unit from the generic closed form of `kgenR`

At generic `θ`, `cSR^n · kgenL = cSL^n · kgenR` (`kgenL_mul_cSR`), so `kgenL = (cSL/cSR)^n kgenR`.
The ratio `cSL/cSR = Π_Y(S)/Π_X(S)` at `θ = 0` is a ratio of products of integers `≤ 2m`.
-/

@[expose] public section

open Finset Matrix Filter Topology CatalanCore.ThmA

namespace CatalanCore.Star

open CatalanCore.Star.Leonard

lemma Delta_ne_zero_genP (K m S : ℕ) (θ : ℚ) (hθ : GenP θ) (hK : 1 ≤ K) (hmK : m ≤ K) :
    ((Wb K θ (bX m (S : ℤ)))ᵀ * Wb K θ (bY m (S : ℤ))).det ≠ 0 := by
  obtain ⟨ℓ, hℓ, hprime⟩ := Nat.exists_infinite_primes (S + K + 2 * m)
  haveI : Fact ℓ.Prime := ⟨hprime⟩
  rw [Delta_closed K m S θ hθ hmK]
  have hx := LU_Vprod (ℓ := ℓ) (θ + (S : ℚ) + 2) m (by omega) (xsθ (θ + (S : ℚ)) m)
    (fun j => by simp only [xsθ])
  have hy := LU_Vprod (ℓ := ℓ) (θ + (S : ℚ) + 1) m (by omega) (ysθ (θ + (S : ℚ)) m)
    (fun j => by simp only [ysθ])
  have hH : LU ℓ (Hunif ℚ K m) := by
    rw [Hunif_eq_hkH K m hK]
    exact CatalanCore.Bordered.Hankel.LU_hkH ℓ m 0 0 (K - 1) (by omega) (by omega)
  have hD : Dpair (θ + (S : ℚ)) K m ≠ 0 := by
    unfold Dpair
    refine Finset.prod_ne_zero_iff.2 fun i hi => mul_ne_zero ?_ ?_
    · refine pochr_ne_zero _ _ fun t ht => ?_
      have := hθ ((S : ℤ) + 1 + i + t) (by omega); push_cast at this
      intro h; apply this; linear_combination h
    · refine pochr_ne_zero _ _ fun t ht => ?_
      have := hθ ((S : ℤ) + K + 1 + i + t) (by omega); push_cast at this
      intro h; apply this; linear_combination h
  exact mul_ne_zero (mul_ne_zero hx.1 hy.1) (div_ne_zero hH.1 hD)

lemma Hn_isUnit_K (K m S : ℕ) (hmK : m ≤ K) (θ : ℚ) (hθ : Gen θ)
    (hΔ : IsUnit ((Wb K θ (bX m (S : ℤ)))ᵀ * Wb K θ (bY m (S : ℤ))).det) :
    IsUnit (Hn K m S (K - m) θ).det := by
  obtain ⟨n, rfl⟩ : ∃ n, K = m + n := ⟨K - m, by omega⟩
  have := Hn_isUnit m n S θ hθ hΔ
  rwa [show m + n - m = n by omega]

/-- generic relation between `kgenL` and `kgenR` -/
theorem kgenL_generic (K m S : ℕ) (hmK : m < K) (hS : 1 ≤ S) (θ : ℚ) (h0 : 0 < θ) (h1 : θ < 1) :
    cSR K m S θ ^ (K - m) * kgenL K m θ (Finset.Icc 1 ((S : ℤ) - 1)) S =
      cSL K m S θ ^ (K - m) * kgen K m S θ := by
  have hθ : Gen θ := gen_of_small h0 h1
  have hΔ : IsUnit ((Wb K θ (bX m (S : ℤ)))ᵀ * Wb K θ (bY m (S : ℤ))).det :=
    isUnit_iff_ne_zero.2 (Delta_ne_zero_genP K m S θ hθ.genP (by omega) hmK.le)
  have key : ∀ (a : Fin K) (z : ℤ), θ + ((a : ℕ) : ℚ) + (z : ℚ) ≠ 0 := fun a z => gen_add hθ a z
  exact kgenL_mul_cSR θ (Finset.Icc 1 ((S : ℤ) - 1)) S hmK.le
    (fun a b h => Fin.ext (Nat.cast_injective h)) (fun j _ a => key a j)
    (fun a => by simpa using key a (S : ℤ)) (fun i a => key a _) (fun i a => key a _) hΔ
    (Hn_isUnit_K K m S hmK.le θ hθ hΔ)

lemma prodAS_ne (K S : ℕ) (hS : 1 ≤ S) (θ : ℚ) (hθ : 0 ≤ θ) :
    ∏ a : Fin K, (θ + ((a : ℕ) : ℚ) + (S : ℚ)) ≠ 0 := by
  refine Finset.prod_ne_zero_iff.2 fun a _ => ?_
  have : (1 : ℚ) ≤ S := by exact_mod_cast hS
  have : (0 : ℚ) ≤ ((a : ℕ) : ℚ) := Nat.cast_nonneg _
  positivity

lemma cA_cS (K m S : ℕ) (hS : 1 ≤ S) (b : Fin m → ℤ) :
    ContinuousAt (fun θ : ℚ => piB b (S : ℚ) / ∏ a : Fin K, (θ + ((a : ℕ) : ℚ) + (S : ℚ))) 0 := by
  refine continuousAt_const.div ?_ (by simpa using prodAS_ne K S hS 0 le_rfl)
  exact (continuous_finset_prod _ fun a _ => by fun_prop).continuousAt

lemma piB_ne (m S : ℕ) (b : Fin m → ℤ) (hb : ∀ i, b i ≠ (S : ℤ)) : piB b (S : ℚ) ≠ 0 := by
  refine Finset.prod_ne_zero_iff.2 fun i _ => ?_
  intro h
  apply hb i
  have : (S : ℚ) = ((b i : ℤ) : ℚ) := by linear_combination h
  exact_mod_cast this.symm

lemma LU_piB {ℓ : ℕ} [Fact ℓ.Prime] (m S : ℕ) (b : Fin m → ℤ) (hb : ∀ i, 1 ≤ (b i - (S : ℤ)).natAbs ∧
    (b i - (S : ℤ)).natAbs < ℓ) : LU ℓ (piB b (S : ℚ)) := by
  refine LU.prod _ _ fun i _ => ?_
  have h := LU_intCast_lt (l := ℓ) (z := (S : ℤ) - b i) (by have := (hb i).1; omega)
    (by have := (hb i).2; omega)
  simpa using h

/-- **`kgenL_LU` modulo the generic closed form of `kgenR`.** -/
theorem kgenL_LU_of_formula {ℓ : ℕ} [Fact ℓ.Prime] (K m S : ℕ) (hmK : m < K) (hS : K - m ≤ S)
    (hl : S + K + 2 * m ≤ ℓ) (σ : ℚ) (hσ : σ = 1 ∨ σ = -1)
    (hgen : ∀ θ : ℚ, 0 < θ → θ < 1 → kgen K m S θ = σ * Fclosed K m S θ) :
    LU ℓ (kgenL K m (0 : ℚ) (Finset.Icc 1 ((S : ℤ) - 1)) S) := by
  have hS1 : 1 ≤ S := by omega
  have hX : piB (bX m S) (S : ℚ) ≠ 0 := piB_ne m S _ (fun i => by simp only [bX]; omega)
  have hcont : ContinuousAt (fun θ : ℚ => (cSL K m S θ / cSR K m S θ) ^ (K - m) *
      (σ * Fclosed K m S θ)) 0 := by
    refine ContinuousAt.mul (ContinuousAt.pow (ContinuousAt.div (cA_cS K m S hS1 _)
      (cA_cS K m S hS1 _) ?_) _) (continuousAt_const.mul (cA_Fclosed K m S))
    show piB (bX m S) (S : ℚ) / ∏ a : Fin K, ((0 : ℚ) + ((a : ℕ) : ℚ) + (S : ℚ)) ≠ 0
    exact div_ne_zero hX (by simpa using prodAS_ne K S hS1 0 le_rfl)
  have h0 := kgenL_zero_of_generic K m S (by omega) hmK.le hS1
    (fun θ => (cSL K m S θ / cSR K m S θ) ^ (K - m) * (σ * Fclosed K m S θ)) hcont (by
      intro θ h0 h1
      have hR := kgenL_generic K m S hmK hS1 θ h0 h1
      have hcR : cSR K m S θ ≠ 0 := by
        simp only [cSR]
        exact div_ne_zero hX (prodAS_ne K S hS1 θ h0.le)
      rw [← hgen θ h0 h1]
      have hpow : cSR K m S θ ^ (K - m) ≠ 0 := pow_ne_zero _ hcR
      rw [div_pow, div_mul_eq_mul_div, eq_div_iff hpow]
      linear_combination hR)
  rw [h0]
  simp only [cSL, cSR, zero_add]
  have hP : ∏ a : Fin K, ((0 : ℚ) + ((a : ℕ) : ℚ) + (S : ℚ)) ≠ 0 := by simpa using prodAS_ne K S hS1 0 le_rfl
  have hY : LU ℓ (piB (bY m S) (S : ℚ)) := LU_piB m S _ (fun i => by
    have := i.2; simp only [bY]; omega)
  have hXl : LU ℓ (piB (bX m S) (S : ℚ)) := LU_piB m S _ (fun i => by
    have := i.2; simp only [bX]; omega)
  have hq : (piB (bY m S) (S : ℚ) / ∏ a : Fin K, ((0 : ℚ) + ((a : ℕ) : ℚ) + (S : ℚ))) /
      (piB (bX m S) (S : ℚ) / ∏ a : Fin K, ((0 : ℚ) + ((a : ℕ) : ℚ) + (S : ℚ))) =
      piB (bY m S) (S : ℚ) / piB (bX m S) (S : ℚ) := by
    field_simp
  simp only [zero_add] at hq hP ⊢
  rw [hq]
  have hσ' : LU ℓ σ := by rcases hσ with rfl | rfl; exact LU.one; exact LU.one.neg
  exact ((hY.div hXl).pow _).mul (hσ'.mul (Fclosed_zero_LU K m S hmK hS hl))

end CatalanCore.Star
