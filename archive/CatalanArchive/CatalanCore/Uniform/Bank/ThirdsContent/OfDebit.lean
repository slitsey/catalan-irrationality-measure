import CatalanCore.Uniform.Bank.ThirdsContent.NoUF
import CatalanCore.Uniform.Content.SmallPrimes.Layers
set_option Elab.async false

/-! # Thirds content from a list of debit layers (lane B, B4b)

`thirds_content_of_debitLayers`: the budgeted-limit content statement on the even-scale thirds
family, from a layer list `L : Fin (k+1) → DebitLayer G310 Fr depth` (layer `0` global, e.g. the
crude tropical layer; the rest `[M3D, LP1, LP2, rank] ++ extra`, where UF is just one more entry, so
adding it later changes no statement) and epsilon-templates.  Exceptional primes are discharged
(`thirds_content_of_layers`): nothing is assumed at primes dividing `M`.  The constant `Lam` is a
parameter (`LamT0` no-UF, `LamT` with UF). -/

namespace CatalanCore.Uniform.Bank.ThirdsContent
open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Bank.Thirds CatalanCore.Uniform.Content.Shape
  CatalanCore.Uniform.Content.BankShared CatalanCore.Uniform.Content.SmallPrimes
  CatalanCore.Uniform.Content.Member CatalanCore.Arith.Hybrid CatalanCore.Basic Filter Finset

theorem thirds_content_of_debitLayers (Fr : Frame) (depth : ℕ) (M : ℕ) [NeZero M] (Lam : ℝ)
    {k : ℕ} (L : Fin (k + 1) → DebitLayer G310 Fr depth) (h0 : ∀ r p, (L 0).valid r p)
    (B : SmallBudget) (tmpl : ℝ → ZMod M → Template) (τ : ℝ)
    (hmass : ∀ ε : ℝ, 0 < ε → contentConstant M (tmpl ε) ≤ Lam + ε)
    (tend_le : ∀ ε : ℝ, 0 < ε → ∀ c : ZMod M, IsUnit c → (tmpl ε c).tend ≤ τ)
    (tail : ∀ ε : ℝ, 0 < ε → ∀ r : ℕ, r % 2 = 0 → ∀ c : ZMod M, IsUnit c → ∀ p : ℕ, p.Prime →
      (p : ZMod M) = c → ⌊(tmpl ε c).tend * r⌋₊ < p → ∃ j, (L j).valid r p ∧ (L j).eff r p = 0)
    (pre : ∀ ε : ℝ, 0 < ε → ∀ r : ℕ, r % 2 = 0 → ∀ c : ZMod M, IsUnit c → ∀ p : ℕ,
      p ≤ ⌊(tmpl ε c).t1 * r⌋₊ → p.Prime → (p : ZMod M) = c →
        ∃ j, (L j).valid r p ∧ (((L j).eff r p : ℕ) : ℝ) ≤ (tmpl ε c).α0 * r + B.X r p)
    (cov : ∀ ε : ℝ, 0 < ε → ∀ r : ℕ, r % 2 = 0 → ∀ c : ZMod M, IsUnit c → ∀ Q ∈ (tmpl ε c).l,
      ∀ p : ℕ, ⌊Q.s * r⌋₊ < p → p ≤ ⌊Q.t * r⌋₊ → p.Prime → (p : ZMod M) = c →
        ∃ j, (L j).valid r p ∧ (((L j).eff r p : ℕ) : ℝ) ≤ Q.α * r + Q.β * p + Q.C) :
    HasScaledContent (FamE Fr depth) G310.scale Lam := by
  classical
  let w : Fin (k + 1) → (FamE Fr depth).ι → ℕ → ℕ := fun j i p =>
    if (L j).valid i.1 p then (L j).base i.1 p + (L j).debit * delCount G310 i
    else (L 0).base i.1 p + (L 0).debit * delCount G310 i
  have hw_le : ∀ j (i : (FamE Fr depth).ι), (FamE Fr depth).Adm i → ∀ p,
      (L j).valid i.1 p → w j i p ≤ (L j).eff i.1 p := by
    intro j i hi p hv
    have hd := delCount_le G310 Fr depth i hi.1
    simp only [w, if_pos hv, DebitLayer.eff]
    exact Nat.add_le_add_left (Nat.mul_le_mul_left _ hd) _
  have hw_real : ∀ j (i : (FamE Fr depth).ι), (FamE Fr depth).Adm i → ∀ p,
      (L j).valid i.1 p → (w j i p : ℝ) ≤ (((L j).eff i.1 p : ℕ) : ℝ) := by
    intro j i hi p hv
    exact_mod_cast hw_le j i hi p hv
  refine thirds_content_of_layers Fr depth M Lam (fun i p => layerMin (fun j => w j i p))
    (fun i => ⌊τ * i.1⌋₊ + 1) ?_ ?_ B tmpl hmass ?_ ?_ ?_ ?_
  · intro i hi p _ _
    refine gle_layerMin (fun j => ?_)
    by_cases hv : (L j).valid i.1 p
    · simp only [w, if_pos hv]; exact (L j).gle i hi.1 p hv
    · simp only [w, if_neg hv]; exact (L 0).gle i hi.1 p (h0 _ _)
  · intro i hi p hp hM hc
    have hunit : IsUnit (p : ZMod M) := (ZMod.isUnit_prime_iff_not_dvd hp).2 hM
    have hlt : ⌊(tmpl 1 (p : ZMod M)).tend * i.1⌋₊ < p := by
      have : ⌊(tmpl 1 (p : ZMod M)).tend * i.1⌋₊ ≤ ⌊τ * i.1⌋₊ :=
        Nat.floor_le_floor (mul_le_mul_of_nonneg_right (tend_le 1 one_pos _ hunit)
          (Nat.cast_nonneg _))
      omega
    obtain ⟨j, hv, he⟩ := tail 1 one_pos i.1 hi.2 _ hunit p hp rfl hlt
    exact layerMin_eq_zero_of_exists ⟨j, Nat.le_zero.1 (he ▸ hw_le j i hi p hv)⟩
  · intro ε hε i hi c hc p hp hpc hlt
    obtain ⟨j, hv, he⟩ := tail ε hε i.1 hi.2 c hc p hp hpc hlt
    exact layerMin_eq_zero_of_exists ⟨j, Nat.le_zero.1 (he ▸ hw_le j i hi p hv)⟩
  · intro ε hε i hi c hc
    have : ⌊(tmpl ε c).tend * i.1⌋₊ ≤ ⌊τ * i.1⌋₊ :=
      Nat.floor_le_floor (mul_le_mul_of_nonneg_right (tend_le ε hε c hc) (Nat.cast_nonneg _))
    show ⌊(tmpl ε c).tend * (i.1 : ℝ)⌋₊ < ⌊τ * i.1⌋₊ + 1
    omega
  · intro ε hε i hi c hc p h1 hp hpc
    obtain ⟨j, hv, he⟩ := pre ε hε i.1 hi.2 c hc p h1 hp hpc
    exact layerMin_le_of_exists ⟨j, (hw_real j i hi p hv).trans he⟩
  · intro ε hε i hi c hc P hP p h1 h2 hp hpc
    obtain ⟨j, hv, he⟩ := cov ε hε i.1 hi.2 c hc P hP p h1 h2 hp hpc
    exact layerMin_le_of_exists ⟨j, (hw_real j i hi p hv).trans he⟩

end CatalanCore.Uniform.Bank.ThirdsContent
