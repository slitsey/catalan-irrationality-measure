module

public import CatalanFrames.Lambda.HybLemmaE2
public import CatalanFrames.Lambda.HybInst
public import CatalanCore.Arith.Hybrid.LemmaE.Summation

@[expose] public section

/-!
# λ: the additive deficits E (class `p ≡ 1 (4)`) and B as `DefHypT` families

For `m = r/8` and any `T ≥ tropExp` that dominates the dual values of the E and B potentials:

* `defHypT_E1`: deficit `m` at the primes `5r/7 < p < r`, `p ≡ 1 (4)` (rank route, `gleAt_E_lam`);
* `defHypT_B_lam`: deficit `m - (p - r)` at the primes `r < p < r + m`;
* `defHypT_add`: deficits with disjoint supports add;
* `lam_defHypT`: both, with the explicit `T`.
-/

open Finset CatalanCore CatalanCore.Basic CatalanCore.Arith CatalanCore.Arith.Hybrid
  CatalanCore.Arith.Hybrid.LemmaE

namespace CatalanFrames.Lambda

/-- Clean primes of class `1 (4)`: `5r/7 < p < r` (with a margin of `8/7`). -/
def cleanE1 (r p : ℕ) : Prop := p.Prime ∧ p % 4 = 1 ∧ 5 * r + 8 ≤ 7 * p ∧ p < r

/-- The dual value of the E-potentials, `∑u + ∑v = 2 (2r - p - k) + 4m`, `k = (3p+1)/4`. -/
def dualE1 (r m p : ℕ) : ℕ := 2 * ((r - p) + (r - (3 * p + 1) / 4)) + 4 * m

lemma eSetup_of_clean {r p : ℕ} (hp : p.Prime) (h4 : p % 4 = 1) (h7 : 5 * r + 8 ≤ 7 * p)
    (hpr : p < r) : ESetup 1 p r (r / 8) 3 ((3 * p + 1) / 4) where
  p5 := by omega
  ho0 := by omega
  ho3 := by omega
  hk := by omega
  hj0 := by norm_num
  hjp := by omega
  hk0 := by omega
  hkp := by omega
  hpr := hpr
  hrk := by omega
  hN := by omega

/-- **Lemma E (class 1) for λ**, in the form needed for `DefHypT`. -/
theorem gle_E1 {r p : ℕ} (hc : cleanE1 r p) [Fact p.Prime] :
    GLE p (dualE1 r (r / 8) p - r / 8) (lamFrame.fullPoly r (r / 8)) := by
  obtain ⟨hp, h4, h7, hpr⟩ := hc
  have S := eSetup_of_clean hp h4 h7 hpr
  have := gleAt_E_lam S
  unfold dualE1
  convert this using 2

/-- The deficit family of class 1. -/
noncomputable def defE1 (r p : ℕ) : ℕ := by
  classical exact if cleanE1 r p then r / 8 else 0

/-- Disjoint supports add. -/
lemma defHypT_add {Fr : Frame} {I : HybInst Fr} {r m : ℕ} {T δ₁ δ₂ : ℕ → ℕ}
    (h1 : DefHypT I r m T δ₁) (h2 : DefHypT I r m T δ₂)
    (hdisj : ∀ p, p.Prime → p < Bnd I r m → δ₁ p = 0 ∨ δ₂ p = 0) :
    DefHypT I r m T (fun p => δ₁ p + δ₂ p) := by
  intro p hp hb
  rcases hdisj p hp hb with h | h
  · simp only [h, zero_add]; exact h2 p hp hb
  · simp only [h, add_zero]; exact h1 p hp hb

/-- **E (class 1) as a `DefHypT` family.** `T` is any exponent bound dominating `tropExp` and the
dual value `dualE1` on the clean primes. -/
theorem defHypT_E1 (r : ℕ) (T : ℕ → ℕ)
    (hT : ∀ p, p.Prime → p < Bnd lamInst r (r / 8) → tropExp lamInst r (r / 8) p ≤ T p)
    (hTd : ∀ p, cleanE1 r p → dualE1 r (r / 8) p ≤ T p) :
    DefHypT lamInst r (r / 8) T (defE1 r) := by
  classical
  refine defHypT_of_local lamInst r (r / 8) T (defE1 r) hT (cleanE1 r) ?_ ?_
  · intro p hp; simp [defE1, hp]
  · intro p hp hb hc
    haveI : Fact p.Prime := ⟨hp⟩
    have hd := hTd p hc
    have h1 : r / 8 ≤ dualE1 r (r / 8) p := by unfold dualE1; omega
    have hg := gle_E1 hc
    have e : defE1 r p = r / 8 := by simp [defE1, hc]
    rw [e]
    exact ⟨by omega, fun [Fact p.Prime] => hg.mono (by omega)⟩

end CatalanFrames.Lambda
