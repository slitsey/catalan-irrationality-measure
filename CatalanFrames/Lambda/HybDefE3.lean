module

public import CatalanFrames.Lambda.HybDefE
public import CatalanCore.Arith.Hybrid.LemmaE.Class3M

@[expose] public section

/-!
# λ: E for the class `p ≡ 3 (4)` as a `DefHypT` family

Clean primes `5r/8 < p < 4r/5`, `p ≡ 3 (4)`, `p ≠ 139`.  Dual value `2r + m`; deficit `m`.
-/

open Finset CatalanCore CatalanCore.Basic CatalanCore.Arith CatalanCore.Arith.Hybrid
  CatalanCore.Arith.Hybrid.LemmaE

namespace CatalanFrames.Lambda

/-- Clean primes of class `3 (4)`. -/
def cleanE3 (r p : ℕ) : Prop :=
  p.Prime ∧ p % 4 = 3 ∧ 5 * r + 8 ≤ 8 * p ∧ 5 * p + 5 ≤ 4 * r ∧ p ≠ 139

lemma not_dvd_6255 {p : ℕ} (hp : p.Prime) (h7 : 7 ≤ p) (h139 : p ≠ 139) : ¬ p ∣ 6255 := by
  intro hd
  have h : (6255 : ℕ) = 3 * 3 * 5 * 139 := by norm_num
  rw [h] at hd
  rcases (Nat.Prime.dvd_mul hp).1 hd with h1 | h1
  · rcases (Nat.Prime.dvd_mul hp).1 h1 with h2 | h2
    · rcases (Nat.Prime.dvd_mul hp).1 h2 with h3 | h3
      · have := Nat.le_of_dvd (by norm_num) h3; omega
      · have := Nat.le_of_dvd (by norm_num) h3; omega
    · have := Nat.le_of_dvd (by norm_num) h2; omega
  · have := (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 139)).1 h1
    exact h139 this

lemma eSetup3_of_clean {r p : ℕ} (hp : p.Prime) (h4 : p % 4 = 3) (h8 : 5 * r + 8 ≤ 8 * p)
    (h5 : 5 * p + 5 ≤ 4 * r) (hr : 16 ≤ r) : ESetup3 1 p r (r / 8) ((p + 1) / 4) where
  p5 := by omega
  hp6 := by omega
  ho0 := by omega
  ho3 := by omega
  hk1 := by omega
  hpr := by omega
  hk2r := by omega
  hN := by omega

/-- **Lemma E (class 3) for λ**, in the form needed for `DefHypT`. -/
theorem gle_E3 {r p : ℕ} (hr : 16 ≤ r) (hc : cleanE3 r p) [Fact p.Prime] :
    GLE p (2 * r + r / 8 - r / 8) (lamFrame.fullPoly r (r / 8)) := by
  obtain ⟨hp, h4, h8, h5, h139⟩ := hc
  have S := eSetup3_of_clean hp h4 h8 h5 hr
  have h7 : 7 ≤ p := by omega
  have := gleAt_E3 S lamData (not_dvd_6255 hp h7 h139)
  rw [wrc_sum S] at this
  exact this

/-- The deficit family of class 3. -/
noncomputable def defE3 (r p : ℕ) : ℕ := by
  classical exact if cleanE3 r p then r / 8 else 0

theorem defHypT_E3 {r : ℕ} (hr : 16 ≤ r) (T : ℕ → ℕ)
    (hT : ∀ p, p.Prime → p < Bnd lamInst r (r / 8) → tropExp lamInst r (r / 8) p ≤ T p)
    (hTd : ∀ p, cleanE3 r p → 2 * r + r / 8 ≤ T p) :
    DefHypT lamInst r (r / 8) T (defE3 r) := by
  classical
  refine defHypT_of_local lamInst r (r / 8) T (defE3 r) hT (cleanE3 r) ?_ ?_
  · intro p hp; simp [defE3, hp]
  · intro p hp hb hc
    haveI : Fact p.Prime := ⟨hp⟩
    have hd := hTd p hc
    have hg := gle_E3 hr hc
    have e : defE3 r p = r / 8 := by simp [defE3, hc]
    rw [e]
    exact ⟨by omega, fun [Fact p.Prime] => hg.mono (by omega)⟩

end CatalanFrames.Lambda
