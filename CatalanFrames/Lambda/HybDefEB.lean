module

public import CatalanFrames.Lambda.HybDefE

@[expose] public section

/-!
# λ: B and E (class 1) together as one `DefHypT` family

`lam_defHypT`: for `r ≥ 16`, `m = r/8`, with `T p = max (tropExp p) (E-dual) (B-dual)`, the deficit
`δ p = m` on the class-1 clean primes `5r/7 < p < r` plus `δ p = m - (p - r)` on `r < p < r + m`.
-/

open Finset CatalanCore CatalanCore.Basic CatalanCore.Arith CatalanCore.Arith.Hybrid
  CatalanCore.Arith.Hybrid.LemmaE

namespace CatalanFrames.Lambda

/-- The singular block start `k` of Theorem B at the prime `p`. -/
def kB (p : ℕ) : ℕ := if p % 4 = 1 then (3 * p + 1) / 4 else (p + 1) / 4

/-- The dual value of the D4 potentials of Theorem B. -/
def dualB (r m p : ℕ) : ℕ :=
  ∑ a : Fin r ⊕ Fin m, uPot p r (kB p) (Frame.hybRow r m a) +
    ∑ b : Fin r ⊕ Fin m, uPot p r (kB p) (Frame.hybCol r m b)

/-- The window of Theorem B. -/
def WB (r p : ℕ) : Prop := p.Prime ∧ r < p ∧ p < r + r / 8

lemma bsetup_k {p r m j k : ℕ} (hp : p.Prime) (S : BSetup p r m j k) : k = kB p := by
  have hp5 := S.p5
  have hodd : p % 2 = 1 := by
    by_contra h
    have h2' : 2 ∣ p := by omega
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h2'
    omega
  have hk := S.hk
  have hkp := S.hkp
  have hj : j < 4 := by
    by_contra h
    have : 4 * p ≤ j * p := Nat.mul_le_mul_right p (by omega)
    omega
  have hj0 := S.hj0
  unfold kB
  interval_cases j <;> split_ifs <;> omega

lemma bsetup_of {p r : ℕ} (hr : 16 ≤ r) (hp : p.Prime) (h1 : r < p) (h2 : p < r + r / 8) :
    BSetup p r (r / 8) (if p % 4 = 1 then 3 else 1) (kB p) := by
  have hodd : p % 2 = 1 := by
    by_contra h
    have h2' : 2 ∣ p := by omega
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h2'
    omega
  unfold kB
  by_cases h4 : p % 4 = 1
  · simp only [if_pos h4]
    exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
      by omega⟩
  · simp only [if_neg h4]
    exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
      by omega⟩

/-- **B and E (class 1) for λ as a single `DefHypT` family.** -/
theorem lam_defHypT {r : ℕ} (hr : 16 ≤ r) :
    ∃ T δ : ℕ → ℕ, DefHypT lamInst r (r / 8) T δ ∧
      (∀ p, cleanE1 r p → δ p = r / 8) ∧ (∀ p, WB r p → δ p = r / 8 - (p - r)) := by
  classical
  set T : ℕ → ℕ := fun p => max (tropExp lamInst r (r / 8) p)
    (max (if cleanE1 r p then dualE1 r (r / 8) p else 0)
      (if WB r p then dualB r (r / 8) p else 0)) with hT
  have hT1 : ∀ p, p.Prime → p < Bnd lamInst r (r / 8) → tropExp lamInst r (r / 8) p ≤ T p :=
    fun p _ _ => le_max_left _ _
  have hE := defHypT_E1 r T hT1 (fun p hc => by
    simp only [hT]
    refine le_trans ?_ (le_max_right _ _)
    refine le_trans ?_ (le_max_left _ _)
    rw [if_pos hc])
  have hB := defHypT_B lamInst lamData r (r / 8) T (WB r) (fun p hp => hp.2.2)
    (fun p hp hW => ⟨_, _, bsetup_of hr hW.1 hW.2.1 hW.2.2⟩) hT1
    (fun p hp hW j k S => by
      rw [bsetup_k hW.1 S]
      simp only [hT]
      refine le_trans ?_ (le_max_right _ _)
      refine le_trans ?_ (le_max_right _ _)
      rw [if_pos hW]
      exact le_rfl)
  refine ⟨T, _, defHypT_add hE hB ?_, ?_, ?_⟩
  · intro p hp hb
    by_cases hc : cleanE1 r p
    · right
      have : ¬ WB r p := fun hw => by have := hc.2.2.2; have := hw.2.1; omega
      simp [this]
    · left; simp [defE1, hc]
  · intro p hc
    have : ¬ WB r p := fun hw => by have := hc.2.2.2; have := hw.2.1; omega
    simp [defE1, hc, this]
  · intro p hW
    have : ¬ cleanE1 r p := fun hc => by have := hc.2.2.2; have := hW.2.1; omega
    simp [defE1, this, hW]

end CatalanFrames.Lambda
