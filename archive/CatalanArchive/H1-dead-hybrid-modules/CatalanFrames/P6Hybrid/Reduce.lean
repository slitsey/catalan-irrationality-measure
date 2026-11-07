module

public import CatalanFrames.P6Hybrid.Level

@[expose] public section

/-!
# P6 hybrid content: reduction to the per-prime weight and the piece summation

`p6_log_Dhyb_le` is `log_Dhyb_le_gen (p6_badInfo r m)` with modulus `6`, classes `{1, 5}`: no
`LevelFacts` or `HybParams` (the exact level has no `high` property).  `p6_content_of_pieces` reduces
`P6ContentStmt` (HH's `Λ = 10339/3072`, member 1) to the per-prime weights and the piece sums (`Pieces.lean`)

  `∀ ε > 0, ∀ᶠ r, ∑_{c ∈ {1,5}} clsSum 6 c (w r) 0 (R r c) ≤ (10339/3072 + ε) r²`

for per-prime weights `w r ≥ tropVal (HW (p6Inst r (mf r)).lev p r (mf r))` that vanish above `R r c`
(the Z-regime dual count with `p6_lev_zero_low`, `p6_lev_zero_win`, the H-dual `val_D1x`, and the piece
sums); these are discharged in `Pieces.lean` (`p6_content`).
-/

open Finset Filter CatalanCore CatalanCore.Arith CatalanCore.Arith.Hybrid CatalanFrames.HybCommon
  CatalanFrames.P6

namespace CatalanFrames.P6Hybrid

/-- good primes are `1, 5 (mod 6)` -/
lemma p6_cls (r m p : ℕ) (hp : p.Prime) (hb : p ∉ (p6Inst r m).cd.bad) :
    (p : ZMod 6) ∈ ({1, 5} : Finset (ZMod 6)) := by
  have hb' : p ∉ ({2, 3} : Finset ℕ) := hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb'
  have h2 : ¬ 2 ∣ p := fun h => hb' (Or.inl ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h).symm)
  have h3 : ¬ 3 ∣ p := fun h => hb' (Or.inr ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h).symm)
  have hq : p % 6 = 1 ∨ p % 6 = 5 := by omega
  rw [← ZMod.natCast_mod p 6]
  rcases hq with h | h <;> rw [h] <;> simp <;> decide

/-- **`log Dhyb` for P6**, from the per-prime weight `w` (generic numerology). -/
theorem p6_log_Dhyb_le (R : ZMod 6 → ℕ) (r m : ℕ) (hr : 1 ≤ r) (w : ℕ → ℝ) (hw0 : ∀ p, 0 ≤ w p)
    (hw : ∀ p, p.Prime → (tropVal (HW (p6Inst r m).lev p r m) : ℝ) ≤ w p)
    (ht : ∀ c ∈ ({1, 5} : Finset (ZMod 6)), ∀ p, p.Prime → p ∉ (p6Inst r m).cd.bad →
      (p : ZMod 6) = c → R c < p → w p = 0) :
    Real.log (Dhyb (p6Inst r m) r m) ≤
      extraG 3 Ecub 2 (badLog (p6Inst r m)) r m +
        ∑ c ∈ ({1, 5} : Finset (ZMod 6)), clsSum 6 c w 0 (R c) := by
  refine log_Dhyb_le_gen (p6_badInfo r m) (M := 6) ({1, 5} : Finset (ZMod 6)) R r m hr w hw0 hw
    (fun p hp hb => p6_cls r m p hp hb) ?_ ht
  intro c hc b hb hbc
  have hb' : b ∈ ({2, 3} : Finset ℕ) := hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb' hc
  rcases hb' with rfl | rfl <;> rcases hc with rfl | rfl <;> exact absurd hbc (by decide)

/-- The integrality `Dhyb · det Full(X) ∈ ℤ[X]` for the P6 instance (diagonal set `p6dok`). -/
theorem p6_Dhyb_integral (r m i : ℕ) :
    ∃ z : ℤ, (Dhyb (p6Inst r m) r m : ℚ) * (p6Frame.fullPoly r m).coeff i = z :=
  Dhyb_integral (p6Inst r m) r m i

/-- **HH's content statement for member 1**: `log Dhyb ≤ (10339/3072 + ε) r²` eventually. -/
def P6ContentStmt (mf : ℕ → ℕ) : Prop :=
  ∀ ε > 0, ∀ᶠ r : ℕ in atTop,
    Real.log (Dhyb (p6Inst r (mf r)) r (mf r)) ≤ (10339 / 3072 + ε) * (r : ℝ) ^ 2

/-- **Reduction**: the content statement follows from per-prime weights and the piece summation. -/
theorem p6_content_of_pieces (mf : ℕ → ℕ) (hmf : ∀ᶠ r : ℕ in atTop, mf r ≤ r)
    (R : ℕ → ZMod 6 → ℕ) (w : ℕ → ℕ → ℝ) (hw0 : ∀ r p, 0 ≤ w r p)
    (hw : ∀ᶠ r : ℕ in atTop, ∀ p, p.Prime →
      (tropVal (HW (p6Inst r (mf r)).lev p r (mf r)) : ℝ) ≤ w r p)
    (ht : ∀ᶠ r : ℕ in atTop, ∀ c ∈ ({1, 5} : Finset (ZMod 6)), ∀ p, p.Prime →
      p ∉ ({2, 3} : Finset ℕ) → (p : ZMod 6) = c → R r c < p → w r p = 0)
    (hsum : ∀ ε > 0, ∀ᶠ r : ℕ in atTop,
      ∑ c ∈ ({1, 5} : Finset (ZMod 6)), clsSum 6 c (w r) 0 (R r c) ≤
        (10339 / 3072 + ε) * (r : ℝ) ^ 2) : P6ContentStmt mf := by
  intro ε hε
  have hx := (p6_badInfo 0 0).extra_small (ε / 2) (by positivity)
  filter_upwards [hsum (ε / 2) (by positivity), hx, eventually_ge_atTop 1, hmf, hw, ht]
    with r h1 h2 hr hmr hwr htr
  have h3 := p6_log_Dhyb_le (R r) r (mf r) hr (w r) (hw0 r) hwr htr
  have h4 : extraG 3 Ecub 2 (badLog (p6Inst r (mf r))) r (mf r) ≤ ε / 2 * (r : ℝ) ^ 2 :=
    h2 (mf r) hmr
  linarith

end CatalanFrames.P6Hybrid

#print axioms CatalanFrames.P6Hybrid.p6_badInfo
#print axioms CatalanFrames.P6Hybrid.p6_lev_zero_low
#print axioms CatalanFrames.P6Hybrid.p6_lev_zero_win
#print axioms CatalanFrames.P6Hybrid.p6_Dhyb_integral
#print axioms CatalanFrames.P6Hybrid.p6_content_of_pieces
