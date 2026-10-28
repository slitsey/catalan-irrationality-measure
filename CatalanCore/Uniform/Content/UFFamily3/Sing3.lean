module

public import CatalanCore.Uniform.Content.UFFamily3.Kill3

@[expose] public section

/-!
# UF thirds families: nonsingular windows from divisibility facts (lane H, H12)

`noSing_T`: `NoSingWin` of the two-term data of `(q, o) = (3, 2)` from `p ∤ k` and `p ∤ 3 k - 2` on the
window; `nopole_T`: the second fact from a finite check on the quotient `j` (`3 k = j p + 2`);
`nosing_mono`, `div_both`.
-/

open Polynomial Matrix Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Arith.Hybrid.Periodic CatalanCore.Uniform.Content.UFMember
  CatalanCore.Uniform.Content.Hybrid CatalanCore.Uniform.Content.UFMoments
  CatalanCore.Uniform.Content.UFWedge CatalanCore.Uniform.Content.Smith

namespace CatalanCore.Uniform.Content.UFFamily3

variable {Fr : Frame}

theorem noSing_T (T : TwoTermData Fr 3 2) {p N : ℕ} [Fact p.Prime] (hN : N ≤ p * p)
    (hsq : ∀ t, 1 ≤ t → t < N → ¬ p ^ 2 ∣ 3 * t - 2) (hnorm : Fr.norm ∈ S p)
    (hnorm0 : red p Fr.norm ≠ 0) (a Δ : ℕ) (ha : 1 ≤ a)
    (h1 : ∀ k, a < k → k ≤ a + Δ → ¬ p ∣ k) (h2 : ∀ k, a < k → k ≤ a + Δ → ¬ p ∣ 3 * k - 2) :
    NoSingWin (twoTermPoleData T hN hsq hnorm hnorm0) a Δ := by
  intro k hk1 hk2
  show ¬ ttSing p 3 2 (k : ℤ)
  rw [ttSing_nat T (by omega)]
  push Not
  exact ⟨h1 k hk1 hk2, h2 k hk1 hk2⟩

theorem nopole_T {p a b : ℕ} (hb : ∀ k, a < k → k ≤ b → 3 * k < 13 * p + 2)
    (h : ∀ j, j < 13 → ∀ k, a < k → k ≤ b → 3 * k = j * p + 2 → False) :
    ∀ k, a < k → k ≤ b → ¬ p ∣ 3 * k - 2 := by
  intro k h1 h2 ⟨j, hj⟩
  have hk := hb k h1 h2
  have e : p * j = j * p := Nat.mul_comm p j
  have hj13 : j < 13 := by
    by_contra hc
    push Not at hc
    have := Nat.mul_le_mul_left p hc
    omega
  exact h j hj13 k h1 h2 (by omega)

theorem nosing_mono {p N : ℕ} [Fact p.Prime] {D : Periodic.PoleData Fr p N} {a Δ Δ' : ℕ}
    (h : NoSingWin D a Δ) (h2 : Δ' ≤ Δ) : NoSingWin D a Δ' :=
  fun k hk1 hk2 => h k hk1 (by omega)

theorem div_both {p a b x : ℕ} (h1 : x * p ≤ a) (h2 : a < (x + 1) * p) (h3 : x * p ≤ b)
    (h4 : b < (x + 1) * p) : a / p = b / p :=
  (Nat.div_eq_of_lt_le h1 h2).trans (Nat.div_eq_of_lt_le h3 h4).symm

end CatalanCore.Uniform.Content.UFFamily3
