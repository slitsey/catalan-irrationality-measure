module

public import Mathlib.Data.Nat.Init

@[expose] public section

/-!
# Selection arithmetic for pinned pairs (G3): the "NV hole" and its removal

A pinned pair family needs, for a prime `ℓ = 6 t + 1`, a member `(r, m)` with `r + 2 m = 3 t`
(the geometry of the nonvanishing theorem) inside the decay window `r ≤ 8 m ≤ r + 8`
(`hybridFamUp` with `α = 1/8`).  Eliminating `r`, this is `3 t ≤ 10 m ≤ 3 t + 8`.

* `pair_window_iff` : such an `m` exists iff `3 t ≢ 1 (mod 10)`;
* `pair_hole_iff` : `3 t ≡ 1 (mod 10)` iff `ℓ ≡ 43 (mod 60)`; these are the only "hole" primes;
* `pinned_pair_exists` : for `ℓ ≡ 1 (mod 6)`, `ℓ ≢ 43 (mod 60)`, `ℓ ≥ 61`, the member exists, with
  `1 ≤ m` and `2 m + 1 ≤ t` (the side conditions of the nonvanishing theorem).

So the prime selection can simply avoid `ℓ ≡ 43 (mod 60)`: use the prime class `S60`
(`CatalanCore/NT/Rules.lean`), at the price `s = 8/7` instead of `1` in the window length.
-/

namespace CatalanCore.Rect

theorem pair_window_iff (t : ℕ) :
    (∃ m : ℕ, 3 * t ≤ 10 * m ∧ 10 * m ≤ 3 * t + 8) ↔ (3 * t) % 10 ≠ 1 := by
  constructor
  · rintro ⟨m, h1, h2⟩
    omega
  · intro h
    exact ⟨(3 * t + 9) / 10, by omega, by omega⟩

theorem pair_hole_iff (t : ℕ) : (3 * t) % 10 = 1 ↔ (6 * t + 1) % 60 = 43 := by omega

theorem pinned_pair_exists (ℓ : ℕ) (h6 : ℓ % 6 = 1) (h60 : ℓ % 60 ≠ 43) (hl : 61 ≤ ℓ) :
    ∃ t r m : ℕ, ℓ = 6 * t + 1 ∧ r + 2 * m = 3 * t ∧ r ≤ 8 * m ∧ 8 * m ≤ r + 8 ∧
      1 ≤ m ∧ 2 * m + 1 ≤ t := by
  refine ⟨(ℓ - 1) / 6, 3 * ((ℓ - 1) / 6) - 2 * ((3 * ((ℓ - 1) / 6) + 9) / 10),
    (3 * ((ℓ - 1) / 6) + 9) / 10, by omega, by omega, by omega, by omega, by omega, by omega⟩

end CatalanCore.Rect
