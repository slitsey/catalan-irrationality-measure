module

public import CatalanCore.Arith.Hybrid.RankGLE

@[expose] public section

/-!
# Rank witnesses (MEM2C)

`HasRankWit Fr p r m u v k` : the data of the rank principle for `Full(X)` of `Frame.fullPoly r m`:
scalings `u, v` with integral lifts `p^{u a + v b} Full_ab` whose reduction `Bbar` has rank
`≤ r + m - k`.  Every rank-route deficit (Theorems B, C5, C7, Lemma E) produces one; it yields

* `HasRankWit.gle` : `GLE p (∑u + ∑v - k) (fullPoly r m)` (member 1), and
* `HasRankWit.border` (in `BorderDef`) : the bordered statement for `afterTop r m` (member 2).
-/

open Polynomial CatalanCore.Basic

namespace CatalanCore.Arith.Hybrid

/-- A rank witness for `Full(X)`. -/
def HasRankWit (Fr : Frame) (p : ℕ) [Fact p.Prime] (r m : ℕ) (u v : Fin r ⊕ Fin m → ℕ)
    (k : ℕ) : Prop :=
  ∃ Bbar : Matrix (Fin r ⊕ Fin m) (Fin r ⊕ Fin m) (RatFunc (ZMod p)),
    (∀ a b, ∃ g : (LocRing p)[X],
      toQ p g = C ((p : ℚ) ^ (u a + v b)) * fullEntry Fr r m a b ∧ phiP p g = Bbar a b) ∧
    Bbar.rank + k ≤ r + m

variable {Fr : Frame} {p : ℕ} [Fact p.Prime] {r m : ℕ} {u v : Fin r ⊕ Fin m → ℕ} {k : ℕ}

theorem HasRankWit.gle (h : HasRankWit Fr p r m u v k) :
    GLE p (∑ a, u a + ∑ b, v b - k) (Fr.fullPoly r m) := by
  obtain ⟨Bbar, hB, hrk⟩ := h
  exact gle_full_of_rank p Fr r m u v Bbar hB k hrk

end CatalanCore.Arith.Hybrid
