import CatalanCore.Uniform.Bank.Chi3Rank.Layer5
import CatalanCore.Rect.CommonMinor
import CatalanCore.Uniform.Content.ClearMin
set_option Elab.async false

/-! # The rank exponent of the common-node minors of `P6` (lane H, H16)

`rankExp base r m p` is `base` with the rank-layer bounds `min`'d in when they apply
(`r = 4m`, `p` prime, `p > N0`, `r ≤ 2p`, and `p < r` for the class `p ≡ 1 (6)`):

* `p ≡ 1 (6)`: `2r + 2m + 1 - (min p (6m - p) - max (r - p) ((p+1)/2))`;
* `p ≡ 5 (6)`: `2r + 2m + 1 - min ((p+1)/2) (6m - 2p)`.

`rankExp_gle`: if `base` is a valid exponent of every common-node minor, so is `rankExp base`.
This is the interface of `Chi3Content.eExp` (B3c): `eExp'` = `rankExp (eExp r m p) r m p`. -/

namespace CatalanCore.Uniform.Bank.Chi3Rank
open Polynomial Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid CatalanCore.Rect
  CatalanCore.Uniform.Content CatalanCore.Uniform.Content.Hybrid CatalanCore.Uniform.Content.Member
  CatalanCore.Uniform.Content.RankProducer CatalanFrames.P6

/-- Rank bound for primes `≡ 1 (6)`. -/
def rankBound1 (r m p : ℕ) : ℕ :=
  2 * r + 2 * m + 1 - (min p (6 * m - p) - max (r - p) ((p + 1) / 2))

/-- Rank bound for primes `≡ 5 (6)`. -/
def rankBound5 (r m p : ℕ) : ℕ := 2 * r + 2 * m + 1 - min ((p + 1) / 2) (6 * m - 2 * p)

open Classical in
/-- `base` improved by the rank layer where it applies. -/
noncomputable def rankExp (base r m p : ℕ) : ℕ :=
  if p.Prime ∧ r = 4 * m ∧ N0 < p ∧ r ≤ 2 * p ∧ p < r ∧ p % 6 = 1 then min base (rankBound1 r m p)
  else if p.Prime ∧ r = 4 * m ∧ N0 < p ∧ r ≤ 2 * p ∧ p % 6 = 5 then min base (rankBound5 r m p)
  else base

theorem rankExp_le (base r m p : ℕ) : rankExp base r m p ≤ base := by
  unfold rankExp
  split_ifs
  · exact min_le_left _ _
  · exact min_le_left _ _
  · exact le_rfl

theorem minor_nodes (r m : ℕ) :
    Function.Injective (fun c : Fin r => (c : ℕ)) ∧
    (∀ (i : Fin m) (j : Fin r), r + 2 * (i : ℕ) ≠ (j : ℕ)) ∧
    (∀ (i : Fin m) (j : Fin r), r + 2 * (i : ℕ) + 1 ≠ (j : ℕ)) ∧
    (∀ (i j : Fin m), r + 2 * (i : ℕ) ≠ r + 2 * (j : ℕ) + 1) := by
  refine ⟨Fin.val_injective, fun i j => ?_, fun i j => ?_, fun i j => ?_⟩
  · have := j.2; omega
  · have := j.2; omega
  · omega

theorem minor_gle_of_member (p : ℕ) [Fact p.Prime] (r m : ℕ) (s : Finset (Fin r))
    (M : RankMember p6Frame u3 q3 (fun c : Fin r => (c : ℕ)) (fun j : Fin m => r + 2 * (j : ℕ))
      (fun j : Fin m => r + 2 * (j : ℕ) + 1) s p) :
    GLE p M.price (commonMinorPoly p6Frame r m s) := by
  obtain ⟨hc, hxc, hyc, hxy⟩ := minor_nodes r m
  exact RankMember.gle p6Frame u3 q3 hu3 hq3 (fun c : Fin r => (c : ℕ))
    (fun j : Fin m => r + 2 * (j : ℕ)) (fun j : Fin m => r + 2 * (j : ℕ) + 1) hc hxc hyc hxy s p M

theorem rankExp_gle (p : ℕ) [hp : Fact p.Prime] (r m base : ℕ) (s : Finset (Fin r))
    (hb : GLE p base (commonMinorPoly p6Frame r m s)) :
    GLE p (rankExp base r m p) (commonMinorPoly p6Frame r m s) := by
  unfold rankExp
  split_ifs with h1 h5
  · obtain ⟨-, hr, hN, hrp, hpr, h6⟩ := h1
    obtain ⟨M, hM⟩ := rank_c1 r m p hr h6 hN hrp hpr s
    refine gle_min hb ((minor_gle_of_member p r m s M).mono ?_)
    unfold rankBound1; omega
  · obtain ⟨-, hr, hN, hrp, h6⟩ := h5
    obtain ⟨M, hM⟩ := rank_c5 r m p hr h6 hN hrp s
    refine gle_min hb ((minor_gle_of_member p r m s M).mono ?_)
    unfold rankBound5; omega
  · exact hb

end CatalanCore.Uniform.Bank.Chi3Rank
