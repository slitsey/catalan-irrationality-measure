module

public import CatalanFrames.HybCommon.Numer
public import CatalanCore.Arith.Hybrid.D1Exact
public import CatalanCore.Arith.Hybrid.Values

@[expose] public section

/-!
# Generic tropical dual bounds, free hybrid size `m`

`XGm I r m p = tropVal (HW I.lev p r m)` and the bounds `D1x, D2, D45, D6` of the dual potentials,
for an arbitrary hybrid size `m` (the old `HybCommon/Trop.lean` fixes `m = r / 8`).  Only
`LevelFacts` (zero set `c < kq q`, good primes `≥ 5`) is used; no modulus, no residue classes.
-/

open Finset Filter CatalanCore CatalanCore.Arith CatalanCore.Arith.Hybrid CatalanFrames.HybCommon

namespace CatalanFrames.HybGen

variable {Fr : Frame}

/-- The level-1 tropical value of the hybrid at `(r, m)` and the prime `p`. -/
noncomputable def XGm (I : HybInst Fr) (r m p : ℕ) : ℕ := tropVal (HW I.lev p r m)

/-- The real-valued weight of the class summation. -/
noncomputable def WGm (I : HybInst Fr) (r m p : ℕ) : ℝ := (XGm I r m p : ℝ)

section Dual

variable {I : HybInst Fr} (T : LevelFacts I (fun p => 5 ≤ p) (fun q c => c < I.cd.kq q))
include T

lemma XGm_D2 (r m p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) (hm : 2 * m < p) (hu : p ≤ r)
    (hk : I.cd.kq p ≤ r) :
    ∃ u L : ℕ, I.cd.kq p + p ≤ u + r ∧ u ≤ r ∧ L ≤ u ∧ L ≤ 2 * m ∧
      XGm I r m p ≤ 2 * (r - u) + 2 * m + L := by
  obtain ⟨hq, hb⟩ := T.good p hp h5
  exact val_D2 p r m (I.cd.kq p) (lev := I.lev) hp.one_lt.le
    (fun c hc => T.high p c hp.one_lt.le hc) hm hu hk
    (fun c => T.zero_iff p c hq hb)

lemma XGm_D45 (r m p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) (hr : r < p) (hmr : 2 * m ≤ r) :
    XGm I r m p ≤ 2 * (r - I.cd.kq p) + 2 * m + (2 * m - (p - r)) := by
  obtain ⟨hq, hb⟩ := T.good p hp h5
  exact val_D45 p r m (I.cd.kq p) (lev := I.lev) hr hmr (fun c => T.zero_iff p c hq hb)

lemma XGm_D6 (r m p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) (hN : r + 2 * m ≤ p)
    (hk : r ≤ I.cd.kq p) : XGm I r m p ≤ 2 * m - (I.cd.kq p - r) := by
  obtain ⟨hq, hb⟩ := T.good p hp h5
  exact val_D6 p r m (I.cd.kq p) (lev := I.lev) hN hk (fun c => T.zero_iff p c hq hb)

end Dual

lemma XGm_D1x (I : HybInst Fr) (r m p : ℕ) (hp : p.Prime) (h2 : p ≠ 2) :
    XGm I r m p ≤ 2 * r + 2 * m - min (m % p) (p - m % p) := by
  have hodd : p % 2 = 1 := by have := hp.eq_two_or_odd; omega
  exact val_D1x p r (lev := I.lev) hodd hp.pos m

end CatalanFrames.HybGen

#print axioms CatalanFrames.HybGen.XGm_D2
#print axioms CatalanFrames.HybGen.XGm_D1x
