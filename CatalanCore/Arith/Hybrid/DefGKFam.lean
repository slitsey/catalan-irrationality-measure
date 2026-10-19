module

public import CatalanCore.Arith.Hybrid.DefGKGle3
public import CatalanCore.Arith.Hybrid.DefGKGle1

@[expose] public section

/-!
# GK (both classes) as one `DefHypT` family

The low-band clean primes `LowClean3 ∪ LowClean1` (GK-deficit-lowband §1): the deficit is `m` against any
`T p ≥ 2r + m`.  `gks3_of` / `gks1_of` turn the arithmetic conditions into the `GKS3` / `GKS1` data.

* `LowClean3 r m p`: `p ≡ 3 (4)`, `13 ≤ p`, `p ≠ 139`, `9p+1 < 4r`, `r + 2m ≤ 3p`.
* `LowClean1 r m p`: `p ≡ 1 (4)`, `13 ≤ p`, `p ≠ 1009`, `2p < r`, `4(r + 2m) ≤ 11p + 1`.
-/

open Finset Polynomial CatalanCore CatalanCore.Basic

namespace CatalanCore.Arith.Hybrid

lemma gks3_of {p r m : ℕ} (h13 : 13 ≤ p) (hmod : p % 4 = 3) (h139 : p ≠ 139)
    (hr : 9 * p + 1 < 4 * r) (hN : r + 2 * m ≤ 3 * p) (hm : 0 < m) :
    GKS3 p r m ((p + 1) / 4) :=
  ⟨h13, by omega, by omega, hN, hm, h139⟩

lemma gks1_of {p r m : ℕ} (h13 : 13 ≤ p) (hmod : p % 4 = 1) (h1009 : p ≠ 1009)
    (hr : 2 * p < r) (hN : 4 * (r + 2 * m) ≤ 11 * p + 1) (hm : 0 < m) :
    GK1.GKS1 p r m ((3 * p + 1) / 4) :=
  ⟨h13, by omega, hr, hN, hm, h1009⟩

/-- The low-band clean primes of GK. -/
def LowClean (r m p : ℕ) : Prop :=
  (13 ≤ p ∧ p % 4 = 3 ∧ p ≠ 139 ∧ 9 * p + 1 < 4 * r ∧ r + 2 * m ≤ 3 * p) ∨
  (13 ≤ p ∧ p % 4 = 1 ∧ p ≠ 1009 ∧ 2 * p < r ∧ 4 * (r + 2 * m) ≤ 11 * p + 1)

open Classical in
/-- **GK as a `DefHypT` family**: deficit `m` on `LowClean`, against any `T ≥ 2r + m`. -/
theorem defHypT_GK {Fr : Frame} (I : HybInst Fr) (hL : LamData Fr) (r m : ℕ) (hm : 0 < m)
    (T : ℕ → ℕ) (hT : ∀ p, p.Prime → p < Bnd I r m → tropExp I r m p ≤ T p)
    (hTd : ∀ p : ℕ, p.Prime → LowClean r m p → 2 * r + m ≤ T p) :
    DefHypT I r m T (fun p => if LowClean r m p then m else 0) := by
  refine defHypT_of_local I r m T _ hT (LowClean r m) (fun p hp => by simp [hp]) ?_
  intro p hp hb hW
  haveI : Fact p.Prime := ⟨hp⟩
  have hd := hTd p hp hW
  have hg : GLE p (2 * r) (Fr.fullPoly r m) := by
    rcases hW with ⟨h13, hmod, h139, hr, hN⟩ | ⟨h13, hmod, h1009, hr, hN⟩
    · exact gleAt_GK3 hL (gks3_of h13 hmod h139 hr hN hm)
    · exact GK1.gleAt_GK1 hL (gks1_of h13 hmod h1009 hr hN hm)
  simp only [if_pos hW]
  exact ⟨by omega, fun [Fact p.Prime] => hg.mono (by omega)⟩

end CatalanCore.Arith.Hybrid
