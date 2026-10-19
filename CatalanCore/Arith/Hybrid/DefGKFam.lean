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

/-- Exceptional primes of the class `j = 1` (`p ≡ 4 - o (mod 4)`): the primes dividing the determinants
of the chain types (`139` for λ, `37, 73, 350972849` for the mirror). -/
def ExcJ1 (o p : ℕ) : Prop := if o = 1 then p ≠ 139 else (p ≠ 37 ∧ p ≠ 73 ∧ p ≠ 350972849)

/-- Exceptional primes of the class `j = 3` (`p ≡ o (mod 4)`): `1009` for λ, `8663` for the mirror. -/
def ExcJ3 (o p : ℕ) : Prop := if o = 1 then p ≠ 1009 else p ≠ 8663

lemma gks3_of {o p r m : ℕ} (ho : o = 1 ∨ o = 3) (h13 : 13 ≤ p) (hmod : p % 4 = 4 - o)
    (hx : ExcJ1 o p) (hr : 9 * p + o < 4 * r) (hN : r + 2 * m ≤ 3 * p) (hm : 0 < m) :
    GKS3 o p r m ((p + o) / 4) := by
  rcases ho with rfl | rfl
  · simp only [ExcJ1, if_true] at hx
    exact ⟨h13, ⟨by omega, by omega, by omega⟩, by omega, hN, hm, hx, by omega, by omega, by omega⟩
  · simp only [ExcJ1] at hx
    exact ⟨h13, ⟨by omega, by omega, by omega⟩, by omega, hN, hm, by omega, hx.1, hx.2.1, hx.2.2⟩

lemma gks1_of {o p r m : ℕ} (ho : o = 1 ∨ o = 3) (h13 : 13 ≤ p) (hmod : p % 4 = o)
    (hx : ExcJ3 o p) (hr : 2 * p < r) (hN : 4 * (r + 2 * m) ≤ 11 * p + o) (hm : 0 < m) :
    GK1.GKS1 o p r m ((3 * p + o) / 4) := by
  rcases ho with rfl | rfl
  · simp only [ExcJ3, if_true] at hx
    exact ⟨h13, ⟨by omega, by omega, by omega⟩, hr, hN, hm, hx, by omega⟩
  · simp only [ExcJ3] at hx
    exact ⟨h13, ⟨by omega, by omega, by omega⟩, hr, hN, hm, by omega, hx⟩

/-- The low-band clean primes of GK, for the offset `o`. -/
def LowCleanO (o r m p : ℕ) : Prop :=
  (13 ≤ p ∧ p % 4 = 4 - o ∧ ExcJ1 o p ∧ 9 * p + o < 4 * r ∧ r + 2 * m ≤ 3 * p) ∨
  (13 ≤ p ∧ p % 4 = o ∧ ExcJ3 o p ∧ 2 * p < r ∧ 4 * (r + 2 * m) ≤ 11 * p + o)

open Classical in
/-- **GK as a `DefHypT` family, generic in the offset `o`**: deficit `m` on `LowCleanO`. -/
theorem defHypT_GK_o {Fr : Frame} (I : HybInst Fr) {o : ℕ} (ho : o = 1 ∨ o = 3)
    (hL : LamData Fr o) (r m : ℕ) (hm : 0 < m)
    (T : ℕ → ℕ) (hT : ∀ p, p.Prime → p < Bnd I r m → tropExp I r m p ≤ T p)
    (hTd : ∀ p : ℕ, p.Prime → LowCleanO o r m p → 2 * r + m ≤ T p) :
    DefHypT I r m T (fun p => if LowCleanO o r m p then m else 0) := by
  refine defHypT_of_local I r m T _ hT (LowCleanO o r m) (fun p hp => by simp [hp]) ?_
  intro p hp hb hW
  haveI : Fact p.Prime := ⟨hp⟩
  have hd := hTd p hp hW
  have hg : GLE p (2 * r) (Fr.fullPoly r m) := by
    rcases hW with ⟨h13, hmod, hx, hr, hN⟩ | ⟨h13, hmod, hx, hr, hN⟩
    · exact gleAt_GK3 hL (gks3_of ho h13 hmod hx hr hN hm)
    · exact GK1.gleAt_GK1 hL (gks1_of ho h13 hmod hx hr hN hm)
  simp only [if_pos hW]
  exact ⟨by omega, fun [Fact p.Prime] => hg.mono (by omega)⟩

/-- The low-band clean primes of GK for λ (`o = 1`). -/
def LowClean (r m p : ℕ) : Prop :=
  (13 ≤ p ∧ p % 4 = 3 ∧ p ≠ 139 ∧ 9 * p + 1 < 4 * r ∧ r + 2 * m ≤ 3 * p) ∨
  (13 ≤ p ∧ p % 4 = 1 ∧ p ≠ 1009 ∧ 2 * p < r ∧ 4 * (r + 2 * m) ≤ 11 * p + 1)

lemma lowClean_iff (r m p : ℕ) : LowClean r m p ↔ LowCleanO 1 r m p := by
  simp [LowClean, LowCleanO, ExcJ1, ExcJ3]

open Classical in
/-- **GK as a `DefHypT` family** (λ): deficit `m` on `LowClean`, against any `T ≥ 2r + m`. -/
theorem defHypT_GK {Fr : Frame} (I : HybInst Fr) (hL : LamData Fr 1) (r m : ℕ) (hm : 0 < m)
    (T : ℕ → ℕ) (hT : ∀ p, p.Prime → p < Bnd I r m → tropExp I r m p ≤ T p)
    (hTd : ∀ p : ℕ, p.Prime → LowClean r m p → 2 * r + m ≤ T p) :
    DefHypT I r m T (fun p => if LowClean r m p then m else 0) := by
  have h := defHypT_GK_o I (Or.inl rfl) hL r m hm T hT
    (fun p hp hW => hTd p hp ((lowClean_iff r m p).2 hW))
  have e : (fun p => if LowClean r m p then m else 0) =
      (fun p => if LowCleanO 1 r m p then m else 0) := by
    funext p
    simp only [lowClean_iff]
  rw [e]
  exact h

end CatalanCore.Arith.Hybrid
