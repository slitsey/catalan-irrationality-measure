module

public import CatalanFrames.P6Hybrid.ValOneEntries
public import CatalanCore.Arith.Hybrid.ValOneFrame
public import CatalanFrames.LambdaHybrid.NV.HDelta
public import CatalanFrames.LambdaHybrid.NV.Members

/-!
# P6's thin valuation-one instance

The first theorem allows any geometry with a full low core and arbitrary common
middle nodes. Thus the proposed endpoint-extension families can use this result
without another arithmetic proof.
-/

@[expose] public section

open Finset CatalanCore CatalanCore.Rect CatalanFrames.P6
open CatalanFrames.LambdaHybrid.NV

namespace CatalanFrames.P6Hybrid

variable {ℓ t : ℕ} [Fact ℓ.Prime]

/-- Any middle-node geometry satisfying the generic cross-Gram condition. -/
theorem p6_full_valOne_ne (hl : ℓ = 6 * t + 1) (ht : 1 ≤ t) (G : Geometry)
    (hlow : ∀ n, n < 2 * t + 1 → n ∈ G.C)
    (hlt : ∀ n, n ∈ G.C ∨ n ∈ G.X' ∨ n ∈ G.Y' → n < 3 * t + 1)
    (hhi : ∀ n, n ∈ G.X' ∨ n ∈ G.Y' → 2 * t + 1 ≤ n)
    (hGram : ((WX ℓ (2 * t + 1) G).transpose * WY ℓ (2 * t + 1) G).det ≠ 0)
    {x : ℚ} {u : ZMod ℓ} (hx : Good ℓ ((ℓ : ℚ) * x) u) (hu : u ≠ 0) :
    (G.Full p6Frame x).det ≠ 0 :=
  CatalanCore.Arith.Hybrid.ValOne.frame_det_ne_zero (p6Data3 hl ht)
    (fun _ _ ha ha' hb hb' hab => midmid_ne_mem hl ht ha ha' hb hb' hab)
    G hlow hlt hhi hGram hx hu

/-- The pinned first member; no hypothesis on the rational border determinant. -/
theorem p6_after_valOne_ne (hl : ℓ = 6 * t + 1) (ht : 1 ≤ t)
    (m : ℕ) (hm : 1 ≤ m) (hband : 2 * m + 1 ≤ t)
    {x : ℚ} {u : ZMod ℓ} (hx : Good ℓ ((ℓ : ℚ) * x) u) (hu : u ≠ 0) :
    ((after (3 * t - 2 * m) m).Full p6Frame x).det ≠ 0 := by
  let r := 3 * t - 2 * m
  have hrK : 2 * t + 1 ≤ r := by dsimp [r]; omega
  apply p6_full_valOne_ne hl ht (after r m)
  · intro n hn
    simpa only [after, Finset.mem_range] using (show n < r by omega)
  · intro n hn
    rcases hn with hc | hx | hy
    · have hn : n < r := by simpa only [after, Finset.mem_range] using hc
      dsimp [r] at hn
      omega
    · have hn := (memXY r m n).1 (Or.inl hx)
      dsimp [r] at hn
      omega
    · have hn := (memXY r m n).1 (Or.inr hy)
      dsimp [r] at hn
      omega
  · intro n hn
    have hn := (memXY r m n).1 hn
    omega
  · exact isUnit_iff_ne_zero.mp (hDelta_after (ℓ := ℓ) (2 * t + 1) m r
      (by omega) (by omega) hrK (by dsimp [r]; omega))
  · exact hx
  · exact hu

#print axioms p6_after_valOne_ne

end CatalanFrames.P6Hybrid
