module

public import CatalanFrames.LambdaMirrorHybrid.MirFinal2
public import CatalanFrames.LambdaMirrorHybrid.MirLegacy
public import CatalanFrames.HybCommon.LogDhybT

@[expose] public section

/-!
# Mirror: the content bound for the deficit family (`DhybT`), before the deficit sums

`mir_logDhybT_le`: the generic `logDhybT_le_G` at `mirNInst` (offset `3`, bad primes `{2, 3}`).
-/

open Filter CatalanCore CatalanCore.Arith CatalanCore.Arith.Hybrid CatalanFrames.LambdaMirror
  CatalanFrames.HybCommon

namespace CatalanFrames.LambdaMirrorHybrid

lemma mirBad : BadInfo mirNInst where
  L4 := rfl
  Ebd4 := fun _ => rfl
  bad_sub := fun p hp => by simpa [mirNInst, mirInst, HybInst.neg, HybInst.ofSing,
    ContentData.neg, mirCD] using hp
  c2 := mir_cOf2
  c3 := mir_cOf3

/-- **The content bound for the glued deficit family, mirror (before the deficit sums).** -/
theorem mir_logDhybT_le {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop, ∀ δ : ℕ → ℕ, DefHypT mirNInst r (r / 8) (TfunG 3 mirNInst r) δ →
      Real.log (DhybT mirNInst r (r / 8) (TfunG 3 mirNInst r) δ) ≤
        (24994314577 / 6665218560 + ε) * (r : ℝ) ^ 2 -
        ∑ p ∈ (Finset.range (Bnd mirNInst r (r / 8))).filter Nat.Prime, (δ p : ℝ) * Real.log p := by
  filter_upwards [logDhybT_le_G mirN_tropFacts mirBad hε] with r hr using hr

#print axioms mir_logDhybT_le

end CatalanFrames.LambdaMirrorHybrid
