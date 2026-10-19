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

/-- **The numerology parameters of the mirror** (`HybParams`): as λ, with offset `3`. -/
noncomputable def mirParams : HybParams mirNInst where
  Lc := 4
  cm := 4
  bad := mirBad
  M := 4
  Cs := {1, 3}
  cls := cls_mod4 mirBad
  mf := fun r => r / 8
  mf_le := fun r => Nat.div_le_self r 8
  Gd := fun p => 5 ≤ p
  Z := fun q c => c < mirNInst.cd.kq q
  levels := mirN_tropFacts.toLevelFacts

/-- **The content bound for the glued deficit family, mirror (before the deficit sums).** -/
theorem mir_logDhybT_le {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop, ∀ δ : ℕ → ℕ, DefHypT mirNInst r (r / 8) (TfunG 3 mirNInst r) δ →
      Real.log (DhybT mirNInst r (r / 8) (TfunG 3 mirNInst r) δ) ≤
        (24994314577 / 6665218560 + ε) * (r : ℝ) ^ 2 -
        ∑ p ∈ (Finset.range (Bnd mirNInst r (r / 8))).filter Nat.Prime, (δ p : ℝ) * Real.log p := by
  filter_upwards [logDhybT_le_G mirN_tropFacts mirBad hε] with r hr using hr

#print axioms mir_logDhybT_le

end CatalanFrames.LambdaMirrorHybrid
