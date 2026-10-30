module

public import CatalanFrames.LambdaMirrorHybrid.MirContent8
public import CatalanFrames.LambdaMirrorHybrid.MirDefAll
public import CatalanCore.Arith.Hybrid.NegFrame

@[expose] public section

/-!
# Mirror: transfer to the legacy frame `mirFrame`

`mirNInst` (frame `mirNFrame`, λ-like sign) and `mirInst` (legacy frame `mirFrame`) share the level data;
`Mn` differs by a sign.  Hence `Bnd`, `tropExp`, `Dhyb` are equal and `DefHypT` transfers
(`fullPoly` changes by `X ↦ -X`).
-/

open Filter CatalanCore CatalanCore.Arith CatalanCore.Arith.Hybrid CatalanFrames.LambdaMirror
  CatalanFrames.HybCommon

namespace CatalanFrames.LambdaMirrorHybrid

lemma mir_Bnd_eq (r m : ℕ) : Bnd mirNInst r m = Bnd mirInst r m := rfl

lemma mir_tropExp_eq (r m p : ℕ) : tropExp mirNInst r m p = tropExp mirInst r m p := rfl

lemma mir_Dhyb_eq (r m : ℕ) : Dhyb mirNInst r m = Dhyb mirInst r m := rfl

/-- The tropical content bound for the legacy mirror frame. -/
theorem mir_content_trop8_legacy {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop, Real.log (Dhyb mirInst r (r / 8)) ≤
      (24994314577 / 6665218560 + ε) * (r : ℝ) ^ 2 := by
  filter_upwards [mir_content_trop8 hε] with r hr
  rw [← mir_Dhyb_eq]; exact hr

/-- The glued deficit family for the legacy mirror frame. -/
theorem mir_defHypT_all3_legacy {r : ℕ} (hr : 16 ≤ r) :
    DefHypT mirInst r (r / 8) (TfunG 3 mirNInst r) (defG 3 r) :=
  DefHypT.of_neg (I₁ := mirNInst) (I₂ := mirInst) (fun a b => mir_Mn_neg a b) (mir_Bnd_eq r (r / 8))
    (mir_defHypT_all3 hr)

end CatalanFrames.LambdaMirrorHybrid
