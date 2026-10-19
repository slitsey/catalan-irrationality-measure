module

public import CatalanCore.Arith.Hybrid.LemmaE.GleE4
public import CatalanCore.Arith.Hybrid.LemmaE.Class3L
public import CatalanCore.Arith.Hybrid.BorderDef

@[expose] public section

/-!
# Lemma E, classes 1 and 3, for the bordered member `afterTop r m` (MEM2C)

Bordered twins of `gleAt_E` and `gleAt_E3`: same hypotheses (plus a `HybInst`), conclusion
`GLE p (∑u + ∑v - m + topC I r m p) ((afterTop r m).fullPolyG Fr)`.
-/

open Finset Polynomial CatalanCore CatalanCore.Basic CatalanCore.Rect Matrix

namespace CatalanCore.Arith.Hybrid

variable {p : ℕ} [Fact p.Prime] {Fr : Frame} {r m j k : ℕ}

/-- Bordered twin of `gleAt_E`. -/
theorem gleAt_E_top (I : HybInst Fr) (hL : LamData Fr) (S : ESetup p r m j k) (sU : ZMod p)
    (hj : ((j : ℕ) : ZMod p) ≠ 0) (he : -(4 * ((j : ℕ) : ZMod p)⁻¹) + 1 ≠ 0)
    (hUU : ∀ a b : ℕ, r - p ≤ a → a < k → r - p ≤ b → b < k →
      TE p j r k a b = (16 : ZMod p)⁻¹ * ((if a = b then sU else 0) +
        ∑ c ∈ Ico k p, ((c : ZMod p) - a)⁻¹ * ((c : ZMod p) - b)⁻¹)) :
    GLE p (∑ a, wE p r k (Frame.hybRow r m a) + ∑ b, wE p r k (Frame.hybCol r m b) - m
      + topC I r m p) ((afterTop r m).fullPolyG Fr) := by
  have hrank := rank_BE_le S sU hj he hUU
  refine gle_fullTop_of_rank' I r m p (fun a => wE p r k (Frame.hybRow r m a))
    (fun b => wE p r k (Frame.hybCol r m b)) (BE p j r m k) (fun a b => hred_E hL S a b) m ?_
  omega

/-- Bordered twin of `gleAt_E3`. -/
theorem gleAt_E3_top (I : HybInst Fr) {k1 : ℕ} (S : ESetup3 p r m k1) (hL : LamData Fr)
    (h6255 : ¬ p ∣ 6255) :
    GLE p (∑ a, wr p r m (Frame.hybRow r m a) + ∑ b, wc p r m (Frame.hybCol r m b) - m
      + topC I r m p) ((afterTop r m).fullPolyG Fr) := by
  have hrank := rank_BE3_le S h6255
  refine gle_fullTop_of_rank' I r m p (fun a => wr p r m (Frame.hybRow r m a))
    (fun b => wc p r m (Frame.hybCol r m b)) (BE3 p r m (sd3 S))
    (fun a b => hred_E3 hL S a b) m ?_
  omega

end CatalanCore.Arith.Hybrid
