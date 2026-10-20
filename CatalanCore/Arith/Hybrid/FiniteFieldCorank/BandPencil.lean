module
public import CatalanCore.Arith.Hybrid.FiniteFieldCorank.SignedMoment
public import CatalanCore.Arith.Hybrid.FiniteFieldCorank.BandsJet
@[expose] public section
open Polynomial Matrix Module Finset
namespace CatalanCore.Arith.Hybrid.FiniteFieldCorank
variable {ell K m S g : ℕ} [Fact ell.Prime]

noncomputable def bandPencil (H : BandGeometry ell K m S g)
    (hn : 3 ≤ K-m) (hng : K-m ≤ g) (h2 : (2 : ZMod ell) ≠ 0) (z : ZMod ell) :=
  momentMatrix (lowBand ell K ∪ highBand ell g)
    (pencilWeight (H.toJetGeometry hn hng h2) (rootProduct (lowBand ell K))
      (rootProduct (borderBand ell g m)) z) (K-m)

lemma eval_rootProduct_of_mem {k : Type*} [Field k] [DecidableEq k]
    (s : Finset k) {a : k} (ha : a ∈ s) : (rootProduct s).eval a = 0 := by
  simp only [rootProduct, eval_prod]
  exact Finset.prod_eq_zero ha (by simp)

theorem bandPencil_corank (H : BandGeometry ell K m S g)
    (hn : 3 ≤ K-m) (hng : K-m ≤ g) (h2 : (2 : ZMod ell) ≠ 0) (z : ZMod ell) :
    finrank (ZMod ell) (LinearMap.ker (bandPencil H hn hng h2 z).mulVecLin) ≤ 3 := by
  have hk := H.hK; have hs := H.hS; have hsg := H.hSg; have hr := H.room
  apply signed_moment_corank (H.toJetGeometry hn hng h2) hn (by omega)
    (rootProduct (lowBand ell K)) (rootProduct (highBand ell g))
    (rootProduct (borderBand ell g m)) (rootProduct (tailBand ell K g m))
    (low_high_disjoint H) (rootProduct_union _ _ (low_high_disjoint H))
    (rootProduct_bands H)
  · exact fun a ha => eval_rootProduct_of_mem _ ha
  · exact fun a ha => eval_rootProduct_of_mem _ ha
  · exact fun a ha => eval_rootProduct_of_mem _ ha
  · change 2 * (rootProduct (lowBand ell K)).natDegree +
      (rootProduct (tailBand ell K g m)).natDegree +
      (lowBand ell K ∪ highBand ell g).card ≤ ell + 2 * (K-m)
    rw [natDegree_rootProduct, natDegree_rootProduct, card_lowBand H,
      card_tailBand H, card_supportBand H]
    omega
  · exact h2

#print axioms bandPencil_corank
end CatalanCore.Arith.Hybrid.FiniteFieldCorank
