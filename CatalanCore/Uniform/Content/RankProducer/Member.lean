module

public import CatalanCore.Uniform.Content.RankProducer.Price
public import CatalanCore.Uniform.Content.Member.Combine
public import CatalanCore.Uniform.Content.Member.FrameDigamma

@[expose] public section

/-!
# The certificate rank layer on deletion members, and `DebitLayer.rank` (lane H15)

`RankMember` bundles, for one deletion member of a rational digamma frame at one prime, the band
hypotheses and a certificate assignment with its subspace data; `RankMember.gle` is the rank price
of the member.  `DebitLayer.rank` turns a supplier of `RankMember`s whose price is at most
`base r p + debit * k` into a `DebitLayer` of a `BlockGeom` family, usable by
`hasContent_of_debitLayers`.
-/

open Polynomial Finset Module Matrix CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Rect CatalanCore.Uniform CatalanCore.Uniform.Content.Hybrid
  CatalanCore.Uniform.Content.Member

namespace CatalanCore.Uniform.Content.RankProducer

open scoped Classical

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Everything `rank_price_certs` needs for one deletion member. -/
structure RankMember (Fr : Frame) (u q : Fin Fr.d → ℕ) (common : ι → ℕ) (xs ys : κ → ℕ)
    (T : Finset ι) (p : ℕ) [hp : Fact p.Prime] where
  B : ℕ
  hcoef : ∀ j, (frameDigamma Fr u q).c j ∈ S p
  hpq : ∀ j, ¬ p ∣ (frameDigamma Fr u q).q j
  hp3 : 3 ≤ p
  hbd : ∀ j, (frameDigamma Fr u q).q j * B + (frameDigamma Fr u q).u j ≤ p ^ 2
  hB : B < p ^ 2
  ha : ∀ i, memberRows common xs T i ≤ B
  hb : ∀ j, memberCols common ys T j ≤ B
  hia : Function.Injective (memberRows common xs T)
  hib : Function.Injective (memberCols common ys T)
  cert : ZMod p → FibreCert
  hOk : ∀ x, (cert x).Ok
  hInt : ∀ x, (cert x).Integral p
  hReal : ∀ x, Realizes ((frameDigamma Fr u q).poleSplit B hcoef hpq hp3 hbd)
    (memberRows common xs T) (memberCols common ys T) x (cert x)
  hcard : (killRows (p := p) (memberRows common xs T) cert).card =
    (killCols (p := p) (memberCols common ys T) cert).card
  Vs : Submodule (RatFunc (ZMod p)) (RatFunc (ZMod p) × RatFunc (ZMod p))
  mc : ZMod p → ℕ
  mr : ZMod p → ℕ
  hmc2 : ∀ x, mc x ≤ finrank (RatFunc (ZMod p)) Vs
  hmr2 : ∀ x, mr x ≤ finrank (RatFunc (ZMod p)) Vs
  hmc : ∀ x ∈ colFib ((frameDigamma Fr u q).poleSplit B hcoef hpq hp3 hbd)
      (memberRows common xs T) (memberCols common ys T) (digitHyp_of_lt ha hb hB) hia hib
      cert hOk hInt hReal hcard,
    mc x ≤ finrank (RatFunc (ZMod p)) ↥(Vs ⊓ Ucol p (cert x))
  hmr : ∀ x ∈ rowFib ((frameDigamma Fr u q).poleSplit B hcoef hpq hp3 hbd)
      (memberRows common xs T) (memberCols common ys T) (digitHyp_of_lt ha hb hB) hia hib
      cert hOk hInt hReal hcard,
    mr x ≤ finrank (RatFunc (ZMod p)) ↥(Vs ⊓ Urow p (cert x))

namespace RankMember

variable {Fr : Frame} {u q : Fin Fr.d → ℕ} {common : ι → ℕ} {xs ys : κ → ℕ} {T : Finset ι}
  {p : ℕ} [hp : Fact p.Prime]

/-- The rank price of the member: `2h - |s| - (F + Σ mc - Σ (dim V - mr))`. -/
noncomputable def price (M : RankMember Fr u q common xs ys T p) : ℕ :=
  Fintype.card (T ⊕ κ) + (Fintype.card (T ⊕ κ) -
      (BKc ((frameDigamma Fr u q).poleSplit M.B M.hcoef M.hpq M.hp3 M.hbd)
        (memberRows common xs T) (memberCols common ys T) (digitHyp_of_lt M.ha M.hb M.hB)
        M.hia M.hib M.cert M.hOk M.hInt M.hReal M.hcard).s.card) -
    (Fintype.card {j : (BKc ((frameDigamma Fr u q).poleSplit M.B M.hcoef M.hpq M.hp3 M.hbd)
        (memberRows common xs T) (memberCols common ys T) (digitHyp_of_lt M.ha M.hb M.hB)
        M.hia M.hib M.cert M.hOk M.hInt M.hReal M.hcard).s //
        load (fun l => ((frameDigamma Fr u q).poleSplit M.B M.hcoef M.hpq M.hp3 M.hbd).lf
            (memberCols common ys T l)) (fun l => redQ p
          ((BKc ((frameDigamma Fr u q).poleSplit M.B M.hcoef M.hpq M.hp3 M.hbd)
            (memberRows common xs T) (memberCols common ys T) (digitHyp_of_lt M.ha M.hb M.hB)
            M.hia M.hib M.cert M.hOk M.hInt M.hReal M.hcard).P l j)) = 0} +
      (∑ x ∈ colFib ((frameDigamma Fr u q).poleSplit M.B M.hcoef M.hpq M.hp3 M.hbd)
          (memberRows common xs T) (memberCols common ys T) (digitHyp_of_lt M.ha M.hb M.hB)
          M.hia M.hib M.cert M.hOk M.hInt M.hReal M.hcard, M.mc x -
        ∑ x ∈ rowFib ((frameDigamma Fr u q).poleSplit M.B M.hcoef M.hpq M.hp3 M.hbd)
          (memberRows common xs T) (memberCols common ys T) (digitHyp_of_lt M.ha M.hb M.hB)
          M.hia M.hib M.cert M.hOk M.hInt M.hReal M.hcard,
          (finrank (RatFunc (ZMod p)) M.Vs - M.mr x)))

/-- **Rank price of a deletion member from certificates.** -/
theorem gle (Fr : Frame) (u q : Fin Fr.d → ℕ) (hu : ∀ j, Fr.μ j = u j / q j) (hq : ∀ j, 0 < q j)
    (common : ι → ℕ) (xs ys : κ → ℕ) (hc : Function.Injective common)
    (hxc : ∀ i j, xs i ≠ common j) (hyc : ∀ i j, ys i ≠ common j) (hxy : ∀ i j, xs i ≠ ys j)
    (T : Finset ι) (p : ℕ) [Fact p.Prime] (M : RankMember Fr u q common xs ys T p) :
    GLE p M.price (FullN Fr (fun a : T => common a.1) xs ys (X : ℚ[X])).det := by
  refine member_gle_of_loewner Fr (frameDigamma Fr u q).f (frameDigamma Fr u q).e
    (mn_eq_loewner Fr u q hu hq) common xs ys hc hxc hyc hxy T ?_
  exact rank_price_certs ((frameDigamma Fr u q).poleSplit M.B M.hcoef M.hpq M.hp3 M.hbd)
    (memberRows common xs T) (memberCols common ys T) (digitHyp_of_lt M.ha M.hb M.hB)
    M.hia M.hib M.cert M.hOk M.hInt M.hReal M.hcard M.Vs M.mc M.mr M.hmc M.hmr M.hmc2 M.hmr2

end RankMember

end CatalanCore.Uniform.Content.RankProducer
