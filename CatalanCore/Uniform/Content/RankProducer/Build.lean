module

public import CatalanCore.Uniform.Content.RankProducer.Layer

@[expose] public section

/-!
# Exact subspace counts: the default `mc`, `mr` (lane H15)

Taking `mc x = dim (V ∩ U^col_x)` and `mr x = dim (V ∩ U^row_x)` needs no inequality hypothesis:
the price is then the exact fibre-additive value for `V`.  For `V = ⊥` it is `h + R0 - F`.
-/

open Polynomial Finset Module Matrix CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Rect CatalanCore.Uniform CatalanCore.Uniform.Content.Hybrid
  CatalanCore.Uniform.Content.Member

namespace CatalanCore.Uniform.Content.RankProducer

open scoped Classical

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- A `RankMember` with the exact subspace dimensions as `mc`, `mr`. -/
noncomputable def RankMember.ofExact (Fr : Frame) (u q : Fin Fr.d → ℕ) (common : ι → ℕ)
    (xs ys : κ → ℕ) (T : Finset ι) (p : ℕ) [Fact p.Prime] (B : ℕ)
    (hcoef : ∀ j, (frameDigamma Fr u q).c j ∈ S p) (hpq : ∀ j, ¬ p ∣ (frameDigamma Fr u q).q j)
    (hp3 : 3 ≤ p) (hbd : ∀ j, (frameDigamma Fr u q).q j * B + (frameDigamma Fr u q).u j ≤ p ^ 2)
    (hB : B < p ^ 2) (ha : ∀ i, memberRows common xs T i ≤ B)
    (hb : ∀ j, memberCols common ys T j ≤ B)
    (hia : Function.Injective (memberRows common xs T))
    (hib : Function.Injective (memberCols common ys T))
    (cert : ZMod p → FibreCert) (hOk : ∀ x, (cert x).Ok) (hInt : ∀ x, (cert x).Integral p)
    (hReal : ∀ x, Realizes ((frameDigamma Fr u q).poleSplit B hcoef hpq hp3 hbd)
      (memberRows common xs T) (memberCols common ys T) x (cert x))
    (hcard : (killRows (p := p) (memberRows common xs T) cert).card =
      (killCols (p := p) (memberCols common ys T) cert).card)
    (Vs : Submodule (RatFunc (ZMod p)) (RatFunc (ZMod p) × RatFunc (ZMod p))) :
    RankMember Fr u q common xs ys T p where
  B := B
  hcoef := hcoef
  hpq := hpq
  hp3 := hp3
  hbd := hbd
  hB := hB
  ha := ha
  hb := hb
  hia := hia
  hib := hib
  cert := cert
  hOk := hOk
  hInt := hInt
  hReal := hReal
  hcard := hcard
  Vs := Vs
  mc := fun x => finrank (RatFunc (ZMod p)) ↥(Vs ⊓ Ucol p (cert x))
  mr := fun x => finrank (RatFunc (ZMod p)) ↥(Vs ⊓ Urow p (cert x))
  hmc2 := fun x => Submodule.finrank_mono inf_le_left
  hmr2 := fun x => Submodule.finrank_mono inf_le_left
  hmc := fun x _ => le_rfl
  hmr := fun x _ => le_rfl

end CatalanCore.Uniform.Content.RankProducer
