module

public import CatalanCore.Uniform.Content.Member.FrameDigamma

@[expose] public section

/-!
# The hybrid rank layer on a deletion member (lane H5, Theorem SD, rank layer)

`member_gle_rank` is the H1 theorem `gle_det_digamma` applied to the MEMBER's own matrix: index
`S ⊕ κ` (retained common nodes and the full border), nodes `Sum.elim common xs` and
`Sum.elim common ys`, and the member's own kernel data `(L, P, s, ρ, σ, R0, V, cost)`.  The
price is `h + R0 - (F₀ + (|Y| dim V - Σ cost))` with `h = |T| + m`: no leading debit, because
`h` is the size of the member itself.  Nothing about the full determinant is used.
-/

open Polynomial Finset Module CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Rect CatalanCore.Uniform.Content.Hybrid

namespace CatalanCore.Uniform.Content.Member

variable {p : ℕ} [hp : Fact p.Prime] {ι κ : Type} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ]

open scoped Classical in
/-- **Rank layer of a deletion member.** -/
theorem member_gle_rank (Fr : Frame) (u q : Fin Fr.d → ℕ)
    (hu : ∀ j, Fr.μ j = u j / q j) (hq : ∀ j, 0 < q j)
    (common : ι → ℕ) (xs ys : κ → ℕ) (hc : Function.Injective common)
    (hxc : ∀ i j, xs i ≠ common j) (hyc : ∀ i j, ys i ≠ common j) (hxy : ∀ i j, xs i ≠ ys j)
    (T : Finset ι) (B : ℕ)
    (hcoef : ∀ j, (frameDigamma Fr u q).c j ∈ S p) (hpq : ∀ j, ¬ p ∣ (frameDigamma Fr u q).q j)
    (hp3 : 3 ≤ p) (hbd : ∀ j, (frameDigamma Fr u q).q j * B + (frameDigamma Fr u q).u j ≤ p ^ 2)
    (hB : B < p ^ 2)
    (ha : ∀ i, memberRows common xs T i ≤ B) (hb : ∀ j, memberCols common ys T j ≤ B)
    (L P : Matrix (T ⊕ κ) (T ⊕ κ) (LocRing p)) (hL : redQ p L.det ≠ 0) (hP : redQ p P.det ≠ 0)
    (s : Finset (T ⊕ κ))
    (hrow : ∀ i ∈ s, ∀ j, (L * ((frameDigamma Fr u q).poleSplit B hcoef hpq hp3 hbd).K
      (memberRows common xs T) (memberCols common ys T) * P) i j = 0)
    (hcol : ∀ i, ∀ j ∈ s, (L * ((frameDigamma Fr u q).poleSplit B hcoef hpq hp3 hbd).K
      (memberRows common xs T) (memberCols common ys T) * P) i j = 0)
    (ρ σ : s → ZMod p)
    (hu' : ∀ (i : s) k, redQ p (L i k) ≠ 0 → (memberRows common xs T k : ZMod p) = ρ i)
    (hv : ∀ (j : s) l, redQ p (P l j) ≠ 0 → (memberCols common ys T l : ZMod p) = σ j)
    (R0 : ℕ) (hR : R0 + s.card = Fintype.card (T ⊕ κ))
    (Vs : Submodule (RatFunc (ZMod p)) (RatFunc (ZMod p) × RatFunc (ZMod p)))
    (cost : Cond (fun i => rfH p (ρ i)) (fun j => rfH p (σ j)) → ℕ)
    (hcost : ∀ c, finrank (RatFunc (ZMod p)) (LinearMap.range (condMap (fun i => rfH p (ρ i))
        (fun i => mapPair (rfH p) (load (fun k => red p ((frameDigamma Fr u q).Lf p
          (memberRows common xs T k))) (fun k => redQ p (L i k))))
        (fun j => rfH p (σ j))
        (fun j => mapPair (rfH p) (load (fun l => red p ((frameDigamma Fr u q).Lf p
          (memberCols common ys T l))) (fun l => redQ p (P l j))))
        Vs c)) ≤ cost c) :
    GLE p (Fintype.card (T ⊕ κ) + R0 -
      (Fintype.card {j : s // load (fun l => red p ((frameDigamma Fr u q).Lf p
          (memberCols common ys T l))) (fun l => redQ p (P l j)) = 0} +
        ((colRes (fun j => rfH p (σ j))).card * finrank (RatFunc (ZMod p)) Vs -
          ∑ c, cost c)))
      (FullN Fr (fun a : T => common a.1) xs ys (X : ℚ[X])).det := by
  refine member_gle_of_loewner Fr (frameDigamma Fr u q).f (frameDigamma Fr u q).e
    (mn_eq_loewner Fr u q hu hq) common xs ys hc hxc hyc hxy T ?_
  exact gle_det_digamma (frameDigamma Fr u q) (memberRows common xs T) (memberCols common ys T)
    B hcoef hpq hp3 hbd hB ha hb L P hL hP s hrow hcol ρ σ hu' hv R0 hR Vs cost hcost

end CatalanCore.Uniform.Content.Member
