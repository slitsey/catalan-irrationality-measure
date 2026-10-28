module

public import CatalanCore.Uniform.Content.UFWedge.Reduce

@[expose] public section

/-!
# UF wedge, W1: a nonzero evaluation at `X = u₀` certifies the kill wedge (lane H9)

`evP u₀ : ℤ_(p)[X] →+* 𝔽_p` reduces the coefficients and evaluates at `u₀`.  If the cross wedge of
the two bordered fibers, computed in `𝔽_p` from `evP`, is nonzero, then the cross wedge in
`𝔽_p(X)` is nonzero (it is the image of a polynomial whose value at `u₀` is the `𝔽_p` cross wedge),
hence the kill wedge is nonzero.  No denominators are inverted: the cross wedge is the polynomial
`B_J A_K - A_J B_K` of bordered determinants, so the "unit at `u₀`" hypothesis of the rational
computation is not needed for the implication.
-/

open Polynomial Matrix Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Arith.Hybrid.Periodic CatalanCore.Uniform.Content.UFMember
  CatalanCore.Uniform.Content.Hybrid CatalanCore.Uniform.Content.UFMoments

namespace CatalanCore.Uniform.Content.UFWedge

variable {p N : ℕ} [Fact p.Prime] {Fr : Frame} {ι κ : Type} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ]

/-- Reduction of coefficients modulo `p` followed by evaluation at `u₀`. -/
noncomputable def evP (p : ℕ) [Fact p.Prime] (u₀ : ZMod p) : (LocRing p)[X] →+* ZMod p :=
  (Polynomial.evalRingHom u₀).comp (Polynomial.mapRingHom (redQ p))

/-- Reduction of coefficients modulo `p` (to `𝔽_p[X]`). -/
noncomputable def psiP (p : ℕ) [Fact p.Prime] : (LocRing p)[X] →+* (ZMod p)[X] :=
  Polynomial.mapRingHom (redQ p)

theorem phiP_eq_comp : phiP p = (algebraMap (ZMod p)[X] (RatFunc (ZMod p))).comp (psiP p) := rfl

theorem evP_eq_comp (u₀ : ZMod p) : evP p u₀ = (Polynomial.evalRingHom u₀).comp (psiP p) := rfl

/-- The cross wedge in `𝔽_p(X)` vanishes iff the polynomial cross wedge does; hence a nonzero
value at `u₀` gives a nonzero wedge. -/
theorem cross_phiP_ne_of_eval (Q : Matrix ι ι (LocRing p)[X]) (c : ι → ℕ)
    (σ₀ σ : ι → (LocRing p)[X]) (z₀ z : (LocRing p)[X]) (k₀ k : ZMod p) (u₀ : ZMod p)
    (h : (fibOf (evP p u₀) Fr c Q σ₀ z₀ k₀).cross (fibOf (evP p u₀) Fr c Q σ z k) ≠ 0) :
    (fibOf (phiP p) Fr c Q σ₀ z₀ k₀).cross (fibOf (phiP p) Fr c Q σ z k) ≠ 0 := by
  intro h0
  apply h
  have e1 : (fibOf (phiP p) Fr c Q σ₀ z₀ k₀) =
      (fibOf (psiP p) Fr c Q σ₀ z₀ k₀).map (algebraMap (ZMod p)[X] (RatFunc (ZMod p))) := rfl
  have e2 : (fibOf (phiP p) Fr c Q σ z k) =
      (fibOf (psiP p) Fr c Q σ z k).map (algebraMap (ZMod p)[X] (RatFunc (ZMod p))) := rfl
  rw [e1, e2, ← FibD.map_cross] at h0
  have hp : (fibOf (psiP p) Fr c Q σ₀ z₀ k₀).cross (fibOf (psiP p) Fr c Q σ z k) = 0 :=
    (RatFunc.algebraMap_injective (ZMod p)) (by rw [h0, map_zero])
  have e3 : (fibOf (evP p u₀) Fr c Q σ₀ z₀ k₀) =
      (fibOf (psiP p) Fr c Q σ₀ z₀ k₀).map (Polynomial.evalRingHom u₀) := rfl
  have e4 : (fibOf (evP p u₀) Fr c Q σ z k) =
      (fibOf (psiP p) Fr c Q σ z k).map (Polynomial.evalRingHom u₀) := rfl
  rw [e3, e4, ← FibD.map_cross, hp, map_zero]

section Wedge

variable (D : PoleData Fr p N) (hN : N < p * p) (c : ι → ℕ) (xs ys : κ → ℕ)
  (hc : ∀ a, c a < N) (hx : ∀ i, xs i < N) (hy : ∀ j, ys j < N)

/-- **(W1) Column kills from a nonzero evaluation.** -/
theorem wedgeC_ne_zero_of_eval (t0 : ℕ) (ht0 : t0 < N) (t : κ) (u₀ : ZMod p)
    (h : (fibOf (evP p u₀) Fr c (sLift c xs ys (hint_of_poleData D hN hc hx hy)).toBlocks₁₁
        (loewRow p Fr c t0) (PF1 p Fr t0) ((t0 : ℕ) : ZMod p)).cross
      (fibOf (evP p u₀) Fr c (sLift c xs ys (hint_of_poleData D hN hc hx hy)).toBlocks₁₁
        (fun a => (sLift c xs ys (hint_of_poleData D hN hc hx hy)).toBlocks₁₂ a t)
        (PF1 p Fr (ys t)) ((ys t : ℕ) : ZMod p)) ≠ 0) :
    wedgeC (sLift c xs ys (hint_of_poleData D hN hc hx hy)) Fr c ys
      (dirOf Fr c (sLift c xs ys (hint_of_poleData D hN hc hx hy)).toBlocks₁₁ t0
        (loewRow p Fr c t0)) t ≠ 0 :=
  wedgeC_ne_zero_of_cross D hN c xs ys hc hx hy t0 ht0 t (cross_phiP_ne_of_eval _ c _ _ _ _ _ _ u₀ h)

/-- **(W1) Row kills from a nonzero evaluation.** -/
theorem wedgeR_ne_zero_of_eval (t0 : ℕ) (ht0 : t0 < N) (t : κ) (u₀ : ZMod p)
    (h : (fibOf (evP p u₀) Fr c (sLift c xs ys (hint_of_poleData D hN hc hx hy)).toBlocks₁₁
        (loewRow p Fr c t0) (PF1 p Fr t0) ((t0 : ℕ) : ZMod p)).cross
      (fibOf (evP p u₀) Fr c (sLift c xs ys (hint_of_poleData D hN hc hx hy)).toBlocks₁₁
        (fun a => (sLift c xs ys (hint_of_poleData D hN hc hx hy)).toBlocks₂₁ t a)
        (PF1 p Fr (xs t)) ((xs t : ℕ) : ZMod p)) ≠ 0) :
    wedgeR (sLift c xs ys (hint_of_poleData D hN hc hx hy)) Fr c xs
      (dirOf Fr c (sLift c xs ys (hint_of_poleData D hN hc hx hy)).toBlocks₁₁ t0
        (loewRow p Fr c t0)) t ≠ 0 :=
  wedgeR_ne_zero_of_cross D hN c xs ys hc hx hy t0 ht0 t (cross_phiP_ne_of_eval _ c _ _ _ _ _ _ u₀ h)

end Wedge

end CatalanCore.Uniform.Content.UFWedge
