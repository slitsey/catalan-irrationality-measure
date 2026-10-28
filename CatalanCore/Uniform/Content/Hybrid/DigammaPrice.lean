module

public import CatalanCore.Uniform.Content.Hybrid.Frame
public import CatalanCore.Uniform.Content.Hybrid.Digamma

@[expose] public section

/-!
# The hybrid rank-layer price of a rational digamma frame at one prime

`gle_det_digamma`: for a rational digamma frame, a prime `p ≥ 3` with `p ∤ q_j`, `c_j` `p`-integral,
nodes `≤ B` with `B < p²` and `q_j B + u_j ≤ p²` (the compact band), exact constant kernel bases
`L, P` of the leading fiber blocks, fiber supports, `R0 + |s| = h`, any constant subspace `V` and
certified cost bounds,

  `denexp_p(det Φ) ≤ h + R0 - (F₀ + (|Y|·dim V - Σ cost))`.

The digit hypothesis is automatic on the band (`digitHyp_of_lt`).
-/

open Polynomial CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid Finset Module

namespace CatalanCore.Uniform.Content.Hybrid

variable {p : ℕ} [hp : Fact p.Prime] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- On the band `B < p²` distinct same-residue nodes have digits differing by a unit. -/
theorem digitHyp_of_lt {a b : ι → ℕ} {B : ℕ} (ha : ∀ i, a i ≤ B) (hb : ∀ j, b j ≤ B)
    (hB : B < p ^ 2) : DigitHyp p B a b := by
  refine ⟨ha, hb, fun i j h hne hz => hne ?_⟩
  have hm := natCast_eq_of_mod h
  have hp0 := hp.out.pos
  have hda : a i / p < p := by
    rw [Nat.div_lt_iff_lt_mul hp0]; have := ha i; nlinarith
  have hdb : b j / p < p := by
    rw [Nat.div_lt_iff_lt_mul hp0]; have := hb j; nlinarith
  have hdvd : (p : ℤ) ∣ digitDiff p a b i j := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1 hz
  have habs : |digitDiff p a b i j| < (p : ℤ) := by
    have h1 : ((a i / p : ℕ) : ℤ) < p := by exact_mod_cast hda
    have h2 : ((b j / p : ℕ) : ℤ) < p := by exact_mod_cast hdb
    have h3 : (0 : ℤ) ≤ ((a i / p : ℕ) : ℤ) := Int.natCast_nonneg _
    have h4 : (0 : ℤ) ≤ ((b j / p : ℕ) : ℤ) := Int.natCast_nonneg _
    rw [abs_lt, digitDiff]; constructor <;> omega
  have h0 := Int.eq_zero_of_abs_lt_dvd hdvd habs
  rw [digitDiff] at h0
  have hq : a i / p = b j / p := by omega
  have h1 := Nat.div_add_mod (a i) p
  have h2 := Nat.div_add_mod (b j) p
  rw [hq, hm] at h1
  omega

open scoped Classical in
/-- **Hybrid rank-layer price of a rational digamma frame at one prime.** -/
theorem gle_det_digamma {J : Type*} [Fintype J] (Dg : DigammaFrame J) (a b : ι → ℕ) (B : ℕ)
    (hc : ∀ j, Dg.c j ∈ S p) (hpq : ∀ j, ¬ p ∣ Dg.q j) (hp3 : 3 ≤ p)
    (hbd : ∀ j, Dg.q j * B + Dg.u j ≤ p ^ 2) (hB : B < p ^ 2)
    (ha : ∀ i, a i ≤ B) (hb : ∀ j, b j ≤ B)
    (L P : Matrix ι ι (LocRing p)) (hL : redQ p L.det ≠ 0) (hP : redQ p P.det ≠ 0)
    (s : Finset ι)
    (hrow : ∀ i ∈ s, ∀ j, (L * (Dg.poleSplit B hc hpq hp3 hbd).K a b * P) i j = 0)
    (hcol : ∀ i, ∀ j ∈ s, (L * (Dg.poleSplit B hc hpq hp3 hbd).K a b * P) i j = 0)
    (ρ σ : s → ZMod p)
    (hu : ∀ (i : s) k, redQ p (L i k) ≠ 0 → (a k : ZMod p) = ρ i)
    (hv : ∀ (j : s) l, redQ p (P l j) ≠ 0 → (b l : ZMod p) = σ j)
    (R0 : ℕ) (hR : R0 + s.card = Fintype.card ι)
    (Vs : Submodule (RatFunc (ZMod p)) (RatFunc (ZMod p) × RatFunc (ZMod p)))
    (cost : Cond (fun i => rfH p (ρ i)) (fun j => rfH p (σ j)) → ℕ)
    (hcost : ∀ c, finrank (RatFunc (ZMod p)) (LinearMap.range (condMap (fun i => rfH p (ρ i))
        (fun i => mapPair (rfH p) (load (fun k => red p (Dg.Lf p (a k)))
          (fun k => redQ p (L i k))))
        (fun j => rfH p (σ j))
        (fun j => mapPair (rfH p) (load (fun l => red p (Dg.Lf p (b l)))
          (fun l => redQ p (P l j))))
        Vs c)) ≤ cost c) :
    GLE p (Fintype.card ι + R0 -
      (Fintype.card {j : s // load (fun l => red p (Dg.Lf p (b l)))
          (fun l => redQ p (P l j)) = 0} +
        ((colRes (fun j => rfH p (σ j))).card * finrank (RatFunc (ZMod p)) Vs -
          ∑ c, cost c))) (loewner a b Dg.f Dg.e).det :=
  gle_det_frame (Dg.poleSplit B hc hpq hp3 hbd) (digitHyp_of_lt ha hb hB) L P hL hP s hrow hcol
    ρ σ hu hv R0 hR Vs cost hcost

end CatalanCore.Uniform.Content.Hybrid
