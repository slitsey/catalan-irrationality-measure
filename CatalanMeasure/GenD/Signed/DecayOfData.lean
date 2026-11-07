module

public import CatalanMeasure.GenD.Signed.MarkedCap
public import CatalanMeasure.GenD.Analytic.DeltaSmall
public import CatalanMeasure.GenD.Signed.DesignConst

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Assembly
open Set Filter Polynomial
open CatalanMeasure.GenD CatalanMeasure.GenD.Analytic OAI.InternalCatalan CatalanMeasure.Parametric
open CatalanMeasure.Signed
noncomputable section

namespace Generic

open CatalanMeasure.GenD.Signed

def gapPredicate (dc : DesignConst) : ℝ → Prop := fun u => (dc.gstar : ℝ) ≤ |u|

/-- **`delta_small` on the nodes**, from the three bounds with `Z = (∏ (1 + ζ s_l))^m` and the node
field `δ`, and the weight bound with `β_ζ` and the constant `Cw` (GP Theorem 4.3 through
`weighted_atom_point_zeta_of_signed`).  `ζ`, `δ`, `Cw`, the window `G`, the cost and the rates
are parameters; the result carries no `ζ` and no `δ`. -/
theorem delta_small_nodes (dc : DesignConst)
    (tau : (N : ℕ) → Fin (dc.d0 * N) → ℝ) (G : ℝ → Prop)
    (hinj : ∀ N, Function.Injective (tau N))
    (hmem : ∀ N a, tau N a ∈ Ioo (-1 : ℝ) 1)
    (hzero : ∀ N a, tau N a ≠ 0)
    (hsupport : ∀ N a, G (realCoordinate (tau N a)))
    (target cost Psi0 α1 ζ Cw : ℝ) (hζ : 0 < ζ) (hCw : 0 ≤ Cw) (δ : ℝ → ℝ)
    (hfirst : FreeFirstBoundZ dc.toParameters G ζ δ target ((dc.n0 : ℝ) * cost))
    (hnear : FreeNearBoundZ dc.toParameters G (NodeSub tau) ζ δ
      target ((dc.n0 : ℝ) * cost) α1)
    (hlarge : FreeLargeBoundZ dc.toParameters G ζ δ target ((dc.n0 : ℝ) * cost) α1)
    (hweights : ∀ᶠ N : ℕ in atTop, ∀ p m : ℕ, p + m = dc.toParameters.n N →
      ∀ k : ℕ, k < dc.toParameters.n N → ∀ a : Fin (dc.d0 * N),
      |(rowCommonFactor dc.toParameters N).eval (tau N a)| *
        |restrictedWeight dc.toParameters N k (tau N) a| *
        CatalanMeasure.zetaBeta ζ p m k ≤
          Cw * (N : ℝ) * Real.exp ((Psi0 + δ (tau N a)) * N)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ x : ℝ,
      |x - catalan| ≤ Real.exp (-(((dc.n0 : ℝ) * cost + Psi0) * N)) →
      |aeval x (deltaPoly dc.toParameters N)| ≤
        Real.exp (-(((dc.n0 : ℝ)^2 * (target - Real.log 2 / 2) - ε) * (N : ℝ)^2)) := by
  have hpoint : WeightedAtomPointBinom dc.toParameters (5 * Cw) tau G
      target ((dc.n0 : ℝ) * cost + Psi0) :=
    weighted_atom_point_zeta_of_signed dc.toParameters dc.admissible hζ Cw hCw δ tau
      G (NodeSub tau)
      (fun N m y a ha h => ⟨a, ha, h⟩) hfirst hnear hlarge le_rfl le_rfl le_rfl hweights
  exact delta_small_binom dc.toParameters dc.admissible (5 * Cw) (by positivity) tau G hinj hmem
    hzero hsupport target ((dc.n0 : ℝ) * cost + Psi0)
    ((dc.n0 : ℝ)^2 * (target - Real.log 2 / 2)) rfl hpoint

end Generic

end
end CatalanMeasure.GenD.Signed.Data.Assembly

#print axioms CatalanMeasure.GenD.Signed.Data.Assembly.Generic.delta_small_nodes
