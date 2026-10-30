module
public import CatalanMeasure.GenD.Uniform.W.HYPlus.HySys
@[expose] public section
set_option Elab.async false

/-!
# Structural no-go: a single constant profile subspace `V` cannot be a packet of the `hySys` tiling

`Ident.dom` (`W/Prof/Count`) asks that every product atom `x ↦ (emb (x_d))_d` lies in `S.dom`.
For the mixed H+ / H- slot system `hySys` the domain has vanishing off-diagonal blocks, so the
H+ slots only see the first `K` profile coordinates and the H- slots only the last `K`.  A single
`V` serving all slots must therefore be zero.  (Mixed packets need atoms of the form
`x_{(τ,t)} = π_τ (emb y_t)` or a common slot polynomial; see `evidence/claude/G8b/NOTES.md`.)
-/

namespace CatalanMeasure.GenD.Uniform.W.Charts2
open CatalanMeasure.Parametric CatalanMeasure.GenD.Uniform.W.HYPlus
  CatalanMeasure.GenD.Uniform.W.SlotsT
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

/-- Every product atom family through one linear embedding `E` lies in `hyDom` only if `E = 0`. -/
theorem hy_prod_dom_trivial {K D d : ℕ} (hD : 0 < D) (k0 : ℤ)
    (E : (Fin d → ZMod p) →ₗ[ZMod p] (Fin (K + K) → ZMod p))
    (h : ∀ x : Fin (D + D) → Fin d → ZMod p, (fun d' => E (x d')) ∈ hyDom P N p K D k0) :
    ∀ y, E y = 0 := by
  intro y
  obtain ⟨h12, h21, -⟩ := (mem_hyDom (P := P) (N := N) k0 (fun _ => E y)).mp (h (fun _ => y))
  funext k
  refine Fin.addCases (fun a => ?_) (fun b => ?_) k
  · have := congrFun (congrFun h21 ⟨0, hD⟩) a
    simpa [blk21] using this
  · have := congrFun (congrFun h12 ⟨0, hD⟩) b
    simpa [blk12] using this

end
end CatalanMeasure.GenD.Uniform.W.Charts2
