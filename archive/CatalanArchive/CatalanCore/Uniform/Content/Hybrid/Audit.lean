module

public import CatalanCore.Uniform.Content.Hybrid.DigammaPrice
public import CatalanCore.Uniform.Content.Hybrid.Blocks
public import CatalanCore.Uniform.Content.Hybrid.Costs

@[expose] public section

/-! Axiom audit of the hybrid rank layer (H1), plus an API instance on a tiny frame. -/

open Polynomial CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid

namespace CatalanCore.Uniform.Content.Hybrid

#print axioms LeadingData.gle_det
#print axioms LeadingData.gle_det_R0
#print axioms bary_off
#print axioms bary_node
#print axioms loadMat_rank_add_le
#print axioms loadMat_rank_add_le_of_bounds
#print axioms compress_entry
#print axioms omega_load_eq_zero
#print axioms LeadingData.nextRed_eq_loadMat
#print axioms card_zeroLoad_le_finrank_ker_lam
#print axioms gle_det_hybrid
#print axioms gle_det_hybrid_of_bounds
#print axioms gle_det_min
#print axioms PoleSplit.hB
#print axioms PoleSplit.hCr
#print axioms PoleSplit.disp
#print axioms horth_of_split
#print axioms gle_det_frame
#print axioms DigammaFrame.poleSplit
#print axioms digitHyp_of_lt
#print axioms gle_det_digamma
#print axioms isUnit_det_blockMat
#print axioms eq_blockMat
#print axioms BlockKernel.hL
#print axioms BlockKernel.hP
#print axioms BlockKernel.hrow'
#print axioms BlockKernel.hcol'
#print axioms BlockKernel.gle_det_frame
#print axioms condMap_rank_le
#print axioms condMap_rank_eq_zero
#print axioms condMap_rank_le_quot

instance fact_prime_five : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- The harmonic frame (one pole, `μ = 1`, `c = 1`). -/
def harmonicFrame : DigammaFrame Unit := ⟨fun _ => 1, fun _ => 1, fun _ => 1⟩

/-- Instance test: the full API instantiates on the `1 × 1` harmonic frame at `p = 5`
(empty kernel set, `V = 0`), giving the crude price `2`. -/
example : GLE 5 2 (loewner (ι := Fin 1) (fun _ => 1) (fun _ => 1)
    harmonicFrame.f harmonicFrame.e).det := by
  classical
  have hs : ∀ x : (∅ : Finset (Fin 1)), False := fun x => absurd x.2 (Finset.notMem_empty _)
  have h := gle_det_digamma (p := 5) harmonicFrame (fun _ => 1) (fun _ => 1) 1
    (fun _ => (Good.one (ℓ := 5)).1) (fun _ => by norm_num [harmonicFrame]) (by norm_num)
    (fun _ => by norm_num [harmonicFrame]) (by norm_num) (fun _ => le_rfl) (fun _ => le_rfl)
    1 1 (by simp) (by simp) ∅ (fun i hi => absurd hi (Finset.notMem_empty _))
    (fun _ j hj => absurd hj (Finset.notMem_empty _))
    (fun x => (hs x).elim) (fun x => (hs x).elim) (fun x => (hs x).elim) (fun x => (hs x).elim)
    1 (by simp) ⊥ (fun _ => 0)
    (fun c => (LinearMap.finrank_range_le _).trans (by simp))
  exact h.mono (by simp only [Fintype.card_fin]; omega)

end CatalanCore.Uniform.Content.Hybrid
