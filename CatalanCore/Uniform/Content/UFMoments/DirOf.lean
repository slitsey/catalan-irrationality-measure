module

public import CatalanCore.Uniform.Content.UFMoments.JType

@[expose] public section

/-!
# UF moments: the exact own-fiber direction of the representative node

`dirOf`: `d = (ℓ_{t₀} - g₀·ℓ)(1 - Σ g₀)⁻¹`; `own_dir_zero`: it kills the own-fiber moment (the
hypothesis `hz` of `jtype_node` / `hnum_jtype`) when `1 - Σ g₀` is a unit (`B₀ ≠ 0`).
-/

open Polynomial Matrix Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Arith.Hybrid.Periodic CatalanCore.Uniform.Content.UFMember
  CatalanCore.Uniform.Content.Hybrid

namespace CatalanCore.Uniform.Content.UFMoments

variable {p : ℕ} [Fact p.Prime] {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The exact own-fiber direction of a node. -/
noncomputable def dirOf (Fr : Frame) (c : ι → ℕ) (Q : Matrix ι ι (LocRing p)[X]) (t : ℕ)
    (σ : ι → (LocRing p)[X]) : GaussLoc p :=
  (ellL p Fr t - (sOwn c t σ ᵥ* (Dmat c Q)⁻¹) ⬝ᵥ (fun a => ellL p Fr (c a))) *
    Ring.inverse (1 - ∑ j, (sOwn c t σ ᵥ* (Dmat c Q)⁻¹) j)


theorem own_dir_zero (Fr : Frame) (c : ι → ℕ) (Q : Matrix ι ι (LocRing p)[X]) (t : ℕ)
    (σ : ι → (LocRing p)[X]) (hB : IsUnit (1 - ∑ j, (sOwn c t σ ᵥ* (Dmat c Q)⁻¹) j)) :
    (ellL p Fr t - dirOf Fr c Q t σ) -
      (sOwn c t σ ᵥ* (Dmat c Q)⁻¹) ⬝ᵥ (fun a => ellL p Fr (c a) - dirOf Fr c Q t σ) = 0 := by
  have h := Ring.inverse_mul_cancel _ hB
  have hlin : (sOwn c t σ ᵥ* (Dmat c Q)⁻¹) ⬝ᵥ (fun a => ellL p Fr (c a) - dirOf Fr c Q t σ) =
      (sOwn c t σ ᵥ* (Dmat c Q)⁻¹) ⬝ᵥ (fun a => ellL p Fr (c a)) -
        dirOf Fr c Q t σ * ∑ j, (sOwn c t σ ᵥ* (Dmat c Q)⁻¹) j :=
    dot_sub_const (sOwn c t σ ᵥ* (Dmat c Q)⁻¹) (fun a => ellL p Fr (c a)) (dirOf Fr c Q t σ)
  rw [hlin]
  unfold dirOf
  generalize Ring.inverse (1 - ∑ j, (sOwn c t σ ᵥ* (Dmat c Q)⁻¹) j) = I at h ⊢
  generalize ∑ j, (sOwn c t σ ᵥ* (Dmat c Q)⁻¹) j = S at h ⊢
  generalize (sOwn c t σ ᵥ* (Dmat c Q)⁻¹) ⬝ᵥ (fun a => ellL p Fr (c a)) = gl
  generalize ellL p Fr t = lt
  calc (lt - (lt - gl) * I) - (gl - (lt - gl) * I * S) = (lt - gl) * (1 - I * (1 - S)) := by ring
    _ = 0 := by rw [h]; ring

end CatalanCore.Uniform.Content.UFMoments
