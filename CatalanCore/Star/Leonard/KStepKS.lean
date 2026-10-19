module

public import CatalanCore.Star.Leonard.KStepY
public import CatalanCore.Star.Leonard.ChainDS
public import CatalanCore.Linalg.KrylovTri
public import CatalanCore.Linalg.KrylovTransfer

/-!
# The K-step identity (package H5, KS)

At the `g = 0` instance `I₁ = (m + (n'+1), m, S = n')` (so `n = n'+1`), `Ã = E Cᵀ` with `E = Π R`,
`Cᵀ = Rᵀ Π`, `R = [c_1..c_{n'}]`.  With the Darboux map `X : I₁ → I₂ = (m + n', m, n'+1)`:

* `kdet_That`: `u_y(T^, z) = (∏ ∏ l(-j)) · det[z_0, …, z_{n'-1}]`, `z_j = Cᵀ c_{-j}`;
* `KS`: `u(Ã₁, Π c₀) · u(T~', w) = det[W | Π c₀ | E] · u(Ã₂, w) · u_y(T^, z)` for any `w`
  (hypothesis: `det [W' | X E] ≠ 0` and cyclicity of `T~'`).
-/

@[expose] public section

open Finset Matrix

namespace CatalanCore.Star.Leonard

variable {F : Type*} [Field F]

section YChain

variable [CharZero F] (m n S : ℕ) (hm : 1 ≤ m) (θ : F) (hθ : Gen θ)

/-- `z_j = Cᵀ c_{-j}` -/
noncomputable def zvec (j : ℕ) : Fin S → F :=
  ((Rm m n S θ)ᵀ * projB (m + n) θ (bX m (S : ℤ)) (bY m (S : ℤ))) *ᵥ
    wcol (m + n) θ (-(j : ℤ))

include hm hθ in
theorem kdet_That
    (hΔ : IsUnit ((Wb (m + n) θ (bX m (S : ℤ)))ᵀ * Wb (m + n) θ (bY m (S : ℤ))).det)
    (hS : 1 ≤ S) :
    kdet (That m n S θ) (zvec m n S θ 0) =
      (∏ k : Fin S, ∏ j ∈ Finset.range k,
          (-tau (m + n) m S θ (-θ - (((-(j : ℤ)) : ℤ) : F)))) *
        (colMat fun j => zvec m n S θ j).det := by
  obtain ⟨hPW, -⟩ := projB_props m n S θ hΔ
  have hdual := That_Ct m n S hm θ hθ hΔ
  refine kdet_chain (That m n S θ) (fun j => zvec m n S θ j)
    (fun j => -tau (m + n) m S θ (-θ - (((-(j : ℤ)) : ℤ) : F))) ?_
  intro j hj
  obtain ⟨d, w, hw, h⟩ := Ttil_rel m n S hm θ hθ (-(j : ℤ)) (by omega)
  have e1 : wcol (m + n) θ (-(j : ℤ) - 1) = wcol (m + n) θ (-(((j + 1 : ℕ)) : ℤ)) := by
    congr 1; push_cast; ring
  have hCw : ((Rm m n S θ)ᵀ * projB (m + n) θ (bX m (S : ℤ)) (bY m (S : ℤ))) *ᵥ w = 0 := by
    rw [← Matrix.mulVec_mulVec, hPW w hw, Matrix.mulVec_zero]
  have hT : That m n S θ *ᵥ zvec m n S θ j = ((Rm m n S θ)ᵀ * projB (m + n) θ (bX m (S : ℤ))
      (bY m (S : ℤ))) *ᵥ (Ttil (m + n) m S θ *ᵥ wcol (m + n) θ (-(j : ℤ))) := by
    unfold zvec
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hdual]
  have e2 : (-(j : ℤ) + 1) = -(((j - 1 : ℕ)) : ℤ) ∨ j = 0 := by
    rcases Nat.eq_zero_or_pos j with h0 | h0
    · exact Or.inr h0
    · left; rw [Nat.cast_sub h0]; push_cast; ring
  have key : That m n S θ *ᵥ zvec m n S θ j - (-tau (m + n) m S θ (-θ - (((-(j : ℤ)) : ℤ) : F))) •
      zvec m n S θ (j + 1) = d • zvec m n S θ j + (-sigma (m + n) m S θ (-θ - ((-(j : ℤ) : ℤ) : F) - 1)) •
        (((Rm m n S θ)ᵀ * projB (m + n) θ (bX m (S : ℤ)) (bY m (S : ℤ))) *ᵥ
          wcol (m + n) θ (-(j : ℤ) + 1)) := by
    rw [hT, h]
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, hCw, add_zero]
    rw [e1]
    unfold zvec
    abel
  rw [key]
  refine Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, by simp, rfl⟩)) ?_
  rcases e2 with e2 | e2
  · refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨j - 1, ?_, ?_⟩)
    · simp only [Set.mem_Iio]; omega
    · unfold zvec; rw [e2]
  · subst e2
    have : sigma (m + n) m S θ (-θ - (((-((0 : ℕ) : ℤ)) : ℤ) : F) - 1) = 0 := by
      simpa using sigma_at_zero (m + n) m S θ
    rw [this]; simp

end YChain

end CatalanCore.Star.Leonard
