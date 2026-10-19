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

section Setup

variable [CharZero F] (m n S : ℕ) (θ : F)

lemma projB_idem
    (hΔ : IsUnit ((Wb (m + n) θ (bX m (S : ℤ)))ᵀ * Wb (m + n) θ (bY m (S : ℤ))).det) :
    projB (m + n) θ (bX m (S : ℤ)) (bY m (S : ℤ)) * projB (m + n) θ (bX m (S : ℤ)) (bY m (S : ℤ)) =
      projB (m + n) θ (bX m (S : ℤ)) (bY m (S : ℤ)) := by
  obtain ⟨hPW, hPc⟩ := projB_props m n S θ hΔ
  refine CatalanCore.mul_eq_of_mulVec _ _ fun v => ?_
  obtain ⟨a, ha⟩ := hPc v
  have h0 := hPW _ ⟨a, rfl⟩
  rw [← Matrix.mulVec_mulVec]
  calc _ = projB (m + n) θ (bX m (S : ℤ)) (bY m (S : ℤ)) *ᵥ (v - Wb (m + n) θ (bY m (S : ℤ)) *ᵥ a) :=
        congrArg _ ha
    _ = _ := by
      rw [Matrix.mulVec_sub]
      have h0' : projB (m + n) θ (bX m (S : ℤ)) (bY m (S : ℤ)) *ᵥ
          (Wb (m + n) θ (bY m (S : ℤ)) *ᵥ a) = 0 := h0
      rw [h0', sub_zero]

lemma Nsum_apply {K : ℕ} (c : ℕ → Fin K → F) (s : ℕ) (a b : Fin K) :
    Nsum c s a b = ∑ j : Fin s, c ((j : ℕ) + 1) a * c ((j : ℕ) + 1) b := by
  induction s with
  | zero => simp [Nsum]
  | succ s ih =>
    rw [Nsum_succ, Matrix.add_apply, ih, Fin.sum_univ_castSucc]
    simp [Matrix.vecMulVec_apply]

lemma Nsum_eq_Rm_mul :
    Nsum (fun y : ℕ => wcol (m + n) θ (y : ℤ)) S = Rm m n S θ * (Rm m n S θ)ᵀ := by
  ext a b
  rw [Nsum_apply]
  simp [Matrix.mul_apply, Rm]

end Setup

section KS

variable [CharZero F] (m n' : ℕ) (hm : 1 ≤ m) (θ : F) (hθ : Gen θ)

include hm hθ in
/-- **K-step identity** (`g = 0`): with `v = Π c₀`, `E = Π R`, `D₁ = det [W | v | E]`,
`u(Ã₁, v) · u(T~', w) = D₁ · u(Ã₂, w) · u_y(T^, z)`, where `z = Cᵀ v`. -/
theorem KS_transfer
    (hΔ : IsUnit ((Wb (m + (n' + 1)) θ (bX m (n' : ℤ)))ᵀ *
      Wb (m + (n' + 1)) θ (bY m (n' : ℤ))).det)
    (hΔ' : IsUnit ((Wb (m + n') θ (bX m ((n' + 1 : ℕ) : ℤ)))ᵀ *
      Wb (m + n') θ (bY m ((n' + 1 : ℕ) : ℤ))).det)
    (w : Fin (m + n') → F)
    (hw : CatalanCore.bkdet (Wb (m + n') θ (bY m ((n' + 1 : ℕ) : ℤ)))
      (Ttil (m + n') m (n' + 1) θ) w ≠ 0)
    (hD2 : (CatalanCore.bmat (Wb (m + n') θ (bY m ((n' + 1 : ℕ) : ℤ)))
      (Xm (m + n') m n' θ * (projB (m + (n' + 1)) θ (bX m (n' : ℤ)) (bY m (n' : ℤ)) *
        Rm m (n' + 1) n' θ))).det ≠ 0) :
    CatalanCore.bkdet (Wb (m + (n' + 1)) θ (bY m (n' : ℤ))) (Atil m (n' + 1) n' θ)
        (projB (m + (n' + 1)) θ (bX m (n' : ℤ)) (bY m (n' : ℤ)) *ᵥ wcol (m + (n' + 1)) θ 0) *
      CatalanCore.bkdet (Wb (m + n') θ (bY m ((n' + 1 : ℕ) : ℤ))) (Ttil (m + n') m (n' + 1) θ) w =
    (CatalanCore.bmat (Wb (m + (n' + 1)) θ (bY m (n' : ℤ)))
        (Matrix.of fun i j => Fin.cases
          ((projB (m + (n' + 1)) θ (bX m (n' : ℤ)) (bY m (n' : ℤ)) *ᵥ wcol (m + (n' + 1)) θ 0) i)
          (fun j' => (projB (m + (n' + 1)) θ (bX m (n' : ℤ)) (bY m (n' : ℤ)) *
            Rm m (n' + 1) n' θ) i j') j)).det *
      CatalanCore.bkdet (Wb (m + n') θ (bY m ((n' + 1 : ℕ) : ℤ))) (Atil m n' (n' + 1) θ) w *
      kdet (That m (n' + 1) n' θ) (zvec m (n' + 1) n' θ 0) := by
  set Pj := projB (m + (n' + 1)) θ (bX m (n' : ℤ)) (bY m (n' : ℤ)) with hPj
  set Rm1 := Rm m (n' + 1) n' θ with hRm
  set E := Pj * Rm1 with hE
  set C := Pjᵀ * Rm1 with hC
  set W := Wb (m + (n' + 1)) θ (bY m (n' : ℤ)) with hW
  set W' := Wb (m + n') θ (bY m ((n' + 1 : ℕ) : ℤ)) with hW'
  set v := Pj *ᵥ wcol (m + (n' + 1)) θ 0 with hv
  have hidem := projB_idem m (n' + 1) n' θ hΔ
  have hA1 : Atil m (n' + 1) n' θ = E * Cᵀ := by
    unfold Atil
    rw [Nsum_eq_Rm_mul]
    simp only [hE, hC, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    rfl
  -- L5
  have h1 := CatalanCore.bkdet_mul_transpose W E C v
  rw [← hA1] at h1
  -- the intertwiners
  have hXA : Xm (m + n') m n' θ * Atil m (n' + 1) n' θ = Atil m n' (n' + 1) θ * Xm (m + n') m n' θ :=
    CatalanCore.mul_eq_of_mulVec _ _ fun x => by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      exact Xm_Atil m n' hm θ hθ hΔ hΔ' x
  have hXT : Xm (m + n') m n' θ * Ttil (m + (n' + 1)) m n' θ =
      (Ttil (m + n') m (n' + 1) θ + betaD (m + n') m n' θ • (1 : Matrix (Fin (m + n')) (Fin (m + n')) F)) *
        Xm (m + n') m n' θ :=
    CatalanCore.mul_eq_of_mulVec _ _ fun x => by
      simp only [← Matrix.mulVec_mulVec]
      rw [Matrix.add_mulVec]
      have hx := Xm_Ttil (m + n') m n' hm θ hθ (by omega) x
      have hb : (betaD (m + n') m n' θ • (1 : Matrix (Fin (m + n')) (Fin (m + n')) F)) *ᵥ
          (Xm (m + n') m n' θ *ᵥ x) = betaD (m + n') m n' θ • (Xm (m + n') m n' θ *ᵥ x) := by
        simp [Matrix.smul_mulVec]
      rw [hb]
      exact hx
  set Φ := Xm (m + n') m n' θ * E with hΦ
  set Ahat := Cᵀ * E with hAhat
  have hΦA : Atil m n' (n' + 1) θ * Φ = Φ * Ahat := by
    calc Atil m n' (n' + 1) θ * Φ = (Atil m n' (n' + 1) θ * Xm (m + n') m n' θ) * E := by
          rw [hΦ, Matrix.mul_assoc]
      _ = (Xm (m + n') m n' θ * Atil m (n' + 1) n' θ) * E := by rw [hXA]
      _ = Xm (m + n') m n' θ * (E * Cᵀ * E) := by rw [hA1, Matrix.mul_assoc]
      _ = Φ * Ahat := by rw [hΦ, hAhat]; simp only [Matrix.mul_assoc]
  have hΦT : (Ttil (m + n') m (n' + 1) θ + betaD (m + n') m n' θ • (1 : Matrix (Fin (m + n')) (Fin (m + n')) F)) * Φ =
      Φ * That m (n' + 1) n' θ := by
    calc _ = (Ttil (m + n') m (n' + 1) θ + betaD (m + n') m n' θ •
          (1 : Matrix (Fin (m + n')) (Fin (m + n')) F)) * Xm (m + n') m n' θ * E := by
          rw [hΦ, Matrix.mul_assoc]
      _ = Xm (m + n') m n' θ * Ttil (m + (n' + 1)) m n' θ * E := by rw [hXT]
      _ = Xm (m + n') m n' θ * (Ttil (m + (n' + 1)) m n' θ * E) := by rw [Matrix.mul_assoc]
      _ = Xm (m + n') m n' θ * (E * That m (n' + 1) n' θ) := by
          rw [hE, hRm, Ttil_E m (n' + 1) n' hm θ hθ hΔ]
      _ = Φ * That m (n' + 1) n' θ := by rw [hΦ]; exact (Matrix.mul_assoc _ _ _).symm
  set z := Cᵀ *ᵥ v with hz
  have h2 := CatalanCore.bkdet_transfer W' Φ (Atil m n' (n' + 1) θ) Ahat hΦA z
  have h3 := CatalanCore.bkdet_transfer W' Φ _ (That m (n' + 1) n' θ) hΦT z
  rw [CatalanCore.bkdet_add_smul_one] at h3
  -- cross ratio at I2
  obtain ⟨hA2, hc2⟩ := Atil_hyps m n' (n' + 1) hm θ hθ hΔ'
  have hT2 := Ttil_preserves_WY m n' (n' + 1) hm θ hθ
  have hcross := CatalanCore.bkdet_cross_ratio hA2 hT2 hc2 hw (Φ *ᵥ z) w
  rw [h2, h3] at hcross
  have hD2' : (CatalanCore.bmat W' Φ).det ≠ 0 := hD2
  have hfin : CatalanCore.kdet Ahat z * CatalanCore.bkdet W' (Ttil (m + n') m (n' + 1) θ) w =
      CatalanCore.bkdet W' (Atil m n' (n' + 1) θ) w * CatalanCore.kdet (That m (n' + 1) n' θ) z := by
    apply mul_left_cancel₀ hD2'
    linear_combination hcross
  have hz0 : z = zvec m (n' + 1) n' θ 0 := by
    have e0 : wcol (m + (n' + 1)) θ (-((0 : ℕ) : ℤ)) = wcol (m + (n' + 1)) θ 0 := by simp
    unfold zvec
    rw [e0, hz, hv, hC, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mulVec_mulVec,
      Matrix.mul_assoc, hidem]
  rw [h1, hz0.symm, mul_assoc, hfin]
  ring

end KS

end CatalanCore.Star.Leonard
