module

public import CatalanCore.Star.Leonard.Induct

/-!
# The Darboux K-step as an exact ratio (package H7, (B2))

`ks_eq`: for `n' ≥ 1`, `θ > 0` generic,
`uu m (n'+1) (n'+1) (θ-1) = uu m n' (n'+1) θ · KSratio m n' θ` where `KSratio` is an explicit
quotient of Cauchy factors, leading-coefficient products and `G = det[z_j]`
(`KS_formula` + frame shift + L2 + cross ratio at the instance `(n'+1, n'+1, θ-1)`).
-/

@[expose] public section

open Finset Matrix

namespace CatalanCore.Star.Leonard

section ShiftJ

variable (m n S : ℕ) (hm : 1 ≤ m) (θ : ℚ) (hθ' : Gen (θ - 1))
  (hΔ : IsUnit ((Wb (m + n) θ (bX m (S : ℤ)))ᵀ * Wb (m + n) θ (bY m (S : ℤ))).det)

include hm hθ' hΔ in
/-- relaxed form of `u_up_shift_eq`: only `n ≤ S + 1` is needed -/
theorem u_up_shiftJ (hS : n ≤ S + 1) :
    CatalanCore.bkdet (Wb (m + n) θ (bY m (S : ℤ))) (Ttil (m + n) m (S + 1) (θ - 1))
        (projB (m + n) θ (bX m (S : ℤ)) (bY m (S : ℤ)) *ᵥ wcol (m + n) θ 0) =
      lprodUp m n (S + 1) (θ - 1) 1 *
        cauFac (θ - 1) (Fin.addCases (fun i : Fin m => ((bY m ((S + 1 : ℕ) : ℤ) i : ℤ) : ℚ))
          (fun j : Fin n => ((((1 : ℤ) + ((j : ℕ) : ℤ) : ℤ)) : ℚ)) : Fin (m + n) → ℚ) := by
  have hΔ' : IsUnit ((Wb (m + n) (θ - 1) (bX m ((S + 1 : ℕ) : ℤ)))ᵀ *
      Wb (m + n) (θ - 1) (bY m ((S + 1 : ℕ) : ℤ))).det := by
    rw [Wb_shift_X, Wb_shift_Y]; exact hΔ
  have h := u_up_1 m n (S + 1) hm (θ - 1) hθ' hΔ' hS
  rw [Wb_shift_Y, projB_shift] at h
  have e : wcol (m + n) (θ - 1) 1 = wcol (m + n) θ 0 := by
    have := wcol_shift (m + n) θ 0; simpa using this
  rw [e] at h
  exact h

include hm hθ' hΔ in
theorem u_up_shiftJ_ne (hS : n ≤ S + 1) :
    CatalanCore.bkdet (Wb (m + n) θ (bY m (S : ℤ))) (Ttil (m + n) m (S + 1) (θ - 1))
        (projB (m + n) θ (bX m (S : ℤ)) (bY m (S : ℤ)) *ᵥ wcol (m + n) θ 0) ≠ 0 := by
  have hΔ' : IsUnit ((Wb (m + n) (θ - 1) (bX m ((S + 1 : ℕ) : ℤ)))ᵀ *
      Wb (m + n) (θ - 1) (bY m ((S + 1 : ℕ) : ℤ))).det := by
    rw [Wb_shift_X, Wb_shift_Y]; exact hΔ
  have h := u_up_1_ne m n (S + 1) hm (θ - 1) hθ' hΔ' hS
  rw [Wb_shift_Y, projB_shift] at h
  have e : wcol (m + n) (θ - 1) 1 = wcol (m + n) θ 0 := by
    have := wcol_shift (m + n) θ 0; simpa using this
  rw [e] at h
  exact h

include hm hθ' hΔ in
theorem u_down_shiftJ (hS : n ≤ S + 1) :
    CatalanCore.bkdet (Wb (m + n) θ (bY m (S : ℤ))) (Ttil (m + n) m (S + 1) (θ - 1))
        (projB (m + n) θ (bX m (S : ℤ)) (bY m (S : ℤ)) *ᵥ wcol (m + n) θ (S : ℤ)) =
      lprodDown m n (S + 1) (θ - 1) ((S + 1 : ℕ) : ℤ) *
        cauFac (θ - 1) (Fin.addCases (fun i : Fin m => ((bY m ((S + 1 : ℕ) : ℤ) i : ℤ) : ℚ))
          (fun j : Fin n => (((((S + 1 : ℕ) : ℤ) - ((j : ℕ) : ℤ) : ℤ)) : ℚ)) : Fin (m + n) → ℚ) := by
  have hΔ' : IsUnit ((Wb (m + n) (θ - 1) (bX m ((S + 1 : ℕ) : ℤ)))ᵀ *
      Wb (m + n) (θ - 1) (bY m ((S + 1 : ℕ) : ℤ))).det := by
    rw [Wb_shift_X, Wb_shift_Y]; exact hΔ
  have h := u_down_S m n (S + 1) hm (θ - 1) hθ' hΔ' hS
  rw [Wb_shift_Y, projB_shift, wcol_shift_nat] at h
  exact h

include hm hθ' hΔ in
theorem u_down_shiftJ_ne (hS : n ≤ S + 1) :
    CatalanCore.bkdet (Wb (m + n) θ (bY m (S : ℤ))) (Ttil (m + n) m (S + 1) (θ - 1))
        (projB (m + n) θ (bX m (S : ℤ)) (bY m (S : ℤ)) *ᵥ wcol (m + n) θ (S : ℤ)) ≠ 0 := by
  have hΔ' : IsUnit ((Wb (m + n) (θ - 1) (bX m ((S + 1 : ℕ) : ℤ)))ᵀ *
      Wb (m + n) (θ - 1) (bY m ((S + 1 : ℕ) : ℤ))).det := by
    rw [Wb_shift_X, Wb_shift_Y]; exact hΔ
  have h := u_down_S_ne m n (S + 1) hm (θ - 1) hθ' hΔ' hS
  rw [Wb_shift_Y, projB_shift, wcol_shift_nat] at h
  exact h

end ShiftJ

lemma ks_alg (X u1 u2 LD LU UT2 CF LpG : ℚ) (hLU : LU ≠ 0) (hUT : UT2 ≠ 0)
    (h1 : X * LU = u1 * LD) (h2 : u1 * UT2 = CF * u2 * LpG) :
    X = u2 * (CF * LpG * LD / (UT2 * LU)) := by
  field_simp
  linear_combination UT2 * h1 + LD * h2

/-- the explicit ratio -/
noncomputable def KSratio (m n' : ℕ) (θ : ℚ) : ℚ :=
  (cauFac θ (Fin.addCases (fun i : Fin m => ((bY m (n' : ℤ) i : ℤ) : ℚ))
      (fun j : Fin (n' + 1) => (((j : ℕ) : ℤ) : ℚ)) : Fin (m + (n' + 1)) → ℚ) *
    ((∏ k : Fin n', ∏ j ∈ range k,
        (-tau (m + (n' + 1)) m n' θ (-θ - (((-(j : ℤ)) : ℤ) : ℚ)))) *
      (CatalanCore.colMat fun j => zvec m (n' + 1) n' θ j).det) *
    (lprodDown m (n' + 1) (n' + 1) (θ - 1) ((n' + 1 : ℕ) : ℤ) *
      cauFac (θ - 1) (Fin.addCases (fun i : Fin m => ((bY m ((n' + 1 : ℕ) : ℤ) i : ℤ) : ℚ))
        (fun j : Fin (n' + 1) => (((((n' + 1 : ℕ) : ℤ) - ((j : ℕ) : ℤ) : ℤ)) : ℚ)) :
          Fin (m + (n' + 1)) → ℚ))) /
  ((lprodDown m n' (n' + 1) θ ((n' + 1 : ℕ) : ℤ) *
      cauFac θ (Fin.addCases (fun i : Fin m => ((bY m ((n' + 1 : ℕ) : ℤ) i : ℤ) : ℚ))
        (fun j : Fin n' => (((((n' + 1 : ℕ) : ℤ) - ((j : ℕ) : ℤ) : ℤ)) : ℚ)) :
          Fin (m + n') → ℚ)) *
    (lprodUp m (n' + 1) (n' + 1) (θ - 1) 1 *
      cauFac (θ - 1) (Fin.addCases (fun i : Fin m => ((bY m ((n' + 1 : ℕ) : ℤ) i : ℤ) : ℚ))
        (fun j : Fin (n' + 1) => ((((1 : ℤ) + ((j : ℕ) : ℤ) : ℤ)) : ℚ)) :
          Fin (m + (n' + 1)) → ℚ)))

theorem ks_eq (m n' : ℕ) (hm : 1 ≤ m) (hn' : 1 ≤ n') (θ : ℚ) (hθ0 : 0 < θ) (hθ : Gen θ) :
    uu m (n' + 1) (n' + 1) (θ - 1) = uu m n' (n' + 1) θ * KSratio m n' θ := by
  have hθ' := gen_sub_one hθ
  have hΔ1 : IsUnit ((Wb (m + (n' + 1)) θ (bX m (n' : ℤ)))ᵀ *
      Wb (m + (n' + 1)) θ (bY m (n' : ℤ))).det :=
    isUnit_iff_ne_zero.2 (Delta_ne_pos (m + (n' + 1)) m n' (by omega) θ hθ0)
  have hΔ2 : IsUnit ((Wb (m + n') θ (bX m ((n' + 1 : ℕ) : ℤ)))ᵀ *
      Wb (m + n') θ (bY m ((n' + 1 : ℕ) : ℤ))).det :=
    isUnit_iff_ne_zero.2 (Delta_ne_pos (m + n') m (n' + 1) (by omega) θ hθ0)
  have hΔJ : IsUnit ((Wb (m + (n' + 1)) (θ - 1) (bX m ((n' + 1 : ℕ) : ℤ)))ᵀ *
      Wb (m + (n' + 1)) (θ - 1) (bY m ((n' + 1 : ℕ) : ℤ))).det := by
    rw [Wb_shift_X, Wb_shift_Y]; exact hΔ1
  -- (F1) the K-step formula
  set w : Fin (m + n') → ℚ := projB (m + n') θ (bX m ((n' + 1 : ℕ) : ℤ)) (bY m ((n' + 1 : ℕ) : ℤ)) *ᵥ
    wcol (m + n') θ ((n' + 1 : ℕ) : ℤ) with hw
  have hwne := u_down_S_ne m n' (n' + 1) hm θ hθ hΔ2 (by omega)
  have F1 := KS_formula m n' hm θ hθ hn' hΔ1 hΔ2 w hwne (hD2_rat m n' hm θ hθ0 hθ)
  have hUT2 := u_down_S m n' (n' + 1) hm θ hθ hΔ2 (by omega)
  -- (F2) frame shift
  have F2 : CatalanCore.bkdet (Wb (m + (n' + 1)) θ (bY m (n' : ℤ))) (Atil m (n' + 1) n' θ)
      (projB (m + (n' + 1)) θ (bX m (n' : ℤ)) (bY m (n' : ℤ)) *ᵥ wcol (m + (n' + 1)) θ 0) =
      CatalanCore.bkdet (Wb (m + (n' + 1)) θ (bY m (n' : ℤ))) (Atil m (n' + 1) (n' + 1) (θ - 1))
      (projB (m + (n' + 1)) θ (bX m (n' : ℤ)) (bY m (n' : ℤ)) *ᵥ wcol (m + (n' + 1)) θ 0) := by
    rw [Atil_shift m (n' + 1) n' θ]
    exact (CatalanCore.bkdet_add_vecMulVec (Atil_hyps m (n' + 1) n' hm θ hθ hΔ1).1 _ _).symm
  -- (F3) cross ratio at the instance (n'+1, n'+1, θ-1)
  have hA := Atil_hyps m (n' + 1) (n' + 1) hm (θ - 1) hθ' hΔJ
  have hT := Ttil_preserves_WY m (n' + 1) (n' + 1) hm (θ - 1) hθ'
  rw [Wb_shift_Y] at hA hT
  have hcyc := u_up_shiftJ_ne m (n' + 1) n' hm θ hθ' hΔ1 (by omega)
  have hcr := CatalanCore.bkdet_cross_ratio hA.1 hT hA.2 hcyc
    (projB (m + (n' + 1)) θ (bX m (n' : ℤ)) (bY m (n' : ℤ)) *ᵥ wcol (m + (n' + 1)) θ (n' : ℤ))
    (projB (m + (n' + 1)) θ (bX m (n' : ℤ)) (bY m (n' : ℤ)) *ᵥ wcol (m + (n' + 1)) θ 0)
  have hTv := u_down_shiftJ m (n' + 1) n' hm θ hθ' hΔ1 (by omega)
  have hTv' := u_up_shiftJ m (n' + 1) n' hm θ hθ' hΔ1 (by omega)
  have hTvne := u_down_shiftJ_ne m (n' + 1) n' hm θ hθ' hΔ1 (by omega)
  have hu1 := uu_shift m (n' + 1) n' θ
  -- assemble
  unfold KSratio
  rw [hu1]
  set u1 := CatalanCore.bkdet (Wb (m + (n' + 1)) θ (bY m (n' : ℤ))) (Atil m (n' + 1) n' θ)
    (projB (m + (n' + 1)) θ (bX m (n' : ℤ)) (bY m (n' : ℤ)) *ᵥ wcol (m + (n' + 1)) θ 0) with hu1def
  rw [← F2] at hcr
  rw [hTv, hTv'] at hcr
  rw [hUT2] at F1
  have hUT2ne : ((∏ k : Fin n', ∏ j ∈ range k, -tau (m + n') m (n' + 1) θ (-θ - ((((n' + 1 : ℕ) : ℤ) - (j : ℤ) : ℤ) : ℚ))) *
      cauFac θ (Fin.addCases (fun i : Fin m => ((bY m ((n' + 1 : ℕ) : ℤ) i : ℤ) : ℚ))
        (fun j : Fin n' => (((((n' + 1 : ℕ) : ℤ) - ((j : ℕ) : ℤ) : ℤ)) : ℚ)) : Fin (m + n') → ℚ)) ≠ 0 := by
    rw [← hUT2]; exact hwne
  have hLUne := hcyc
  rw [hTv'] at hLUne
  exact ks_alg _ _ _ _ _ _ _ _ hLUne hUT2ne hcr F1

end CatalanCore.Star.Leonard
