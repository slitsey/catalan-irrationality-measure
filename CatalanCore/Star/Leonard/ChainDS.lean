module

public import CatalanCore.Star.Leonard.ChainInst

/-!
# The diagonal step with its cyclicity hypotheses discharged (package H4)

`ds_cyc`: the cross-ratio identity of `ds_concrete` for `v₀ = Π c₀`, `v_S = Π c_S`, with all three
cyclicity hypotheses proved from the explicit chain products of `ChainInst`.
`T'`-chain forms: the instance `(θ-1, S+1)` shares the borders and `Π`, and
`c'_{S+1} = c_S`, `c'_1 = c_0`.
-/

@[expose] public section

open Finset Matrix

namespace CatalanCore.Star.Leonard

variable {F : Type*} [Field F]

lemma wcol_shift_nat (K : ℕ) (θ : F) (y : ℕ) :
    wcol K (θ - 1) ((y + 1 : ℕ) : ℤ) = wcol K θ (y : ℤ) := by
  have := wcol_shift K θ (y : ℤ)
  simpa using this

/-- `u(T~', Π c_0)` is `u(T~', Π' c'_1)`: the upward chain of the instance `(θ-1, S+1)`. -/
theorem u_up_shift_ne [CharZero F] (m n S : ℕ) (hm : 1 ≤ m) (θ : F) (hθ' : Gen (θ - 1))
    (hΔ : IsUnit ((Wb (m + n) θ (bX m (S : ℤ)))ᵀ * Wb (m + n) θ (bY m (S : ℤ))).det)
    (hS : n ≤ S) :
    CatalanCore.bkdet (Wb (m + n) θ (bY m (S : ℤ))) (Ttil (m + n) m (S + 1) (θ - 1))
      (projB (m + n) θ (bX m (S : ℤ)) (bY m (S : ℤ)) *ᵥ wcol (m + n) θ 0) ≠ 0 := by
  have hΔ' : IsUnit ((Wb (m + n) (θ - 1) (bX m ((S + 1 : ℕ) : ℤ)))ᵀ *
      Wb (m + n) (θ - 1) (bY m ((S + 1 : ℕ) : ℤ))).det := by
    rw [Wb_shift_X, Wb_shift_Y]; exact hΔ
  have h := u_up_1_ne m n (S + 1) hm (θ - 1) hθ' hΔ' (by omega)
  rw [Wb_shift_Y, projB_shift] at h
  have e : wcol (m + n) (θ - 1) 1 = wcol (m + n) θ 0 := by
    have := wcol_shift (m + n) θ 0; simpa using this
  rw [e] at h
  exact h

/-- `u(T~', Π c_S)`: the downward chain from the top of the instance `(θ-1, S+1)`. -/
theorem u_down_shift_ne [CharZero F] (m n S : ℕ) (hm : 1 ≤ m) (θ : F) (hθ' : Gen (θ - 1))
    (hΔ : IsUnit ((Wb (m + n) θ (bX m (S : ℤ)))ᵀ * Wb (m + n) θ (bY m (S : ℤ))).det)
    (hS : n ≤ S) :
    CatalanCore.bkdet (Wb (m + n) θ (bY m (S : ℤ))) (Ttil (m + n) m (S + 1) (θ - 1))
      (projB (m + n) θ (bX m (S : ℤ)) (bY m (S : ℤ)) *ᵥ wcol (m + n) θ (S : ℤ)) ≠ 0 := by
  have hΔ' : IsUnit ((Wb (m + n) (θ - 1) (bX m ((S + 1 : ℕ) : ℤ)))ᵀ *
      Wb (m + n) (θ - 1) (bY m ((S + 1 : ℕ) : ℤ))).det := by
    rw [Wb_shift_X, Wb_shift_Y]; exact hΔ
  have h := u_down_S_ne m n (S + 1) hm (θ - 1) hθ' hΔ' (by omega)
  rw [Wb_shift_Y, projB_shift, wcol_shift_nat] at h
  exact h

/-- **The diagonal step (H4)** with cyclicity discharged. -/
theorem ds_cyc [CharZero F] (m n S : ℕ) (hm : 1 ≤ m) (θ : F) (hθ : Gen θ) (hθ' : Gen (θ - 1))
    (hΔ : IsUnit ((Wb (m + n) θ (bX m (S : ℤ)))ᵀ * Wb (m + n) θ (bY m (S : ℤ))).det)
    (hS : n ≤ S) (hn : 1 ≤ n) :
    CatalanCore.bkdet (Wb (m + n) θ (bY m (S : ℤ))) (Atil m n S θ)
        (projB (m + n) θ (bX m (S : ℤ)) (bY m (S : ℤ)) *ᵥ wcol (m + n) θ (S : ℤ)) *
      CatalanCore.bkdet (Wb (m + n) θ (bY m (S : ℤ))) (Ttil (m + n) m S θ)
        (projB (m + n) θ (bX m (S : ℤ)) (bY m (S : ℤ)) *ᵥ wcol (m + n) θ 0) *
      CatalanCore.bkdet (Wb (m + n) θ (bY m (S : ℤ))) (Ttil (m + n) m (S + 1) (θ - 1))
        (projB (m + n) θ (bX m (S : ℤ)) (bY m (S : ℤ)) *ᵥ wcol (m + n) θ (S : ℤ)) =
    CatalanCore.bkdet (Wb (m + n) θ (bY m (S : ℤ))) (Atil m n (S + 1) (θ - 1))
        (projB (m + n) θ (bX m (S : ℤ)) (bY m (S : ℤ)) *ᵥ wcol (m + n) θ (S : ℤ)) *
      CatalanCore.bkdet (Wb (m + n) θ (bY m (S : ℤ))) (Ttil (m + n) m S θ)
        (projB (m + n) θ (bX m (S : ℤ)) (bY m (S : ℤ)) *ᵥ wcol (m + n) θ (S : ℤ)) *
      CatalanCore.bkdet (Wb (m + n) θ (bY m (S : ℤ))) (Ttil (m + n) m (S + 1) (θ - 1))
        (projB (m + n) θ (bX m (S : ℤ)) (bY m (S : ℤ)) *ᵥ wcol (m + n) θ 0) :=
  ds_concrete m n S hm θ hθ hθ' hΔ _ _ (u_down_0_ne m n S hm θ hθ hΔ hS hn)
    (u_up_shift_ne m n S hm θ hθ' hΔ hS) rfl


/-! ### The four chain values, transported to the shared borders -/

section Explicit

variable [CharZero F] (m n S : ℕ) (hm : 1 ≤ m) (θ : F) (hθ' : Gen (θ - 1))
  (hΔ : IsUnit ((Wb (m + n) θ (bX m (S : ℤ)))ᵀ * Wb (m + n) θ (bY m (S : ℤ))).det)

include hm hθ' hΔ in
/-- `u(T~', Π c_S)` explicitly (instance `(θ-1, S+1)`, downward chain from its top). -/
theorem u_down_shift_eq (hS : n ≤ S) :
    CatalanCore.bkdet (Wb (m + n) θ (bY m (S : ℤ))) (Ttil (m + n) m (S + 1) (θ - 1))
        (projB (m + n) θ (bX m (S : ℤ)) (bY m (S : ℤ)) *ᵥ wcol (m + n) θ (S : ℤ)) =
      (∏ k : Fin n, ∏ j ∈ Finset.range k,
          (-tau (m + n) m (S + 1) (θ - 1) (-(θ - 1) - ((((S + 1 : ℕ) : ℤ) - (j : ℤ) : ℤ) : F)))) *
        cauFac (θ - 1) (Fin.addCases (fun i : Fin m => ((bY m ((S + 1 : ℕ) : ℤ) i : ℤ) : F))
          (fun j : Fin n => ((((S + 1 : ℕ) : ℤ) - ((j : ℕ) : ℤ) : ℤ) : F))) := by
  have hΔ' : IsUnit ((Wb (m + n) (θ - 1) (bX m ((S + 1 : ℕ) : ℤ)))ᵀ *
      Wb (m + n) (θ - 1) (bY m ((S + 1 : ℕ) : ℤ))).det := by
    rw [Wb_shift_X, Wb_shift_Y]; exact hΔ
  have h := u_down_S m n (S + 1) hm (θ - 1) hθ' hΔ' (by omega)
  rw [Wb_shift_Y, projB_shift, wcol_shift_nat] at h
  exact h

include hm hθ' hΔ in
/-- `u(T~', Π c_0)` explicitly (instance `(θ-1, S+1)`, upward chain from `c'_1 = c_0`). -/
theorem u_up_shift_eq (hS : n ≤ S) :
    CatalanCore.bkdet (Wb (m + n) θ (bY m (S : ℤ))) (Ttil (m + n) m (S + 1) (θ - 1))
        (projB (m + n) θ (bX m (S : ℤ)) (bY m (S : ℤ)) *ᵥ wcol (m + n) θ 0) =
      (∏ k : Fin n, ∏ j ∈ Finset.range k,
          (-sigma (m + n) m (S + 1) (θ - 1)
            (-(θ - 1) - (((1 : ℤ) + (j : ℤ) : ℤ) : F) - 1))) *
        cauFac (θ - 1) (Fin.addCases (fun i : Fin m => ((bY m ((S + 1 : ℕ) : ℤ) i : ℤ) : F))
          (fun j : Fin n => ((((1 : ℤ) + ((j : ℕ) : ℤ) : ℤ)) : F))) := by
  have hΔ' : IsUnit ((Wb (m + n) (θ - 1) (bX m ((S + 1 : ℕ) : ℤ)))ᵀ *
      Wb (m + n) (θ - 1) (bY m ((S + 1 : ℕ) : ℤ))).det := by
    rw [Wb_shift_X, Wb_shift_Y]; exact hΔ
  have h := u_up_1 m n (S + 1) hm (θ - 1) hθ' hΔ' (by omega)
  rw [Wb_shift_Y, projB_shift] at h
  have e : wcol (m + n) (θ - 1) 1 = wcol (m + n) θ 0 := by
    have := wcol_shift (m + n) θ 0; simpa using this
  rw [e] at h
  exact h

end Explicit

/-- the leading-coefficient product of a downward chain `c_{y0}, c_{y0-1}, …` (`l(y) = -τ(-θ-y)`) -/
noncomputable def lprodDown (m n S : ℕ) (θ : F) (y0 : ℤ) : F :=
  ∏ k : Fin n, ∏ j ∈ Finset.range k, (-tau (m + n) m S θ (-θ - ((y0 - (j : ℤ) : ℤ) : F)))

/-- the leading-coefficient product of an upward chain `c_{y1}, c_{y1+1}, …` (`r(y) = -σ(-θ-y-1)`) -/
noncomputable def lprodUp (m n S : ℕ) (θ : F) (y1 : ℤ) : F :=
  ∏ k : Fin n, ∏ j ∈ Finset.range k, (-sigma (m + n) m S θ (-θ - ((y1 + (j : ℤ) : ℤ) : F) - 1))

section DSExplicit

variable [CharZero F] (m n S : ℕ) (hm : 1 ≤ m) (θ : F) (hθ : Gen θ) (hθ' : Gen (θ - 1))
  (hΔ : IsUnit ((Wb (m + n) θ (bX m (S : ℤ)))ᵀ * Wb (m + n) θ (bY m (S : ℤ))).det)

include hm hθ hθ' hΔ in
/-- **The diagonal step, fully explicit.**  `(n ≤ S, 1 ≤ n)`:
`u(Ã,Πc_S) · [l₀ Cau₀] · [l'_S Cau'_S] = u(Ã',Πc_S) · [l_S Cau_S] · [r'₁ Cau'₁]`
(`Ã = Ã_{θ,S}`, `Ã' = Ã_{θ-1,S+1}`; `l = lprodDown`, `r = lprodUp`, `Cau = cauFac`). -/
theorem ds_explicit (hS : n ≤ S) (hn : 1 ≤ n) :
    CatalanCore.bkdet (Wb (m + n) θ (bY m (S : ℤ))) (Atil m n S θ)
        (projB (m + n) θ (bX m (S : ℤ)) (bY m (S : ℤ)) *ᵥ wcol (m + n) θ (S : ℤ)) *
      (lprodDown m n S θ 0 *
        cauFac θ (Fin.addCases (fun i : Fin m => ((bY m (S : ℤ) i : ℤ) : F))
          (fun j : Fin n => ((((0 : ℤ) - ((j : ℕ) : ℤ) : ℤ)) : F)))) *
      (lprodDown m n (S + 1) (θ - 1) ((S + 1 : ℕ) : ℤ) *
        cauFac (θ - 1) (Fin.addCases (fun i : Fin m => ((bY m ((S + 1 : ℕ) : ℤ) i : ℤ) : F))
          (fun j : Fin n => ((((S + 1 : ℕ) : ℤ) - ((j : ℕ) : ℤ) : ℤ) : F)))) =
    CatalanCore.bkdet (Wb (m + n) θ (bY m (S : ℤ))) (Atil m n (S + 1) (θ - 1))
        (projB (m + n) θ (bX m (S : ℤ)) (bY m (S : ℤ)) *ᵥ wcol (m + n) θ (S : ℤ)) *
      (lprodDown m n S θ (S : ℤ) *
        cauFac θ (Fin.addCases (fun i : Fin m => ((bY m (S : ℤ) i : ℤ) : F))
          (fun j : Fin n => ((((S : ℤ) - ((j : ℕ) : ℤ) : ℤ)) : F)))) *
      (lprodUp m n (S + 1) (θ - 1) 1 *
        cauFac (θ - 1) (Fin.addCases (fun i : Fin m => ((bY m ((S + 1 : ℕ) : ℤ) i : ℤ) : F))
          (fun j : Fin n => ((((1 : ℤ) + ((j : ℕ) : ℤ) : ℤ)) : F)))) := by
  have h := ds_cyc m n S hm θ hθ hθ' hΔ hS hn
  rw [u_down_0 m n S hm θ hθ hΔ hS hn, u_down_S m n S hm θ hθ hΔ hS,
    u_down_shift_eq m n S hm θ hθ' hΔ hS, u_up_shift_eq m n S hm θ hθ' hΔ hS] at h
  exact h

end DSExplicit

end CatalanCore.Star.Leonard
