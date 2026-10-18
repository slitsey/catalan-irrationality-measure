module

public import CatalanCore.ThmA.UnitChains2

/-!
# The s-step and K-step identities, and `ℓ`-unit propagation over `ℚ`
-/

@[expose] public section

open Finset Matrix

namespace CatalanCore.ThmA

section Identities

variable {F : Type*} [Field F] {N : ℕ}

/-- The s-step identity `u(K,s) u(T,c_{σ+1}) = u(K,s+1) u(T,c_σ)`, `σ = s+1`. -/
theorem uK_succ_identity (h : CharGt F N) (K s : ℕ) (hK : 1 ≤ K) (hN : s + 1 + 2 * K ≤ N + 1) :
    uK F K s * kdet (Tmat F K (s + 1)) (cvec F K (((s + 1 : ℕ) : F) + 1)) =
      uK F K (s + 1) * kdet (Tmat F K (s + 1)) (cvec F K (((s + 1 : ℕ) : F))) := by
  have hcomm := Tmat_commute_N (F := F) K (s + 1) (fun n hn hle => h.ne hn (by omega))
  have hcyc := Tmat_cyclic h K (s + 1) (by omega)
  have cr := kdet_cross_ratio hcyc hcomm (cvec F K (((s + 1 : ℕ) : F)))
    (cvec F K (((s + 1 : ℕ) : F) + 1))
  have l2 : kdet (Nmat F K (s + 1)) (cvec F K (((s + 1 : ℕ) : F))) = uK F K s := by
    have : cvec F K (((s + 1 : ℕ) : F)) = wvec F K s := by
      rw [wvec_eq_cvec]; push_cast; rfl
    rw [this, Nmat_succ]
    exact kdet_add_vecMulVec _ _
  have l3 : kdet (Nmat F K (s + 1)) (cvec F K (((s + 1 : ℕ) : F) + 1)) = uK F K (s + 1) := by
    rw [uK, ← wvec_eq_cvec]
  change kdet (Nmat F K (s + 1)) _ * _ = kdet (Nmat F K (s + 1)) _ * _ at cr
  rw [l2, l3] at cr
  exact cr

/-- The K-step identity (`K = m+1`):
`u(m+1,m) · u(T,e₀) · u(Y,c̃_K) = det[e₀|C] · u(T,c_K) · u(Y,c̃₀) · u(m,m+1)`. -/
theorem uK_pred_identity (h : CharGt F N) (m : ℕ) (hm : 1 ≤ m) (hN : 3 * (m + 1) ≤ N) :
    uK F (m + 1) m * (kdet (Tmat F (m + 1) m) (ev (m + 1) 0) *
        kdet (Ymat F (m + 1) m) (ctil F m (((m + 1 : ℕ)) : F))) =
      (border (Cmat F (m + 1) m) (ev (m + 1) 0)).det * kdet (Tmat F (m + 1) m) (wvec F (m + 1) m) *
        kdet (Ymat F (m + 1) m) (ctil F m 0) * uK F m (m + 1) := by
  have hF : ∀ n : ℕ, 0 < n → n ≤ (m + 1) + m → (n : F) ≠ 0 := fun n hn hle => h.ne hn (by omega)
  have hcommT := Tmat_commute_N (F := F) (m + 1) m hF
  have hcycT := Tmat_cyclic h (m + 1) m (by omega)
  have hcommY := Ymat_commute_M (F := F) (m + 1) m hF
  have hcycY := Ymat_cyclic h (m + 1) m (by omega) (by omega) (by omega)
  have e1 := kdet_cross_ratio hcycT hcommT (wvec F (m + 1) m) (ev (m + 1) 0)
  have e2 := kdet_mul_transpose (Cmat F (m + 1) m) (ev (m + 1) 0)
  have e3 := kdet_cross_ratio hcycY hcommY (ctil F m 0) (ctil F m ((m + 1 : ℕ) : F))
  rw [CT_e0] at e2
  rw [CtC_eq] at e3
  have hMk : kdet (Nmat F m (m + 1)) (ctil F m ((m + 1 : ℕ) : F)) = uK F m (m + 1) := by
    rw [ctil_succ_eq]; rfl
  rw [hMk] at e3
  rw [CtC_eq] at e2
  change kdet (Nmat F (m + 1) m) _ * _ = kdet (Nmat F (m + 1) m) _ * _ at e1
  change kdet (Nmat F (m + 1) m) _ = _ at e2
  have e1' : uK F (m + 1) m * kdet (Tmat F (m + 1) m) (ev (m + 1) 0) =
      kdet (Nmat F (m + 1) m) (ev (m + 1) 0) * kdet (Tmat F (m + 1) m) (wvec F (m + 1) m) := e1
  have e3' : kdet (Nmat F m (m + 1)) (ctil F m 0) * kdet (Ymat F (m + 1) m) (ctil F m ((m + 1 : ℕ) : F)) =
      uK F m (m + 1) * kdet (Ymat F (m + 1) m) (ctil F m 0) := e3
  linear_combination (kdet (Ymat F (m + 1) m) (ctil F m ((m + 1 : ℕ) : F))) * e1' +
    (kdet (Tmat F (m + 1) m) (wvec F (m + 1) m) *
      kdet (Ymat F (m + 1) m) (ctil F m ((m + 1 : ℕ) : F))) * e2 +
    ((border (Cmat F (m + 1) m) (ev (m + 1) 0)).det * kdet (Tmat F (m + 1) m) (wvec F (m + 1) m)) * e3'

end Identities

variable {l : ℕ} [hl : Fact l.Prime]

/-- s-step on `ℓ`-units. -/
theorem LU_uK_succ (K s : ℕ) (hK : 1 ≤ K) (hs : K ≤ s + 1) (hl' : s + 1 + K + 1 ≤ l)
    (hu : LU l (uK ℚ K s)) : LU l (uK ℚ K (s + 1)) := by
  have id := uK_succ_identity (charGt_rat (s + 1 + 2 * K)) K s hK (by omega)
  have hdown : LU l (kdet (Tmat ℚ K (s + 1)) (cvec ℚ K (((s + 1 : ℕ) : ℚ)))) :=
    LU_T_down K (s + 1) hK hs (by omega)
  have hup : LU l (kdet (Tmat ℚ K (s + 1)) (cvec ℚ K (((s + 1 : ℕ) : ℚ) + 1))) := by
    have := LU_T_up (l := l) K (s + 1) hK (by omega) (by omega)
    simpa using this
  have : uK ℚ K (s + 1) = uK ℚ K s * kdet (Tmat ℚ K (s + 1)) (cvec ℚ K (((s + 1 : ℕ) : ℚ) + 1)) /
      kdet (Tmat ℚ K (s + 1)) (cvec ℚ K (((s + 1 : ℕ) : ℚ))) := by
    exact (eq_div_iff hdown.1).2 id.symm
  rw [this]
  exact (hu.mul hup).div hdown

/-- K-step on `ℓ`-units (`K = m + 1`). -/
theorem LU_uK_pred (m : ℕ) (hm : 1 ≤ m) (hl' : 2 * (m + 1) ≤ l)
    (hu : LU l (uK ℚ m (m + 1))) : LU l (uK ℚ (m + 1) m) := by
  have id := uK_pred_identity (charGt_rat (3 * (m + 1))) m hm le_rfl
  have hTe := LU_Te0 (l := l) (m + 1) m (by omega) (by omega)
  have hYk := LU_Yk (l := l) m hm hl'
  have hB := LU_border (l := l) m (by omega)
  have hTw : LU l (kdet (Tmat ℚ (m + 1) m) (wvec ℚ (m + 1) m)) := by
    rw [wvec_eq_cvec]; exact LU_T_up (l := l) (m + 1) m (by omega) hm (by omega)
  have hY0 := LU_Y0 (l := l) m hm (by omega)
  have : uK ℚ (m + 1) m =
      (border (Cmat ℚ (m + 1) m) (ev (m + 1) 0)).det * kdet (Tmat ℚ (m + 1) m) (wvec ℚ (m + 1) m) *
        kdet (Ymat ℚ (m + 1) m) (ctil ℚ m 0) * uK ℚ m (m + 1) /
      (kdet (Tmat ℚ (m + 1) m) (ev (m + 1) 0) *
        kdet (Ymat ℚ (m + 1) m) (ctil ℚ m (((m + 1 : ℕ)) : ℚ))) := by
    exact (eq_div_iff (hTe.mul hYk).1).2 id
  rw [this]
  exact (((hB.mul hTw).mul hY0).mul hu).div (hTe.mul hYk)

end CatalanCore.ThmA
