module

public import CatalanCore.Rect.Geometry

@[expose] public section

/-!
# The hybrid family and the negative control (WP-H1)

Conventions fixed here (for `PolyFamily.hybrid`, whose `den` is a parameter):

* `hybridFam Fr α := PolyFamily.hybrid Fr α (fun _ => 1)`: **`Q (r,m) = fullPoly r m`** (rational
  coefficients).  This matches the paper's constants literally: content `Dden = denF`
  (`log denF ≤ (Λ_F+ε) r²`), decay `D_F` of `det Full`; at `m = 0` it is *exactly* `Fam.ofFrame`.
* `hybridFamQt Fr α := PolyFamily.hybrid Fr α (denF Fr ·.1 ·.2)`: `Q = denF · det Full ∈ ℤ[X]`
  (the paper's `Q̃`); `Qt_int` shows integrality.  Its content is trivial (`Dden = 1`) and its
  decay is `D_F - Λ_F`.  Both give the same measure exponent.

Sign convention: `fullPoly = det (X·1_C + Mn)` (the `T_t` convention), see `Rect/Full`.
-/

open Polynomial Finset Matrix

namespace CatalanCore.Rect

/-- Negative control: at `m = 0`, `Full` is the square frame, `det Full(X) = P_r(X)`. -/
theorem fullPoly_zero (Fr : Frame) (r : ℕ) : Fr.fullPoly r 0 = Fr.Ppoly r := by
  unfold Frame.fullPoly Frame.Ppoly
  rw [← Matrix.det_submatrix_equiv_self (Equiv.sumEmpty (Fin r) (Fin 0)).symm]
  congr 1

/-- Schur step for `Frame.fullPoly`. -/
theorem fullPoly_eq (Fr : Frame) (r m : ℕ) (hD : ((after r m).RXYG Fr).det ≠ 0) :
    Fr.fullPoly r m
      = Polynomial.C ((after r m).RXYG Fr).det * (after r m).schurPG Fr := by
  rw [← det_full_after]; exact Geometry.det_full_eq _ Fr hD

/-- Least positive integer clearing all coefficient denominators of `fullPoly r m`. -/
noncomputable def denF (Fr : Frame) (r m : ℕ) : ℕ :=
  (Fr.fullPoly r m).support.lcm (fun k => ((Fr.fullPoly r m).coeff k).den)

theorem denF_pos (Fr : Frame) (r m : ℕ) : 0 < denF Fr r m := by
  rw [Nat.pos_iff_ne_zero, denF, Ne, Finset.lcm_eq_zero_iff]
  simp only [Finset.mem_image, not_exists, not_and]
  intro k _ h; exact (Rat.den_nz _) h

/-- `denF · det Full(X) ∈ ℤ[X]`. -/
theorem Qt_int (Fr : Frame) (r m k : ℕ) :
    ∃ z : ℤ, ((denF Fr r m : ℚ) * (Fr.fullPoly r m).coeff k) = z := by
  by_cases hk : k ∈ (Fr.fullPoly r m).support
  · obtain ⟨u, hu⟩ := Finset.dvd_lcm (f := fun k => ((Fr.fullPoly r m).coeff k).den) hk
    set q := (Fr.fullPoly r m).coeff k
    refine ⟨q.num * (u : ℤ), ?_⟩
    have h1 : (denF Fr r m : ℚ) = (q.den : ℚ) * u := by
      have : denF Fr r m = q.den * u := hu
      exact_mod_cast this
    rw [h1]; push_cast
    have := Rat.num_div_den q
    calc (q.den : ℚ) * u * q = (q.den * q) * u := by ring
      _ = _ := by rw [mul_comm (q.den : ℚ) q, Rat.mul_den_eq_num]
  · exact ⟨0, by simp [Polynomial.notMem_support_iff.1 hk]⟩

/-- The hybrid family, `Q = det Full(X)`. -/
noncomputable def hybridFam (Fr : Frame) (α : ℚ) : PolyFamily :=
  PolyFamily.hybrid Fr α (fun _ => 1)

/-- The hybrid family with the denominator-cleared `Q̃ = denF · det Full(X)`. -/
noncomputable def hybridFamQt (Fr : Frame) (α : ℚ) : PolyFamily :=
  PolyFamily.hybrid Fr α (fun rm => (denF Fr rm.1 rm.2 : ℚ))

@[simp] theorem hybridFam_Q (Fr : Frame) (α : ℚ) (rm : ℕ × ℕ) :
    (hybridFam Fr α).Q rm = Fr.fullPoly rm.1 rm.2 := by
  simp [hybridFam, PolyFamily.hybrid]

theorem hybridFamQt_Q (Fr : Frame) (α : ℚ) (rm : ℕ × ℕ) :
    (hybridFamQt Fr α).Q rm = Polynomial.C (denF Fr rm.1 rm.2 : ℚ) * Fr.fullPoly rm.1 rm.2 := rfl

/-- **Negative control** (`m = 0`, `α = 0`): `Fam.hybrid Fr 0` agrees with `Fam.ofFrame Fr`
on the members `(r, 0)`: same constant, same degree, admissible, and `Q = P` exactly. -/
theorem hybridFam_zero (Fr : Frame) (r : ℕ) :
    (hybridFam Fr 0).const = (PolyFamily.ofFrame Fr).const ∧
    (hybridFam Fr 0).deg (r, 0) = (PolyFamily.ofFrame Fr).deg r ∧
    (hybridFam Fr 0).Adm (r, 0) ∧
    (hybridFam Fr 0).Q (r, 0) = (PolyFamily.ofFrame Fr).Q r := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · simp [hybridFam, PolyFamily.hybrid]
  · simp [fullPoly_zero, PolyFamily.ofFrame]

/-- Clearing by a nonzero scalar does not change vanishing. -/
theorem evalQ_ne_zero_iff (Fr : Frame) (α : ℚ) (den : ℕ × ℕ → ℚ) (rm : ℕ × ℕ) (hden : den rm ≠ 0)
    (x : ℚ) :
    (PolyFamily.hybrid Fr α den).evalQ rm x ≠ 0 ↔ (Fr.fullPoly rm.1 rm.2).eval x ≠ 0 := by
  simp [PolyFamily.evalQ, PolyFamily.hybrid, hden]

/-- With `det R_{X'Y'} ≠ 0`, vanishing of the hybrid member at `x` is vanishing of the monic `P_r`. -/
theorem evalQ_ne_zero_iff_schur (Fr : Frame) (α : ℚ) (r m : ℕ)
    (hD : ((after r m).RXYG Fr).det ≠ 0) (x : ℚ) :
    (hybridFam Fr α).evalQ (r, m) x ≠ 0 ↔ ((after r m).schurPG Fr).eval x ≠ 0 := by
  simp [PolyFamily.evalQ, fullPoly_eq Fr r m hD, hD]

end CatalanCore.Rect
