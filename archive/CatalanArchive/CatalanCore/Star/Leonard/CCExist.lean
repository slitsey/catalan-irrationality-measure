module

public import CatalanCore.Star.Leonard.CCPoly

/-!
# (CC) existence: the remainder polynomial `N` of degree `< m` (package H2)

`Hfull = H₀ - Q̂·(ℓ·u(u+1) + d·(u-1)(u+1) + r·(u-1)u) = (u-1)u(u+1)·N` with `deg N ≤ m-1`, where
`ℓ, d, r` are the residues of `a(z)/(u-1)`, `Dt/u`, `b(z)/(u+1)` over `Q̂`.
-/

@[expose] public section

open Polynomial

namespace CatalanCore.Star.Leonard

variable {F : Type*} [Field F]

lemma lin_one (b : F) : lin 1 b = X - C (-b) := by
  unfold lin; simp [sub_eq_add_neg]

lemma eval_lin (a b z : F) : (lin a b).eval z = a * z + b := by simp [lin]

section Exist

variable (K m : ℕ) (S θ y g c0 : F)

/-- `-τ(a-1)·Q̂ = -p(a-1)(z+S)·P`. -/
noncomputable def aP : F[X] := -(pmz K θ * lin 1 S * PPf S m)
/-- `-σ(a)·Q̂ = -p(a)(z+S+1)·P`. -/
noncomputable def bP : F[X] := -(pz K θ * lin 1 (S + 1) * PPf S m)
/-- `D̃·Q̂`. -/
noncomputable def Dt : F[X] := Dz K m S θ g c0 * PPf (S - 1) m
/-- `Q̂ = ∏_{t∈Y}(z+t)`. -/
noncomputable def Qh : F[X] := PPf (S - 1) m

lemma Hz_eq : Hz K m S θ y g c0 =
    aP K m S θ * (lin 1 y * lin 1 (y + 1)) + bP K m S θ * (lin 1 (y - 1) * lin 1 y)
      + Dt K m S θ g c0 * (lin 1 (y - 1) * lin 1 (y + 1)) := by
  unfold Hz alphaz betaz aP bP Dt; ring

end Exist


/-- Three simple roots: split off the linear factors. -/
lemma three_div (f1 f2 f3 : F[X]) (z1 z2 z3 : F) (h1 : f1.eval z1 = 0) (h2 : f2.eval z2 = 0)
    (h3 : f3.eval z3 = 0) :
    ∃ N : F[X], f1 * ((X - C z2) * (X - C z3)) + f2 * ((X - C z1) * (X - C z3))
      + f3 * ((X - C z1) * (X - C z2)) = (X - C z1) * (X - C z2) * (X - C z3) * N := by
  obtain ⟨G1, e1⟩ := Polynomial.dvd_iff_isRoot.2 (show IsRoot f1 z1 from h1)
  obtain ⟨G2, e2⟩ := Polynomial.dvd_iff_isRoot.2 (show IsRoot f2 z2 from h2)
  obtain ⟨G3, e3⟩ := Polynomial.dvd_iff_isRoot.2 (show IsRoot f3 z3 from h3)
  refine ⟨G1 + G2 + G3, ?_⟩
  rw [e1, e2, e3]; ring

lemma natDegree_three (z1 z2 z3 : F) :
    ((X - C z1) * (X - C z2) * (X - C z3)).natDegree = 3 := by
  rw [natDegree_mul (mul_ne_zero (X_sub_C_ne_zero z1) (X_sub_C_ne_zero z2)) (X_sub_C_ne_zero z3),
    natDegree_mul (X_sub_C_ne_zero z1) (X_sub_C_ne_zero z2)]
  simp [natDegree_X_sub_C]


lemma natDegree_PPf_le (S : F) (m : ℕ) : (PPf S m).natDegree ≤ m := (RF_PP S m).1

lemma natDegree_lin_mul_lin_le (a b c d : F) : (lin a b * lin c d).natDegree ≤ 2 :=
  (natDegree_mul_le).trans (add_le_add (natDegree_lin_le a b) (natDegree_lin_le c d))

/-- **(CC) in polynomial form.**  If `Q̂` does not vanish at the three poles, there is a polynomial
`N` of degree `< m` with `H₀ - Q̂ (ℓ u(u+1) + d (u-1)(u+1) + r (u-1)u) = (u-1)u(u+1) N`. -/
theorem CC_poly [CharZero F] (K m : ℕ) (hm : 1 ≤ m) (S θ y : F)
    (hQ1 : (Qh m S).eval (1 - y) ≠ 0) (hQ2 : (Qh m S).eval (-y) ≠ 0)
    (hQ3 : (Qh m S).eval (-y - 1) ≠ 0) :
    ∃ N : F[X], N.natDegree < m ∧
      Hz K m S θ y (S - K + m + 1)
        (-2 * ((K : F) - 1) * (θ + (S - K + m + 1)) - 2 * K ^ 2 + 2 * K - m ^ 2)
        - Qh m S * (C ((aP K m S θ).eval (1 - y) / (Qh m S).eval (1 - y)) * (lin 1 y * lin 1 (y + 1))
            + C ((Dt K m S θ (S - K + m + 1)
                (-2 * ((K : F) - 1) * (θ + (S - K + m + 1)) - 2 * K ^ 2 + 2 * K - m ^ 2)).eval (-y)
                / (Qh m S).eval (-y)) * (lin 1 (y - 1) * lin 1 (y + 1))
            + C ((bP K m S θ).eval (-y - 1) / (Qh m S).eval (-y - 1))
              * (lin 1 (y - 1) * lin 1 y))
      = (lin 1 (y - 1) * lin 1 y * lin 1 (y + 1)) * N := by
  set g : F := S - K + m + 1 with hg
  set c0 : F := -2 * ((K : F) - 1) * (θ + (S - K + m + 1)) - 2 * K ^ 2 + 2 * K - m ^ 2 with hc0
  set ℓ := (aP K m S θ).eval (1 - y) / (Qh m S).eval (1 - y) with hℓ
  set d := (Dt K m S θ g c0).eval (-y) / (Qh m S).eval (-y) with hd
  set r := (bP K m S θ).eval (-y - 1) / (Qh m S).eval (-y - 1) with hr
  have e1 : lin 1 (y - 1) = X - C (1 - y) := by rw [lin_one]; congr 2; ring
  have e2 : lin 1 y = X - C (-y) := lin_one y
  have e3 : lin 1 (y + 1) = X - C (-y - 1) := by rw [lin_one]; congr 2; ring
  obtain ⟨N, hN⟩ := three_div (aP K m S θ - C ℓ * Qh m S) (Dt K m S θ g c0 - C d * Qh m S)
    (bP K m S θ - C r * Qh m S) (1 - y) (-y) (-y - 1)
    (by rw [eval_sub, eval_mul, eval_C, hℓ, div_mul_cancel₀ _ hQ1, sub_self])
    (by rw [eval_sub, eval_mul, eval_C, hd, div_mul_cancel₀ _ hQ2, sub_self])
    (by rw [eval_sub, eval_mul, eval_C, hr, div_mul_cancel₀ _ hQ3, sub_self])
  have heq : Hz K m S θ y g c0 - Qh m S * (C ℓ * (lin 1 y * lin 1 (y + 1))
      + C d * (lin 1 (y - 1) * lin 1 (y + 1)) + C r * (lin 1 (y - 1) * lin 1 y))
      = (lin 1 (y - 1) * lin 1 y * lin 1 (y + 1)) * N := by
    rw [e1, e2, e3, ← hN, Hz_eq, e1, e2, e3]; ring
  refine ⟨N, ?_, heq⟩
  have hdeg : ((lin 1 (y - 1) * lin 1 y * lin 1 (y + 1)) * N).natDegree ≤ m + 2 := by
    rw [← heq]
    refine (natDegree_sub_le _ _).trans (max_le (Hz_natDegree_le K m S θ y) ?_)
    refine (natDegree_mul_le).trans ?_
    have h1 : (C ℓ * (lin 1 y * lin 1 (y + 1))).natDegree ≤ 2 :=
      (natDegree_C_mul_le _ _).trans (natDegree_lin_mul_lin_le _ _ _ _)
    have h2 : (C d * (lin 1 (y - 1) * lin 1 (y + 1))).natDegree ≤ 2 :=
      (natDegree_C_mul_le _ _).trans (natDegree_lin_mul_lin_le _ _ _ _)
    have h3 : (C r * (lin 1 (y - 1) * lin 1 y)).natDegree ≤ 2 :=
      (natDegree_C_mul_le _ _).trans (natDegree_lin_mul_lin_le _ _ _ _)
    have h12 := (natDegree_add_le _ _).trans (max_le h1 h2)
    have h123 := (natDegree_add_le _ _).trans (max_le h12 h3)
    have hQ : (Qh m S).natDegree ≤ m := natDegree_PPf_le _ _
    omega
  by_cases hN0 : N = 0
  · subst hN0; simp; omega
  · have hU : (lin 1 (y - 1) * lin 1 y * lin 1 (y + 1)).natDegree = 3 := by
      rw [e1, e2, e3]; exact natDegree_three _ _ _
    have hUne : (lin 1 (y - 1) * lin 1 y * lin 1 (y + 1)) ≠ 0 := by
      intro h0; rw [h0] at hU; simp at hU
    rw [natDegree_mul hUne hN0, hU] at hdeg
    omega

end CatalanCore.Star.Leonard
