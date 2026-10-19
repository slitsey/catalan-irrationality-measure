module

public import CatalanCore.Star.Leonard.CCExist

/-!
# (RC) in polynomial form: the row chain mod `span{c_x : x ∈ X}` (package H2)

`T~ᵀ c_y` has the entries `-σ(a-1)c_y(a-1) + D(a)c_y(a) - τ(a)c_y(a+1)`.  Clearing `P = ∏_{x∈X}(z+x)`:
`σ(a-1) P = p(a-1) (z+S+2m) Q̂`, `τ(a) P = p(a) (z+S+2m+1) Q̂`, so the polynomial
`H₀' = Q̂ α' + P β₀` has degree `≤ m + 2` exactly as for the column chain (roles of `P, Q̂` swapped).
-/

@[expose] public section

open Polynomial

namespace CatalanCore.Star.Leonard

variable {F : Type*} [Field F]

noncomputable def alpha2z (K m : ℕ) (S θ y : F) : F[X] :=
  -(pmz K θ * lin 1 (S + 2 * m) * lin 1 y * lin 1 (y + 1))
  - (pz K θ * lin 1 (S + 2 * m + 1) * lin 1 (y - 1) * lin 1 y)

/-- `H₀' = Q̂ α' + P β₀`. -/
noncomputable def Hz2 (K m : ℕ) (S θ y g c0 : F) : F[X] :=
  PPf (S - 1) m * alpha2z K m S θ y + PPf S m * betaz K m S θ y g c0

noncomputable def alpha2r (K m : ℕ) (S θ y : F) : F[X] :=
  -(lin (-θ) 1 * lin 0 1 * lin ((K : F) + θ) (-1) * lin (S + 2 * m) 1 * lin y 1 * lin (y + 1) 1)
  - (lin (1 - θ) 1 * lin 1 1 * lin ((K : F) - 1 + θ) (-1) * lin (S + 2 * m + 1) 1 *
      lin (y - 1) 1 * lin y 1)

lemma RF_alpha2 (K m : ℕ) (S θ y : F) : RF 6 (alpha2z K m S θ y) (alpha2r K m S θ y) := by
  unfold alpha2z alpha2r pmz pz
  exact RF_sub (RF_neg (RF_lin6 _ _ _ _ _ _ _ _ _ _ _ _)) (RF_lin6 _ _ _ _ _ _ _ _ _ _ _ _)

noncomputable def Hr2 (K m : ℕ) (S θ y g c0 : F) : F[X] :=
  PPr (S - 1) m * alpha2r K m S θ y + PPr S m * betar K m S θ y g c0

lemma RF_H2 (K m : ℕ) (S θ y g c0 : F) :
    RF (m + 6) (Hz2 K m S θ y g c0) (Hr2 K m S θ y g c0) :=
  RF_add (RF_mul (RF_PP (S - 1) m) (RF_alpha2 K m S θ y))
    (RF_mul (RF_PP S m) (RF_beta K m S θ y g c0))

/-- Second ring identity (roles of `P` and `Q̂` swapped). -/
lemma key_ring2 {R : Type*} [CommRing R] (w θ S y K m : R) (hw : w ^ 4 = 0) :
    Jt w 6 (6 * m * ((S - 1) + m + 1)) (3 * m * (m - 1) * ((S - 1) + m + 1) ^ 2 - m * (m ^ 2 - 1))
      (m * (m - 1) * (m - 2) * ((S - 1) + m + 1) ^ 3
          - (m - 2) * ((S - 1) + m + 1) * (m * (m ^ 2 - 1)))
      * (-(Jt w 1 (-θ) 0 0 * Jt w 1 0 0 0 * Jt w (-1) (K + θ) 0 0 * Jt w 1 (S + 2 * m) 0 0
            * Jt w 1 y 0 0 * Jt w 1 (y + 1) 0 0)
        - Jt w 1 (1 - θ) 0 0 * Jt w 1 1 0 0 * Jt w (-1) (K - 1 + θ) 0 0
            * Jt w 1 (S + 2 * m + 1) 0 0 * Jt w 1 (y - 1) 0 0 * Jt w 1 y 0 0)
    + Jt w 6 (6 * m * (S + m + 1)) (3 * m * (m - 1) * (S + m + 1) ^ 2 - m * (m ^ 2 - 1))
      (m * (m - 1) * (m - 2) * (S + m + 1) ^ 3 - (m - 2) * (S + m + 1) * (m * (m ^ 2 - 1)))
      * ((-(Jt w (-1) (K - 1 + θ) 0 0 * Jt w (-1) (K - 1 + θ) 0 0 * Jt w 1 (S + 1) 0 0
            * Jt w 1 (S + 2 * m + 1) 0 0)
          - (Jt w 1 (-θ) 0 0 * Jt w 1 0 0 0 * Jt w 1 (-θ) 0 0 * Jt w 1 0 0 0)
          + (Jt w 0 ((S - K + m + 1) * ((S - K + m + 1) + 1)) 0 0 * Jt w 0 1 0 0
              * Jt w 1 (-θ) 0 0 * Jt w 1 (-θ) 0 0)
          + (Jt w 0 ((S - K + m + 1) * (-2 * (K - 1) * (θ + (S - K + m + 1)) - 2 * K ^ 2 + 2 * K
                - m ^ 2)) 0 0 * Jt w 0 1 0 0 * Jt w 0 1 0 0 * Jt w 1 (-θ) 0 0))
        * Jt w 1 (y - 1) 0 0 * Jt w 1 (y + 1) 0 0) = 0 := by
  simp only [Jt_mul hw, Jt_add, Jt_sub, Jt_neg]
  refine Jt_eq_zero _ _ _ _ ?_ ?_ ?_ ?_ <;> ring


theorem six_phi_Hr2 (K m : ℕ) (S θ y : F) :
    (6 : R4 F) * phi F (Hr2 K m S θ y (S - K + m + 1)
      (-2 * ((K : F) - 1) * (θ + (S - K + m + 1)) - 2 * K ^ 2 + 2 * K - m ^ 2)) = 0 := by
  have key := key_ring2 (phi F X) (algebraMap F (R4 F) θ) (algebraMap F (R4 F) S)
    (algebraMap F (R4 F) y) (K : R4 F) (m : R4 F) (phi_X_pow_four (F := F))
  unfold Hr2 PPr
  rw [map_add, map_mul, map_mul, mul_add, ← mul_assoc, ← mul_assoc, jet_prod_Jt, jet_prod_Jt]
  unfold alpha2r betar Dr
  simp only [phi_lin_Jt, map_add, map_sub, map_neg, map_mul, map_ofNat, map_natCast, map_one,
    map_zero, map_pow, jA1, jA2, jA3]
  exact key

theorem Hz2_natDegree_le [CharZero F] (K m : ℕ) (S θ y : F) :
    (Hz2 K m S θ y (S - K + m + 1)
      (-2 * ((K : F) - 1) * (θ + (S - K + m + 1)) - 2 * K ^ 2 + 2 * K - m ^ 2)).natDegree ≤
      m + 2 := by
  have h6 : (6 : F) ≠ 0 := by norm_num
  have hz : phi F (Hr2 K m S θ y (S - K + m + 1)
      (-2 * ((K : F) - 1) * (θ + (S - K + m + 1)) - 2 * K ^ 2 + 2 * K - m ^ 2)) = 0 := by
    have h := six_phi_Hr2 K m S θ y
    have e : (algebraMap F (R4 F) (6⁻¹)) * (6 : R4 F) = 1 := by
      have : (6 : R4 F) = algebraMap F (R4 F) 6 := (map_ofNat (algebraMap F (R4 F)) 6).symm
      rw [this, ← map_mul, inv_mul_cancel₀ h6, map_one]
    calc _ = (algebraMap F (R4 F) (6⁻¹) * 6) * phi F (Hr2 K m S θ y (S - K + m + 1)
        (-2 * ((K : F) - 1) * (θ + (S - K + m + 1)) - 2 * K ^ 2 + 2 * K - m ^ 2)) := by
          rw [e, one_mul]
      _ = 0 := by rw [mul_assoc, h, mul_zero]
  have := natDegree_le_of_RF (k := 4) (by omega) (RF_H2 K m S θ y (S - K + m + 1)
    (-2 * ((K : F) - 1) * (θ + (S - K + m + 1)) - 2 * K ^ 2 + 2 * K - m ^ 2))
    (phi_eq_zero_iff.1 hz)
  omega

section Exist2

variable (K m : ℕ) (S θ y g c0 : F)

noncomputable def aP2 : F[X] := -(pmz K θ * lin 1 (S + 2 * m) * PPf (S - 1) m)
noncomputable def bP2 : F[X] := -(pz K θ * lin 1 (S + 2 * m + 1) * PPf (S - 1) m)
noncomputable def Dt2 : F[X] := Dz K m S θ g c0 * PPf S m
noncomputable def Qh2 : F[X] := PPf S m

lemma Hz2_eq : Hz2 K m S θ y g c0 =
    aP2 K m S θ * (lin 1 y * lin 1 (y + 1)) + bP2 K m S θ * (lin 1 (y - 1) * lin 1 y)
      + Dt2 K m S θ g c0 * (lin 1 (y - 1) * lin 1 (y + 1)) := by
  unfold Hz2 alpha2z betaz aP2 bP2 Dt2; ring

end Exist2

/-- **(RC) in polynomial form.** -/
theorem RC_poly [CharZero F] (K m : ℕ) (hm : 1 ≤ m) (S θ y : F)
    (hQ1 : (Qh2 m S).eval (1 - y) ≠ 0) (hQ2 : (Qh2 m S).eval (-y) ≠ 0)
    (hQ3 : (Qh2 m S).eval (-y - 1) ≠ 0) :
    ∃ N : F[X], N.natDegree < m ∧
      Hz2 K m S θ y (S - K + m + 1)
        (-2 * ((K : F) - 1) * (θ + (S - K + m + 1)) - 2 * K ^ 2 + 2 * K - m ^ 2)
        - Qh2 m S * (C ((aP2 K m S θ).eval (1 - y) / (Qh2 m S).eval (1 - y)) * (lin 1 y * lin 1 (y + 1))
            + C ((Dt2 K m S θ (S - K + m + 1)
                (-2 * ((K : F) - 1) * (θ + (S - K + m + 1)) - 2 * K ^ 2 + 2 * K - m ^ 2)).eval (-y)
                / (Qh2 m S).eval (-y)) * (lin 1 (y - 1) * lin 1 (y + 1))
            + C ((bP2 K m S θ).eval (-y - 1) / (Qh2 m S).eval (-y - 1))
              * (lin 1 (y - 1) * lin 1 y))
      = (lin 1 (y - 1) * lin 1 y * lin 1 (y + 1)) * N := by
  set g : F := S - K + m + 1 with hg
  set c0 : F := -2 * ((K : F) - 1) * (θ + (S - K + m + 1)) - 2 * K ^ 2 + 2 * K - m ^ 2 with hc0
  set ℓ := (aP2 K m S θ).eval (1 - y) / (Qh2 m S).eval (1 - y) with hℓ
  set d := (Dt2 K m S θ g c0).eval (-y) / (Qh2 m S).eval (-y) with hd
  set r := (bP2 K m S θ).eval (-y - 1) / (Qh2 m S).eval (-y - 1) with hr
  have e1 : lin 1 (y - 1) = X - C (1 - y) := by rw [lin_one]; congr 2; ring
  have e2 : lin 1 y = X - C (-y) := lin_one y
  have e3 : lin 1 (y + 1) = X - C (-y - 1) := by rw [lin_one]; congr 2; ring
  obtain ⟨N, hN⟩ := three_div (aP2 K m S θ - C ℓ * Qh2 m S) (Dt2 K m S θ g c0 - C d * Qh2 m S)
    (bP2 K m S θ - C r * Qh2 m S) (1 - y) (-y) (-y - 1)
    (by rw [eval_sub, eval_mul, eval_C, hℓ, div_mul_cancel₀ _ hQ1, sub_self])
    (by rw [eval_sub, eval_mul, eval_C, hd, div_mul_cancel₀ _ hQ2, sub_self])
    (by rw [eval_sub, eval_mul, eval_C, hr, div_mul_cancel₀ _ hQ3, sub_self])
  have heq : Hz2 K m S θ y g c0 - Qh2 m S * (C ℓ * (lin 1 y * lin 1 (y + 1))
      + C d * (lin 1 (y - 1) * lin 1 (y + 1)) + C r * (lin 1 (y - 1) * lin 1 y))
      = (lin 1 (y - 1) * lin 1 y * lin 1 (y + 1)) * N := by
    rw [e1, e2, e3, ← hN, Hz2_eq, e1, e2, e3]; ring
  refine ⟨N, ?_, heq⟩
  have hdeg : ((lin 1 (y - 1) * lin 1 y * lin 1 (y + 1)) * N).natDegree ≤ m + 2 := by
    rw [← heq]
    refine (natDegree_sub_le _ _).trans (max_le (Hz2_natDegree_le K m S θ y) ?_)
    refine (natDegree_mul_le).trans ?_
    have h1 : (C ℓ * (lin 1 y * lin 1 (y + 1))).natDegree ≤ 2 :=
      (natDegree_C_mul_le _ _).trans (natDegree_lin_mul_lin_le _ _ _ _)
    have h2 : (C d * (lin 1 (y - 1) * lin 1 (y + 1))).natDegree ≤ 2 :=
      (natDegree_C_mul_le _ _).trans (natDegree_lin_mul_lin_le _ _ _ _)
    have h3 : (C r * (lin 1 (y - 1) * lin 1 y)).natDegree ≤ 2 :=
      (natDegree_C_mul_le _ _).trans (natDegree_lin_mul_lin_le _ _ _ _)
    have h12 := (natDegree_add_le _ _).trans (max_le h1 h2)
    have h123 := (natDegree_add_le _ _).trans (max_le h12 h3)
    have hQ : (Qh2 m S).natDegree ≤ m := natDegree_PPf_le _ _
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
