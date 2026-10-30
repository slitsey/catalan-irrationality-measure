module

public import CatalanCore.Star.Leonard.Jets

/-!
# (CC) in polynomial form: the degree bound (package H2 core)

With `z = θ + a` and `Q̂(z) = ∏_{t∈Y}(z+t)`, the column chain `T~ c_y ≡ l c_{y-1} + d c_y + r c_{y+1}
mod span{c_t : t∈Y}` is equivalent to: the polynomial

  `H₀ = P·α + Q̂·β₀`,   `α = -p₋·(z+S)·u(u+1) - p·(z+S+1)·(u-1)u`,   `β₀ = D̃·(u-1)(u+1)`,   `u = z+y`,

has degree `≤ m+2` (here `P = ∏_{i=1}^m (z+S+2i)`, `Q̂ = P(z-1)`).  `H0_natDegree_le` proves this
for symbolic `m` through the top-coefficient jets of `P` and `Q̂` (`Jets.lean`) and reflection.
-/

@[expose] public section

open Polynomial

namespace CatalanCore.Star.Leonard

variable {F : Type*} [Field F]

/-- `P(z) = ∏_{i=1}^m (z + S + 2i)`. -/
noncomputable def PPf (S : F) (m : ℕ) : F[X] := ∏ i ∈ Finset.range m, lin 1 (S + 2 * ((i : F) + 1))

/-- `p(a)` with `a = z - θ`: `(z-θ+1)(z+1)(K-1+θ-z)`. -/
noncomputable def pz (K : ℕ) (θ : F) : F[X] := lin 1 (1 - θ) * lin 1 1 * lin (-1) ((K : F) - 1 + θ)

/-- `p(a-1)`: `(z-θ) z (K+θ-z)`. -/
noncomputable def pmz (K : ℕ) (θ : F) : F[X] := lin 1 (-θ) * lin 1 0 * lin (-1) ((K : F) + θ)

/-- `D(a)` with `a = z - θ`, in 4-fold product form. -/
noncomputable def Dz (K m : ℕ) (S θ g c0 : F) : F[X] :=
  -(lin (-1) ((K : F) - 1 + θ) * lin (-1) ((K : F) - 1 + θ) * lin 1 (S + 1) * lin 1 (S + 2 * m + 1))
  - (lin 1 (-θ) * lin 1 0 * lin 1 (-θ) * lin 1 0)
  + (lin 0 (g * (g + 1)) * lin 0 1 * lin 1 (-θ) * lin 1 (-θ))
  + (lin 0 (g * c0) * lin 0 1 * lin 0 1 * lin 1 (-θ))

noncomputable def alphaz (K : ℕ) (S θ y : F) : F[X] :=
  -(pmz K θ * lin 1 S * lin 1 y * lin 1 (y + 1))
  - (pz K θ * lin 1 (S + 1) * lin 1 (y - 1) * lin 1 y)

noncomputable def betaz (K m : ℕ) (S θ y g c0 : F) : F[X] :=
  Dz K m S θ g c0 * lin 1 (y - 1) * lin 1 (y + 1)

/-- `H₀ = P α + Q̂ β₀` with `Q̂ = P(S-1)`. -/
noncomputable def Hz (K m : ℕ) (S θ y g c0 : F) : F[X] :=
  PPf S m * alphaz K S θ y + PPf (S - 1) m * betaz K m S θ y g c0


/-! ### Reflection -/

lemma RF_lin4 (a1 b1 a2 b2 a3 b3 a4 b4 : F) :
    RF 4 (lin a1 b1 * lin a2 b2 * lin a3 b3 * lin a4 b4)
      (lin b1 a1 * lin b2 a2 * lin b3 a3 * lin b4 a4) :=
  RF_mul (RF_mul (RF_mul (RF_lin _ _) (RF_lin _ _)) (RF_lin _ _)) (RF_lin _ _)

lemma RF_lin6 (a1 b1 a2 b2 a3 b3 a4 b4 a5 b5 a6 b6 : F) :
    RF 6 (lin a1 b1 * lin a2 b2 * lin a3 b3 * lin a4 b4 * lin a5 b5 * lin a6 b6)
      (lin b1 a1 * lin b2 a2 * lin b3 a3 * lin b4 a4 * lin b5 a5 * lin b6 a6) :=
  RF_mul (RF_mul (RF_mul (RF_mul (RF_mul (RF_lin _ _) (RF_lin _ _)) (RF_lin _ _)) (RF_lin _ _))
    (RF_lin _ _)) (RF_lin _ _)

/-- Reflected `α`. -/
noncomputable def alphar (K : ℕ) (S θ y : F) : F[X] :=
  -(lin (-θ) 1 * lin 0 1 * lin ((K : F) + θ) (-1) * lin S 1 * lin y 1 * lin (y + 1) 1)
  - (lin (1 - θ) 1 * lin 1 1 * lin ((K : F) - 1 + θ) (-1) * lin (S + 1) 1 * lin (y - 1) 1 *
      lin y 1)

lemma RF_alpha (K : ℕ) (S θ y : F) : RF 6 (alphaz K S θ y) (alphar K S θ y) := by
  unfold alphaz alphar pmz pz
  exact RF_sub (RF_neg (RF_lin6 _ _ _ _ _ _ _ _ _ _ _ _)) (RF_lin6 _ _ _ _ _ _ _ _ _ _ _ _)

/-- Reflected `D̃`. -/
noncomputable def Dr (K m : ℕ) (S θ g c0 : F) : F[X] :=
  -(lin ((K : F) - 1 + θ) (-1) * lin ((K : F) - 1 + θ) (-1) * lin (S + 1) 1 *
      lin (S + 2 * m + 1) 1)
  - (lin (-θ) 1 * lin 0 1 * lin (-θ) 1 * lin 0 1)
  + (lin (g * (g + 1)) 0 * lin 1 0 * lin (-θ) 1 * lin (-θ) 1)
  + (lin (g * c0) 0 * lin 1 0 * lin 1 0 * lin (-θ) 1)

lemma RF_Dz (K m : ℕ) (S θ g c0 : F) : RF 4 (Dz K m S θ g c0) (Dr K m S θ g c0) := by
  unfold Dz Dr
  exact RF_add (RF_add (RF_sub (RF_neg (RF_lin4 _ _ _ _ _ _ _ _)) (RF_lin4 _ _ _ _ _ _ _ _))
    (RF_lin4 _ _ _ _ _ _ _ _)) (RF_lin4 _ _ _ _ _ _ _ _)

/-- Reflected `β₀`. -/
noncomputable def betar (K m : ℕ) (S θ y g c0 : F) : F[X] :=
  Dr K m S θ g c0 * lin (y - 1) 1 * lin (y + 1) 1

lemma RF_beta (K m : ℕ) (S θ y g c0 : F) :
    RF 6 (betaz K m S θ y g c0) (betar K m S θ y g c0) := by
  unfold betaz betar
  exact RF_mul (RF_mul (RF_Dz K m S θ g c0) (RF_lin _ _)) (RF_lin _ _)

/-- Reflected `P`. -/
noncomputable def PPr (S : F) (m : ℕ) : F[X] :=
  ∏ i ∈ Finset.range m, lin (S + 2 * ((i : F) + 1)) 1

lemma RF_PP (S : F) (m : ℕ) : RF m (PPf S m) (PPr S m) := by
  unfold PPf PPr
  exact RF_prod_range m (fun _ => 1) (fun i => S + 2 * ((i : F) + 1))

/-- Reflected `H₀`. -/
noncomputable def Hr (K m : ℕ) (S θ y g c0 : F) : F[X] :=
  PPr S m * alphar K S θ y + PPr (S - 1) m * betar K m S θ y g c0

lemma RF_H (K m : ℕ) (S θ y g c0 : F) :
    RF (m + 6) (Hz K m S θ y g c0) (Hr K m S θ y g c0) :=
  RF_add (RF_mul (RF_PP S m) (RF_alpha K S θ y)) (RF_mul (RF_PP (S - 1) m) (RF_beta K m S θ y g c0))


/-! ### The top-coefficient identity -/

lemma phi_lin (a b : F) :
    phi F (lin a b) = algebraMap F (R4 F) a * phi F X + algebraMap F (R4 F) b := by
  have hC : ∀ c : F, phi F (C c) = algebraMap F (R4 F) c := fun c => by
    rw [← Polynomial.algebraMap_eq]; exact (phi F).commutes c
  simp [lin, hC]

/-! #### Truncated jets `a₀ + a₁ w + a₂ w² + a₃ w³` with `w⁴ = 0` -/

/-- `a₀ + a₁ w + a₂ w² + a₃ w³`. -/
def Jt {R : Type*} [CommRing R] (w a0 a1 a2 a3 : R) : R := a0 + a1 * w + a2 * w ^ 2 + a3 * w ^ 3

section Jt

variable {R : Type*} [CommRing R] {w : R} (hw : w ^ 4 = 0)

include hw in
lemma Jt_mul (a0 a1 a2 a3 b0 b1 b2 b3 : R) :
    Jt w a0 a1 a2 a3 * Jt w b0 b1 b2 b3 =
      Jt w (a0 * b0) (a0 * b1 + a1 * b0) (a0 * b2 + a1 * b1 + a2 * b0)
        (a0 * b3 + a1 * b2 + a2 * b1 + a3 * b0) := by
  unfold Jt
  linear_combination (a1 * b3 + a2 * b2 + a3 * b1 + w * (a2 * b3 + a3 * b2) + w ^ 2 * a3 * b3) * hw

lemma Jt_add (a0 a1 a2 a3 b0 b1 b2 b3 : R) :
    Jt w a0 a1 a2 a3 + Jt w b0 b1 b2 b3 = Jt w (a0 + b0) (a1 + b1) (a2 + b2) (a3 + b3) := by
  unfold Jt; ring

lemma Jt_sub (a0 a1 a2 a3 b0 b1 b2 b3 : R) :
    Jt w a0 a1 a2 a3 - Jt w b0 b1 b2 b3 = Jt w (a0 - b0) (a1 - b1) (a2 - b2) (a3 - b3) := by
  unfold Jt; ring

lemma Jt_neg (a0 a1 a2 a3 : R) : -Jt w a0 a1 a2 a3 = Jt w (-a0) (-a1) (-a2) (-a3) := by
  unfold Jt; ring

lemma Jt_eq_zero (a0 a1 a2 a3 : R) (h0 : a0 = 0) (h1 : a1 = 0) (h2 : a2 = 0) (h3 : a3 = 0) :
    Jt w a0 a1 a2 a3 = 0 := by
  subst h0 h1 h2 h3; unfold Jt; ring

end Jt

/-- The pure ring identity behind the top coefficients. -/
lemma key_ring {R : Type*} [CommRing R] (w θ S y K m : R) (hw : w ^ 4 = 0) :
    Jt w 6 (6 * m * (S + m + 1)) (3 * m * (m - 1) * (S + m + 1) ^ 2 - m * (m ^ 2 - 1))
      (m * (m - 1) * (m - 2) * (S + m + 1) ^ 3 - (m - 2) * (S + m + 1) * (m * (m ^ 2 - 1)))
      * (-(Jt w 1 (-θ) 0 0 * Jt w 1 0 0 0 * Jt w (-1) (K + θ) 0 0 * Jt w 1 S 0 0 * Jt w 1 y 0 0
            * Jt w 1 (y + 1) 0 0)
        - Jt w 1 (1 - θ) 0 0 * Jt w 1 1 0 0 * Jt w (-1) (K - 1 + θ) 0 0 * Jt w 1 (S + 1) 0 0
            * Jt w 1 (y - 1) 0 0 * Jt w 1 y 0 0)
    + Jt w 6 (6 * m * ((S - 1) + m + 1)) (3 * m * (m - 1) * ((S - 1) + m + 1) ^ 2 - m * (m ^ 2 - 1))
      (m * (m - 1) * (m - 2) * ((S - 1) + m + 1) ^ 3
          - (m - 2) * ((S - 1) + m + 1) * (m * (m ^ 2 - 1)))
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


lemma phi_lin_Jt (a b : F) :
    phi F (lin a b) = Jt (phi F X) (algebraMap F (R4 F) b) (algebraMap F (R4 F) a) 0 0 := by
  rw [phi_lin]; unfold Jt; ring

lemma jet_prod_Jt (S : F) (m : ℕ) :
    (6 : R4 F) * phi F (∏ i ∈ Finset.range m, lin (S + 2 * ((i : F) + 1)) 1) =
      Jt (phi F X) 6 (algebraMap F (R4 F) (jA1 m S)) (algebraMap F (R4 F) (jA2 m S))
        (algebraMap F (R4 F) (jA3 m S)) := by
  rw [jet_prod]; unfold Jt; ring

theorem six_phi_Hr (K m : ℕ) (S θ y : F) :
    (6 : R4 F) * phi F (Hr K m S θ y (S - K + m + 1)
      (-2 * ((K : F) - 1) * (θ + (S - K + m + 1)) - 2 * K ^ 2 + 2 * K - m ^ 2)) = 0 := by
  have key := key_ring (phi F X) (algebraMap F (R4 F) θ) (algebraMap F (R4 F) S)
    (algebraMap F (R4 F) y) (K : R4 F) (m : R4 F) (phi_X_pow_four (F := F))
  unfold Hr PPr
  rw [map_add, map_mul, map_mul, mul_add, ← mul_assoc, ← mul_assoc, jet_prod_Jt, jet_prod_Jt]
  unfold alphar betar Dr
  simp only [phi_lin_Jt, map_add, map_sub, map_neg, map_mul, map_ofNat, map_natCast, map_one,
    map_zero, map_pow, jA1, jA2, jA3]
  exact key


/-- **The degree bound.**  `deg H₀ ≤ m + 2` for symbolic `m`, with `g = S - K + m + 1`. -/
theorem Hz_natDegree_le [CharZero F] (K m : ℕ) (S θ y : F) :
    (Hz K m S θ y (S - K + m + 1)
      (-2 * ((K : F) - 1) * (θ + (S - K + m + 1)) - 2 * K ^ 2 + 2 * K - m ^ 2)).natDegree ≤
      m + 2 := by
  have h6 : (6 : F) ≠ 0 := by norm_num
  have hz : phi F (Hr K m S θ y (S - K + m + 1)
      (-2 * ((K : F) - 1) * (θ + (S - K + m + 1)) - 2 * K ^ 2 + 2 * K - m ^ 2)) = 0 := by
    have h := six_phi_Hr K m S θ y
    have e : (algebraMap F (R4 F) (6⁻¹)) * (6 : R4 F) = 1 := by
      have : (6 : R4 F) = algebraMap F (R4 F) 6 := (map_ofNat (algebraMap F (R4 F)) 6).symm
      rw [this, ← map_mul, inv_mul_cancel₀ h6, map_one]
    calc _ = (algebraMap F (R4 F) (6⁻¹) * 6) * phi F (Hr K m S θ y (S - K + m + 1)
        (-2 * ((K : F) - 1) * (θ + (S - K + m + 1)) - 2 * K ^ 2 + 2 * K - m ^ 2)) := by rw [e, one_mul]
      _ = 0 := by rw [mul_assoc, h, mul_zero]
  have := natDegree_le_of_RF (k := 4) (by omega) (RF_H K m S θ y (S - K + m + 1)
    (-2 * ((K : F) - 1) * (θ + (S - K + m + 1)) - 2 * K ^ 2 + 2 * K - m ^ 2))
    (phi_eq_zero_iff.1 hz)
  omega

end CatalanCore.Star.Leonard
