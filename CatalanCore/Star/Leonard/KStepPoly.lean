module

public import CatalanCore.Star.Leonard.CCExist

/-!
# K-step relations (K4a/K4b) in polynomial form (package H5)

At `g = 0` (`K = S + m + 1`) the Darboux map `X = diag(D)·U` sends Cauchy columns to Cauchy columns
of the next instance modulo `span WY'`.  Clearing `P = ∏_{x∈X}(z+x)`:
`P·D_i μ_i = -c₀ (K-1-a)(z+S+2m+1) Q̂`, `P·D_i σ_i = c₀ (a+1)(a+1+θ) P`, and the degree bound
`deg ≤ m + 1` of the main part needs only the first two top coefficients (`R2 = F[X]/(X²)` jets).
-/

@[expose] public section

open Polynomial

namespace CatalanCore.Star.Leonard

variable {F : Type*} [Field F]

/-- `F[X]/(X²)`. -/
abbrev R2 (F : Type*) [Field F] := F[X] ⧸ Ideal.span {(X : F[X]) ^ 2}

noncomputable def phi2 (F : Type*) [Field F] : F[X] →ₐ[F] R2 F := Ideal.Quotient.mkₐ F _

lemma phi2_eq_zero_iff {f : F[X]} : phi2 F f = 0 ↔ (X : F[X]) ^ 2 ∣ f := by
  unfold phi2
  rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]

lemma phi2_X_sq : (phi2 F X) ^ 2 = 0 := by
  rw [← map_pow, phi2_eq_zero_iff]

lemma phi2_lin (a b : F) :
    phi2 F (lin a b) = algebraMap F (R2 F) b + algebraMap F (R2 F) a * phi2 F X := by
  have hC : ∀ c : F, phi2 F (C c) = algebraMap F (R2 F) c := fun c => by
    rw [← Polynomial.algebraMap_eq]; exact (phi2 F).commutes c
  simp [lin, hC]; ring

/-- `∏ (1 + c_i W) ≡ 1 + (Σ c_i) W (mod W²)` for the progression `S + 2(i+1)`. -/
lemma jet2_prod (S : F) (m : ℕ) :
    phi2 F (∏ i ∈ Finset.range m, lin (S + 2 * ((i : F) + 1)) 1) =
      1 + algebraMap F (R2 F) ((m : F) * (S + m + 1)) * phi2 F X := by
  induction m with
  | zero => simp
  | succ m ih =>
    have e : ((m + 1 : ℕ) : F) * (S + ((m + 1 : ℕ) : F) + 1) =
        (m : F) * (S + m + 1) + (S + 2 * ((m : F) + 1)) := by push_cast; ring
    rw [Finset.prod_range_succ, map_mul, ih, phi2_lin, e]
    simp only [map_add, map_one]
    linear_combination (algebraMap F (R2 F) ((m : F) * (S + m + 1)) *
      (algebraMap F (R2 F) S + algebraMap F (R2 F) (2 * ((m : F) + 1)))) * (phi2_X_sq (F := F))


/-! ### Truncated first-order jets -/

def Jt2 {R : Type*} [CommRing R] (w a0 a1 : R) : R := a0 + a1 * w

section Jt2

variable {R : Type*} [CommRing R] {w : R} (hw : w ^ 2 = 0)

include hw in
lemma Jt2_mul (a0 a1 b0 b1 : R) :
    Jt2 w a0 a1 * Jt2 w b0 b1 = Jt2 w (a0 * b0) (a0 * b1 + a1 * b0) := by
  unfold Jt2
  linear_combination (a1 * b1) * hw

lemma Jt2_add (a0 a1 b0 b1 : R) : Jt2 w a0 a1 + Jt2 w b0 b1 = Jt2 w (a0 + b0) (a1 + b1) := by
  unfold Jt2; ring

lemma Jt2_eq_zero (a0 a1 : R) (h0 : a0 = 0) (h1 : a1 = 0) : Jt2 w a0 a1 = 0 := by
  subst h0 h1; unfold Jt2; ring

end Jt2

/-- Ring identity for `K4a`. -/
lemma key_K4a {R : Type*} [CommRing R] (w θ S y K m : R) (hw : w ^ 2 = 0)
    (hKS : K = S + m + 1) :
    Jt2 w 1 (m * ((S - 1) + m + 1))
        * (Jt2 w (-1) (K - 1 + θ) * Jt2 w 1 (S + 2 * m + 1) * Jt2 w 1 (y + 1))
      + Jt2 w 1 (m * (S + m + 1))
        * (Jt2 w 1 (1 - θ) * Jt2 w 1 1 * Jt2 w 1 y) = 0 := by
  simp only [Jt2_mul hw, Jt2_add]
  refine Jt2_eq_zero _ _ ?_ ?_
  · ring
  · subst hKS; ring

/-- Ring identity for `K4b`. -/
lemma key_K4b {R : Type*} [CommRing R] (w θ S y K m : R) (hw : w ^ 2 = 0)
    (hKS : K = S + m + 1) :
    Jt2 w 1 (m * ((S - 1) + m + 1))
        * (Jt2 w (-1) (K - 1 + θ) * Jt2 w 1 (S + 2 * m + 1) * Jt2 w 1 (y - 1))
      + Jt2 w 1 (m * (S + m + 1))
        * (Jt2 w 1 (-θ) * Jt2 w 1 0 * Jt2 w 1 y) = 0 := by
  simp only [Jt2_mul hw, Jt2_add]
  refine Jt2_eq_zero _ _ ?_ ?_
  · ring
  · subst hKS; ring


/-! ### Degree bounds -/

lemma jet2_prod_Jt2 (S : F) (m : ℕ) :
    phi2 F (∏ i ∈ Finset.range m, lin (S + 2 * ((i : F) + 1)) 1) =
      Jt2 (phi2 F X) 1 (algebraMap F (R2 F) ((m : F) * (S + m + 1))) := by
  rw [jet2_prod]; unfold Jt2; ring

lemma phi2_lin_Jt2 (a b : F) :
    phi2 F (lin a b) = Jt2 (phi2 F X) (algebraMap F (R2 F) b) (algebraMap F (R2 F) a) := by
  rw [phi2_lin]; unfold Jt2; ring

/-- `A₃ = (K-1-a)(z+S+2m+1)(z+y+1)`. -/
noncomputable def A3a (K m : ℕ) (S θ y : F) : F[X] :=
  lin (-1) ((K : F) - 1 + θ) * lin 1 (S + 2 * m + 1) * lin 1 (y + 1)

noncomputable def B3a (θ y : F) : F[X] := lin 1 (1 - θ) * lin 1 1 * lin 1 y

noncomputable def A3b (K m : ℕ) (S θ y : F) : F[X] :=
  lin (-1) ((K : F) - 1 + θ) * lin 1 (S + 2 * m + 1) * lin 1 (y - 1)

noncomputable def B3b (θ y : F) : F[X] := lin 1 (-θ) * lin 1 0 * lin 1 y

noncomputable def MainA (K m : ℕ) (S θ y : F) : F[X] :=
  PPf (S - 1) m * A3a K m S θ y + PPf S m * B3a θ y

noncomputable def MainB (K m : ℕ) (S θ y : F) : F[X] :=
  PPf (S - 1) m * A3b K m S θ y + PPf S m * B3b θ y

theorem MainA_natDegree_le [CharZero F] (K m : ℕ) (S θ y : F) (hK : (K : F) = S + m + 1) :
    (MainA K m S θ y).natDegree ≤ m + 1 := by
  have hA : RF 3 (A3a K m S θ y)
      (lin ((K : F) - 1 + θ) (-1) * lin (S + 2 * m + 1) 1 * lin (y + 1) 1) :=
    RF_mul (RF_mul (RF_lin _ _) (RF_lin _ _)) (RF_lin _ _)
  have hB : RF 3 (B3a θ y) (lin (1 - θ) 1 * lin 1 1 * lin y 1) :=
    RF_mul (RF_mul (RF_lin _ _) (RF_lin _ _)) (RF_lin _ _)
  have hR : RF (m + 3) (MainA K m S θ y)
      (PPr (S - 1) m * (lin ((K : F) - 1 + θ) (-1) * lin (S + 2 * m + 1) 1 * lin (y + 1) 1)
        + PPr S m * (lin (1 - θ) 1 * lin 1 1 * lin y 1)) :=
    RF_add (RF_mul (RF_PP (S - 1) m) hA) (RF_mul (RF_PP S m) hB)
  have key := key_K4a (phi2 F X) (algebraMap F (R2 F) θ) (algebraMap F (R2 F) S)
    (algebraMap F (R2 F) y) (K : R2 F) (m : R2 F) (phi2_X_sq (F := F))
    (by have := congrArg (algebraMap F (R2 F)) hK; simpa using this)
  have hz : phi2 F (PPr (S - 1) m * (lin ((K : F) - 1 + θ) (-1) * lin (S + 2 * m + 1) 1 *
        lin (y + 1) 1) + PPr S m * (lin (1 - θ) 1 * lin 1 1 * lin y 1)) = 0 := by
    unfold PPr
    simp only [map_add, map_mul, jet2_prod_Jt2, phi2_lin_Jt2, map_sub, map_neg, map_ofNat,
      map_natCast, map_one, map_zero]
    exact key
  have := natDegree_le_of_RF (k := 2) (by omega) hR (phi2_eq_zero_iff.1 hz)
  omega

theorem MainB_natDegree_le [CharZero F] (K m : ℕ) (S θ y : F) (hK : (K : F) = S + m + 1) :
    (MainB K m S θ y).natDegree ≤ m + 1 := by
  have hA : RF 3 (A3b K m S θ y)
      (lin ((K : F) - 1 + θ) (-1) * lin (S + 2 * m + 1) 1 * lin (y - 1) 1) :=
    RF_mul (RF_mul (RF_lin _ _) (RF_lin _ _)) (RF_lin _ _)
  have hB : RF 3 (B3b θ y) (lin (-θ) 1 * lin 0 1 * lin y 1) :=
    RF_mul (RF_mul (RF_lin _ _) (RF_lin _ _)) (RF_lin _ _)
  have hR : RF (m + 3) (MainB K m S θ y)
      (PPr (S - 1) m * (lin ((K : F) - 1 + θ) (-1) * lin (S + 2 * m + 1) 1 * lin (y - 1) 1)
        + PPr S m * (lin (-θ) 1 * lin 0 1 * lin y 1)) :=
    RF_add (RF_mul (RF_PP (S - 1) m) hA) (RF_mul (RF_PP S m) hB)
  have key := key_K4b (phi2 F X) (algebraMap F (R2 F) θ) (algebraMap F (R2 F) S)
    (algebraMap F (R2 F) y) (K : R2 F) (m : R2 F) (phi2_X_sq (F := F))
    (by have := congrArg (algebraMap F (R2 F)) hK; simpa using this)
  have hz : phi2 F (PPr (S - 1) m * (lin ((K : F) - 1 + θ) (-1) * lin (S + 2 * m + 1) 1 *
        lin (y - 1) 1) + PPr S m * (lin (-θ) 1 * lin 0 1 * lin y 1)) = 0 := by
    unfold PPr
    simp only [map_add, map_mul, jet2_prod_Jt2, phi2_lin_Jt2, map_sub, map_neg, map_ofNat,
      map_natCast, map_one, map_zero]
    exact key
  have := natDegree_le_of_RF (k := 2) (by omega) hR (phi2_eq_zero_iff.1 hz)
  omega

end CatalanCore.Star.Leonard
