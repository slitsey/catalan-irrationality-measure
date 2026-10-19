module

public import CatalanCore.Star.Leonard.CCExist
public import Mathlib.Tactic.FieldSimp

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


/-! ### Two simple roots -/

lemma two_div (f1 f2 : F[X]) (z1 z2 : F) (h1 : f1.eval z1 = 0) (h2 : f2.eval z2 = 0) :
    ∃ N : F[X], f1 * (X - C z2) - f2 * (X - C z1) = (X - C z1) * (X - C z2) * N := by
  obtain ⟨G1, e1⟩ := Polynomial.dvd_iff_isRoot.2 (show IsRoot f1 z1 from h1)
  obtain ⟨G2, e2⟩ := Polynomial.dvd_iff_isRoot.2 (show IsRoot f2 z2 from h2)
  refine ⟨G1 - G2, ?_⟩
  rw [e1, e2]; ring

lemma natDegree_two (z1 z2 : F) : ((X - C z1) * (X - C z2)).natDegree = 2 := by
  rw [natDegree_mul (X_sub_C_ne_zero z1) (X_sub_C_ne_zero z2)]
  simp

lemma natDegree_N_lt {z1 z2 : F} {N : F[X]} {m : ℕ} (hm : 1 ≤ m)
    (h : ((X - C z1) * (X - C z2) * N).natDegree ≤ m + 1) : N.natDegree < m := by
  by_cases hN0 : N = 0
  · subst hN0; simp; omega
  · have hUne : ((X - C z1) * (X - C z2)) ≠ 0 :=
      mul_ne_zero (X_sub_C_ne_zero z1) (X_sub_C_ne_zero z2)
    rw [natDegree_mul hUne hN0, natDegree_two] at h
    omega

section K4poly

variable [CharZero F] (K m : ℕ) (hm : 1 ≤ m) (S θ y c0 : F) (hK : (K : F) = S + m + 1)

/-- `pK1 = (K-1-a)(z+S+2m+1)`. -/
noncomputable def pK1 : F[X] := lin (-1) ((K : F) - 1 + θ) * lin 1 (S + 2 * m + 1)

/-- `A`-coefficient: `Φ(-y)/P(-y)`. -/
noncomputable def coefA : F :=
  -c0 * (((PPf (S - 1) m).eval (-y)) * (pK1 K m S θ).eval (-y)) / (PPf S m).eval (-y)

/-- `B`-coefficient of `K4a`: `-c₀ p₂(-y-1)`. -/
noncomputable def coefB : F := -c0 * ((lin 1 (1 - θ) * lin 1 1).eval (-y - 1))

lemma natDegree_tail (m : ℕ) (S a b p q : F) :
    (PPf S m * (C a * lin 1 p + C b * lin 1 q)).natDegree ≤ m + 1 := by
  have h1 : (C a * lin 1 p).natDegree ≤ 1 := (natDegree_C_mul_le _ _).trans (natDegree_lin_le _ _)
  have h2 : (C b * lin 1 q).natDegree ≤ 1 := (natDegree_C_mul_le _ _).trans (natDegree_lin_le _ _)
  have h3 := (natDegree_add_le (C a * lin 1 p) (C b * lin 1 q)).trans (max_le h1 h2)
  have h4 := natDegree_PPf_le S m
  exact (natDegree_mul_le).trans (by omega)

include hm hK in
theorem K4a_poly (hP : (PPf S m).eval (-y) ≠ 0) :
    ∃ N : F[X], N.natDegree < m ∧
      C (-c0) * MainA K m S θ y - PPf S m * (C (coefA K m S θ y c0) * lin 1 (y + 1)
        + C (coefB θ y c0) * lin 1 y) = (lin 1 y * lin 1 (y + 1)) * N := by
  have e1 : lin 1 y = X - C (-y) := lin_one y
  have e2 : lin 1 (y + 1) = X - C (-y - 1) := by rw [lin_one]; congr 2; ring
  have hA : coefA K m S θ y c0 * (PPf S m).eval (-y) =
      -c0 * (((PPf (S - 1) m).eval (-y)) * (pK1 K m S θ).eval (-y)) := by
    unfold coefA; field_simp
  obtain ⟨N, hN⟩ := two_div
    (C (-c0) * (PPf (S - 1) m * pK1 K m S θ) - C (coefA K m S θ y c0) * PPf S m)
    (C c0 * (lin 1 (1 - θ) * lin 1 1 * PPf S m) + C (coefB θ y c0) * PPf S m) (-y) (-y - 1)
    (by
      simp only [eval_sub, eval_mul, eval_C]
      linear_combination (-1 : F) * hA)
    (by
      unfold coefB
      simp only [eval_add, eval_mul, eval_C]
      ring)
  have heq : C (-c0) * MainA K m S θ y - PPf S m * (C (coefA K m S θ y c0) * lin 1 (y + 1)
        + C (coefB θ y c0) * lin 1 y) = (lin 1 y * lin 1 (y + 1)) * N := by
    rw [e1, e2, ← hN]
    unfold MainA A3a B3a pK1
    rw [e1, e2]
    simp only [map_neg]
    ring
  refine ⟨N, ?_, heq⟩
  have hdeg : ((lin 1 y * lin 1 (y + 1)) * N).natDegree ≤ m + 1 := by
    rw [← heq]
    exact (natDegree_sub_le _ _).trans (max_le ((natDegree_C_mul_le _ _).trans
      (MainA_natDegree_le K m S θ y hK)) (natDegree_tail m S _ _ _ _))
  rw [e1, e2] at hdeg
  exact natDegree_N_lt hm hdeg


/-- `B`-coefficient of `K4b`: `-c₀ p₂'(1-y)`, `p₂' = (z-θ) z`. -/
noncomputable def coefB' (θ y c0 : F) : F := -c0 * ((lin 1 (-θ) * lin 1 0).eval (1 - y))

include hm hK in
theorem K4b_poly (hP : (PPf S m).eval (-y) ≠ 0) :
    ∃ N : F[X], N.natDegree < m ∧
      C (-c0) * MainB K m S θ y - PPf S m * (C (coefA K m S θ y c0) * lin 1 (y - 1)
        + C (coefB' θ y c0) * lin 1 y) = (lin 1 y * lin 1 (y - 1)) * N := by
  have e1 : lin 1 y = X - C (-y) := lin_one y
  have e2 : lin 1 (y - 1) = X - C (1 - y) := by rw [lin_one]; congr 2; ring
  have hA : coefA K m S θ y c0 * (PPf S m).eval (-y) =
      -c0 * (((PPf (S - 1) m).eval (-y)) * (pK1 K m S θ).eval (-y)) := by
    unfold coefA; field_simp
  obtain ⟨N, hN⟩ := two_div
    (C (-c0) * (PPf (S - 1) m * pK1 K m S θ) - C (coefA K m S θ y c0) * PPf S m)
    (C c0 * (lin 1 (-θ) * lin 1 0 * PPf S m) + C (coefB' θ y c0) * PPf S m) (-y) (1 - y)
    (by
      simp only [eval_sub, eval_mul, eval_C]
      linear_combination (-1 : F) * hA)
    (by
      unfold coefB'
      simp only [eval_add, eval_mul, eval_C]
      ring)
  have heq : C (-c0) * MainB K m S θ y - PPf S m * (C (coefA K m S θ y c0) * lin 1 (y - 1)
        + C (coefB' θ y c0) * lin 1 y) = (lin 1 y * lin 1 (y - 1)) * N := by
    rw [e1, e2, ← hN]
    unfold MainB A3b B3b pK1
    rw [e1, e2]
    simp only [map_neg]
    ring
  refine ⟨N, ?_, heq⟩
  have hdeg : ((lin 1 y * lin 1 (y - 1)) * N).natDegree ≤ m + 1 := by
    rw [← heq]
    exact (natDegree_sub_le _ _).trans (max_le ((natDegree_C_mul_le _ _).trans
      (MainB_natDegree_le K m S θ y hK)) (natDegree_tail m S _ _ _ _))
  rw [e1, e2] at hdeg
  exact natDegree_N_lt hm hdeg

end K4poly

end CatalanCore.Star.Leonard
