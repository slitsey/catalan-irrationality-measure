module

public import CatalanCore.Star.Leonard.Ttil

/-!
# The Darboux map `X` (package H5 glue)

`Xmat K m S θ : Matrix (Fin (K-1)) (Fin K) F` with `X = diag(D_0..D_{K-2}) · U_{[0,K-2],[0,K-1]}`,
i.e. `(X v)_i = D_i μ_i v_i - D_i σ_i v_{i+1}`.  `K4a_col`/`K4b_col` restate (K4a)/(K4b) as vector
identities on the Cauchy columns `wcol` of the two instances `(K, m, S)` and `(K-1, m, S+1)`.
-/

@[expose] public section

open Finset Matrix

namespace CatalanCore.Star.Leonard

variable {F : Type*} [Field F]

/-- `X = diag(D)·U` (last row dropped). -/
noncomputable def Xmat (K m S : ℕ) (θ : F) : Matrix (Fin (K - 1)) (Fin K) F :=
  Matrix.of fun i j =>
    if (j : ℕ) = i then Dfac K m S θ i * mu K m S θ i
    else if (j : ℕ) = i + 1 then -(Dfac K m S θ i * sigma K m S θ i) else 0

lemma Xmat_mulVec (K m S : ℕ) (θ : F) (g : Fin K → F) (i : Fin (K - 1)) :
    (Xmat K m S θ *ᵥ g) i =
      Dfac K m S θ i * mu K m S θ i * g ⟨i, by omega⟩
        + -(Dfac K m S θ i * sigma K m S θ i) * g ⟨i + 1, by omega⟩ := by
  have hi := i.2
  have hT : ∀ j : Fin K, Xmat K m S θ i j * g j =
      (if (j : ℕ) = i then Dfac K m S θ i * mu K m S θ i * g j else 0)
        + (if (j : ℕ) = i + 1 then -(Dfac K m S θ i * sigma K m S θ i) * g j else 0) := by
    intro j
    simp only [Xmat, Matrix.of_apply]
    split_ifs <;> first | (exfalso; omega) | simp
  simp only [Matrix.mulVec, dotProduct, hT, Finset.sum_add_distrib]
  rw [CatalanCore.sum_ite_val_eq (i : ℕ) (fun j => Dfac K m S θ i * mu K m S θ i * g j),
    CatalanCore.sum_ite_val_eq ((i : ℕ) + 1)
      (fun j => -(Dfac K m S θ i * sigma K m S θ i) * g j)]
  rw [dif_pos (by omega), dif_pos (by omega)]

lemma XmatT_mulVec (K m S : ℕ) (θ : F) (g : Fin (K - 1) → F) (j : Fin K) :
    ((Xmat K m S θ)ᵀ *ᵥ g) j =
      (if h : (j : ℕ) < K - 1 then Dfac K m S θ j * mu K m S θ j * g ⟨j, h⟩ else 0)
        + (if h : 0 < (j : ℕ) then
            -(Dfac K m S θ (((j : ℕ) - 1 : ℕ)) * sigma K m S θ (((j : ℕ) - 1 : ℕ)))
              * g ⟨(j : ℕ) - 1, by have := j.2; omega⟩ else 0) := by
  have hT : ∀ i : Fin (K - 1), (Xmat K m S θ)ᵀ j i * g i =
      (if (i : ℕ) = j then Dfac K m S θ i * mu K m S θ i * g i else 0)
        + (if (j : ℕ) = i + 1 then -(Dfac K m S θ i * sigma K m S θ i) * g i else 0) := by
    intro i
    simp only [Matrix.transpose_apply, Xmat, Matrix.of_apply]
    split_ifs <;> first | (exfalso; omega) | simp | skip
  simp only [Matrix.mulVec, dotProduct, hT, Finset.sum_add_distrib]
  rw [CatalanCore.sum_ite_val_eq (j : ℕ) (fun i => Dfac K m S θ i * mu K m S θ i * g i)]
  have e2 : ∑ i : Fin (K - 1), (if (j : ℕ) = i + 1 then
        -(Dfac K m S θ i * sigma K m S θ i) * g i else 0) =
      if h : 0 < (j : ℕ) then
        -(Dfac K m S θ (((j : ℕ) - 1 : ℕ)) * sigma K m S θ (((j : ℕ) - 1 : ℕ)))
          * g ⟨(j : ℕ) - 1, by have := j.2; omega⟩ else 0 := by
    rcases Nat.eq_zero_or_pos (j : ℕ) with h | h
    · rw [dif_neg (by omega)]
      exact Finset.sum_eq_zero fun i _ => if_neg (by omega)
    · rw [dif_pos h]
      have : ∑ i : Fin (K - 1), (if (j : ℕ) = i + 1 then
          -(Dfac K m S θ i * sigma K m S θ i) * g i else 0) =
          ∑ i : Fin (K - 1), (if (i : ℕ) = (j : ℕ) - 1 then
          -(Dfac K m S θ i * sigma K m S θ i) * g i else 0) :=
        Finset.sum_congr rfl fun i _ => by
          congr 1; exact propext ⟨fun h2 => by omega, fun h2 => by omega⟩
      rw [this, CatalanCore.sum_ite_val_eq ((j : ℕ) - 1)
        (fun i => -(Dfac K m S θ i * sigma K m S θ i) * g i), dif_pos (by have := j.2; omega)]
  rw [e2]

lemma mu_top (K m S : ℕ) (θ : F) (hK : 1 ≤ K) : mu K m S θ ((K - 1 : ℕ) : F) = 0 := by
  have : ((K - 1 : ℕ) : F) = (K : F) - 1 := by rw [Nat.cast_sub hK]; simp
  simp [mu, this]

lemma XmatT_row (K m S : ℕ) (θ : F) (y : F) (j : Fin K) :
    ((Xmat K m S θ)ᵀ *ᵥ (fun b : Fin (K - 1) => 1 / (θ + ((b : ℕ) : F) + y))) j =
      Dfac K m S θ j * mu K m S θ j * (1 / (θ + j + y))
        + -(Dfac K m S θ ((j : F) - 1) * sigma K m S θ ((j : F) - 1)) *
            (1 / (θ + ((j : F) - 1) + y)) := by
  rw [XmatT_mulVec]
  have h1 : (if h : (j : ℕ) < K - 1 then Dfac K m S θ j * mu K m S θ j *
      (1 / (θ + (((⟨j, h⟩ : Fin (K - 1)) : ℕ) : F) + y)) else 0) =
      Dfac K m S θ j * mu K m S θ j * (1 / (θ + j + y)) := by
    split_ifs with h
    · rfl
    · have : ((j : ℕ) : F) = ((K - 1 : ℕ) : F) := by congr 1; have := j.2; omega
      rw [this, mu_top K m S θ (by have := j.2; omega)]; simp
  have h2 : (if h : 0 < (j : ℕ) then
      -(Dfac K m S θ (((j : ℕ) - 1 : ℕ)) * sigma K m S θ (((j : ℕ) - 1 : ℕ))) *
        (1 / (θ + (((⟨(j : ℕ) - 1, by have := j.2; omega⟩ : Fin (K - 1)) : ℕ) : F) + y)) else 0) =
      -(Dfac K m S θ ((j : F) - 1) * sigma K m S θ ((j : F) - 1)) *
        (1 / (θ + ((j : F) - 1) + y)) := by
    split_ifs with h
    · have : ((((j : ℕ) - 1 : ℕ)) : F) = (j : F) - 1 := by rw [Nat.cast_sub (by omega)]; simp
      simp only [this]
    · have h0 : (j : ℕ) = 0 := by omega
      have : ((j : ℕ) : F) = 0 := by rw [h0]; simp
      rw [this, sigma_bot]; simp
  rw [h1, h2]

lemma Xmat_row (K m S : ℕ) (θ : F) (y : F) (i : Fin (K - 1)) :
    (Xmat K m S θ *ᵥ (fun b : Fin K => 1 / (θ + ((b : ℕ) : F) + y))) i =
      Dfac K m S θ i * mu K m S θ i * (1 / (θ + i + y))
        + -(Dfac K m S θ i * sigma K m S θ i) * (1 / (θ + ((i : F) + 1) + y)) := by
  rw [Xmat_mulVec]; push_cast; rfl

/-- **(K4a) as a vector identity.** -/
theorem K4a_col [CharZero F] (K m S : ℕ) (hm : 1 ≤ m) (θ : F) (hθ : Gen θ) (hKS : K = S + m + 1)
    (n : ℤ) (hn : n ≤ (S : ℤ)) :
    ∃ ℰ : ℕ → F, Xmat K m S θ *ᵥ wcol K θ n =
      (Dfac K m S θ (-θ - n) * mu K m S θ (-θ - n)) • wcol (K - 1) θ n
        + (-(Dfac K m S θ (-θ - n - 1) * sigma K m S θ (-θ - n - 1))) • wcol (K - 1) θ (n + 1)
        + ∑ j ∈ Finset.range m, ℰ j • wcol (K - 1) θ ((S + 2 * j + 2 : ℕ) : ℤ) := by
  obtain ⟨ℰ, hℰ⟩ := K4a_field K m S hm θ hθ hKS n hn
  refine ⟨ℰ, ?_⟩
  funext i
  have h := hℰ i (by have := i.2; omega)
  have hrow := Xmat_row K m S θ (n : F) i
  have hw : wcol K θ n = fun b : Fin K => 1 / (θ + ((b : ℕ) : F) + (n : F)) := rfl
  rw [hw, hrow]
  simp only [wcol, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
  push_cast
  have hs : ∑ x ∈ Finset.range m, ℰ x / (θ + ((i : ℕ) : F) + ((S : F) + 2 * (x : F) + 2)) =
      ∑ x ∈ Finset.range m, ℰ x * (1 / (θ + ((i : ℕ) : F) + ((S : F) + 2 * (x : F) + 2))) := by
    exact Finset.sum_congr rfl fun x _ => div_eq_mul_one_div _ _
  linear_combination h + hs

/-- **(K4b) as a vector identity.** -/
theorem K4b_col [CharZero F] (K m S : ℕ) (hm : 1 ≤ m) (θ : F) (hθ : Gen θ) (hKS : K = S + m + 1)
    (n : ℤ) (hn : n ≤ (S : ℤ) + 1) :
    ∃ ℱ : ℕ → F, (Xmat K m S θ)ᵀ *ᵥ wcol (K - 1) θ n =
      (Dfac K m S θ (-θ - n) * mu K m S θ (-θ - n)) • wcol K θ n
        + (-(Dfac K m S θ (-θ - n) * sigma K m S θ (-θ - n))) • wcol K θ (n - 1)
        + ∑ j ∈ Finset.range m, ℱ j • wcol K θ ((S + 2 * j + 2 : ℕ) : ℤ) := by
  obtain ⟨ℱ, hℱ⟩ := K4b_field K m S hm θ hθ hKS n hn
  refine ⟨ℱ, ?_⟩
  funext j
  have h := hℱ j j.2
  have hrow := XmatT_row K m S θ (n : F) j
  have hw : wcol (K - 1) θ n = fun b : Fin (K - 1) => 1 / (θ + ((b : ℕ) : F) + (n : F)) := rfl
  rw [hw, hrow]
  simp only [wcol, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
  push_cast
  have hs : ∑ x ∈ Finset.range m, ℱ x / (θ + ((j : ℕ) : F) + ((S : F) + 2 * (x : F) + 2)) =
      ∑ x ∈ Finset.range m, ℱ x * (1 / (θ + ((j : ℕ) : F) + ((S : F) + 2 * (x : F) + 2))) := by
    exact Finset.sum_congr rfl fun x _ => div_eq_mul_one_div _ _
  linear_combination h + hs

/-- **(K4a) as a vector identity, general `y` (polynomial coefficients).** -/
theorem K4a_col_gen [CharZero F] (K m S : ℕ) (hm : 1 ≤ m) (θ : F) (hθ : Gen θ) (hKS : K = S + m + 1)
    (n : ℤ) (hn : ∀ j : ℕ, j < m → (S : ℤ) + 2 * j + 2 ≠ n) :
    ∃ ℰ : ℕ → F, Xmat K m S θ *ᵥ wcol K θ n =
      coefA K m (S : F) θ (n : F) (cK K m S θ) • wcol (K - 1) θ n
        + coefB θ (n : F) (cK K m S θ) • wcol (K - 1) θ (n + 1)
        + ∑ j ∈ Finset.range m, ℰ j • wcol (K - 1) θ ((S + 2 * j + 2 : ℕ) : ℤ) := by
  obtain ⟨ℰ, hℰ⟩ := K4a_gen K m S hm θ hθ hKS n hn
  refine ⟨ℰ, ?_⟩
  funext i
  have h := hℰ i (by have := i.2; omega)
  have hrow := Xmat_row K m S θ (n : F) i
  have hw : wcol K θ n = fun b : Fin K => 1 / (θ + ((b : ℕ) : F) + (n : F)) := rfl
  rw [hw, hrow]
  simp only [wcol, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
  push_cast
  have hs : ∑ x ∈ Finset.range m, ℰ x / (θ + ((i : ℕ) : F) + ((S : F) + 2 * (x : F) + 2)) =
      ∑ x ∈ Finset.range m, ℰ x * (1 / (θ + ((i : ℕ) : F) + ((S : F) + 2 * (x : F) + 2))) := by
    exact Finset.sum_congr rfl fun x _ => div_eq_mul_one_div _ _
  linear_combination h + hs

/-- **(K4b) as a vector identity, general `y` (polynomial coefficients).** -/
theorem K4b_col_gen [CharZero F] (K m S : ℕ) (hm : 1 ≤ m) (θ : F) (hθ : Gen θ) (hKS : K = S + m + 1)
    (n : ℤ) (hn : ∀ j : ℕ, j < m → (S : ℤ) + 2 * j + 2 ≠ n) :
    ∃ ℱ : ℕ → F, (Xmat K m S θ)ᵀ *ᵥ wcol (K - 1) θ n =
      coefA K m (S : F) θ (n : F) (cK K m S θ) • wcol K θ n
        + coefB' θ (n : F) (cK K m S θ) • wcol K θ (n - 1)
        + ∑ j ∈ Finset.range m, ℱ j • wcol K θ ((S + 2 * j + 2 : ℕ) : ℤ) := by
  obtain ⟨ℱ, hℱ⟩ := K4b_gen K m S hm θ hθ hKS n hn
  refine ⟨ℱ, ?_⟩
  funext j
  have h := hℱ j j.2
  have hrow := XmatT_row K m S θ (n : F) j
  have hw : wcol (K - 1) θ n = fun b : Fin (K - 1) => 1 / (θ + ((b : ℕ) : F) + (n : F)) := rfl
  rw [hw, hrow]
  simp only [wcol, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
  push_cast
  have hs : ∑ x ∈ Finset.range m, ℱ x / (θ + ((j : ℕ) : F) + ((S : F) + 2 * (x : F) + 2)) =
      ∑ x ∈ Finset.range m, ℱ x * (1 / (θ + ((j : ℕ) : F) + ((S : F) + 2 * (x : F) + 2))) := by
    exact Finset.sum_congr rfl fun x _ => div_eq_mul_one_div _ _
  linear_combination h + hs

end CatalanCore.Star.Leonard
