module

public import CatalanCore.Star.Leonard.KStepField
public import CatalanCore.Star.Defs
public import CatalanCore.Linalg.Tridiag

/-!
# The tridiagonal `T~` and its chains on Cauchy columns (package H1/H2 glue)

`Ttil K m S θ` is the `K × K` node tridiagonal with diagonal `D(a)`, superdiagonal `-σ(a)`,
subdiagonal `-τ(a)`.  `Ttil_col` / `Ttil_row` restate (CC) / (RC) as vector identities on
`wcol K θ y` (column `1/(θ + a + y)`), with the border corrections in `span{wcol K θ t}`.
-/

@[expose] public section

open Finset Matrix

namespace CatalanCore.Star.Leonard

variable {F : Type*} [Field F]

/-- Non-symmetric tridiagonal matrix: diagonal `d i`, `T i (i+1) = up i`, `T (j+1) j = lo j`. -/
def trid (n : ℕ) (up lo d : ℕ → F) : Matrix (Fin n) (Fin n) F :=
  Matrix.of fun i j =>
    if (j : ℕ) = i then d i else if (j : ℕ) = i + 1 then up i else if (i : ℕ) = j + 1 then lo j
    else 0

lemma trid_mulVec (n : ℕ) (up lo d : ℕ → F) (g : Fin n → F) (a : Fin n) :
    (trid n up lo d *ᵥ g) a =
      d a * g a + (if h : (a : ℕ) + 1 < n then up a * g ⟨a + 1, h⟩ else 0)
        + (if h : 0 < (a : ℕ) then lo ((a : ℕ) - 1) * g ⟨(a : ℕ) - 1, by omega⟩ else 0) := by
  have hT : ∀ j : Fin n, trid n up lo d a j * g j =
      (if (j : ℕ) = a then d a * g j else 0) + (if (j : ℕ) = a + 1 then up a * g j else 0)
        + (if (a : ℕ) = j + 1 then lo j * g j else 0) := by
    intro j
    simp only [trid, Matrix.of_apply]
    split_ifs <;> first | (exfalso; omega) | simp
  simp only [Matrix.mulVec, dotProduct, hT, Finset.sum_add_distrib]
  rw [CatalanCore.sum_ite_val_eq (a : ℕ) (fun j => d a * g j),
    CatalanCore.sum_ite_val_eq ((a : ℕ) + 1) (fun j => up a * g j)]
  have e3 : ∑ j : Fin n, (if (a : ℕ) = j + 1 then lo j * g j else 0) =
      if h : 0 < (a : ℕ) then lo ((a : ℕ) - 1) * g ⟨(a : ℕ) - 1, by omega⟩ else 0 := by
    rcases Nat.eq_zero_or_pos (a : ℕ) with h | h
    · rw [dif_neg (by omega)]
      exact Finset.sum_eq_zero fun j _ => if_neg (by omega)
    · rw [dif_pos h]
      have : ∑ j : Fin n, (if (a : ℕ) = j + 1 then lo j * g j else 0) =
          ∑ j : Fin n, (if (j : ℕ) = (a : ℕ) - 1 then lo j * g j else 0) :=
        Finset.sum_congr rfl fun j _ => by
          congr 1; exact propext ⟨fun h2 => by omega, fun h2 => by omega⟩
      rw [this, CatalanCore.sum_ite_val_eq ((a : ℕ) - 1) (fun j => lo j * g j), dif_pos (by omega)]
  rw [e3, dif_pos a.2]


/-- The node tridiagonal `T~`. -/
noncomputable def Ttil (K m S : ℕ) (θ : F) : Matrix (Fin K) (Fin K) F :=
  trid K (fun i => -sigma K m S θ i) (fun j => -tau K m S θ j) (fun i => Dd K m S θ i)

lemma tau_bot (K m S : ℕ) (θ : F) : tau K m S θ ((0 : F) - 1) = 0 := by
  simp [tau, pp]

lemma sigma_top (K m S : ℕ) (θ : F) (hK : 1 ≤ K) : sigma K m S θ ((K - 1 : ℕ) : F) = 0 := by
  have : ((K - 1 : ℕ) : F) = (K : F) - 1 := by rw [Nat.cast_sub hK]; simp
  simp [sigma, pp, this]

lemma Ttil_apply (K m S : ℕ) (θ : F) (g : Fin K → F) (a : Fin K) :
    (Ttil K m S θ *ᵥ g) a =
      Dd K m S θ a * g a + (if h : (a : ℕ) + 1 < K then -sigma K m S θ a * g ⟨a + 1, h⟩ else 0)
        + (if h : 0 < (a : ℕ) then -tau K m S θ ((a : ℕ) - 1 : ℕ) * g ⟨(a : ℕ) - 1, by omega⟩
            else 0) := by
  unfold Ttil; rw [trid_mulVec]

/-- Boundary conventions for the chains: the sub/superdiagonal terms exist exactly where they are
nonzero. -/
lemma Ttil_row (K m S : ℕ) (θ : F) (y : F) (a : Fin K) :
    (Ttil K m S θ *ᵥ (fun b : Fin K => 1 / (θ + ((b : ℕ) : F) + y))) a =
      Dd K m S θ a * (1 / (θ + a + y))
        + -sigma K m S θ a * (1 / (θ + ((a : F) + 1) + y))
        + -tau K m S θ ((a : F) - 1) * (1 / (θ + ((a : F) - 1) + y)) := by
  rw [Ttil_apply]
  have hσ : (if h : (a : ℕ) + 1 < K then -sigma K m S θ a * (1 / (θ + (((⟨a + 1, h⟩ : Fin K)
      : ℕ) : F) + y)) else 0) = -sigma K m S θ a * (1 / (θ + ((a : F) + 1) + y)) := by
    split_ifs with h
    · push_cast; rfl
    · have : ((a : ℕ) : F) = ((K - 1 : ℕ) : F) := by congr 1; have := a.2; omega
      rw [this, sigma_top K m S θ (by have := a.2; omega)]; simp
  have hτ : (if h : 0 < (a : ℕ) then -tau K m S θ (((a : ℕ) - 1 : ℕ) : F) *
      (1 / (θ + (((⟨(a : ℕ) - 1, by omega⟩ : Fin K) : ℕ) : F) + y)) else 0) =
      -tau K m S θ ((a : F) - 1) * (1 / (θ + ((a : F) - 1) + y)) := by
    split_ifs with h
    · have : ((((a : ℕ) - 1 : ℕ)) : F) = (a : F) - 1 := by rw [Nat.cast_sub (by omega)]; simp
      simp only [this]
    · have h0 : (a : ℕ) = 0 := by omega
      have : ((a : ℕ) : F) = 0 := by rw [h0]; simp
      rw [this, tau_bot]; simp
  rw [hσ, hτ]


/-- **(CC) as a vector identity** on Cauchy columns, symbolic `m`: `T~ c_n = l(n) c_{n-1} +
d(n) c_n + r(n) c_{n+1} + Σ_{t∈Y} κ_t c_t` (`n ≤ S - 1`). -/
theorem Ttil_col [CharZero F] (K m S : ℕ) (hm : 1 ≤ m) (θ : F) (hθ : Gen θ) (n : ℤ)
    (hn : n + 1 ≤ (S : ℤ)) :
    ∃ κ : ℕ → F, Ttil K m S θ *ᵥ wcol K θ n =
      (-tau K m S θ (-θ - n)) • wcol K θ (n - 1) + Dd K m S θ (-θ - n) • wcol K θ n
        + (-sigma K m S θ (-θ - n - 1)) • wcol K θ (n + 1)
        + ∑ j ∈ Finset.range m, κ j • wcol K θ ((S + 2 * j + 1 : ℕ) : ℤ) := by
  obtain ⟨κ, hκ⟩ := CC_field K m S hm θ hθ n hn
  refine ⟨κ, ?_⟩
  funext a
  have h := hκ a a.2
  have hrow := Ttil_row K m S θ (n : F) a
  have hw : wcol K θ n = fun b : Fin K => 1 / (θ + ((b : ℕ) : F) + (n : F)) := rfl
  rw [hw, hrow]
  simp only [wcol, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
  push_cast
  have hs : ∑ x ∈ Finset.range m, κ x / (θ + ((a : ℕ) : F) + ((S : F) + 2 * (x : F) + 1)) =
      ∑ x ∈ Finset.range m, κ x * (1 / (θ + ((a : ℕ) : F) + ((S : F) + 2 * (x : F) + 1))) := by
    exact Finset.sum_congr rfl fun x _ => div_eq_mul_one_div _ _
  linear_combination h + hs

lemma trid_transpose (n : ℕ) (up lo d : ℕ → F) : (trid n up lo d)ᵀ = trid n lo up d := by
  ext i j
  simp only [Matrix.transpose_apply, trid, Matrix.of_apply]
  split_ifs <;> (try (exfalso; omega)) <;> (try rfl) <;> (congr 1 <;> omega)

lemma sigma_bot (K m S : ℕ) (θ : F) : sigma K m S θ ((0 : F) - 1) = 0 := by
  simp [sigma, pp]

lemma tau_top (K m S : ℕ) (θ : F) (hK : 1 ≤ K) : tau K m S θ ((K - 1 : ℕ) : F) = 0 := by
  have : ((K - 1 : ℕ) : F) = (K : F) - 1 := by rw [Nat.cast_sub hK]; simp
  simp [tau, pp, this]

lemma TtilT_row (K m S : ℕ) (θ : F) (y : F) (a : Fin K) :
    ((Ttil K m S θ)ᵀ *ᵥ (fun b : Fin K => 1 / (θ + ((b : ℕ) : F) + y))) a =
      Dd K m S θ a * (1 / (θ + a + y))
        + -tau K m S θ a * (1 / (θ + ((a : F) + 1) + y))
        + -sigma K m S θ ((a : F) - 1) * (1 / (θ + ((a : F) - 1) + y)) := by
  have hT : (Ttil K m S θ)ᵀ =
      trid K (fun i => -tau K m S θ i) (fun j => -sigma K m S θ j) (fun i => Dd K m S θ i) := by
    unfold Ttil; rw [trid_transpose]
  rw [hT, trid_mulVec]
  have hσ : (if h : (a : ℕ) + 1 < K then -tau K m S θ a * (1 / (θ + (((⟨a + 1, h⟩ : Fin K)
      : ℕ) : F) + y)) else 0) = -tau K m S θ a * (1 / (θ + ((a : F) + 1) + y)) := by
    split_ifs with h
    · push_cast; rfl
    · have : ((a : ℕ) : F) = ((K - 1 : ℕ) : F) := by congr 1; have := a.2; omega
      rw [this, tau_top K m S θ (by have := a.2; omega)]; simp
  have hτ : (if h : 0 < (a : ℕ) then -sigma K m S θ (((a : ℕ) - 1 : ℕ) : F) *
      (1 / (θ + (((⟨(a : ℕ) - 1, by omega⟩ : Fin K) : ℕ) : F) + y)) else 0) =
      -sigma K m S θ ((a : F) - 1) * (1 / (θ + ((a : F) - 1) + y)) := by
    split_ifs with h
    · have : ((((a : ℕ) - 1 : ℕ)) : F) = (a : F) - 1 := by rw [Nat.cast_sub (by omega)]; simp
      simp only [this]
    · have h0 : (a : ℕ) = 0 := by omega
      have : ((a : ℕ) : F) = 0 := by rw [h0]; simp
      rw [this, sigma_bot]; simp
  rw [hσ, hτ]

/-- **(RC) as a vector identity**: `T~ᵀ c_n = r(n-1) c_{n-1} + d(n) c_n + l(n+1) c_{n+1} +
Σ_{x∈X} κ_x c_x`. -/
theorem TtilT_col [CharZero F] (K m S : ℕ) (hm : 1 ≤ m) (θ : F) (hθ : Gen θ) (n : ℤ)
    (hn : n + 1 ≤ (S : ℤ)) :
    ∃ κ : ℕ → F, (Ttil K m S θ)ᵀ *ᵥ wcol K θ n =
      (-sigma K m S θ (-θ - n)) • wcol K θ (n - 1) + Dd K m S θ (-θ - n) • wcol K θ n
        + (-tau K m S θ (-θ - n - 1)) • wcol K θ (n + 1)
        + ∑ j ∈ Finset.range m, κ j • wcol K θ ((S + 2 * j + 2 : ℕ) : ℤ) := by
  obtain ⟨κ, hκ⟩ := RC_field K m S hm θ hθ n hn
  refine ⟨κ, ?_⟩
  funext a
  have h := hκ a a.2
  have hrow := TtilT_row K m S θ (n : F) a
  have hw : wcol K θ n = fun b : Fin K => 1 / (θ + ((b : ℕ) : F) + (n : F)) := rfl
  rw [hw, hrow]
  simp only [wcol, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
  push_cast
  have hs : ∑ x ∈ Finset.range m, κ x / (θ + ((a : ℕ) : F) + ((S : F) + 2 * (x : F) + 2)) =
      ∑ x ∈ Finset.range m, κ x * (1 / (θ + ((a : ℕ) : F) + ((S : F) + 2 * (x : F) + 2))) := by
    exact Finset.sum_congr rfl fun x _ => div_eq_mul_one_div _ _
  linear_combination h + hs

end CatalanCore.Star.Leonard
