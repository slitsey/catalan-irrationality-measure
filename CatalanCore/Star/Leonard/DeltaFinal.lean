module

public import CatalanCore.Star.Leonard.DeltaHunif
public import CatalanCore.Star.Leonard.DeltaWb

/-!
# Prop hDelta: the closed form

`det(W_Xᵀ W_Y) = V(X) V(Y) · Hunif(K,m) / ∏_{i=1}^m (θ+S+i)_m (θ+S+K+i)_m`
with `Hunif(K,m) = det[∑_{a<K} a^{p+q}]` the Hankel determinant of the uniform weight on `{0..K-1}`.
-/

@[expose] public section

open Finset Matrix

namespace CatalanCore.Star.Leonard

variable {F : Type*} [Field F] [DecidableEq F] [CharZero F]

/-- the Pochhammer product `∏_{i=1}^m (θ+i)_m (θ+K+i)_m` -/
noncomputable def Dpair (θ : F) (K m : ℕ) : F :=
  ∏ i ∈ range m, (pochr (θ + 1 + (i : F)) m * pochr (θ + (K : F) + 1 + (i : F)) m)

/-- the uniform-weight moment Hankel determinant -/
noncomputable def Hunif (F : Type*) [Field F] (K m : ℕ) : F :=
  (Matrix.of fun (p q : Fin m) => ∑ a : Fin K, ((a : ℕ) : F) ^ ((p : ℕ) + (q : ℕ))).det

theorem det_E_Hunif (θ : F) (hθ : Gen θ) (K m : ℕ) :
    (Emat θ K m).det = Hunif F K m *
      ((∏ p : Fin m, pochr (θ + 1) (m - 1 - (p : ℕ))) *
        (∏ q : Fin m, (pochr (θ + 1) (m + (q : ℕ) + K))⁻¹) *
        ((∏ i : Fin m, pochr (θ + (m : F) + 1) (K - 1 - (i : ℕ))) *
          (∏ j : Fin m, (pochr (θ + (m : F) + 1) (j : ℕ))⁻¹))) := by
  rw [det_E_HB θ hθ K m, Hunif, Hunif_eq]
  ring

theorem Rpoch_eq (θ : F) (hθ : Gen θ) (K m : ℕ) (hmK : m ≤ K) :
    (∏ p : Fin m, pochr (θ + 1) (m - 1 - (p : ℕ))) *
        (∏ q : Fin m, (pochr (θ + 1) (m + (q : ℕ) + K))⁻¹) *
        ((∏ i : Fin m, pochr (θ + (m : F) + 1) (K - 1 - (i : ℕ))) *
          (∏ j : Fin m, (pochr (θ + (m : F) + 1) (j : ℕ))⁻¹)) = (Dpair θ K m)⁻¹ := by
  set g : ℕ → F := fun n => pochr (θ + 1) n with hg
  have hg0 : ∀ n, g n ≠ 0 := fun n => pochr_one_ne θ hθ n
  have hadd : ∀ a b : ℕ, pochr (θ + 1 + (a : F)) b = g (a + b) / g a := by
    intro a b
    have := pochr_add (θ + 1) a b
    simp only [hg]
    rw [this, mul_div_cancel_left₀ _ (hg0 a)]
  have gm : g m ^ m ≠ 0 := pow_ne_zero _ (hg0 m)
  have A : ∏ p : Fin m, pochr (θ + 1) (m - 1 - (p : ℕ)) = ∏ i ∈ range m, g i := by
    rw [Fin.prod_univ_eq_prod_range (fun p => g (m - 1 - p)) m]
    exact Finset.prod_range_reflect g m
  have B : ∏ q : Fin m, (pochr (θ + 1) (m + (q : ℕ) + K))⁻¹ = (∏ i ∈ range m, g (K + m + i))⁻¹ := by
    rw [Fin.prod_univ_eq_prod_range (fun q => (g (m + q + K))⁻¹) m, Finset.prod_inv_distrib]
    congr 1
    exact Finset.prod_congr rfl fun i _ => by rw [show m + i + K = K + m + i by omega]
  have C : ∏ i : Fin m, pochr (θ + (m : F) + 1) (K - 1 - (i : ℕ)) =
      (∏ i ∈ range m, g (K + i)) / g m ^ m := by
    rw [Fin.prod_univ_eq_prod_range (fun i => pochr (θ + (m : F) + 1) (K - 1 - i)) m]
    have : ∀ i ∈ range m, pochr (θ + (m : F) + 1) (K - 1 - i) = g (K + (m - 1 - i)) / g m := by
      intro i hi
      have hi' := Finset.mem_range.1 hi
      rw [show θ + (m : F) + 1 = θ + 1 + (m : F) by ring, hadd, show m + (K - 1 - i) = K + (m - 1 - i) by omega]
    rw [Finset.prod_congr rfl this, Finset.prod_div_distrib, Finset.prod_const, Finset.card_range]
    congr 1
    exact Finset.prod_range_reflect (fun i => g (K + i)) m
  have D : ∏ j : Fin m, (pochr (θ + (m : F) + 1) (j : ℕ))⁻¹ = g m ^ m / ∏ j ∈ range m, g (m + j) := by
    rw [Fin.prod_univ_eq_prod_range (fun j => (pochr (θ + (m : F) + 1) j)⁻¹) m]
    have : ∀ j ∈ range m, (pochr (θ + (m : F) + 1) j)⁻¹ = g m / g (m + j) := by
      intro j _
      rw [show θ + (m : F) + 1 = θ + 1 + (m : F) by ring, hadd, inv_div]
    rw [Finset.prod_congr rfl this, Finset.prod_div_distrib, Finset.prod_const, Finset.card_range]
  have E : Dpair θ K m = ((∏ i ∈ range m, g (m + i)) / ∏ i ∈ range m, g i) *
      ((∏ i ∈ range m, g (K + m + i)) / ∏ i ∈ range m, g (K + i)) := by
    unfold Dpair
    rw [Finset.prod_mul_distrib]
    have e1 : ∀ i ∈ range m, pochr (θ + 1 + (i : F)) m = g (m + i) / g i := by
      intro i _; rw [hadd, add_comm]
    have e2 : ∀ i ∈ range m, pochr (θ + (K : F) + 1 + (i : F)) m = g (K + m + i) / g (K + i) := by
      intro i _
      rw [show θ + (K : F) + 1 + (i : F) = θ + 1 + ((K + i : ℕ) : F) by push_cast; ring, hadd,
        show K + i + m = K + m + i by omega]
    rw [Finset.prod_congr rfl e1, Finset.prod_congr rfl e2, Finset.prod_div_distrib,
      Finset.prod_div_distrib]
  rw [A, B, C, D, E]
  have h1 : ∏ i ∈ range m, g i ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => hg0 i
  have h2 : ∏ i ∈ range m, g (m + i) ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => hg0 _
  have h3 : ∏ i ∈ range m, g (K + i) ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => hg0 _
  have h4 : ∏ i ∈ range m, g (K + m + i) ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => hg0 _
  field_simp

/-- **Prop hDelta (closed form).** -/
theorem Delta_closed (K m S : ℕ) (θ : F) (hθ : Gen θ) (hmK : m ≤ K) :
    ((Wb K θ (bX m (S : ℤ)))ᵀ * Wb K θ (bY m (S : ℤ))).det =
      Vprod (xsθ (θ + (S : F)) m) * Vprod (ysθ (θ + (S : F)) m) *
        (Hunif F K m / Dpair (θ + (S : F)) K m) := by
  rw [Delta_eq_E K m S θ hθ]
  have h := det_E_Hunif (θ + (S : F)) (Gen_add_nat hθ S) K m
  rw [Rpoch_eq (θ + (S : F)) (Gen_add_nat hθ S) K m hmK] at h
  have : (Matrix.of fun (p q : Fin m) => ∑ a : Fin K,
          (pochr (((a : ℕ) : F) + (θ + (S : F)) + ((p : ℕ) : F) + 1)
            (2 * m - (p : ℕ) - (q : ℕ)))⁻¹).det = (Emat (θ + (S : F)) K m).det := rfl
  rw [this, h]
  ring

end CatalanCore.Star.Leonard
