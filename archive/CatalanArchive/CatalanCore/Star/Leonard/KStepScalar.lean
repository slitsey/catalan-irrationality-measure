module

public import CatalanCore.Star.Leonard.Darboux
public import CatalanCore.Star.Leonard.LU

/-!
# Scalar core of the Darboux intertwining `X T~ = (T~' + β) X` (package H5)

At `g = 0` (`S + m = K'`, instance `(K'+1, m, S)` and its Christoffel transform `(K', m, S+1)`):
* `Dfac_ne_zero`;
* `E4`: `D_i σ_i = σ'_i D_{i+1}` (K2a);
* `E1`: `D_{i+1} μ_{i+1} τ_i = τ'_i D_i μ_i` (K2a + K2b).
These, with `Dd_i = μ_i + σ_{i-1}τ_{i-1}/μ_{i-1}` and `Dd'_i + β = μ_i + σ_iτ_i/μ_i`, give the four
coefficient identities of `X T~ = (T~' + β) X`.
-/

@[expose] public section

open Finset Matrix

namespace CatalanCore.Star.Leonard

variable {F : Type*} [Field F]

lemma Dfac_ne_zero [CharZero F] (K' m S : ℕ) (θ : F) (hθ : Gen θ) (i : ℕ) (hi : i < K') :
    Dfac (K' + 1) m S θ i ≠ 0 := by
  have hK0 : (K' : F) ≠ 0 := by
    have := natsub_ne (F := F) (a := K') (b := 0) (by omega); simpa using this
  have hKi : (K' : F) - i ≠ 0 := natsub_ne (by omega)
  have hP0 : Pe m S θ 0 ≠ 0 := by simpa using Pe_ne_zero m S (genAt_nat hθ 0)
  have hQ0 : Qo m S θ 0 ≠ 0 := by simpa using Qo_ne_zero m S (genAt_nat hθ 0)
  have hPi := Pe_ne_zero m S (genAt_nat hθ i)
  have hQi := Qo_ne_zero m S (genAt_nat hθ i)
  unfold Dfac
  push_cast
  have hKi' : (K' : F) + 1 - 1 - i ≠ 0 := by intro h0; apply hKi; linear_combination h0
  have hK0' : (K' : F) + 1 - 1 ≠ 0 := by intro h0; apply hK0; linear_combination h0
  exact mul_ne_zero (mul_ne_zero (div_ne_zero hK0' hKi') (div_ne_zero hP0 hPi))
    (div_ne_zero hQi hQ0)

/-- **E4.** `D_i σ_i = σ'_i D_{i+1}`. -/
lemma Dfac_sigma_shift [CharZero F] (K' m S : ℕ) (θ : F) (hθ : Gen θ) (i : ℕ) (hi : i + 2 ≤ K') :
    Dfac (K' + 1) m S θ i * sigma (K' + 1) m S θ i =
      sigma K' m (S + 1) θ i * Dfac (K' + 1) m S θ ((i : F) + 1) := by
  have h := sigma_darboux K' m S θ hθ i hi
  have hD := Dfac_ne_zero K' m S θ hθ i (by omega)
  rw [← h]
  field_simp


lemma sigma_ne_zero [CharZero F] (K m S : ℕ) (θ : F) (hθ : Gen θ) (i : ℕ) (hi : i + 1 < K) :
    sigma K m S θ i ≠ 0 := by
  have hK : (K : F) - 1 - i ≠ 0 := by
    have := natsub_ne (F := F) (a := K - 1) (b := i) (by omega)
    rw [Nat.cast_sub (by omega)] at this
    push_cast at this; exact this
  have h1 : (i : F) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero i
  have h2 : (i : F) + 1 + θ ≠ 0 := by
    have := hθ ((i : ℤ) + 1); push_cast at this
    intro h0; apply this; linear_combination h0
  have hP := Pe_ne_zero m S (genAt_nat hθ i)
  have hQ := Qo_ne_zero m S (genAt_nat hθ i)
  unfold sigma pp
  exact div_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero h1 h2) hK) hP) hQ

/-- **E1.** `D_{i+1} μ_{i+1} τ_i = τ'_i D_i μ_i`. -/
lemma Dfac_mu_tau_shift [CharZero F] (K' m S : ℕ) (hm : 1 ≤ m) (θ : F) (hθ : Gen θ) (i : ℕ)
    (hi : i + 2 ≤ K') :
    Dfac (K' + 1) m S θ ((i : F) + 1) * mu (K' + 1) m S θ ((i : F) + 1) * tau (K' + 1) m S θ i =
      tau K' m (S + 1) θ i * Dfac (K' + 1) m S θ i * mu (K' + 1) m S θ i := by
  have hE4 := Dfac_sigma_shift K' m S θ hθ i hi
  have hst := sigma_tau_darboux K' m S θ hθ hm i hi
  have hσ := sigma_ne_zero (K' + 1) m S θ hθ i (by omega)
  have hμ := mu_ne_zero (K' + 1) m S θ hθ i (by omega)
  have hD := Dfac_ne_zero K' m S θ hθ i (by omega)
  -- D_{i+1} · (σ' τ') = D_i σ_i τ'
  have h1 : Dfac (K' + 1) m S θ ((i : F) + 1) * (sigma K' m (S + 1) θ i * tau K' m (S + 1) θ i) =
      Dfac (K' + 1) m S θ i * sigma (K' + 1) m S θ i * tau K' m (S + 1) θ i := by
    rw [hE4]; ring
  rw [hst] at h1
  field_simp at h1
  linear_combination h1


/-- The shift `β` of the Christoffel transform (value of the constant of `darboux_diag_poly`). -/
noncomputable def betaD (K' m S : ℕ) (θ : F) : F :=
  (mu (K' + 1) m S θ 0 - ((0 + 1) * (0 + 1 + θ)) ^ 2) -
    (mu K' m (S + 1) θ 0 - (0 * (0 + θ)) ^ 2 + gg K' m (S + 1) * (gg K' m (S + 1) + 1) * 0 ^ 2
      + gg K' m (S + 1) * cc0 K' m θ (gg K' m (S + 1)) * 0)

/-- **E2/E3 core (K2c).**  `D'_i + β = μ_i + σ_i τ_i / μ_i` for `i < K'`. -/
lemma Dd_shift_beta [CharZero F] (K' m S : ℕ) (hm : 1 ≤ m) (θ : F) (hθ : Gen θ) (hS : S + m = K')
    (i : ℕ) (hi : i < K') :
    Dd K' m (S + 1) θ i + betaD K' m S θ =
      mu (K' + 1) m S θ i + sigma (K' + 1) m S θ i * tau (K' + 1) m S θ i / mu (K' + 1) m S θ i := by
  have hK : (K' : F) - i ≠ 0 := natsub_ne (by omega)
  have hK1 : ((K' + 1 : ℕ) : F) - 1 - i ≠ 0 := by
    push_cast; intro h0; apply hK; linear_combination h0
  rw [Dd_eq K' m (S + 1) θ i hm (genAt_nat_sub_one hθ i) hK,
    sigma_tau_div_mu (K' + 1) m S θ i hm (genAt_nat hθ i) hK1]
  have := darboux_diag_poly K' m S θ hS (i : F)
  unfold betaD
  linear_combination -this


section Coeffs

variable [CharZero F] (K' m S : ℕ) (hm : 1 ≤ m) (θ : F) (hθ : Gen θ) (hS : S + m = K')

/-- `Dd` at `g = 0`. -/
lemma Dd_g0 (a : F) (hS : S + m = K') :
    Dd (K' + 1) m S θ a = mu (K' + 1) m S θ a +
      sigma (K' + 1) m S θ (a - 1) * tau (K' + 1) m S θ (a - 1) / mu (K' + 1) m S θ (a - 1) := by
  have hg : gg (K' + 1) m S = (0 : F) := by
    unfold gg
    have : ((S + m : ℕ) : F) = K' := congrArg (Nat.cast : ℕ → F) hS
    push_cast at this ⊢; linear_combination this
  unfold Dd; rw [hg]; ring

include hm hθ in
/-- Coefficient of `v_{i-1}` (E1, `i ≥ 1`). -/
lemma coef_prev (n : ℕ) (h1 : 1 ≤ n) (hn : n < K') :
    Dfac (K' + 1) m S θ (n : F) * mu (K' + 1) m S θ (n : F) *
        tau (K' + 1) m S θ (((n - 1 : ℕ)) : F) =
      tau K' m (S + 1) θ (((n - 1 : ℕ)) : F) * Dfac (K' + 1) m S θ (((n - 1 : ℕ)) : F) *
        mu (K' + 1) m S θ (((n - 1 : ℕ)) : F) := by
  obtain ⟨i, rfl⟩ : ∃ i, n = i + 1 := ⟨n - 1, by omega⟩
  have := Dfac_mu_tau_shift K' m S hm θ hθ i (by omega)
  simpa using this

include hm hθ hS in
/-- Coefficient of `v_i` (E2). -/
lemma coef_diag (n : ℕ) (hn : n < K') :
    Dfac (K' + 1) m S θ (n : F) * mu (K' + 1) m S θ (n : F) * Dd (K' + 1) m S θ (n : F)
        + Dfac (K' + 1) m S θ (n : F) * sigma (K' + 1) m S θ (n : F) * tau (K' + 1) m S θ (n : F) =
      (Dd K' m (S + 1) θ (n : F) + betaD K' m S θ) * (Dfac (K' + 1) m S θ (n : F) *
        mu (K' + 1) m S θ (n : F))
        + (if 0 < n then tau K' m (S + 1) θ (((n - 1 : ℕ)) : F) *
            (Dfac (K' + 1) m S θ (((n - 1 : ℕ)) : F) * sigma (K' + 1) m S θ (((n - 1 : ℕ)) : F))
          else 0) := by
  rw [Dd_g0 K' m S θ (n : F) hS]
  have hb := Dd_shift_beta K' m S hm θ hθ hS n hn
  rw [hb]
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · subst h0
    simp only [Nat.cast_zero, zero_sub, lt_irrefl, if_false]
    have h1 : sigma (K' + 1) m S θ (-1) = 0 := by simp [sigma, pp]
    rw [h1]
    have hμ0 : mu (K' + 1) m S θ 0 ≠ 0 := by
      simpa using mu_ne_zero (K' + 1) m S θ hθ 0 (by omega)
    field_simp
    simp only [zero_mul, zero_div, add_zero]
    ring
  · rw [if_pos h0]
    obtain ⟨i, rfl⟩ : ∃ i, n = i + 1 := ⟨n - 1, by omega⟩
    have hE := coef_prev K' m S hm θ hθ (i + 1) (by omega) hn
    have hμ := mu_ne_zero (K' + 1) m S θ hθ i (by omega)
    have hμ1 := mu_ne_zero (K' + 1) m S θ hθ (i + 1) (by omega)
    push_cast at hμ1
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one] at hE ⊢
    have e : (i : F) + 1 - 1 = i := by ring
    rw [e]
    field_simp
    linear_combination (sigma (K' + 1) m S θ i) * hE

include hm hθ hS in
/-- Coefficient of `v_{i+1}` (E3). -/
lemma coef_next (n : ℕ) (hn : n < K') :
    Dfac (K' + 1) m S θ (n : F) * mu (K' + 1) m S θ (n : F) * sigma (K' + 1) m S θ (n : F)
        + Dfac (K' + 1) m S θ (n : F) * sigma (K' + 1) m S θ (n : F) *
          Dd (K' + 1) m S θ ((n : F) + 1) =
      (Dd K' m (S + 1) θ (n : F) + betaD K' m S θ) *
          (Dfac (K' + 1) m S θ (n : F) * sigma (K' + 1) m S θ (n : F))
        + (if n + 1 < K' then sigma K' m (S + 1) θ (n : F) *
            (Dfac (K' + 1) m S θ ((n : F) + 1) * mu (K' + 1) m S θ ((n : F) + 1)) else 0) := by
  have hμ := mu_ne_zero (K' + 1) m S θ hθ n (by omega)
  rw [Dd_g0 K' m S θ ((n : F) + 1) hS, Dd_shift_beta K' m S hm θ hθ hS n hn]
  have e : (n : F) + 1 - 1 = n := by ring
  rw [e]
  by_cases h : n + 1 < K'
  · rw [if_pos h]
    have hE4 := Dfac_sigma_shift K' m S θ hθ n (by omega)
    field_simp
    linear_combination (mu (K' + 1) m S θ ((n : F) + 1) * mu (K' + 1) m S θ n) * hE4
  · rw [if_neg h]
    have hK : n + 1 = K' := by omega
    have hz : mu (K' + 1) m S θ ((n : F) + 1) = 0 := by
      unfold mu
      have : ((n : F) + 1) = (K' : F) := by rw [← hK]; push_cast; ring
      rw [this]; push_cast; ring
    rw [hz]
    field_simp
    ring

include hm hθ in
/-- Coefficient of `v_{i+2}` (E4). -/
lemma coef_next2 (n : ℕ) (hn : n + 2 ≤ K') :
    Dfac (K' + 1) m S θ (n : F) * sigma (K' + 1) m S θ (n : F) *
        sigma (K' + 1) m S θ ((n : F) + 1) =
      sigma K' m (S + 1) θ (n : F) * Dfac (K' + 1) m S θ ((n : F) + 1) *
        sigma (K' + 1) m S θ ((n : F) + 1) := by
  rw [Dfac_sigma_shift K' m S θ hθ n hn]

end Coeffs

/-- `Xmat (K'+1)` with the row type `Fin K'` (avoids `K' + 1 - 1`). -/
noncomputable def Xm (K' m S : ℕ) (θ : F) : Matrix (Fin K') (Fin (K' + 1)) F :=
  Matrix.of fun i j =>
    if (j : ℕ) = i then Dfac (K' + 1) m S θ i * mu (K' + 1) m S θ i
    else if (j : ℕ) = i + 1 then -(Dfac (K' + 1) m S θ i * sigma (K' + 1) m S θ i) else 0

lemma Xm_mulVec (K' m S : ℕ) (θ : F) (g : Fin (K' + 1) → F) (i : Fin K') :
    (Xm K' m S θ *ᵥ g) i =
      Dfac (K' + 1) m S θ i * mu (K' + 1) m S θ i * g ⟨i, by omega⟩
        + -(Dfac (K' + 1) m S θ i * sigma (K' + 1) m S θ i) * g ⟨i + 1, by omega⟩ := by
  have hi := i.2
  have hT : ∀ j : Fin (K' + 1), Xm K' m S θ i j * g j =
      (if (j : ℕ) = i then Dfac (K' + 1) m S θ i * mu (K' + 1) m S θ i * g j else 0)
        + (if (j : ℕ) = i + 1 then
            -(Dfac (K' + 1) m S θ i * sigma (K' + 1) m S θ i) * g j else 0) := by
    intro j
    simp only [Xm, Matrix.of_apply]
    split_ifs <;> first | (exfalso; omega) | simp
  simp only [Matrix.mulVec, dotProduct, hT, Finset.sum_add_distrib]
  rw [CatalanCore.sum_ite_val_eq (i : ℕ)
      (fun j => Dfac (K' + 1) m S θ i * mu (K' + 1) m S θ i * g j),
    CatalanCore.sum_ite_val_eq ((i : ℕ) + 1)
      (fun j => -(Dfac (K' + 1) m S θ i * sigma (K' + 1) m S θ i) * g j)]
  rw [dif_pos (by omega), dif_pos (by omega)]

/-- **The Darboux intertwiner** (vector form): `X T~ = (T~' + β) X`, `g = 0`. -/
theorem Xm_Ttil [CharZero F] (K' m S : ℕ) (hm : 1 ≤ m) (θ : F) (hθ : Gen θ) (hS : S + m = K')
    (v : Fin (K' + 1) → F) :
    Xm K' m S θ *ᵥ (Ttil (K' + 1) m S θ *ᵥ v) =
      Ttil K' m (S + 1) θ *ᵥ (Xm K' m S θ *ᵥ v) + betaD K' m S θ • (Xm K' m S θ *ᵥ v) := by
  funext i
  have hi := i.2
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [Xm_mulVec, Ttil_apply, Ttil_apply, Ttil_apply, Xm_mulVec]
  have hv : ∀ (h : (i : ℕ) - 1 + 1 < K' + 1) (h' : (i : ℕ) < K' + 1), 0 < (i : ℕ) →
      v ⟨(i : ℕ) - 1 + 1, h⟩ = v ⟨(i : ℕ), h'⟩ := fun h h' h0 =>
    congrArg v (Fin.ext (by simp only; omega))
  by_cases h0 : 0 < (i : ℕ)
  · have hp := coef_prev K' m S hm θ hθ (i : ℕ) h0 hi
    have hd := coef_diag K' m S hm θ hθ hS (i : ℕ) hi
    rw [if_pos h0] at hd
    by_cases h1 : (i : ℕ) + 1 < K'
    · have hn := coef_next K' m S hm θ hθ hS (i : ℕ) hi
      rw [if_pos h1] at hn
      have hn2 := coef_next2 K' m S hm θ hθ (i : ℕ) (by omega)
      simp only [h0, h1, dif_pos, hi, Nat.add_lt_add_iff_right, Nat.succ_pos,
        Nat.add_one_sub_one]
      rw [Xm_mulVec, Xm_mulVec, hv _ (by omega) h0]
      push_cast
      linear_combination (-(v ⟨(i : ℕ) - 1, by omega⟩)) * hp + (v ⟨(i : ℕ), by omega⟩) * hd
        + (-(v ⟨(i : ℕ) + 1, by omega⟩)) * hn + (v ⟨(i : ℕ) + 1 + 1, by omega⟩) * hn2
    · have hn := coef_next K' m S hm θ hθ hS (i : ℕ) hi
      rw [if_neg h1] at hn
      simp only [h0, h1, dif_pos, dif_neg, hi, Nat.add_lt_add_iff_right, Nat.succ_pos,
        Nat.add_one_sub_one, not_false_eq_true]
      rw [Xm_mulVec, hv _ (by omega) h0]
      push_cast
      linear_combination (-(v ⟨(i : ℕ) - 1, by omega⟩)) * hp + (v ⟨(i : ℕ), by omega⟩) * hd
        + (-(v ⟨(i : ℕ) + 1, by omega⟩)) * hn
  · have hd := coef_diag K' m S hm θ hθ hS (i : ℕ) hi
    rw [if_neg h0] at hd
    by_cases h1 : (i : ℕ) + 1 < K'
    · have hn := coef_next K' m S hm θ hθ hS (i : ℕ) hi
      rw [if_pos h1] at hn
      have hn2 := coef_next2 K' m S hm θ hθ (i : ℕ) (by omega)
      simp only [h0, h1, dif_pos, dif_neg, hi, Nat.add_lt_add_iff_right, Nat.succ_pos,
        Nat.add_one_sub_one, not_false_eq_true]
      rw [Xm_mulVec]
      push_cast
      linear_combination (v ⟨(i : ℕ), by omega⟩) * hd
        + (-(v ⟨(i : ℕ) + 1, by omega⟩)) * hn + (v ⟨(i : ℕ) + 1 + 1, by omega⟩) * hn2
    · have hn := coef_next K' m S hm θ hθ hS (i : ℕ) hi
      rw [if_neg h1] at hn
      simp only [h0, h1, dif_pos, dif_neg, hi, Nat.add_lt_add_iff_right, Nat.succ_pos,
        Nat.add_one_sub_one, not_false_eq_true]
      push_cast
      linear_combination (v ⟨(i : ℕ), by omega⟩) * hd + (-(v ⟨(i : ℕ) + 1, by omega⟩)) * hn

/-- `Xm` is `Xmat (K'+1)` (the row type `Fin (K'+1-1)` is `Fin K'`). -/
lemma Xm_eq_Xmat (K' m S : ℕ) (θ : F) :
    Xm K' m S θ = (Xmat (K' + 1) m S θ : Matrix (Fin K') (Fin (K' + 1)) F) := rfl

end CatalanCore.Star.Leonard
