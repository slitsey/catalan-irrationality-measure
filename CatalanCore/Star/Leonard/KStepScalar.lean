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

end CatalanCore.Star.Leonard
