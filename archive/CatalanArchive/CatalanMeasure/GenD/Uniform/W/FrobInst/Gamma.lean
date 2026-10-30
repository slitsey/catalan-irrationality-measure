module
public import CatalanMeasure.GenD.Uniform.W.Frob.MixedM
public import CatalanMeasure.GenD.Uniform.W.Thin.TKill
public import CatalanMeasure.GenD.Uniform.W.Thin.TPoly
@[expose] public section
set_option Elab.async false

/-!
# Derivation of the `Γ` matrix of Theorem M from the moment forms

The truncated (`H+`) atoms of Theorem U carry, in block `k`, the `Y`-series (`Y = X^p`)

    F-part  (Y-1) (U_k + U_{k-1})(Y),      T-part  (Y-1)(1+Y)(U_k - U_{k-1})(Y)

(`physical_pair_U_plus/T_plus`, then `(y-1)^h Λ_s = (Y-1) R`).  `psiLinH` is the source covector
`digitPhi` of these two series at the actual moments `sourceM J`, `sourceZ J`.  Here the digit-`3`
entries `psiLinH … J 3 (e_i)` for `J = 1, 2`, `i = 0, 1` are *computed* from the moment forms
and shown to be the entries of `gammaQ`; the determinant `-1291/96` is then a computation on the
derived entries.
-/

namespace CatalanMeasure.GenD.Uniform.W.FrobInst
open Polynomial Polynomial.Chebyshev OAI.InternalCatalan CatalanMeasure.GenD.Uniform.Prefix
  CatalanMeasure.GenD.Uniform.W.Thin CatalanMeasure.GenD.Uniform.W Matrix
noncomputable section
variable {p : ℕ} [Fact p.Prime]

/-- `F`-series of the symmetric pair atoms: `(Y-1) Σ_k y_k (U_{k0+k} + U_{k0+k-1})`. -/
def tyH (p K : ℕ) [Fact p.Prime] (k0 : ℤ) : (Fin K → ZMod p) →ₗ[ZMod p] (ZMod p)[X] :=
  ∑ k : Fin K, (LinearMap.proj k : (Fin K → ZMod p) →ₗ[ZMod p] ZMod p).smulRight
    ((X - 1) * (Chebyshev.U (ZMod p) (k0 + (k : ℕ)) + Chebyshev.U (ZMod p) (k0 + (k : ℕ) - 1)))

/-- `T`-series of the symmetric pair atoms: `(Y-1)(1+Y) Σ_k y_k (U_{k0+k} - U_{k0+k-1})`. -/
def gyH (p K : ℕ) [Fact p.Prime] (k0 : ℤ) : (Fin K → ZMod p) →ₗ[ZMod p] (ZMod p)[X] :=
  ∑ k : Fin K, (LinearMap.proj k : (Fin K → ZMod p) →ₗ[ZMod p] ZMod p).smulRight
    ((X - 1) * (1 + X) * (Chebyshev.U (ZMod p) (k0 + (k : ℕ)) - Chebyshev.U (ZMod p) (k0 + (k : ℕ) - 1)))

theorem tyH_apply (K : ℕ) (k0 : ℤ) (y : Fin K → ZMod p) :
    tyH p K k0 y = ∑ k : Fin K, C (y k) *
      ((X - 1) * (Chebyshev.U (ZMod p) (k0 + (k : ℕ)) + Chebyshev.U (ZMod p) (k0 + (k : ℕ) - 1))) := by
  simp [tyH, LinearMap.sum_apply, Polynomial.smul_eq_C_mul]

theorem gyH_apply (K : ℕ) (k0 : ℤ) (y : Fin K → ZMod p) :
    gyH p K k0 y = ∑ k : Fin K, C (y k) *
      ((X - 1) * (1 + X) * (Chebyshev.U (ZMod p) (k0 + (k : ℕ)) - Chebyshev.U (ZMod p) (k0 + (k : ℕ) - 1))) := by
  simp [gyH, LinearMap.sum_apply, Polynomial.smul_eq_C_mul]

/-- The source covector of the symmetric pair atoms at `(J, a)` as a linear functional. -/
def psiLinH (p K : ℕ) [Fact p.Prime] (k0 : ℤ) (H J : ℕ) (a : ℤ) :
    (Fin K → ZMod p) →ₗ[ZMod p] ZMod p where
  toFun y := digitPhi H a (sourceM (p := p) J) (sourceZ (p := p) J)
    (gyH p K k0 y) (tyH p K k0 y) (3 / 2)
  map_add' y z := by
    simp only [map_add]
    unfold digitPhi
    simp only [intrinsicCoeff_add', add_mul, Finset.sum_add_distrib, mul_add]
    ring
  map_smul' c y := by
    simp only [map_smul, RingHom.id_apply, smul_eq_mul]
    unfold digitPhi
    simp only [intrinsicCoeff_smul', mul_assoc, ← Finset.mul_sum]
    ring

/-! ### Rational residues of explicit literals -/

theorem palRes_div (a : ℤ) (b : ℕ) (hb : (b : ZMod p) ≠ 0) :
    palindromicRatResidue p ((a : ℚ) / b) = (a : ZMod p) / (b : ZMod p) := by
  have hb0 : b ≠ 0 := fun h => hb (by simp [h])
  set q : ℚ := (a : ℚ) / b with hq
  have hdvd : (q.den : ℤ) ∣ (b : ℤ) := by
    have h := Rat.den_dvd a (b : ℤ)
    rwa [Rat.divInt_eq_div] at h
  have hden : (q.den : ZMod p) ≠ 0 := by
    intro h
    apply hb
    have h1 : p ∣ q.den := (ZMod.natCast_eq_zero_iff _ _).mp h
    have h2 : (q.den : ℤ) ∣ (b : ℤ) := hdvd
    have h3 : q.den ∣ b := by exact_mod_cast h2
    exact (ZMod.natCast_eq_zero_iff _ _).mpr (h1.trans h3)
  have hcross : q.num * (b : ℤ) = a * (q.den : ℤ) := by
    have h := Rat.num_div_den q
    have hbq : (b : ℚ) ≠ 0 := by exact_mod_cast hb0
    have hdq : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_nz
    have : (q.num : ℚ) / q.den = (a : ℚ) / b := by rw [h]
    rw [div_eq_div_iff hdq hbq] at this
    exact_mod_cast this
  unfold palindromicRatResidue
  rw [div_eq_div_iff hden hb]
  have := congrArg (fun z : ℤ => (z : ZMod p)) hcross
  simpa using this

theorem unit_of_dvd_72 (hp2 : p ≠ 2) (hp3 : p ≠ 3) (b : ℕ) (hb : b ∣ 72) (hb0 : b ≠ 0) :
    (b : ZMod p) ≠ 0 := by
  intro h
  have h1 : p ∣ b := (ZMod.natCast_eq_zero_iff _ _).mp h
  have h2 : p ∣ 72 := h1.trans hb
  have hp := Fact.out (p := p.Prime)
  have h3 : p ∣ 2 ^ 3 * 3 ^ 2 := by norm_num; exact h2
  rcases (Nat.Prime.dvd_mul hp).mp h3 with h4 | h4
  · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h4))
  · exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow h4))

end
end CatalanMeasure.GenD.Uniform.W.FrobInst
