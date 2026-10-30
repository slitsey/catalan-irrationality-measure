module
public import CatalanMeasure.GenD.Uniform.W.FrobInst.MInj
@[expose] public section
set_option Elab.async false

/-!
# Theorem M: the instance `MixedMData`

For a design in the window `MWin` and `p ∉ {2, 3}` we construct

    mixedInst : MixedMData P N p (mCount P N p)

with `α v = (psiLin 3 0 H J 2 v)_{J=0,1}`, `β v = (psiLin 3 0 H (J+1) 3 v)_{J=0,1}`,
`Γ = gammaH p H` (derived from the moments; equal to the residue of `gammaQ`), and the atom map

    ι V x = cTheta (φ ⊗ fst x) + hTheta (φ ⊗ snd x),

where `φ : F_p^{mCount} → ker holeMap` is an injective linear map into the admissible
polynomials `S` (so `P = (y-1)^h S` has no coefficients in the hole `[h, eta)`).
-/

namespace CatalanMeasure.GenD.Uniform.W.FrobInst
open Module Polynomial Polynomial.Chebyshev CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W.Thin
  CatalanMeasure.GenD.Uniform.W
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

/-- `φ ⊗ id`: `x ↦ (r ↦ Σ_a φ(e_a)_r • x_a)`. -/
def tens {T : Type*} [AddCommGroup T] [Module (ZMod p) T] {m R : ℕ}
    (φ : (Fin m → ZMod p) →ₗ[ZMod p] (Fin R → ZMod p)) : (Fin m → T) →ₗ[ZMod p] (Fin R → T) where
  toFun x r := ∑ a : Fin m, φ (Pi.single a (1 : ZMod p)) r • x a
  map_add' x y := by
    funext r
    simp only [Pi.add_apply, smul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    funext r
    simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]
    exact Finset.sum_congr rfl fun a _ => smul_comm _ _ _

theorem phi_apply {m R : ℕ} (φ : (Fin m → ZMod p) →ₗ[ZMod p] (Fin R → ZMod p))
    (y : Fin m → ZMod p) (r : Fin R) :
    φ y r = ∑ a : Fin m, φ (Pi.single a 1) r * y a := by
  have hy : y = ∑ a : Fin m, y a • (Pi.single a 1 : Fin m → ZMod p) := by
    funext b
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hy]
  simp [map_sum, map_smul, mul_comm]

theorem tens_injective {m R c : ℕ} (φ : (Fin m → ZMod p) →ₗ[ZMod p] (Fin R → ZMod p))
    (hφ : Function.Injective φ) (x : Fin m → Fin c → ZMod p) (h : tens φ x = 0) : x = 0 := by
  funext a k
  have h1 : (fun a => x a k) = 0 := by
    apply hφ
    funext r
    have h2 := congrFun (congrFun h r) k
    simp only [tens, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, Pi.zero_apply] at h2
    rw [phi_apply]
    simpa using h2
  exact congrFun h1 a

/-- `q_a(e) = Σ_r cMat e r · φ(e_a)_r`: the `e`-th coefficient of `2 P_a`. -/
def qco (P : Parameters) (N p : ℕ) [Fact p.Prime] {m : ℕ}
    (φ : (Fin m → ZMod p) →ₗ[ZMod p] (Fin (R0 P N p) → ZMod p)) (a : Fin m) (e : ℕ) : ZMod p :=
  ∑ r : Fin (R0 P N p), cMat P N p e r * φ (Pi.single a 1) r

theorem lin_comb {m : ℕ} {T : Type*} [AddCommGroup T] [Module (ZMod p) T]
    (φ : (Fin m → ZMod p) →ₗ[ZMod p] (Fin (R0 P N p) → ZMod p))
    (L : T →ₗ[ZMod p] ZMod p) (c : Fin m → T) (e : ℕ) :
    L (∑ r : Fin (R0 P N p), cMat P N p e r • tens φ c r) =
      ∑ a : Fin m, qco P N p φ a e * L (c a) := by
  have h1 : ∀ r : Fin (R0 P N p), L (tens φ c r) =
      ∑ a : Fin m, φ (Pi.single a (1 : ZMod p)) r * L (c a) := by
    intro r
    simp only [tens, LinearMap.coe_mk, AddHom.coe_mk, map_sum, map_smul, smul_eq_mul]
  simp only [map_sum, map_smul, smul_eq_mul, h1, qco, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun r _ => ?_
  ring

theorem cMat_eq (e r : ℕ) :
    (2 * (X - 1) ^ P.h N * X ^ (0 + r) : (ZMod p)[X]).coeff e = cMat P N p e r := by
  simp [cMat, mul_assoc, Polynomial.coeff_ofNat_mul]

theorem wvec_prof_cMat (hp2 : p ≠ 2) {K R : ℕ} (z : Fin R → Fin K → ZMod p) (e : ℕ) :
    wvec P N p (prof hp2 K 0 R z) e = ∑ r : Fin R, cMat P N p e r • z r := by
  rw [wvec_prof]
  exact Finset.sum_congr rfl fun r _ => by rw [cMat_eq]

theorem wH_cMat {K R : ℕ} (z : Fin R → Fin K → ZMod p) (e : ℕ) :
    wH p (P.h N) z e = ∑ r : Fin R, cMat P N p e r • z r := rfl

end
end CatalanMeasure.GenD.Uniform.W.FrobInst
