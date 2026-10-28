module
public import CatalanMeasure.GenD.Uniform.W.FrobInst.HAtoms
@[expose] public section
set_option Elab.async false

/-!
# Response of the truncated (`H+`) atoms

`uResp_hTheta` : for `z : Π ⊗ F_p^K` (all pairs actual rows) and a visible column `j < H`,

    uResp j (hTheta z) = Σ_{e < mn} [p ∣ H-1-(j mod p)-e] · psiLinH K k0 H (j/p) a_e (w_e),
    w_e = Σ_r 2 [X^e]((X-1)^h X^r) · z_r,  a_e = (H-1-(j mod p)-e)/p.
-/

namespace CatalanMeasure.GenD.Uniform.W.FrobInst
open Polynomial Polynomial.Chebyshev CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W.Thin
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

/-- Low-coefficient profile `w_e = Σ_r 2 [X^e]((X-1)^h X^r) z_r`. -/
def wH (p h : ℕ) {K R0 : ℕ} (z : Fin R0 → Fin K → ZMod p) (e : ℕ) : Fin K → ZMod p :=
  ∑ r : Fin R0, (2 * ((X - 1) ^ h * X ^ (r : ℕ) : (ZMod p)[X]).coeff e) • z r

theorem hU_hTheta {K R0 : ℕ} (hp2 : p ≠ 2) {h mn : ℕ} (h0 : 0 < h) (hh : h ≤ (p - 1) / 2 + 1)
    (hmn : mn ≤ h) (hhp : h ≤ p) (k0 : ℤ)
    (hg : ∀ (j : Fin ((p - 1) / 2 + 1)) (k : Fin K), HGood P N p k0 (j : ℕ) k)
    (z : Fin R0 → Fin K → ZMod p) :
    (X - 1) ^ h * intrinsicU P N p (hTheta P N p hp2 h0 hh hmn K R0 k0 z) =
      ∑ r : Fin R0, Rpoly p h mn r * (tyH p K k0 (z r)).comp (X ^ p) := by
  have h1 := intrinsicU_hRows (P := P) (N := N) hp2 k0 (hprof hp2 h0 hh hmn K R0 z)
    (fun d k hn => absurd (hg d k) hn)
  have h2 := regroup (K := K) (R0 := R0) hp2 h0 hh hmn z
    (fun k => Chebyshev.U (ZMod p) (k0 + (k : ℕ)) + Chebyshev.U (ZMod p) (k0 + (k : ℕ) - 1))
  show (X - 1) ^ h * intrinsicU P N p (hRows P N p K ((p - 1) / 2 + 1) k0
    (hprof hp2 h0 hh hmn K R0 z)) = _
  rw [h1, h2, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Lpoly]
  have e1 : (X - 1 : (ZMod p)[X]) ^ h * (X - 1) ^ (p - h) = X ^ p - 1 := by
    rw [← pow_add, Nat.add_sub_cancel' hhp, sub_pow_char, one_pow]
  have hrhs : (tyH p K k0 (z r)).comp (X ^ p) = (X ^ p - 1) * (∑ k : Fin K, C (z r k) *
      (Chebyshev.U (ZMod p) (k0 + (k : ℕ)) + Chebyshev.U (ZMod p) (k0 + (k : ℕ) - 1))).comp
        (X ^ p) := by
    rw [tyH_apply]
    simp only [sum_comp', Polynomial.mul_comp, Polynomial.C_comp, Polynomial.sub_comp,
      Polynomial.X_comp, Polynomial.one_comp, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [hrhs, ← e1]
  ring

theorem hT_hTheta {K R0 : ℕ} (hp2 : p ≠ 2) {h mn : ℕ} (h0 : 0 < h) (hh : h ≤ (p - 1) / 2 + 1)
    (hmn : mn ≤ h) (hhp : h ≤ p) (k0 : ℤ)
    (hg : ∀ (j : Fin ((p - 1) / 2 + 1)) (k : Fin K), HGood P N p k0 (j : ℕ) k)
    (z : Fin R0 → Fin K → ZMod p) :
    (X - 1) ^ h * ((X ^ 2 - 1 : (ZMod p)[X]) ^ ((p - 1) / 2) *
        intrinsicT P N p (hTheta P N p hp2 h0 hh hmn K R0 k0 z)) =
      ∑ r : Fin R0, Rpoly p h mn r * (gyH p K k0 (z r)).comp (X ^ p) := by
  have h1 := intrinsicT_hRows (P := P) (N := N) hp2 k0 (hprof hp2 h0 hh hmn K R0 z)
    (fun d k hn => absurd (hg d k) hn)
  have h2 := regroup (K := K) (R0 := R0) hp2 h0 hh hmn z
    (fun k => (1 + X) * (Chebyshev.U (ZMod p) (k0 + (k : ℕ)) -
      Chebyshev.U (ZMod p) (k0 + (k : ℕ) - 1)))
  show (X - 1) ^ h * ((X ^ 2 - 1 : (ZMod p)[X]) ^ ((p - 1) / 2) *
    intrinsicT P N p (hRows P N p K ((p - 1) / 2 + 1) k0 (hprof hp2 h0 hh hmn K R0 z))) = _
  rw [h1, h2, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Lpoly]
  have e1 : (X - 1 : (ZMod p)[X]) ^ h * (X - 1) ^ (p - h) = X ^ p - 1 := by
    rw [← pow_add, Nat.add_sub_cancel' hhp, sub_pow_char, one_pow]
  have hrhs : (gyH p K k0 (z r)).comp (X ^ p) = (X ^ p - 1) * (∑ k : Fin K, C (z r k) *
      ((1 + X) * (Chebyshev.U (ZMod p) (k0 + (k : ℕ)) -
        Chebyshev.U (ZMod p) (k0 + (k : ℕ) - 1)))).comp (X ^ p) := by
    rw [gyH_apply]
    simp only [sum_comp', Polynomial.mul_comp, Polynomial.C_comp, Polynomial.sub_comp,
      Polynomial.X_comp, Polynomial.one_comp, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [hrhs, ← e1]
  ring

end
end CatalanMeasure.GenD.Uniform.W.FrobInst
