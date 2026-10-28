module
public import CatalanMeasure.GenD.Uniform.W.FrobInst.HResp
public import CatalanMeasure.GenD.Uniform.W.FrobInst.CType
@[expose] public section
set_option Elab.async false

/-!
# Response of the mixed atoms `cTheta zC + hTheta zH`

`uResp_mixed` : for a visible column `j < H`,

    uResp j (cTheta zC + hTheta zH) =
      Σ_{e < h + R0} [p ∣ H-1-(j mod p)-e] ·
        (psiLin 3 0 H (j/p) a_e (wvec e of zC) + psiLinH 3 0 H (j/p) a_e (w_e of zH)),

the `C` slot coefficients `[X^e] 2 (X-1)^h X^r` and the `H` slot coefficients
`[X^e] 2 trunc_{<mn}((X-1)^h X^r)` (zero for `e ≥ mn`).
-/

namespace CatalanMeasure.GenD.Uniform.W.FrobInst
open Module Polynomial Polynomial.Chebyshev CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W.Thin
  CatalanMeasure.GenD.Uniform.W
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

theorem Rsum_expand {K R0 : ℕ} (h mn : ℕ) (L : (Fin K → ZMod p) →ₗ[ZMod p] (ZMod p)[X])
    (z : Fin R0 → Fin K → ZMod p) :
    ∑ r : Fin R0, Rpoly p h mn r * (L (z r)).comp (X ^ p) =
      ∑ e ∈ Finset.range mn, X ^ e * (L (wH p h z e)).comp (X ^ p) := by
  have hL : ∀ e, L (wH p h z e) = ∑ r : Fin R0,
      C (2 * ((X - 1) ^ h * X ^ (r : ℕ) : (ZMod p)[X]).coeff e) * L (z r) := by
    intro e
    simp [wH, map_sum, map_smul, Polynomial.smul_eq_C_mul]
  have hR : ∀ r : Fin R0, Rpoly p h mn r * (L (z r)).comp (X ^ p) =
      ∑ e ∈ Finset.range mn, X ^ e * (C (2 * ((X - 1) ^ h * X ^ (r : ℕ) : (ZMod p)[X]).coeff e) *
        (L (z r)).comp (X ^ p)) := by
    intro r
    unfold Rpoly
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun e _ => by ring
  have hE : ∀ e, X ^ e * (L (wH p h z e)).comp (X ^ p) =
      ∑ r : Fin R0, X ^ e * (C (2 * ((X - 1) ^ h * X ^ (r : ℕ) : (ZMod p)[X]).coeff e) *
        (L (z r)).comp (X ^ p)) := by
    intro e
    rw [hL e, sum_comp', Finset.mul_sum]
    exact Finset.sum_congr rfl fun r _ => by rw [Polynomial.mul_comp, Polynomial.C_comp]
  simp_rw [hR, hE]
  rw [Finset.sum_comm]

theorem uResp_hTheta (hP : Admissible P) (hN : 0 < N) (hp2 : p ≠ 2) (hH : P.H N < p ^ 2)
    {K R0 : ℕ} {mn : ℕ} (h0 : 0 < P.h N) (hh : P.h N ≤ (p - 1) / 2 + 1) (hmn : mn ≤ P.h N)
    (hhp : P.h N ≤ p) (k0 : ℤ)
    (hg : ∀ (j : Fin ((p - 1) / 2 + 1)) (k : Fin K), HGood P N p k0 (j : ℕ) k)
    (z : Fin R0 → Fin K → ZMod p) {j : ℕ} (hj : j < P.H N) :
    uResp P N p j (hTheta P N p hp2 h0 hh hmn K R0 k0 z) =
      ∑ e ∈ Finset.range mn,
        if (p : ℤ) ∣ (P.H N : ℤ) - 1 - ((j % p : ℕ) : ℤ) - e then
          psiLinH p K k0 (P.H N) (j / p)
            (((P.H N : ℤ) - 1 - ((j % p : ℕ) : ℤ) - e) / p) (wH p (P.h N) z e)
        else 0 := by
  rw [uResp_intrinsicResponse hP hN hp2 hH hj, mul_assoc,
    hT_hTheta hp2 h0 hh hmn hhp k0 hg z, hU_hTheta hp2 h0 hh hmn hhp k0 hg z,
    Rsum_expand (P.h N) mn (gyH p K k0) z, Rsum_expand (P.h N) mn (tyH p K k0) z,
    intrinsicResponse_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [intrinsicResponse_monomial]
  split_ifs <;> rfl

end
end CatalanMeasure.GenD.Uniform.W.FrobInst
