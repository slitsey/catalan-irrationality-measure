module
public import CatalanMeasure.GenD.Uniform.W.FrobInst.Gamma
public import CatalanMeasure.GenD.Uniform.W.Thin.TPoly
public import CatalanMeasure.GenD.Uniform.Prefix.NativeSpans
@[expose] public section
set_option Elab.async false

/-!
# Symmetric (H-type) pair rows in the G row index

`pairRowH j k = e_{(k0+k)p + j} + e_{(k0+k+1)p - j}`, `0 ≤ j ≤ (p-1)/2` (`j = 0` is the pair of
block centres).  These are the `H+` atoms of the physical tiling (`Thin.Index`: tiling pair
`(k, j)` sits at G rows `kp + j`, `(k+1)p - j` after the shift).

* `intrinsicU_hRows`, `intrinsicT_hRows` : the identities `F = nativePlus_j (U_k + U_{k-1})(Y)`,
  `U_{p-1} G = nativePlus_j (1+Y)(U_k - U_{k-1})(Y)` (`physical_pair_U_plus/T_plus`).
-/

namespace CatalanMeasure.GenD.Uniform.W.FrobInst
open Polynomial Polynomial.Chebyshev CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W.Thin
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

/-- The symmetric pair row `e_{(k0+k)p + j} + e_{(k0+k+1)p - j}`. -/
def pairRowH (P : Parameters) (N p : ℕ) {K : ℕ} (k0 : ℤ) (j : ℕ) (k : Fin K) :
    Fin (P.n N) → ZMod p := fun r =>
  (if (r : ℤ) - P.g N = (k0 + (k : ℕ)) * p + j then (1 : ZMod p) else 0) +
    (if (r : ℤ) - P.g N = (k0 + (k : ℕ) + 1) * p - j then (1 : ZMod p) else 0)

/-- Both members of the pair are actual rows. -/
def HGood (P : Parameters) (N p : ℕ) {K : ℕ} (k0 : ℤ) (j : ℕ) (k : Fin K) : Prop :=
  InRange P N ((k0 + (k : ℕ)) * p + j) ∧ InRange P N ((k0 + (k : ℕ) + 1) * p - j)

/-- Rows of an `H+` profile family `x : Fin D → Fin K → F_p` (offset `j = d`). -/
def hRows (P : Parameters) (N p K D : ℕ) (k0 : ℤ) :
    (Fin D → Fin K → ZMod p) →ₗ[ZMod p] (Fin (P.n N) → ZMod p) :=
  ∑ d : Fin D, ∑ k : Fin K,
    (coordLin p K D d k).smulRight (pairRowH P N p k0 (d : ℕ) k)

theorem hRows_apply (K D : ℕ) (k0 : ℤ) (x : Fin D → Fin K → ZMod p) (r : Fin (P.n N)) :
    hRows P N p K D k0 x r = ∑ d : Fin D, ∑ k : Fin K, x d k * pairRowH P N p k0 (d : ℕ) k r := by
  simp [hRows, LinearMap.sum_apply, coordLin]

theorem sum_pairRowH {K : ℕ} (k0 : ℤ) (j : ℕ) (k : Fin K) (hg : HGood P N p k0 j k)
    (F : ℤ → (ZMod p)[X]) :
    ∑ r : Fin (P.n N), C (pairRowH P N p k0 j k r) * F ((r : ℤ) - P.g N) =
      F ((k0 + (k : ℕ)) * p + j) + F ((k0 + (k : ℕ) + 1) * p - j) := by
  calc ∑ r : Fin (P.n N), C (pairRowH P N p k0 j k r) * F ((r : ℤ) - P.g N)
      = ∑ r : Fin (P.n N),
        (C (if (r : ℤ) - P.g N = (k0 + (k : ℕ)) * p + j then (1 : ZMod p) else 0) *
            F ((r : ℤ) - P.g N) +
          C (if (r : ℤ) - P.g N = (k0 + (k : ℕ) + 1) * p - j then (1 : ZMod p) else 0) *
            F ((r : ℤ) - P.g N)) :=
        Finset.sum_congr rfl fun r _ => by unfold pairRowH; rw [map_add, _root_.add_mul]
    _ = _ := by rw [Finset.sum_add_distrib, sum_ind _ hg.1, sum_ind _ hg.2]

theorem sum_hRows {K D : ℕ} (k0 : ℤ) (x : Fin D → Fin K → ZMod p)
    (hx : ∀ (d : Fin D) k, ¬ HGood P N p k0 (d : ℕ) k → x d k = 0) (F : ℤ → (ZMod p)[X]) :
    ∑ r : Fin (P.n N), C (hRows P N p K D k0 x r) * F ((r : ℤ) - P.g N) =
      ∑ d : Fin D, ∑ k : Fin K, C (x d k) *
        (F ((k0 + (k : ℕ)) * p + (d : ℕ)) + F ((k0 + (k : ℕ) + 1) * p - (d : ℕ))) := by
  simp_rw [hRows_apply, map_sum, map_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hg : HGood P N p k0 (d : ℕ) k
  · rw [← sum_pairRowH k0 (d : ℕ) k hg F, Finset.mul_sum]
    exact Finset.sum_congr rfl fun r _ => by ring
  · rw [hx d k hg]
    simp

/-! ### The identities -/

theorem nativeCenter_eq_U (hp2 : p ≠ 2) :
    nativeCenter (p := p) = Chebyshev.U (ZMod p) ((p : ℤ) - 1) := by
  rw [chebyshev_U_prime hp2]; rfl

/-- `U_{p-1} T_j + (1 - T_p) U_{j-1} = nativePlus j`. -/
theorem slotPlus_eq (hp2 : p ≠ 2) (j : ℤ) :
    Chebyshev.U (ZMod p) ((p : ℤ) - 1) * Chebyshev.T (ZMod p) j +
      (1 - Chebyshev.T (ZMod p) (p : ℤ)) * Chebyshev.U (ZMod p) (j - 1) = nativePlus (p := p) j := by
  rw [nativePlus_formula hp2, ← nativeCenter_eq_U hp2, chebyshev_T_prime hp2]

theorem U_pair_plus (hp2 : p ≠ 2) (κ j : ℤ) :
    Chebyshev.U (ZMod p) (κ * p + j - 1) + Chebyshev.U (ZMod p) ((κ + 1) * p - j - 1) =
      (Chebyshev.U (ZMod p) κ + Chebyshev.U (ZMod p) (κ - 1)).comp (X ^ p) *
        nativePlus (p := p) j := by
  have h := physical_pair_U_plus (ZMod p) κ p j
  rw [h, ← slotPlus_eq hp2 j, chebyshev_T_prime hp2]
  simp only [Polynomial.add_comp]

theorem T_pair_plus (hp2 : p ≠ 2) (κ j : ℤ) :
    (X ^ 2 - 1 : (ZMod p)[X]) ^ ((p - 1) / 2) *
        (Chebyshev.T (ZMod p) (κ * p + j) + Chebyshev.T (ZMod p) ((κ + 1) * p - j)) =
      ((1 + X) * (Chebyshev.U (ZMod p) κ - Chebyshev.U (ZMod p) (κ - 1))).comp (X ^ p) *
        nativePlus (p := p) j := by
  have h := physical_pair_T_plus (ZMod p) κ p j
  rw [← chebyshev_U_prime hp2, h, ← slotPlus_eq hp2 j, chebyshev_T_prime hp2]
  simp only [Polynomial.mul_comp, Polynomial.add_comp, Polynomial.sub_comp, Polynomial.one_comp,
    Polynomial.X_comp]

/-- `F`-part of the `H+` rows. -/
theorem intrinsicU_hRows {K D : ℕ} (hp2 : p ≠ 2) (k0 : ℤ) (x : Fin D → Fin K → ZMod p)
    (hx : ∀ (d : Fin D) k, ¬ HGood P N p k0 (d : ℕ) k → x d k = 0) :
    intrinsicU P N p (hRows P N p K D k0 x) =
      ∑ d : Fin D, nativePlus (p := p) ((d : ℕ) : ℤ) *
        (∑ k : Fin K, C (x d k) *
          (Chebyshev.U (ZMod p) (k0 + (k : ℕ)) + Chebyshev.U (ZMod p) (k0 + (k : ℕ) - 1))).comp
            (X ^ p) := by
  have h := sum_hRows (P := P) (N := N) k0 x hx (fun m => Chebyshev.U (ZMod p) (m - 1))
  unfold intrinsicU
  rw [show (∑ r : Fin (P.n N), C (hRows P N p K D k0 x r) *
      Chebyshev.U (ZMod p) ((r.val : ℤ) - P.g N - 1)) = _ from h]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [sum_comp', Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have e := U_pair_plus hp2 (k0 + (k : ℕ)) ((d : ℕ) : ℤ)
  have e' : Chebyshev.U (ZMod p) ((k0 + (k : ℕ)) * p + (d : ℕ) - 1) +
      Chebyshev.U (ZMod p) ((k0 + (k : ℕ) + 1) * p - (d : ℕ) - 1) =
      (Chebyshev.U (ZMod p) (k0 + (k : ℕ)) + Chebyshev.U (ZMod p) (k0 + (k : ℕ) - 1)).comp
        (X ^ p) * nativePlus (p := p) ((d : ℕ) : ℤ) := e
  rw [e']
  simp only [Polynomial.C_mul_comp]
  ring

/-- `T`-part of the `H+` rows. -/
theorem intrinsicT_hRows {K D : ℕ} (hp2 : p ≠ 2) (k0 : ℤ) (x : Fin D → Fin K → ZMod p)
    (hx : ∀ (d : Fin D) k, ¬ HGood P N p k0 (d : ℕ) k → x d k = 0) :
    (X ^ 2 - 1 : (ZMod p)[X]) ^ ((p - 1) / 2) * intrinsicT P N p (hRows P N p K D k0 x) =
      ∑ d : Fin D, nativePlus (p := p) ((d : ℕ) : ℤ) *
        (∑ k : Fin K, C (x d k) *
          ((1 + X) * (Chebyshev.U (ZMod p) (k0 + (k : ℕ)) -
            Chebyshev.U (ZMod p) (k0 + (k : ℕ) - 1)))).comp (X ^ p) := by
  have h := sum_hRows (P := P) (N := N) k0 x hx (fun m => Chebyshev.T (ZMod p) m)
  unfold intrinsicT
  rw [show (∑ r : Fin (P.n N), C (hRows P N p K D k0 x r) *
      Chebyshev.T (ZMod p) ((r.val : ℤ) - P.g N)) = _ from h]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [sum_comp', Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have e := T_pair_plus hp2 (k0 + (k : ℕ)) ((d : ℕ) : ℤ)
  have e' : (X ^ 2 - 1 : (ZMod p)[X]) ^ ((p - 1) / 2) *
      (Chebyshev.T (ZMod p) ((k0 + (k : ℕ)) * p + (d : ℕ)) +
        Chebyshev.T (ZMod p) ((k0 + (k : ℕ) + 1) * p - (d : ℕ))) =
      ((1 + X) * (Chebyshev.U (ZMod p) (k0 + (k : ℕ)) -
        Chebyshev.U (ZMod p) (k0 + (k : ℕ) - 1))).comp (X ^ p) *
        nativePlus (p := p) ((d : ℕ) : ℤ) := e
  rw [← mul_assoc, mul_comm _ (C (x d k)), mul_assoc, e']
  simp only [Polynomial.C_mul_comp]
  ring

end
end CatalanMeasure.GenD.Uniform.W.FrobInst
