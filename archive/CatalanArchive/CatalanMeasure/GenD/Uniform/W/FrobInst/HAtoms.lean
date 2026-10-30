module
public import CatalanMeasure.GenD.Uniform.W.FrobInst.HRows
@[expose] public section
set_option Elab.async false

/-!
# Truncated (`H+`) atoms `Hplus(Λ_s) τ^i` with `Λ_s = (y-1)^{p-h} R`

For a monomial coordinate `y^r` of the free polynomial `S`, put
`R_r = 2 · trunc_{<mn}((y-1)^h y^r)` (low part of `2P`, `mn = min(eta, h)`) and
`Λ_r = (y-1)^{p-h} R_r`.  For `h ≤ (p-1)/2 + 1` and `mn ≤ h` the polynomial `Λ_r` lies in the exact
native span `(y-1)^{(p-1)/2} · degreeLT ((p-1)/2+1)` of the `H+` pair vectors
(`Prefix.plus_native_span`), so it has coordinates `ρ_r` in `nativePlus 0 … nativePlus ((p-1)/2)`.

`hTheta` is the atom map on `Π ⊗ F_p^K`; `hU_hTheta`, `hT_hTheta` are the response identities
`(y-1)^h · F = Σ_r R_r(y) · (Y-1)(U_k+U_{k-1})(Y) z_{r,k}` (using `(y-1)^p = Y-1`).
-/

namespace CatalanMeasure.GenD.Uniform.W.FrobInst
open Polynomial Polynomial.Chebyshev CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W.Thin
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

/-- `2 · trunc_{<mn} ((y-1)^h y^r)`. -/
def Rpoly (p h mn r : ℕ) : (ZMod p)[X] :=
  ∑ e ∈ Finset.range mn, C (2 * ((X - 1) ^ h * X ^ r : (ZMod p)[X]).coeff e) * X ^ e

theorem Rpoly_coeff (h mn r e : ℕ) :
    (Rpoly p h mn r).coeff e =
      if e < mn then 2 * ((X - 1) ^ h * X ^ r : (ZMod p)[X]).coeff e else 0 := by
  unfold Rpoly
  rw [finsetSum_coeff]
  simp only [coeff_C_mul, coeff_X_pow]
  simp [Finset.sum_ite_eq']

theorem Rpoly_natDegree_le (h mn r : ℕ) : (Rpoly p h mn r).natDegree ≤ mn - 1 := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro e he
  rw [Rpoly_coeff, if_neg (by omega)]

/-- `Λ_r = (y-1)^{p-h} R_r`. -/
def Lpoly (p h mn r : ℕ) : (ZMod p)[X] := (X - 1) ^ (p - h) * Rpoly p h mn r

theorem plusVectors_rev (hp2 : p ≠ 2) (j : Fin ((p - 1) / 2 + 1)) :
    plusVectors (p := p) (Fin.rev j) = nativePlus (p := p) ((j : ℕ) : ℤ) := by
  have hj := j.isLt
  have hodd := native_half_identity hp2
  unfold plusVectors
  by_cases h0 : (j : ℕ) = 0
  · have : ¬ (Fin.rev j).val < (p - 1) / 2 := by rw [Fin.val_rev]; omega
    rw [if_neg this, h0]
    unfold nativeCenter nativePlus
    haveI : NeZero (2 : ZMod p) := ⟨two_ne_zero_zmod hp2⟩
    rw [← chebyshev_U_prime hp2]
    simp
  · have : (Fin.rev j).val < (p - 1) / 2 := by rw [Fin.val_rev]; omega
    rw [if_pos this]
    congr 1
    rw [Fin.val_rev]
    have hjle : (j : ℕ) ≤ (p - 1) / 2 := by omega
    have e1 : (p - 1) / 2 + 1 - ((j : ℕ) + 1) = (p - 1) / 2 - (j : ℕ) := by omega
    rw [e1, Nat.cast_sub hjle]
    ring

theorem Lpoly_mem (hp2 : p ≠ 2) {h mn : ℕ} (h0 : 0 < h) (hh : h ≤ (p - 1) / 2 + 1) (hmn : mn ≤ h)
    (r : ℕ) :
    Lpoly p h mn r ∈ Submodule.span (ZMod p) (Set.range (plusVectors (p := p))) := by
  have hodd := native_half_identity hp2
  rw [plus_native_span hp2]
  refine Submodule.mem_map.mpr ⟨(X - 1) ^ (p - h - (p - 1) / 2) * Rpoly p h mn r, ?_, ?_⟩
  · rw [Polynomial.mem_degreeLT]
    have hd : ((X - 1) ^ (p - h - (p - 1) / 2) * Rpoly p h mn r : (ZMod p)[X]).natDegree ≤
        (p - 1) / 2 := by
      refine natDegree_mul_le.trans ?_
      have h1 : ((X - 1) ^ (p - h - (p - 1) / 2) : (ZMod p)[X]).natDegree ≤
          p - h - (p - 1) / 2 := by
        refine natDegree_pow_le.trans ?_
        have : (X - 1 : (ZMod p)[X]).natDegree ≤ 1 := by compute_degree
        nlinarith
      have h2 := Rpoly_natDegree_le (p := p) h mn r
      omega
    exact lt_of_le_of_lt (degree_le_of_natDegree_le hd) (by exact_mod_cast Nat.lt_succ_self _)
  · show (X - 1 : (ZMod p)[X]) ^ ((p - 1) / 2) * ((X - 1) ^ (p - h - (p - 1) / 2) * Rpoly p h mn r) = _
    rw [← mul_assoc, ← pow_add, Lpoly]
    congr 2
    omega

theorem exists_rho (hp2 : p ≠ 2) {h mn : ℕ} (h0 : 0 < h) (hh : h ≤ (p - 1) / 2 + 1)
    (hmn : mn ≤ h) (r : ℕ) :
    ∃ ρ : Fin ((p - 1) / 2 + 1) → ZMod p,
      ∑ j : Fin ((p - 1) / 2 + 1), C (ρ j) * nativePlus (p := p) ((j : ℕ) : ℤ) = Lpoly p h mn r := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod p)).mp
    (Lpoly_mem hp2 h0 hh hmn r)
  refine ⟨fun j => c (Fin.rev j), ?_⟩
  rw [← hc]
  have := Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin ((p - 1) / 2 + 1)))
    (fun i => c i • plusVectors (p := p) i)
  simp only [Fin.revPerm_apply] at this
  rw [← this]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [plusVectors_rev hp2, Polynomial.smul_eq_C_mul]

/-- Coordinates of `Λ_r` in the native `H+` pair basis. -/
def rhoCoef (hp2 : p ≠ 2) {h mn : ℕ} (h0 : 0 < h) (hh : h ≤ (p - 1) / 2 + 1) (hmn : mn ≤ h) (r : ℕ) :
    Fin ((p - 1) / 2 + 1) → ZMod p :=
  Classical.choose (exists_rho hp2 h0 hh hmn r)

theorem rhoCoef_spec (hp2 : p ≠ 2) {h mn : ℕ} (h0 : 0 < h) (hh : h ≤ (p - 1) / 2 + 1) (hmn : mn ≤ h) (r : ℕ) :
    ∑ j : Fin ((p - 1) / 2 + 1), C (rhoCoef hp2 h0 hh hmn r j) * nativePlus (p := p) ((j : ℕ) : ℤ) =
      Lpoly p h mn r :=
  Classical.choose_spec (exists_rho hp2 h0 hh hmn r)

/-- The coordinate change `(z_{r,k}) ↦ (ρ_{j,k} = Σ_r ρ_r(j) z_{r,k})`. -/
def hprof (hp2 : p ≠ 2) {h mn : ℕ} (h0 : 0 < h) (hh : h ≤ (p - 1) / 2 + 1) (hmn : mn ≤ h) (K R0 : ℕ) :
    (Fin R0 → Fin K → ZMod p) →ₗ[ZMod p] (Fin ((p - 1) / 2 + 1) → Fin K → ZMod p) where
  toFun z j k := ∑ r : Fin R0, rhoCoef hp2 h0 hh hmn r j * z r k
  map_add' x y := by
    ext j k
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' a x := by
    ext j k
    simp [Finset.mul_sum, mul_left_comm]

/-- The atom map of the truncated `H+` family. -/
def hTheta (P : Parameters) (N p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) {h mn : ℕ}
    (h0 : 0 < h) (hh : h ≤ (p - 1) / 2 + 1) (hmn : mn ≤ h) (K R0 : ℕ) (k0 : ℤ) :
    (Fin R0 → Fin K → ZMod p) →ₗ[ZMod p] (Fin (P.n N) → ZMod p) :=
  (hRows P N p K ((p - 1) / 2 + 1) k0).comp (hprof hp2 h0 hh hmn K R0)

theorem frobenius_sub_one (hp2 : p ≠ 2) (a : (ZMod p)[X]) :
    ((X - 1) ^ p * a : (ZMod p)[X]) = (X ^ p - 1) * a := by
  rw [sub_pow_char, one_pow]

/-- Regrouping: `Σ_j nativePlus_j (Σ_k ρ_{jk} B_k)(Y) = Σ_r Λ_r (Σ_k z_{rk} B_k)(Y)`. -/
theorem regroup {K R0 : ℕ} (hp2 : p ≠ 2) {h mn : ℕ} (h0 : 0 < h) (hh : h ≤ (p - 1) / 2 + 1) (hmn : mn ≤ h)
    (z : Fin R0 → Fin K → ZMod p) (B : Fin K → (ZMod p)[X]) :
    ∑ j : Fin ((p - 1) / 2 + 1), nativePlus (p := p) ((j : ℕ) : ℤ) *
        (∑ k : Fin K, C (hprof hp2 h0 hh hmn K R0 z j k) * B k).comp (X ^ p) =
      ∑ r : Fin R0, Lpoly p h mn r * (∑ k : Fin K, C (z r k) * B k).comp (X ^ p) := by
  set G : Fin R0 → (ZMod p)[X] := fun r => (∑ k : Fin K, C (z r k) * B k).comp (X ^ p) with hG
  have key : ∀ j : Fin ((p - 1) / 2 + 1),
      (∑ k : Fin K, C (hprof hp2 h0 hh hmn K R0 z j k) * B k).comp (X ^ p) =
        ∑ r : Fin R0, C (rhoCoef hp2 h0 hh hmn r j) * G r := by
    intro j
    have e : ∀ k, hprof hp2 h0 hh hmn K R0 z j k = ∑ r : Fin R0, rhoCoef hp2 h0 hh hmn r j * z r k :=
      fun k => rfl
    simp_rw [e, map_sum, map_mul, Finset.sum_mul, sum_comp']
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [hG]
    simp only [sum_comp', Polynomial.mul_comp, Polynomial.C_comp, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have hsp : ∀ r : Fin R0, Lpoly p h mn r =
      ∑ j : Fin ((p - 1) / 2 + 1), C (rhoCoef hp2 h0 hh hmn r j) * nativePlus (p := p) ((j : ℕ) : ℤ) :=
    fun r => (rhoCoef_spec hp2 h0 hh hmn r).symm
  simp_rw [key, hsp, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun j _ => ?_
  ring

end
end CatalanMeasure.GenD.Uniform.W.FrobInst
