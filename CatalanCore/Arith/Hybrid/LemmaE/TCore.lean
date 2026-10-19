module

public import CatalanCore.Arith.Hybrid.LemmaE.Gauss
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.FieldTheory.RatFunc.Basic

@[expose] public section

/-!
# The T-route criterion (Lemma E / GK / C7 core)

`det Full = det A · det T` with `T = D - C A⁻¹ B` (Schur complement of the clean block `A = R_CC + X`).

`tcore` is the frame- and prime-generic statement.  The instance supplies

* `g`   : a *primitive* polynomial (`gn p g = 1`), the determinant of the rescaled block;
* `N`   : a polynomial matrix with `A * N = g • 1` (`N = D adj(Ã) D`, so `A⁻¹ = N/g`);
* `hdet`: `p^s · det A = g`  (`s = 2 ∑ d_i`, block scaling);
* `hT`  : the entries of `g·D - C N B` (= `g·T`) are `p^{-b}`-integral (`GLE p b`);

and obtains `GLE p (m·b + s) (det Full)`: `v(det Full) ≥ -s - m b`.  With `b = -θ` this is the
statement `v_p(det Full) ≥ -(τ_A + m θ)` of HB's T-route.
-/

open Polynomial Matrix CatalanCore.Basic

namespace CatalanCore.Arith.Hybrid.LemmaE

variable (p : ℕ) [Fact p.Prime]

section Tcore

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The scaled Schur complement `g·D - C N B`. -/
noncomputable def Tscaled (g : ℚ[X]) (A : Matrix ι ι ℚ[X]) (B : Matrix ι κ ℚ[X]) (C : Matrix κ ι ℚ[X])
    (D : Matrix κ κ ℚ[X]) (N : Matrix ι ι ℚ[X]) : Matrix κ κ ℚ[X] :=
  g • D - C * N * B

lemma gn_const_pow_det (b : ℕ) (M : Matrix κ κ ℚ[X]) (h : ∀ a c, GLE p b (M a c)) :
    gn p M.det ≤ (p : ℝ) ^ (Fintype.card κ * b) := by
  have h1 := det_gle M (fun _ _ => b) h
  have h2 : tropVal (fun (_ : κ) (_ : κ) => b) ≤ Fintype.card κ * b := by
    apply tropVal_le_of_forall
    intro σ
    simp
  exact ((gle_iff_gn p _ _).mp (h1.mono h2))

/-- **T-route criterion.** -/
theorem tcore (Full : Matrix (ι ⊕ κ) (ι ⊕ κ) ℚ[X]) (g : ℚ[X]) (hg : gn p g = 1)
    (N : Matrix ι ι ℚ[X]) (hAN : Full.toBlocks₁₁ * N = g • (1 : Matrix ι ι ℚ[X]))
    (s : ℕ) (hdet : C ((p : ℚ) ^ s) * Full.toBlocks₁₁.det = g)
    (b : ℕ) (hT : ∀ z y, GLE p b (Tscaled g Full.toBlocks₁₁ Full.toBlocks₁₂ Full.toBlocks₂₁
        Full.toBlocks₂₂ N z y)) :
    GLE p (Fintype.card κ * b + s) Full.det := by
  classical
  set A := Full.toBlocks₁₁
  set B := Full.toBlocks₁₂
  set C' := Full.toBlocks₂₁
  set D := Full.toBlocks₂₂
  have hg0 : g ≠ 0 := by
    intro h; rw [h] at hg; simp [gn] at hg
  -- pass to the fraction field
  let K := FractionRing ℚ[X]
  let φ : ℚ[X] →+* K := algebraMap ℚ[X] K
  have hφ : Function.Injective φ := IsFractionRing.injective ℚ[X] K
  have hgK : φ g ≠ 0 := by simpa using (map_ne_zero_iff φ hφ).mpr hg0
  set Ak : Matrix ι ι K := A.map φ
  set Nk : Matrix ι ι K := N.map φ
  have hsm : ∀ (c : ℚ[X]) (M : Matrix ι ι ℚ[X]), (c • M).map φ = φ c • M.map φ := by
    intro c M; ext i j; simp
  have hAN' : Ak * Nk = (φ g) • (1 : Matrix ι ι K) := by
    have e := φ.mapMatrix.map_mul A N
    simp only [RingHom.mapMatrix_apply] at e
    have e2 : (A * N).map φ = Ak * Nk := e
    rw [← e2, hAN, hsm]
    simp
  set Ainv : Matrix ι ι K := (φ g)⁻¹ • Nk
  have h1 : Ak * Ainv = 1 := by
    simp only [Ainv, Matrix.mul_smul, hAN', smul_smul, inv_mul_cancel₀ hgK, one_smul]
  have h2 : Ainv * Ak = 1 := mul_eq_one_comm.mp h1
  let _ : Invertible Ak := ⟨Ainv, h2, h1⟩
  have hinv : (⅟Ak) = Ainv := rfl
  have hFull : Full.map φ = fromBlocks Ak (B.map φ) (C'.map φ) (D.map φ) := by
    conv_lhs => rw [← Matrix.fromBlocks_toBlocks Full]
    rw [Matrix.fromBlocks_map]
  have hdetM : ∀ {n : Type} [Fintype n] [DecidableEq n] (M : Matrix n n ℚ[X]),
      φ M.det = (M.map φ).det := fun M => by
    have := RingHom.map_det φ M
    simpa using this
  have hdetK : φ Full.det = φ A.det *
      (D.map φ - C'.map φ * Ainv * B.map φ).det := by
    have := Matrix.det_fromBlocks₁₁ Ak (B.map φ) (C'.map φ) (D.map φ)
    rw [hdetM, hFull, this, hinv, hdetM A]
  have hTK : D.map φ - C'.map φ * Ainv * B.map φ = (φ g)⁻¹ • (Tscaled g A B C' D N).map φ := by
    have e : (Tscaled g A B C' D N).map φ = φ g • D.map φ - C'.map φ * Nk * B.map φ := by
      ext i j
      simp [Tscaled, Matrix.mul_apply, Nk, Matrix.sub_apply, Matrix.smul_apply]
    rw [e, smul_sub, smul_smul, inv_mul_cancel₀ hgK, one_smul]
    simp only [Ainv, Matrix.mul_smul, Matrix.smul_mul]
  rw [hTK, Matrix.det_smul] at hdetK
  -- polynomial identity: p^s * det Full * g^m = g * det T'
  have hm := Fintype.card κ
  set T := Tscaled g A B C' D N
  set cc : ℚ[X] := C ((p : ℚ) ^ s) with hcc
  have key : cc * Full.det * g ^ Fintype.card κ = g * T.det := by
    apply hφ
    have hd : φ cc * φ A.det = φ g := by
      rw [← map_mul, hdet]
    have hdT : φ T.det = (T.map φ).det := hdetM T
    simp only [map_mul, map_pow]
    rw [hdetK, hdT]
    calc _ = (φ cc * φ A.det) * (T.map φ).det *
          (((φ g)⁻¹) ^ Fintype.card κ * (φ g) ^ Fintype.card κ) := by ring
      _ = φ g * (T.map φ).det := by
        rw [hd, ← mul_pow, inv_mul_cancel₀ hgK, one_pow, mul_one]
  -- norms
  have hT' : gn p T.det ≤ (p : ℝ) ^ (Fintype.card κ * b) :=
    gn_const_pow_det p b T hT
  have hn : gn p (cc * Full.det * g ^ Fintype.card κ) = gn p (g * T.det) := by
    rw [key]
  rw [gn_mul, gn_mul, gn_mul, hg] at hn
  have hpow : gn p (g ^ Fintype.card κ) = 1 := by
    rw [gn_pow, hg, one_pow]
  have hpow' : gn p cc = ((p : ℝ)⁻¹) ^ s := by
    rw [hcc, gn_C]
    have h := map_pow (Rat.AbsoluteValue.padic p) (p : ℚ) s
    simp only [Rat.AbsoluteValue.padic_eq_padicNorm] at h
    have h3 : ((padicNorm p (p : ℚ) : ℚ) : ℝ) = (p : ℝ)⁻¹ := by
      rw [padicNorm.padicNorm_p_of_prime]; push_cast; simp
    rw [← h3, ← h]
  rw [hpow, hpow'] at hn
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  rw [gle_iff_gn]
  have h3 : ((p : ℝ)⁻¹) ^ s * gn p Full.det ≤ (p : ℝ) ^ (Fintype.card κ * b) := by
    linarith
  rw [inv_pow, inv_mul_le_iff₀ (pow_pos hp0 s)] at h3
  calc gn p Full.det ≤ (p : ℝ) ^ s * (p : ℝ) ^ (Fintype.card κ * b) := h3
    _ = (p : ℝ) ^ (Fintype.card κ * b + s) := by rw [← pow_add, add_comm]

end Tcore

end CatalanCore.Arith.Hybrid.LemmaE
