module

public import CatalanCore.Star.Defs
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Algebra.BigOperators.Field

/-!
# Star.Pencil: the bridge `k^gen = c_S^n 𝒦` between the K-space and the pencil

Proof plan (no eigenvectors, no roots):
1. Lagrange: `w_jᵀ u_i = Π_X(j) j^i / ∏_a(θ+a+j)` (`wcol_ubasis`).
2. `Uₓᵀ`-orthogonality, Gram `U_Yᵀ U_X = H_n`, cross `U_Yᵀ N₂ U_X = H_c`.
3. `Π = U_X H_n⁻¹ U_Yᵀ` from the invertibility of `[U_X | W_Y]` (block argument).
4. `Π N₂ U_X = U_X H_n⁻¹ H_c`, hence the Krylov rows are `c_S ν_Sᵀ B^k`.
-/

@[expose] public section

open Finset Matrix Polynomial

namespace CatalanCore.Star

variable {F : Type*} [Field F]

/-! ### Lagrange -/

/-- The polynomial `f_i = Π_b(X) X^i` whose node values are the entries of `ubasis`. -/
noncomputable def fpoly {m : ℕ} (b : Fin m → ℤ) (i : ℕ) : F[X] :=
  (∏ k, (X - C (b k : F))) * X ^ i

lemma eval_fpoly {m : ℕ} (b : Fin m → ℤ) (i : ℕ) (z : F) :
    (fpoly b i).eval z = piB b z * z ^ i := by
  simp [fpoly, piB, eval_prod]

lemma degree_fpoly_lt {m : ℕ} (b : Fin m → ℤ) {i K : ℕ} (h : m + i < K) :
    (fpoly (F := F) b i).degree < K := by
  have : (fpoly (F := F) b i).natDegree ≤ m + i := by
    unfold fpoly
    refine (natDegree_mul_le).trans ?_
    refine add_le_add ?_ (by simp)
    refine (natDegree_prod_le _ _).trans ?_
    refine (Finset.sum_le_sum (g := fun _ => 1) (fun k _ => ?_)).trans (by simp)
    exact (natDegree_sub_le _ _).trans (by simp)
  exact lt_of_le_of_lt (degree_le_natDegree) (by exact_mod_cast lt_of_le_of_lt this h)

/-- Lagrange interpolation at the nodes `ζ_a = -(θ+a)`. -/
lemma lagr_sum {K : ℕ} (θ : F)
    (hdist : ∀ a b : Fin K, ((a : ℕ) : F) = ((b : ℕ) : F) → a = b)
    (f : F[X]) (hf : f.degree < K) (j : F) (hj : ∀ a : Fin K, θ + ((a : ℕ) : F) + j ≠ 0) :
    ∑ a : Fin K, f.eval (-(θ + ((a : ℕ) : F))) / pia K a * (1 / (θ + ((a : ℕ) : F) + j))
      = f.eval j / ∏ a : Fin K, (θ + ((a : ℕ) : F) + j) := by
  classical
  set v : Fin K → F := fun a => -(θ + ((a : ℕ) : F)) with hv
  have hinj : Set.InjOn v (univ : Finset (Fin K)) := by
    intro a _ b _ hab
    apply hdist
    simpa [hv] using hab
  have hfe := Lagrange.eq_interpolate (s := univ) hinj (f := f) (by simpa using hf)
  have hne : ∀ a b : Fin K, a ≠ b → v a - v b ≠ 0 := by
    intro a b hab h
    apply hab; apply hdist
    simp only [hv] at h
    linear_combination -h
  have hpi : ∀ a : Fin K, pia (F := F) K a ≠ 0 := by
    intro a
    unfold pia
    rw [Finset.prod_ne_zero_iff]
    intro b hb
    have := hne a b (Finset.ne_of_mem_erase hb).symm
    intro h
    apply this
    simp only [hv]
    linear_combination h
  have hprod : ∏ a : Fin K, (θ + ((a : ℕ) : F) + j) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun a _ => hj a)
  have hbasis : ∀ a : Fin K, (Lagrange.basis univ v a).eval j
      = (∏ b ∈ univ.erase a, (j - v b)) / pia K a := by
    intro a
    simp only [Lagrange.basis, Lagrange.basisDivisor, eval_prod, eval_mul, eval_C, eval_sub, eval_X]
    rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib, div_eq_mul_inv, mul_comm]
    congr 2
    unfold pia
    refine Finset.prod_congr rfl (fun b _ => ?_)
    simp [hv]; ring
  have hfj : f.eval j = ∑ a : Fin K, f.eval (v a) * ((∏ b ∈ univ.erase a, (j - v b)) / pia K a) := by
    conv_lhs => rw [hfe]
    simp [Lagrange.interpolate_apply, eval_finset_sum, hbasis]
  rw [hfj, Finset.sum_div]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  have hja : j - v a = θ + ((a : ℕ) : F) + j := by simp [hv]; ring
  have hfull : ∏ b : Fin K, (θ + ((b : ℕ) : F) + j) = (θ + ((a : ℕ) : F) + j) * ∏ b ∈ univ.erase a, (j - v b) := by
    rw [← Finset.mul_prod_erase univ (fun b : Fin K => (θ + ((b : ℕ) : F) + j)) (mem_univ a)]
    congr 1
    refine Finset.prod_congr rfl (fun b _ => ?_)
    simp [hv]; ring
  rw [hfull]
  have h1 := hj a
  have h2 : ∏ b ∈ univ.erase a, (j - v b) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro b hb
    have : j - v b = θ + ((b : ℕ) : F) + j := by simp [hv]; ring
    rw [this]; exact hj b
  have := hpi a
  field_simp
  rfl



lemma piB_bX_bY_eq (m S : ℕ) (z : F) : piB (bX m S) z * piB (bY m S) z = PiZ m S z := by
  simp only [piB, PiZ, bX, bY]
  rw [Fin.prod_univ_eq_prod_range (fun i => z - (((S : ℤ) + 2 + 2 * (i : ℕ) : ℤ) : F)) m,
    Fin.prod_univ_eq_prod_range (fun i => z - (((S : ℤ) + 1 + 2 * (i : ℕ) : ℤ) : F)) m]
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.prod_range_succ, Finset.prod_range_succ, show 2 * (m + 1) = 2 * m + 1 + 1 by ring,
      Finset.prod_range_succ, Finset.prod_range_succ]
    have := ih
    push_cast at this ⊢
    calc _ = (∏ x ∈ range m, (z - (S + 2 + 2 * x))) * (∏ x ∈ range m, (z - (S + 1 + 2 * x))) *
          ((z - (S + 2 + 2 * m)) * (z - (S + 1 + 2 * m))) := by ring
      _ = _ := by rw [this]; ring

/-! ### Columns against the kernel basis -/

lemma ubasis_apply {K n m : ℕ} (θ : F) (bx : Fin m → ℤ) (a : Fin K) (i : Fin n) :
    ubasis K n θ bx a i = (fpoly bx i).eval (-(θ + ((a : ℕ) : F))) / pia K a := by
  simp [ubasis, eval_fpoly]

/-- Lagrange: `w_jᵀ u_i = Π_X(j) j^i / ∏_a (θ+a+j)`. -/
lemma wcol_ubasis {K n m : ℕ} (θ : F)
    (hdist : ∀ a b : Fin K, ((a : ℕ) : F) = ((b : ℕ) : F) → a = b) (hmn : m + n ≤ K)
    (bx : Fin m → ℤ) (j : ℤ) (hj : ∀ a : Fin K, θ + ((a : ℕ) : F) + (j : F) ≠ 0) (i : Fin n) :
    ((wcol K θ j) ᵥ* ubasis K n θ bx) i
      = piB bx (j : F) * (j : F) ^ (i : ℕ) / ∏ a : Fin K, (θ + ((a : ℕ) : F) + (j : F)) := by
  have h := lagr_sum θ hdist (fpoly bx i) (degree_fpoly_lt bx (by omega)) (j : F) hj
  rw [eval_fpoly] at h
  rw [← h]
  simp only [vecMul, dotProduct, ubasis_apply, wcol, eval_fpoly]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [mul_comm]

lemma Wt_ubasis_self {K n m : ℕ} (θ : F)
    (hdist : ∀ a b : Fin K, ((a : ℕ) : F) = ((b : ℕ) : F) → a = b) (hmn : m + n ≤ K)
    (bx : Fin m → ℤ) (hbx : ∀ (i : Fin m) (a : Fin K), θ + ((a : ℕ) : F) + (bx i : F) ≠ 0) :
    (Wb K θ bx)ᵀ * ubasis K n θ bx = 0 := by
  ext i' i
  have h := wcol_ubasis θ hdist hmn bx (bx i') (hbx i') i
  have h0 : piB bx ((bx i' : ℤ) : F) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ i') (sub_self _)
  rw [h0] at h
  simp only [zero_mul, zero_div] at h
  simp only [mul_apply, transpose_apply, Wb, of_apply, Matrix.zero_apply]
  rw [← h]
  simp [vecMul, dotProduct, wcol]

lemma Wt_ubasis_cross {K n m : ℕ} (θ : F)
    (hdist : ∀ a b : Fin K, ((a : ℕ) : F) = ((b : ℕ) : F) → a = b) (hmn : m + n ≤ K)
    (bx by' : Fin m → ℤ) (hby : ∀ (i : Fin m) (a : Fin K), θ + ((a : ℕ) : F) + (by' i : F) ≠ 0) :
    (ubasis K n θ by')ᵀ * Wb K θ by' = 0 := by
  have := Wt_ubasis_self θ hdist hmn by' hby
  have h2 := congrArg Matrix.transpose this
  simpa [Matrix.transpose_mul] using h2

/-- Gram: `U_Yᵀ U_X = H_n`. -/
lemma gram_eq {K n m : ℕ} (θ : F) (S : ℕ) (bx by' : Fin m → ℤ)
    (hZ : ∀ z : F, piB bx z * piB by' z = PiZ m S z) :
    (ubasis K n θ by')ᵀ * ubasis K n θ bx = Hn K m S n θ := by
  ext i i'
  simp only [mul_apply, transpose_apply, Hn, of_apply, ubasis, omegaN]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [← hZ]
  ring

/-- Cross term: `U_Yᵀ N₂ U_X = H_c`. -/
lemma cross_eq {K n m : ℕ} (θ : F)
    (hdist : ∀ a b : Fin K, ((a : ℕ) : F) = ((b : ℕ) : F) → a = b) (hmn : m + n ≤ K)
    (S : ℕ) (bx by' : Fin m → ℤ) (J : Finset ℤ)
    (hZ : ∀ z : F, piB bx z * piB by' z = PiZ m S z)
    (hJ : ∀ j ∈ J, ∀ a : Fin K, θ + ((a : ℕ) : F) + (j : F) ≠ 0) :
    (ubasis K n θ by')ᵀ * Nmat K θ J * ubasis K n θ bx = Hc K m S n θ J := by
  ext i i'
  have step : ∀ j ∈ J, ((ubasis K n θ by')ᵀ * Matrix.vecMulVec (wcol K θ j) (wcol K θ j)
      * ubasis K n θ bx) i i' = gammaC K m S θ j * (j : F) ^ ((i : ℕ) + i') := by
    intro j hjJ
    rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul]
    simp only [vecMulVec_apply, mulVec_transpose]
    rw [wcol_ubasis θ hdist hmn by' j (hJ j hjJ) i, wcol_ubasis θ hdist hmn bx j (hJ j hjJ) i',
      gammaC, ← hZ, pow_add]
    ring
  simp only [Nmat, Matrix.mul_sum, Matrix.sum_mul, Matrix.sum_apply, Hc, of_apply]
  exact Finset.sum_congr rfl step

/-! ### The projector -/

lemma proj_abstract {K n m : ℕ} (hK : n + m = K) (U V : Matrix (Fin K) (Fin n) F)
    (WX WY : Matrix (Fin K) (Fin m) F) (H : Matrix (Fin n) (Fin n) F)
    (hH : IsUnit H.det) (hG : IsUnit (WXᵀ * WY).det)
    (h1 : Vᵀ * U = H) (h2 : Vᵀ * WY = 0) (h3 : WXᵀ * U = 0) :
    U * H⁻¹ * Vᵀ + WY * (WXᵀ * WY)⁻¹ * WXᵀ = 1 := by
  set G := WXᵀ * WY with hGdef
  have hPM : fromRows Vᵀ WXᵀ * fromCols U WY = fromBlocks H 0 0 G := by
    rw [fromRows_mul_fromCols, h1, h2, h3]
  have hPMD : fromRows Vᵀ WXᵀ * (fromCols U WY * fromBlocks H⁻¹ 0 0 G⁻¹) = 1 := by
    rw [← Matrix.mul_assoc, hPM, fromBlocks_multiply]
    simp [Matrix.mul_nonsing_inv _ hH, Matrix.mul_nonsing_inv _ hG]
  have hcard : Fintype.card (Fin n ⊕ Fin m) = Fintype.card (Fin K) := by simp [hK]
  have h := (Matrix.mul_eq_one_comm_of_equiv (Fintype.card_eq.mp hcard).some).mp hPMD
  rw [fromCols_mul_fromBlocks, fromCols_mul_fromRows] at h
  simpa using h


/-! ### The bridge -/

/-- Generic bridge: `k(θ;J) = c_S^n 𝒦` for any border data with `Π_{bx} Π_{by} = Π_Z`. -/
theorem kgenCore_eq_pen {K m : ℕ} (θ : F) (J : Finset ℤ) (S : ℕ) (bx by' : Fin m → ℤ)
    (hm : m ≤ K) (hdist : ∀ a b : Fin K, ((a : ℕ) : F) = ((b : ℕ) : F) → a = b)
    (hZ : ∀ z : F, piB bx z * piB by' z = PiZ m S z)
    (hJ : ∀ j ∈ J, ∀ a : Fin K, θ + ((a : ℕ) : F) + (j : F) ≠ 0)
    (hS : ∀ a : Fin K, θ + ((a : ℕ) : F) + (S : F) ≠ 0)
    (hbx : ∀ (i : Fin m) (a : Fin K), θ + ((a : ℕ) : F) + (bx i : F) ≠ 0)
    (hby : ∀ (i : Fin m) (a : Fin K), θ + ((a : ℕ) : F) + (by' i : F) ≠ 0)
    (hG : IsUnit ((Wb K θ bx)ᵀ * Wb K θ by').det)
    (hH : IsUnit (Hn K m S (K - m) θ).det) :
    kgenCore K m θ J (S : ℤ) bx by'
      = (piB bx (S : F) / ∏ a : Fin K, (θ + ((a : ℕ) : F) + (S : F))) ^ (K - m)
        * Kpen K m S θ J := by
  have hmn : m + (K - m) ≤ K := by omega
  have hK : (K - m) + m = K := by omega
  set U := ubasis K (K - m) θ bx with hU
  set V := ubasis K (K - m) θ by' with hV
  have hgram : Vᵀ * U = Hn K m S (K - m) θ := gram_eq θ S bx by' hZ
  have hcross : Vᵀ * Nmat K θ J * U = Hc K m S (K - m) θ J :=
    cross_eq θ hdist hmn S bx by' J hZ hJ
  have h2 : Vᵀ * Wb K θ by' = 0 := Wt_ubasis_cross θ hdist hmn bx by' hby
  have h3 : (Wb K θ bx)ᵀ * U = 0 := Wt_ubasis_self θ hdist hmn bx hbx
  have hproj : projB K θ bx by' = U * (Hn K m S (K - m) θ)⁻¹ * Vᵀ := by
    have := proj_abstract hK U V (Wb K θ bx) (Wb K θ by') _ hH hG hgram h2 h3
    unfold projB
    exact (eq_sub_of_add_eq this).symm
  set B := (Hn K m S (K - m) θ)⁻¹ * Hc K m S (K - m) θ J with hB
  have hstep : projB K θ bx by' * Nmat K θ J * U = U * B := by
    rw [hproj, hB, ← hcross]
    simp only [Matrix.mul_assoc]
  have hpow : ∀ k : ℕ, (projB K θ bx by' * Nmat K θ J) ^ k * U = U * B ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', Matrix.mul_assoc, ih, ← Matrix.mul_assoc, hstep, Matrix.mul_assoc, ← pow_succ']
  have hw : (wcol K θ (S : ℤ)) ᵥ* U
      = (piB bx (S : F) / ∏ a : Fin K, (θ + ((a : ℕ) : F) + (S : F))) • nuS (K - m) (S : F) := by
    funext i
    have := wcol_ubasis θ hdist hmn bx (S : ℤ) (by simpa using hS) i
    simp only [Int.cast_natCast] at this
    rw [hU, this]
    simp [nuS, mul_div_right_comm]
  unfold kgenCore Kpen
  have hrow : ∀ k : Fin (K - m),
      ((wcol K θ (S : ℤ)) ᵥ* ((projB K θ bx by' * Nmat K θ J) ^ (k : ℕ))) ᵥ* U
        = (piB bx (S : F) / ∏ a : Fin K, (θ + ((a : ℕ) : F) + (S : F))) •
          ((nuS (K - m) (S : F)) ᵥ* B ^ (k : ℕ)) := by
    intro k
    rw [Matrix.vecMul_vecMul, hpow, ← Matrix.vecMul_vecMul, hw, Matrix.smul_vecMul]
  have hmat : (Matrix.of fun (k i : Fin (K - m)) =>
      (((wcol K θ (S : ℤ)) ᵥ* ((projB K θ bx by' * Nmat K θ J) ^ (k : ℕ))) ᵥ* U) i)
      = (piB bx (S : F) / ∏ a : Fin K, (θ + ((a : ℕ) : F) + (S : F))) •
        (Matrix.of fun (k i : Fin (K - m)) => ((nuS (K - m) (S : F)) ᵥ* B ^ (k : ℕ)) i) := by
    ext k i
    simp only [Matrix.of_apply, Matrix.smul_apply, hrow k, Pi.smul_apply, smul_eq_mul]
  rw [hmat, Matrix.det_smul, Fintype.card_fin]

/-- Right-hand version: `k_R(θ;J) = k_pen`. -/
theorem kgenR_eq_kpen {K m : ℕ} (θ : F) (J : Finset ℤ) (S : ℕ)
    (hm : m ≤ K) (hdist : ∀ a b : Fin K, ((a : ℕ) : F) = ((b : ℕ) : F) → a = b)
    (hJ : ∀ j ∈ J, ∀ a : Fin K, θ + ((a : ℕ) : F) + (j : F) ≠ 0)
    (hS : ∀ a : Fin K, θ + ((a : ℕ) : F) + (S : F) ≠ 0)
    (hbx : ∀ (i : Fin m) (a : Fin K), θ + ((a : ℕ) : F) + (bX m S i : F) ≠ 0)
    (hby : ∀ (i : Fin m) (a : Fin K), θ + ((a : ℕ) : F) + (bY m S i : F) ≠ 0)
    (hG : IsUnit ((Wb K θ (bX m S))ᵀ * Wb K θ (bY m S)).det)
    (hH : IsUnit (Hn K m S (K - m) θ).det) :
    kgenR K m θ J S = kpen K m S θ J := by
  unfold kgenR kpen cSR
  rw [kgenCore_eq_pen θ J S (bX m S) (bY m S) hm hdist (piB_bX_bY_eq m S) hJ hS hbx hby hG hH]

/-- Left-hand version: `k_L(θ;J) = c_S^L(…)^n 𝒦` (same `𝒦`, other constant). -/
theorem kgenL_eq_pen {K m : ℕ} (θ : F) (J : Finset ℤ) (S : ℕ)
    (hm : m ≤ K) (hdist : ∀ a b : Fin K, ((a : ℕ) : F) = ((b : ℕ) : F) → a = b)
    (hJ : ∀ j ∈ J, ∀ a : Fin K, θ + ((a : ℕ) : F) + (j : F) ≠ 0)
    (hS : ∀ a : Fin K, θ + ((a : ℕ) : F) + (S : F) ≠ 0)
    (hbx : ∀ (i : Fin m) (a : Fin K), θ + ((a : ℕ) : F) + (bX m S i : F) ≠ 0)
    (hby : ∀ (i : Fin m) (a : Fin K), θ + ((a : ℕ) : F) + (bY m S i : F) ≠ 0)
    (hG : IsUnit ((Wb K θ (bX m S))ᵀ * Wb K θ (bY m S)).det)
    (hH : IsUnit (Hn K m S (K - m) θ).det) :
    kgenL K m θ J S = cSL K m S θ ^ (K - m) * Kpen K m S θ J := by
  unfold kgenL cSL
  have hG' : IsUnit ((Wb K θ (bY m S))ᵀ * Wb K θ (bX m S)).det := by
    rw [← Matrix.det_transpose]
    simpa [Matrix.transpose_mul] using hG
  rw [kgenCore_eq_pen θ J S (bY m S) (bX m S) hm hdist
    (fun z => by rw [mul_comm]; exact piB_bX_bY_eq m S z) hJ hS hby hbx hG' hH]


/-- `k_L` and `k_R` differ by the constant `(c_S^L / c_S^R)^n` (cross-multiplied form). -/
theorem kgenL_mul_cSR {K m : ℕ} (θ : F) (J : Finset ℤ) (S : ℕ)
    (hm : m ≤ K) (hdist : ∀ a b : Fin K, ((a : ℕ) : F) = ((b : ℕ) : F) → a = b)
    (hJ : ∀ j ∈ J, ∀ a : Fin K, θ + ((a : ℕ) : F) + (j : F) ≠ 0)
    (hS : ∀ a : Fin K, θ + ((a : ℕ) : F) + (S : F) ≠ 0)
    (hbx : ∀ (i : Fin m) (a : Fin K), θ + ((a : ℕ) : F) + (bX m S i : F) ≠ 0)
    (hby : ∀ (i : Fin m) (a : Fin K), θ + ((a : ℕ) : F) + (bY m S i : F) ≠ 0)
    (hG : IsUnit ((Wb K θ (bX m S))ᵀ * Wb K θ (bY m S)).det)
    (hH : IsUnit (Hn K m S (K - m) θ).det) :
    cSR K m S θ ^ (K - m) * kgenL K m θ J S = cSL K m S θ ^ (K - m) * kgenR K m θ J S := by
  rw [kgenR_eq_kpen θ J S hm hdist hJ hS hbx hby hG hH,
    kgenL_eq_pen θ J S hm hdist hJ hS hbx hby hG hH]
  unfold kpen
  ring


end CatalanCore.Star
