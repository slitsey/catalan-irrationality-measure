module

public import CatalanCore.Star.Leonard.HnUnit
public import CatalanCore.Star.Leonard.KStepKS
public import Mathlib.LinearAlgebra.Vandermonde

/-!
# The normalising constant `ν` of `kgen = ν · u(Ã, Π w_S)` in closed form (item 2 of the H7 plan)

`kgen_bridge`: `c_Y^n · det[W_Y|U] · kgen = c_X^n · det Hn · u`.  Block determinants give
* `det[W_X|V] · det[W_Y|U] = Δ · det Hn`   (`[W_X|V]ᵀ [W_Y|U] = diag(Δ, Hn)`),
* `det[W_Y|C] · det[W_X|V] = Δ · det(CᵀV)` (`[W_Y|C]ᵀ [W_X|V]` block triangular, `C = [c_1..c_n]`),

and `CᵀV = diag(Π_Y(j)/N(j)) · Vandermonde(1..n)` (`wcol_ubasis`, Lagrange), `det[W_Y|C]` is a Cauchy
determinant.  Hence `ν = (Π_X(S)/Π_Y(S))^n ∏_j Π_Y(j)/N(j) · V(1..n) / cauFac(Y ∪ {1..n})`, and the
`θ`-dependence is `∏_{a<K}∏_{t∈Y}(θ+a+t)` only.
-/

@[expose] public section

open Finset Matrix

namespace CatalanCore.Star.Leonard

variable {F : Type*} [Field F]

lemma bmat_transpose_mul {m n : ℕ}
    (A C : Matrix (Fin (m + n)) (Fin m) F) (B D : Matrix (Fin (m + n)) (Fin n) F) :
    (CatalanCore.bmat A B)ᵀ * CatalanCore.bmat C D =
    Matrix.reindex finSumFinEquiv finSumFinEquiv
      (Matrix.fromBlocks (Aᵀ * C) (Aᵀ * D) (Bᵀ * C) (Bᵀ * D)) := by
  ext i j
  induction i using Fin.addCases with
  | left i' =>
    induction j using Fin.addCases with
    | left j' => simp [CatalanCore.bmat, Matrix.mul_apply, Matrix.fromBlocks]
    | right j' => simp [CatalanCore.bmat, Matrix.mul_apply, Matrix.fromBlocks]
  | right i' =>
    induction j using Fin.addCases with
    | left j' => simp [CatalanCore.bmat, Matrix.mul_apply, Matrix.fromBlocks]
    | right j' => simp [CatalanCore.bmat, Matrix.mul_apply, Matrix.fromBlocks]

/-- `det[A|B] · det[C|D] = det(AᵀC) · det(BᵀD)` when `AᵀD = 0` (upper-right block zero). -/
lemma det_bmat_mul_zero12 {m n : ℕ}
    (A C : Matrix (Fin (m + n)) (Fin m) F) (B D : Matrix (Fin (m + n)) (Fin n) F)
    (h : Aᵀ * D = 0) :
    (CatalanCore.bmat A B).det * (CatalanCore.bmat C D).det = (Aᵀ * C).det * (Bᵀ * D).det := by
  rw [← Matrix.det_transpose (CatalanCore.bmat A B), ← Matrix.det_mul, bmat_transpose_mul, h,
    Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₁₂]

section Nu

variable [CharZero F] (m n S : ℕ) (θ : F) (hθ : Gen θ)

lemma hdist_nat (K : ℕ) : ∀ a b : Fin K, ((a : ℕ) : F) = ((b : ℕ) : F) → a = b :=
  fun a b h => Fin.ext (Nat.cast_injective h)

include hθ in
lemma Wt_U_X : (Wb (m + n) θ (bX m (S : ℤ)))ᵀ * ubasis (m + n) n θ (bX m (S : ℤ)) = 0 :=
  Wt_ubasis_self θ (hdist_nat _) le_rfl _ (fun i a => gen_add hθ a _)

include hθ in
lemma Vt_WY : (ubasis (m + n) n θ (bY m (S : ℤ)))ᵀ * Wb (m + n) θ (bY m (S : ℤ)) = 0 :=
  Wt_ubasis_cross θ (hdist_nat _) le_rfl (bX m (S : ℤ)) _ (fun i a => gen_add hθ a _)

include hθ in
/-- `det[W_X|V] · det[W_Y|U] = Δ · det Hn` -/
theorem detB :
    (CatalanCore.bmat (Wb (m + n) θ (bX m (S : ℤ))) (ubasis (m + n) n θ (bY m (S : ℤ)))).det *
      (CatalanCore.bmat (Wb (m + n) θ (bY m (S : ℤ))) (ubasis (m + n) n θ (bX m (S : ℤ)))).det =
    ((Wb (m + n) θ (bX m (S : ℤ)))ᵀ * Wb (m + n) θ (bY m (S : ℤ))).det *
      (Hn (m + n) m S n θ).det := by
  rw [det_bmat_mul_zero12 _ _ _ _ (Wt_U_X m n S θ hθ)]
  congr 2
  exact gram_eq θ S (bX m (S : ℤ)) (bY m (S : ℤ)) (piB_bX_bY_eq m S)

include hθ in
/-- `det[W_Y|C] · det[W_X|V] = Δ · det(CᵀV)`, `C = [c_1..c_n]` -/
theorem detC :
    (CatalanCore.bmat (Wb (m + n) θ (bY m (S : ℤ))) (Rm m n n θ)).det *
      (CatalanCore.bmat (Wb (m + n) θ (bX m (S : ℤ))) (ubasis (m + n) n θ (bY m (S : ℤ)))).det =
    ((Wb (m + n) θ (bX m (S : ℤ)))ᵀ * Wb (m + n) θ (bY m (S : ℤ))).det *
      ((Rm m n n θ)ᵀ * ubasis (m + n) n θ (bY m (S : ℤ))).det := by
  have h : (Wb (m + n) θ (bY m (S : ℤ)))ᵀ * ubasis (m + n) n θ (bY m (S : ℤ)) = 0 := by
    have := congrArg Matrix.transpose (Vt_WY m n S θ hθ)
    simpa [Matrix.transpose_mul] using this
  rw [det_bmat_mul_zero12 _ _ _ _ h, ← Matrix.det_transpose ((Wb (m + n) θ (bX m (S : ℤ)))ᵀ *
    Wb (m + n) θ (bY m (S : ℤ))), Matrix.transpose_mul, Matrix.transpose_transpose]

end Nu

section Nu2

variable [CharZero F] (m n S : ℕ) (θ : F) (hθ : Gen θ)

/-- the node `j + 1` of the `j`-th column of `C = [c_1..c_n]` -/
def xv (n : ℕ) (j : Fin n) : F := ((((j : ℕ) + 1 : ℕ) : ℤ) : F)

include hθ in
theorem CtV_eq :
    (Rm m n n θ)ᵀ * ubasis (m + n) n θ (bY m (S : ℤ)) =
      Matrix.diagonal (fun j : Fin n => piB (bY m (S : ℤ)) (xv n j : F) /
          ∏ a : Fin (m + n), (θ + ((a : ℕ) : F) + xv n j)) * Matrix.vandermonde (xv (F := F) n) := by
  ext j i
  rw [Matrix.diagonal_mul]
  have h := wcol_ubasis θ (hdist_nat (m + n)) (le_rfl : m + n ≤ m + n) (bY m (S : ℤ))
    ((((j : ℕ) + 1 : ℕ) : ℤ)) (fun a => gen_add hθ a _) i
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Rm, Matrix.of_apply, Matrix.vandermonde_apply]
  change (wcol (m + n) θ ((((j : ℕ) + 1 : ℕ) : ℤ)) ᵥ* ubasis (m + n) n θ (bY m (S : ℤ))) i = _
  rw [h]; unfold xv; ring

include hθ in
theorem det_CtV :
    ((Rm m n n θ)ᵀ * ubasis (m + n) n θ (bY m (S : ℤ))).det =
      (∏ j : Fin n, piB (bY m (S : ℤ)) (xv n j : F) /
          ∏ a : Fin (m + n), (θ + ((a : ℕ) : F) + xv n j)) *
        ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (xv n j - xv n i : F) := by
  rw [CtV_eq m n S θ hθ, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_vandermonde]

/-- the shifts `Y ∪ {1..n}` of the Cauchy columns `[W_Y | C]` -/
def vshift (m n S : ℕ) : Fin (m + n) → F :=
  Fin.addCases (fun i : Fin m => ((bY m (S : ℤ) i : ℤ) : F)) (fun j : Fin n => xv n j)

include hθ in
theorem det_WYC :
    (CatalanCore.bmat (Wb (m + n) θ (bY m (S : ℤ))) (Rm m n n θ)).det =
      cauFac θ (vshift (F := F) m n S) := by
  have hne : ∀ (a : Fin (m + n)) (j : Fin (m + n)),
      θ + ((a : ℕ) : F) + vshift (F := F) m n S j ≠ 0 := by
    intro a j
    refine Fin.addCases (fun i => ?_) (fun j => ?_) j
    · simp only [vshift, Fin.addCases_left]; exact gen_add hθ a _
    · simp only [vshift, Fin.addCases_right, xv]; exact gen_add hθ a _
  exact CatalanCore.bmat_cauchy_det θ (fun i : Fin m => ((bY m (S : ℤ) i : ℤ) : F))
    (fun j : Fin n => xv n j) hne

lemma vshift_inj (hS : n ≤ S) : Function.Injective (fun j : Fin (m + n) => (
    Fin.addCases (motive := fun _ => ℤ) (fun i : Fin m => bY m (S : ℤ) i) (fun j : Fin n => (((j : ℕ) + 1 : ℕ) : ℤ)) j : ℤ)) := by
  intro i j h
  induction i using Fin.addCases with
  | left i' =>
    induction j using Fin.addCases with
    | left j' =>
      simp only [Fin.addCases_left, bY] at h
      congr 1; apply Fin.ext; omega
    | right j' =>
      simp only [Fin.addCases_left, Fin.addCases_right, bY] at h
      have := j'.2; exfalso; omega
  | right i' =>
    induction j using Fin.addCases with
    | left j' =>
      simp only [Fin.addCases_left, Fin.addCases_right, bY] at h
      have := i'.2; exfalso; omega
    | right j' =>
      simp only [Fin.addCases_right] at h
      congr 1; apply Fin.ext; omega

include hθ in
/-- **`kgen = ν · u(Ã, Π w_S)` with `ν` in closed form** (`n ≤ S`, `Δ` a unit). -/
theorem kgen_eq_nu_mul_u (hS : n ≤ S) (hS1 : 1 ≤ S)
    (hΔ : IsUnit ((Wb (m + n) θ (bX m (S : ℤ)))ᵀ * Wb (m + n) θ (bY m (S : ℤ))).det) :
    kgen (m + n) m S θ =
      ((piB (bX m (S : ℤ)) (S : F) / ∏ a : Fin (m + n), (θ + ((a : ℕ) : F) + (S : F))) /
          (piB (bY m (S : ℤ)) (S : F) / ∏ a : Fin (m + n), (θ + ((a : ℕ) : F) + (S : F)))) ^ n *
        (((∏ j : Fin n, piB (bY m (S : ℤ)) (xv n j : F) /
            ∏ a : Fin (m + n), (θ + ((a : ℕ) : F) + xv n j)) *
          ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (xv n j - xv n i : F)) /
          cauFac θ (vshift (F := F) m n S)) *
      CatalanCore.bkdet (Wb (m + n) θ (bY m (S : ℤ))) (Atil m n S θ)
        (projB (m + n) θ (bX m (S : ℤ)) (bY m (S : ℤ)) *ᵥ wcol (m + n) θ (S : ℤ)) := by
  have hH := Hn_isUnit m n S θ hθ hΔ
  have hbr := kgen_bridge m n S θ hθ hΔ hS1 hH
  have e1 := detB m n S θ hθ
  have e2 := detC m n S θ hθ
  rw [det_CtV m n S θ hθ] at e2
  rw [det_WYC m n S θ hθ] at e2
  have hΔ0 := hΔ.ne_zero
  have hH0 := hH.ne_zero
  have hD1 : (CatalanCore.bmat (Wb (m + n) θ (bY m (S : ℤ)))
      (ubasis (m + n) n θ (bX m (S : ℤ)))).det ≠ 0 := by
    intro h; rw [h, mul_zero] at e1; exact mul_ne_zero hΔ0 hH0 e1.symm
  have hDc : cauFac θ (vshift (F := F) m n S) ≠ 0 := by
    have := cauFac_ne_zero hθ (fun j : Fin (m + n) =>
      (Fin.addCases (fun i : Fin m => bY m (S : ℤ) i) (fun j : Fin n => (((j : ℕ) + 1 : ℕ) : ℤ)) j))
      (vshift_inj m n S hS)
    convert this using 2
    funext j
    refine Fin.addCases (fun i => ?_) (fun j => ?_) j <;> simp [vshift, xv]
  set Hd := (Hn (m + n) m S n θ).det
  set D1 := (CatalanCore.bmat (Wb (m + n) θ (bY m (S : ℤ)))
      (ubasis (m + n) n θ (bX m (S : ℤ)))).det
  set Dc := cauFac θ (vshift (F := F) m n S)
  set Dxv := (CatalanCore.bmat (Wb (m + n) θ (bX m (S : ℤ)))
      (ubasis (m + n) n θ (bY m (S : ℤ)))).det
  set Δd := ((Wb (m + n) θ (bX m (S : ℤ)))ᵀ * Wb (m + n) θ (bY m (S : ℤ))).det
  set Ct := (∏ j : Fin n, piB (bY m (S : ℤ)) (xv n j : F) /
          ∏ a : Fin (m + n), (θ + ((a : ℕ) : F) + xv n j)) *
        ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (xv n j - xv n i : F)
  have hHd : Hd * Dc = Ct * D1 := by
    apply mul_left_cancel₀ hΔ0
    linear_combination (-1 : F) * Dc * e1 + D1 * e2
  have hpY : piB (bY m (S : ℤ)) (S : F) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.2 fun i _ => ?_
    intro h
    have : ((1 + 2 * (i : ℕ) : ℕ) : F) = 0 := by push_cast; simp only [bY] at h; push_cast at h; linear_combination -h
    exact absurd (Nat.cast_eq_zero.1 this) (by omega)
  have hN : (∏ a : Fin (m + n), (θ + ((a : ℕ) : F) + (S : F))) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun a _ => by simpa using gen_add hθ a (S : ℤ)
  have hcY : piB (bY m (S : ℤ)) (S : F) / ∏ a : Fin (m + n), (θ + ((a : ℕ) : F) + (S : F)) ≠ 0 :=
    div_ne_zero hpY hN
  have hHd' : Hd = Ct * D1 / Dc := by rw [eq_div_iff hDc]; exact hHd
  have key : kgen (m + n) m S θ = (piB (bX m (S : ℤ)) (S : F) / ∏ a : Fin (m + n), (θ + ((a : ℕ) : F) + (S : F))) ^ n * Hd *
      CatalanCore.bkdet (Wb (m + n) θ (bY m (S : ℤ))) (Atil m n S θ)
        (projB (m + n) θ (bX m (S : ℤ)) (bY m (S : ℤ)) *ᵥ wcol (m + n) θ (S : ℤ)) /
      ((piB (bY m (S : ℤ)) (S : F) / ∏ a : Fin (m + n), (θ + ((a : ℕ) : F) + (S : F))) ^ n * D1) := by
    rw [eq_div_iff (mul_ne_zero (pow_ne_zero n hcY) hD1)]
    linear_combination hbr
  rw [key, hHd']
  simp only [div_pow]
  have hb : piB (bY m (S : ℤ)) (S : F) ^ n ≠ 0 := pow_ne_zero n hpY
  have hNn : (∏ a : Fin (m + n), (θ + ((a : ℕ) : F) + (S : F))) ^ n ≠ 0 := pow_ne_zero n hN
  field_simp

/-- the constant numerator of `cauFac` -/
def cnum {N : ℕ} (v : Fin N → F) : F :=
  ∏ i : Fin N, ∏ j ∈ Finset.Ioi i, ((((j : ℕ) : F) - ((i : ℕ) : F)) * (v j - v i))

/-- `∏_{a<K} ∏_{t∈Y} (θ + a + t)`: the whole `θ`-dependence of `ν` -/
def YD (m n S : ℕ) (θ : F) : F :=
  ∏ a : Fin (m + n), ∏ i : Fin m, (θ + ((a : ℕ) : F) + ((bY m (S : ℤ) i : ℤ) : F))

/-- the `θ`-free constant of `ν` -/
def Cnu (m n S : ℕ) : F :=
  (piB (bX m (S : ℤ)) (S : F) / piB (bY m (S : ℤ)) (S : F)) ^ n *
    ((∏ j : Fin n, piB (bY m (S : ℤ)) (xv n j : F)) *
      ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (xv n j - xv n i : F)) / cnum (vshift (F := F) m n S)

include hθ in
/-- **`ν = C_ν · ∏_{a<K}∏_{t∈Y}(θ+a+t)`**, `C_ν` independent of `θ`. -/
theorem nu_form (hS : n ≤ S) :
    ((piB (bX m (S : ℤ)) (S : F) / ∏ a : Fin (m + n), (θ + ((a : ℕ) : F) + (S : F))) /
          (piB (bY m (S : ℤ)) (S : F) / ∏ a : Fin (m + n), (θ + ((a : ℕ) : F) + (S : F)))) ^ n *
        (((∏ j : Fin n, piB (bY m (S : ℤ)) (xv n j : F) /
            ∏ a : Fin (m + n), (θ + ((a : ℕ) : F) + xv n j)) *
          ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (xv n j - xv n i : F)) /
          cauFac θ (vshift (F := F) m n S)) = Cnu (F := F) m n S * YD m n S θ := by
  have hDc : cauFac θ (vshift (F := F) m n S) ≠ 0 := by
    have := cauFac_ne_zero hθ (fun j : Fin (m + n) =>
      (Fin.addCases (motive := fun _ => ℤ) (fun i : Fin m => bY m (S : ℤ) i)
        (fun j : Fin n => (((j : ℕ) + 1 : ℕ) : ℤ)) j : ℤ)) (vshift_inj m n S hS)
    convert this using 2
    funext j
    refine Fin.addCases (fun i => ?_) (fun j => ?_) j <;> simp [vshift, xv]
  have hDn : (∏ a : Fin (m + n), ∏ j : Fin (m + n),
      (θ + ((a : ℕ) : F) + vshift (F := F) m n S j)) =
      YD m n S θ * ∏ j : Fin n, ∏ a : Fin (m + n), (θ + ((a : ℕ) : F) + xv n j) := by
    unfold YD
    have e1 : (∏ j : Fin n, ∏ a : Fin (m + n), (θ + ((a : ℕ) : F) + xv n j)) =
        ∏ a : Fin (m + n), ∏ j : Fin n, (θ + ((a : ℕ) : F) + xv n j) := Finset.prod_comm
    rw [e1, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [Fin.prod_univ_add]
    simp [vshift]
  have hcau : cauFac θ (vshift (F := F) m n S) = cnum (vshift (F := F) m n S) /
      (YD m n S θ * ∏ j : Fin n, ∏ a : Fin (m + n), (θ + ((a : ℕ) : F) + xv n j)) := by
    unfold cauFac cnum; rw [← hDn]
  have hY0 : YD m n S θ ≠ 0 := Finset.prod_ne_zero_iff.2 fun a _ => Finset.prod_ne_zero_iff.2 fun i _ => by
    simpa using gen_add hθ a (bY m (S : ℤ) i)
  have hN0 : (∏ j : Fin n, ∏ a : Fin (m + n), (θ + ((a : ℕ) : F) + xv n j)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun j _ => Finset.prod_ne_zero_iff.2 fun a _ => by
      simpa [xv] using gen_add hθ a (((j : ℕ) + 1 : ℕ) : ℤ)
  have hc0 : cnum (vshift (F := F) m n S) ≠ 0 := by
    intro h; rw [hcau, h, zero_div] at hDc; exact hDc rfl
  have hpY : piB (bY m (S : ℤ)) (S : F) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.2 fun i _ => ?_
    intro h
    have : ((1 + 2 * (i : ℕ) : ℕ) : F) = 0 := by push_cast; simp only [bY] at h; push_cast at h; linear_combination -h
    exact absurd (Nat.cast_eq_zero.1 this) (by omega)
  have hN : (∏ a : Fin (m + n), (θ + ((a : ℕ) : F) + (S : F))) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun a _ => by simpa using gen_add hθ a (S : ℤ)
  have hprod : (∏ j : Fin n, piB (bY m (S : ℤ)) (xv n j : F) /
      ∏ a : Fin (m + n), (θ + ((a : ℕ) : F) + xv n j)) =
      (∏ j : Fin n, piB (bY m (S : ℤ)) (xv n j : F)) /
        ∏ j : Fin n, ∏ a : Fin (m + n), (θ + ((a : ℕ) : F) + xv n j) := by rw [Finset.prod_div_distrib]
  rw [hprod, hcau]
  unfold Cnu
  rw [div_div_div_cancel_right₀ hN, div_pow]
  field_simp

end Nu2

end CatalanCore.Star.Leonard
