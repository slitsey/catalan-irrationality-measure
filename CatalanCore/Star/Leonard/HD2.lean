module

public import CatalanCore.Star.Leonard.HD2Abs
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import CatalanCore.Star.Leonard.KStep3
public import CatalanCore.Star.Leonard.KStepKS
public import CatalanCore.Star.Leonard.CauPos
public import CatalanCore.Star.Leonard.GDelta

/-!
# `hD2`: the nondegeneracy `det [W' | X Π R] ≠ 0` of the K-step (positivity route)

Over `ℚ`, `θ > 0`, `Gen θ`.  If `W' s + X Π R t = 0` then `s = 0` (apply `W_X'ᵀ`, `XΠ = Π'X`), and
`y = Π R t ∈ ker X ∩ ker W_Xᵀ`.  By (K4b) `range Xᵀ ⊆ range [R | W_X]`, both of dimension `K-1`, hence
equal (`perp_of_range`), so `Rᵀ y = 0`, i.e. `(Rᵀ Π R) t = 0`; and `det (RᵀΠR) · Δ =
det([R|W_X]ᵀ [R|W_Y]) ≠ 0` (Schur complement + Cauchy–Gram positivity).
-/

@[expose] public section

open Finset Matrix CatalanCore

namespace CatalanCore.Star.Leonard

variable {F : Type*} [Field F]

section XInj

variable [CharZero F] (m n' : ℕ) (hm : 1 ≤ m) (θ : F) (hθ : Gen θ)

include hθ hm in
lemma Xm_diag_ne (i : Fin (m + n')) :
    Dfac (m + n' + 1) m n' θ ((i : ℕ) : F) * mu (m + n' + 1) m n' θ ((i : ℕ) : F) ≠ 0 := by
  have hi := i.2
  have hK : ((m + n' + 1 : ℕ) : F) - 1 - ((i : ℕ) : F) ≠ 0 := by
    have : ((m + n' + 1 : ℕ) : F) - 1 - ((i : ℕ) : F) = ((m + n' - (i : ℕ) : ℕ) : F) := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [this]; exact_mod_cast (by omega : m + n' - (i : ℕ) ≠ 0)
  have hK0 : ((m + n' + 1 : ℕ) : F) - 1 ≠ 0 := by
    have : ((m + n' + 1 : ℕ) : F) - 1 = ((m + n' : ℕ) : F) := by push_cast; ring
    rw [this]; exact_mod_cast (by omega : m + n' ≠ 0)
  unfold Dfac mu
  have hP0 : Pe m n' θ 0 ≠ 0 := by simpa using Pe_ne_zero m n' (genAt_nat hθ 0)
  have hPi : Pe m n' θ ((i : ℕ) : F) ≠ 0 := Pe_ne_zero m n' (genAt_nat hθ i)
  have hQ0 : Qo m n' θ 0 ≠ 0 := by simpa using Qo_ne_zero m n' (genAt_nat hθ 0)
  have hQi : Qo m n' θ ((i : ℕ) : F) ≠ 0 := Qo_ne_zero m n' (genAt_nat hθ i)
  have h1 : θ + (n' : F) + 1 + ((i : ℕ) : F) ≠ 0 := by
    intro h; apply gen_add hθ (i : ℕ) ((n' : ℤ) + 1); push_cast; linear_combination h
  have h2 : θ + (n' : F) + 2 * (m : F) + 1 + ((i : ℕ) : F) ≠ 0 := by
    intro h; apply gen_add hθ (i : ℕ) ((n' : ℤ) + 2 * m + 1); push_cast; linear_combination h
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (div_ne_zero hK0 hK) (div_ne_zero hP0 hPi))
    (div_ne_zero hQi hQ0)) (neg_ne_zero.2 (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hK) h1) h2))

include hθ hm in
lemma Xmt_inj (v : Fin (m + n') → F) (h : (Xm (m + n') m n' θ)ᵀ *ᵥ v = 0) : v = 0 := by
  set Xsq : Matrix (Fin (m + n')) (Fin (m + n')) F :=
    Matrix.of fun i j => Xm (m + n') m n' θ i (Fin.castSucc j) with hXsq
  have htri : Xsq.BlockTriangular id := by
    intro i j hji
    simp only [id] at hji
    simp only [hXsq, Matrix.of_apply, Xm, Fin.val_castSucc]
    rw [if_neg (by omega), if_neg (by omega)]
  have hdet : Xsq.det ≠ 0 := by
    rw [Matrix.det_of_upperTriangular htri]
    refine Finset.prod_ne_zero_iff.2 fun i _ => ?_
    have := Xm_diag_ne m n' hm θ hθ i
    simpa [hXsq, Xm] using this
  have h2 : Xsqᵀ *ᵥ v = 0 := by
    funext j
    have := congrFun h (Fin.castSucc j)
    simpa [Matrix.mulVec, dotProduct, hXsq, Matrix.transpose_apply] using this
  have hdet' : Xsqᵀ.det ≠ 0 := by rwa [Matrix.det_transpose]
  exact Matrix.eq_zero_of_mulVec_eq_zero hdet' h2

end XInj

section CRsec

variable [CharZero F] (m n S : ℕ) (θ : F)

/-- `[R | W_b]`, the Cauchy matrix of the shifts `1, …, S` and the border `b`. -/
noncomputable def CR (b : Fin m → ℤ) : Matrix (Fin (m + n)) (Fin (S + m)) F :=
  Matrix.of fun a j => Fin.addCases (fun j' : Fin S => Rm m n S θ a j')
    (fun i : Fin m => Wb (m + n) θ b a i) j

lemma CR_mulVec (b : Fin m → ℤ) (z : Fin (S + m) → F) :
    CR m n S θ b *ᵥ z = Rm m n S θ *ᵥ (fun j => z (Fin.castAdd m j)) +
      Wb (m + n) θ b *ᵥ (fun i => z (Fin.natAdd S i)) := by
  ext i
  simp [Matrix.mulVec, dotProduct, CR, Fin.sum_univ_add]

/-- the shifts of the columns of `CR` -/
noncomputable def csv (b : Fin m → ℤ) : Fin (S + m) → F :=
  Fin.addCases (fun j' : Fin S => θ + (((j' : ℕ) + 1 : ℕ) : ℤ))
    (fun i : Fin m => θ + ((b i : ℤ) : F))

lemma CR_eq (b : Fin m → ℤ) : CR m n S θ b = Cm (m + n) (csv m S θ b) := by
  ext a j
  induction j using Fin.addCases with
  | left j' => simp [CR, Cm, csv, Rm, wcol]; ring_nf
  | right i => simp [CR, Cm, csv, Wb, wcol]; ring_nf

theorem RPR_mul_Delta
    (hΔ : IsUnit ((Wb (m + n) θ (bX m (S : ℤ)))ᵀ * Wb (m + n) θ (bY m (S : ℤ))).det) :
    ((Rm m n S θ)ᵀ * projB (m + n) θ (bX m (S : ℤ)) (bY m (S : ℤ)) * Rm m n S θ).det *
        ((Wb (m + n) θ (bX m (S : ℤ)))ᵀ * Wb (m + n) θ (bY m (S : ℤ))).det =
      ((CR m n S θ (bX m (S : ℤ)))ᵀ * CR m n S θ (bY m (S : ℤ))).det := by
  set WX := Wb (m + n) θ (bX m (S : ℤ)) with hWX
  set WY := Wb (m + n) θ (bY m (S : ℤ)) with hWY
  set R := Rm m n S θ with hR
  have hblock : (CR m n S θ (bX m (S : ℤ)))ᵀ * CR m n S θ (bY m (S : ℤ)) =
      Matrix.reindex finSumFinEquiv finSumFinEquiv
      (Matrix.fromBlocks (Rᵀ * R) (Rᵀ * WY) (WXᵀ * R) (WXᵀ * WY)) := by
    ext i j
    induction i using Fin.addCases with
    | left i' =>
      induction j using Fin.addCases with
      | left j' => simp [CR, Matrix.mul_apply, Matrix.fromBlocks, hR, hWX, hWY]
      | right j' => simp [CR, Matrix.mul_apply, Matrix.fromBlocks, hR, hWX, hWY]
    | right i' =>
      induction j using Fin.addCases with
      | left j' => simp [CR, Matrix.mul_apply, Matrix.fromBlocks, hR, hWX, hWY]
      | right j' => simp [CR, Matrix.mul_apply, Matrix.fromBlocks, hR, hWX, hWY]
  have : Invertible (WXᵀ * WY) := Matrix.invertibleOfIsUnitDet _ hΔ
  rw [hblock, Matrix.det_reindex_self, Matrix.det_fromBlocks₂₂, mul_comm]
  congr 1
  unfold projB
  rw [Matrix.invOf_eq_nonsing_inv]
  congr 1
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_assoc]
  rfl

end CRsec

section Pos

lemma csv_strictMono (m S : ℕ) (θ : ℚ) (b : Fin m → ℤ) (hb : StrictMono b)
    (hS : ∀ i, (S : ℤ) < b i) : StrictMono (csv m S θ b) := by
  intro i j hij
  induction i using Fin.addCases with
  | left i' =>
    induction j using Fin.addCases with
    | left j' =>
      have : (i' : ℕ) < j' := hij
      simp only [csv, Fin.addCases_left]
      have : ((((i' : ℕ) + 1 : ℕ) : ℤ) : ℚ) < ((((j' : ℕ) + 1 : ℕ) : ℤ) : ℚ) := by exact_mod_cast (by omega)
      linarith
    | right j' =>
      simp only [csv, Fin.addCases_left, Fin.addCases_right]
      have h1 := hS j'
      have h2 : (((i' : ℕ) : ℤ) + 1) ≤ (S : ℤ) := by have := i'.2; omega
      have : ((((i' : ℕ) + 1 : ℕ) : ℤ) : ℚ) < ((b j' : ℤ) : ℚ) := by exact_mod_cast (by push_cast; omega)
      linarith
  | right i' =>
    induction j using Fin.addCases with
    | left j' =>
      exfalso
      have := hij
      simp [Fin.lt_def] at this
      have := j'.2; omega
    | right j' =>
      have : (i' : ℕ) < j' := by have h : S + (i' : ℕ) < S + (j' : ℕ) := hij; omega
      simp only [csv, Fin.addCases_right]
      have : ((b i' : ℤ) : ℚ) < ((b j' : ℤ) : ℚ) := by exact_mod_cast hb (by exact_mod_cast this)
      linarith

lemma csv_pos (m n S : ℕ) (θ : ℚ) (hθ : 0 < θ) (b : Fin m → ℤ) (hb : ∀ i, 0 ≤ b i)
    (a : Fin (m + n)) (j : Fin (S + m)) : 0 < ((a : ℕ) : ℚ) + csv m S θ b j := by
  induction j using Fin.addCases with
  | left j' =>
    simp only [csv, Fin.addCases_left]
    have : (0 : ℚ) ≤ ((a : ℕ) : ℚ) := Nat.cast_nonneg _
    have : (0 : ℚ) ≤ ((((j' : ℕ) + 1 : ℕ) : ℤ) : ℚ) := by exact_mod_cast (Int.natCast_nonneg _)
    linarith
  | right i =>
    simp only [csv, Fin.addCases_right]
    have : (0 : ℚ) ≤ ((a : ℕ) : ℚ) := Nat.cast_nonneg _
    have : (0 : ℚ) ≤ ((b i : ℤ) : ℚ) := by exact_mod_cast hb i
    linarith

/-- Gram determinants of the Cauchy matrices `[R | W_b]` are nonzero (θ > 0). -/
theorem CR_gram_ne (m n S : ℕ) (hSn : S ≤ n) (θ : ℚ) (hθ : 0 < θ)
    (bx by' : Fin m → ℤ) (hbx : StrictMono bx) (hby : StrictMono by')
    (hsx : ∀ i, (S : ℤ) < bx i) (hsy : ∀ i, (S : ℤ) < by' i) :
    ((CR m n S θ bx)ᵀ * CR m n S θ by').det ≠ 0 := by
  rw [CR_eq, CR_eq]
  refine det_CmCm_ne_zero_pos (by omega) _ _
    (csv_pos m n S θ hθ bx (fun i => by have := hsx i; omega))
    (csv_pos m n S θ hθ by' (fun i => by have := hsy i; omega))
    (Vprod_ne_zero_of_injective _ (csv_strictMono m S θ bx hbx hsx))
    (Vprod_ne_zero_of_injective _ (csv_strictMono m S θ by' hby hsy))

lemma bX_strictMono (m : ℕ) (S : ℤ) : StrictMono (bX m S) := by
  intro i j h
  have : (i : ℕ) < j := h
  simp only [bX]; omega

lemma bY_strictMono (m : ℕ) (S : ℤ) : StrictMono (bY m S) := by
  intro i j h
  have : (i : ℕ) < j := h
  simp only [bY]; omega

/-- `Δ = det (W_Xᵀ W_Y) ≠ 0` for `θ > 0` (rational). -/
theorem Delta_ne_pos (K m S : ℕ) (hmK : m ≤ K) (θ : ℚ) (hθ : 0 < θ) :
    ((Wb K θ (bX m (S : ℤ)))ᵀ * Wb K θ (bY m (S : ℤ))).det ≠ 0 := by
  have e : ∀ b : Fin m → ℤ, Wb K θ b = Cm K (fun i => θ + ((b i : ℤ) : ℚ)) := by
    intro b; ext a i; simp [Wb, Cm, wcol]; ring_nf
  rw [e, e]
  have hp : ∀ (b : Fin m → ℤ), (∀ i, 0 ≤ b i) → ∀ (a : Fin K) (i : Fin m),
      0 < ((a : ℕ) : ℚ) + (θ + ((b i : ℤ) : ℚ)) := by
    intro b hb a i
    have : (0 : ℚ) ≤ ((a : ℕ) : ℚ) := Nat.cast_nonneg _
    have : (0 : ℚ) ≤ ((b i : ℤ) : ℚ) := by exact_mod_cast hb i
    linarith
  refine det_CmCm_ne_zero_pos hmK _ _ (hp _ (fun i => by simp [bX]; omega))
    (hp _ (fun i => by simp [bY]; omega)) ?_ ?_
  · refine Vprod_ne_zero_of_injective _ fun i j h => ?_
    have h1 : ((bX m (S : ℤ) i : ℤ) : ℚ) < ((bX m (S : ℤ) j : ℤ) : ℚ) := by exact_mod_cast bX_strictMono m (S : ℤ) h
    show _ < _; linarith
  · refine Vprod_ne_zero_of_injective _ fun i j h => ?_
    have h1 : ((bY m (S : ℤ) i : ℤ) : ℚ) < ((bY m (S : ℤ) j : ℤ) : ℚ) := by exact_mod_cast bY_strictMono m (S : ℤ) h
    show _ < _; linarith

end Pos

section Main

lemma mulVec_zero' {F : Type*} [Field F] {r c : ℕ} (M : Matrix (Fin r) (Fin c) F) :
    M *ᵥ (fun _ => (0 : F)) = 0 := Matrix.mulVec_zero M

variable [CharZero F] (m n' : ℕ) (hm : 1 ≤ m) (θ : F) (hθ : Gen θ)

/-- the matrix `N = [R | W_X]` of the first instance `(m + (n'+1), m, S = n')` -/
noncomputable abbrev NN : Matrix (Fin (m + (n' + 1))) (Fin (n' + m)) F :=
  CR m (n' + 1) n' θ (bX m (n' : ℤ))

lemma range_WX_le :
    LinearMap.range (Matrix.mulVecLin (Wb (m + n' + 1) θ (bX m (n' : ℤ)))) ≤
      LinearMap.range (Matrix.mulVecLin (NN m n' θ)) := by
  rintro w ⟨a, rfl⟩
  refine ⟨Fin.addCases (fun _ => 0) a, ?_⟩
  rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, NN, CR_mulVec]
  simp only [Fin.addCases_left, Fin.addCases_right]
  rw [mulVec_zero', zero_add]
  rfl

lemma wcol_mem_NN (t : ℕ) (h1 : 1 ≤ t) (h2 : t ≤ n') :
    wcol (m + n' + 1) θ (t : ℤ) ∈ LinearMap.range (Matrix.mulVecLin (NN m n' θ)) := by
  refine ⟨Fin.addCases (Pi.single (⟨t - 1, by omega⟩ : Fin n') 1) (fun _ => 0), ?_⟩
  ext a
  simp only [Matrix.mulVecLin_apply, NN, CR_mulVec, Fin.addCases_left, Fin.addCases_right]
  rw [mulVec_zero', add_zero]
  have e1 : (fun j : Fin n' => (Pi.single (⟨t - 1, by omega⟩ : Fin n') (1 : F) : Fin n' → F) j) =
      Pi.single (⟨t - 1, by omega⟩ : Fin n') 1 := rfl
  rw [e1, Matrix.mulVec_single_one]
  have : t - 1 + 1 = t := by omega
  have e : ((t - 1 : ℕ) : F) + 1 = (t : F) := by exact_mod_cast this
  simp [Rm, wcol, e]

include hm hθ in
lemma hcolX (j : Fin (n' + m)) :
    (Xm (m + n') m n' θ)ᵀ *ᵥ (fun i => (CR m n' n' θ (bX m ((n' + 1 : ℕ) : ℤ))) i j) ∈
      LinearMap.range (Matrix.mulVecLin (NN m n' θ)) := by
  induction j using Fin.addCases with
  | left j' =>
    have hcolj : (fun i => (CR m n' n' θ (bX m ((n' + 1 : ℕ) : ℤ))) i (Fin.castAdd m j')) =
        wcol (m + n') θ ((((j' : ℕ) + 1 : ℕ)) : ℤ) := by
      funext i; simp [CR, Rm]
    rw [hcolj]
    have hj := j'.2
    obtain ⟨ℱ, h⟩ := K4b_col_gen (m + n' + 1) m n' hm θ hθ (by omega)
      ((((j' : ℕ) + 1 : ℕ)) : ℤ) (fun l hl => by omega)
    have h' : (Xm (m + n') m n' θ)ᵀ *ᵥ wcol (m + n') θ ((((j' : ℕ) + 1 : ℕ)) : ℤ) =
        coefA (m + n' + 1) m (n' : F) θ (((((j' : ℕ) + 1 : ℕ)) : ℤ) : F) (cK (m + n' + 1) m n' θ) •
          wcol (m + n' + 1) θ ((((j' : ℕ) + 1 : ℕ)) : ℤ)
        + coefB' θ (((((j' : ℕ) + 1 : ℕ)) : ℤ) : F) (cK (m + n' + 1) m n' θ) •
          wcol (m + n' + 1) θ (((((j' : ℕ) + 1 : ℕ)) : ℤ) - 1)
        + ∑ l ∈ Finset.range m, ℱ l • wcol (m + n' + 1) θ ((n' + 2 * l + 2 : ℕ) : ℤ) := h
    rw [h']
    refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.smul_mem _ _ ?_) ?_)
      (range_WX_le m n' θ (sumX_mem (m + n' + 1) m n' θ ℱ))
    · exact wcol_mem_NN m n' θ _ (by omega) (by omega)
    · rcases Nat.eq_zero_or_pos (j' : ℕ) with h0 | h0
      · have : coefB' θ (((((j' : ℕ) + 1 : ℕ)) : ℤ) : F) (cK (m + n' + 1) m n' θ) = 0 := by
          rw [coefB'_eq_coefB, h0]
          have : (((((0 : ℕ) + 1 : ℕ)) : ℤ) : F) - 1 = 0 := by simp
          rw [this]; exact coefB_zero _ _
        rw [this, zero_smul]; exact Submodule.zero_mem _
      · refine Submodule.smul_mem _ _ ?_
        have e : ((((j' : ℕ) + 1 : ℕ)) : ℤ) - 1 = (((j' : ℕ) : ℕ) : ℤ) := by push_cast; ring
        rw [e]
        exact wcol_mem_NN m n' θ _ (by omega) (by omega)
  | right i =>
    have hcolj : (fun a => (CR m n' n' θ (bX m ((n' + 1 : ℕ) : ℤ))) a (Fin.natAdd n' i)) =
        wcol (m + n') θ ((n' : ℤ) + 3 + 2 * ((i : ℕ) : ℤ)) := by
      funext a; simp only [CR, Matrix.of_apply, Fin.addCases_right, Wb, bX, wcol]
      congr 3
    rw [hcolj]
    exact range_WX_le m n' θ (Xm_col_X' m n' hm θ hθ i)

end Main

section Final

variable (m n' : ℕ) (hm : 1 ≤ m) (θ : ℚ) (hθ0 : 0 < θ) (hθ : Gen θ)

include hθ0 in
lemma NN_inj (a : Fin (n' + m) → ℚ) (h : NN m n' θ *ᵥ a = 0) : a = 0 := by
  have hdet := CR_gram_ne m (n' + 1) n' (by omega) θ hθ0 (bX m (n' : ℤ)) (bY m (n' : ℤ))
    (bX_strictMono m _) (bY_strictMono m _) (fun i => by simp [bX]; omega)
    (fun i => by simp [bY]; omega)
  have hdet' : ((CR m (n' + 1) n' θ (bY m (n' : ℤ)))ᵀ * NN m n' θ).det ≠ 0 := by
    have := Matrix.det_transpose ((CR m (n' + 1) n' θ (bX m (n' : ℤ)))ᵀ *
      CR m (n' + 1) n' θ (bY m (n' : ℤ)))
    rw [Matrix.transpose_mul, Matrix.transpose_transpose] at this
    rw [NN, this]; exact hdet
  refine Matrix.eq_zero_of_mulVec_eq_zero hdet' ?_
  rw [← Matrix.mulVec_mulVec, h, Matrix.mulVec_zero]

include hθ0 in
lemma C_span :
    Submodule.span ℚ (Set.range fun j : Fin (n' + m) =>
      fun i => (CR m n' n' θ (bX m ((n' + 1 : ℕ) : ℤ))) i j) = ⊤ := by
  set C := CR m n' n' θ (bX m ((n' + 1 : ℕ) : ℤ)) with hC
  have hdet := CR_gram_ne m n' n' le_rfl θ hθ0 (bX m ((n' + 1 : ℕ) : ℤ)) (bX m ((n' + 1 : ℕ) : ℤ))
    (bX_strictMono m _) (bX_strictMono m _) (fun i => by simp [bX]; omega)
    (fun i => by simp [bX]; omega)
  have hli : LinearIndependent ℚ (fun j : Fin (n' + m) => fun i => C i j) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have : C *ᵥ g = 0 := by
      funext i
      have := congrFun hg i
      simpa [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm] using this
    have h2 : (Cᵀ * C) *ᵥ g = 0 := by rw [← Matrix.mulVec_mulVec, this, Matrix.mulVec_zero]
    exact fun i => congrFun (Matrix.eq_zero_of_mulVec_eq_zero hdet h2) i
  refine LinearIndependent.span_eq_top_of_card_eq_finrank' hli ?_
  simp [Fintype.card_fin, Module.finrank_fin_fun]; omega

include hθ0 in
lemma RPR_det_ne
    (hΔ : IsUnit ((Wb (m + (n' + 1)) θ (bX m (n' : ℤ)))ᵀ * Wb (m + (n' + 1)) θ (bY m (n' : ℤ))).det) :
    ((Rm m (n' + 1) n' θ)ᵀ * projB (m + (n' + 1)) θ (bX m (n' : ℤ)) (bY m (n' : ℤ)) *
      Rm m (n' + 1) n' θ).det ≠ 0 := by
  intro h0
  have h := RPR_mul_Delta m (n' + 1) n' θ hΔ
  rw [h0, zero_mul] at h
  exact CR_gram_ne m (n' + 1) n' (by omega) θ hθ0 _ _ (bX_strictMono m _) (bY_strictMono m _)
    (fun i => by simp [bX]; omega) (fun i => by simp [bY]; omega) h.symm

lemma NNt_castAdd (y : Fin (m + (n' + 1)) → ℚ) (j : Fin n') :
    ((NN m n' θ)ᵀ *ᵥ y) (Fin.castAdd m j) = ((Rm m (n' + 1) n' θ)ᵀ *ᵥ y) j := by
  simp only [Matrix.mulVec, dotProduct, NN, CR, Matrix.transpose_apply, Matrix.of_apply,
    Fin.addCases_left]

include hm hθ0 hθ in
/-- **`hD2`** (over `ℚ`, `θ > 0`): the nondegeneracy of the Darboux K-step. -/
theorem hD2_rat :
    (CatalanCore.bmat (Wb (m + n') θ (bY m ((n' + 1 : ℕ) : ℤ)))
      (Xm (m + n') m n' θ * (projB (m + (n' + 1)) θ (bX m (n' : ℤ)) (bY m (n' : ℤ)) *
        Rm m (n' + 1) n' θ))).det ≠ 0 := by
  have hΔ : IsUnit ((Wb (m + (n' + 1)) θ (bX m (n' : ℤ)))ᵀ *
      Wb (m + (n' + 1)) θ (bY m (n' : ℤ))).det :=
    isUnit_iff_ne_zero.2 (Delta_ne_pos _ m n' (by omega) θ hθ0)
  have hΔ' : IsUnit ((Wb (m + n') θ (bX m ((n' + 1 : ℕ) : ℤ)))ᵀ *
      Wb (m + n') θ (bY m ((n' + 1 : ℕ) : ℤ))).det :=
    isUnit_iff_ne_zero.2 (Delta_ne_pos _ m (n' + 1) (by omega) θ hθ0)
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  rw [CatalanCore.bmat_mulVec] at hv
  set s : Fin m → ℚ := fun i => v (Fin.castAdd n' i) with hs
  set t : Fin n' → ℚ := fun j => v (Fin.natAdd m j) with ht
  set Pj := projB (m + (n' + 1)) θ (bX m (n' : ℤ)) (bY m (n' : ℤ)) with hPj
  set R := Rm m (n' + 1) n' θ with hR
  set X := Xm (m + n') m n' θ with hX
  have h1 : (Wb (m + n') θ (bX m ((n' + 1 : ℕ) : ℤ)))ᵀ *ᵥ
      (Wb (m + n') θ (bY m ((n' + 1 : ℕ) : ℤ)) *ᵥ s + (X * (Pj * R)) *ᵥ t) = 0 := by
    rw [hv, Matrix.mulVec_zero]
  have h2 : (Wb (m + n') θ (bX m ((n' + 1 : ℕ) : ℤ)))ᵀ *ᵥ ((X * (Pj * R)) *ᵥ t) = 0 := by
    have e : X * (Pj * R) = projB (m + n') θ (bX m ((n' + 1 : ℕ) : ℤ)) (bY m ((n' + 1 : ℕ) : ℤ)) *
        (X * R) := by
      have hXP := Xm_projB m n' hm θ hθ hΔ hΔ'
      rw [← Matrix.mul_assoc]
      exact (congrArg (fun M => M * R) hXP).trans (Matrix.mul_assoc _ _ _)
    rw [e, ← Matrix.mulVec_mulVec]
    exact WXt_projB m n' (n' + 1) θ hΔ' _
  rw [Matrix.mulVec_add, h2, add_zero, Matrix.mulVec_mulVec] at h1
  have hs0 : s = 0 := Matrix.eq_zero_of_mulVec_eq_zero hΔ'.ne_zero h1
  rw [hs0, Matrix.mulVec_zero, zero_add] at hv
  have hy : X *ᵥ (Pj *ᵥ (R *ᵥ t)) = 0 := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]; exact hv
  have hNt := perp_of_range (q := m + n' + 1) X (NN m n' θ) (CR m n' n' θ (bX m ((n' + 1 : ℕ) : ℤ)))
    (by simp; omega) (Xmt_inj m n' hm θ hθ) (NN_inj m n' θ hθ0) (C_span m n' θ hθ0)
    (hcolX m n' hm θ hθ) _ hy
  have hRt : Rᵀ *ᵥ (Pj *ᵥ (R *ᵥ t)) = 0 := by
    funext j
    have := congrFun hNt (Fin.castAdd m j)
    rw [NNt_castAdd] at this
    exact this
  have ht0 : t = 0 := by
    refine Matrix.eq_zero_of_mulVec_eq_zero (RPR_det_ne m n' θ hθ0 hΔ) ?_
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]; exact hRt
  apply hv0
  funext i
  induction i using Fin.addCases with
  | left i => simpa [hs] using congrFun hs0 i
  | right j => simpa [ht] using congrFun ht0 j

end Final

end CatalanCore.Star.Leonard
