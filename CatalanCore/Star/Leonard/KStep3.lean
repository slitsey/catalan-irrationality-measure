module

public import CatalanCore.Star.Leonard.Darboux
public import CatalanCore.Star.Leonard.CrossRatio
public import CatalanCore.Star.Leonard.ChainProd
public import CatalanCore.Star.Leonard.KStepScalar
public import CatalanCore.Linalg.TelescopeX

/-!
# (K3), (K4): the Darboux map `X` intertwines `Π` and `Ã = Π N_S Π` (package H5)

Instances `(K'+1, m, S)` and `(K', m, S+1)` with `S + m = K'` (`g = 0`).  `WY = Wb (K'+1) (bY S)`,
`WX = Wb (K'+1) (bX S)`; primed `WY' = Wb K' (bY (S+1))` has columns `c'_{S+2j+2}`, `WX'` columns
`c'_{S+3+2j}`.

* `Xm_WY`/`Xm_WXp`: `X WY ⊆ range WY'` and `X^T WX' ⊆ range WX` (border points of (K4a)/(K4b)).
* `Xm_projB` (K3): `X Π = Π' X`.
* `Xm_N_mem` (K4): `X N_S x - N'_{S+1} X x ∈ range WY'` for `WX^T x = 0`.
* `Xm_Atil`: `X Ã = Ã' X`.
-/

@[expose] public section

open Finset Matrix Polynomial

namespace CatalanCore.Star.Leonard

variable {F : Type*} [Field F]

lemma coefA_at_Y (K m S : ℕ) (θ c0 : F) (l : ℕ) (hl : l < m) (y : F) (hy : y = S + 1 + 2 * l) :
    coefA K m (S : F) θ y c0 = 0 := by
  unfold coefA
  have : (PPf ((S : F) - 1) m).eval (-y) = 0 := by
    unfold PPf
    rw [eval_prod]
    refine Finset.prod_eq_zero (Finset.mem_range.2 hl) ?_
    rw [eval_lin, hy]; ring
  rw [this]; simp

lemma coefA_at_X' (K m S : ℕ) (θ c0 : F) (l : ℕ) (hl : l < m) (y : F) (hy : y = S + 3 + 2 * l) :
    coefA K m (S : F) θ y c0 = 0 := by
  unfold coefA
  by_cases h : l + 1 < m
  · have : (PPf ((S : F) - 1) m).eval (-y) = 0 := by
      unfold PPf
      rw [eval_prod]
      refine Finset.prod_eq_zero (Finset.mem_range.2 h) ?_
      rw [eval_lin, hy]; push_cast; ring
    rw [this]; simp
  · have hm : m = l + 1 := by omega
    have : (pK1 K m (S : F) θ).eval (-y) = 0 := by
      unfold pK1
      simp only [eval_mul, eval_lin]
      rw [hy, hm]; push_cast; ring
    rw [this]; simp

/-! ### Border columns -/

lemma colY_mem (K m : ℕ) (s : ℤ) (θ : F) (j : Fin m) :
    wcol K θ (s + 1 + 2 * ((j : ℕ) : ℤ)) ∈ LinearMap.range (Matrix.mulVecLin (Wb K θ (bY m s))) := by
  have : wcol K θ (s + 1 + 2 * ((j : ℕ) : ℤ)) = fun a => Wb K θ (bY m s) a j := by
    funext a; simp [Wb, bY, wcol]
  rw [this]; exact col_mem_Wsp _ j

lemma colX_mem (K m : ℕ) (s : ℤ) (θ : F) (j : Fin m) :
    wcol K θ (s + 2 + 2 * ((j : ℕ) : ℤ)) ∈ LinearMap.range (Matrix.mulVecLin (Wb K θ (bX m s))) := by
  have : wcol K θ (s + 2 + 2 * ((j : ℕ) : ℤ)) = fun a => Wb K θ (bX m s) a j := by
    funext a; simp [Wb, bX, wcol]
  rw [this]; exact col_mem_Wsp _ j

lemma sumY_mem (K' m S : ℕ) (θ : F) (κ : ℕ → F) :
    (∑ j ∈ Finset.range m, κ j • wcol K' θ ((S + 2 * j + 2 : ℕ) : ℤ)) ∈
      LinearMap.range (Matrix.mulVecLin (Wb K' θ (bY m ((S + 1 : ℕ) : ℤ)))) := by
  refine Submodule.sum_mem _ fun j hj => Submodule.smul_mem _ _ ?_
  have hj' := Finset.mem_range.1 hj
  have := colY_mem K' m ((S + 1 : ℕ) : ℤ) θ ⟨j, hj'⟩
  have e : ((S + 1 : ℕ) : ℤ) + 1 + 2 * (((⟨j, hj'⟩ : Fin m) : ℕ) : ℤ) = ((S + 2 * j + 2 : ℕ) : ℤ) := by
    push_cast; ring
  rw [e] at this; exact this

lemma sumX_mem (K m S : ℕ) (θ : F) (κ : ℕ → F) :
    (∑ j ∈ Finset.range m, κ j • wcol K θ ((S + 2 * j + 2 : ℕ) : ℤ)) ∈
      LinearMap.range (Matrix.mulVecLin (Wb K θ (bX m (S : ℤ)))) := by
  refine Submodule.sum_mem _ fun j hj => Submodule.smul_mem _ _ ?_
  have hj' := Finset.mem_range.1 hj
  have := colX_mem K m (S : ℤ) θ ⟨j, hj'⟩
  have e : (S : ℤ) + 2 + 2 * (((⟨j, hj'⟩ : Fin m) : ℕ) : ℤ) = ((S + 2 * j + 2 : ℕ) : ℤ) := by
    push_cast; ring
  rw [e] at this; exact this

section Border

variable [CharZero F] (m n' : ℕ) (hm : 1 ≤ m) (θ : F) (hθ : Gen θ)

include hm hθ in
/-- `X c_t ∈ range WY'` for `t ∈ Y`. -/
lemma Xm_col_Y (i : Fin m) :
    Xm (m + n') m n' θ *ᵥ wcol (m + n' + 1) θ ((n' : ℤ) + 1 + 2 * ((i : ℕ) : ℤ)) ∈
      LinearMap.range (Matrix.mulVecLin (Wb (m + n') θ (bY m ((n' + 1 : ℕ) : ℤ)))) := by
  obtain ⟨ℰ, h⟩ := K4a_col_gen (m + n' + 1) m n' hm θ hθ (by omega)
    ((n' : ℤ) + 1 + 2 * ((i : ℕ) : ℤ)) (fun j hj => by have := i.2; omega)
  have hA := coefA_at_Y (m + n' + 1) m n' θ (cK (m + n' + 1) m n' θ) i i.2
    (((n' : ℤ) + 1 + 2 * ((i : ℕ) : ℤ) : ℤ) : F) (by push_cast; ring)
  have h' : Xm (m + n') m n' θ *ᵥ wcol (m + n' + 1) θ ((n' : ℤ) + 1 + 2 * ((i : ℕ) : ℤ)) =
      coefB θ ((((n' : ℤ) + 1 + 2 * ((i : ℕ) : ℤ) : ℤ) : F)) (cK (m + n' + 1) m n' θ) •
        wcol (m + n') θ (((n' : ℤ) + 1 + 2 * ((i : ℕ) : ℤ)) + 1)
        + ∑ j ∈ Finset.range m, ℰ j • wcol (m + n') θ ((n' + 2 * j + 2 : ℕ) : ℤ) := by
    have := h
    rw [hA, zero_smul, zero_add] at this
    exact this
  rw [h']
  refine Submodule.add_mem _ (Submodule.smul_mem _ _ ?_) (sumY_mem (m + n') m n' θ ℰ)
  have := colY_mem (m + n') m ((n' + 1 : ℕ) : ℤ) θ i
  have e : ((n' + 1 : ℕ) : ℤ) + 1 + 2 * ((i : ℕ) : ℤ) = ((n' : ℤ) + 1 + 2 * ((i : ℕ) : ℤ)) + 1 := by
    push_cast; ring
  rw [e] at this; exact this

include hm hθ in
/-- `X^T c'_{x'} ∈ range WX` for `x' ∈ X'`. -/
lemma Xm_col_X' (i : Fin m) :
    (Xm (m + n') m n' θ)ᵀ *ᵥ wcol (m + n') θ ((n' : ℤ) + 3 + 2 * ((i : ℕ) : ℤ)) ∈
      LinearMap.range (Matrix.mulVecLin (Wb (m + n' + 1) θ (bX m (n' : ℤ)))) := by
  obtain ⟨ℱ, h⟩ := K4b_col_gen (m + n' + 1) m n' hm θ hθ (by omega)
    ((n' : ℤ) + 3 + 2 * ((i : ℕ) : ℤ)) (fun j hj => by have := i.2; omega)
  have hA := coefA_at_X' (m + n' + 1) m n' θ (cK (m + n' + 1) m n' θ) i i.2
    (((n' : ℤ) + 3 + 2 * ((i : ℕ) : ℤ) : ℤ) : F) (by push_cast; ring)
  have h' : (Xm (m + n') m n' θ)ᵀ *ᵥ wcol (m + n') θ ((n' : ℤ) + 3 + 2 * ((i : ℕ) : ℤ)) =
      coefB' θ ((((n' : ℤ) + 3 + 2 * ((i : ℕ) : ℤ) : ℤ) : F)) (cK (m + n' + 1) m n' θ) •
        wcol (m + n' + 1) θ (((n' : ℤ) + 3 + 2 * ((i : ℕ) : ℤ)) - 1)
        + ∑ j ∈ Finset.range m, ℱ j • wcol (m + n' + 1) θ ((n' + 2 * j + 2 : ℕ) : ℤ) := by
    have := h
    rw [hA, zero_smul, zero_add] at this
    exact this
  rw [h']
  refine Submodule.add_mem _ (Submodule.smul_mem _ _ ?_) (sumX_mem (m + n' + 1) m n' θ ℱ)
  have := colX_mem (m + n' + 1) m (n' : ℤ) θ i
  have e : (n' : ℤ) + 2 + 2 * ((i : ℕ) : ℤ) = ((n' : ℤ) + 3 + 2 * ((i : ℕ) : ℤ)) - 1 := by ring
  rw [e] at this; exact this

end Border

lemma exists_mul_eq {r r2 c c2 : ℕ} (M : Matrix (Fin r2) (Fin r) F) (W : Matrix (Fin r) (Fin c) F)
    (W2 : Matrix (Fin r2) (Fin c2) F)
    (h : ∀ i : Fin c, M *ᵥ (fun a => W a i) ∈ LinearMap.range (Matrix.mulVecLin W2)) :
    ∃ B : Matrix (Fin c2) (Fin c) F, M * W = W2 * B := by
  choose b hb using h
  refine ⟨Matrix.of fun r i => b i r, ?_⟩
  ext a i
  have := congrFun (hb i) a
  simp only [Matrix.mulVecLin_apply] at this
  simp only [Matrix.mul_apply, Matrix.of_apply]
  have e1 : ∑ x, M a x * W x i = (M *ᵥ fun a => W a i) a := rfl
  have e2 : ∑ x, W2 a x * b i x = (W2 *ᵥ b i) a := rfl
  rw [e1, e2, this]

section K3

variable [CharZero F] (m n' : ℕ) (hm : 1 ≤ m) (θ : F) (hθ : Gen θ)

lemma colWY (K : ℕ) (s : ℤ) (i : Fin m) :
    (fun a => Wb K θ (bY m s) a i) = wcol K θ (s + 1 + 2 * ((i : ℕ) : ℤ)) := by
  funext a; simp [Wb, bY, wcol]

lemma colWX (K : ℕ) (s : ℤ) (i : Fin m) :
    (fun a => Wb K θ (bX m s) a i) = wcol K θ (s + 2 + 2 * ((i : ℕ) : ℤ)) := by
  funext a; simp [Wb, bX, wcol]

include hm hθ in
lemma Xm_WY : ∃ B : Matrix (Fin m) (Fin m) F,
    Xm (m + n') m n' θ * Wb (m + n' + 1) θ (bY m (n' : ℤ)) =
      Wb (m + n') θ (bY m ((n' + 1 : ℕ) : ℤ)) * B :=
  exists_mul_eq _ _ _ fun i => by
    rw [colWY]; exact Xm_col_Y m n' hm θ hθ i

include hm hθ in
lemma Xm_WXp : ∃ C : Matrix (Fin m) (Fin m) F,
    (Wb (m + n') θ (bX m ((n' + 1 : ℕ) : ℤ)))ᵀ * Xm (m + n') m n' θ =
      C * (Wb (m + n' + 1) θ (bX m (n' : ℤ)))ᵀ := by
  obtain ⟨B, hB⟩ := exists_mul_eq (Xm (m + n') m n' θ)ᵀ (Wb (m + n') θ (bX m ((n' + 1 : ℕ) : ℤ)))
    (Wb (m + n' + 1) θ (bX m (n' : ℤ))) fun i => by
      rw [colWX]
      have := Xm_col_X' m n' hm θ hθ i
      have e : ((n' + 1 : ℕ) : ℤ) + 2 + 2 * ((i : ℕ) : ℤ) = (n' : ℤ) + 3 + 2 * ((i : ℕ) : ℤ) := by
        push_cast; ring
      rw [e]; exact this
  refine ⟨Bᵀ, ?_⟩
  have := congrArg Matrix.transpose hB
  rwa [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose] at this

include hm hθ in
/-- **(K3)** `X Π = Π' X`. -/
theorem Xm_projB
    (hΔ : IsUnit ((Wb (m + n' + 1) θ (bX m (n' : ℤ)))ᵀ * Wb (m + n' + 1) θ (bY m (n' : ℤ))).det)
    (hΔ' : IsUnit ((Wb (m + n') θ (bX m ((n' + 1 : ℕ) : ℤ)))ᵀ *
      Wb (m + n') θ (bY m ((n' + 1 : ℕ) : ℤ))).det) :
    Xm (m + n') m n' θ * projB (m + n' + 1) θ (bX m (n' : ℤ)) (bY m (n' : ℤ)) =
      projB (m + n') θ (bX m ((n' + 1 : ℕ) : ℤ)) (bY m ((n' + 1 : ℕ) : ℤ)) *
        Xm (m + n') m n' θ := by
  obtain ⟨B, hB⟩ := Xm_WY m n' hm θ hθ
  obtain ⟨C, hC⟩ := Xm_WXp m n' hm θ hθ
  set X := Xm (m + n') m n' θ
  set WX := Wb (m + n' + 1) θ (bX m (n' : ℤ))
  set WY := Wb (m + n' + 1) θ (bY m (n' : ℤ))
  set WXp := Wb (m + n') θ (bX m ((n' + 1 : ℕ) : ℤ))
  set WYp := Wb (m + n') θ (bY m ((n' + 1 : ℕ) : ℤ))
  have hGB : (WXpᵀ * WYp) * B = C * (WXᵀ * WY) := by
    calc (WXpᵀ * WYp) * B = WXpᵀ * (WYp * B) := by rw [Matrix.mul_assoc]
      _ = WXpᵀ * (X * WY) := by rw [hB]
      _ = (WXpᵀ * X) * WY := by rw [Matrix.mul_assoc]
      _ = (C * WXᵀ) * WY := by rw [hC]
      _ = C * (WXᵀ * WY) := by rw [Matrix.mul_assoc]
  have hM : (WXᵀ * WY)⁻¹ * (WXᵀ * WY) = 1 := Matrix.nonsing_inv_mul _ hΔ
  have hM' : (WXpᵀ * WYp)⁻¹ * (WXpᵀ * WYp) = 1 := Matrix.nonsing_inv_mul _ hΔ'
  have hMr : (WXᵀ * WY) * (WXᵀ * WY)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hΔ
  have hBG : B * (WXᵀ * WY)⁻¹ = (WXpᵀ * WYp)⁻¹ * C := by
    calc B * (WXᵀ * WY)⁻¹ = (WXpᵀ * WYp)⁻¹ * ((WXpᵀ * WYp) * B) * (WXᵀ * WY)⁻¹ := by
          rw [← Matrix.mul_assoc ((WXpᵀ * WYp)⁻¹), hM', Matrix.one_mul]
      _ = (WXpᵀ * WYp)⁻¹ * (C * (WXᵀ * WY)) * (WXᵀ * WY)⁻¹ := by rw [hGB]
      _ = (WXpᵀ * WYp)⁻¹ * C := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, hMr, Matrix.mul_one]
  unfold projB
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul]
  congr 1
  calc X * (WY * (WXᵀ * WY)⁻¹ * WXᵀ) = (X * WY) * (WXᵀ * WY)⁻¹ * WXᵀ := by
        simp only [Matrix.mul_assoc]
    _ = WYp * (B * (WXᵀ * WY)⁻¹) * WXᵀ := by rw [hB]; simp only [Matrix.mul_assoc]
    _ = WYp * ((WXpᵀ * WYp)⁻¹ * C) * WXᵀ := by rw [hBG]
    _ = WYp * (WXpᵀ * WYp)⁻¹ * (C * WXᵀ) := by simp only [Matrix.mul_assoc]
    _ = WYp * (WXpᵀ * WYp)⁻¹ * (WXpᵀ * X) := by rw [hC]
    _ = (WYp * (WXpᵀ * WYp)⁻¹ * WXpᵀ) * X := by simp only [Matrix.mul_assoc]

end K3

lemma coefA_top (K m S : ℕ) (hm : 1 ≤ m) (θ c0 : F) (y : F) (hy : y = (S : F) + 1) :
    coefA K m (S : F) θ y c0 = 0 := by
  unfold coefA
  have : (PPf ((S : F) - 1) m).eval (-y) = 0 := by
    unfold PPf
    rw [eval_prod]
    refine Finset.prod_eq_zero (Finset.mem_range.2 (by omega : 0 < m)) ?_
    rw [eval_lin, hy]; push_cast; ring
  rw [this]; simp

lemma coefB'_eq_coefB (θ y c0 : F) : coefB' θ y c0 = coefB θ (y - 1) c0 := by
  unfold coefB' coefB
  simp only [eval_mul, eval_lin]
  ring

lemma coefB_zero (θ c0 : F) : coefB θ 0 c0 = 0 := by
  unfold coefB
  simp only [eval_mul, eval_lin]
  ring

lemma WXt_projB [CharZero F] (m n S : ℕ) (θ : F)
    (hΔ : IsUnit ((Wb (m + n) θ (bX m (S : ℤ)))ᵀ * Wb (m + n) θ (bY m (S : ℤ))).det)
    (x : Fin (m + n) → F) :
    (Wb (m + n) θ (bX m (S : ℤ)))ᵀ *ᵥ (projB (m + n) θ (bX m (S : ℤ)) (bY m (S : ℤ)) *ᵥ x) = 0 := by
  have hMr : ((Wb (m + n) θ (bX m (S : ℤ)))ᵀ * Wb (m + n) θ (bY m (S : ℤ))) *
      ((Wb (m + n) θ (bX m (S : ℤ)))ᵀ * Wb (m + n) θ (bY m (S : ℤ)))⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ hΔ
  unfold projB
  rw [Matrix.mulVec_mulVec, Matrix.mul_sub, Matrix.mul_one]
  have : (Wb (m + n) θ (bX m (S : ℤ)))ᵀ * (Wb (m + n) θ (bY m (S : ℤ)) *
      ((Wb (m + n) θ (bX m (S : ℤ)))ᵀ * Wb (m + n) θ (bY m (S : ℤ)))⁻¹ *
      (Wb (m + n) θ (bX m (S : ℤ)))ᵀ) = (Wb (m + n) θ (bX m (S : ℤ)))ᵀ := by
    calc _ = ((Wb (m + n) θ (bX m (S : ℤ)))ᵀ * Wb (m + n) θ (bY m (S : ℤ))) *
          ((Wb (m + n) θ (bX m (S : ℤ)))ᵀ * Wb (m + n) θ (bY m (S : ℤ)))⁻¹ *
          (Wb (m + n) θ (bX m (S : ℤ)))ᵀ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hMr, Matrix.one_mul]
  rw [this, sub_self, Matrix.zero_mulVec]

section K4

variable [CharZero F] (m n' : ℕ) (hm : 1 ≤ m) (θ : F) (hθ : Gen θ)

include hm hθ in
/-- **(K4)** the defect of `X N_S - N'_{S+1} X` lies in `range WY'` on `ker WX^T`. -/
theorem Xm_N_mem (x : Fin (m + n' + 1) → F)
    (hx : (Wb (m + n' + 1) θ (bX m (n' : ℤ)))ᵀ *ᵥ x = 0) :
    Xm (m + n') m n' θ *ᵥ (Nsum (fun y : ℕ => wcol (m + n' + 1) θ (y : ℤ)) n' *ᵥ x) -
        Nsum (fun y : ℕ => wcol (m + n') θ (y : ℤ)) (n' + 1) *ᵥ (Xm (m + n') m n' θ *ᵥ x) ∈
      LinearMap.range (Matrix.mulVecLin (Wb (m + n') θ (bY m ((n' + 1 : ℕ) : ℤ)))) := by
  refine telescopeX' (Xm (m + n') m n' θ) (fun y : ℕ => wcol (m + n' + 1) θ (y : ℤ))
    (fun y : ℕ => wcol (m + n') θ (y : ℤ))
    (fun y : ℕ => coefA (m + n' + 1) m (n' : F) θ (((y : ℕ) : ℤ) : F) (cK (m + n' + 1) m n' θ))
    (fun y : ℕ => coefB θ (((y : ℕ) : ℤ) : F) (cK (m + n' + 1) m n' θ))
    (LinearMap.range (Matrix.mulVecLin (Wb (m + n' + 1) θ (bX m (n' : ℤ)))))
    (LinearMap.range (Matrix.mulVecLin (Wb (m + n') θ (bY m ((n' + 1 : ℕ) : ℤ)))))
    x ?_ ?_ n' ?_ ?_ ?_
  · rintro w ⟨z, rfl⟩
    change (Wb (m + n' + 1) θ (bX m (n' : ℤ)) *ᵥ z) ⬝ᵥ x = 0
    rw [dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hx, zero_dotProduct]
  · simp [coefB_zero]
  · exact coefA_top _ m n' hm θ _ _ (by push_cast; ring)
  · intro y h1 h2
    obtain ⟨ℰ, h⟩ := K4a_col_gen (m + n' + 1) m n' hm θ hθ (by omega) (y : ℤ)
      (fun j hj => by omega)
    have e : wcol (m + n') θ (((y + 1 : ℕ)) : ℤ) = wcol (m + n') θ ((y : ℤ) + 1) := by
      push_cast; rfl
    have h2' : Xm (m + n') m n' θ *ᵥ wcol (m + n' + 1) θ (y : ℤ) =
        coefA (m + n' + 1) m (n' : F) θ (((y : ℕ) : ℤ) : F) (cK (m + n' + 1) m n' θ) •
          wcol (m + n') θ (y : ℤ) +
        coefB θ (((y : ℕ) : ℤ) : F) (cK (m + n' + 1) m n' θ) • wcol (m + n') θ ((y : ℤ) + 1) +
        ∑ j ∈ Finset.range m, ℰ j • wcol (m + n') θ ((n' + 2 * j + 2 : ℕ) : ℤ) := h
    show Xm (m + n') m n' θ *ᵥ wcol (m + n' + 1) θ (y : ℤ) -
        coefA (m + n' + 1) m (n' : F) θ (((y : ℕ) : ℤ) : F) (cK (m + n' + 1) m n' θ) •
          wcol (m + n') θ (y : ℤ) -
        coefB θ (((y : ℕ) : ℤ) : F) (cK (m + n' + 1) m n' θ) • wcol (m + n') θ (((y + 1 : ℕ)) : ℤ)
        ∈ _
    rw [e, h2']
    have : ∀ (A B C : Fin (m + n') → F), A + B + C - A - B = C := fun A B C => by abel
    rw [this]
    exact sumY_mem (m + n') m n' θ ℰ
  · intro y h1 h2
    obtain ⟨ℱ, h⟩ := K4b_col_gen (m + n' + 1) m n' hm θ hθ (by omega) (y : ℤ)
      (fun j hj => by omega)
    have e : wcol (m + n' + 1) θ (((y - 1 : ℕ)) : ℤ) = wcol (m + n' + 1) θ ((y : ℤ) - 1) := by
      rw [Nat.cast_sub h1]; push_cast; rfl
    have hb : coefB θ ((((y - 1 : ℕ) : ℤ)) : F) (cK (m + n' + 1) m n' θ) =
        coefB' θ (((y : ℕ) : ℤ) : F) (cK (m + n' + 1) m n' θ) := by
      rw [coefB'_eq_coefB]; congr 1; rw [Nat.cast_sub h1]; push_cast; ring
    have h2' : (Xm (m + n') m n' θ)ᵀ *ᵥ wcol (m + n') θ (y : ℤ) =
        coefA (m + n' + 1) m (n' : F) θ (((y : ℕ) : ℤ) : F) (cK (m + n' + 1) m n' θ) •
          wcol (m + n' + 1) θ (y : ℤ) +
        coefB' θ (((y : ℕ) : ℤ) : F) (cK (m + n' + 1) m n' θ) • wcol (m + n' + 1) θ ((y : ℤ) - 1) +
        ∑ j ∈ Finset.range m, ℱ j • wcol (m + n' + 1) θ ((n' + 2 * j + 2 : ℕ) : ℤ) := h
    show (Xm (m + n') m n' θ)ᵀ *ᵥ wcol (m + n') θ (y : ℤ) -
        coefA (m + n' + 1) m (n' : F) θ (((y : ℕ) : ℤ) : F) (cK (m + n' + 1) m n' θ) •
          wcol (m + n' + 1) θ (y : ℤ) -
        coefB θ ((((y - 1 : ℕ) : ℤ)) : F) (cK (m + n' + 1) m n' θ) •
          wcol (m + n' + 1) θ (((y - 1 : ℕ)) : ℤ) ∈ _
    rw [e, hb, h2']
    have : ∀ (A B C : Fin (m + n' + 1) → F), A + B + C - A - B = C := fun A B C => by abel
    rw [this]
    exact sumX_mem (m + n' + 1) m n' θ ℱ

end K4

end CatalanCore.Star.Leonard
