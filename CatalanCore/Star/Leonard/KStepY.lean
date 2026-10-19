module

public import CatalanCore.Star.Leonard.CommN
public import CatalanCore.Star.Leonard.ChainProd

/-!
# The `y`-space operator `T^` (package H5, K-step)

`R = [c_1, …, c_S]`, `E = Π R`, `Cᵀ = Rᵀ Π`.  `T^ = trid S (l(i+2)) (r(i+1)) (d(i+1))` with the residue
coefficients of (CC)/(RC) satisfies `T~ E = E T^` (`Ttil_E`) and `T^ Cᵀ = Cᵀ T~` (`That_Ct`).
-/

@[expose] public section

open Finset Matrix Polynomial

namespace CatalanCore.Star.Leonard

variable {F : Type*} [Field F]

section Coef

variable (m n S : ℕ) (θ : F)

/-- residue coefficients of (CC)/(RC) -/
noncomputable def lc (y : ℕ) : F := -tau (m + n) m S θ (-θ - ((y : ℤ) : F))
noncomputable def dc (y : ℕ) : F :=
  (Dz (m + n) m (S : F) θ (gg (m + n) m S) (cc0 (m + n) m θ (gg (m + n) m S))).eval
    (-((y : ℤ) : F))
noncomputable def rc (y : ℕ) : F :=
  (bP (m + n) m (S : F) θ).eval (-((y : ℤ) : F) - 1) / (Qh m (S : F)).eval (-((y : ℤ) : F) - 1)

end Coef

section Rel

variable [CharZero F] (m n S : ℕ) (hm : 1 ≤ m) (θ : F) (hθ : Gen θ)

include hm hθ in
/-- (CC) for `1 ≤ y ≤ S`, modulo `range W_Y`. -/
lemma cc_proj (y : ℕ) (h1 : 1 ≤ y) (h2 : y ≤ S) :
    Ttil (m + n) m S θ *ᵥ wcol (m + n) θ (y : ℤ) - lc m n S θ y • wcol (m + n) θ ((y - 1 : ℕ) : ℤ)
      - dc m n S θ y • wcol (m + n) θ (y : ℤ) - rc m n S θ y • wcol (m + n) θ ((y + 1 : ℕ) : ℤ) ∈
      CatalanCore.Wsp (Wb (m + n) θ (bY m (S : ℤ))) := by
  obtain ⟨κ, h⟩ := Ttil_col_all (m + n) m S hm θ hθ y h2
  have hcprev : wcol (m + n) θ ((y - 1 : ℕ) : ℤ) = wcol (m + n) θ ((y : ℤ) - 1) := by
    congr 1; omega
  have hcnext : wcol (m + n) θ ((y + 1 : ℕ) : ℤ) = wcol (m + n) θ ((y : ℤ) + 1) := by
    congr 1
  rw [hcprev, hcnext]
  have h' : Ttil (m + n) m S θ *ᵥ wcol (m + n) θ (y : ℤ) =
      lc m n S θ y • wcol (m + n) θ ((y : ℤ) - 1) + dc m n S θ y • wcol (m + n) θ (y : ℤ)
        + rc m n S θ y • wcol (m + n) θ ((y : ℤ) + 1)
        + ∑ j ∈ Finset.range m, κ j • wcol (m + n) θ ((S + 2 * j + 1 : ℕ) : ℤ) := h
  rw [h']
  have : ∀ (A B C D : Fin (m + n) → F), A + B + C + D - A - B - C = D := fun A B C D => by abel
  rw [this]
  exact sum_border_mem m n S θ κ


include hm hθ in
/-- (RC) for `1 ≤ y ≤ S`, paired with `x ∈ ker W_Xᵀ`. -/
lemma rc_dot (y : ℕ) (h1 : 1 ≤ y) (h2 : y ≤ S) (x : Fin (m + n) → F)
    (hx : (Wb (m + n) θ (bX m (S : ℤ)))ᵀ *ᵥ x = 0) :
    ((Ttil (m + n) m S θ)ᵀ *ᵥ wcol (m + n) θ (y : ℤ)) ⬝ᵥ x =
      rc m n S θ (y - 1) * (wcol (m + n) θ ((y - 1 : ℕ) : ℤ) ⬝ᵥ x)
        + dc m n S θ y * (wcol (m + n) θ (y : ℤ) ⬝ᵥ x)
        + lc m n S θ (y + 1) * (wcol (m + n) θ ((y + 1 : ℕ) : ℤ) ⬝ᵥ x) := by
  have hwX : ∀ (j : ℕ) (hj : j < m), wcol (m + n) θ ((S + 2 * j + 2 : ℕ) : ℤ) =
      fun a => Wb (m + n) θ (bX m (S : ℤ)) a ⟨j, hj⟩ := by
    intro j hj; funext a; simp [Wb, bX, wcol]; ring_nf
  have hdotX : ∀ (j : ℕ) (hj : j < m), wcol (m + n) θ ((S + 2 * j + 2 : ℕ) : ℤ) ⬝ᵥ x = 0 := by
    intro j hj
    rw [hwX j hj]
    have := congrFun hx ⟨j, hj⟩
    simpa [Matrix.mulVec, dotProduct] using this
  obtain ⟨κ, h⟩ := TtilT_col_all (m + n) m S hm θ hθ y h2
  have hcprev : wcol (m + n) θ ((y - 1 : ℕ) : ℤ) = wcol (m + n) θ ((y : ℤ) - 1) := by
    congr 1; omega
  have hcnext : wcol (m + n) θ ((y + 1 : ℕ) : ℤ) = wcol (m + n) θ ((y : ℤ) + 1) := by
    congr 1
  have hrr : rc m n S θ (y - 1) = -sigma (m + n) m S θ (-θ - ((y : ℤ) : F)) := by
    have := res_r (m + n) m S hm θ (((y - 1 : ℕ)) : ℤ) (by omega)
    unfold rc; rw [this]
    congr 2
    push_cast [Nat.cast_sub h1]; ring
  have hll : lc m n S θ (y + 1) = -tau (m + n) m S θ (-θ - ((y : ℤ) : F) - 1) := by
    unfold lc; congr 2; push_cast; ring
  have h' : (Ttil (m + n) m S θ)ᵀ *ᵥ wcol (m + n) θ (y : ℤ) =
      (-sigma (m + n) m S θ (-θ - ((y : ℤ) : F))) • wcol (m + n) θ ((y : ℤ) - 1)
        + dc m n S θ y • wcol (m + n) θ (y : ℤ)
        + (-tau (m + n) m S θ (-θ - ((y : ℤ) : F) - 1)) • wcol (m + n) θ ((y : ℤ) + 1)
        + ∑ j ∈ Finset.range m, κ j • wcol (m + n) θ ((S + 2 * j + 2 : ℕ) : ℤ) := h
  have hsum : (∑ j ∈ Finset.range m, κ j • wcol (m + n) θ ((S + 2 * j + 2 : ℕ) : ℤ)) ⬝ᵥ x = 0 := by
    have e : (∑ j ∈ Finset.range m, κ j • wcol (m + n) θ ((S + 2 * j + 2 : ℕ) : ℤ)) ⬝ᵥ x =
        ∑ j ∈ Finset.range m, κ j * (wcol (m + n) θ ((S + 2 * j + 2 : ℕ) : ℤ) ⬝ᵥ x) := by
      simp only [dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul,
        Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    rw [e]
    exact Finset.sum_eq_zero fun j hj => by rw [hdotX j (Finset.mem_range.1 hj), mul_zero]
  rw [hcprev, hcnext, h', add_dotProduct, add_dotProduct, add_dotProduct, hsum, smul_dotProduct,
    smul_dotProduct, smul_dotProduct, hrr, hll]
  simp only [smul_eq_mul, add_zero]

end Rel

section Edge

variable (m n S : ℕ) (θ : F)

lemma lc_one : lc m n S θ 1 = 0 := by
  unfold lc
  have hp : pp (m + n) θ (-θ - (((1 : ℕ) : ℤ) : F)) = 0 := by
    unfold pp; push_cast; ring
  have : tau (m + n) m S θ (-θ - (((1 : ℕ) : ℤ) : F)) = 0 := by
    unfold tau; rw [hp]; simp
  rw [this]; simp

lemma rc_zero (hm : 1 ≤ m) : rc m n S θ 0 = 0 := by
  unfold rc
  have : (bP (m + n) m (S : F) θ).eval (-(((0 : ℕ) : ℤ) : F) - 1) = 0 := by
    have hp : (pz (m + n) θ).eval (-(((0 : ℕ) : ℤ) : F) - 1) = 0 := by
      unfold pz; simp only [eval_mul, eval_lin]; push_cast; ring
    unfold bP
    simp only [eval_neg, eval_mul]
    rw [hp]; ring
  rw [this]; simp

lemma lc_top (hm : 1 ≤ m) : lc m n S θ (S + 1) = 0 := by
  have h0 := tau_border (m + n) m S θ 0 hm
  unfold lc
  have : tau (m + n) m S θ (-θ - (((S + 1 : ℕ) : ℤ) : F)) = 0 := by
    convert h0 using 2; push_cast; ring
  rw [this]; simp

lemma wcol_S1_mem (hm : 1 ≤ m) :
    wcol (m + n) θ ((S + 1 : ℕ) : ℤ) ∈ CatalanCore.Wsp (Wb (m + n) θ (bY m (S : ℤ))) := by
  have e : wcol (m + n) θ ((S + 1 : ℕ) : ℤ) = fun a => Wb (m + n) θ (bY m (S : ℤ)) a ⟨0, hm⟩ := by
    funext a; simp [Wb, bY, wcol]
  rw [e]; exact col_mem_Wsp _ _

end Edge

section Trid

lemma trid_mul_apply {n r : ℕ} (up lo d : ℕ → F) (N : Matrix (Fin n) (Fin r) F) (i : Fin n)
    (b : Fin r) :
    (trid n up lo d * N) i b =
      d i * N i b + (if h : (i : ℕ) + 1 < n then up i * N ⟨i + 1, h⟩ b else 0)
        + (if h : 0 < (i : ℕ) then lo ((i : ℕ) - 1) * N ⟨(i : ℕ) - 1, by omega⟩ b else 0) := by
  have := trid_mulVec n up lo d (fun k => N k b) i
  simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this

lemma mul_trid_apply {n r : ℕ} (up lo d : ℕ → F) (M : Matrix (Fin r) (Fin n) F) (a : Fin r)
    (j : Fin n) :
    (M * trid n up lo d) a j =
      M a j * d j + (if h : 0 < (j : ℕ) then M a ⟨(j : ℕ) - 1, by omega⟩ * up ((j : ℕ) - 1) else 0)
        + (if h : (j : ℕ) + 1 < n then M a ⟨j + 1, h⟩ * lo j else 0) := by
  have h1 : (M * trid n up lo d) a j = ((trid n up lo d)ᵀ * Mᵀ) j a := by
    rw [← Matrix.transpose_mul]; rfl
  rw [h1, trid_transpose, trid_mul_apply]
  simp only [Matrix.transpose_apply]
  by_cases hj : 0 < (j : ℕ) <;> by_cases hj' : (j : ℕ) + 1 < n <;> simp [hj, hj'] <;> ring

end Trid

section TE

variable [CharZero F] (m n S : ℕ) (hm : 1 ≤ m) (θ : F) (hθ : Gen θ)

/-- `R = [c_1, …, c_S]`. -/
noncomputable def Rm : Matrix (Fin (m + n)) (Fin S) F :=
  Matrix.of fun a j => wcol (m + n) θ ((((j : ℕ) + 1 : ℕ)) : ℤ) a

/-- The `S × S` tridiagonal `T^`. -/
noncomputable def That : Matrix (Fin S) (Fin S) F :=
  trid S (fun i => lc m n S θ (i + 2)) (fun i => rc m n S θ (i + 1)) (fun i => dc m n S θ (i + 1))

lemma Em_apply (Pj : Matrix (Fin (m + n)) (Fin (m + n)) F) (a : Fin (m + n)) (j : Fin S) :
    (Pj * Rm m n S θ) a j = (Pj *ᵥ wcol (m + n) θ ((((j : ℕ) + 1 : ℕ)) : ℤ)) a := by
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, Rm]

lemma mul_col_apply {r c k : ℕ} (A : Matrix (Fin r) (Fin c) F) (M : Matrix (Fin c) (Fin k) F)
    (a : Fin r) (j : Fin k) : (A * M) a j = (A *ᵥ fun b => M b j) a := by
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]

include hm hθ in
/-- `T~ Π R = Π R T^`. -/
theorem Ttil_E
    (hΔ : IsUnit ((Wb (m + n) θ (bX m (S : ℤ)))ᵀ * Wb (m + n) θ (bY m (S : ℤ))).det) :
    Ttil (m + n) m S θ * (projB (m + n) θ (bX m (S : ℤ)) (bY m (S : ℤ)) * Rm m n S θ) =
      (projB (m + n) θ (bX m (S : ℤ)) (bY m (S : ℤ)) * Rm m n S θ) * That m n S θ := by
  obtain ⟨hPW, -⟩ := projB_props m n S θ hΔ
  have hcomm := Ttil_comm_projB m n S hm θ hθ hΔ
  set Pj := projB (m + n) θ (bX m (S : ℤ)) (bY m (S : ℤ)) with hPj
  set T := Ttil (m + n) m S θ with hT
  ext a j
  have hy1 : 1 ≤ (j : ℕ) + 1 := by omega
  have hy2 : (j : ℕ) + 1 ≤ S := j.2
  have hcc := cc_proj m n S hm θ hθ ((j : ℕ) + 1) hy1 hy2
  set w := T *ᵥ wcol (m + n) θ (((j : ℕ) + 1 : ℕ) : ℤ)
      - lc m n S θ ((j : ℕ) + 1) • wcol (m + n) θ ((((j : ℕ) + 1 - 1 : ℕ)) : ℤ)
      - dc m n S θ ((j : ℕ) + 1) • wcol (m + n) θ (((j : ℕ) + 1 : ℕ) : ℤ)
      - rc m n S θ ((j : ℕ) + 1) • wcol (m + n) θ ((((j : ℕ) + 1 + 1 : ℕ)) : ℤ) with hw
  have hTc : T *ᵥ wcol (m + n) θ (((j : ℕ) + 1 : ℕ) : ℤ) = w
      + (lc m n S θ ((j : ℕ) + 1) • wcol (m + n) θ ((((j : ℕ) + 1 - 1 : ℕ)) : ℤ)
      + dc m n S θ ((j : ℕ) + 1) • wcol (m + n) θ (((j : ℕ) + 1 : ℕ) : ℤ)
      + rc m n S θ ((j : ℕ) + 1) • wcol (m + n) θ ((((j : ℕ) + 1 + 1 : ℕ)) : ℤ)) := by
    rw [hw]; abel
  have hL : (T * (Pj * Rm m n S θ)) a j = (Pj *ᵥ (T *ᵥ wcol (m + n) θ (((j : ℕ) + 1 : ℕ) : ℤ))) a := by
    rw [← Matrix.mul_assoc, hcomm, Matrix.mul_assoc, mul_col_apply]
    congr 2
  rw [hL, hTc, Matrix.mulVec_add, hPW w hcc, zero_add]
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  unfold That
  rw [mul_trid_apply]
  simp only [Em_apply]
  have e0 : ((j : ℕ) + 1 - 1) = (j : ℕ) := by omega
  simp only [e0]
  by_cases hj : 0 < (j : ℕ)
  · by_cases hj' : (j : ℕ) + 1 < S
    · simp only [hj, hj', dif_pos]
      have e1 : (j : ℕ) - 1 + 1 = (j : ℕ) := by omega
      have e2 : (j : ℕ) - 1 + 2 = (j : ℕ) + 1 := by omega
      simp only [e1, e2]
      ring
    · have hS : (j : ℕ) + 1 = S := by omega
      have hz : Pj *ᵥ wcol (m + n) θ ((((j : ℕ) + 1 + 1 : ℕ)) : ℤ) = 0 := by
        rw [hS]; exact hPW _ (wcol_S1_mem m n S θ hm)
      simp only [hj, hj', dif_pos, dif_neg, not_false_eq_true]
      have e1 : (j : ℕ) - 1 + 1 = (j : ℕ) := by omega
      have e2 : (j : ℕ) - 1 + 2 = (j : ℕ) + 1 := by omega
      simp only [e1, e2, hz, Pi.zero_apply]
      ring
  · have hj0 : (j : ℕ) = 0 := by omega
    have hl : lc m n S θ ((j : ℕ) + 1) = 0 := by rw [hj0]; exact lc_one m n S θ
    by_cases hj' : (j : ℕ) + 1 < S
    · simp only [hj, hj', dif_pos, dif_neg, not_false_eq_true, hl]
      ring
    · have hS : (j : ℕ) + 1 = S := by omega
      have hz : Pj *ᵥ wcol (m + n) θ ((((j : ℕ) + 1 + 1 : ℕ)) : ℤ) = 0 := by
        rw [hS]; exact hPW _ (wcol_S1_mem m n S θ hm)
      simp only [hj, hj', dif_pos, dif_neg, not_false_eq_true, hl, hz, Pi.zero_apply]
      ring

end TE

end CatalanCore.Star.Leonard
