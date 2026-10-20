module

public import CatalanFrames.LambdaHybrid.NV.Mod3

@[expose] public section

open Matrix
namespace CatalanFrames.LambdaHybrid.NV
variable {F : Type*} [Field F] {A A' c m : Type*}
  [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A']
  [Fintype c] [DecidableEq c] [Fintype m] [DecidableEq m]

/-- Keep every high/common and border coordinate, restricting only low nodes. -/
def lowKeep (f : A' → A) : (A' ⊕ c) ⊕ m → (A ⊕ c) ⊕ m :=
  Sum.map (Sum.map f id) id

theorem Zmat_submatrix_low (f : A' → A) (hf : Function.Injective f)
    (x t d : F) (Aa : Matrix A A F) (Wc : Matrix A c F) (Wx Wy : Matrix A m F) :
    (Zmat x t d Aa Wc Wx Wy).submatrix (lowKeep f) (lowKeep f) =
      Zmat x t d (Aa.submatrix f f) (Wc.submatrix f id)
        (Wx.submatrix f id) (Wy.submatrix f id) := by
  ext ((a | j) | i) ((b | k) | l) <;>
    simp [Zmat, lowKeep, Matrix.submatrix, Matrix.one_apply, hf.eq_iff]

theorem borderedN_submatrix_low (f : A' → A) (hf : Function.Injective f)
    (z : F) (N : Matrix A A F) (Wx Wy : Matrix A m F) :
    (borderedN z N Wx Wy).submatrix (Sum.map f id) (Sum.map f id) =
      borderedN z (N.submatrix f f) (Wx.submatrix f id) (Wy.submatrix f id) := by
  ext (a | i) (b | j) <;>
    simp [borderedN, Matrix.submatrix, Matrix.one_apply, hf.eq_iff]

/-- The Schur identity commutes with arbitrary principal restriction of the low block. -/
theorem det_ZmatN_submatrix_low (f : A' → A) (hf : Function.Injective f)
    (x t d κ h : F) (ht : t ≠ 0) (hd : d ≠ 0) (hκ : κ ≠ 0) (htk : t * t = -d * κ)
    (Aa : Matrix A A F) (Wc : Matrix A c F) (Wx Wy : Matrix A m F) (N : Matrix A A F)
    (hA : Aa = κ • (Wc * Wc.transpose + N + Wx * Wx.transpose +
      Wy * Wy.transpose + h • 1)) :
    ((Zmat x t d Aa Wc Wx Wy).submatrix (lowKeep f) (lowKeep f)).det =
      d ^ (Fintype.card c + Fintype.card m) * (-κ) ^ Fintype.card A' *
        ((borderedN (h - x / κ) N Wx Wy).submatrix
          (Sum.map f id) (Sum.map f id)).det := by
  rw [Zmat_submatrix_low f hf, borderedN_submatrix_low f hf]
  apply det_ZmatN x t d κ h ht hd hκ htk
  ext a b
  have he := congrFun (congrFun hA (f a)) (f b)
  simpa [Matrix.submatrix, Matrix.mul_apply, Matrix.one_apply,
    Matrix.smul_apply, hf.eq_iff] using he

section CommonIndex
open CatalanCore CatalanCore.Rect
variable {K : ℕ} (G : Geometry) (hlow : ∀ n, n < K → n ∈ G.C)

def commonKeep (f : A' → Fin K) : A' ⊕ HiC K G → G.C :=
  fun i => Equiv.sumCompl (fun b : G.C => (b : ℕ) < K)
    (Sum.map (fun a => eLow K G hlow (f a)) id i)

theorem commonKeep_injective (f : A' → Fin K) (hf : Function.Injective f) :
    Function.Injective (commonKeep G hlow f) :=
  (Equiv.sumCompl (fun b : G.C => (b : ℕ) < K)).injective.comp
    (Sum.map_injective.mpr ⟨(eLow K G hlow).injective.comp hf, Function.injective_id⟩)

theorem eIdx_lowKeep (f : A' → Fin K) (i : (A' ⊕ HiC K G) ⊕ Fin G.k) :
    eIdx K G hlow (lowKeep f i) = Sum.map (commonKeep G hlow f) id i := by
  rcases i with (a | b) | j <;> rfl
end CommonIndex

section Reduction
open CatalanCore CatalanCore.Rect
variable {ℓ K T : ℕ} [Fact ℓ.Prime] {Fr : Frame}

/-- Reduction of a physical principal minor deleting only low common nodes.
No all-low hypothesis is imposed on the retained geometry. -/
theorem reduction_G3_low (D : ModData3 Fr ℓ K T) (G : Geometry)
    (hlow : ∀ n, n < K → n ∈ G.C)
    (hlt : ∀ n, n ∈ G.C ∨ n ∈ G.X' ∨ n ∈ G.Y' → n < T)
    (hhi : ∀ n, n ∈ G.X' ∨ n ∈ G.Y' → K ≤ n)
    {g : Type} [Fintype g] [DecidableEq g] (nd : g → ℕ) (hnd : Function.Injective nd)
    (hab : ∀ n, (∃ i, nd i = n) ↔ n ∈ absS K T G.C G.X' G.Y')
    (f : A' → Fin K) (hf : Function.Injective f)
    {x : ℚ} (hx : x ∈ S ℓ)
    (hdet : ((G.Full Fr x).submatrix
      (fun i => eIdx K G hlow (lowKeep f i))
      (fun i => eIdx K G hlow (lowKeep f i))).det = 0) :
    ((borderedN (D.h + red ℓ x / D.κ)
      (Gcols ℓ K nd * (Gcols ℓ K nd).transpose + (D.τ₀ / D.κ) • Ttop ℓ K T)
      (WX ℓ K G) (WY ℓ K G)).submatrix (Sum.map f id) (Sum.map f id)).det = 0 := by
  let e := fun i => eIdx K G hlow (lowKeep f i)
  let P := (G.Full Fr x).submatrix e e
  let U := (Ncell Fr ℓ K G x).submatrix e e
  have hU : U = -(Matrix.diagonal (fun i => Dq ℓ K (rn G (e i))) * P *
      Matrix.diagonal (fun j => Dq ℓ K (cn G (e j)))) := by
    ext i j
    change -(Dq ℓ K (rn G (e i)) * Dq ℓ K (cn G (e j)) * G.Full Fr x (e i) (e j)) = _
    simp only [P, Matrix.submatrix_apply, Matrix.neg_apply, Matrix.diagonal_mul, Matrix.mul_diagonal]
    ring
  have h0 : U.det = 0 := by
    rw [hU, Matrix.det_neg, Matrix.det_mul, Matrix.det_mul]
    change (-1) ^ _ * (_ * ((G.Full Fr x).submatrix e e).det * _) = 0
    rw [hdet]
    simp
  have hy : ((Zmat (-red ℓ x) D.t D.d D.A (WC ℓ K G) (WX ℓ K G)
      (WY ℓ K G)).submatrix (lowKeep f) (lowKeep f)).det = 0 :=
    (red_det U _ (fun i j => y_good3 D G hlow hlt hhi ⟨hx, rfl⟩
      (lowKeep f i) (lowKeep f j))).eq_zero h0
  rw [det_ZmatN_submatrix_low f hf (-red ℓ x) D.t D.d D.κ D.h
    D.ht D.hd D.hκ D.htk D.A (WC ℓ K G) (WX ℓ K G) (WY ℓ K G)
    (Gcols ℓ K nd * (Gcols ℓ K nd).transpose + (D.τ₀ / D.κ) • Ttop ℓ K T)
    (by rw [hA_ident3 D G hlt hhi nd hnd hab]; congr 1; abel)] at hy
  have he : D.h - -red ℓ x / D.κ = D.h + red ℓ x / D.κ := by ring
  rw [he] at hy
  exact (mul_eq_zero.mp hy).resolve_left
    (mul_ne_zero (pow_ne_zero _ D.hd) (pow_ne_zero _ (neg_ne_zero.mpr D.hκ)))
end Reduction
end CatalanFrames.LambdaHybrid.NV



#print axioms CatalanFrames.LambdaHybrid.NV.reduction_G3_low
