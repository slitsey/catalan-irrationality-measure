module

public import CatalanFrames.LambdaHybrid.NV.FinalS
public import CatalanCore.Star.Leonard.KgenGood
public import CatalanCore.Star.Leonard.KgenSpan

/-!
# The last mile: `kgen(0)` an `ℓ`-unit ⟹ `k_R'` of the NV pair is nonzero in `𝔽_ℓ`

Dictionary (`S = s' + 1`, `r + 2m + S = ℓ`): `Wnode ℓ K (r+2i) a = 1/(a + j)` with `j = ℓ - r - 2i`,
so `WX ℓ K (after r m)`, `WY ℓ K (after r m)` are `Wb K 0 (bX m S)`, `Wb K 0 (bY m S)` over `ZMod ℓ` with
the columns reversed (simultaneously, so `projP` is unchanged); `N2 = Nmat K 0 {1..S-1}`,
`wLast = wcol K 0 S`.
-/

@[expose] public section

open Finset Matrix CatalanCore.Star CatalanCore.Rect

namespace CatalanFrames.LambdaHybrid.NV

section Generic

variable {F : Type*} [Field F] {A : Type*} [Fintype A] [DecidableEq A]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

lemma projP_reindex (WX WY : Matrix A ι F) (e : κ ≃ ι) :
    projP (WX.submatrix id e) (WY.submatrix id e) = projP WX WY := by
  unfold projP
  have h1 : (WX.submatrix id e)ᵀ * WY.submatrix id e = (WXᵀ * WY).submatrix e e := by
    ext i j
    simp [Matrix.mul_apply, Matrix.submatrix_apply]
  rw [h1, Matrix.inv_submatrix_equiv]
  congr 1
  ext a b
  simp only [Matrix.mul_apply, Matrix.submatrix_apply, Matrix.transpose_apply, id]
  rw [← Equiv.sum_comp e]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  exact Equiv.sum_comp e (fun j => WY a j * (WXᵀ * WY)⁻¹ j (e i))

lemma spansKer_reindex (WX : Matrix A ι F) (e : κ ≃ ι) {n : ℕ} (U : Matrix A (Fin n) F) :
    SpansKer (WX.submatrix id e) U ↔ SpansKer WX U := by
  have key : ∀ x : A → F, (WX.submatrix id e)ᵀ *ᵥ x = 0 ↔ WXᵀ *ᵥ x = 0 := by
    intro x
    constructor
    · intro h
      ext j
      have := congrFun h (e.symm j)
      simpa [Matrix.mulVec, dotProduct] using this
    · intro h
      ext j
      have := congrFun h (e j)
      simpa [Matrix.mulVec, dotProduct] using this
  unfold SpansKer
  constructor
  · intro h x hx; exact h x ((key x).2 hx)
  · intro h x hx; exact h x ((key x).1 hx)

lemma kgenR'_reindex {n : ℕ} (N : Matrix A A F) (w : A → F) (WX WY : Matrix A ι F) (e : κ ≃ ι)
    (U : Matrix A (Fin n) F) :
    kgenR' N w (WX.submatrix id e) (WY.submatrix id e) U = kgenR' N w WX WY U := by
  unfold kgenR' kgenK
  rw [projP_reindex]

end Generic

section Dict

variable {ℓ : ℕ} [Fact ℓ.Prime] (K m r s' : ℕ)

/-- reversal of the border columns -/
def tauE (r m : ℕ) : Fin (after r m).k ≃ Fin m := (finCongr (after_k r m)).trans Fin.revPerm

lemma tauE_val (r m : ℕ) (i : Fin (after r m).k) : ((tauE r m i : Fin m) : ℕ) = m - ((i : ℕ) + 1) := by
  simp [tauE, Fin.val_rev]

lemma WX_eq (hr : r + 2 * m + (s' + 1) = ℓ) :
    WX ℓ K (after r m) = (Wb K (0 : ZMod ℓ) (bX m ((s' + 1 : ℕ) : ℤ))).submatrix id (tauE r m) := by
  ext a i
  have hi : (i : ℕ) < m := by have := i.2; have hk := after_k r m; omega
  simp only [WX, Wnode, Matrix.of_apply, Matrix.submatrix_apply, id, Wb, wcol, bX, after_xs,
    tauE_val]
  have h1 : (((s' + 1 : ℕ) : ℤ) + 2 + 2 * ((m - ((i : ℕ) + 1) : ℕ) : ℤ) : ℤ) =
      ((ℓ - (r + 2 * (i : ℕ)) : ℕ) : ℤ) := by omega
  rw [h1]
  have h2 : ((ℓ - (r + 2 * (i : ℕ)) : ℕ) : ZMod ℓ) = -((r + 2 * (i : ℕ) : ℕ) : ZMod ℓ) := by
    rw [Nat.cast_sub (by omega), ZMod.natCast_self, zero_sub]
  simp only [Int.cast_natCast, h2]
  congr 1
  ring

lemma WY_eq (hr : r + 2 * m + (s' + 1) = ℓ) :
    WY ℓ K (after r m) = (Wb K (0 : ZMod ℓ) (bY m ((s' + 1 : ℕ) : ℤ))).submatrix id (tauE r m) := by
  ext a i
  have hi : (i : ℕ) < m := by have := i.2; have hk := after_k r m; omega
  simp only [WY, Wnode, Matrix.of_apply, Matrix.submatrix_apply, id, Wb, wcol, bY, after_ys,
    tauE_val]
  have h1 : (((s' + 1 : ℕ) : ℤ) + 1 + 2 * ((m - ((i : ℕ) + 1) : ℕ) : ℤ) : ℤ) =
      ((ℓ - (r + 2 * (i : ℕ) + 1) : ℕ) : ℤ) := by omega
  rw [h1]
  have h2 : ((ℓ - (r + 2 * (i : ℕ) + 1) : ℕ) : ZMod ℓ) = -((r + 2 * (i : ℕ) + 1 : ℕ) : ZMod ℓ) := by
    rw [Nat.cast_sub (by omega), ZMod.natCast_self, zero_sub]
  simp only [Int.cast_natCast, h2]
  congr 1
  ring


lemma Wnode_abs (i : ℕ) (hi : i + 1 ≤ ℓ) (a : Fin K) :
    Wnode ℓ K (ℓ - 1 - i) a = wcol K (0 : ZMod ℓ) ((i : ℤ) + 1) a := by
  simp only [Wnode, wcol]
  have h2 : ((ℓ - 1 - i : ℕ) : ZMod ℓ) = -((i : ZMod ℓ) + 1) := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), ZMod.natCast_self]; push_cast; ring
  rw [h2]
  push_cast
  congr 1
  ring

lemma wLast_eq (hr : r + 2 * m + (s' + 1) = ℓ) :
    wLast ℓ K s' = wcol K (0 : ZMod ℓ) ((s' + 1 : ℕ) : ℤ) := by
  funext a
  unfold wLast ndAbs
  simp only [Fin.val_last]
  rw [Wnode_abs K s' (by omega) a]
  push_cast
  rfl

lemma N2_eq (hr : r + 2 * m + (s' + 1) = ℓ) :
    N2 ℓ K s' = Nmat K (0 : ZMod ℓ) (Finset.Icc 1 (((s' + 1 : ℕ) : ℤ) - 1)) := by
  ext a b
  simp only [N2, Gcols, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Nmat,
    Matrix.sum_apply, Matrix.vecMulVec_apply, Function.comp_apply, ndAbs]
  refine Finset.sum_bij (fun (i : Fin s') _ => ((i : ℕ) : ℤ) + 1) ?_ ?_ ?_ ?_
  · intro i _
    simp only [Finset.mem_Icc]; have := i.2; omega
  · intro i _ j _ h
    apply Fin.ext
    simpa using h
  · intro j hj
    simp only [Finset.mem_Icc] at hj
    refine ⟨⟨(j - 1).toNat, by omega⟩, Finset.mem_univ _, ?_⟩
    simp only
    omega
  · intro i _
    have hi := i.2
    simp only [Fin.val_castSucc]
    rw [Wnode_abs K i (by omega) a, Wnode_abs K i (by omega) b]


end Dict

/-- **The last mile.** If `kgen K m (s'+1) 0` is an `ℓ`-unit then the NV pair has a spanning family
with `k_R' ≠ 0` in `𝔽_ℓ`. -/
theorem kgenR'_ne_zero_of_LU {ℓ : ℕ} [Fact ℓ.Prime] (K m r s' : ℕ) (hmK : m < K) (hrK : K ≤ r)
    (hr : r + 2 * m + (s' + 1) = ℓ)
    (hLU : CatalanCore.ThmA.LU ℓ (kgen K m (s' + 1) (0 : ℚ))) :
    ∃ U : Matrix (Fin K) (Fin (K - m)) (ZMod ℓ), SpansKer (WX ℓ K (after r m)) U ∧
      kgenR' (N2 ℓ K s') (wLast ℓ K s') (WX ℓ K (after r m)) (WY ℓ K (after r m)) U ≠ 0 := by
  have hK1 : 1 ≤ K := by omega
  have hKl : K < ℓ := by omega
  have hΔq := CatalanCore.Star.Leonard.Delta_LU (ℓ := ℓ) K m (s' + 1) hmK.le hK1 (by omega)
  have hbx : ∀ i : Fin m, 1 ≤ bX m ((s' + 1 : ℕ) : ℤ) i ∧ bX m ((s' + 1 : ℕ) : ℤ) i + K ≤ ℓ := by
    intro i; have := i.2; simp only [bX]; omega
  have hby : ∀ i : Fin m, 1 ≤ bY m ((s' + 1 : ℕ) : ℤ) i ∧ bY m ((s' + 1 : ℕ) : ℤ) i + K ≤ ℓ := by
    intro i; have := i.2; simp only [bY]; omega
  have hgood := CatalanCore.Star.Leonard.good_kgenCore (ℓ := ℓ) (K := K) (m := m)
    (Finset.Icc 1 (((s' + 1 : ℕ) : ℤ) - 1)) ((s' + 1 : ℕ) : ℤ) (bX m ((s' + 1 : ℕ) : ℤ))
    (bY m ((s' + 1 : ℕ) : ℤ)) hKl (fun j hj => by have := Finset.mem_Icc.1 hj; omega)
    (by omega) hbx hby hΔq
  have hne : kgenCore K m (0 : ZMod ℓ) (Finset.Icc 1 (((s' + 1 : ℕ) : ℤ) - 1))
      ((s' + 1 : ℕ) : ℤ) (bX m ((s' + 1 : ℕ) : ℤ)) (bY m ((s' + 1 : ℕ) : ℤ)) ≠ 0 :=
    CatalanCore.Star.Leonard.ne_zero_of_LU_good hLU hgood
  have hdist : ∀ a b : Fin K, ((a : ℕ) : ZMod ℓ) = ((b : ℕ) : ZMod ℓ) → a = b := by
    intro a b h
    by_contra hab
    exact CatalanCore.natCast_ne_natCast (by have := a.2; omega) (by have := b.2; omega)
      (fun h' => hab (Fin.ext h')) h
  have hGZ := (CatalanCore.Star.Leonard.good_Wb (K := K) _ hbx).transpose.mul
    (CatalanCore.Star.Leonard.good_Wb (K := K) _ hby)
  have hΔZ : ((Wb K (0 : ZMod ℓ) (bX m ((s' + 1 : ℕ) : ℤ)))ᵀ *
      Wb K (0 : ZMod ℓ) (bY m ((s' + 1 : ℕ) : ℤ))).det ≠ 0 :=
    CatalanCore.Star.Leonard.ne_zero_of_LU_good hΔq hGZ.det
  refine ⟨ubasis K (K - m) (0 : ZMod ℓ) (bX m ((s' + 1 : ℕ) : ℤ)), ?_, ?_⟩
  · rw [WX_eq K m r s' hr, spansKer_reindex]
    intro x hx
    exact CatalanCore.Star.Leonard.exists_ubasis_of_ker_K K m (K - m) (by omega) 0 hdist _ _
      (fun i a => CatalanCore.Star.Leonard.zmod_ne_zero_aj a _ (hbx i).1 (by
        have := a.2; have := hbx i; omega)) hΔZ x hx
  · rw [WX_eq K m r s' hr, WY_eq K m r s' hr, kgenR'_reindex, N2_eq K m r s' hr,
      wLast_eq K m r s' hr]
    exact hne

end CatalanFrames.LambdaHybrid.NV
