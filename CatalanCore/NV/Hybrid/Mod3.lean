module

public import CatalanCore.NV.LevelData
public import CatalanCore.NV.Hybrid.Split
public import CatalanCore.NV.Hybrid.Main
public import CatalanCore.NV.Hybrid.Primal

/-!
# Generic level-indexed mod-`ℓ` reduction: `ModData3` (DO Prop 1.3, frame-generic)

`ModData3 Fr ℓ K T` carries the node levels low `[0,K)`, mid `[K,T)` and top `[T,ℓ)`.  Geometry nodes
are `< T`; the top nodes enter only through the harmonic sum, with weight `τ₀` instead of the mid
weight `κ`.  The two-level data `ModData Fr ℓ K` is the instance `T = ℓ` (`ModData.toLevels`, no top
nodes, `τ₀ = 1`); P6 has `T = (ℓ+1)/2`.

Here: `det_ZmatN` (the `borderedN` form of the Schur step, arbitrary `N` in place of `G Gᵀ`), the entry
transfer `y_good3`, the harmonic split `hA_ident3`, and `reduction_G3`: `det Full(x) = 0` gives
`det borderedN (h + x̄/κ) (Gm Gmᵀ + (τ₀/κ) Ttop) WX WY = 0`.  The old two-level `reduction_G` is the
corollary in `Instance.lean`.
-/

@[expose] public section

open Finset Matrix CatalanCore CatalanCore.Rect

namespace CatalanFrames.LambdaHybrid.NV

/- Compatibility names for the generic node-level data. -/
export CatalanCore.NV (ModData3)
namespace ModData3
export CatalanCore.NV.ModData3
  (mk t d κ h τ₀ A ht hd hκ hτ htk low lh hl hhOff hhDiag harm)
end ModData3

/-- The two-level data is the `T = ℓ` instance (no top nodes; `τ₀ = 1`). -/
def ModData.toLevels {Fr : Frame} {ℓ K : ℕ} [Fact ℓ.Prime] (D : ModData Fr ℓ K) :
    ModData3 Fr ℓ K ℓ where
  t := D.t
  d := D.d
  κ := D.κ
  h := D.h
  τ₀ := 1
  A := D.A
  ht := D.ht
  hd := D.hd
  hκ := D.hκ
  hτ := one_ne_zero
  htk := D.htk
  low := D.low
  lh := D.lh
  hl := D.hl
  hhOff := D.hhOff
  hhDiag := D.hhDiag
  harm a a' := by simp [D.harm a a']

section SchurN

variable {F : Type*} [Field F] {A c m : Type*}
  [Fintype A] [DecidableEq A] [Fintype c] [DecidableEq c] [Fintype m] [DecidableEq m]

/-- **Prop 1.3, Schur step, with frame constants.**  `κ` is the harmonic-identity scale
(`A = κ (W_c W_cᵀ + N + W_x W_xᵀ + W_y W_yᵀ + h)`), `t² = -d κ`. -/
theorem det_ZmatN (x t d κ h : F) (ht : t ≠ 0) (hd : d ≠ 0) (hκ : κ ≠ 0) (htk : t * t = -d * κ)
    (Aa : Matrix A A F) (Wc : Matrix A c F) (Wx Wy : Matrix A m F) (N : Matrix A A F)
    (hA : Aa = κ • (Wc * Wcᵀ + N + Wx * Wxᵀ + Wy * Wyᵀ + h • 1)) :
    (Zmat x t d Aa Wc Wx Wy).det =
      d ^ (Fintype.card c + Fintype.card m) * (-κ) ^ Fintype.card A *
        (borderedN (h - x / κ) N Wx Wy).det := by
  rw [← Matrix.det_submatrix_equiv_self (zEquiv A c m).symm]
  have hZ : (Zmat x t d Aa Wc Wx Wy).submatrix (zEquiv A c m).symm (zEquiv A c m).symm =
      fromBlocks (fromBlocks (x • (1 : Matrix A A F) - Aa) (t • Wy) (t • Wxᵀ) 0)
        (fromRows (t • Wc) 0) (fromCols (t • Wcᵀ) 0) (d • (1 : Matrix c c F)) := by
    ext ((a | i) | j) ((b | k) | l) <;> simp [Zmat, zEquiv]
  rw [hZ]
  have : Invertible (d • (1 : Matrix c c F)) := ⟨d⁻¹ • 1, by simp [smul_smul, hd], by simp [smul_smul, hd]⟩
  rw [det_fromBlocks₂₂]
  have hi : ⅟(d • (1 : Matrix c c F)) = d⁻¹ • 1 := invOf_eq_right_inv (by simp [smul_smul, hd])
  rw [hi]
  have htd : t * d⁻¹ * t = -κ := by
    field_simp; linear_combination htk
  have hUV : fromRows (t • Wc) 0 * (d⁻¹ • (1 : Matrix c c F)) * fromCols (t • Wcᵀ) 0 =
      fromBlocks ((-κ) • (Wc * Wcᵀ)) (0 : Matrix A m F) (0 : Matrix m A F) (0 : Matrix m m F) := by
    rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, fromRows_mul_fromCols]
    simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    have : d⁻¹ * (t * t) = -κ := by rw [← htd]; ring
    ext (i | i) (j | j) <;> simp [Matrix.smul_apply, ← mul_assoc, this]
  rw [hUV]
  set Y : F := h - x / κ with hY
  have hS : fromBlocks (x • (1 : Matrix A A F) - Aa) (t • Wy) (t • Wxᵀ) 0 -
      fromBlocks ((-κ) • (Wc * Wcᵀ)) (0 : Matrix A m F) (0 : Matrix m A F) (0 : Matrix m m F) =
      fromBlocks (x • (1 : Matrix A A F) - Aa + κ • (Wc * Wcᵀ)) (t • Wy) (t • Wxᵀ) 0 := by
    ext (i | i) (j | j) <;> simp
  have hmain : fromBlocks (x • (1 : Matrix A A F) - Aa + κ • (Wc * Wcᵀ)) (t • Wy) (t • Wxᵀ) 0 =
      fromBlocks (1 : Matrix A A F) ((-(κ / t)) • Wx) (0 : Matrix m A F) (1 : Matrix m m F) *
        (fromBlocks ((-κ) • (1 : Matrix A A F)) 0 0 (t • (1 : Matrix m m F))
          * borderedN Y N Wx Wy *
          fromBlocks (1 : Matrix A A F) 0 0 ((-(t / κ)) • (1 : Matrix m m F))) *
      fromBlocks (1 : Matrix A A F) 0 ((-(κ / t)) • Wyᵀ) (1 : Matrix m m F) := by
    simp only [borderedN, Matrix.fromBlocks_multiply]
    rw [Matrix.fromBlocks_inj]
    refine ⟨?_, ?_, ?_, ?_⟩
    all_goals
      simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul, Matrix.smul_mul,
        Matrix.mul_smul, smul_smul, Matrix.add_mul, Matrix.mul_add, smul_add,
        Matrix.transpose_smul, smul_zero, add_zero, zero_add, Matrix.mul_zero]
      try rw [hA]
      try simp only [hY]
      try (first | module | (match_scalars <;> (try field_simp) <;> (try ring)))
  rw [hS, hmain, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul,
    det_fromBlocks_zero₂₁, det_fromBlocks_zero₁₂, det_fromBlocks_zero₁₂, det_fromBlocks_zero₁₂]
  simp only [det_smul, det_one, det_neg, Matrix.det_one, one_pow, mul_one, one_mul]
  have e2 : t ^ Fintype.card m * (-(t / κ)) ^ Fintype.card m = d ^ Fintype.card m := by
    rw [← mul_pow]; congr 1; field_simp; linear_combination -htk
  rw [pow_add]
  linear_combination (d ^ Fintype.card c * (-κ) ^ Fintype.card A * (borderedN Y N Wx Wy).det) * e2

end SchurN

section YGood3

variable {ℓ K T : ℕ} [Fact ℓ.Prime]

theorem y_good3 {Fr : Frame} (D : ModData3 Fr ℓ K T) (G : Geometry) (hlow : ∀ n, n < K → n ∈ G.C)
    (hlt : ∀ n, n ∈ G.C ∨ n ∈ G.X' ∨ n ∈ G.Y' → n < T)
    (hhi : ∀ n, n ∈ G.X' ∨ n ∈ G.Y' → K ≤ n)
    {x : ℚ} {xb : ZMod ℓ} (hx : Good ℓ x xb) (i j : (Fin K ⊕ HiC K G) ⊕ Fin G.k) :
    Good ℓ (Ncell Fr ℓ K G x (eIdx K G hlow i) (eIdx K G hlow j))
      (Zmat (-xb) D.t D.d D.A (WC ℓ K G) (WX ℓ K G) (WY ℓ K G) i j) := by
  have hxsK : ∀ i : Fin G.k, K ≤ G.xs i ∧ G.xs i < T := fun i =>
    ⟨hhi _ (Or.inl (xs_mem G i)), hlt _ (Or.inr (Or.inl (xs_mem G i)))⟩
  have hysK : ∀ i : Fin G.k, K ≤ G.ys i ∧ G.ys i < T := fun i =>
    ⟨hhi _ (Or.inr (ys_mem G i)), hlt _ (Or.inr (Or.inr (ys_mem G i)))⟩
  have hCl : ∀ b : G.C, (b : ℕ) < T := fun b => hlt _ (Or.inl b.2)
  have hCxs : ∀ (b : G.C) (i : Fin G.k), (b : ℕ) ≠ G.xs i := fun b i h =>
    Finset.disjoint_left.1 G.disjCX b.2 (h ▸ xs_mem G i)
  have hCys : ∀ (b : G.C) (i : Fin G.k), (b : ℕ) ≠ G.ys i := fun b i h =>
    Finset.disjoint_left.1 G.disjCY b.2 (h ▸ ys_mem G i)
  have hxy : ∀ i j : Fin G.k, G.xs i ≠ G.ys j := fun i j h =>
    Finset.disjoint_left.1 G.disjXY (xs_mem G i) (h ▸ ys_mem G j)
  rcases i with (a | b) | i <;> rcases j with (a' | b') | j
  · -- low / low
    have he : Good ℓ (if (a : ℕ) = a' then x else 0) (if (a : ℕ) = a' then xb else 0) := by
      split_ifs
      · exact hx
      · exact Good.zero
    have hg := (D.low a a' he).neg
    have hN : Ncell Fr ℓ K G x (eIdx K G hlow (Sum.inl (Sum.inl a)))
        (eIdx K G hlow (Sum.inl (Sum.inl a'))) = -(Dq ℓ K a * Dq ℓ K a' *
          ((if (a : ℕ) = a' then x else 0) + Fr.Mn a a')) := by
      simp [Ncell, eIdx, eLow, rn, cn, full_ll, Fin.ext_iff]
    rw [hN]
    refine hg.congr ?_
    by_cases haa : a = a'
    · subst haa; simp [Zmat]; ring
    · have : (a : ℕ) ≠ a' := fun h => haa (Fin.ext h)
      simp [Zmat, haa, this]
  · -- low / high common
    have ha := a.2
    have hb : K ≤ (b' : G.C).1 := by have := b'.2; omega
    have hbl := hCl b'.1
    have hne : (a : ℕ) ≠ (b'.1 : ℕ) := by omega
    have hg := (D.lh a b'.1.1 ha hb hbl).neg
    have hN : Ncell Fr ℓ K G x (eIdx K G hlow (Sum.inl (Sum.inl a)))
        (eIdx K G hlow (Sum.inl (Sum.inr b'))) = -(Dq ℓ K a *
          Dq ℓ K b'.1.1 * (0 + Fr.Mn a b'.1.1)) := by
      simp [Ncell, eIdx, eLow, rn, cn, full_ll, Subtype.ext_iff, hne]
    rw [hN]
    refine hg.congr ?_
    simp [Zmat, WC, Wnode]
  · -- low / Y'
    have ha := a.2
    have hg := (D.lh a (G.ys j) ha (hysK j).1 (hysK j).2).neg
    have hN : Ncell Fr ℓ K G x (eIdx K G hlow (Sum.inl (Sum.inl a)))
        (eIdx K G hlow (Sum.inr j)) = -(Dq ℓ K a *
          Dq ℓ K (G.ys j) * (0 + Fr.Mn a (G.ys j))) := by
      simp [Ncell, eIdx, eLow, rn, cn, full_lr]
    rw [hN]
    refine hg.congr ?_
    simp [Zmat, WY, Wnode]
  · -- high common / low
    have ha := a'.2
    have hb : K ≤ (b : G.C).1 := by have := b.2; omega
    have hbl := hCl b.1
    have hne : (b.1 : ℕ) ≠ (a' : ℕ) := by omega
    have hg := (D.hl b.1.1 a' hb hbl ha).neg
    have hN : Ncell Fr ℓ K G x (eIdx K G hlow (Sum.inl (Sum.inr b)))
        (eIdx K G hlow (Sum.inl (Sum.inl a'))) = -(Dq ℓ K b.1.1 *
          Dq ℓ K a' * (0 + Fr.Mn b.1.1 a')) := by
      simp [Ncell, eIdx, eLow, rn, cn, full_ll, Subtype.ext_iff, hne]
    rw [hN]
    refine hg.congr ?_
    simp [Zmat, WC, Wnode]
  · -- high common / high common
    have hb : K ≤ (b : G.C).1 := by have := b.2; omega
    have hb' : K ≤ (b' : G.C).1 := by have := b'.2; omega
    by_cases hbb : b = b'
    · subst hbb
      have hg := (D.hhDiag b.1.1 hb (hCl b.1) hx).neg
      have hN : Ncell Fr ℓ K G x (eIdx K G hlow (Sum.inl (Sum.inr b)))
          (eIdx K G hlow (Sum.inl (Sum.inr b))) = -(Dq ℓ K b.1.1 *
            Dq ℓ K b.1.1 * (x + Fr.Mn b.1.1 b.1.1)) := by
        simp [Ncell, eIdx, rn, cn, full_ll]
      rw [hN]
      refine hg.congr ?_
      simp [Zmat]
    · have hne : (b.1 : ℕ) ≠ (b'.1 : ℕ) := fun h => hbb (Subtype.ext (Subtype.ext h))
      have hg := (D.hhOff b.1.1 b'.1.1 hb (hCl b.1) hb' (hCl b'.1) hne).neg
      have hN : Ncell Fr ℓ K G x (eIdx K G hlow (Sum.inl (Sum.inr b)))
          (eIdx K G hlow (Sum.inl (Sum.inr b'))) = -(Dq ℓ K b.1.1 *
            Dq ℓ K b'.1.1 * (0 + Fr.Mn b.1.1 b'.1.1)) := by
        have hne' : b.1 ≠ b'.1 := fun h => hne (congrArg Subtype.val h)
        simp [Ncell, eIdx, rn, cn, full_ll, hne']
      rw [hN]
      refine hg.congr ?_
      simp [Zmat, hbb]
  · -- high common / Y'
    have hb : K ≤ (b : G.C).1 := by have := b.2; omega
    have hg := (D.hhOff b.1.1 (G.ys j) hb (hCl b.1) (hysK j).1 (hysK j).2 (hCys b.1 j)).neg
    have hN : Ncell Fr ℓ K G x (eIdx K G hlow (Sum.inl (Sum.inr b)))
        (eIdx K G hlow (Sum.inr j)) = -(Dq ℓ K b.1.1 *
          Dq ℓ K (G.ys j) * (0 + Fr.Mn b.1.1 (G.ys j))) := by
      simp [Ncell, eIdx, rn, cn, full_lr]
    rw [hN]
    refine hg.congr ?_
    simp [Zmat]
  · -- X' / low
    have ha := a'.2
    have hg := (D.hl (G.xs i) a' (hxsK i).1 (hxsK i).2 ha).neg
    have hN : Ncell Fr ℓ K G x (eIdx K G hlow (Sum.inr i))
        (eIdx K G hlow (Sum.inl (Sum.inl a'))) = -(Dq ℓ K (G.xs i) *
          Dq ℓ K a' * (0 + Fr.Mn (G.xs i) a')) := by
      simp [Ncell, eIdx, eLow, rn, cn, full_rl]
    rw [hN]
    refine hg.congr ?_
    simp [Zmat, WX, Wnode]
  · -- X' / high common
    have hb' : K ≤ (b' : G.C).1 := by have := b'.2; omega
    have hg := (D.hhOff (G.xs i) b'.1.1 (hxsK i).1 (hxsK i).2 hb' (hCl b'.1)
      (Ne.symm (hCxs b'.1 i))).neg
    have hN : Ncell Fr ℓ K G x (eIdx K G hlow (Sum.inr i))
        (eIdx K G hlow (Sum.inl (Sum.inr b'))) = -(Dq ℓ K (G.xs i) *
          Dq ℓ K b'.1.1 * (0 + Fr.Mn (G.xs i) b'.1.1)) := by
      simp [Ncell, eIdx, rn, cn, full_rl]
    rw [hN]
    refine hg.congr ?_
    simp [Zmat]
  · -- X' / Y'
    have hg := (D.hhOff (G.xs i) (G.ys j) (hxsK i).1 (hxsK i).2 (hysK j).1 (hysK j).2
      (hxy i j)).neg
    have hN : Ncell Fr ℓ K G x (eIdx K G hlow (Sum.inr i))
        (eIdx K G hlow (Sum.inr j)) = -(Dq ℓ K (G.xs i) *
          Dq ℓ K (G.ys j) * (0 + Fr.Mn (G.xs i) (G.ys j))) := by
      simp [Ncell, eIdx, rn, cn, full_rr]
    rw [hN]
    refine hg.congr ?_
    simp [Zmat]

end YGood3
section Red3

variable {ℓ K T : ℕ} [Fact ℓ.Prime] {Fr : Frame}

/-- Cauchy Gram matrix of the top nodes `[T, ℓ)`. -/
noncomputable def Ttop (ℓ K T : ℕ) [Fact ℓ.Prime] : Matrix (Fin K) (Fin K) (ZMod ℓ) :=
  Matrix.of fun a b => ∑ n ∈ Ico T ℓ, Wnode ℓ K n a * Wnode ℓ K n b

theorem hA_ident3 (D : ModData3 Fr ℓ K T) (G : Geometry)
    (hlt : ∀ n, n ∈ G.C ∨ n ∈ G.X' ∨ n ∈ G.Y' → n < T)
    (hhi : ∀ n, n ∈ G.X' ∨ n ∈ G.Y' → K ≤ n)
    {g : Type} [Fintype g] [DecidableEq g] (nd : g → ℕ) (hnd : Function.Injective nd)
    (hab : ∀ n, (∃ i, nd i = n) ↔ n ∈ absS K T G.C G.X' G.Y') :
    D.A = D.κ • (WC ℓ K G * (WC ℓ K G)ᵀ + Gcols ℓ K nd * (Gcols ℓ K nd)ᵀ +
      (D.τ₀ / D.κ) • Ttop ℓ K T +
      WX ℓ K G * (WX ℓ K G)ᵀ + WY ℓ K G * (WY ℓ K G)ᵀ + D.h • 1) := by
  ext a a'
  have hsp := sum_split K T G.C G.X' G.Y' G.disjCX G.disjCY G.disjXY
    (fun n hn => hlt n (Or.inl hn)) (fun n hn => ⟨hhi n (Or.inl hn), hlt n (Or.inr (Or.inl hn))⟩)
    (fun n hn => ⟨hhi n (Or.inr hn), hlt n (Or.inr (Or.inr hn))⟩)
    (fun n => (1 / (((a : ℕ) : ZMod ℓ) - n)) * (1 / (((a' : ℕ) : ZMod ℓ) - n)))
  obtain ⟨hxi, hxr⟩ := xs_family G
  obtain ⟨hyi, hyr⟩ := ys_family G
  obtain ⟨hci, hcr⟩ := hic_family K G
  have s1 := sum_family (fun b : HiC K G => ((b.1 : G.C) : ℕ)) hci _ hcr
    (fun n => (1 / (((a : ℕ) : ZMod ℓ) - n)) * (1 / (((a' : ℕ) : ZMod ℓ) - n)))
  have s2 := sum_family nd hnd _ hab
    (fun n => (1 / (((a : ℕ) : ZMod ℓ) - n)) * (1 / (((a' : ℕ) : ZMod ℓ) - n)))
  have s3 := sum_family G.xs hxi _ hxr
    (fun n => (1 / (((a : ℕ) : ZMod ℓ) - n)) * (1 / (((a' : ℕ) : ZMod ℓ) - n)))
  have s4 := sum_family G.ys hyi _ hyr
    (fun n => (1 / (((a : ℕ) : ZMod ℓ) - n)) * (1 / (((a' : ℕ) : ZMod ℓ) - n)))
  have hκ := D.hκ
  rw [D.harm a a', hsp, ← s1, ← s2, ← s3, ← s4]
  simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.mul_apply,
    Matrix.transpose_apply, WC, WX, WY, Gcols, Wnode, Ttop, smul_eq_mul, Matrix.one_apply,
    Matrix.of_apply]
  split_ifs <;> field_simp <;> ring

/-- **Three-level DO Prop 1.3.** `det Full(x) = 0` forces the vanishing of a `borderedN` determinant whose
`N` is the Gram matrix of the absent mid columns plus `τ₀/κ` times the top Gram matrix. -/
theorem reduction_G3 (D : ModData3 Fr ℓ K T) (G : Geometry)
    (hlow : ∀ n, n < K → n ∈ G.C)
    (hlt : ∀ n, n ∈ G.C ∨ n ∈ G.X' ∨ n ∈ G.Y' → n < T)
    (hhi : ∀ n, n ∈ G.X' ∨ n ∈ G.Y' → K ≤ n)
    {g : Type} [Fintype g] [DecidableEq g] (nd : g → ℕ) (hnd : Function.Injective nd)
    (hab : ∀ n, (∃ i, nd i = n) ↔ n ∈ absS K T G.C G.X' G.Y')
    {x : ℚ} (hx : x ∈ S ℓ) (hdet : (G.Full Fr x).det = 0) :
    (borderedN (D.h + red ℓ x / D.κ)
      (Gcols ℓ K nd * (Gcols ℓ K nd)ᵀ + (D.τ₀ / D.κ) • Ttop ℓ K T)
      (WX ℓ K G) (WY ℓ K G)).det = 0 := by
  have hx' : Good ℓ x (red ℓ x) := ⟨hx, rfl⟩
  have h0 : (Ncell Fr ℓ K G x).det = 0 := by
    have : Ncell Fr ℓ K G x = -(Matrix.diagonal (fun i => Dq ℓ K (rn G i)) *
        G.Full Fr x * Matrix.diagonal (fun j => Dq ℓ K (cn G j))) := by
      ext i j
      simp [Ncell, Matrix.diagonal_mul, Matrix.mul_diagonal, mul_assoc, mul_comm, mul_left_comm]
    rw [this, Matrix.det_neg, Matrix.det_mul, Matrix.det_mul, hdet]
    simp
  have hy := det_eq_zero_of_good (eIdx K G hlow) (Ncell Fr ℓ K G x)
    (Zmat (-red ℓ x) D.t D.d D.A (WC ℓ K G) (WX ℓ K G) (WY ℓ K G))
    (fun i j => y_good3 D G hlow hlt hhi hx' i j) h0
  rw [det_ZmatN (-red ℓ x) D.t D.d D.κ D.h D.ht D.hd D.hκ D.htk D.A (WC ℓ K G) (WX ℓ K G)
    (WY ℓ K G) (Gcols ℓ K nd * (Gcols ℓ K nd)ᵀ + (D.τ₀ / D.κ) • Ttop ℓ K T)
    (by rw [hA_ident3 D G hlt hhi nd hnd hab]; congr 1; abel)] at hy
  have e : D.h - -red ℓ x / D.κ = D.h + red ℓ x / D.κ := by ring
  rw [e] at hy
  have hne : D.d ^ (Fintype.card (HiC K G) + Fintype.card (Fin G.k)) *
      (-D.κ) ^ Fintype.card (Fin K) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ D.hd) (pow_ne_zero _ (neg_ne_zero.2 D.hκ))
  exact (mul_eq_zero.1 hy).resolve_left hne

end Red3

end CatalanFrames.LambdaHybrid.NV
