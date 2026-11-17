module

public import CatalanCore.Content.GaussMv
public import Mathlib.FieldTheory.Finite.Basic

@[expose] public section

/-!
# Weighted determinants: half-integer potentials plus a corank (generic)

The first-order content law (`N9-LAI-CONTENT` Lemma 2.2, the half-integer extension of
CONTENT-LAYER-LAW's first-order theorem).  Indices split into an integral group `A` and a
half-integral group `B`; potentials are `π_i = k_i` on `A` and `π_i = k_i + ½` on `B`.  If
`v(M_ij) ≥ π_i + π_j` on `A × A` and `B × B` and `v(M_ij) ≥ π_i + π_j + ½` on mixed pairs, then

  `v(det M) ≥ 2 ∑ π_i + corank N̄_BB`  (`GV.det_halfInt`),

where `N̄_BB` is the reduction of `p^{-(π_i + π_j)} M_ij` on `B × B`; and, mirror image,
`v(det M) ≥ 2 ∑ π_i + corank N̄_AA` (`GV.det_halfInt_mirror`).  No `√p` is needed: the row
weights `k_i` and column weights `k_j + [j ∈ B]` make every scaled entry integral and the
`B × A` block divisible by `p`, so the reduction is block triangular (`rank_le_blockTri`).
No symmetry and no invertibility of any block is assumed.
-/

open MvPolynomial CatalanCore.Basic CatalanCore.Arith.Hybrid

namespace CatalanCore.Content

section Rank

variable {K : Type*} [Field K]

/-- Subadditivity of the matrix rank. -/
theorem matrix_rank_add_le {m n : Type*} [Fintype m] [Fintype n] (A B : Matrix m n K) :
    (A + B).rank ≤ A.rank + B.rank := by
  unfold Matrix.rank
  rw [Matrix.mulVecLin_add]
  calc Module.finrank K (LinearMap.range (A.mulVecLin + B.mulVecLin))
      ≤ Module.finrank K ↥(LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin) :=
        Submodule.finrank_mono (LinearMap.range_add_le _ _)
    _ ≤ _ := Submodule.finrank_add_le_finrank_add_finrank _ _

/-- **Block-triangular rank bound.**  If the rows in `G` vanish outside the columns in `G`, the
rank is at most the number of rows outside `G` plus the rank of the `G × G` block. -/
theorem rank_le_blockTri {ι : Type*} [Fintype ι] [DecidableEq ι] (N : Matrix ι ι K)
    (G : Finset ι) (hz : ∀ i ∈ G, ∀ j ∉ G, N i j = 0) :
    N.rank ≤ (Finset.univ \ G).card + (N.submatrix (fun i : G => (i : ι)) (fun i : G => (i : ι))).rank := by
  classical
  set N1 : Matrix ι ι K := Matrix.of fun i j => if i ∈ G then 0 else N i j
  set N2 : Matrix ι ι K := Matrix.of fun i j => if i ∈ G then N i j else 0
  have hN : N = N1 + N2 := by
    ext i j; simp only [N1, N2, Matrix.add_apply, Matrix.of_apply]; split_ifs <;> simp
  have h1 : N1.rank ≤ (Finset.univ \ G).card := by
    apply Matrix.rank_le_card_of_support_subset
    intro i hi
    simp only [Finset.coe_sdiff, Finset.coe_univ, Set.mem_diff, Set.mem_univ, Finset.mem_coe,
      true_and]
    intro hiG
    apply hi
    funext j
    simp [N1, Matrix.row, hiG]
  set E : Matrix ι G K := Matrix.of fun i g => if i = g.1 then 1 else 0
  set F : Matrix G ι K := Matrix.of fun g j => if g.1 = j then 1 else 0
  have hE : ∀ (A : Matrix G ι K) i j, (E * A) i j = if hi : i ∈ G then A ⟨i, hi⟩ j else 0 := by
    intro A i j
    simp only [Matrix.mul_apply, E, Matrix.of_apply]
    split_ifs with hi
    · rw [Finset.sum_eq_single ⟨i, hi⟩]
      · simp
      · intro g _ hg; rw [if_neg (fun h => hg (Subtype.ext h.symm)), zero_mul]
      · simp
    · refine Finset.sum_eq_zero fun g _ => ?_
      rw [if_neg (fun h => hi (by rw [h]; exact g.2)), zero_mul]
  have hF : ∀ (A : Matrix G G K) g j, (A * F) g j = if hj : j ∈ G then A g ⟨j, hj⟩ else 0 := by
    intro A g j
    simp only [Matrix.mul_apply, F, Matrix.of_apply]
    split_ifs with hj
    · rw [Finset.sum_eq_single ⟨j, hj⟩]
      · simp
      · intro h _ hh; rw [if_neg (fun e => hh (Subtype.ext e)), mul_zero]
      · simp
    · refine Finset.sum_eq_zero fun h _ => ?_
      rw [if_neg (fun e => hj (by rw [← e]; exact h.2)), mul_zero]
  have hN2 : N2 = E * N.submatrix (fun i : G => (i : ι)) (fun i : G => (i : ι)) * F := by
    ext i j
    rw [Matrix.mul_assoc, hE]
    simp only [N2, Matrix.of_apply]
    by_cases hi : i ∈ G
    · rw [dif_pos hi, if_pos hi, hF]
      by_cases hj : j ∈ G
      · rw [dif_pos hj]; rfl
      · rw [dif_neg hj, hz i hi j hj]
    · rw [dif_neg hi, if_neg hi]
  have h2 : N2.rank ≤ (N.submatrix (fun i : G => (i : ι)) (fun i : G => (i : ι))).rank := by
    rw [hN2]
    exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
  calc N.rank = (N1 + N2).rank := by rw [← hN]
    _ ≤ N1.rank + N2.rank := matrix_rank_add_le _ _
    _ ≤ _ := Nat.add_le_add h1 h2

end Rank

section Weighted

variable {σ : Type*} {p : ℕ} [hp : Fact p.Prime]

lemma p_mul_zpow (e : ℤ) : (p : ℚ) * (p : ℚ) ^ (-(e + 1)) = (p : ℚ) ^ (-e) := by
  rw [neg_add, zpow_add₀ p_ne_zero, zpow_neg_one, mul_comm, mul_assoc, inv_mul_cancel₀ p_ne_zero,
    mul_one]

lemma redMv_Cp_mul (w : MvPolynomial σ (LocRing p)) :
    redMv p (C ((p : ℕ) : LocRing p) * w) = 0 :=
  (redMv_eq_zero_iff _).2 (dvd_mul_right _ _)

/-- **The group lemma.**  Integer row and column weights `r, c`; a group `G` of indices whose rows
are one order deeper outside the `G` columns.  Then
`v(det M) ≥ ∑ r + ∑ c + corank` of the reduced `G × G` block. -/
theorem GV.det_group {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι (MvPolynomial σ ℚ))
    (r c : ι → ℤ) (G : Finset ι)
    (hM : ∀ i j, GV p (r i + c j + (if i ∈ G ∧ j ∉ G then 1 else 0)) (M i j))
    (ZG : Matrix G G (MvPolynomial σ (LocRing p)))
    (hZG : ∀ i j : G, toQmv p (ZG i j) = C ((p : ℚ) ^ (-(r i + c j))) * M i j)
    (κ : ℕ) (hrk : (ZG.map (redMv p)).rank + κ ≤ G.card) :
    GV p (∑ i, r i + ∑ j, c j + κ) M.det := by
  classical
  have hM0 : ∀ i j, GV p (r i + c j) (M i j) := fun i j =>
    (hM i j).mono (by split_ifs <;> omega)
  choose Z0 hZ using fun i j => (hM0 i j).exists_lift
  set Z : Matrix ι ι (MvPolynomial σ (LocRing p)) := Matrix.of Z0 with hZdef
  have hblock : ∀ i j : G, Z i j = ZG i j := fun i j =>
    toQmv_injective (by simp only [hZdef, Matrix.of_apply]; rw [hZ, hZG])
  have hzero : ∀ i ∈ G, ∀ j ∉ G, (Z.map (redMv p)) i j = 0 := by
    intro i hi j hj
    have h1 := hM i j
    rw [if_pos ⟨hi, hj⟩] at h1
    obtain ⟨w, hw⟩ := h1.exists_lift
    have : Z i j = C ((p : ℕ) : LocRing p) * w := by
      apply toQmv_injective
      have e1 : toQmv (σ := σ) p (C ((p : ℕ) : LocRing p)) = C (p : ℚ) := by simp [toQmv]
      rw [hZdef, Matrix.of_apply, hZ, map_mul, hw, e1, ← mul_assoc, ← C_mul, p_mul_zpow]
    simp [Matrix.map_apply, this, redMv_Cp_mul]
  have hsub : (Z.map (redMv p)).submatrix (fun i : G => (i : ι)) (fun i : G => (i : ι)) = ZG.map (redMv p) := by
    ext i j; simp [hblock]
  apply GV.det_of_rank M r c Z hZ κ
  have := rank_le_blockTri (Z.map (redMv p)) G hzero
  rw [hsub] at this
  have hcard : (Finset.univ \ G).card + G.card = Fintype.card ι := by
    rw [Finset.card_sdiff_add_card_eq_card (Finset.subset_univ G), Finset.card_univ]
  omega

/-- The potential `π_i = k_i + ½ [i ∈ B]`. -/
def halfPot {ι : Type*} [DecidableEq ι] (k : ι → ℤ) (B : Finset ι) (i : ι) : ℚ := k i + if i ∈ B then 1 / 2 else 0

lemma two_sum_halfPot {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ι → ℤ) (B : Finset ι) :
    2 * ∑ i, halfPot k B i = ((2 * ∑ i, k i + B.card : ℤ) : ℚ) := by
  classical
  simp only [halfPot, Finset.sum_add_distrib, mul_add, Finset.sum_ite_mem, Finset.univ_inter,
    Finset.sum_const, nsmul_eq_mul]
  push_cast; ring

/-- **LC06 (content note Lemma 2.2), half-integral group.**  Potentials `π = k + ½[· ∈ B]`;
entries `v(M_ij) ≥ π_i + π_j`, `+½` on mixed pairs (in integer form: `k_i + k_j + [i ∈ B ∨ j ∈ B]`).
Then `v(det M) ≥ 2∑π + corank N̄_BB`, where `N̄_BB` reduces `p^{-(π_i+π_j)} M_ij` on `B × B`. -/
theorem GV.det_halfInt {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι (MvPolynomial σ ℚ))
    (k : ι → ℤ) (B : Finset ι)
    (hM : ∀ i j, GV p (k i + k j + (if i ∈ B ∨ j ∈ B then 1 else 0)) (M i j))
    (ZB : Matrix B B (MvPolynomial σ (LocRing p)))
    (hZB : ∀ i j : B, toQmv p (ZB i j) = C ((p : ℚ) ^ (-(k i + k j + 1))) * M i j)
    (κ : ℕ) (hrk : (ZB.map (redMv p)).rank + κ ≤ B.card) :
    GV p (2 * ∑ i, k i + B.card + κ) M.det := by
  classical
  have hs : ∑ i, (if i ∈ B then (1 : ℤ) else 0) = B.card := by simp [Finset.sum_ite_mem]
  have hM' : ∀ i j, GV p (k i + (k j + if j ∈ B then 1 else 0) +
      (if i ∈ B ∧ j ∉ B then 1 else 0)) (M i j) := by
    intro i j; refine (hM i j).mono ?_
    by_cases hi : i ∈ B <;> by_cases hj : j ∈ B <;> simp [hi, hj] <;> omega
  have := GV.det_group M k (fun j => k j + if j ∈ B then 1 else 0) B hM' ZB
    (fun i j => by rw [hZB, if_pos j.2, add_assoc]) κ hrk
  refine this.mono (le_of_eq ?_)
  rw [Finset.sum_add_distrib, hs]; ring

/-- **LC06, mirror image** (the tie group is the integral one): corank of `N̄_AA`,
`A` the complement of `B`. -/
theorem GV.det_halfInt_mirror {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι (MvPolynomial σ ℚ)) (k : ι → ℤ) (B : Finset ι)
    (hM : ∀ i j, GV p (k i + k j + (if i ∈ B ∨ j ∈ B then 1 else 0)) (M i j))
    (ZA : Matrix ↥(Finset.univ \ B) ↥(Finset.univ \ B) (MvPolynomial σ (LocRing p)))
    (hZA : ∀ i j : ↥(Finset.univ \ B), toQmv p (ZA i j) = C ((p : ℚ) ^ (-(k i + k j))) * M i j)
    (κ : ℕ) (hrk : (ZA.map (redMv p)).rank + κ ≤ (Finset.univ \ B).card) :
    GV p (2 * ∑ i, k i + B.card + κ) M.det := by
  classical
  have hA : ∀ i : ↥(Finset.univ \ B), (i : ι) ∉ B := fun i => (Finset.mem_sdiff.1 i.2).2
  have hs : ∑ i, (if i ∈ B then (1 : ℤ) else 0) = B.card := by simp [Finset.sum_ite_mem]
  have hM' : ∀ i j, GV p ((k i + if i ∈ B then 1 else 0) + k j +
      (if i ∈ Finset.univ \ B ∧ j ∉ Finset.univ \ B then 1 else 0)) (M i j) := by
    intro i j; refine (hM i j).mono ?_
    by_cases hi : i ∈ B <;> by_cases hj : j ∈ B <;> simp [hi, hj] <;> omega
  have := GV.det_group M (fun i => k i + if i ∈ B then 1 else 0) k (Finset.univ \ B) hM' ZA
    (fun i j => by rw [hZA, if_neg (hA i), add_zero]) κ hrk
  refine this.mono (le_of_eq ?_)
  rw [Finset.sum_add_distrib, hs]; ring

end Weighted

section PowerSum

variable {p : ℕ} [hp : Fact p.Prime]

/-- **LC08 (content note Lemma 2.4).**  In a ring `K` of characteristic `p`, the sum over the
residues `s ∈ 𝔽_p` of a polynomial of degree `≤ p - 2` vanishes. -/
theorem sum_zmod_eval_eq_zero {K : Type*} [CommRing K] [CharP K p] (H : Polynomial K)
    (hH : H.natDegree ≤ p - 2) :
    ∑ s : ZMod p, H.eval (ZMod.castHom (dvd_refl p) K s) = 0 := by
  classical
  have h2 := hp.out.two_le
  have hlt : H.natDegree < p - 1 := by omega
  simp_rw [Polynomial.eval_eq_sum_range' hlt]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun i hi => ?_
  have hi' : i < p - 1 := Finset.mem_range.1 hi
  rw [← Finset.mul_sum]
  have : ∑ s : ZMod p, (ZMod.castHom (dvd_refl p) K s) ^ i
      = ZMod.castHom (dvd_refl p) K (∑ s : ZMod p, s ^ i) := by
    rw [map_sum]; simp
  have h0 : ∑ s : ZMod p, s ^ i = 0 :=
    FiniteField.sum_pow_lt_card_sub_one (ZMod p) i (by rwa [ZMod.card])
  rw [this, h0, map_zero, mul_zero]

end PowerSum

end CatalanCore.Content
