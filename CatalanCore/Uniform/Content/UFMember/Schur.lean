module

public import CatalanCore.Uniform.Content.UFMember.Wit3

@[expose] public section

/-!
# UF member package: three-level witnesses from the border Schur complement

Lemma A2 of `smith-deletion/THEOREM.md` in Lean form.  Write the integral lift of `p² M` in
core/border blocks `[[Q, R'], [S', T']]` with `Q` (the core block) primitive (`det Q` a unit
modulo `p`; in the scaled gauge it is monic in `U`).  The polynomial unit shears

  `L₀ = [[1, 0], [-S' adj Q, det Q]]`,  `P₀ = [[1, -adj Q R'], [0, det Q]]`

give `L₀ A P₀ = diag(Q, det Q · Sch)` with `Sch = det Q · T' - S' adj Q R'` (`schur_sandwich`).
If `Sch = p W` (distinct border residues) and `W` carries two-level data `(L₂, P₂, s, N₂)`
(the `J`-supported kernels and their divided Cauchy pairing, (S7)–(S8)), then
`ThreeLevelWit.ofSchur` is a three-level witness of `M` with `t` = all border indices.  Its
price is `2h - (m + σ + (σ - b))`, i.e. `2|C| + m - (σ + (σ - b))`.

So the remaining frame obligations are exactly: the integral lift, `det Q` primitive,
`p ∣ Sch`, and the two-level data of `W = Sch / p`.
-/

open Polynomial Matrix Finset CatalanCore.Basic CatalanCore.Arith.Hybrid

namespace CatalanCore.Uniform.Content.UFMember

section Algebra

variable {R : Type*} [CommRing R] {C B : Type*} [Fintype C] [DecidableEq C] [Fintype B]
  [DecidableEq B]

/-- The unit-shear sandwich of a core/border block matrix. -/
theorem schur_sandwich (Q : Matrix C C R) (R' : Matrix C B R) (S' : Matrix B C R)
    (T' : Matrix B B R) (L₂ P₂ : Matrix B B R) :
    Matrix.fromBlocks 1 0 0 L₂ * Matrix.fromBlocks 1 0 (-(S' * Q.adjugate)) (Q.det • 1) *
        Matrix.fromBlocks Q R' S' T' *
        (Matrix.fromBlocks 1 (-(Q.adjugate * R')) 0 (Q.det • 1) * Matrix.fromBlocks 1 0 0 P₂) =
      Matrix.fromBlocks Q 0 0 (Q.det • (L₂ * (Q.det • T' - S' * Q.adjugate * R') * P₂)) := by
  have e1 : Matrix.fromBlocks 1 0 (-(S' * Q.adjugate)) (Q.det • 1) * Matrix.fromBlocks Q R' S' T'
      = Matrix.fromBlocks Q R' 0 (Q.det • T' - S' * Q.adjugate * R') := by
    rw [Matrix.fromBlocks_multiply]
    congr 1
    · simp
    · simp
    · rw [Matrix.neg_mul, Matrix.mul_assoc, Matrix.adjugate_mul]
      simp
    · rw [Matrix.neg_mul, Matrix.smul_mul, Matrix.one_mul]
      abel
  have e2 : Matrix.fromBlocks Q R' 0 (Q.det • T' - S' * Q.adjugate * R') *
      Matrix.fromBlocks 1 (-(Q.adjugate * R')) 0 (Q.det • 1) =
      Matrix.fromBlocks Q 0 0 (Q.det • (Q.det • T' - S' * Q.adjugate * R')) := by
    rw [Matrix.fromBlocks_multiply]
    congr 1
    · simp
    · rw [Matrix.mul_neg, ← Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.mul_smul,
        Matrix.mul_one]
      simp
    · simp
    · simp [Matrix.mul_smul]
  calc Matrix.fromBlocks 1 0 0 L₂ * Matrix.fromBlocks 1 0 (-(S' * Q.adjugate)) (Q.det • 1) *
        Matrix.fromBlocks Q R' S' T' *
        (Matrix.fromBlocks 1 (-(Q.adjugate * R')) 0 (Q.det • 1) * Matrix.fromBlocks 1 0 0 P₂)
      = Matrix.fromBlocks 1 0 0 L₂ *
          ((Matrix.fromBlocks 1 0 (-(S' * Q.adjugate)) (Q.det • 1) *
            Matrix.fromBlocks Q R' S' T') *
          Matrix.fromBlocks 1 (-(Q.adjugate * R')) 0 (Q.det • 1)) *
          Matrix.fromBlocks 1 0 0 P₂ := by simp only [Matrix.mul_assoc]
    _ = Matrix.fromBlocks 1 0 0 L₂ *
          Matrix.fromBlocks Q 0 0 (Q.det • (Q.det • T' - S' * Q.adjugate * R')) *
          Matrix.fromBlocks 1 0 0 P₂ := by rw [e1, e2]
    _ = _ := by
          rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
          simp [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]

end Algebra

variable {p : ℕ} [Fact p.Prime] {C B : Type*} [Fintype C] [DecidableEq C] [Fintype B]
  [DecidableEq B]

/-- The border index set `B` inside `C ⊕ B`. -/
def borderSet (C B : Type*) [Fintype B] : Finset (C ⊕ B) := univ.map Function.Embedding.inr

/-- A subset of the border inside `C ⊕ B`. -/
def borderSub (C : Type*) {B : Type*} (s : Finset B) : Finset (C ⊕ B) :=
  s.map Function.Embedding.inr

lemma mem_borderSub {s : Finset B} {i : C ⊕ B} (h : i ∈ borderSub C s) :
    ∃ x ∈ s, i = Sum.inr x := by
  obtain ⟨x, hx, rfl⟩ := Finset.mem_map.1 h
  exact ⟨x, hx, rfl⟩

lemma mem_borderSet {i : C ⊕ B} (h : i ∈ borderSet C B) : ∃ x, i = Sum.inr x := by
  obtain ⟨x, -, rfl⟩ := Finset.mem_map.1 h
  exact ⟨x, rfl⟩

/-- The point of `s` under an element of `borderSub C s`. -/
noncomputable def borderSub.pt {s : Finset B} (i : borderSub C s) : s :=
  ⟨(mem_borderSub i.2).choose, (mem_borderSub i.2).choose_spec.1⟩

lemma borderSub.pt_spec {s : Finset B} (i : borderSub C s) :
    i.1 = Sum.inr (borderSub.pt i).1 :=
  (mem_borderSub i.2).choose_spec.2

/-- **Three-level witness from the border Schur complement** (Lemma A2). -/
noncomputable def ThreeLevelWit.ofSchur (M : Matrix (C ⊕ B) (C ⊕ B) ℚ[X])
    (Bl : Matrix (C ⊕ B) (C ⊕ B) (LocRing p)[X])
    (hB : ∀ i j, toQ p (Bl i j) = Polynomial.C ((p : ℚ) ^ 2) * M i j)
    (hQ : phiP p Bl.toBlocks₁₁.det ≠ 0) (W : Matrix B B (LocRing p)[X])
    (hW : Bl.toBlocks₁₁.det • Bl.toBlocks₂₂ - Bl.toBlocks₂₁ * Bl.toBlocks₁₁.adjugate *
      Bl.toBlocks₁₂ = Polynomial.C ((p : ℕ) : LocRing p) • W)
    (L₂ P₂ : Matrix B B (LocRing p)[X]) (hL₂ : phiP p L₂.det ≠ 0) (hP₂ : phiP p P₂.det ≠ 0)
    (s : Finset B)
    (hrow : ∀ i ∈ s, ∀ j, Polynomial.C ((p : ℕ) : LocRing p) ∣ (L₂ * W * P₂) i j)
    (hcol : ∀ i, ∀ j ∈ s, Polynomial.C ((p : ℕ) : LocRing p) ∣ (L₂ * W * P₂) i j)
    (N₂ : Matrix s s (LocRing p)[X])
    (hN₂ : ∀ i j : s, (L₂ * W * P₂) i j = Polynomial.C ((p : ℕ) : LocRing p) * N₂ i j)
    (b : ℕ) (hb : (N₂.map (phiP p)).rank ≤ b) : ThreeLevelWit p M b := by
  classical
  set Q := Bl.toBlocks₁₁
  set π : (LocRing p)[X] := Polynomial.C ((p : ℕ) : LocRing p)
  let L : Matrix (C ⊕ B) (C ⊕ B) (LocRing p)[X] := Matrix.fromBlocks 1 0 0 L₂ *
    Matrix.fromBlocks 1 0 (-(Bl.toBlocks₂₁ * Q.adjugate)) (Q.det • 1)
  let P : Matrix (C ⊕ B) (C ⊕ B) (LocRing p)[X] :=
    Matrix.fromBlocks 1 (-(Q.adjugate * Bl.toBlocks₁₂)) 0 (Q.det • 1) * Matrix.fromBlocks 1 0 0 P₂
  have hLBP : L * Bl * P = Matrix.fromBlocks Q 0 0 ((Q.det * π) • (L₂ * W * P₂)) := by
    have h := schur_sandwich Q Bl.toBlocks₁₂ Bl.toBlocks₂₁ Bl.toBlocks₂₂ L₂ P₂
    rw [Matrix.fromBlocks_toBlocks] at h
    simp only [L, P]
    rw [h, hW, Matrix.mul_smul, Matrix.smul_mul, smul_smul]
  have hentry : ∀ x y, (L * Bl * P) (Sum.inr x) (Sum.inr y) = Q.det * π * (L₂ * W * P₂) x y := by
    intro x y; rw [hLBP]; simp
  have hcross : ∀ x y, (L * Bl * P) (Sum.inr x) (Sum.inl y) = 0 := by
    intro x y; rw [hLBP]; simp
  have hcross' : ∀ x y, (L * Bl * P) (Sum.inl x) (Sum.inr y) = 0 := by
    intro x y; rw [hLBP]; simp
  have hdetQ : phiP p (Q.det ^ Fintype.card B) ≠ 0 := by
    rw [map_pow]; exact pow_ne_zero _ hQ
  exact
  { Bl := Bl
    hB := hB
    L := L
    P := P
    hL := by
      simp only [L, Matrix.det_mul, Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, one_mul,
        Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_sum]
      rw [map_mul]
      exact mul_ne_zero hL₂ (by simpa using hdetQ)
    hP := by
      simp only [P, Matrix.det_mul, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul,
        Matrix.det_smul, mul_one]
      rw [map_mul]
      exact mul_ne_zero (by simpa using hdetQ) hP₂
    t := borderSet C B
    s := borderSub C s
    hst := by
      intro i hi
      obtain ⟨x, -, rfl⟩ := mem_borderSub hi
      exact Finset.mem_map_of_mem _ (Finset.mem_univ x)
    H1 := by
      intro i hi j
      obtain ⟨x, rfl⟩ := mem_borderSet hi
      rcases j with y | y
      · rw [hcross]; exact dvd_zero _
      · rw [hentry]; exact Dvd.dvd.mul_right (dvd_mul_left _ _) _
    H2 := by
      intro i hi j
      obtain ⟨x, hx, rfl⟩ := mem_borderSub hi
      rcases j with y | y
      · rw [hcross]; exact dvd_zero _
      · rw [hentry, pow_two, mul_assoc]
        exact dvd_mul_of_dvd_right (mul_dvd_mul_left _ (hrow x hx y)) _
    H3 := by
      intro i j hj
      obtain ⟨y, hy, rfl⟩ := mem_borderSub hj
      rcases i with x | x
      · rw [hcross']; exact dvd_zero _
      · rw [hentry]; exact Dvd.dvd.mul_right (dvd_mul_left _ _) _
    H4 := by
      intro i hi j hj
      obtain ⟨x, rfl⟩ := mem_borderSet hi
      obtain ⟨y, hy, rfl⟩ := mem_borderSub hj
      rw [hentry, pow_two, mul_assoc]
      exact dvd_mul_of_dvd_right (mul_dvd_mul_left _ (hcol x y hy)) _
    N₂ := Matrix.of fun i j => Q.det * N₂ (borderSub.pt i) (borderSub.pt j)
    H5 := by
      intro i j
      rw [borderSub.pt_spec i, borderSub.pt_spec j, hentry, hN₂]
      simp only [Matrix.of_apply]
      ring
    hb := by
      have e : (Matrix.of fun i j : borderSub C s =>
          Q.det * N₂ (borderSub.pt i) (borderSub.pt j)).map (phiP p) =
          ((Matrix.diagonal fun _ => phiP p Q.det) * N₂.map (phiP p)).submatrix
            borderSub.pt borderSub.pt := by
        ext i j; simp [Matrix.diagonal_mul]
      rw [e]
      exact ((Matrix.rank_submatrix_le _ _ _).trans (Matrix.rank_mul_le_right _ _)).trans hb }

end CatalanCore.Uniform.Content.UFMember
