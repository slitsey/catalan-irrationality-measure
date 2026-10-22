module

public import CatalanCore.Arith.Hybrid.RankGLE
public import CatalanCore.Linalg.TwoLevelDet

@[expose] public section

/-!
# The two-level principle for `GLE` (shift-nonclean packages G1, G2)

`RankGLE.gle_det_of_scaled_dvd` is the common bridge: `π^k ∣ det Bl` plus the scaling relation
`toQ Bl = diag(p^u) M diag(p^v)` gives `GLE (∑u + ∑v - k) det M`.  The rank principle feeds the bridge
with `dvd_det_of_rank`; here the two-level principle feeds it with
`TwoLevelDet.two_level_dvd_det_of_primitive_changes`.

* `TwoLevelWit p M b` : a *two-level witness* (integral lift `Bl`, weights `u v`, a row/column set `s`,
  primitive changes of basis `L P` such that `L Bl P` is divisible by `p` along the rows and columns
  of `s`, and the divided `s × s` block has rank `≤ b` modulo `p`).
* `TwoLevelWit.gle` (G1) : `GLE p (∑u + ∑v - (|s| + (|s| - b))) (det M)`.
* `TwoLevelWit.border` and `gle_det_two_level_border` (G2) : bordering by one row and column with
  `GLE w` entries (`GLE 2w` corner) costs exactly `2w + 1` and leaves `s`, `b` unchanged.
  This is the same cost as the production `topC = 2 topW + 1`.
-/

open Polynomial CatalanCore.Basic CatalanCore.Linalg Matrix

namespace CatalanCore.Arith.Hybrid

/-- The chosen quotient by `p` (junk value `0` when `p` does not divide). -/
noncomputable def quotP (p : ℕ) [Fact p.Prime] (x : (LocRing p)[X]) : (LocRing p)[X] := by
  classical
  exact if h : C ((p : ℕ) : LocRing p) ∣ x then h.choose else 0

lemma quotP_spec (p : ℕ) [Fact p.Prime] {x : (LocRing p)[X]} (h : C ((p : ℕ) : LocRing p) ∣ x) :
    C ((p : ℕ) : LocRing p) * quotP p x = x := by
  unfold quotP
  rw [dif_pos h]
  exact h.choose_spec.symm

/-- A two-level witness for the determinant of `M`. -/
structure TwoLevelWit (p : ℕ) [Fact p.Prime] {κ : Type*} [Fintype κ] [DecidableEq κ]
    (M : Matrix κ κ ℚ[X]) (b : ℕ) where
  Bl : Matrix κ κ (LocRing p)[X]
  u : κ → ℕ
  v : κ → ℕ
  hB : ∀ i j, toQ p (Bl i j) = C ((p : ℚ) ^ (u i + v j)) * M i j
  s : Finset κ
  L : Matrix κ κ (LocRing p)[X]
  P : Matrix κ κ (LocRing p)[X]
  hL : phiP p L.det ≠ 0
  hP : phiP p P.det ≠ 0
  hrow : ∀ i ∈ s, ∀ j, C ((p : ℕ) : LocRing p) ∣ (L * Bl * P) i j
  hcol : ∀ i, ∀ j ∈ s, C ((p : ℕ) : LocRing p) ∣ (L * Bl * P) i j
  hH : (Matrix.of fun i j : s => phiP p (quotP p ((L * Bl * P) i j))).rank ≤ b

namespace TwoLevelWit

variable {p : ℕ} [Fact p.Prime] {κ : Type*} [Fintype κ] [DecidableEq κ]
  {M : Matrix κ κ ℚ[X]} {b : ℕ}

/-- The exponent produced by a witness. -/
def cost (W : TwoLevelWit p M b) : ℕ :=
  ∑ i, W.u i + ∑ j, W.v j - (W.s.card + (W.s.card - b))

/-- **G1.** The two-level principle for `GLE`. -/
theorem gle (W : TwoLevelWit p M b) : GLE p W.cost M.det := by
  classical
  let e := Equiv.sumCompl (fun a : κ => a ∈ W.s)
  have hprime : Prime (C ((p : ℕ) : LocRing p) : (LocRing p)[X]) :=
    Polynomial.prime_C_iff.2 (prime_p p)
  set X' := W.L * W.Bl * W.P with hX
  let H : Matrix {a // a ∈ W.s} {a // a ∈ W.s} (LocRing p)[X] :=
    Matrix.of fun i j => quotP p (X' i j)
  let B : Matrix {a // a ∈ W.s} {a // ¬ a ∈ W.s} (LocRing p)[X] :=
    Matrix.of fun i j => quotP p (X' i j)
  let Cm : Matrix {a // ¬ a ∈ W.s} {a // a ∈ W.s} (LocRing p)[X] :=
    Matrix.of fun i j => quotP p (X' i j)
  let D : Matrix {a // ¬ a ∈ W.s} {a // ¬ a ∈ W.s} (LocRing p)[X] :=
    Matrix.of fun i j => X' i j
  have hsub : W.L.submatrix e e * W.Bl.submatrix e e * W.P.submatrix e e = X'.submatrix e e := by
    rw [hX, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
  have hform : X'.submatrix e e = Matrix.fromBlocks (C ((p : ℕ) : LocRing p) • H)
      (C ((p : ℕ) : LocRing p) • B) (C ((p : ℕ) : LocRing p) • Cm) D := by
    refine Matrix.ext fun a c => ?_
    rcases a with i | i <;> rcases c with j | j
    · simp only [Matrix.submatrix_apply, e, Equiv.sumCompl_apply_inl, Matrix.fromBlocks_apply₁₁,
        Matrix.smul_apply, smul_eq_mul, H, Matrix.of_apply]
      exact (quotP_spec p (W.hrow i i.2 j)).symm
    · simp only [Matrix.submatrix_apply, e, Equiv.sumCompl_apply_inl, Equiv.sumCompl_apply_inr,
        Matrix.fromBlocks_apply₁₂, Matrix.smul_apply, smul_eq_mul, B, Matrix.of_apply]
      exact (quotP_spec p (W.hrow i i.2 j)).symm
    · simp only [Matrix.submatrix_apply, e, Equiv.sumCompl_apply_inl, Equiv.sumCompl_apply_inr,
        Matrix.fromBlocks_apply₂₁, Matrix.smul_apply, smul_eq_mul, Cm, Matrix.of_apply]
      exact (quotP_spec p (W.hcol i j j.2)).symm
    · simp [Matrix.submatrix_apply, e, D]
  have hrank : (H.map (phiP p)).rank ≤ b := W.hH
  have hdvd := two_level_dvd_det_of_primitive_changes (phiP p) hprime (phiP_eq_zero_iff p)
    (W.Bl.submatrix e e) (W.L.submatrix e e) (W.P.submatrix e e)
    (by rw [Matrix.det_submatrix_equiv_self]; exact W.hL)
    (by rw [Matrix.det_submatrix_equiv_self]; exact W.hP)
    H B Cm D b hrank (by rw [hsub, hform])
  rw [Matrix.det_submatrix_equiv_self] at hdvd
  have := gle_det_of_scaled_dvd p M W.Bl W.u W.v W.hB _ hdvd
  simpa only [TwoLevelWit.cost, Fintype.card_coe] using this

end TwoLevelWit

/-! ### G2 : the bordered two-level principle -/

/-- A matrix over `Option κ` assembled from an inner block, a column, a row and a corner. -/
def borderMat {κ : Type*} {R : Type*} (B : Matrix κ κ R) (r c : κ → R) (d : R) :
    Matrix (Option κ) (Option κ) R :=
  Matrix.of fun a b => match a, b with
    | some i, some j => B i j
    | some i, none => r i
    | none, some j => c j
    | none, none => d

section BorderMat

variable {κ : Type} {R : Type*} [Fintype κ] [DecidableEq κ] [CommRing R]

/-- Conjugating a bordered matrix by `1`-extended changes of basis. -/
lemma borderMat_sandwich (L P Bl : Matrix κ κ R) (r c : κ → R) (d : R) :
    borderMat L 0 0 1 * borderMat Bl r c d * borderMat P 0 0 1 =
      borderMat (L * Bl * P) (L.mulVec r) (c ᵥ* P) d := by
  ext a b
  rcases a with _ | i <;> rcases b with _ | j <;>
    simp [borderMat, Matrix.mul_apply, Fintype.sum_option, Matrix.mulVec, Matrix.vecMul,
      dotProduct, Finset.sum_mul]

lemma borderMat_det (A : Matrix κ κ R) : (borderMat A 0 0 1).det = A.det := by
  have : borderMat A (0 : κ → R) (0 : κ → R) 1 =
      (Matrix.fromBlocks A 0 0 (1 : Matrix PUnit.{1} PUnit.{1} R)).submatrix
        (Equiv.optionEquivSumPUnit κ) (Equiv.optionEquivSumPUnit κ) := by
    ext a b
    rcases a with _ | i <;> rcases b with _ | j <;>
      simp [borderMat, Equiv.optionEquivSumPUnit]
  rw [this, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁]
  simp

end BorderMat

section Border

variable {p : ℕ} [Fact p.Prime] {κ : Type} [Fintype κ] [DecidableEq κ]

/-- A `GLE c` polynomial scaled by `p^e` with `c < e` lifts to a multiple of `p`. -/
lemma exists_lift_dvd {c e : ℕ} {f : ℚ[X]} (hf : GLE p c f) (h : c + 1 ≤ e) :
    ∃ g : (LocRing p)[X], toQ p g = C ((p : ℚ) ^ e) * f ∧ C ((p : ℕ) : LocRing p) ∣ g := by
  obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
  obtain ⟨g0, hg0⟩ := exists_lift p (hf.mono (show c ≤ e' by omega))
  refine ⟨C ((p : ℕ) : LocRing p) * g0, ?_, dvd_mul_right _ _⟩
  have h1 : toQ p (C ((p : ℕ) : LocRing p)) = C (p : ℚ) := by simp [toQ]
  rw [map_mul, h1, hg0, ← mul_assoc, ← C_mul, pow_succ']

/-- **G2 (existence form).** Bordering a two-level witness by one row and column whose entries are
`GLE w` (corner `GLE 2w`) gives a two-level witness of the bordered matrix with the same `s`, `b`;
the weights grow by `w + 1` (border row) and `w` (border column). -/
theorem exists_border_wit {M : Matrix (Option κ) (Option κ) ℚ[X]} {b : ℕ}
    (W : TwoLevelWit p (Matrix.of fun i j => M (some i) (some j)) b)
    (hu : ∀ i, 1 ≤ W.u i) (w : ℕ)
    (hr : ∀ i, GLE p w (M (some i) none)) (hc : ∀ j, GLE p w (M none (some j)))
    (hd : GLE p (w + w) (M none none)) :
    ∃ W' : TwoLevelWit p M b,
      W'.cost = (∑ i, W.u i + ∑ j, W.v j + (w + 1) + w) - (W.s.card + (W.s.card - b)) := by
  classical
  have h1 : ∀ i, ∃ g : (LocRing p)[X], toQ p g = C ((p : ℚ) ^ (W.u i + w)) * M (some i) none ∧
      C ((p : ℕ) : LocRing p) ∣ g := fun i => exists_lift_dvd (hr i) (by have := hu i; omega)
  have h2 : ∀ j, ∃ g : (LocRing p)[X], toQ p g = C ((p : ℚ) ^ (w + 1 + W.v j)) * M none (some j) ∧
      C ((p : ℕ) : LocRing p) ∣ g := fun j => exists_lift_dvd (hc j) (by omega)
  choose rr hrr1 hrr2 using h1
  choose cc hcc1 hcc2 using h2
  obtain ⟨dd, hdd⟩ := exists_lift p (hd.mono (show w + w ≤ w + 1 + w by omega))
  let emb : κ ↪ Option κ := ⟨some, Option.some_injective _⟩
  refine ⟨{ Bl := borderMat W.Bl rr cc dd
            u := fun a => a.elim (w + 1) W.u
            v := fun a => a.elim w W.v
            hB := ?_
            s := W.s.map emb
            L := borderMat W.L 0 0 1
            P := borderMat W.P 0 0 1
            hL := ?_
            hP := ?_
            hrow := ?_
            hcol := ?_
            hH := ?_ }, ?_⟩
  · intro a c
    rcases a with _ | i <;> rcases c with _ | j
    · simpa [borderMat] using hdd
    · simpa [borderMat] using hcc1 j
    · simpa [borderMat] using hrr1 i
    · simpa [borderMat] using W.hB i j
  · rw [borderMat_det]; exact W.hL
  · rw [borderMat_det]; exact W.hP
  · intro a ha c
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.1 ha
    rw [borderMat_sandwich]
    rcases c with _ | j
    · simp only [borderMat, Matrix.of_apply, Matrix.mulVec, dotProduct]
      exact Finset.dvd_sum fun k _ => Dvd.dvd.mul_left (hrr2 k) _
    · exact W.hrow i hi j
  · intro a c hc'
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.1 hc'
    rw [borderMat_sandwich]
    rcases a with _ | i
    · simp only [borderMat, Matrix.of_apply, Matrix.vecMul, dotProduct]
      exact Finset.dvd_sum fun k _ => Dvd.dvd.mul_right (hcc2 k) _
    · exact W.hcol i j hj
  · let f : W.s → (W.s.map emb) := fun i => ⟨some i.1, Finset.mem_map_of_mem emb i.2⟩
    have hf : Function.Bijective f := by
      constructor
      · intro x y hxy
        exact Subtype.ext (Option.some_injective _ (congrArg Subtype.val hxy))
      · rintro ⟨a, ha⟩
        obtain ⟨i, hi, rfl⟩ := Finset.mem_map.1 ha
        exact ⟨⟨i, hi⟩, rfl⟩
    let ef := Equiv.ofBijective f hf
    rw [← Matrix.rank_submatrix _ ef ef]
    convert W.hH using 2
    refine Matrix.ext fun i j => ?_
    show phiP p (quotP p ((borderMat W.L 0 0 1 * borderMat W.Bl rr cc dd *
      borderMat W.P 0 0 1) (some i.1) (some j.1))) = phiP p (quotP p ((W.L * W.Bl * W.P) i.1 j.1))
    rw [borderMat_sandwich]
    rfl
  · simp only [TwoLevelWit.cost, Fintype.sum_option, Option.elim, Finset.card_map]
    omega

/-- **G2.** The bordered two-level principle: the cost of the border is exactly `2w + 1`
(`topC = 2 topW + 1` when `w = topW`), whatever the first-level data. -/
theorem gle_det_two_level_border {M : Matrix (Option κ) (Option κ) ℚ[X]} {b : ℕ}
    (W : TwoLevelWit p (Matrix.of fun i j => M (some i) (some j)) b)
    (hu : ∀ i, 1 ≤ W.u i) (w : ℕ)
    (hr : ∀ i, GLE p w (M (some i) none)) (hc : ∀ j, GLE p w (M none (some j)))
    (hd : GLE p (w + w) (M none none))
    (hk : W.s.card + (W.s.card - b) ≤ ∑ i, W.u i + ∑ j, W.v j) :
    GLE p (W.cost + (w + w + 1)) M.det := by
  obtain ⟨W', hW'⟩ := exists_border_wit W hu w hr hc hd
  have e : W.cost + (w + w + 1) =
      (∑ i, W.u i + ∑ j, W.v j + (w + 1) + w) - (W.s.card + (W.s.card - b)) := by
    unfold TwoLevelWit.cost; omega
  rw [e, ← hW']
  exact W'.gle

end Border

end CatalanCore.Arith.Hybrid

#print axioms CatalanCore.Arith.Hybrid.TwoLevelWit.gle
#print axioms CatalanCore.Arith.Hybrid.gle_det_two_level_border
#print axioms CatalanCore.Arith.Hybrid.gle_det_of_rank
