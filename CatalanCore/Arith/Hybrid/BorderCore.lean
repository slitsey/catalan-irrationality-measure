module

public import CatalanCore.Arith.Hybrid.RankGLE

@[expose] public section

/-!
# Bordering lemma for the rank principle (MEM2C)

`gle_det_border_of_rank`: let `M` be a square matrix over `ℚ[X]` indexed by `Option ι` (a bordered
matrix: one extra row and column `none`).  Suppose the inner block `M|_{ι×ι}` satisfies the
hypotheses of the rank principle `gle_det_of_rank` (weights `u, v`, integral scaled lift `Bl`, rank
of the reduction `≤ |ι| - k`), and the border entries are `p^w`-integral.  Then
`GLE p (∑u + ∑v + 2w - (k - 1)) (det M)`.

Everything is generic: no frame, no Hybrid data.  A rank-`k` deficit of the inner block costs at
most one unit and the new weights `2w`.
-/

open Polynomial CatalanCore.Basic

namespace CatalanCore.Arith.Hybrid

section RankAdd

variable {K : Type*} [Field K] {m n : Type*} [Fintype n]

theorem matrix_rank_add_le (A B : Matrix m n K) : (A + B).rank ≤ A.rank + B.rank := by
  have h := LinearMap.rank_add_le A.mulVecLin B.mulVecLin
  rw [← Matrix.mulVecLin_add] at h
  have e : ∀ C : Matrix m n K, (C.rank : Cardinal) = LinearMap.rank C.mulVecLin := fun C => by
    unfold Matrix.rank LinearMap.rank
    exact Module.finrank_eq_rank K _
  rw [← e, ← e, ← e] at h
  exact_mod_cast h

end RankAdd

section RankBorder

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The inner block padded by zeros. -/
def borderPad (N : Matrix (Option ι) (Option ι) K) : Matrix (Option ι) (Option ι) K :=
  Matrix.of fun a b => match a, b with
    | some i, some j => N (some i) (some j)
    | _, _ => 0

/-- The border row. -/
def borderRow (N : Matrix (Option ι) (Option ι) K) : Matrix (Option ι) (Option ι) K :=
  Matrix.vecMulVec (Pi.single none 1) (N none)

/-- The border column (without its corner). -/
def borderCol (N : Matrix (Option ι) (Option ι) K) : Matrix (Option ι) (Option ι) K :=
  Matrix.vecMulVec (fun a => match a with | some i => N (some i) none | none => 0)
    (Pi.single none 1)

theorem border_decomp (N : Matrix (Option ι) (Option ι) K) :
    N = borderPad N + borderRow N + borderCol N := by
  ext a b
  rcases a with _ | i <;> rcases b with _ | j <;>
    simp [borderPad, borderRow, borderCol, Matrix.vecMulVec_apply]

theorem rank_borderPad_le (N : Matrix (Option ι) (Option ι) K) :
    (borderPad N).rank ≤ (N.submatrix some some).rank := by
  let L : Matrix (Option ι) ι K := Matrix.of fun a i => if a = some i then 1 else 0
  have : borderPad N = L * (N.submatrix some some) * L.transpose := by
    ext a b
    rcases a with _ | i <;> rcases b with _ | j <;>
      simp [borderPad, L, Matrix.mul_apply, Matrix.submatrix_apply]
  rw [this]
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)

/-- Bordering a matrix by one row and one column raises the rank by at most `2`. -/
theorem matrix_rank_border_le (N : Matrix (Option ι) (Option ι) K) :
    N.rank ≤ (N.submatrix some some).rank + 2 := by
  have h0 := rank_borderPad_le N
  have h1 : (borderRow N).rank ≤ 1 := Matrix.rank_vecMulVec_le _ _
  have h2 : (borderCol N).rank ≤ 1 := Matrix.rank_vecMulVec_le _ _
  have h3 := matrix_rank_add_le (borderPad N) (borderRow N)
  have h4 := matrix_rank_add_le (borderPad N + borderRow N) (borderCol N)
  have h5 : N.rank = (borderPad N + borderRow N + borderCol N).rank :=
    congrArg Matrix.rank (border_decomp N)
  omega

end RankBorder

section Border

variable (p : ℕ) [hp : Fact p.Prime]

/-- **Bordering lemma for the rank principle.** -/
theorem gle_det_border_of_rank {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix (Option ι) (Option ι) ℚ[X]) (Bl : Matrix ι ι (LocRing p)[X]) (u v : ι → ℕ)
    (hB : ∀ i j, toQ p (Bl i j) = C ((p : ℚ) ^ (u i + v j)) * M (some i) (some j)) (k : ℕ)
    (hrk : (Bl.map (phiP p)).rank + k ≤ Fintype.card ι) (w : ℕ)
    (hr : ∀ i, GLE p w (M (some i) none)) (hc : ∀ j, GLE p w (M none (some j)))
    (hd : GLE p (w + w) (M none none)) :
    GLE p (∑ i, u i + ∑ j, v j + (w + w) - (k - 1)) M.det := by
  classical
  let u' : Option ι → ℕ := fun a => a.elim w u
  let v' : Option ι → ℕ := fun a => a.elim w v
  have hlift : ∀ a b, ∃ g : (LocRing p)[X], toQ p g = C ((p : ℚ) ^ (u' a + v' b)) * M a b := by
    intro a b
    apply exists_lift
    rcases a with _ | i <;> rcases b with _ | j
    · simpa [u', v'] using hd
    · simpa [u', v'] using (hc j).mono (Nat.le_add_right _ _)
    · simpa [u', v', add_comm] using (hr i).mono (Nat.le_add_left _ _)
    · have := hB i j
      have hg : GLE p (u i + v j) (M (some i) (some j)) := by
        intro n
        have h1 := congrArg (fun q : ℚ[X] => q.coeff n) this
        simp only [toQ_coeff, coeff_C_mul] at h1
        rw [← h1]
        exact (Bl i j).coeff n |>.2
      simpa [u', v'] using hg
  choose Bl0 hBl' using hlift
  let Bl' : Matrix (Option ι) (Option ι) (LocRing p)[X] := Matrix.of Bl0
  have hinj : Function.Injective (toQ p) :=
    Polynomial.map_injective _ Subtype.val_injective
  have hsub : (Bl'.map (phiP p)).submatrix some some = Bl.map (phiP p) := by
    ext i j
    have : Bl' (some i) (some j) = Bl i j := by
      apply hinj
      rw [show Bl' (some i) (some j) = Bl0 (some i) (some j) from rfl, hBl', hB]
      rfl
    simp [this]
  have hrank : (Bl'.map (phiP p)).rank + (k - 1) ≤ Fintype.card (Option ι) := by
    rw [Fintype.card_option]
    by_cases hk : k = 0
    · subst hk
      have := Matrix.rank_le_card_width (Bl'.map (phiP p))
      simp only [Fintype.card_option] at this
      omega
    · have h2 := matrix_rank_border_le (Bl'.map (phiP p))
      rw [hsub] at h2
      omega
  have := gle_det_of_rank p M Bl' u' v' hBl' (k - 1) hrank
  simpa [Fintype.sum_option, u', v', add_assoc, add_comm, add_left_comm] using this

end Border

end CatalanCore.Arith.Hybrid
