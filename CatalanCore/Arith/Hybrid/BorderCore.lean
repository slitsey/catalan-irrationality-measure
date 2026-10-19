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

/-! ### Tropical bordering -/

section TropBorder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Bordering a weight table by one row and column (entries `≤ w`, corner `≤ 2w`) raises the
tropical value by at most `2w`. -/
theorem tropVal_option_le (W2 : Option ι → Option ι → ℕ) (w : ℕ)
    (hr : ∀ i, W2 (some i) none ≤ w) (hc : ∀ j, W2 none (some j) ≤ w)
    (hd : W2 none none ≤ w + w) :
    tropVal W2 ≤ tropVal (fun i j => W2 (some i) (some j)) + (w + w) := by
  apply tropVal_le_of_forall
  intro σ
  rw [Fintype.sum_option]
  have key : ∀ x : ι, W2 (σ (some x)) (some x) ≤
      W2 (some (Equiv.removeNone σ x)) (some x) + (if σ (some x) = none then w else 0) := by
    intro x
    by_cases h : σ (some x) = none
    · rw [if_pos h, h]; have := hc x; omega
    · rw [if_neg h]
      obtain ⟨y, hy⟩ := Option.ne_none_iff_exists'.mp h
      rw [← Equiv.removeNone_some σ ⟨y, hy⟩]
      omega
  have hsum := Finset.sum_le_sum (fun x (_ : x ∈ (Finset.univ : Finset ι)) => key x)
  rw [Finset.sum_add_distrib] at hsum
  have hτ := le_tropVal (fun i j => W2 (some i) (some j)) (Equiv.removeNone σ)
  have hfin : W2 (σ none) none + ∑ x : ι, (if σ (some x) = none then w else 0) ≤ w + w := by
    cases h0 : σ none with
    | none =>
      have : ∑ x : ι, (if σ (some x) = none then w else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro x _
        rw [if_neg]
        intro h
        have : σ (some x) = σ none := by rw [h, h0]
        exact absurd (σ.injective this) (by simp)
      rw [this]; omega
    | some i =>
      have h1 := hr i
      rw [h0] at *
      by_cases hex : ∃ x0, σ (some x0) = none
      · obtain ⟨x0, hx0⟩ := hex
        have : ∑ x : ι, (if σ (some x) = none then w else 0) = w := by
          rw [Finset.sum_eq_single x0]
          · rw [if_pos hx0]
          · intro x _ hne
            rw [if_neg]
            intro h
            exact hne (Option.some_injective _ (σ.injective (by rw [h, hx0])))
          · simp
        rw [this]; omega
      · push Not at hex
        have : ∑ x : ι, (if σ (some x) = none then w else 0) = 0 :=
          Finset.sum_eq_zero fun x _ => if_neg (hex x)
        rw [this]; omega
  omega

variable (p : ℕ) [Fact p.Prime]

/-- **Tropical bordering for `GLE`.** -/
theorem det_gle_border (M : Matrix (Option ι) (Option ι) ℚ[X]) (W : ι → ι → ℕ)
    (hW : ∀ i j, GLE p (W i j) (M (some i) (some j))) (w : ℕ)
    (hr : ∀ i, GLE p w (M (some i) none)) (hc : ∀ j, GLE p w (M none (some j)))
    (hd : GLE p (w + w) (M none none)) :
    GLE p (tropVal W + (w + w)) M.det := by
  let W2 : Option ι → Option ι → ℕ := fun a b =>
    match a, b with
    | some i, some j => W i j
    | some _, none => w
    | none, some _ => w
    | none, none => w + w
  have h2 : GLE p (tropVal W2) M.det := by
    apply det_gle
    rintro (_ | i) (_ | j)
    · exact hd
    · exact hc j
    · exact hr i
    · exact hW i j
  refine h2.mono ?_
  exact tropVal_option_le W2 w (fun i => le_rfl) (fun j => le_rfl) le_rfl

end TropBorder

end CatalanCore.Arith.Hybrid
