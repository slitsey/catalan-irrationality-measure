module

public import CatalanCore.Uniform.Content.Hybrid.Frame
public import Mathlib.Data.Matrix.Block
public import Mathlib.Logic.Equiv.Fintype

@[expose] public section

/-!
# Global kernel bases from per-fiber local data

At growing `N` the exact unit changes of basis `L, P` of UC4 are assembled from LOCAL data on the
residue fibers.  Rows of `Φ` are identified with `Σ x, Tr x` (fiber `x`, local row index) by
`er : ι ≃ Σ x, Tr x`, columns with `Σ x, Tc x` by `ec`.  If the leading matrix vanishes across
fibers, then `K` is the reindexed block diagonal of its local blocks `K_x`.  Given, on each fiber,
local `L_x, P_x` with local inverses over `ℤ_(p)` and local kill sets with `L_x K_x P_x` vanishing
on them (`BlockKernel`), the global

  `L = blockdiag(L_x)`,  `P = blockdiag(P_x)·π`,  `s = ⋃ (killed local rows)`

form valid UC4 data: `L, P` are units mod `p`, `L K P` vanishes on the rows and columns of `s`
(the permutation `π` matches the column kill set to `s`; only the total counts must agree), and
every kernel row/column is supported in one fiber.  `BlockKernel.gle_det_frame` is the frame price
with these data.
-/

open Polynomial CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid Finset Module Matrix

namespace CatalanCore.Uniform.Content.Hybrid

section Block

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]
  {Fb : Type*} [Fintype Fb] [DecidableEq Fb]

/-- A block-diagonal matrix, reindexed to `ι`. -/
def blockMat {Tr Tc : Fb → Type*} (er : ι ≃ Σ x, Tr x) (ec : ι ≃ Σ x, Tc x)
    (M : ∀ x, Matrix (Tr x) (Tc x) R) : Matrix ι ι R :=
  (blockDiagonal' M).submatrix er ec

lemma blockMat_mul {Tr Tm Tc : Fb → Type*} [∀ x, Fintype (Tm x)]
    (er : ι ≃ Σ x, Tr x) (em : ι ≃ Σ x, Tm x) (ec : ι ≃ Σ x, Tc x)
    (A : ∀ x, Matrix (Tr x) (Tm x) R) (B : ∀ x, Matrix (Tm x) (Tc x) R) :
    blockMat er em A * blockMat em ec B = blockMat er ec (fun x => A x * B x) := by
  unfold blockMat
  rw [submatrix_mul_equiv, blockDiagonal'_mul]

lemma blockMat_one {T : Fb → Type*} [∀ x, Fintype (T x)] [∀ x, DecidableEq (T x)]
    (e : ι ≃ Σ x, T x) : blockMat e e (fun x => (1 : Matrix (T x) (T x) R)) = 1 := by
  unfold blockMat
  rw [show (fun x => (1 : Matrix (T x) (T x) R)) = 1 from rfl, blockDiagonal'_one,
    submatrix_one_equiv]

lemma isUnit_det_blockMat {T : Fb → Type*} [∀ x, Fintype (T x)] [∀ x, DecidableEq (T x)]
    (e : ι ≃ Σ x, T x) (A B : ∀ x, Matrix (T x) (T x) R) (h : ∀ x, A x * B x = 1) :
    IsUnit (blockMat e e A).det := by
  have hm : blockMat e e A * blockMat e e B = 1 := by
    rw [blockMat_mul, show (fun x => A x * B x) = fun x => 1 from funext h, blockMat_one]
  have := congrArg Matrix.det hm
  rw [det_mul, det_one] at this
  exact isUnit_iff_exists_inv.2 ⟨_, this⟩

lemma blockMat_apply_sym {Tr Tc : Fb → Type*} (er : ι ≃ Σ x, Tr x) (ec : ι ≃ Σ x, Tc x)
    (M : ∀ x, Matrix (Tr x) (Tc x) R) (x y : Fb) (t : Tr x) (c : Tc y) :
    blockMat er ec M (er.symm ⟨x, t⟩) (ec.symm ⟨y, c⟩) =
      if h : x = y then M x t (h ▸ c) else 0 := by
  unfold blockMat
  rw [submatrix_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply, blockDiagonal'_apply']
  by_cases h : x = y
  · subst h; simp
  · simp [h]

lemma blockMat_fiber {Tr Tc : Fb → Type*} (er : ι ≃ Σ x, Tr x) (ec : ι ≃ Σ x, Tc x)
    (M : ∀ x, Matrix (Tr x) (Tc x) R) {i j : ι} (h : blockMat er ec M i j ≠ 0) :
    (er i).1 = (ec j).1 := by
  obtain ⟨⟨x, t⟩, rfl⟩ := er.symm.surjective i
  obtain ⟨⟨y, c⟩, rfl⟩ := ec.symm.surjective j
  rw [blockMat_apply_sym] at h
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  by_contra hxy
  exact h (dif_neg hxy)

lemma blockMat_row_zero {Tr Tc : Fb → Type*} (er : ι ≃ Σ x, Tr x) (ec : ι ≃ Σ x, Tc x)
    (M : ∀ x, Matrix (Tr x) (Tc x) R) (kr : ∀ x, Finset (Tr x))
    (h : ∀ x t c, t ∈ kr x → M x t c = 0) {i : ι} (hi : (er i).2 ∈ kr (er i).1) (j : ι) :
    blockMat er ec M i j = 0 := by
  obtain ⟨⟨x, t⟩, rfl⟩ := er.symm.surjective i
  obtain ⟨⟨y, c⟩, rfl⟩ := ec.symm.surjective j
  rw [Equiv.apply_symm_apply] at hi
  rw [blockMat_apply_sym]
  split_ifs with hxy
  · exact h x t _ hi
  · rfl

lemma blockMat_col_zero {Tr Tc : Fb → Type*} (er : ι ≃ Σ x, Tr x) (ec : ι ≃ Σ x, Tc x)
    (M : ∀ x, Matrix (Tr x) (Tc x) R) (kc : ∀ x, Finset (Tc x))
    (h : ∀ x t c, c ∈ kc x → M x t c = 0) (i : ι) {j : ι} (hj : (ec j).2 ∈ kc (ec j).1) :
    blockMat er ec M i j = 0 := by
  obtain ⟨⟨x, t⟩, rfl⟩ := er.symm.surjective i
  obtain ⟨⟨y, c⟩, rfl⟩ := ec.symm.surjective j
  rw [Equiv.apply_symm_apply] at hj
  rw [blockMat_apply_sym]
  split_ifs with hxy
  · subst hxy; exact h x t c hj
  · rfl

/-- The local blocks of a matrix. -/
def localK {Tr Tc : Fb → Type*} (er : ι ≃ Σ x, Tr x) (ec : ι ≃ Σ x, Tc x) (K : Matrix ι ι R)
    (x : Fb) : Matrix (Tr x) (Tc x) R :=
  Matrix.of fun t c => K (er.symm ⟨x, t⟩) (ec.symm ⟨x, c⟩)

/-- A matrix vanishing across fibers is the block diagonal of its local blocks. -/
lemma eq_blockMat {Tr Tc : Fb → Type*} (er : ι ≃ Σ x, Tr x) (ec : ι ≃ Σ x, Tc x)
    (K : Matrix ι ι R) (hcross : ∀ i j, (er i).1 ≠ (ec j).1 → K i j = 0) :
    K = blockMat er ec (localK er ec K) := by
  ext i j
  obtain ⟨⟨x, t⟩, rfl⟩ := er.symm.surjective i
  obtain ⟨⟨y, c⟩, rfl⟩ := ec.symm.surjective j
  rw [blockMat_apply_sym]
  split_ifs with hxy
  · subst hxy; rfl
  · apply hcross
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]; exact hxy

lemma mul_submatrix_perm (A B : Matrix ι ι R) (π : Equiv.Perm ι) :
    A * B.submatrix id π = (A * B).submatrix id π := by
  ext i j; simp [Matrix.mul_apply]

end Block

/-! ### Local kernel data -/

variable {p : ℕ} [hp : Fact p.Prime] {ι : Type*} [Fintype ι] [DecidableEq ι]
  {Fb : Type*} [Fintype Fb] [DecidableEq Fb]
  {Tr Tc : Fb → Type*} [∀ x, Fintype (Tr x)] [∀ x, DecidableEq (Tr x)]
  [∀ x, Fintype (Tc x)] [∀ x, DecidableEq (Tc x)]

/-- Per-fiber exact kernel data for UC4. -/
structure BlockKernel (p : ℕ) [Fact p.Prime] (er : ι ≃ Σ x, Tr x) (ec : ι ≃ Σ x, Tc x)
    (K : Matrix ι ι (LocRing p)) where
  Lx : ∀ x, Matrix (Tr x) (Tr x) (LocRing p)
  Lx' : ∀ x, Matrix (Tr x) (Tr x) (LocRing p)
  Px : ∀ x, Matrix (Tc x) (Tc x) (LocRing p)
  Px' : ∀ x, Matrix (Tc x) (Tc x) (LocRing p)
  hLx : ∀ x, Lx x * Lx' x = 1
  hPx : ∀ x, Px x * Px' x = 1
  kr : ∀ x, Finset (Tr x)
  kc : ∀ x, Finset (Tc x)
  hrow : ∀ x t c, t ∈ kr x → (Lx x * localK er ec K x * Px x) t c = 0
  hcol : ∀ x t c, c ∈ kc x → (Lx x * localK er ec K x * Px x) t c = 0
  hcross : ∀ i j, (er i).1 ≠ (ec j).1 → K i j = 0
  hcard : (univ.filter fun i => (er i).2 ∈ kr (er i).1).card =
    (univ.filter fun j => (ec j).2 ∈ kc (ec j).1).card

namespace BlockKernel

variable {er : ι ≃ Σ x, Tr x} {ec : ι ≃ Σ x, Tc x} {K : Matrix ι ι (LocRing p)}
  (BK : BlockKernel p er ec K)

/-- Killed rows. -/
def s : Finset ι := univ.filter fun i => (er i).2 ∈ BK.kr (er i).1

/-- Killed columns (before matching). -/
def sc : Finset ι := univ.filter fun j => (ec j).2 ∈ BK.kc (ec j).1

/-- A permutation carrying `s` onto the killed columns. -/
noncomputable def perm : Equiv.Perm ι :=
  (Fintype.equivOfCardEq (by rw [Fintype.card_coe, Fintype.card_coe]; exact BK.hcard) :
    {i // i ∈ BK.s} ≃ {j // j ∈ BK.sc}).extendSubtype

lemma perm_mem (j : ι) : BK.perm j ∈ BK.sc ↔ j ∈ BK.s := by
  constructor
  · intro h
    by_contra hj
    exact Equiv.extendSubtype_not_mem _ j hj h
  · intro hj
    exact Equiv.extendSubtype_mem _ j hj

/-- Global `L`. -/
def L : Matrix ι ι (LocRing p) := blockMat er er BK.Lx

/-- Global `P` (columns matched to `s`). -/
noncomputable def P : Matrix ι ι (LocRing p) := (blockMat ec ec BK.Px).submatrix id BK.perm

lemma LKP_eq : BK.L * K * BK.P =
    (blockMat er ec (fun x => BK.Lx x * localK er ec K x * BK.Px x)).submatrix id BK.perm := by
  have hK := congrArg (fun M => BK.L * M * blockMat ec ec BK.Px) (eq_blockMat er ec K BK.hcross)
  rw [P, mul_submatrix_perm, hK, L, blockMat_mul, blockMat_mul]

lemma redQ_ne_zero_of_isUnit {x : LocRing p} (h : IsUnit x) : redQ p x ≠ 0 :=
  (h.map (redQ p)).ne_zero

lemma hL : redQ p BK.L.det ≠ 0 :=
  redQ_ne_zero_of_isUnit (isUnit_det_blockMat er BK.Lx BK.Lx' BK.hLx)

lemma hP : redQ p BK.P.det ≠ 0 := by
  rw [P, det_permute']
  refine redQ_ne_zero_of_isUnit (IsUnit.mul ?_ (isUnit_det_blockMat ec BK.Px BK.Px' BK.hPx))
  rcases Int.units_eq_one_or (Equiv.Perm.sign BK.perm) with h | h <;> rw [h] <;> simp

lemma hrow' : ∀ i ∈ BK.s, ∀ j, (BK.L * K * BK.P) i j = 0 := by
  intro i hi j
  rw [LKP_eq, submatrix_apply]
  exact blockMat_row_zero er ec _ BK.kr BK.hrow (by simpa [s] using hi) _

lemma hcol' : ∀ i, ∀ j ∈ BK.s, (BK.L * K * BK.P) i j = 0 := by
  intro i j hj
  rw [LKP_eq, submatrix_apply]
  have := (BK.perm_mem j).2 hj
  exact blockMat_col_zero er ec _ BK.kc BK.hcol i (by simpa [sc] using this)

lemma supp_row {i k : ι} (h : redQ p (BK.L i k) ≠ 0) : (er k).1 = (er i).1 := by
  have h' : BK.L i k ≠ 0 := fun h0 => h (by rw [h0, map_zero])
  exact (blockMat_fiber er er BK.Lx h').symm

lemma supp_col {l j : ι} (h : redQ p (BK.P l j) ≠ 0) : (ec l).1 = (ec (BK.perm j)).1 := by
  have h' : BK.P l j ≠ 0 := fun h0 => h (by rw [h0, map_zero])
  exact blockMat_fiber ec ec BK.Px h'

end BlockKernel

variable {a b : ι → ℕ} {B : ℕ} {f e : ℕ → ℚ}

open scoped Classical in
/-- **Frame price from per-fiber kernel data.** Fibers are labelled by `res : Fb → ZMod p`
(row residues `a i ≡ res (er i).1`, column residues `b j ≡ res (ec j).1`). -/
theorem BlockKernel.gle_det_frame {er : ι ≃ Σ x, Tr x} {ec : ι ≃ Σ x, Tc x}
    (PS : PoleSplit p B f e) (hd : DigitHyp p B a b) (BK : BlockKernel p er ec (PS.K a b))
    (res : Fb → ZMod p) (hra : ∀ i, (a i : ZMod p) = res (er i).1)
    (hrb : ∀ j, (b j : ZMod p) = res (ec j).1)
    (R0 : ℕ) (hR : R0 + BK.s.card = Fintype.card ι)
    (Vs : Submodule (RatFunc (ZMod p)) (RatFunc (ZMod p) × RatFunc (ZMod p)))
    (cost : Cond (fun i : BK.s => rfH p (res (er i).1))
      (fun j : BK.s => rfH p (res (ec (BK.perm j)).1)) → ℕ)
    (hcost : ∀ c, finrank (RatFunc (ZMod p)) (LinearMap.range (condMap
        (fun i : BK.s => rfH p (res (er i).1))
        (fun i => mapPair (rfH p) (load (fun k => PS.lf (a k)) (fun k => redQ p (BK.L i k))))
        (fun j : BK.s => rfH p (res (ec (BK.perm j)).1))
        (fun j => mapPair (rfH p) (load (fun l => PS.lf (b l)) (fun l => redQ p (BK.P l j))))
        Vs c)) ≤ cost c) :
    GLE p (Fintype.card ι + R0 -
      (Fintype.card {j : BK.s // load (fun l => PS.lf (b l)) (fun l => redQ p (BK.P l j)) = 0} +
        ((colRes (fun j : BK.s => rfH p (res (ec (BK.perm j)).1))).card *
          finrank (RatFunc (ZMod p)) Vs - ∑ c, cost c))) (loewner a b f e).det :=
  CatalanCore.Uniform.Content.Hybrid.gle_det_frame PS hd BK.L BK.P BK.hL BK.hP BK.s
    BK.hrow' BK.hcol' (fun i => res (er i).1) (fun j => res (ec (BK.perm j)).1)
    (fun i k h => by rw [hra, BK.supp_row h])
    (fun j l h => by rw [hrb, BK.supp_col h])
    R0 hR Vs cost hcost

end CatalanCore.Uniform.Content.Hybrid
