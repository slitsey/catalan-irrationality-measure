module

public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NoncommRing

/-!
# The pivotal transform: displacement and bordering (lane H, wave H2b; ledger P201, P205, P214)

`PLANE2-ROW-SIMPLIFICATION-2026-11-07` §2, over any commutative ring `R`, with no division and no
valuation.  Let `H` be a matrix on `(Ω ⊕ I) × (Ω ⊕ J)` whose pivot block `Q = H[Ω,Ω]` has an inverse `Z`,
and suppose `(a_r - b_c) H(r,c) = φ_r - ψ_c` (the displacement identity of a Löwner matrix, valid
whatever the diagonal; this is `IsDisp`).  The pivotal transform is
`Sw = [[T, h], [h', -Z]]` on `(I ⊕ Ω) × (J ⊕ Ω)`, `T = W - V Z U`, `h = V Z`, `h' = Z U`.

* `pivot_displacement` (P201, P214): with the generators `R0, R1` (rows) and `C0, C1` (columns)
  built from `A = Z𝟏`, `B = Zφ`, `A' = Zᵀ𝟏`, `B' = Zᵀψ`, `a = 𝟏 - VA`, `b̂ = φ - VB`, `a' = 𝟏 - UᵀA'`,
  `b̂' = ψ - UᵀB'`, every entry satisfies
  `(node r - node c) Sw(r,c) = R0 r C0 c - R1 r C1 c`.  The four identities of the sweep (for `Z`, `h`, `h'`,
  `T`) are the four blocks, each from `D_ρ Q - Q D_γ = φ𝟏ᵀ - 𝟏ψᵀ` multiplied through by `Z`
  (`I1` to `I4`).
* `jacobi` (P205, P214): for sets `A`, `A'` of deleted pivot rows and columns and any pairings, the
  minor `H[(Ω∖A) ⊕ I, (Ω∖A') ⊕ J]` is associated to the label minor `Sw[I ⊕ A', J ⊕ A]`.  Proof: border
  the matrix by unit columns on `A` and unit rows on `A'` (`Nhat`); the bordered determinant is the minor
  (`det_NT`, a triangular block form), and one Schur complement of `Q` (`Matrix.det_fromBlocks₁₁`) gives
  `det Q` times the label minor up to the signs `sgnL`, `sgnC` (`schur_block`).  `jacobi_L` is the form
  with minors indexed by one type `L` through inclusions.
-/
@[expose] public section

open Matrix

namespace CatalanCore.Uniform.Content.Sweep.Schur

variable {R : Type*} [CommRing R] {Ω I J : Type*} [Fintype Ω] [DecidableEq Ω]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-! ### The pivot blocks and the transform -/

section Blocks

variable (H : Matrix (Ω ⊕ I) (Ω ⊕ J) R) (Z : Matrix Ω Ω R)

/-- The pivot block `Q = H[Ω,Ω]`. -/
def Qm : Matrix Ω Ω R := H.submatrix Sum.inl Sum.inl
def Um : Matrix Ω J R := H.submatrix Sum.inl Sum.inr
def Vm : Matrix I Ω R := H.submatrix Sum.inr Sum.inl
def Wm : Matrix I J R := H.submatrix Sum.inr Sum.inr

/-- `T = W - V Z U`, `h = V Z`, `h' = Z U`. -/
def Tm : Matrix I J R := Wm H - Vm H * Z * Um H
def hm : Matrix I Ω R := Vm H * Z
def hm' : Matrix Ω J R := Z * Um H

/-- The pivotal transform `Sw = [[T, h],[h', -Z]]` on `(I ⊕ Ω) × (J ⊕ Ω)`: rows `I` and the pivot
columns `t`, columns `J` and the pivot rows `s`. -/
def Sw : Matrix (I ⊕ Ω) (J ⊕ Ω) R := Matrix.fromBlocks (Tm H Z) (hm H Z) (hm' H Z) (-Z)

end Blocks

/-! ### The generators and the displacement of the transform -/

section Displacement

variable (H : Matrix (Ω ⊕ I) (Ω ⊕ J) R) (Z : Matrix Ω Ω R)
  (a : Ω ⊕ I → R) (b : Ω ⊕ J → R) (φ : Ω ⊕ I → R) (ψ : Ω ⊕ J → R)

/-- `A = Z 𝟏`, `B = Z φ` on the pivot columns; `A' = Zᵀ 𝟏`, `B' = Zᵀ ψ` on the pivot rows. -/
def gA : Ω → R := Z *ᵥ (fun _ => 1)
def gB : Ω → R := Z *ᵥ (φ ∘ Sum.inl)
def gA' : Ω → R := (fun _ => 1) ᵥ* Z
def gB' : Ω → R := (ψ ∘ Sum.inl) ᵥ* Z

/-- Row-type generators: `(b̂, a)`. -/
def R0 : I ⊕ Ω → R := Sum.elim (fun z => φ (Sum.inr z) - (Vm H *ᵥ gB Z φ) z) (gB Z φ)
def R1 : I ⊕ Ω → R := Sum.elim (fun z => 1 - (Vm H *ᵥ gA Z) z) (gA Z)
/-- Column-type generators: `(a', b̂')`. -/
def C0 : J ⊕ Ω → R := Sum.elim (fun y => 1 - (gA' Z ᵥ* Um H) y) (gA' Z)
def C1 : J ⊕ Ω → R := Sum.elim (fun y => ψ (Sum.inr y) - (gB' Z ψ ᵥ* Um H) y) (gB' Z ψ)

/-- Node values of the row labels (`a_z`, `b_t`) and of the column labels (`b_y`, `a_s`). -/
def nodeR : I ⊕ Ω → R := Sum.elim (a ∘ Sum.inr) (b ∘ Sum.inl)
def nodeC : J ⊕ Ω → R := Sum.elim (b ∘ Sum.inr) (a ∘ Sum.inl)

/-- The displacement identity of the whole matrix. -/
def IsDisp : Prop := ∀ r c, (a r - b c) * H r c = φ r - ψ c

variable {H Z a b φ ψ}

theorem disp_blocks (hd : IsDisp H a b φ ψ) :
    (diagonal (a ∘ Sum.inl) * Qm H - Qm H * diagonal (b ∘ Sum.inl) =
        vecMulVec (φ ∘ Sum.inl) (fun _ => 1) - vecMulVec (fun _ => 1) (ψ ∘ Sum.inl)) ∧
    (diagonal (a ∘ Sum.inl) * Um H - Um H * diagonal (b ∘ Sum.inr) =
        vecMulVec (φ ∘ Sum.inl) (fun _ => 1) - vecMulVec (fun _ => 1) (ψ ∘ Sum.inr)) ∧
    (diagonal (a ∘ Sum.inr) * Vm H - Vm H * diagonal (b ∘ Sum.inl) =
        vecMulVec (φ ∘ Sum.inr) (fun _ => 1) - vecMulVec (fun _ => 1) (ψ ∘ Sum.inl)) ∧
    (diagonal (a ∘ Sum.inr) * Wm H - Wm H * diagonal (b ∘ Sum.inr) =
        vecMulVec (φ ∘ Sum.inr) (fun _ => 1) - vecMulVec (fun _ => 1) (ψ ∘ Sum.inr)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext i j
    simp [Qm, diagonal_mul, mul_diagonal, vecMulVec_apply]
    linear_combination hd (Sum.inl i) (Sum.inl j)
  · ext i j
    simp [Um, diagonal_mul, mul_diagonal, vecMulVec_apply]
    linear_combination hd (Sum.inl i) (Sum.inr j)
  · ext i j
    simp [Vm, diagonal_mul, mul_diagonal, vecMulVec_apply]
    linear_combination hd (Sum.inr i) (Sum.inl j)
  · ext i j
    simp [Wm, diagonal_mul, mul_diagonal, vecMulVec_apply]
    linear_combination hd (Sum.inr i) (Sum.inr j)






variable {H : Matrix (Ω ⊕ I) (Ω ⊕ J) R} {Z : Matrix Ω Ω R}
  {a : Ω ⊕ I → R} {b : Ω ⊕ J → R} {φ : Ω ⊕ I → R} {ψ : Ω ⊕ J → R}

theorem rank_two_mul (M : Matrix Ω Ω R) (x y : Ω → R) (N : Matrix Ω Ω R) :
    M * (vecMulVec x (fun _ => 1) - vecMulVec (fun _ => 1) y) * N =
      vecMulVec (M *ᵥ x) ((fun _ => 1) ᵥ* N) - vecMulVec (M *ᵥ (fun _ => 1)) (y ᵥ* N) := by
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_vecMulVec, Matrix.mul_vecMulVec,
    Matrix.vecMulVec_mul, Matrix.vecMulVec_mul]

/-- (I1): `Z D_ρ - D_γ Z = B A'ᵀ - A B'ᵀ`. -/
theorem I1 (hd : IsDisp H a b φ ψ) (hZ1 : Qm H * Z = 1) (hZ2 : Z * Qm H = 1) :
    Z * diagonal (a ∘ Sum.inl) - diagonal (b ∘ Sum.inl) * Z =
      vecMulVec (gB Z φ) (gA' Z) - vecMulVec (gA Z) (gB' Z ψ) := by
  have h1 := (disp_blocks hd).1
  have e : Z * (diagonal (a ∘ Sum.inl) * Qm H - Qm H * diagonal (b ∘ Sum.inl)) * Z =
      Z * diagonal (a ∘ Sum.inl) - diagonal (b ∘ Sum.inl) * Z := by
    have : Z * (diagonal (a ∘ Sum.inl) * Qm H - Qm H * diagonal (b ∘ Sum.inl)) * Z =
        Z * diagonal (a ∘ Sum.inl) * (Qm H * Z) - (Z * Qm H) * diagonal (b ∘ Sum.inl) * Z := by
      noncomm_ring
    rw [this, hZ1, hZ2]; simp
  rw [← e, h1]
  have := rank_two_mul Z (φ ∘ Sum.inl) (ψ ∘ Sum.inl) Z
  rw [this]; rfl




theorem vecMulVec_sub_left (x y : Ω → R) (z : Ω → R) :
    vecMulVec (x - y) z = vecMulVec x z - vecMulVec y z := by
  ext i j; simp [vecMulVec_apply]; ring

/-- (I2): `D_I h - h D_ρ = b̂ A'ᵀ - a B'ᵀ` for `h = V Z`. -/
theorem I2 (hd : IsDisp H a b φ ψ) (hZ1 : Qm H * Z = 1) (hZ2 : Z * Qm H = 1) :
    diagonal (a ∘ Sum.inr) * hm H Z - hm H Z * diagonal (a ∘ Sum.inl) =
      vecMulVec (R0 H Z φ ∘ Sum.inl) (gA' Z) - vecMulVec (R1 H Z ∘ Sum.inl) (gB' Z ψ) := by
  have h3 := (disp_blocks hd).2.2.1
  have e1 := I1 hd hZ1 hZ2
  have e : diagonal (a ∘ Sum.inr) * hm H Z - hm H Z * diagonal (a ∘ Sum.inl) =
      (diagonal (a ∘ Sum.inr) * Vm H - Vm H * diagonal (b ∘ Sum.inl)) * Z +
        Vm H * (diagonal (b ∘ Sum.inl) * Z - Z * diagonal (a ∘ Sum.inl)) := by
    unfold hm; simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]; abel
  rw [e, h3]
  have e2 : diagonal (b ∘ Sum.inl) * Z - Z * diagonal (a ∘ Sum.inl) =
      -(Z * diagonal (a ∘ Sum.inl) - diagonal (b ∘ Sum.inl) * Z) := by abel
  rw [e2, e1, Matrix.sub_mul, Matrix.vecMulVec_mul, Matrix.vecMulVec_mul]
  ext z s
  simp [vecMulVec_apply, R0, R1, gA', gB', Matrix.mul_sub, Matrix.mul_vecMulVec, vecMulVec_apply]
  ring




/-- (I3): `D_γ h' - h' D_J = B a'ᵀ - A b̂'ᵀ` for `h' = Z U`. -/
theorem I3 (hd : IsDisp H a b φ ψ) (hZ1 : Qm H * Z = 1) (hZ2 : Z * Qm H = 1) :
    diagonal (b ∘ Sum.inl) * hm' H Z - hm' H Z * diagonal (b ∘ Sum.inr) =
      vecMulVec (R0 H Z φ ∘ Sum.inr) (C0 H Z ∘ Sum.inl) -
        vecMulVec (R1 H Z ∘ Sum.inr) (C1 H Z ψ ∘ Sum.inl) := by
  have h2 := (disp_blocks hd).2.1
  have e1 := I1 hd hZ1 hZ2
  have e : diagonal (b ∘ Sum.inl) * hm' H Z - hm' H Z * diagonal (b ∘ Sum.inr) =
      -(Z * diagonal (a ∘ Sum.inl) - diagonal (b ∘ Sum.inl) * Z) * Um H +
        Z * (diagonal (a ∘ Sum.inl) * Um H - Um H * diagonal (b ∘ Sum.inr)) := by
    unfold hm'; simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.neg_mul, Matrix.mul_assoc]; abel
  rw [e, h2, e1, Matrix.neg_mul, Matrix.sub_mul, Matrix.vecMulVec_mul, Matrix.vecMulVec_mul,
    Matrix.mul_sub, Matrix.mul_vecMulVec, Matrix.mul_vecMulVec]
  ext t y
  simp [vecMulVec_apply, R0, R1, C0, C1, gA, gB, gA', gB']
  ring

/-- (I4): `D_I T - T D_J = b̂ a'ᵀ - a b̂'ᵀ` for `T = W - V Z U`. -/
theorem I4 (hd : IsDisp H a b φ ψ) (hZ1 : Qm H * Z = 1) (hZ2 : Z * Qm H = 1) :
    diagonal (a ∘ Sum.inr) * Tm H Z - Tm H Z * diagonal (b ∘ Sum.inr) =
      vecMulVec (R0 H Z φ ∘ Sum.inl) (C0 H Z ∘ Sum.inl) -
        vecMulVec (R1 H Z ∘ Sum.inl) (C1 H Z ψ ∘ Sum.inl) := by
  have h2 := (disp_blocks hd).2.1
  have h3 := (disp_blocks hd).2.2.1
  have h4 := (disp_blocks hd).2.2.2
  have e1 := I1 hd hZ1 hZ2
  have e : diagonal (a ∘ Sum.inr) * Tm H Z - Tm H Z * diagonal (b ∘ Sum.inr) =
      (diagonal (a ∘ Sum.inr) * Wm H - Wm H * diagonal (b ∘ Sum.inr)) -
        ((diagonal (a ∘ Sum.inr) * Vm H - Vm H * diagonal (b ∘ Sum.inl)) * Z * Um H -
          Vm H * (Z * diagonal (a ∘ Sum.inl) - diagonal (b ∘ Sum.inl) * Z) * Um H +
          Vm H * Z * (diagonal (a ∘ Sum.inl) * Um H - Um H * diagonal (b ∘ Sum.inr))) := by
    unfold Tm; simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]; abel
  rw [e, h4, h3, h2, e1]
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.vecMulVec_mul, Matrix.mul_vecMulVec,
    Matrix.mul_assoc]
  ext z y
  simp [vecMulVec_apply, R0, R1, C0, C1, gA, gB, gA', gB', Matrix.mulVec_mulVec, Matrix.vecMul_vecMul,
    Matrix.mul_vecMulVec, Matrix.vecMulVec_mul]
  ring




/-- **The displacement of the transform** (Lemmas 1 and 5 of the sweep, rectangular): for every row label
`r ∈ I ⊕ Ω` and column label `c ∈ J ⊕ Ω`,
`(node r - node c) · Sw(r, c) = R0 r · C0 c - R1 r · C1 c`. -/
theorem pivot_displacement (hd : IsDisp H a b φ ψ) (hZ1 : Qm H * Z = 1) (hZ2 : Z * Qm H = 1)
    (r : I ⊕ Ω) (c : J ⊕ Ω) :
    (nodeR a b r - nodeC a b c) * Sw H Z r c =
      R0 H Z φ r * C0 H Z c - R1 H Z r * C1 H Z ψ c := by
  rcases r with z | t <;> rcases c with y | s
  · have := congrArg (fun M => M z y) (I4 hd hZ1 hZ2)
    simp [Matrix.sub_apply, diagonal_mul, mul_diagonal, vecMulVec_apply] at this
    simp only [Sw, nodeR, nodeC, Matrix.fromBlocks_apply₁₁, Sum.elim_inl, Function.comp_apply]
    simp only [R0, R1, C0, C1, Sum.elim_inl]
    try simp only [R0, R1, C0, C1, Sum.elim_inl, Sum.elim_inr] at this
    linear_combination this
  · have := congrArg (fun M => M z s) (I2 hd hZ1 hZ2)
    simp [Matrix.sub_apply, diagonal_mul, mul_diagonal, vecMulVec_apply] at this
    simp only [Sw, nodeR, nodeC, Matrix.fromBlocks_apply₁₂, Sum.elim_inl, Sum.elim_inr,
      Function.comp_apply]
    simp only [R0, R1, C0, C1, Sum.elim_inl, Sum.elim_inr]
    try simp only [R0, R1, C0, C1, Sum.elim_inl, Sum.elim_inr] at this
    linear_combination this
  · have := congrArg (fun M => M t y) (I3 hd hZ1 hZ2)
    simp [Matrix.sub_apply, diagonal_mul, mul_diagonal, vecMulVec_apply] at this
    simp only [Sw, nodeR, nodeC, Matrix.fromBlocks_apply₂₁, Sum.elim_inl, Sum.elim_inr,
      Function.comp_apply]
    simp only [R0, R1, C0, C1, Sum.elim_inl, Sum.elim_inr]
    try simp only [R0, R1, C0, C1, Sum.elim_inl, Sum.elim_inr] at this
    linear_combination this
  · have := congrArg (fun M => M t s) (I1 hd hZ1 hZ2)
    simp [Matrix.sub_apply, diagonal_mul, mul_diagonal, vecMulVec_apply] at this
    simp only [Sw, nodeR, nodeC, Matrix.fromBlocks_apply₂₂, Sum.elim_inr, Function.comp_apply,
      Matrix.neg_apply]
    simp only [R0, R1, C0, C1, Sum.elim_inr]
    try simp only [R0, R1, C0, C1, Sum.elim_inl, Sum.elim_inr] at this
    linear_combination this




end Displacement

/-! ### Reindexing a determinant by two equivalences -/

section Reindex

variable {n n' : Type*} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']

theorem det_submatrix_equivs (N : Matrix n n R) (e₁ e₂ : n' ≃ n) :
    (N.submatrix e₁ e₂).det = Equiv.Perm.sign (e₂.trans e₁.symm) * N.det := by
  have h1 : N.submatrix e₁ e₂ = (N.submatrix e₁ e₁).submatrix id (e₂.trans e₁.symm) := by
    ext i j; simp
  rw [h1, det_permute', det_submatrix_equiv_self]

/-- A sign times a determinant is associated to the determinant. -/
theorem associated_sign_mul (s : ℤˣ) (d : R) : Associated (((s : ℤ) : R) * d) d := by
  rcases Int.units_eq_one_or s with h | h <;> simp [h]

/-- Any two determinants of the same matrix by different pairings are associated. -/
theorem associated_det_submatrix (N : Matrix n n R) (e₁ e₂ : n' ≃ n) :
    Associated (N.submatrix e₁ e₂).det N.det := by
  rw [det_submatrix_equivs]
  exact associated_sign_mul _ _

end Reindex


/-! ### Bordering -/

section Border

variable (H : Matrix (Ω ⊕ I) (Ω ⊕ J) R) (A A' : Finset Ω)

/-- Rows of the minor: the kept pivot rows and `I`. -/
abbrev Xr (A : Finset Ω) (I : Type*) := {s : Ω // s ∉ A} ⊕ I

/-- The splitting of `Ω ⊕ K` into the deleted pivots `A`, the kept pivots and `K`. -/
def split (A : Finset Ω) (K : Type*) : ↥A ⊕ ({s : Ω // s ∉ A} ⊕ K) ≃ Ω ⊕ K where
  toFun := Sum.elim (fun a => Sum.inl a.1) (Sum.elim (fun s => Sum.inl s.1) Sum.inr)
  invFun := fun x => match x with
    | Sum.inl s => if h : s ∈ A then Sum.inl ⟨s, h⟩ else Sum.inr (Sum.inl ⟨s, h⟩)
    | Sum.inr k => Sum.inr (Sum.inr k)
  left_inv := by
    rintro (a | s | k)
    · simp [a.2]
    · simp [s.2]
    · rfl
  right_inv := by
    rintro (s | k)
    · by_cases h : s ∈ A <;> simp [h]
    · rfl

/-- The minor `H[(Ω∖A) ⊕ I, (Ω∖A') ⊕ J]`. -/
def Mm : Matrix (Xr A I) (Xr A' J) R :=
  H.submatrix (Sum.map Subtype.val id) (Sum.map Subtype.val id)

/-- Unit columns on the deleted pivot rows, unit rows on the deleted pivot columns. -/
def Ecol : Matrix (Ω ⊕ I) ↥A R := fun x a => if x = Sum.inl a.1 then 1 else 0
def Erow : Matrix ↥A' (Ω ⊕ J) R := fun a' y => if y = Sum.inl a'.1 then 1 else 0

/-- The bordered matrix. -/
def Nhat : Matrix ((Ω ⊕ I) ⊕ ↥A') ((Ω ⊕ J) ⊕ ↥A) R :=
  Matrix.fromBlocks H (Ecol A) (Erow A') 0

variable (eM : Xr A I ≃ Xr A' J)

/-- Pairing of the rows `↥A ⊕ Xr ⊕ ↥A'` with the columns, through `eM`. -/
def swapEq : (↥A ⊕ Xr A I) ⊕ ↥A' ≃ (↥A' ⊕ Xr A' J) ⊕ ↥A where
  toFun := Sum.elim (Sum.elim Sum.inr (fun x => Sum.inl (Sum.inr (eM x)))) (fun a' => Sum.inl (Sum.inl a'))
  invFun := Sum.elim (Sum.elim Sum.inr (fun y => Sum.inl (Sum.inr (eM.symm y)))) (fun a => Sum.inl (Sum.inl a))
  left_inv := by rintro ((a | x) | a') <;> simp
  right_inv := by rintro ((a' | y) | a) <;> simp

def rowsT : (↥A ⊕ Xr A I) ⊕ ↥A' ≃ (Ω ⊕ I) ⊕ ↥A' := Equiv.sumCongr (split A I) (Equiv.refl _)
def colsT : (↥A ⊕ Xr A I) ⊕ ↥A' ≃ (Ω ⊕ J) ⊕ ↥A :=
  (swapEq A A' eM).trans (Equiv.sumCongr (split A' J) (Equiv.refl _))




theorem det_tri3 {m1 m2 m3 : Type*} [Fintype m1] [DecidableEq m1] [Fintype m2] [DecidableEq m2]
    [Fintype m3] [DecidableEq m3] (N : Matrix ((m1 ⊕ m2) ⊕ m3) ((m1 ⊕ m2) ⊕ m3) R)
    (h11 : ∀ i j, N (Sum.inl (Sum.inl i)) (Sum.inl (Sum.inl j)) = (1 : Matrix m1 m1 R) i j)
    (h21 : ∀ x j, N (Sum.inl (Sum.inr x)) (Sum.inl (Sum.inl j)) = 0)
    (h31 : ∀ c j, N (Sum.inr c) (Sum.inl (Sum.inl j)) = 0)
    (h32 : ∀ c x, N (Sum.inr c) (Sum.inl (Sum.inr x)) = 0)
    (h33 : ∀ c c', N (Sum.inr c) (Sum.inr c') = (1 : Matrix m3 m3 R) c c') :
    N.det = (Matrix.of fun x x' => N (Sum.inl (Sum.inr x)) (Sum.inl (Sum.inr x'))).det := by
  have hb21 : N.toBlocks₂₁ = 0 := by
    ext c j
    rcases j with j | j
    · simpa [Matrix.toBlocks₂₁] using h31 c j
    · simpa [Matrix.toBlocks₂₁] using h32 c j
  have hb22 : N.toBlocks₂₂ = 1 := by
    ext c c'
    simpa [Matrix.toBlocks₂₂] using h33 c c'
  have hp21 : N.toBlocks₁₁.toBlocks₂₁ = 0 := by
    ext x j
    simpa [Matrix.toBlocks₂₁, Matrix.toBlocks₁₁] using h21 x j
  have hp11 : N.toBlocks₁₁.toBlocks₁₁ = 1 := by
    ext i j
    simpa [Matrix.toBlocks₁₁] using h11 i j
  have e1 : N.det = N.toBlocks₁₁.det := by
    conv_lhs => rw [← Matrix.fromBlocks_toBlocks N]
    rw [hb21, hb22, Matrix.det_fromBlocks_zero₂₁]
    simp
  have e2 : N.toBlocks₁₁.det = N.toBlocks₁₁.toBlocks₂₂.det := by
    conv_lhs => rw [← Matrix.fromBlocks_toBlocks N.toBlocks₁₁]
    rw [hp21, hp11, Matrix.det_fromBlocks_zero₂₁]
    simp
  rw [e1, e2]
  rfl




theorem Erow_elim (c : ↥A') (y : Xr A' J) :
    (Erow A' c (Sum.elim (fun s : {s : Ω // s ∉ A'} => (Sum.inl s.1 : Ω ⊕ J)) Sum.inr y) : R) = 0 := by
  rcases y with s | z
  · have : (Sum.inl s.1 : Ω ⊕ J) ≠ Sum.inl c.1 := fun h =>
      s.2 (by have := Sum.inl_injective h; rw [this]; exact c.2)
    simp [Erow, this]
  · simp [Erow]

theorem det_NT :
    ((Nhat H A A').submatrix (rowsT (I := I) A A') (colsT (J := J) (I := I) A A' eM)).det =
      ((Mm H A A').submatrix id eM).det := by
  have key := det_tri3 ((Nhat H A A').submatrix (rowsT (I := I) A A') (colsT (J := J) (I := I) A A' eM))
    (by
      intro i j
      simp [Nhat, rowsT, colsT, swapEq, split, Ecol, Matrix.one_apply])
    (by
      intro x j
      rcases x with s | z
      · simp [Nhat, rowsT, colsT, swapEq, split, Ecol]
        intro h
        exact (s.2 (h ▸ j.2)).elim
      · simp [Nhat, rowsT, colsT, swapEq, split, Ecol])
    (by
      intro c j
      simp [Nhat, rowsT, colsT, swapEq, split])
    (by
      intro c x
      simp only [Nhat, rowsT, colsT, swapEq, split, Matrix.submatrix_apply, Equiv.trans_apply,
        Equiv.sumCongr_apply, Equiv.coe_fn_mk, Sum.map_inr, Sum.map_inl, Sum.elim_inl, Sum.elim_inr,
        Matrix.fromBlocks_apply₂₁, Function.comp_apply]
      exact Erow_elim A' c _)
    (by
      intro c c'
      simp [Nhat, rowsT, colsT, swapEq, split, Erow, Matrix.one_apply, eq_comm])
  rw [key]
  congr 1




/-! ### The Schur picture -/

/-- Rows regrouped as pivots, then the non-pivot rows and the border rows. -/
def rowsS : Ω ⊕ (I ⊕ ↥A') ≃ (Ω ⊕ I) ⊕ ↥A' := (Equiv.sumAssoc _ _ _).symm

/-- Columns regrouped as pivots, then the non-pivot columns and the border columns, relabelled by `eS`. -/
def colsS (eS : (I ⊕ ↥A') ≃ (J ⊕ ↥A)) : Ω ⊕ (I ⊕ ↥A') ≃ (Ω ⊕ J) ⊕ ↥A :=
  (Equiv.sumCongr (Equiv.refl _) eS).trans (Equiv.sumAssoc _ _ _).symm

/-- The three non-pivot blocks of the bordered matrix, before relabelling by `eS`. -/
def V2 : Matrix (I ⊕ ↥A') Ω R := fun l t =>
  Sum.elim (fun z => H (Sum.inr z) (Sum.inl t)) (fun a' => if t = a'.1 then 1 else 0) l
def U2 : Matrix Ω (J ⊕ ↥A) R := fun s c =>
  Sum.elim (fun y => H (Sum.inl s) (Sum.inr y)) (fun a => if s = a.1 then 1 else 0) c
def W2 : Matrix (I ⊕ ↥A') (J ⊕ ↥A) R := fun l c =>
  Sum.elim (fun z => Sum.elim (fun y => H (Sum.inr z) (Sum.inr y)) (fun _ => 0) c) (fun _ => 0) l

theorem NS_eq (eS : (I ⊕ ↥A') ≃ (J ⊕ ↥A)) :
    (Nhat H A A').submatrix (rowsS A') (colsS A A' eS) =
      Matrix.fromBlocks (Qm H) ((U2 H A).submatrix id eS) (V2 H A') ((W2 H A A').submatrix id eS) := by
  ext (s | l) (t | l')
  · simp [Nhat, rowsS, colsS, Qm]
  · rcases hc : eS l' with y | a
    · simp [Nhat, rowsS, colsS, U2, hc]
    · simp [Nhat, rowsS, colsS, U2, hc, Ecol]
  · rcases l with z | a'
    · simp [Nhat, rowsS, colsS, V2]
    · simp [Nhat, rowsS, colsS, V2, Erow]
  · rcases l with z | a' <;> rcases hc : eS l' with y | a
    · simp [Nhat, rowsS, colsS, W2, hc]
    · simp [Nhat, rowsS, colsS, W2, hc, Ecol]
    · simp [Nhat, rowsS, colsS, W2, hc, Erow]
    · simp [Nhat, rowsS, colsS, W2, hc]




/-- The label submatrix of the transform, rows `I ⊕ A'`, columns `J ⊕ A`. -/
def Sm0 (Z : Matrix Ω Ω R) : Matrix (I ⊕ ↥A') (J ⊕ ↥A) R :=
  (Sw H Z).submatrix (Sum.map id Subtype.val) (Sum.map id Subtype.val)

/-- Signs of the rows and columns of the bordered Schur complement. -/
def sgnL : I ⊕ ↥A' → R := Sum.elim (fun _ => 1) (fun _ => -1)
def sgnC : J ⊕ ↥A → R := Sum.elim (fun _ => 1) (fun _ => -1)

theorem schur_block (Z : Matrix Ω Ω R) :
    W2 H A A' - V2 H A' * Z * U2 H A =
      Matrix.of fun l c => sgnL A' l * sgnC A c * Sm0 H A A' Z l c := by
  ext (z | a') (y | a)
  · simp [W2, V2, U2, Sm0, Sw, Tm, Wm, Vm, Um, sgnL, sgnC, Matrix.mul_apply]
  · simp [W2, V2, U2, Sm0, Sw, hm, Vm, sgnL, sgnC, Matrix.mul_apply]
  · simp [W2, V2, U2, Sm0, Sw, hm', Um, sgnL, sgnC, Matrix.mul_apply]
  · simp [W2, V2, U2, Sm0, Sw, sgnL, sgnC, Matrix.mul_apply]




theorem isUnit_det_diagonal_sgn {κ : Type*} [Fintype κ] [DecidableEq κ] (s : κ → R)
    (hs : ∀ i, s i = 1 ∨ s i = -1) : IsUnit (diagonal s).det := by
  rw [det_diagonal]
  refine Finset.prod_induction _ IsUnit (fun a b => IsUnit.mul) isUnit_one (fun i _ => ?_)
  rcases hs i with h | h <;> simp [h]

theorem sgnL_cases (l : I ⊕ ↥A') : (sgnL A' l : R) = 1 ∨ (sgnL A' l : R) = -1 := by
  rcases l with _ | _ <;> simp [sgnL]

theorem sgnC_cases (c : J ⊕ ↥A) : (sgnC A c : R) = 1 ∨ (sgnC A c : R) = -1 := by
  rcases c with _ | _ <;> simp [sgnC]

/-- **Bordered determinant** (Lemma 5 of the sweep, rectangular): for an invertible pivot block `Q`
(with inverse `Z`), deleted pivot rows `A`, deleted pivot columns `A'`, and any pairings `eM`, `eS`,
the minor `H[(Ω∖A) ⊕ I, (Ω∖A') ⊕ J]` is associated to the label minor `Sw[I ⊕ A', J ⊕ A]`. -/
theorem jacobi (Z : Matrix Ω Ω R) (hZ1 : Qm H * Z = 1) (hZ2 : Z * Qm H = 1)
    (eM : Xr A I ≃ Xr A' J) (eS : (I ⊕ ↥A') ≃ (J ⊕ ↥A)) :
    Associated ((Mm H A A').submatrix id eM).det ((Sm0 H A A' Z).submatrix id eS).det := by
  -- the pairing `T` of the first computation and the Schur pairing
  set NT := (Nhat H A A').submatrix (rowsT (I := I) A A') (colsT (J := J) (I := I) A A' eM) with hNT
  set NS := (Nhat H A A').submatrix (rowsS A') (colsS A A' eS) with hNS
  have h1 : NT.det = ((Mm H A A').submatrix id eM).det := det_NT H A A' eM
  have h2 : NS = NT.submatrix ((rowsS A').trans (rowsT (I := I) A A').symm)
      ((colsS A A' eS).trans (colsT (J := J) (I := I) A A' eM).symm) := by
    ext i j; simp [hNS, hNT]
  have h3 : Associated NS.det NT.det := by
    rw [h2]; exact associated_det_submatrix _ _ _
  letI : Invertible (Qm H) := ⟨Z, hZ2, hZ1⟩
  have hinv : ⅟(Qm H) = Z := by apply invOf_eq_right_inv; exact hZ1
  have h4 : NS.det = (Qm H).det * ((W2 H A A' - V2 H A' * Z * U2 H A).submatrix id eS).det := by
    rw [hNS, NS_eq H A A' eS]
    have := Matrix.det_fromBlocks₁₁ (Qm H) ((U2 H A).submatrix id eS) (V2 H A') ((W2 H A A').submatrix id eS)
    rw [this, hinv]
    congr 2
  have h5 : (W2 H A A' - V2 H A' * Z * U2 H A).submatrix id eS =
      diagonal (sgnL A') * (Sm0 H A A' Z).submatrix id eS * diagonal (fun l => sgnC A (eS l)) := by
    rw [schur_block]
    ext i j
    simp [diagonal_mul, mul_diagonal]
    ring
  have hQu : IsUnit (Qm H).det := by
    refine isUnit_iff_exists_inv.mpr ⟨Z.det, ?_⟩
    rw [← det_mul, hZ1, det_one]
  have hu1 : IsUnit (diagonal (sgnL (R := R) (I := I) A')).det := isUnit_det_diagonal_sgn (sgnL (R := R) (I := I) A') (sgnL_cases (I := I) A')
  have hu2 : IsUnit (diagonal (fun l : I ⊕ ↥A' => (sgnC A (eS l) : R))).det :=
    isUnit_det_diagonal_sgn (fun l : I ⊕ ↥A' => (sgnC A (eS l) : R)) (fun l => sgnC_cases (J := J) A (eS l))
  have h6 : NS.det = ((Qm H).det * (diagonal (sgnL (R := R) (I := I) A')).det * (diagonal (fun l : I ⊕ ↥A' => (sgnC A (eS l) : R))).det) *
      ((Sm0 H A A' Z).submatrix id eS).det := by
    rw [h4, h5, det_mul, det_mul]; ring
  have h7 : Associated NS.det ((Sm0 H A A' Z).submatrix id eS).det := by
    rw [h6]
    exact associated_unit_mul_left _ _ ((hQu.mul hu1).mul hu2)
  rw [← h1]
  exact (h3.symm.trans h7)




/-- **Bordered determinant, labelled form.**  Rows and columns of the actual minor are indexed by one
type `L` through `ρ`, `κ` which are the bijections onto `(Ω∖A) ⊕ I` and `(Ω∖A') ⊕ J` followed by the
inclusions; the labels of the transform are indexed by `L'` likewise. -/
theorem jacobi_L {L L' : Type*} [Fintype L] [DecidableEq L] [Fintype L'] [DecidableEq L']
    (Z : Matrix Ω Ω R) (hZ1 : Qm H * Z = 1) (hZ2 : Z * Qm H = 1)
    (ρ : L → Ω ⊕ I) (κ : L → Ω ⊕ J) (ρ' : L' → I ⊕ Ω) (κ' : L' → J ⊕ Ω)
    (eL : L ≃ Xr A I) (eC : L ≃ Xr A' J) (eL' : L' ≃ I ⊕ ↥A') (eC' : L' ≃ J ⊕ ↥A)
    (hρ : ∀ l, ρ l = Sum.map Subtype.val id (eL l)) (hκ : ∀ l, κ l = Sum.map Subtype.val id (eC l))
    (hρ' : ∀ l, ρ' l = Sum.map id Subtype.val (eL' l))
    (hκ' : ∀ l, κ' l = Sum.map id Subtype.val (eC' l)) :
    Associated (Matrix.of fun a b => H (ρ a) (κ b)).det
      (Matrix.of fun a b => (Sw H Z) (ρ' a) (κ' b)).det := by
  have e1 : (Matrix.of fun a b => H (ρ a) (κ b)) =
      ((Mm H A A').submatrix id (eL.symm.trans eC)).submatrix eL eL := by
    ext a b; simp [Mm, hρ, hκ]
  have e2 : (Matrix.of fun a b => (Sw H Z) (ρ' a) (κ' b)) =
      (((Sm0 H A A' Z).submatrix id (eL'.symm.trans eC')).submatrix eL' eL') := by
    ext a b; simp [Sm0, hρ', hκ']
  rw [e1, e2, det_submatrix_equiv_self, det_submatrix_equiv_self]
  exact jacobi H A A' Z hZ1 hZ2 _ _

end Border

end CatalanCore.Uniform.Content.Sweep.Schur

#print axioms CatalanCore.Uniform.Content.Sweep.Schur.pivot_displacement
#print axioms CatalanCore.Uniform.Content.Sweep.Schur.jacobi
#print axioms CatalanCore.Uniform.Content.Sweep.Schur.jacobi_L
