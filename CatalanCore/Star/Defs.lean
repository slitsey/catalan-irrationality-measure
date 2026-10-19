module

public import CatalanCore.Bordered.Z1.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Int.Interval

/-!
# Star.Defs: the generic bordered Krylov determinant `k^gen` and its pencil form

Frame-independent, over an arbitrary field `F`.  Global parameters `(K m S : ℕ)` (plus the prime
`ℓ` only where units are needed), with `n = K - m`.  Nodes `x_a = θ + a` (`a < K`), columns
`w_j(a) = 1/(θ + a + j)`, evaluation column `S`, borders
`J_X = S + {2,4,…,2m}`, `J_Y = S + {1,3,…,2m-1}`.

* `kgenR K m θ J S` is the Krylov determinant `det[w_Sᵀ (Π N₂)^k u_i]` with `Π` the projector onto
  `ker W_Xᵀ` along `range W_Y`, `N₂ = Σ_{j∈J} w_j w_jᵀ`, `u_i(a) = Π_X(-x_a)(-x_a)^i/π_a`.
  `kgen K m S θ` is the case `J = {1..S-1}` (the `k^gen` of FG/GI).
* `kgenL` is the same with `X ↔ Y`.
* Pencil side (GI §1): `Hn`, `Hc`, `cS`, `kpen`.  The bridge `kgenR = kpen` is in `Star.Pencil`.

Everything is stated for a general border data `bx by : Fin m → ℤ` (`kgenCore`), the `R`/`L`
versions being the two standard instances.
-/

@[expose] public section

open Finset Matrix

namespace CatalanCore.Star

variable {F : Type*} [Field F]

/-! ### Borders, columns, projector -/

/-- Border of `X`: `S + 2 + 2i`. -/
def bX (m : ℕ) (S : ℤ) : Fin m → ℤ := fun i => S + 2 + 2 * (i : ℕ)
/-- Border of `Y`: `S + 1 + 2i`. -/
def bY (m : ℕ) (S : ℤ) : Fin m → ℤ := fun i => S + 1 + 2 * (i : ℕ)

/-- Column `w_j(a) = 1/(θ + a + j)`, nodes `a < K`. -/
def wcol (K : ℕ) (θ : F) (j : ℤ) : Fin K → F := fun a => 1 / (θ + ((a : ℕ) : F) + (j : F))

/-- Border matrix `K × m` with columns `w_{b i}`. -/
def Wb (K : ℕ) (θ : F) {m : ℕ} (b : Fin m → ℤ) : Matrix (Fin K) (Fin m) F :=
  Matrix.of fun a i => wcol K θ (b i) a

/-- `Π = 1 - W_Y (W_Xᵀ W_Y)⁻¹ W_Xᵀ`. -/
noncomputable def projB (K : ℕ) (θ : F) {m : ℕ} (bx by' : Fin m → ℤ) : Matrix (Fin K) (Fin K) F :=
  1 - Wb K θ by' * ((Wb K θ bx)ᵀ * Wb K θ by')⁻¹ * (Wb K θ bx)ᵀ

/-- `N₂ = Σ_{j∈J} w_j w_jᵀ`. -/
def Nmat (K : ℕ) (θ : F) (J : Finset ℤ) : Matrix (Fin K) (Fin K) F :=
  ∑ j ∈ J, Matrix.vecMulVec (wcol K θ j) (wcol K θ j)

/-- `Π_b(z) = ∏_i (z - b_i)`. -/
def piB {m : ℕ} (b : Fin m → ℤ) (z : F) : F := ∏ i, (z - (b i : F))

/-- `π_a = ∏_{b≠a} (b - a)`. -/
def pia (K : ℕ) (a : Fin K) : F := ∏ b ∈ univ.erase a, (((b : ℕ) : F) - ((a : ℕ) : F))

/-- Kernel basis `u_i(a) = Π_X(-x_a) (-x_a)^i / π_a`, `i < n`. -/
def ubasis (K n : ℕ) (θ : F) {m : ℕ} (bx : Fin m → ℤ) : Matrix (Fin K) (Fin n) F :=
  Matrix.of fun a i =>
    piB bx (-(θ + ((a : ℕ) : F))) * (-(θ + ((a : ℕ) : F))) ^ (i : ℕ) / pia K a

/-- The Krylov determinant `det[w_Sᵀ (Π N₂)^k u_i]_{k,i<K-m}` for general border data. -/
noncomputable def kgenCore (K m : ℕ) (θ : F) (J : Finset ℤ) (S : ℤ) (bx by' : Fin m → ℤ) : F :=
  Matrix.det (Matrix.of fun (k i : Fin (K - m)) =>
    (((wcol K θ S) ᵥ* ((projB K θ bx by' * Nmat K θ J) ^ (k : ℕ))) ᵥ* ubasis K (K - m) θ bx) i)

/-- `k_R(θ; J)`: borders `J_X = S+{2,4,…}`, `J_Y = S+{1,3,…}`. -/
noncomputable def kgenR (K m : ℕ) (θ : F) (J : Finset ℤ) (S : ℕ) : F :=
  kgenCore K m θ J (S : ℤ) (bX m S) (bY m S)

/-- `k_L(θ; J)`: `X ↔ Y`. -/
noncomputable def kgenL (K m : ℕ) (θ : F) (J : Finset ℤ) (S : ℕ) : F :=
  kgenCore K m θ J (S : ℤ) (bY m S) (bX m S)

/-- `k^gen(θ; K, m, S) = k_R(θ; {1..S-1})`. -/
noncomputable def kgen (K m S : ℕ) (θ : F) : F := kgenR K m θ (Finset.Icc 1 ((S : ℤ) - 1)) S

/-! ### Pencil side -/

/-- `Π_Z(z) = ∏_{i<2m} (z - (S+1+i))`, `Z = {S+1..S+2m}`. -/
def PiZ (m S : ℕ) (z : F) : F := ∏ i ∈ range (2 * m), (z - ((S + 1 + i : ℕ) : F))

/-- Node weight `ω_a = Π_Z(ζ_a)/π_a²`, `ζ_a = -(θ+a)`. -/
def omegaN (K m S : ℕ) (θ : F) (a : Fin K) : F :=
  PiZ m S (-(θ + ((a : ℕ) : F))) / pia K a ^ 2

/-- Column weight `γ_j = Π_Z(j)/∏_a (θ+a+j)²`. -/
def gammaC (K m S : ℕ) (θ : F) (j : ℤ) : F :=
  PiZ m S (j : F) / (∏ a : Fin K, (θ + ((a : ℕ) : F) + (j : F))) ^ 2

/-- `H_n(i,i') = Σ_a ω_a ζ_a^{i+i'}`. -/
def Hn (K m S n : ℕ) (θ : F) : Matrix (Fin n) (Fin n) F :=
  Matrix.of fun i i' =>
    ∑ a : Fin K, omegaN K m S θ a * (-(θ + ((a : ℕ) : F))) ^ ((i : ℕ) + i')

/-- `H_c(i,i') = Σ_{j∈J} γ_j j^{i+i'}`. -/
def Hc (K m S n : ℕ) (θ : F) (J : Finset ℤ) : Matrix (Fin n) (Fin n) F :=
  Matrix.of fun i i' => ∑ j ∈ J, gammaC K m S θ j * (j : F) ^ ((i : ℕ) + i')

/-- `ν_S = (S^i)_{i<n}`. -/
def nuS (n : ℕ) (S : F) : Fin n → F := fun i => S ^ (i : ℕ)

/-- `c_S^R = Π_X(S)/∏_a (θ+a+S)`. -/
def cSR (K m S : ℕ) (θ : F) : F := piB (bX m S) (S : F) / ∏ a : Fin K, (θ + ((a : ℕ) : F) + S)
/-- `c_S^L = Π_Y(S)/∏_a (θ+a+S)`. -/
def cSL (K m S : ℕ) (θ : F) : F := piB (bY m S) (S : F) / ∏ a : Fin K, (θ + ((a : ℕ) : F) + S)

/-- Pencil Krylov determinant `𝒦 = det[ν_Sᵀ B^k]_{k<n}`, `B = H_n⁻¹ H_c`. -/
noncomputable def Kpen (K m S : ℕ) (θ : F) (J : Finset ℤ) : F :=
  Matrix.det (Matrix.of fun (k i : Fin (K - m)) =>
    ((nuS (K - m) (S : F)) ᵥ* ((Hn K m S (K - m) θ)⁻¹ * Hc K m S (K - m) θ J) ^ (k : ℕ)) i)

/-- `k_pen = c_S^n 𝒦` (right version). -/
noncomputable def kpen (K m S : ℕ) (θ : F) (J : Finset ℤ) : F :=
  cSR K m S θ ^ (K - m) * Kpen K m S θ J

/-- Link with the Z1 helper `Z1.PiX`. -/
lemma piB_bX_natCast [CharZero F] (m S j : ℕ) :
    piB (bX m S) ((j : ℕ) : F) = ((CatalanCore.Bordered.Z1.PiX S m j : ℚ) : F) := by
  simp only [piB, bX, CatalanCore.Bordered.Z1.PiX]
  rw [Fin.prod_univ_eq_prod_range (fun i => ((j : F) - (((S : ℤ) + 2 + 2 * (i : ℕ) : ℤ) : F))) m]
  rw [Rat.cast_prod]
  push_cast
  rfl

end CatalanCore.Star
