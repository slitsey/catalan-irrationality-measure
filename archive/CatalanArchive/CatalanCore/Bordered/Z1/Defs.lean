module

public import CatalanCore.Bordered.Z1.Tri3
public import CatalanCore.Linalg.Krylov
public import CatalanCore.Linalg.TridiagCyclic
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Data.Nat.Factorial.Basic

/-!
# Z1.1: bordered objects

All objects are defined over an arbitrary commutative `ℚ`-algebra `R`, with the parameter
`θ : R`.  Instantiating `R = ℚ[X]`, `θ = X` gives the polynomial objects; `R = ℝ⟦X⟧`,
`θ = C(-c) + X` gives the local objects; `R = ℚ`, `θ = q` gives numerical values.
Algebra homomorphisms commute with all the constructions (`*_map`).

Geometry: `K = s + m`, columns `j ∈ {1..s}` (0-based `k = j - 1`), nodes `a ∈ {0..K-1}`,
`Z = {s+1, …, s+2m}`, `X = s + 2 + 2i`, `Y = s + 1 + 2i` (`i < m`).

Normalisation (checked exactly against `FZ-blocksplit/lib.py: Tmat` and hence WP-H7's
`Tmat Γ = (Γ⁻¹)_{GG}` with `Γ = C_{G∪X}ᵀ C_{G∪Y}`, K ≤ 6, θ ∈ {1/3, 7/5}, all m): with the
definitions below `Tmat s m θ = (Γ̂⁻¹)_{GG}` on the nose (scalar 1), with
`Λ₁ = poch/(Π_Y ω′)` and `Λ₂ = poch/(Π_X ω′)`, `Π_X(j) = ∏_{x∈X}(j-x)`.
-/

@[expose] public section

open Finset Matrix

namespace CatalanCore.Bordered.Z1

section Defs

variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-- Rational constant in `R`. -/
def qc (c : ℚ) : R := algebraMap ℚ R c

/-- `ω′(j) = ∏_{i ≤ s, i ≠ j} (j - i) = (-1)^(s-j) (j-1)! (s-j)!` (closed form). -/
def omegaP (s j : ℕ) : ℚ := (-1) ^ (s - j) * ((j - 1).factorial : ℚ) * ((s - j).factorial : ℚ)

/-- `Π_X(j) = ∏_{x ∈ X} (j - x)`, `X = {s+2+2i}`. -/
def PiX (s m j : ℕ) : ℚ := ∏ i ∈ range m, ((j : ℚ) - ((s + 2 + 2 * i : ℕ) : ℚ))

/-- `Π_Y(j) = ∏_{y ∈ Y} (j - y)`, `Y = {s+1+2i}`. -/
def PiY (s m j : ℕ) : ℚ := ∏ i ∈ range m, ((j : ℚ) - ((s + 1 + 2 * i : ℕ) : ℚ))

/-- Pochhammer-type product `∏_{a<K} (θ + j + a)`. -/
def poch (θ : R) (K j : ℕ) : R := ∏ a ∈ range K, (θ + ((j + a : ℕ) : R))

/-- `Λ₁` at 0-based index `k` (column `j = k+1`). -/
def Lam1 (s m : ℕ) (θ : R) (k : ℕ) : R :=
  qc (1 / (PiY s m (k + 1) * omegaP s (k + 1))) * poch θ (s + m) (k + 1)

/-- `Λ₂` at 0-based index `k`. -/
def Lam2 (s m : ℕ) (θ : R) (k : ℕ) : R :=
  qc (1 / (PiX s m (k + 1) * omegaP s (k + 1))) * poch θ (s + m) (k + 1)

/-- `∏_{z ∈ Z} (x + z)`, `Z = {s+1..s+2m}`. -/
def Zp (s m : ℕ) (x : R) : R := ∏ i ∈ range (2 * m), (x + ((s + 1 + i : ℕ) : R))

/-- Node weight `ρ_a = ∏_{z∈Z}(θ + a + z) / (a! (K-1-a)!)²`. -/
def rho (s m : ℕ) (θ : R) (a : ℕ) : R :=
  qc (1 / (((a.factorial) * ((s + m - 1 - a).factorial) : ℕ) ^ 2 : ℚ)) * Zp s m (θ + (a : R))

/-- `lag x j = ∏_{i<s, i≠j} (x + i + 1)` (0-based `j`): `(x+1)_s / (x + j + 1)`. -/
def lag (s : ℕ) (x : R) (j : ℕ) : R := ∏ i ∈ (range s).erase j, (x + ((i + 1 : ℕ) : R))

/-- `K × s` matrix `Lag(a, j)`. -/
def Lag (s m : ℕ) (θ : R) : Matrix (Fin (s + m)) (Fin s) R :=
  Matrix.of fun a j => lag s (θ + ((a : ℕ) : R)) j

/-- `A = Lagᵀ diag(ρ) Lag`, exactly polynomial. -/
def Amat (s m : ℕ) (θ : R) : Matrix (Fin s) (Fin s) R :=
  (Lag s m θ)ᵀ * Matrix.diagonal (fun a : Fin (s + m) => rho s m θ a) * Lag s m θ

/-- `T = Λ₁ A Λ₂`. -/
def Tmat (s m : ℕ) (θ : R) : Matrix (Fin s) (Fin s) R :=
  Matrix.diagonal (fun k : Fin s => Lam1 s m θ k) * Amat s m θ *
    Matrix.diagonal (fun k : Fin s => Lam2 s m θ k)

/-- The quartic `D(x)` of the bispectral identity. -/
def Dq (s m : ℕ) (θ x : R) : R :=
  -2 * x ^ 4 + 4 * (θ - 1) * x ^ 3 +
    (3 * (m : R) ^ 2 + 4 * m * s + 2 * m * θ + 2 * (s : R) ^ 2 + 2 * s * θ - 2 * θ ^ 2 + 6 * θ - 4) * x ^ 2 +
    (-2 * (m : R) ^ 3 - 2 * (m : R) ^ 2 * s - 4 * (m : R) ^ 2 * θ + 3 * (m : R) ^ 2 - 4 * m * s * θ
      + 4 * m * s - 2 * m * θ ^ 2 + 2 * m * θ - 2 * (s : R) ^ 2 * θ + 2 * (s : R) ^ 2
      - 2 * s * θ ^ 2 + 2 * s * θ - 2 * θ ^ 2 + 4 * θ - 2) * x

/-- Node-side polynomials. -/
def Fq (s m : ℕ) (θ x : R) : R :=
  (x + 1 + s) * (x + 1 + s + 2 * m) * (((s + m : ℕ) : R) - 1 + θ - x) ^ 2
def Gq (θ x : R) : R := x ^ 2 * (x - θ) ^ 2
/-- Column-side polynomials. -/
def rq (s m : ℕ) (θ y : R) : R := ((s : R) - y) * (s + 2 * m - y) * (((s + m : ℕ) : R) + θ + y) ^ 2
def lq (θ y : R) : R := (y - 1) ^ 2 * (y - 1 + θ) ^ 2

/-- `X` (column side), tridiagonal: `X(k,k+1) = ℓ(k+2)`, `X(k+1,k) = r(k+1)`, `X(k,k) = D(-(k+1))`. -/
def Xmat (s m : ℕ) (θ : R) : Matrix (Fin s) (Fin s) R :=
  tri3 s (fun k => lq θ ((k : R) + 2)) (fun k => Dq s m θ (-((k : R) + 1)))
    (fun k => rq s m θ ((k : R) + 1))

/-- `L̃` (node side, polynomial gauge): `L̃_{a,a+1} = (x+1)(x+1+s+2m)(K-1-a)²`,
`L̃_{a+1,a} = x'(a+1)²(x'+s)` with `x' = θ+a+1`, `L̃_{aa} = D(x_a)`. -/
def Ltil (s m : ℕ) (θ : R) : Matrix (Fin (s + m)) (Fin (s + m)) R :=
  tri3 (s + m)
    (fun a => (θ + a + 1) * (θ + a + 1 + s + 2 * m) * (((s + m : ℕ) : R) - 1 - a) ^ 2)
    (fun a => Dq s m θ (θ + a))
    (fun a => (θ + a + 1) * ((a : R) + 1) ^ 2 * (θ + a + 1 + s))

/-- Ratio `p_j = Π_X(j-1)/Π_X(j)` at `j = k+2`. -/
def pj (s m k : ℕ) : ℚ := PiX s m (k + 1) / PiX s m (k + 2)

/-- Closed-form `X′ = Λ₂⁻¹ X Λ₂`. -/
def Xp (s m : ℕ) (θ : R) : Matrix (Fin s) (Fin s) R :=
  tri3 s
    (fun k => -(((k : R) + 1) * ((k : R) + 1 + θ) * ((k : R) + 1 + θ + ((s + m : ℕ) : R))
        * ((s : R) - k - 1)) * qc (pj s m k))
    (fun k => Dq s m θ (-((k : R) + 1)))
    (fun k => -(((k : R) + 1) * ((k : R) + 1 + θ) * ((s : R) + 2 * m - k - 1)
        * (((s + m : ℕ) : R) + θ + k + 1)) * qc (1 / pj s m k))

/-- Last unit vector `e_s`. -/
def es (R : Type*) [CommRing R] (s : ℕ) : Fin s → R := fun i => if (i : ℕ) = s - 1 then 1 else 0

/-- The Krylov determinant `k_B = u(T, e_s)`. -/
def kB (s m : ℕ) (θ : R) : R := kdet (Tmat s m θ) (es R s)

end Defs

section Map

variable {R S : Type*} [CommRing R] [Algebra ℚ R] [CommRing S] [Algebra ℚ S]

lemma qc_map (f : R →ₐ[ℚ] S) (c : ℚ) : f (qc c) = qc c := by
  simp [qc]

lemma poch_map (f : R →ₐ[ℚ] S) (θ : R) (K j : ℕ) : f (poch θ K j) = poch (f θ) K j := by
  simp [poch, map_prod]

lemma Lam1_map (f : R →ₐ[ℚ] S) (s m : ℕ) (θ : R) (k : ℕ) :
    f (Lam1 s m θ k) = Lam1 s m (f θ) k := by
  simp [Lam1, qc_map, poch_map]

lemma Lam2_map (f : R →ₐ[ℚ] S) (s m : ℕ) (θ : R) (k : ℕ) :
    f (Lam2 s m θ k) = Lam2 s m (f θ) k := by
  simp [Lam2, qc_map, poch_map]

lemma Zp_map (f : R →ₐ[ℚ] S) (s m : ℕ) (x : R) : f (Zp s m x) = Zp s m (f x) := by
  simp [Zp, map_prod]

lemma rho_map (f : R →ₐ[ℚ] S) (s m : ℕ) (θ : R) (a : ℕ) : f (rho s m θ a) = rho s m (f θ) a := by
  simp [rho, qc_map, Zp_map]

lemma lag_map (f : R →ₐ[ℚ] S) (s : ℕ) (x : R) (j : ℕ) : f (lag s x j) = lag s (f x) j := by
  simp [lag, map_prod]

lemma Lag_map (f : R →ₐ[ℚ] S) (s m : ℕ) (θ : R) :
    (Lag s m θ).map f = Lag s m (f θ) := by
  ext a j; simp [Lag, lag_map]

lemma Amat_map (f : R →ₐ[ℚ] S) (s m : ℕ) (θ : R) :
    (Amat s m θ).map f = Amat s m (f θ) := by
  simp only [Amat, ← Lag_map]
  ext i j
  simp [Matrix.mul_apply, rho_map, Matrix.diagonal_apply, Matrix.map_apply]

lemma Tmat_map (f : R →ₐ[ℚ] S) (s m : ℕ) (θ : R) :
    (Tmat s m θ).map f = Tmat s m (f θ) := by
  ext i j
  simp [Tmat, Matrix.mul_apply, Matrix.diagonal_apply, Lam1_map, Lam2_map, ← Amat_map]

end Map

end CatalanCore.Bordered.Z1
