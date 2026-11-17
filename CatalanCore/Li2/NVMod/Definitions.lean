module

public import Mathlib.FieldTheory.RatFunc.Basic
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

@[expose] public section

open Polynomial Matrix
open scoped BigOperators

namespace CatalanCore.Li2.NVMod

inductive Kind | V | U
  deriving DecidableEq

structure TypeKey where
  kind : Kind
  a : ℕ
  c : ℕ
  size : ℕ
  deriving DecidableEq

noncomputable section

def rfPoly {F : Type*} [Field F] (P : F[X]) : RatFunc F :=
  algebraMap F[X] (RatFunc F) P

def rfX {F : Type*} [Field F] : RatFunc F := rfPoly (X : F[X])

def pp (F : RatFunc ℚ) : ℚ[X] := F.num /ₘ F.denom

def poleIndices (F : RatFunc ℚ) : Finset ℕ :=
  (F.denom.roots.toFinset.filter (fun x => x ≤ 0 ∧ x.den = 1)).image
    (fun x => (-x).num.toNat)

def poleRes (F : RatFunc ℚ) (m : ℕ) : ℚ :=
  F.num.eval (-(m : ℚ)) / F.denom.derivative.eval (-(m : ℚ))

def SimplePoles (F : RatFunc ℚ) : Prop :=
  ∃ S : Finset ℕ, F.denom ∣ ∏ m ∈ S, (X + C (m : ℚ))

def liNeg {F : Type*} [Field F] (j : ℕ) (z : F) : F :=
  if j = 0 then z / (1-z) else
    ∑ i ∈ Finset.Icc 1 j,
      (Nat.stirlingSecond j i : F) * (Nat.factorial i : F) * z^i / (1-z)^(i+1)

def tauK {F : Type*} [Field F] (z : F) (m : ℕ) : F :=
  ∑ b ∈ Finset.Icc 1 m, z^b / (b : F)^2

def regularV {F : Type*} [Field F] [Algebra ℚ F]
    (z : F) (f : RatFunc ℚ) : F :=
  (∑ m ∈ poleIndices f, algebraMap ℚ F (poleRes f m) *
    z^(-(m : ℤ)) * tauK z m) +
  ∑ j ∈ Finset.Icc 1 (pp f).natDegree,
    (j : F) * algebraMap ℚ F ((pp f).coeff j) * liNeg (j-1) z

def weightNum (A : TypeKey) : ℚ[X] :=
  match A.kind with
  | .V => ∏ j ∈ Finset.range A.a, (X + C (j : ℚ))^2
  | .U => X * ∏ j ∈ Finset.Icc 1 A.a, (X + C (j : ℚ))^2

def poleSet (A : TypeKey) : Finset ℕ :=
  match A.kind with
  | .V => Finset.Ico A.a A.c
  | .U => Finset.Ioc A.a A.c

def weightDen (A : TypeKey) : ℚ[X] :=
  ∏ j ∈ poleSet A, (X + C (j : ℚ))

def weight (A : TypeKey) : RatFunc ℚ := rfPoly (weightNum A) / rfPoly (weightDen A)

def residue (A : TypeKey) (m : ℕ) : ℚ :=
  (weightNum A).eval (-(m : ℚ)) / (weightDen A).derivative.eval (-(m : ℚ))

def polyPart (A : TypeKey) (g : ℚ[X]) : ℚ[X] := weightNum A * g /ₘ weightDen A

def omega (z : ℚ) (m : ℕ) : ℚ :=
  ∑ b ∈ Finset.Icc 1 m, z^((b : ℤ)-m) / (b : ℚ)^2

def L (A : TypeKey) (z : ℚ) (g : ℚ[X]) : ℚ := regularV z (rfPoly g * weight A)

def K (A : TypeKey) (z : ℚ) : ℚ :=
  Matrix.det (fun i j : Fin A.size => L A z (X^((i : ℕ)+j)))

def momentRF (A : TypeKey) (g : ℚ[X]) : RatFunc ℚ :=
  regularV (rfX : RatFunc ℚ) (rfPoly g * weight A)

def constantRF (A : TypeKey) : RatFunc ℚ :=
  Matrix.det (fun i j : Fin A.size => momentRF A (X^((i : ℕ)+j)))

def omegaRF (m : ℕ) : RatFunc ℚ :=
  ∑ b ∈ Finset.Icc 1 m, rfX^((b : ℤ)-m) / rfPoly (C ((b : ℚ)^2))

def neededAt (q k : ℕ) : Finset TypeKey :=
  let base : Finset TypeKey :=
    {⟨.V,q,4*q+k,2*q+k⟩, ⟨.V,q+1,4*q+k+1,2*q+k-1⟩}
  let mid : Finset TypeKey := if 1 ≤ q ∧ k ≤ 2 then
    {⟨.V,q,4*q+k+1,2*q+k+1⟩, ⟨.U,q,4*q+k,2*q+k⟩} else ∅
  let tied : Finset TypeKey := if 1 ≤ k then
    {⟨.V,q+1,4*q+k,2*q+k-2⟩, ⟨.V,q+1,4*q+k,2*q+k-1⟩,
     ⟨.U,q,4*q+k,2*q+k-1⟩, ⟨.U,q,4*q+k,2*q+k⟩} else ∅
  base ∪ mid ∪ tied

def needed (q0 : ℕ) : Finset TypeKey :=
  (Finset.range (q0+1)).biUnion (fun q =>
    (if q=0 then ({3} : Finset ℕ) else Finset.range 4).biUnion (neededAt q))

def AllConstantsNonzero (z : ℚ) (q0 : ℕ) : Prop := ∀ A ∈ needed q0, K A z ≠ 0

def Z0 : Finset ℚ := {-12, -4, -4/5, 12/13}

def Allowed (z : ℚ) : Prop := z ≠ 0 ∧ z ≠ 1 ∧ z ∉ Z0

end
end CatalanCore.Li2.NVMod
