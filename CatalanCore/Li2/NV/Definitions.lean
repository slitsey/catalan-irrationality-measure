module
public import CatalanCore.Li2.NVMod.Definitions
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section
open Polynomial Matrix
open scoped BigOperators
namespace CatalanCore.Li2.NV
noncomputable section
def countClass (N ℓ s : ℕ) : ℕ :=
  ((Finset.Icc 1 N).filter (fun i => i % ℓ = s)).card
def a (n ℓ s : ℕ) : ℕ := countClass n ℓ s
def c (n ℓ s : ℕ) : ℕ := countClass (4*n) ℓ s
def m (n ℓ s : ℕ) : ℕ := c n ℓ s - 2*a n ℓ s
def b (n ℓ s : ℕ) : ℕ := c n ℓ s - a n ℓ s
def nu (n ℓ s : ℕ) : ℤ := 3*(a n ℓ s : ℤ) - c n ℓ s - 1 + if s = 0 then 1 else 0
def pot (n ℓ s : ℕ) : ℚ := (m n ℓ s : ℚ) + (nu n ℓ s : ℚ)/2
def pi (n ℓ s i : ℕ) : ℚ := (i : ℚ) + (nu n ℓ s : ℚ)/2
def r (n ℓ : ℕ) : ℕ := n % ℓ
def k (n ℓ : ℕ) : ℕ := 4*(n % ℓ)/ℓ
def r' (n ℓ : ℕ) : ℕ := 4*(n % ℓ)%ℓ
def tied (n ℓ : ℕ) : Prop := r' n ℓ < r n ℓ
def Range (n ℓ : ℕ) : Prop :=
  4*n < ℓ*(ℓ-1) ∧ (ℓ ≤ n ∨ (n < ℓ ∧ 3*ℓ < 4*n))
def Cset (n ℓ : ℕ) : Finset ℕ := Finset.Ioc (r' n ℓ) (r n ℓ)
def Bset (n ℓ : ℕ) : Finset ℕ := Finset.Ioc (r n ℓ) (r' n ℓ)
abbrev Ix (n ℓ : ℕ) := (s : Fin ℓ) × Fin (m n ℓ s)
def d (n ℓ : ℕ) (s : Fin ℓ) (P : Ix n ℓ) : ℕ :=
  if s = P.1 then P.2 else m n ℓ s
def slack (n ℓ : ℕ) (s : Fin ℓ) (P Q : Ix n ℓ) : ℚ :=
  (nu n ℓ s : ℚ) + d n ℓ s P + d n ℓ s Q -
    pi n ℓ P.1 P.2 - pi n ℓ Q.1 Q.2
def BinTail {K : Type*} [Field K] (r t : ℕ) (y : K) : K :=
  ∑ i ∈ Finset.Ioc t r, (Nat.choose r i : K)*y^i*(1-y)^(r-i)
def pairPoly {K : Type*} [CommRing K] (y : K) : K[X] :=
  C (-18*y^4+132*y^3-180*y^2+72*y)*X +
  C (-81*y^4+504*y^3-636*y^2+240*y)*X^2 +
  C (-81*y^4+444*y^3-528*y^2+192*y)*X^3

inductive ClassType | A | B | C | D | zero
  deriving DecidableEq
def typeAC (n ℓ s : ℕ) : ℕ×ℕ :=
  (n/ℓ + if s≠0 ∧ s≤r n ℓ then 1 else 0,
    4*(n/ℓ)+k n ℓ + if s≠0 ∧ s≤r' n ℓ then 1 else 0)
def classType (n ℓ s : ℕ) : ClassType :=
  if s=0 then .zero else
  if s≤r n ℓ then (if s≤r' n ℓ then .A else .C)
  else if s≤r' n ℓ then .B else .D
def typeM (q K : ℕ) : ClassType→ℤ
  | .A => 2*(q:ℤ)+K-1
  | .B => 2*(q:ℤ)+K+1
  | .C => 2*(q:ℤ)+K-2
  | .D | .zero => 2*(q:ℤ)+K
def typePot (q K : ℕ) : ClassType→ℚ
  | .A | .D => (3*(q:ℚ)+K-1)/2
  | .B | .zero => (3*(q:ℚ)+K)/2
  | .C => (3*(q:ℚ)+K-2)/2
def parityGroup (C : ClassType) : Bool :=
  match C with | .B | .C | .zero => true | .A | .D => false
def ExceptionalSlack (n ℓ : ℕ) (s : Fin ℓ) (P Q : Ix n ℓ) : Prop :=
  (s=P.1 ∧ P.1≠Q.1 ∧ classType n ℓ s=.C ∧ Q.1.val=0 ∧
    Q.2.val+1=m n ℓ 0) ∨
  (s=Q.1 ∧ P.1≠Q.1 ∧ classType n ℓ s=.C ∧ P.1.val=0 ∧
    P.2.val+1=m n ℓ 0) ∨
  (classType n ℓ s=.C ∧ P.1.val=0 ∧ Q.1.val=0 ∧
    P.2.val+1=m n ℓ 0 ∧ Q.2.val+1=m n ℓ 0)

def Intg (ℓ : ℕ) [Fact ℓ.Prime] (x : Padic ℓ) : Prop := ‖x‖ ≤ 1
def Unit (ℓ : ℕ) [Fact ℓ.Prime] (x : Padic ℓ) : Prop := ‖x‖ = 1
def Vge (ℓ : ℕ) [Fact ℓ.Prime] (x : Padic ℓ) (e : ℤ) : Prop :=
  ‖x‖ ≤ (ℓ:ℝ)^(-(e:ℝ))
end
end CatalanCore.Li2.NV
