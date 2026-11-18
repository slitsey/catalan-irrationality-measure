module
public import CatalanCore.Li2.NVMod.CheckerSound
@[expose] public section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
open Polynomial Finset
open scoped BigOperators
namespace CatalanCore.Li2.NVMod
noncomputable section

def poles (A : TypeKey) : Finset ℕ :=
  match A.kind with
  | .V=>Finset.Ico A.a A.c
  | .U=>Finset.Ico (A.a+1) (A.c+1)
def numeratorK (K : Type*) [Field K] (A : TypeKey) : K[X] :=
  match A.kind with
  | .V=>∏ m∈Finset.range A.a,(X+C (m:K))^2
  | .U=>X*∏ m∈Finset.Icc 1 A.a,(X+C (m:K))^2
def denominatorK (K : Type*) [Field K] (A : TypeKey) : K[X] :=
  ∏ m∈poles A,(X+C (m:K))
def quotientK (K : Type*) [Field K] (A : TypeKey) (e : ℕ) : K[X] :=
  (X^e*numeratorK K A) /ₘ denominatorK K A
def formulaTau (K : Type*) [Field K] (r : K) (m : ℕ) : K :=
  ∑ b∈Finset.Icc 1 m,r^b/(b:K)^2
def formulaLiNeg (K : Type*) [Field K] (r : K) (j : ℕ) : K :=
  if j=0 then r/(1-r) else
    ∑ i∈Finset.Icc 1 j,(Nat.stirlingSecond j i:K)*(Nat.factorial i:K)*r^i/(1-r)^(i+1)
def residueK (K : Type*) [Field K] (A : TypeKey) (e m : ℕ) : K :=
  (X^e*numeratorK K A).eval (-(m:K))/(denominatorK K A).derivative.eval (-(m:K))
def momentFormula (K : Type*) [Field K] (A : TypeKey) (r : K) (e : ℕ) : K :=
  let q := quotientK K A e
  (∑ k∈Finset.range (q.natDegree+1),(k:K)*q.coeff k*formulaLiNeg K r (k-1))+
    ∑ m∈(poles A).filter (0<·),residueK K A e m*(r^m)⁻¹*formulaTau K r m
def goodFormulaPrime (A : TypeKey) (p : ℕ) : Prop := p.Prime ∧ ∀ m∈poles A,m<p
def momentNat (p : ℕ) [Fact p.Prime] (A : TypeKey) (r e : ℕ) : ℕ :=
  (momentFormula (ZMod p) A (r:ZMod p) e).val
def momentRow (p : ℕ) [Fact p.Prime] (A : TypeKey) (r : ℕ) : List (ZMod p) :=
  (List.range (2*A.size-1)).map (fun e=>(momentNat p A r e:ZMod p))

def numeratorZ (A : TypeKey) : ℤ[X] :=
  match A.kind with
  | .V=>∏ m∈Finset.range A.a,(X+C (m:ℤ))^2
  | .U=>X*∏ m∈Finset.Icc 1 A.a,(X+C (m:ℤ))^2
def denominatorZ (A : TypeKey) : ℤ[X] := ∏ m∈poles A,(X+C (m:ℤ))
def quotientZ (A : TypeKey) (e : ℕ) : ℤ[X] := (X^e*numeratorZ A) /ₘ denominatorZ A

theorem poles_eq_poleSet (A : TypeKey) : poles A=poleSet A := by
  ext m
  cases hk : A.kind <;> simp only [poles,poleSet,hk,Finset.mem_Ico,Finset.mem_Ioc] <;> omega
theorem denominatorZ_monic (A : TypeKey) : (denominatorZ A).Monic :=
  Polynomial.monic_prod_of_monic _ _ (fun _ _=>Polynomial.monic_X_add_C _)
theorem denominatorK_monic (K : Type*) [Field K] (A : TypeKey) : (denominatorK K A).Monic :=
  Polynomial.monic_prod_of_monic _ _ (fun _ _=>Polynomial.monic_X_add_C _)

theorem numeratorZ_map (K : Type*) [Field K] (A : TypeKey) :
    (numeratorZ A).map (Int.castRingHom K)=numeratorK K A := by
  cases hk : A.kind <;> simp [numeratorZ,numeratorK,hk,Polynomial.map_prod]
theorem denominatorZ_map (K : Type*) [Field K] (A : TypeKey) :
    (denominatorZ A).map (Int.castRingHom K)=denominatorK K A := by
  simp [denominatorZ,denominatorK,Polynomial.map_prod]
theorem quotientZ_map (K : Type*) [Field K] (A : TypeKey) (e : ℕ) :
    (quotientZ A e).map (Int.castRingHom K)=quotientK K A e := by
  rw [quotientZ,Polynomial.map_divByMonic _ (denominatorZ_monic A)]
  simp [quotientK,numeratorZ_map,denominatorZ_map]

theorem numeratorK_Q (A : TypeKey) : numeratorK ℚ A=weightNum A := by cases A.kind <;> rfl
theorem denominatorK_Q (A : TypeKey) : denominatorK ℚ A=weightDen A := by
  simp only [denominatorK,weightDen,poles_eq_poleSet]
theorem quotientK_Q (A : TypeKey) (e : ℕ) : quotientK ℚ A e=polyPart A (X^e) := by
  simp only [quotientK,numeratorK_Q,denominatorK_Q,polyPart,mul_comm]
theorem formulaLiNeg_eq {K : Type*} [Field K] (r : K) (j : ℕ) : formulaLiNeg K r j=liNeg j r := rfl

#print axioms quotientZ_map
#print axioms quotientK_Q
end
end CatalanCore.Li2.NVMod
