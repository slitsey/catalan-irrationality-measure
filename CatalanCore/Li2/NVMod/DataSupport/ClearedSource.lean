module
public import CatalanCore.Li2.NVMod.DataSupport.MomentClearing
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 1200000
open Polynomial Finset
open scoped BigOperators
namespace CatalanCore.Li2.NVMod.DataSupport
noncomputable section

def poleClearingPoly (S : Finset ℕ) (rho : ℕ→ℚ) (e cutoff : ℕ) : ℚ[X] :=
  ∑ m∈S,Polynomial.C (rho m*(-(m:ℚ))^e)*omegaNumerator cutoff m

def quotientClearingPoly (P : ℚ[X]) (order : ℕ) : ℚ[X] :=
  ∑ j∈Icc 1 P.natDegree,Polynomial.C ((j:ℚ)*P.coeff j)*liNumerator order (j-1)

def clearedSourcePoly (S : Finset ℕ) (rho : ℕ→ℚ) (P : ℚ[X])
    (e D cutoff order : ℕ) : ℚ[X] :=
  Polynomial.C (D:ℚ)*((1-X)^order*poleClearingPoly S rho e cutoff+
    X^cutoff*quotientClearingPoly P order)

theorem poleClearingPoly_spec (S : Finset ℕ) (rho : ℕ→ℚ) (e cutoff : ℕ)
    (hcut : ∀ m∈S,m≤cutoff) :
    rfPoly (poleClearingPoly S rho e cutoff)=
      (rfX:RatFunc ℚ)^cutoff*
        ∑ m∈S,((rho m*(-(m:ℚ))^e:ℚ):RatFunc ℚ)*omegaRF m := by
  simp only [poleClearingPoly,rfPoly,map_sum,map_mul,rationalMap_C,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  have hw := omegaNumerator_spec cutoff m (hcut m hm)
  change (algebraMap ℚ[X] (RatFunc ℚ)) (omegaNumerator cutoff m)=_ at hw
  rw [hw]
  push_cast
  ring

theorem quotientClearingPoly_spec (P : ℚ[X]) (order : ℕ)
    (horder : P.natDegree≤order) :
    rfPoly (quotientClearingPoly P order)=
      (1-rfX:RatFunc ℚ)^order*
        ∑ j∈Icc 1 P.natDegree,(j:RatFunc ℚ)*(P.coeff j:RatFunc ℚ)*liNeg (j-1) rfX := by
  simp only [quotientClearingPoly,rfPoly,map_sum,map_mul,rationalMap_C,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjO : j-1+1≤order := by have hb:=Finset.mem_Icc.mp hj;omega
  have hw := liNumerator_spec order (j-1) hjO
  change (algebraMap ℚ[X] (RatFunc ℚ)) (liNumerator order (j-1))=_ at hw
  rw [hw]
  push_cast
  ring

theorem clearedSourcePoly_spec (A : TypeKey) (S : Finset ℕ) (rho : ℕ→ℚ)
    (P : ℚ[X]) (e D cutoff order : ℕ)
    (hS : S=poleSet A) (hrho : ∀ m∈S,rho m=residue A m)
    (hP : polyPart A (X^e)=P) (hcut : ∀ m∈S,m≤cutoff)
    (horder : P.natDegree≤order) :
    rfPoly (clearedSourcePoly S rho P e D cutoff order)=
      rfPoly (Polynomial.C (D:ℚ))*(rfX:RatFunc ℚ)^cutoff*(1-rfX)^order*
        momentRF A (X^e) := by
  subst S
  have hm : momentRF A (X^e)=
      (∑ m∈poleSet A,((rho m*(-(m:ℚ))^e:ℚ):RatFunc ℚ)*omegaRF m)+
        ∑ j∈Icc 1 P.natDegree,(j:RatFunc ℚ)*(P.coeff j:RatFunc ℚ)*liNeg (j-1) rfX := by
    rw [momentRF_partial_fractions,hP]
    simp only [Polynomial.eval_pow,Polynomial.eval_X,eq_ratCast]
    congr 1
    apply Finset.sum_congr rfl
    intro m hm
    rw [hrho m hm]
  rw [hm]
  have hp := poleClearingPoly_spec (poleSet A) rho e cutoff hcut
  have hq := quotientClearingPoly_spec P order horder
  change (algebraMap ℚ[X] (RatFunc ℚ)) (poleClearingPoly (poleSet A) rho e cutoff)=_ at hp
  change (algebraMap ℚ[X] (RatFunc ℚ)) (quotientClearingPoly P order)=_ at hq
  simp only [clearedSourcePoly,rfPoly,map_mul,map_add,map_pow,map_sub,map_one,
    rationalMap_C,rationalMap_X]
  rw [hp,hq]
  ring
#print axioms clearedSourcePoly_spec
end
end CatalanCore.Li2.NVMod.DataSupport
