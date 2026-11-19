module
public import CatalanCore.Li2.NVMod.DataSupport.PolynomialFamily
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
open Polynomial Finset
open scoped BigOperators
namespace CatalanCore.Li2.NVMod.DataSupport
noncomputable section
structure MomentCache where
  power : List ℚ
  omega : ℕ→List ℚ
  li : ℕ→List ℚ

def cachedPoleCoefficients (C : MomentCache) (ms : List ℕ) (rho : ℕ→ℚ) (e : ℕ) : List ℚ :=
  sumCoefficients (ms.map (fun (m : ℕ)=>coefficientsScale (rho m*(-(m:ℚ))^e) (C.omega m)))
def cachedQuotientCoefficients (C : MomentCache) (qs : List ℚ) : List ℚ :=
  sumCoefficients ((List.range qs.length).map (fun (j : ℕ)=>
    coefficientsScale ((j:ℚ)*qs.getD j 0) (C.li (j-1))))
def cachedClearedCoefficients (C : MomentCache) (ms : List ℕ) (rho : ℕ→ℚ) (qs : List ℚ)
    (e D cutoff : ℕ) : List ℚ :=
  coefficientsScale (D:ℚ) (coefficientsAdd
    (coefficientsMul C.power (cachedPoleCoefficients C ms rho e))
    (coefficientsMul (monomialCoefficients cutoff 1) (cachedQuotientCoefficients C qs)))

theorem cachedPole_spec (C : MomentCache) (ms : List ℕ) (rho : ℕ→ℚ) (e cutoff : ℕ)
    (hn : ms.Nodup) (ho : ∀ m∈ms.toFinset,coefficientsPoly (C.omega m)=omegaNumerator cutoff m) :
    coefficientsPoly (cachedPoleCoefficients C ms rho e)=poleClearingPoly ms.toFinset rho e cutoff := by
  simp only [cachedPoleCoefficients,sumCoefficients_spec,List.map_map,Function.comp_def,
    coefficientsPoly_scale]
  rw [←List.sum_toFinset (fun m : ℕ=>Polynomial.C (rho m*(-(m:ℚ))^e)*coefficientsPoly (C.omega m)) hn]
  apply Finset.sum_congr rfl
  intro m hm
  rw [ho m hm]

theorem cachedQuotient_spec (C : MomentCache) (qs : List ℚ) (order : ℕ)
    (hl : ∀ j<qs.length,coefficientsPoly (C.li (j-1))=liNumerator order (j-1)) :
    coefficientsPoly (cachedQuotientCoefficients C qs)=quotientClearingPoly (coefficientsPoly qs) order := by
  cases qs with
  | nil=>simp [cachedQuotientCoefficients,sumCoefficients,coefficientsPoly,quotientClearingPoly]
  | cons a as=>
    have hd : (coefficientsPoly (a::as)).natDegree<(a::as).length :=
      Nat.lt_succ_of_le (coefficients_natDegree_bound _ as.length (by simp))
    rw [quotientClearingPoly_sum,Polynomial.sum_over_range' _ (by intro j;simp) _ hd]
    simp only [cachedQuotientCoefficients,sumCoefficients_spec,List.map_map,Function.comp_def,
      coefficientsPoly_scale,range_sum,coefficientsPoly_coeff]
    apply Finset.sum_congr rfl
    intro j hj
    rw [hl j (Finset.mem_range.mp hj)]

theorem cachedCleared_spec (C : MomentCache) (ms : List ℕ) (rho : ℕ→ℚ) (qs : List ℚ)
    (e D cutoff order : ℕ) (hn : ms.Nodup)
    (hp : coefficientsPoly C.power=(1-X:ℚ[X])^order)
    (ho : ∀ m∈ms.toFinset,coefficientsPoly (C.omega m)=omegaNumerator cutoff m)
    (hl : ∀ j<qs.length,coefficientsPoly (C.li (j-1))=liNumerator order (j-1)) :
    coefficientsPoly (cachedClearedCoefficients C ms rho qs e D cutoff)=
      clearedSourcePoly ms.toFinset rho (coefficientsPoly qs) e D cutoff order := by
  rw [cachedClearedCoefficients,coefficientsPoly_scale,coefficientsPoly_add,
    coefficientsPoly_mul,coefficientsPoly_mul,hp,cachedPole_spec C ms rho e cutoff hn ho,
    monomialCoefficients_spec,cachedQuotient_spec C qs order hl]
  simp only [map_one,one_mul]
  rfl

def cachedMomentCheck (C : MomentCache) (L : ℕ) (ms : List ℕ) (rho : ℕ→ℚ)
    (qs zs : List ℤ) (e D cutoff : ℕ) : Bool :=
  decide (padCoefficients L (zs.map (fun (z : ℤ)=>(z:ℚ)))=
    padCoefficients L (cachedClearedCoefficients C ms rho (qs.map (fun (z : ℤ)=>(z:ℚ))) e D cutoff))

theorem moment_from_cached_check (C : MomentCache) (A : TypeKey) (L : ℕ) (ms : List ℕ)
    (rho : ℕ→ℚ) (qs zs : List ℤ) (e D cutoff order : ℕ)
    (hN : ms.Nodup) (hS : ms.toFinset=poleSet A)
    (hrho : ∀ m∈ms.toFinset,rho m=residue A m)
    (hQ : (coefficientsPoly qs).map (Int.castRingHom ℚ)=polyPart A (X^e))
    (hcut : ∀ m∈ms.toFinset,m≤cutoff) (horder : qs.length≤order+1)
    (hp : coefficientsPoly C.power=(1-X:ℚ[X])^order)
    (ho : ∀ m∈ms.toFinset,coefficientsPoly (C.omega m)=omegaNumerator cutoff m)
    (hl : ∀ j<qs.length,coefficientsPoly (C.li (j-1))=liNumerator order (j-1))
    (hc : cachedMomentCheck C L ms rho qs zs e D cutoff=true) :
    intPolyRF (coefficientsPoly zs)=rfPoly (Polynomial.C (D:ℚ))*rfX^cutoff*(1-rfX)^order*
      momentRF A (X^e) := by
  have he : padCoefficients L (zs.map (fun (z : ℤ)=>(z:ℚ)))=
      padCoefficients L (cachedClearedCoefficients C ms rho (qs.map (fun (z : ℤ)=>(z:ℚ))) e D cutoff) :=
    of_decide_eq_true hc
  have hpoly:=congrArg (coefficientsPoly (R:=ℚ)) he
  simp only [padCoefficients_spec] at hpoly
  rw [cachedCleared_spec C ms rho _ e D cutoff order hN hp ho
    (by simpa only [List.length_map] using hl)] at hpoly
  change rfPoly ((coefficientsPoly zs).map (Int.castRingHom ℚ))=_
  rw [coefficientsPoly_map]
  change rfPoly (coefficientsPoly (zs.map (fun (z : ℤ)=>(z:ℚ))))=_
  rw [hpoly]
  apply clearedSourcePoly_spec A ms.toFinset rho _ e D cutoff order hS hrho ?_ hcut ?_
  · simpa only [coefficientsPoly_map,Int.coe_castRingHom] using hQ.symm
  · apply coefficients_natDegree_bound
    simpa using horder
#print axioms moment_from_cached_check
end
end CatalanCore.Li2.NVMod.DataSupport
