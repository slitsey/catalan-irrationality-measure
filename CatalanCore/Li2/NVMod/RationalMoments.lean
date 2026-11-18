module
public import CatalanCore.Li2.NVMod.Series
public import CatalanCore.Li2.NVMod.Moments
@[expose] public section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
open Polynomial Matrix Finset
open scoped BigOperators
namespace CatalanCore.Li2.NVMod
noncomputable section
private theorem rfPoly_C (q : ℚ) : rfPoly (C q)=algebraMap ℚ (RatFunc ℚ) q := by
  simpa [rfPoly] using (RatFunc.algebraMap_apply (K:=ℚ) q).symm
private theorem omegaRF_factor (m : ℕ) :
    omegaRF m=rfX^(-(m:ℤ))*tauK (rfX : RatFunc ℚ) m := by
  have hx : (rfX : RatFunc ℚ)≠0 := RatFunc.algebraMap_ne_zero Polynomial.X_ne_zero
  unfold omegaRF tauK
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  rw [show (b:ℤ)-m=-(m:ℤ)+(b:ℤ) by omega,zpow_add₀ hx,rfPoly_C]
  simp only [map_pow,map_natCast,zpow_natCast]
  ring
private theorem regularV_fraction_rf (P : ℚ[X]) (S : Finset ℕ) :
    regularV (rfX : RatFunc ℚ) (rfPoly P/rfPoly (poleProd S))=
      (∑ m∈S,algebraMap ℚ (RatFunc ℚ) (poleCoeff P S m)*omegaRF m)+
        ∑ k∈Finset.Icc 1 (P /ₘ poleProd S).natDegree,
          (k:RatFunc ℚ)*algebraMap ℚ (RatFunc ℚ) ((P /ₘ poleProd S).coeff k)*liNeg (k-1) rfX := by
  classical
  let F:=rfPoly P/rfPoly (poleProd S)
  have hc:=fraction_coefficients P S
  have hdiv : F.denom∣poleProd S:=RatFunc.denom_div_dvd P (poleProd S)
  obtain ⟨hD,hI⟩:=canonical_poles F S hdiv
  have hsub : poleIndices F⊆S := by rw [hI];exact Finset.filter_subset _ _
  change (∑ m∈poleIndices F,algebraMap ℚ (RatFunc ℚ) (poleRes F m)*rfX^(-(m:ℤ))*tauK rfX m)+
    (∑ k∈Finset.Icc 1 (pp F).natDegree,(k:RatFunc ℚ)*algebraMap ℚ (RatFunc ℚ) ((pp F).coeff k)*liNeg (k-1) rfX)=_
  rw [hc.1]
  congr 1
  let f : ℕ→RatFunc ℚ:=fun m=>algebraMap ℚ (RatFunc ℚ) (if m∈poleIndices F then poleRes F m else 0)*rfX^(-(m:ℤ))*tauK rfX m
  calc
    (∑ m∈poleIndices F,algebraMap ℚ (RatFunc ℚ) (poleRes F m)*rfX^(-(m:ℤ))*tauK rfX m)=∑ m∈poleIndices F,f m := by
      apply Finset.sum_congr rfl
      intro m hm
      simp only [f,if_pos hm]
    _=∑ m∈S,f m:=Finset.sum_subset hsub (fun m hmS hmI=>by simp [f,hmI])
    _=∑ m∈S,algebraMap ℚ (RatFunc ℚ) (poleCoeff P S m)*omegaRF m := by
      apply Finset.sum_congr rfl
      intro m hm
      dsimp only [f]
      rw [hc.2 m hm,omegaRF_factor]
      ring
theorem momentRF_partial_fractions (A : TypeKey) (g : ℚ[X]) :
    momentRF A g=
      (∑ m∈poleSet A,algebraMap ℚ (RatFunc ℚ) (residue A m*g.eval (-(m:ℚ)))*omegaRF m)+
        ∑ k∈Finset.Icc 1 (polyPart A g).natDegree,
          (k:RatFunc ℚ)*algebraMap ℚ (RatFunc ℚ) ((polyPart A g).coeff k)*liNeg (k-1) rfX := by
  have hf : rfPoly g*weight A=rfPoly (weightNum A*g)/rfPoly (poleProd (poleSet A)) := by
    simp only [weight,weightDen,poleProd,rfPoly,map_mul,div_eq_mul_inv]
    ring
  unfold momentRF
  rw [hf,regularV_fraction_rf]
  congr 1
  apply Finset.sum_congr rfl
  intro m hm
  congr 2
  simp only [poleCoeff,poleProd,residue,weightDen,eval_mul,div_eq_mul_inv]
  ring
#print axioms momentRF_partial_fractions
end
end CatalanCore.Li2.NVMod
