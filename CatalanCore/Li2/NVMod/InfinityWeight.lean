module
public import CatalanCore.Li2.NVMod.InfinityDefinitions
@[expose] public section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
open Polynomial Finset
open scoped BigOperators
namespace CatalanCore.Li2.NVMod
noncomputable section

theorem poleProd_monic' (S : Finset ℕ) : (poleProd S).Monic :=
  Polynomial.monic_prod_of_monic _ _ (fun _ _=>Polynomial.monic_X_add_C _)

theorem poleProd_eval_ne (S : Finset ℕ) (t : ℕ) (ht : t∉S) :
    (poleProd S).eval (-(t:ℚ))≠0 := by
  simp only [poleProd,Polynomial.eval_prod,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_C]
  apply Finset.prod_ne_zero_iff.mpr
  intro m hm
  have hmt : m≠t := by intro he; exact ht (he ▸ hm)
  have hn : (m:ℚ)-(t:ℚ)≠0 := sub_ne_zero.mpr (by exact_mod_cast hmt)
  simpa only [sub_eq_add_neg,add_comm] using hn

theorem weightDen_split (A : TypeKey) (t : ℕ) (ht : t∈poleSet A) :
    weightDen A=(X+C (t:ℚ))*poleProd ((poleSet A).erase t) := by
  exact (Finset.mul_prod_erase _ _ ht).symm

theorem weight_regular_off (A : TypeKey) (t : ℕ) (ht : t∉poleSet A) :
    RFRegular (-(t:ℚ)) (weight A) := by
  exact RFRegular.fraction _ _ _ (poleProd_monic' (poleSet A)).ne_zero
    (poleProd_eval_ne _ t ht)

theorem weight_removed (A : TypeKey) (t : ℕ) (ht : t∈poleSet A) :
    (rfX+rfPoly (C (t:ℚ)))*weight A=
      rfPoly (weightNum A)/rfPoly (poleProd ((poleSet A).erase t)) := by
  have hl : rfPoly (X+C (t:ℚ))≠0 := RatFunc.algebraMap_ne_zero (Polynomial.monic_X_add_C _).ne_zero
  have hq : rfPoly (poleProd ((poleSet A).erase t))≠0 := RatFunc.algebraMap_ne_zero (poleProd_monic' _).ne_zero
  rw [weight,weightDen_split A t ht]
  change (rfPoly X+rfPoly (C (t:ℚ)))*
    (rfPoly (weightNum A)/rfPoly ((X+C (t:ℚ))*poleProd ((poleSet A).erase t)))= _
  simp only [rfPoly,map_add,map_mul] at hl hq ⊢
  field_simp

theorem weight_removed_regular (A : TypeKey) (t : ℕ) (ht : t∈poleSet A) :
    RFRegular (-(t:ℚ)) ((rfX+rfPoly (C (t:ℚ)))*weight A) := by
  rw [weight_removed A t ht]
  exact RFRegular.fraction _ _ _ (poleProd_monic' _).ne_zero
    (poleProd_eval_ne _ t (Finset.notMem_erase _ _))

theorem weight_removed_eval (A : TypeKey) (t : ℕ) (ht : t∈poleSet A) :
    rfEval ((rfX+rfPoly (C (t:ℚ)))*weight A) (-(t:ℚ))=residue A t := by
  have hq := poleProd_eval_ne ((poleSet A).erase t) t (Finset.notMem_erase _ _)
  rw [rfEval_fraction _ (weightNum A) (poleProd ((poleSet A).erase t)) _
    (poleProd_monic' _).ne_zero hq (weight_removed A t ht)]
  unfold residue
  rw [weightDen_split A t ht]
  simp [Polynomial.derivative_mul,Polynomial.eval_add,Polynomial.eval_mul]

theorem weightNum_pole_ne (A : TypeKey) (t : ℕ) (ht : t∈poleSet A) :
    (weightNum A).eval (-(t:ℚ))≠0 := by
  cases hk : A.kind
  · simp only [poleSet,hk,Finset.mem_Ico] at ht
    simp only [weightNum,hk,Polynomial.eval_prod,Polynomial.eval_pow,
      Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_C]
    apply Finset.prod_ne_zero_iff.mpr
    intro m hm
    have hmt : m≠t := by simp only [Finset.mem_range] at hm; omega
    apply pow_ne_zero
    have hn : (m:ℚ)-(t:ℚ)≠0 := sub_ne_zero.mpr (by exact_mod_cast hmt)
    simpa only [sub_eq_add_neg,add_comm] using hn
  · simp only [poleSet,hk,Finset.mem_Ioc] at ht
    simp only [weightNum,hk,Polynomial.eval_mul,Polynomial.eval_X,Polynomial.eval_prod,
      Polynomial.eval_pow,Polynomial.eval_add,Polynomial.eval_C]
    apply mul_ne_zero (neg_ne_zero.mpr (by exact_mod_cast (show t≠0 by omega)))
    apply Finset.prod_ne_zero_iff.mpr
    intro m hm
    have hmt : m≠t := by simp only [Finset.mem_Icc] at hm; omega
    apply pow_ne_zero
    have hn : (m:ℚ)-(t:ℚ)≠0 := sub_ne_zero.mpr (by exact_mod_cast hmt)
    simpa only [sub_eq_add_neg,add_comm] using hn

theorem residue_ne_zero (A : TypeKey) (t : ℕ) (ht : t∈poleSet A) : residue A t≠0 := by
  unfold residue
  apply div_ne_zero (weightNum_pole_ne A t ht)
  rw [weightDen_split A t ht]
  simpa [Polynomial.derivative_mul,Polynomial.eval_mul,Polynomial.eval_add] using
    poleProd_eval_ne ((poleSet A).erase t) t (Finset.notMem_erase _ _)

theorem polePhi_regular (A : TypeKey) (Q : ℚ[X]) (t : ℕ) (ht : t∈poleSet A) :
    RFRegular (-(t:ℚ)) ((rfX+rfPoly (C (t:ℚ)))*(rfPoly Q)^2*weight A) := by
  have he : (rfX+rfPoly (C (t:ℚ)))*(rfPoly Q)^2*weight A=
      rfPoly (Q^2)*((rfX+rfPoly (C (t:ℚ)))*weight A) := by
    simp only [rfPoly,map_pow]
    ring
  rw [he]
  exact (RFRegular.poly _ _).mul (weight_removed_regular A t ht)

theorem polePhi_eval (A : TypeKey) (Q : ℚ[X]) (t : ℕ) (ht : t∈poleSet A) :
    rfEval ((rfX+rfPoly (C (t:ℚ)))*(rfPoly Q)^2*weight A) (-(t:ℚ))=
      residue A t*(Q.eval (-(t:ℚ)))^2 := by
  have he : (rfX+rfPoly (C (t:ℚ)))*(rfPoly Q)^2*weight A=
      rfPoly (Q^2)*((rfX+rfPoly (C (t:ℚ)))*weight A) := by
    simp only [rfPoly,map_pow]
    ring
  rw [he,rfEval_mul (RFRegular.poly _ _) (weight_removed_regular A t ht),
    rfEval_poly,Polynomial.eval_pow,weight_removed_eval A t ht,mul_comm]

theorem off_pole_double_dvd (A : TypeKey) (Q : ℚ[X]) (u t : ℕ)
    (ht : t∈poleSet A) (hut : u<t) (hu : u∉poleSet A)
    (hU : A.kind=.U→u=0→X∣Q) :
    (X+C (u:ℚ))^2∣Q*weightNum A := by
  cases hk : A.kind
  · have hua : u<A.a := by
      simp only [poleSet,hk,Finset.mem_Ico] at ht hu
      omega
    apply dvd_mul_of_dvd_right
    simp only [weightNum,hk]
    exact Finset.dvd_prod_of_mem _ (Finset.mem_range.mpr hua)
  · have hua : u≤A.a := by
      simp only [poleSet,hk,Finset.mem_Ioc] at ht hu
      omega
    by_cases hz : u=0
    · obtain ⟨R,hR⟩ := hU hk hz
      rw [hz,hR]
      simp only [Nat.cast_zero,map_zero,add_zero,weightNum,hk]
      refine ⟨R*(∏ j∈Finset.Icc 1 A.a,(X+C (j:ℚ))^2),?_⟩
      ring
    · apply dvd_mul_of_dvd_right
      simp only [weightNum,hk]
      apply dvd_mul_of_dvd_right
      exact Finset.dvd_prod_of_mem _ (Finset.mem_Icc.mpr ⟨by omega,hua⟩)

theorem weight_poly_factor_regular (A : TypeKey) (Q : ℚ[X]) (u d : ℕ)
    (hu : u∉poleSet A) (hdiv : (X+C (u:ℚ))^d∣Q*weightNum A) :
    ∃ F : RatFunc ℚ, RFRegular (-(u:ℚ)) F ∧
      rfPoly Q*weight A=F*rfPoly ((X+C (u:ℚ))^d) := by
  obtain ⟨R,hR⟩ := hdiv
  refine ⟨rfPoly R/rfPoly (weightDen A),?_,?_⟩
  · exact RFRegular.fraction _ _ _ (poleProd_monic' _).ne_zero (poleProd_eval_ne _ u hu)
  · unfold weight
    have he : rfPoly Q*rfPoly (weightNum A)=rfPoly ((X+C (u:ℚ))^d)*rfPoly R := by
      simpa only [rfPoly,map_mul] using congrArg rfPoly hR
    calc
      rfPoly Q*(rfPoly (weightNum A)/rfPoly (weightDen A))=
          (rfPoly Q*rfPoly (weightNum A))/rfPoly (weightDen A) := by ring
      _ = (rfPoly ((X+C (u:ℚ))^d)*rfPoly R)/rfPoly (weightDen A) := by rw [he]
      _ = _ := by ring

#print axioms weight_removed_regular
#print axioms weight_removed_eval
#print axioms residue_ne_zero
#print axioms polePhi_eval
#print axioms off_pole_double_dvd
#print axioms weight_poly_factor_regular
end
end CatalanCore.Li2.NVMod
