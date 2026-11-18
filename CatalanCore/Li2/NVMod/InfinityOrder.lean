module
public import CatalanCore.Li2.NVMod.InfinityMoments
public import CatalanCore.Li2.NVMod.InfinityWeight
public import CatalanCore.Li2.NVMod.HermiteJet
@[expose] public section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
open Polynomial Finset
open scoped BigOperators
namespace CatalanCore.Li2.NVMod
noncomputable section

theorem moment_prefix_coeff_zero (A : TypeKey) (g : ℚ[X]) (t : ℕ)
    (ht : t∈poleSet A)
    (hprev : ∀ u∈poleSet A,u<t→(X+C (u:ℚ))^3∣g)
    (hU : A.kind=.U→X∣g) (u : ℕ) (hut : u<t) :
    (atInf (momentRF A g)).coeff (u:ℤ)=0 := by
  rw [(moment_at_infinity A g).2 u]
  have hs : (∑ m∈(poleSet A).filter (fun m=>m<u),
      residue A m*g.eval (-(m:ℚ))/((m:ℚ)-u)^2)=0 := by
    apply Finset.sum_eq_zero
    intro m hm
    obtain ⟨hm,hmu⟩ := Finset.mem_filter.mp hm
    obtain ⟨R,hR⟩ := hprev m hm (by omega)
    rw [hR]
    simp [Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_add]
  rw [hs,neg_zero,zero_sub]
  by_cases hu : u∈poleSet A
  · rw [if_pos hu]
    obtain ⟨R,hR⟩ := hprev u hu hut
    let W := (rfX+rfPoly (C (u:ℚ)))*weight A
    have hW : RFRegular (-(u:ℚ)) W := weight_removed_regular A u hu
    have he : (rfX+rfPoly (C (u:ℚ)))*rfPoly g*weight A=
        (W*rfPoly R)*rfPoly ((X+C (u:ℚ))^3) := by
      rw [hR]
      dsimp only [W]
      simp only [rfPoly,map_mul]
      ring
    rw [he,second_product_vanish _ u 3 (hW.mul (RFRegular.poly _ _)) (by omega)]
    norm_num
  · rw [if_neg hu]
    have hd := off_pole_double_dvd A g u t ht hut hu (fun hk _=>hU hk)
    obtain ⟨F,hF,he⟩ := weight_poly_factor_regular A g u 2 hu hd
    rw [he,first_product_vanish F u 2 hF (by omega),neg_zero]

theorem moment_prefix_order (A : TypeKey) (g : ℚ[X]) (t : ℕ)
    (ht : t∈poleSet A)
    (hprev : ∀ u∈poleSet A,u<t→(X+C (u:ℚ))^3∣g)
    (hU : A.kind=.U→X∣g) : Oge (atInf (momentRF A g)) (t:ℤ) := by
  intro e he
  by_cases hn : e<0
  · exact (moment_at_infinity A g).1 e hn
  · have hen : (e.toNat:ℤ)=e := Int.toNat_of_nonneg (by omega)
    rw [←hen]
    apply moment_prefix_coeff_zero A g t ht hprev hU e.toNat
    omega

#print axioms moment_prefix_coeff_zero
#print axioms moment_prefix_order
end
end CatalanCore.Li2.NVMod
