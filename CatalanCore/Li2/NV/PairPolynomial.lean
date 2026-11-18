module
public import CatalanCore.Li2.NV.Classes
public import CatalanCore.Li2.NV.Binomial
public import Mathlib.Data.Rat.Lemmas
public import Mathlib.Data.Nat.PrimeFin
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith
@[expose] public section
open Polynomial Finset
open scoped BigOperators
namespace CatalanCore.Li2.NV
noncomputable section
noncomputable def coeffDen (P : ℚ[X]) : ℕ := ∏ i∈P.support, (P.coeff i).den
noncomputable def clearDen (P : ℚ[X]) : ℤ[X] :=
  ∑ i∈P.support, Polynomial.monomial i (((coeffDen P:ℚ)*P.coeff i).num)

theorem clearDen_spec (P : ℚ[X]) :
  0<coeffDen P ∧ (clearDen P).map (Int.castRingHom ℚ)=C (coeffDen P:ℚ)*P := by
  classical
  refine ⟨Finset.prod_pos (fun i hi => (P.coeff i).pos),?_⟩
  have hint : ∀ i∈P.support, ∃ z:ℤ, (coeffDen P:ℚ)*P.coeff i=z := by
    intro i hi
    have hd : (P.coeff i).den∣coeffDen P := Finset.dvd_prod_of_mem (fun j => (P.coeff j).den) hi
    obtain ⟨t,ht⟩:=hd
    refine ⟨(t:ℤ)*(P.coeff i).num,?_⟩
    rw [ht]
    push_cast
    have he : P.coeff i*((P.coeff i).den:ℚ)=(P.coeff i).num :=
      (eq_div_iff (by exact_mod_cast (P.coeff i).den_ne_zero)).mp (P.coeff i).num_div_den.symm
    calc
      ((P.coeff i).den:ℚ)*t*P.coeff i=(t:ℚ)*(P.coeff i*((P.coeff i).den:ℚ)) := by ring
      _ = _ := by rw [he]
  ext i
  simp only [coeff_map,coeff_C_mul]
  by_cases hi : i∈P.support
  · obtain ⟨z,hz⟩:=hint i hi
    simp only [clearDen,finsetSum_coeff,coeff_monomial]
    rw [Finset.sum_eq_single i]
    · simp only [ite_true,hz,Rat.num_intCast]
      rfl
    · intro b hb hbi
      simp [hbi]
    · exact fun h => False.elim (h hi)
  · have hz : P.coeff i=0 := Polynomial.notMem_support_iff.mp hi
    simp [clearDen,finsetSum_coeff,coeff_monomial,hi,hz]

private theorem pair_degree (y : ℚ) : (pairPoly y).natDegree≤3 := by
  unfold pairPoly
  apply (natDegree_add_le _ _).trans
  apply max_le
  · apply (natDegree_add_le _ _).trans
    apply max_le
    · exact (natDegree_C_mul_le _ _).trans (by simp)
    · exact (natDegree_C_mul_X_pow_le _ 2).trans (by decide)
  · exact natDegree_C_mul_X_pow_le _ 3

private theorem pair_ne_zero (y : ℚ) (hy : y≠0) : pairPoly y≠0 := by
  intro he
  have h1:=congrArg (fun p : ℚ[X] => p.coeff 1) he
  have h2:=congrArg (fun p : ℚ[X] => p.coeff 2) he
  simp only [pairPoly,coeff_add,coeff_C_mul,coeff_X,coeff_X_pow,coeff_zero] at h1 h2
  norm_num at h1 h2
  have hid : (-2781*y^2+15198*y-10208)*(-18*y^4+132*y^3-180*y^2+72*y)+
      (618*y^2-4064*y+3076)*(-81*y^4+504*y^3-636*y^2+240*y)=3264*y := by ring
  simp only [neg_mul] at hid
  rw [h1,h2,mul_zero,mul_zero,zero_add] at hid
  exact hy (by linarith)

theorem pair_poly_nonzero (y : ℚ) (hy : y≠0) :
  (pairPoly y).natDegree≤3 ∧ pairPoly y≠0 ∧
    ∃ bad : Finset ℕ, ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ∉bad →
      ((clearDen (pairPoly y)).map (Int.castRingHom (ZMod ℓ))).natDegree≤3 ∧
      (clearDen (pairPoly y)).map (Int.castRingHom (ZMod ℓ))≠0 ∧
      ((clearDen (pairPoly y)).map (Int.castRingHom (ZMod ℓ))).roots.toFinset.card≤3 := by
  classical
  have hp:=pair_ne_zero y hy
  have hs:=clearDen_spec (pairPoly y)
  let F:=clearDen (pairPoly y)
  have hf : F≠0 := by
    intro hz
    have he:=hs.2
    change F.map (Int.castRingHom ℚ)=_ at he
    rw [hz,Polynomial.map_zero] at he
    exact (mul_ne_zero (Polynomial.C_ne_zero.mpr (by exact_mod_cast hs.1.ne')) hp) he.symm
  have hd : F.natDegree≤3 := by
    rw [← Polynomial.natDegree_map_eq_of_injective (f:=Int.castRingHom ℚ) (by intro a b h; change (a:ℚ)=(b:ℚ) at h; exact_mod_cast h) F]
    change (F.map (Int.castRingHom ℚ)).natDegree≤3
    rw [show F.map (Int.castRingHom ℚ)=C (coeffDen (pairPoly y):ℚ)*pairPoly y from hs.2]
    exact (natDegree_C_mul_le _ _).trans (pair_degree y)
  have hl : F.leadingCoeff≠0 := Polynomial.leadingCoeff_ne_zero.mpr hf
  refine ⟨pair_degree y,hp,F.leadingCoeff.natAbs.primeFactors,?_⟩
  intro ℓ inst hbad
  have hprime : ℓ.Prime := Fact.out
  let G:=F.map (Int.castRingHom (ZMod ℓ))
  have hgd : G.natDegree≤3 := (Polynomial.natDegree_map_le).trans hd
  have hg : G≠0 := by
    intro hz
    have hc:=congrArg (fun p : (ZMod ℓ)[X] => p.coeff F.natDegree) hz
    change (F.map (Int.castRingHom (ZMod ℓ))).coeff F.natDegree=0 at hc
    simp only [Polynomial.coeff_map,Polynomial.coeff_natDegree] at hc
    have hdvd : (ℓ:ℤ)∣F.leadingCoeff := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hc
    have hn : ℓ∣F.leadingCoeff.natAbs := by
      exact Int.natCast_dvd.mp hdvd
    exact hbad (Nat.mem_primeFactors.mpr ⟨hprime,hn,Int.natAbs_ne_zero.mpr hl⟩)
  exact ⟨hgd,hg,(Multiset.toFinset_card_le _).trans ((Polynomial.card_roots' G).trans hgd)⟩

#print axioms clearDen_spec
#print axioms pair_poly_nonzero
end
end CatalanCore.Li2.NV
