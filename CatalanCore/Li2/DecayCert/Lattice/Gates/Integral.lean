module
public import CatalanCore.Li2.DecayCert.Lattice.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 600000
open Polynomial Set MeasureTheory
open scoped BigOperators
open CatalanCore.Uniform.Decay.Tools
namespace CatalanCore.Li2.DecayCert.LatticeGate

theorem bern_mean (a : ℕ→ℝ) (n : ℕ) :
    (∑ k ∈ Finset.range (n+1),bern a n k)/((n+1:ℕ):ℝ)=
      ∑ i ∈ Finset.range (n+1),a i/((i+1:ℕ):ℝ) := by
  unfold bern
  have hswap := Finset.sum_Ico_Ico_comm (M:=ℝ) 0 (n+1)
    (fun i k=>((k.choose i:ℕ):ℝ)/((n.choose i:ℕ):ℝ)*a i)
  simp only [Finset.range_eq_Ico] at hswap ⊢
  rw [← hswap,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  have hin : i≤n := by have := Finset.mem_Ico.mp hi;omega
  have hn : ((n+1:ℕ):ℝ)≠0 := by positivity
  have hi0 : ((i+1:ℕ):ℝ)≠0 := by positivity
  have hc0 : (n.choose i:ℝ)≠0 := by exact_mod_cast (Nat.choose_pos hin).ne'
  have hs : (∑ k ∈ Finset.Ico i (n+1),(k.choose i:ℝ))=((n+1).choose (i+1):ℝ) := by
    have h := Nat.sum_Icc_choose n i
    rw [← Finset.Ico_add_one_right_eq_Icc] at h
    exact_mod_cast h
  have hinner : (∑ k ∈ Finset.Ico i (n+1),(k.choose i:ℝ)/(n.choose i:ℝ)*a i)=
      (∑ k ∈ Finset.Ico i (n+1),(k.choose i:ℝ))*a i/(n.choose i:ℝ) := by
    rw [Finset.sum_mul,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [hinner,hs]
  have hc : ((i+1:ℕ):ℝ)*((n+1).choose (i+1):ℝ)=
      ((n+1:ℕ):ℝ)*(n.choose i:ℝ) := by
    calc
      _=((n+1).choose (i+1):ℝ)*((i+1:ℕ):ℝ) := mul_comm _ _
      _=_ := by exact_mod_cast (Nat.add_one_mul_choose_eq n i).symm
  have hh := congrArg (fun z : ℝ=>z*a i) hc
  field_simp
  <;> nlinarith only [hh]

theorem integral_peval_unit (a : ℕ→ℝ) (n : ℕ) :
    (∫ t in (0:ℝ)..1,peval a n t)=∑ i ∈ Finset.range (n+1),a i/((i+1:ℕ):ℝ) := by
  unfold peval
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [intervalIntegral.integral_const_mul,integral_pow]
    simp [div_eq_mul_inv]
  · intro i hi
    exact (continuous_const.mul (continuous_id.pow i)).intervalIntegrable _ _

theorem integral_peval_bern_mean (a : ℕ→ℝ) (n : ℕ) :
    (∫ t in (0:ℝ)..1,peval a n t)=
      (∑ k ∈ Finset.range (n+1),bern a n k)/((n+1:ℕ):ℝ) := by
  rw [integral_peval_unit,bern_mean]

#print axioms bern_mean
#print axioms integral_peval_bern_mean
theorem polynomial_cell_integral (p : ℚ[X]) (a b : ℚ) (n : ℕ) (hn : p.natDegree≤n) :
    (∫ x in (a:ℝ)..(b:ℝ),(p.map (Rat.castHom ℝ)).eval x)=
      ((b:ℝ)-a)*(∑ k ∈ Finset.range (n+1),(bernCoeff p a b n k:ℝ))/((n+1:ℕ):ℝ) := by
  let f := fun x : ℝ=>(p.map (Rat.castHom ℝ)).eval x
  have h := intervalIntegral.smul_integral_comp_add_mul (a:=(0:ℝ)) (b:=1) f ((b:ℝ)-a) (a:ℝ)
  have he0 : (a:ℝ)+((b:ℝ)-a)*0=(a:ℝ) := by ring
  have he1 : (a:ℝ)+((b:ℝ)-a)*1=(b:ℝ) := by ring
  rw [he0,he1,smul_eq_mul] at h
  rw [← h]
  have hp (x : ℝ) : f x=peval (fun j=>(p.coeff j:ℝ)) n x := by
    dsimp only [f]
    rw [Polynomial.eval_map,Polynomial.eval₂_eq_sum_range' (Rat.castHom ℝ) (by omega : p.natDegree<n+1)]
    rfl
  simp_rw [hp,← peval_affCoeffs]
  rw [integral_peval_bern_mean]
  simp only [cast_bernCoeff]
  ring

theorem sum_lget_map {α : Type} [Zero α] (xs : List α) (f : α→ℚ) :
    (∑ k ∈ Finset.range xs.length,f (BernsteinGrid.lget xs k))=(xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.length_cons,Finset.sum_range_succ',BernsteinGrid.lget,
      List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some,List.map_cons,List.sum_cons]
    change (∑ k ∈ Finset.range xs.length,f (BernsteinGrid.lget xs k))+f x=f x+(xs.map f).sum
    rw [ih,add_comm]

def upperMeanQ (bs : List (ℚ×ℚ)) : ℚ := (bs.map Prod.snd).sum/(bs.length:ℚ)

theorem cell_polynomial_integral_upper (p : ℚ[X]) (a b : ℚ) (n : ℕ)
    (hn : p.natDegree≤n) (hab : a≤b) (bs : List (ℚ×ℚ))
    (hb : BernsteinGrid.CellBoxRep p a b n bs) :
    (∫ x in (a:ℝ)..(b:ℝ),(p.map (Rat.castHom ℝ)).eval x)≤
      ((b:ℝ)-a)*(upperMeanQ bs:ℝ) := by
  have hmean : (∑ k ∈ Finset.range (n+1),bernCoeff p a b n k)/((n+1:ℕ):ℚ)≤upperMeanQ bs := by
    unfold upperMeanQ
    rw [← sum_lget_map bs Prod.snd,hb.1]
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply Finset.sum_le_sum
    intro k hk
    exact (hb.2 k (by have := Finset.mem_range.mp hk;omega)).2
  have hmeanR : (∑ k ∈ Finset.range (n+1),(bernCoeff p a b n k:ℝ))/((n+1:ℕ):ℝ)≤(upperMeanQ bs:ℝ) := by
    exact_mod_cast hmean
  rw [polynomial_cell_integral p a b n hn,mul_div_assoc]
  apply mul_le_mul_of_nonneg_left hmeanR
  exact_mod_cast sub_nonneg.mpr hab

#print axioms polynomial_cell_integral
#print axioms cell_polynomial_integral_upper

end CatalanCore.Li2.DecayCert.LatticeGate
