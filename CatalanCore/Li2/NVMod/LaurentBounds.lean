module
public import CatalanCore.Li2.NVMod.Expansion
@[expose] public section
set_option Elab.async false
open Polynomial Finset
open scoped BigOperators
namespace CatalanCore.Li2.NVMod
noncomputable section
theorem Oge.mono {f : HahnSeries ℤ ℚ} {a b : ℤ} (h : Oge f a) (hab : b≤a) : Oge f b :=
  fun e he=>h e (he.trans_le hab)
theorem Oge.zero (a : ℤ) : Oge (0 : HahnSeries ℤ ℚ) a := by intro e he; simp
theorem Oge.add {f g : HahnSeries ℤ ℚ} {a : ℤ} (hf : Oge f a) (hg : Oge g a) : Oge (f+g) a := by
  intro e he
  simp only [HahnSeries.coeff_add,hf e he,hg e he,add_zero]
theorem Oge.neg {f : HahnSeries ℤ ℚ} {a : ℤ} (hf : Oge f a) : Oge (-f) a := by
  intro e he
  simp only [HahnSeries.coeff_neg,hf e he,neg_zero]
theorem Oge.sub {f g : HahnSeries ℤ ℚ} {a : ℤ} (hf : Oge f a) (hg : Oge g a) : Oge (f-g) a := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg
theorem Oge.sum {ι : Type*} (S : Finset ι) (f : ι→HahnSeries ℤ ℚ) (a : ℤ)
    (h : ∀ i∈S,Oge (f i) a) : Oge (∑ i∈S,f i) a := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using Oge.zero a
  | @insert i S hi ih =>
    rw [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self _ _)).add (ih (fun j hj=>h j (Finset.mem_insert_of_mem hj)))
theorem Oge.single (a : ℤ) (q : ℚ) : Oge (HahnSeries.single a q) a := by
  intro e he
  exact HahnSeries.coeff_single_of_ne (ne_of_lt he)
theorem Oge.C (q : ℚ) : Oge (HahnSeries.C q) 0 := Oge.single 0 q
theorem Oge.mul {f g : HahnSeries ℤ ℚ} {a b : ℤ} (hf : Oge f a) (hg : Oge g b) : Oge (f*g) (a+b) := by
  classical
  intro e he
  rw [HahnSeries.coeff_mul]
  apply Finset.sum_eq_zero
  intro uv huv
  rcases Finset.mem_antidiagonal.mp huv with ⟨hu,hv,hs⟩
  change f.coeff uv.1≠0 at hu
  change g.coeff uv.2≠0 at hv
  have hau : a≤uv.1 := le_of_not_gt (fun h=>hu (hf _ h))
  have hbv : b≤uv.2 := le_of_not_gt (fun h=>hv (hg _ h))
  omega
theorem Oge.pow {f : HahnSeries ℤ ℚ} {a : ℤ} (hf : Oge f a) (n : ℕ) : Oge (f^n) (n*a) := by
  induction n with
  | zero =>
    simp only [pow_zero,Nat.cast_zero,zero_mul]
    simpa only [map_one] using Oge.C 1
  | succ n ih =>
    simpa only [pow_succ,Nat.cast_add,Nat.cast_one,add_mul,one_mul] using ih.mul hf
theorem Oge.order {f : HahnSeries ℤ ℚ} {a : ℤ} (hf : Oge f a) (hn : f≠0) : a≤f.order := by
  by_contra h
  have hc:=hf f.order (by omega)
  exact hn (HahnSeries.coeff_order_eq_zero.mp hc)
theorem Oge.of_order {f : HahnSeries ℤ ℚ} {a : ℤ} (ha : a≤f.order) : Oge f a :=
  fun e he=>HahnSeries.coeff_eq_zero_of_lt_order (he.trans_le ha)
theorem Oge.inv {f : HahnSeries ℤ ℚ} {a : ℤ} (hf : Oge f a) (hc : f.coeff a≠0) : Oge f⁻¹ (-a) := by
  have hn : f≠0 := by intro h;simpa [h] using hc
  have ho : f.order=a := le_antisymm (HahnSeries.order_le_of_coeff_ne_zero hc) (hf.order hn)
  have hi:=HahnSeries.order_mul hn (inv_ne_zero hn)
  rw [mul_inv_cancel₀ hn,HahnSeries.order_one,ho] at hi
  exact Oge.of_order (by omega)
#print axioms Oge.inv
#print axioms Oge.mul
theorem liNeg_map {F G : Type*} [Field F] [Field G] (f : F→+*G) (j : ℕ) (z : F) :
    f (liNeg j z)=liNeg j (f z) := by
  by_cases hj : j=0
  · simp only [liNeg,if_pos hj,map_div₀,map_sub,map_one]
  · simp only [liNeg,if_neg hj,map_sum,map_div₀,map_mul,map_natCast,map_pow,map_sub,map_one]
theorem liNeg_at_hX (j : ℕ) : Oge (liNeg j (hX : HahnSeries ℤ ℚ)) 1 := by
  have hx : Oge (hX : HahnSeries ℤ ℚ) 1 := Oge.single 1 1
  have h1 : Oge (1 : HahnSeries ℤ ℚ) 0 := by simpa only [map_one] using Oge.C 1
  have hd : Oge (1-hX : HahnSeries ℤ ℚ) 0 := h1.sub (hx.mono (by omega))
  have hc : (1-hX : HahnSeries ℤ ℚ).coeff 0≠0 := by
    norm_num [HahnSeries.coeff_sub,hX,HahnSeries.coeff_single]
  have hi : Oge (1-hX : HahnSeries ℤ ℚ)⁻¹ 0 := by simpa using hd.inv hc
  have hnat (n : ℕ) : Oge (n : HahnSeries ℤ ℚ) 0 := Oge.single 0 n
  by_cases hj : j=0
  · simp only [liNeg,if_pos hj,div_eq_mul_inv]
    simpa using hx.mul hi
  · simp only [liNeg,if_neg hj]
    apply Oge.sum
    intro i hib
    have hib1 := (Finset.mem_Icc.mp hib).1
    have hp : Oge ((hX : HahnSeries ℤ ℚ)^i) 1 :=
      (hx.pow i).mono (by norm_num;exact_mod_cast hib1)
    have hpi : Oge (((1-hX : HahnSeries ℤ ℚ)⁻¹)^(i+1)) 0 := by simpa using hi.pow (i+1)
    simpa only [zero_add,add_zero,div_eq_mul_inv,inv_pow] using
      (((hnat (Nat.stirlingSecond j i)).mul (hnat (Nat.factorial i))).mul hp).mul hpi
#print axioms liNeg_at_hX
end
end CatalanCore.Li2.NVMod
