module
public import CatalanCore.Li2.NVMod.LaurentBounds
public import CatalanCore.Li2.NVMod.RationalMoments
public import CatalanCore.Linalg.HahnDet
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
@[expose] public section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
open Polynomial Finset
open scoped BigOperators
namespace CatalanCore.Li2.NVMod
noncomputable section
private theorem coeff_mul_zero {f g : HahnSeries ℤ ℚ} (hf : Oge f 0) (hg : Oge g 0) :
    (f*g).coeff 0=f.coeff 0*g.coeff 0 := by
  classical
  rw [HahnSeries.coeff_mul]
  refine Finset.sum_eq_single (0,0) ?_ ?_
  · intro uv huv hne
    rcases Finset.mem_antidiagonal.mp huv with ⟨hu,hv,hs⟩
    change f.coeff uv.1≠0 at hu
    change g.coeff uv.2≠0 at hv
    have hu0 : 0≤uv.1 := le_of_not_gt (fun h=>hu (hf _ h))
    have hv0 : 0≤uv.2 := le_of_not_gt (fun h=>hv (hg _ h))
    exact False.elim (hne (Prod.ext (by omega) (by omega)))
  · intro hn
    by_cases hf0 : f.coeff 0=0
    · simp [hf0]
    by_cases hg0 : g.coeff 0=0
    · simp [hg0]
    exact False.elim (hn (Finset.mem_antidiagonal.mpr ⟨hf0,hg0,by simp⟩))
private theorem regular_pow {f : HahnSeries ℤ ℚ} (hf : Oge f 0) (hc : f.coeff 0=1) (n : ℕ) :
    Oge (f^n) 0 ∧ (f^n).coeff 0=1 := by
  induction n with
  | zero =>
    constructor
    · simpa using Oge.C 1
    · simp
  | succ n ih =>
    constructor
    · simpa only [pow_succ,zero_add] using ih.1.mul hf
    · rw [pow_succ,coeff_mul_zero ih.1 hf,ih.2,hc,mul_one]
private theorem regular_inv {f : HahnSeries ℤ ℚ} (hf : Oge f 0) (hc : f.coeff 0=1) :
    Oge f⁻¹ 0 ∧ (f⁻¹).coeff 0=1 := by
  have hc0 : f.coeff 0≠0 := by rw [hc];norm_num
  have hi : Oge f⁻¹ 0 := by simpa using hf.inv hc0
  have hn : f≠0 := by intro h;simp [h] at hc
  refine ⟨hi,?_⟩
  have hh:=coeff_mul_zero hf hi
  rw [mul_inv_cancel₀ hn,hc,one_mul] at hh
  simpa using hh.symm
private theorem regular_zpow {f : HahnSeries ℤ ℚ} (hf : Oge f 0) (hc : f.coeff 0=1) (e : ℤ) :
    Oge (f^e) 0 ∧ (f^e).coeff 0=1 := by
  cases e with
  | ofNat n => simpa only [Int.ofNat_eq_natCast,zpow_natCast] using regular_pow hf hc n
  | negSucc n =>
    simpa only [zpow_negSucc] using regular_inv (regular_pow hf hc (n+1)).1 (regular_pow hf hc (n+1)).2
private theorem one_hom_X : affineRFHahnQ 1 (-1) (by norm_num) (rfX : RatFunc ℚ)=1-hX := by
  simp only [rfX,rfPoly,affineRFHahnQ,RatFunc.liftRingHom_algebraMap,
    affinePolyHahnQ,RingHom.comp_apply,Polynomial.coe_compRingHom_apply,Polynomial.X_comp,
    map_add,map_mul,polyHahnQ_C,polyHahnQ_X,map_one,map_neg,neg_one_mul]
  ring
private theorem one_hom_C (q : ℚ) :
    affineRFHahnQ 1 (-1) (by norm_num) (rfPoly (C q))=HahnSeries.C q := by
  simp only [rfPoly,affineRFHahnQ,RatFunc.liftRingHom_algebraMap,
    affinePolyHahnQ,RingHom.comp_apply,Polynomial.coe_compRingHom_apply,Polynomial.C_comp,polyHahnQ_C]
private theorem one_omega_expansion (m : ℕ) :
    atOne (omegaRF m)=∑ b∈Icc 1 m,
      (1-hX : HahnSeries ℤ ℚ)^((b:ℤ)-m)*HahnSeries.C (((b:ℚ)^2)⁻¹) := by
  rw [atOne_eq_hom]
  simp only [omegaRF,map_sum,map_mul,map_inv₀,map_div₀,map_zpow₀,one_hom_X,one_hom_C,div_eq_mul_inv,
    HahnSeries.C_apply,HahnSeries.inv_single,neg_zero]
private theorem coeff_sum_one {ι : Type*} (S : Finset ι) (f : ι→HahnSeries ℤ ℚ) :
    (∑ i∈S,f i).coeff 0=∑ i∈S,(f i).coeff 0 := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih => simp only [Finset.sum_insert hi,HahnSeries.coeff_add,ih]
theorem omega_at_one (m : ℕ) : Oge (atOne (omegaRF m)) 0 ∧
    (atOne (omegaRF m)).coeff 0=∑ b∈Icc 1 m,(1:ℚ)/(b:ℚ)^2 := by
  have hf : Oge (1-hX : HahnSeries ℤ ℚ) 0 :=
    (show Oge (1 : HahnSeries ℤ ℚ) 0 by simpa using Oge.C 1).sub
      ((Oge.single 1 (1:ℚ)).mono (by omega))
  have hc : (1-hX : HahnSeries ℤ ℚ).coeff 0=1 := by
    norm_num [HahnSeries.coeff_sub,hX,HahnSeries.coeff_single]
  rw [one_omega_expansion]
  constructor
  · apply Oge.sum
    intro b hb
    simpa only [zero_add] using ((regular_zpow hf hc ((b:ℤ)-m)).1.mul (Oge.C _))
  · rw [coeff_sum_one]
    apply Finset.sum_congr rfl
    intro b hb
    rw [coeff_mul_zero (regular_zpow hf hc ((b:ℤ)-m)).1 (Oge.C _),
      (regular_zpow hf hc ((b:ℤ)-m)).2]
    simp only [HahnSeries.C_apply,HahnSeries.coeff_single_same,one_mul,one_div]

private theorem coeff_sum_hahn {ι : Type*} (S : Finset ι)
    (f : ι→HahnSeries ℤ ℚ) (e : ℤ) :
    (∑ i∈S,f i).coeff e=∑ i∈S,(f i).coeff e := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih => simp only [Finset.sum_insert hi,HahnSeries.coeff_add,ih]

private theorem hX_inv_pow (n : ℕ) :
    ((hX : HahnSeries ℤ ℚ)^n)⁻¹=HahnSeries.single (-(n:ℤ)) 1 := by
  simp only [hX,HahnSeries.single_pow,HahnSeries.inv_single,nsmul_eq_mul,
    mul_one,one_pow,inv_one]
private theorem one_minus_hX_regular :
    Oge (1-hX : HahnSeries ℤ ℚ) 0 ∧ (1-hX : HahnSeries ℤ ℚ).coeff 0=1 := by
  constructor
  · exact (show Oge (1 : HahnSeries ℤ ℚ) 0 by simpa using Oge.C 1).sub
      ((Oge.single 1 (1:ℚ)).mono (by omega))
  · norm_num [HahnSeries.coeff_sub,hX,HahnSeries.coeff_single]
private theorem polylog_term (j i : ℕ) :
    Oge ((Nat.stirlingSecond j i : HahnSeries ℤ ℚ)*(Nat.factorial i : HahnSeries ℤ ℚ)*
      (1-hX)^i/(hX : HahnSeries ℤ ℚ)^(i+1)) (-((i:ℤ)+1)) ∧
    (((Nat.stirlingSecond j i : HahnSeries ℤ ℚ)*(Nat.factorial i : HahnSeries ℤ ℚ)*
      (1-hX)^i/(hX : HahnSeries ℤ ℚ)^(i+1)).coeff (-((i:ℤ)+1)))=
        (Nat.stirlingSecond j i:ℚ)*(Nat.factorial i:ℚ) := by
  have hu:=regular_pow one_minus_hX_regular.1 one_minus_hX_regular.2 i
  have hc : Oge ((Nat.stirlingSecond j i : HahnSeries ℤ ℚ)*(Nat.factorial i : HahnSeries ℤ ℚ)) 0 := by
    simpa only [map_mul,map_natCast] using Oge.C ((Nat.stirlingSecond j i:ℚ)*(Nat.factorial i:ℚ))
  have hcu : Oge ((Nat.stirlingSecond j i : HahnSeries ℤ ℚ)*(Nat.factorial i : HahnSeries ℤ ℚ)*(1-hX)^i) 0 := by
    simpa only [zero_add] using hc.mul hu.1
  rw [div_eq_mul_inv,hX_inv_pow]
  constructor
  · simpa only [Nat.cast_add,Nat.cast_one,zero_add] using hcu.mul (Oge.single (-((i+1:ℕ):ℤ)) 1)
  · rw [HahnSeries.coeff_mul_single]
    simp only [Nat.cast_add,Nat.cast_one,sub_self,mul_one]
    rw [coeff_mul_zero hc hu.1,hu.2,mul_one]
    have he : (Nat.stirlingSecond j i : HahnSeries ℤ ℚ)*(Nat.factorial i : HahnSeries ℤ ℚ)=
        HahnSeries.C ((Nat.stirlingSecond j i:ℚ)*(Nat.factorial i:ℚ)) := by
      simp only [map_mul,map_natCast]
    rw [he,HahnSeries.C_apply,HahnSeries.coeff_single_same]
theorem liNeg_at_one (j : ℕ) :
    Oge (liNeg j (1-hX : HahnSeries ℤ ℚ)) (-((j:ℤ)+1)) ∧
      (liNeg j (1-hX : HahnSeries ℤ ℚ)).coeff (-((j:ℤ)+1))=(Nat.factorial j:ℚ) := by
  by_cases hj : j=0
  · subst j
    rw [liNeg,if_pos rfl]
    simp only [sub_sub_cancel,div_eq_mul_inv]
    rw [show (hX : HahnSeries ℤ ℚ)⁻¹=HahnSeries.single (-1) 1 by simpa using hX_inv_pow 1]
    constructor
    · simpa only [Nat.cast_zero,zero_add] using one_minus_hX_regular.1.mul (Oge.single (-1) 1)
    · rw [HahnSeries.coeff_mul_single]
      simpa using one_minus_hX_regular.2
  · simp only [liNeg,if_neg hj,sub_sub_cancel]
    constructor
    · apply Oge.sum
      intro i hi
      exact (polylog_term j i).1.mono (by have hh:=(Finset.mem_Icc.mp hi).2;omega)
    · rw [coeff_sum_hahn]
      rw [Finset.sum_eq_single j]
      · rw [(polylog_term j j).2,Nat.stirlingSecond_self,Nat.cast_one,one_mul]
      · intro i hi hij
        exact (polylog_term j i).1 _ (by have hh:=(Finset.mem_Icc.mp hi).2;omega)
      · intro hnot
        exact False.elim (hnot (Finset.mem_Icc.mpr ⟨by omega,le_refl _⟩))

private theorem one_hom_rat (q : ℚ) :
    affineRFHahnQ 1 (-1) (by norm_num) (algebraMap ℚ (RatFunc ℚ) q)=HahnSeries.C q := by
  rw [eq_ratCast,map_ratCast]
  rfl
private theorem one_moment_expansion (A : TypeKey) (g : ℚ[X]) :
    atOne (momentRF A g)=
      (∑ m∈poleSet A,HahnSeries.C (residue A m*g.eval (-(m:ℚ)))*atOne (omegaRF m))+
        ∑ k∈Icc 1 (polyPart A g).natDegree,
          (k:HahnSeries ℤ ℚ)*HahnSeries.C ((polyPart A g).coeff k)*liNeg (k-1) (1-hX) := by
  simp only [atOne_eq_hom]
  rw [momentRF_partial_fractions,map_add]
  simp only [map_sum,map_mul,one_hom_rat,map_natCast,liNeg_map,one_hom_X]
private theorem one_pole_regular (A : TypeKey) (g : ℚ[X]) :
    Oge (∑ m∈poleSet A,HahnSeries.C (residue A m*g.eval (-(m:ℚ)))*atOne (omegaRF m)) 0 ∧
    (∑ m∈poleSet A,HahnSeries.C (residue A m*g.eval (-(m:ℚ)))*atOne (omegaRF m)).coeff 0=
      ∑ m∈poleSet A,residue A m*g.eval (-(m:ℚ))*∑ b∈Icc 1 m,(1:ℚ)/(b:ℚ)^2 := by
  constructor
  · apply Oge.sum
    intro m hm
    simpa only [zero_add] using (Oge.C _).mul (omega_at_one m).1
  · rw [coeff_sum_hahn]
    apply Finset.sum_congr rfl
    intro m hm
    rw [HahnSeries.C_apply,HahnSeries.coeff_single_zero_mul,(omega_at_one m).2]
private theorem one_poly_term (k : ℕ) (hk : 1≤k) (q : ℚ) :
    Oge ((k:HahnSeries ℤ ℚ)*HahnSeries.C q*liNeg (k-1) (1-hX)) (-(k:ℤ)) ∧
      ((k:HahnSeries ℤ ℚ)*HahnSeries.C q*liNeg (k-1) (1-hX)).coeff (-(k:ℤ))=
        (Nat.factorial k:ℚ)*q := by
  have ht:=liNeg_at_one (k-1)
  have hi : ((k-1:ℕ):ℤ)+1=(k:ℤ) := by omega
  rw [hi] at ht
  have he : (k:HahnSeries ℤ ℚ)*HahnSeries.C q=HahnSeries.C ((k:ℚ)*q) := by
    simp only [map_mul,map_natCast]
  rw [he]
  constructor
  · simpa only [zero_add] using (Oge.C _).mul ht.1
  · rw [HahnSeries.C_apply,HahnSeries.coeff_single_zero_mul,ht.2]
    have hf : Nat.factorial k=k*Nat.factorial (k-1) := by
      simpa only [Nat.sub_add_cancel hk] using Nat.factorial_succ (k-1)
    rw [hf,Nat.cast_mul]
    ring
theorem moment_at_one (A : TypeKey) (g : ℚ[X]) :
  let deg := (polyPart A g).degree
  (deg≤0 → Oge (atOne (momentRF A g)) 0 ∧
    (atOne (momentRF A g)).coeff 0=
      ∑ m∈poleSet A,residue A m*g.eval (-(m:ℚ))*
        ∑ b∈Icc 1 m,(1:ℚ)/(b:ℚ)^2) ∧
  (∀ k : ℕ,1≤k → deg=k →
    Oge (atOne (momentRF A g)) (-(k:ℤ)) ∧
      (atOne (momentRF A g)).coeff (-(k:ℤ))=
        (Nat.factorial k:ℚ)*(polyPart A g).leadingCoeff) := by
  dsimp only
  constructor
  · intro hd
    have hn : (polyPart A g).natDegree=0 := natDegree_eq_zero_iff_degree_le_zero.mpr hd
    rw [one_moment_expansion,hn]
    simpa using one_pole_regular A g
  · intro k hk hd
    have hn : (polyPart A g).natDegree=k := natDegree_eq_of_degree_eq_some hd
    rw [one_moment_expansion,hn]
    have hp : Oge (∑ m∈poleSet A,HahnSeries.C (residue A m*g.eval (-(m:ℚ)))*atOne (omegaRF m)) 0 :=
      (one_pole_regular A g).1
    have hq : Oge (∑ i∈Icc 1 k,(i:HahnSeries ℤ ℚ)*HahnSeries.C ((polyPart A g).coeff i)*
        liNeg (i-1) (1-hX)) (-(k:ℤ)) := by
      apply Oge.sum
      intro i hi
      exact (one_poly_term i (Finset.mem_Icc.mp hi).1 _).1.mono
        (by have hh:=(Finset.mem_Icc.mp hi).2;omega)
    constructor
    · exact (hp.mono (by omega)).add hq
    · rw [HahnSeries.coeff_add,hp _ (by omega),zero_add,coeff_sum_hahn]
      rw [Finset.sum_eq_single k]
      · rw [(one_poly_term k hk _).2,←hn,Polynomial.coeff_natDegree]
      · intro i hi hne
        exact (one_poly_term i (Finset.mem_Icc.mp hi).1 _).1 _
          (by have hh:=(Finset.mem_Icc.mp hi).2;omega)
      · intro hnot
        exact False.elim (hnot (Finset.mem_Icc.mpr ⟨hk,le_refl _⟩))

def h0 (A : TypeKey) : ℤ :=
  ((weightDen A).natDegree:ℤ)-(weightNum A).natDegree
private theorem weightNum_monic (A : TypeKey) : (weightNum A).Monic := by
  cases hk : A.kind
  · simp only [weightNum,hk]
    apply Polynomial.monic_prod_of_monic
    intro j hj
    exact (Polynomial.monic_X_add_C _).pow 2
  · simp only [weightNum,hk]
    apply Polynomial.Monic.mul Polynomial.monic_X
    apply Polynomial.monic_prod_of_monic
    intro j hj
    exact (Polynomial.monic_X_add_C _).pow 2
private theorem weightDen_monic (A : TypeKey) : (weightDen A).Monic := by
  apply Polynomial.monic_prod_of_monic
  intro j hj
  exact Polynomial.monic_X_add_C _
private theorem polyPart_monomial_degree (A : TypeKey) (e : ℕ) :
    (polyPart A (X^e)).natDegree=(weightNum A).natDegree+e-(weightDen A).natDegree := by
  rw [polyPart,Polynomial.natDegree_divByMonic _ (weightDen_monic A),
    Polynomial.natDegree_mul (weightNum_monic A).ne_zero (pow_ne_zero e Polynomial.X_ne_zero),
    Polynomial.natDegree_X_pow]
theorem polyPart_monomial_regular (A : TypeKey) (e : ℕ) (he : (e:ℤ)≤h0 A) :
    (polyPart A (X^e)).degree≤0 := by
  apply Polynomial.natDegree_eq_zero_iff_degree_le_zero.mp
  rw [polyPart_monomial_degree]
  unfold h0 at he
  omega
theorem polyPart_monomial_pole (A : TypeKey) (e : ℕ) (he : h0 A<(e:ℤ)) :
    (polyPart A (X^e)).degree=((e:ℤ)-h0 A).toNat ∧
      (polyPart A (X^e)).leadingCoeff=1 := by
  have hn := polyPart_monomial_degree A e
  have hd : (weightDen A).natDegree < (weightNum A).natDegree+e := by unfold h0 at he;omega
  have hpos : 0<(polyPart A (X^e)).natDegree := by omega
  have hne : polyPart A (X^e)≠0 := by intro h;rw [h,Polynomial.natDegree_zero] at hpos;omega
  have heq : (weightNum A).natDegree+e-(weightDen A).natDegree=((e:ℤ)-h0 A).toNat := by
    unfold h0
    omega
  constructor
  · rw [Polynomial.degree_eq_natDegree hne,hn,heq]
  · have hprod := (weightNum_monic A).mul (Polynomial.monic_X.pow e)
    have hdeg : (weightDen A).degree≤(weightNum A*X^e).degree := by
      rw [Polynomial.degree_eq_natDegree (weightDen_monic A).ne_zero,
        Polynomial.degree_eq_natDegree hprod.ne_zero,
        Polynomial.natDegree_mul (weightNum_monic A).ne_zero (pow_ne_zero e Polynomial.X_ne_zero),
        Polynomial.natDegree_X_pow]
      exact_mod_cast Nat.le_of_lt hd
    rw [polyPart,Polynomial.leadingCoeff_divByMonic_of_monic (weightDen_monic A) hdeg]
    exact hprod

def oneH1 (A : TypeKey) : ℕ := ((h0 A+1)/2).toNat
def oneH2 (A : TypeKey) : ℕ := (h0 A/2).toNat
def oneR (A : TypeKey) (i : Fin A.size) : ℤ :=
  if 0≤h0 A then -max 0 ((i:ℤ)-oneH1 A) else -(i:ℤ)
def oneC (A : TypeKey) (j : Fin A.size) : ℤ :=
  if 0≤h0 A then -max 0 ((j:ℤ)-oneH2 A) else h0 A-(j:ℤ)
def regularMoment (A : TypeKey) (e : ℕ) : ℚ :=
  ∑ m∈poleSet A,residue A m*(-(m:ℚ))^e*
    ∑ j∈Icc 1 m,(1:ℚ)/(j:ℚ)^2
def regularHankel (A : TypeKey) (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  fun i j=>regularMoment A (i.val+j.val)
def oneMatrix (A : TypeKey) : Matrix (Fin A.size) (Fin A.size) ℚ :=
  fun i j=>if (i:ℤ)+j≤h0 A then
    if oneR A i+oneC A j=0 then regularMoment A (i.val+j.val) else 0
  else if oneR A i+oneC A j = -((i:ℤ)+j-h0 A) then
    (Nat.factorial (((i:ℤ)+j-h0 A).toNat):ℚ) else 0
def cornerHankel (A : TypeKey) : Matrix (Fin (oneH1 A+1)) (Fin (oneH1 A+1)) ℚ :=
  fun i j=>regularMoment A (i.val+j.val)-
    if i.val=oneH1 A ∧ j.val=oneH1 A then
      ((A.size-oneH1 A-1:ℕ):ℚ)/((A.size-oneH1 A-1:ℕ)+1) else 0
def factorialHankel (n γ : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  fun i j=>(Nat.factorial (i.val+j.val+γ):ℚ)
def FactorialDetChecked (A : TypeKey) : Prop :=
  ∀ n≤A.size,∀ γ∈({0,1,2,(h0 A).natAbs}:Finset ℕ),
    (factorialHankel n γ).det=∏ k : Fin n,(Nat.factorial k.val:ℚ)*(Nat.factorial (k.val+γ):ℚ)
theorem one_potentials_bound (A : TypeKey) (i j : Fin A.size) :
    oneR A i+oneC A j≤-max 0 ((i:ℤ)+j-h0 A) := by
  unfold oneR oneC
  split_ifs with hh
  · have he : (oneH1 A:ℤ)+(oneH2 A:ℤ)=h0 A := by
      unfold oneH1 oneH2
      omega
    omega
  · have hi : 0≤(i:ℤ) := Int.natCast_nonneg _
    have hj : 0≤(j:ℤ) := Int.natCast_nonneg _
    omega

private theorem one_monomial_initial (A : TypeKey) (e : ℕ) :
    Oge (atOne (momentRF A (X^e))) (-max 0 ((e:ℤ)-h0 A)) ∧
      (atOne (momentRF A (X^e))).coeff (-max 0 ((e:ℤ)-h0 A))=
        if (e:ℤ)≤h0 A then regularMoment A e
        else (Nat.factorial (((e:ℤ)-h0 A).toNat):ℚ) := by
  by_cases he : (e:ℤ)≤h0 A
  · have hh := (moment_at_one A (X^e)).1 (polyPart_monomial_regular A e he)
    simpa only [max_eq_left (by omega : (e:ℤ)-h0 A≤0),neg_zero,if_pos he,
      regularMoment,Polynomial.eval_pow,Polynomial.eval_X] using hh
  · have hpoly:=polyPart_monomial_pole A e (by omega)
    have hk : 1≤((e:ℤ)-h0 A).toNat := by omega
    have hh := (moment_at_one A (X^e)).2 _ hk hpoly.1
    rw [hpoly.2,mul_one] at hh
    have heq : (((e:ℤ)-h0 A).toNat:ℤ)=(e:ℤ)-h0 A := by omega
    simpa only [heq,max_eq_right (by omega : 0≤(e:ℤ)-h0 A),if_neg he] using hh
private theorem one_entry_initial (A : TypeKey) (i j : Fin A.size) :
    Oge (atOne (momentRF A (X^(i.val+j.val)))) (oneR A i+oneC A j) ∧
      (atOne (momentRF A (X^(i.val+j.val)))).coeff (oneR A i+oneC A j)=oneMatrix A i j := by
  have hh := one_monomial_initial A (i.val+j.val)
  have hpot:=one_potentials_bound A i j
  simp only [Nat.cast_add] at hh
  constructor
  · exact hh.1.mono hpot
  · by_cases he : (i:ℤ)+j≤h0 A
    · rw [max_eq_left (by omega : (i:ℤ)+j-h0 A≤0),neg_zero,if_pos he] at hh
      unfold oneMatrix
      rw [if_pos he]
      by_cases hp : oneR A i+oneC A j=0
      · rw [if_pos hp,hp,hh.2]
      · rw [if_neg hp]
        exact hh.1 _ (by omega)
    · rw [max_eq_right (by omega : 0≤(i:ℤ)+j-h0 A),if_neg he] at hh
      unfold oneMatrix
      rw [if_neg he]
      by_cases hp : oneR A i+oneC A j = -((i:ℤ)+j-h0 A)
      · rw [if_pos hp,hp,hh.2]
      · rw [if_neg hp]
        exact hh.1 _ (by omega)
theorem hankel_at_one (A : TypeKey) :
  let e := (Finset.sum Finset.univ (oneR A))+(Finset.sum Finset.univ (oneC A))
  Oge (atOne (constantRF A)) e ∧
    (atOne (constantRF A)).coeff e=(oneMatrix A).det := by
  let M : Matrix (Fin A.size) (Fin A.size) (HahnSeries ℤ ℚ) :=
    fun i j=>atOne (momentRF A (X^(i.val+j.val)))
  have hM : M.det=atOne (constantRF A) := by
    rw [atOne_eq_hom,constantRF,RingHom.map_det]
    congr 1
    apply Matrix.ext
    intro i j
    exact atOne_eq_hom _
  have hh:=CatalanCore.Linalg.det_potential_coeff M (oneR A) (oneC A)
    (fun i j e he=>(one_entry_initial A i j).1 e he)
  rw [hM] at hh
  constructor
  · exact hh.1
  · rw [hh.2]
    congr 1
    funext i j
    exact (one_entry_initial A i j).2

theorem one_matrix_det_negative (A : TypeKey) (hf : FactorialDetChecked A) (hh : h0 A<0) :
    (oneMatrix A).det=∏ k : Fin A.size,(Nat.factorial k.val:ℚ)*
      (Nat.factorial (k.val+(h0 A).natAbs):ℚ) := by
  have he : oneMatrix A=factorialHankel A.size (h0 A).natAbs := by
    ext i j
    have hi : 0≤(i:ℤ) := Int.natCast_nonneg _
    have hj : 0≤(j:ℤ) := Int.natCast_nonneg _
    have hle : ¬((i:ℤ)+j≤h0 A) := by omega
    simp only [oneMatrix,hle,if_false,oneR,oneC,show ¬0≤h0 A by omega]
    rw [if_pos (by omega)]
    change (Nat.factorial (((i:ℤ)+j-h0 A).toNat):ℚ)=
      (Nat.factorial (i.val+j.val+(h0 A).natAbs):ℚ)
    congr 2
    omega
  rw [he]
  exact hf A.size (le_refl _) (h0 A).natAbs (by simp)
theorem one_matrix_det_regular (A : TypeKey) (hh : 0≤h0 A) (hs : A.size≤oneH2 A+1) :
    (oneMatrix A).det=(regularHankel A A.size).det := by
  congr 1
  ext i j
  have hH : oneH2 A≤oneH1 A := by unfold oneH1 oneH2;omega
  have he : (i:ℤ)+j≤h0 A := by
    have hi:=i.isLt
    have hj:=j.isLt
    unfold oneH2 at hs
    omega
  have hr : oneR A i=0 := by
    unfold oneR
    rw [if_pos hh,max_eq_left (by have hi:=i.isLt;omega),neg_zero]
  have hc : oneC A j=0 := by
    unfold oneC
    rw [if_pos hh,max_eq_left (by have hj:=j.isLt;omega),neg_zero]
  simp only [oneMatrix,he,if_true,hr,hc,zero_add,regularHankel,ite_true]

theorem one_matrix_det_odd (A : TypeKey) (hf : FactorialDetChecked A)
    (hh : 0≤h0 A) (ho : Odd (h0 A)) (hs : oneH1 A≤A.size) :
    (oneMatrix A).det=(regularHankel A (oneH1 A)).det*
      ∏ k : Fin (A.size-oneH1 A),(Nat.factorial k.val:ℚ)*(Nat.factorial (k.val+1):ℚ) := by
  classical
  have hodd : h0 A=2*(oneH1 A:ℤ)-1 ∧ oneH1 A=oneH2 A+1 := by
    obtain ⟨b,hb⟩:=ho
    unfold oneH1 oneH2
    omega
  let d := oneH1 A
  let n := A.size-d
  have hn : d+n=A.size := by dsimp [d,n];omega
  let e : Fin d⊕Fin n ≃ Fin A.size := finSumFinEquiv.trans (finCongr hn)
  have einl (i : Fin d) : (e (Sum.inl i)).val=i.val := rfl
  have einr (j : Fin n) : (e (Sum.inr j)).val=d+j.val := rfl
  let C : Matrix (Fin n) (Fin d) ℚ := fun i j=>oneMatrix A (e (Sum.inr i)) (e (Sum.inl j))
  have hblock : Matrix.fromBlocks (regularHankel A d) 0 C (factorialHankel n 1)=
      (oneMatrix A).submatrix e e := by
    ext i j
    rcases i with i|i <;> rcases j with j|j
    · have hi : ((e (Sum.inl i)):ℤ)≤oneH1 A := by change ((e (Sum.inl i)).val:ℤ)≤_;rw [einl];have hi:=i.isLt;dsimp [d] at hi;omega
      have hj : ((e (Sum.inl j)):ℤ)≤oneH2 A := by change ((e (Sum.inl j)).val:ℤ)≤_;rw [einl];have hj:=j.isLt;dsimp [d] at hj;omega
      have he : ((e (Sum.inl i)):ℤ)+e (Sum.inl j)≤h0 A := by omega
      have hr : oneR A (e (Sum.inl i))=0 := by unfold oneR;rw [if_pos hh];omega
      have hc : oneC A (e (Sum.inl j))=0 := by unfold oneC;rw [if_pos hh];omega
      change regularMoment A (i.val+j.val)=oneMatrix A (e (Sum.inl i)) (e (Sum.inl j))
      rw [oneMatrix,if_pos he,hr,hc,zero_add,if_pos rfl]
      simp only [einl]
    · change 0=oneMatrix A (e (Sum.inl i)) (e (Sum.inr j))
      have hi:=i.isLt
      have hj:=j.isLt
      have hiv : ((e (Sum.inl i)):ℤ)=(i.val:ℤ) := congrArg (fun x:ℕ=>(x:ℤ)) (einl i)
      have hjv : ((e (Sum.inr j)):ℤ)=(d:ℤ)+j.val := by exact_mod_cast einr j
      unfold oneMatrix oneR oneC
      simp only [if_pos hh]
      split_ifs with he hp <;> try rfl
      all_goals exfalso;dsimp [d] at hi hjv;omega
    · rfl
    · change factorialHankel n 1 i j=oneMatrix A (e (Sum.inr i)) (e (Sum.inr j))
      have hiv : ((e (Sum.inr i)):ℤ)=(d:ℤ)+i.val := by exact_mod_cast einr i
      have hjv : ((e (Sum.inr j)):ℤ)=(d:ℤ)+j.val := by exact_mod_cast einr j
      have he : ¬((e (Sum.inr i)):ℤ)+e (Sum.inr j)≤h0 A := by dsimp [d] at hiv hjv;omega
      have hp : oneR A (e (Sum.inr i))+oneC A (e (Sum.inr j))=
          -(((e (Sum.inr i)):ℤ)+e (Sum.inr j)-h0 A) := by
        unfold oneR oneC
        simp only [if_pos hh]
        dsimp [d] at hiv hjv
        omega
      simp only [oneMatrix,if_neg he,if_pos hp,factorialHankel]
      congr 2
      dsimp [d] at hiv hjv
      omega
  have hd:=congrArg Matrix.det hblock
  rw [Matrix.det_submatrix_equiv_self,Matrix.det_fromBlocks_zero₁₂] at hd
  rw [←hd]
  congr 1
  exact hf n (by dsimp [n];omega) 1 (by simp)

private def facProduct (n γ : ℕ) : ℚ :=
  ∏ k : Fin n,(Nat.factorial k.val:ℚ)*(Nat.factorial (k.val+γ):ℚ)
private theorem facProduct_succ (n γ : ℕ) :
    facProduct (n+1) γ=facProduct n γ*(Nat.factorial n:ℚ)*(Nat.factorial (n+γ):ℚ) := by
  unfold facProduct
  rw [Fin.prod_univ_castSucc]
  simp only [Fin.val_castSucc,Fin.val_last]
  ring
private theorem factorial_corner_ratio (n : ℕ) :
    ((n:ℚ)+1)*facProduct (n+1) 0=facProduct n 2 := by
  induction n with
  | zero => norm_num [facProduct]
  | succ n ih =>
    rw [facProduct_succ (n+1) 0,facProduct_succ n 2,←ih]
    simp only [Nat.add_zero,Nat.cast_add,Nat.cast_one,Nat.factorial_succ,Nat.cast_mul]
    ring
private theorem factorial_product_ne_zero (n γ : ℕ) : facProduct n γ≠0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  apply mul_ne_zero
  · exact_mod_cast Nat.factorial_ne_zero i.val
  · exact_mod_cast Nat.factorial_ne_zero (i.val+γ)

private theorem factorial_schur_scalar (n : ℕ)
    (h0det : (factorialHankel (n+1) 0).det=facProduct (n+1) 0)
    (h2det : (factorialHankel n 2).det=facProduct n 2) :
    let B : Matrix (Fin 1) (Fin n) ℚ := fun _ j=>(Nat.factorial (j.val+1):ℚ)
    let C : Matrix (Fin n) (Fin 1) ℚ := fun i _=>(Nat.factorial (i.val+1):ℚ)
    (B*(factorialHankel n 2)⁻¹*C) 0 0=(n:ℚ)/((n:ℚ)+1) := by
  classical
  let A : Matrix (Fin 1) (Fin 1) ℚ := fun _ _=>1
  let B : Matrix (Fin 1) (Fin n) ℚ := fun _ j=>(Nat.factorial (j.val+1):ℚ)
  let C : Matrix (Fin n) (Fin 1) ℚ := fun i _=>(Nat.factorial (i.val+1):ℚ)
  let D := factorialHankel n 2
  let e : Fin 1⊕Fin n ≃ Fin (n+1) := finSumFinEquiv.trans (finCongr (by omega : 1+n=n+1))
  have einl (i : Fin 1) : (e (Sum.inl i)).val=i.val := rfl
  have einr (j : Fin n) : (e (Sum.inr j)).val=1+j.val := rfl
  have he : Matrix.fromBlocks A B C D=(factorialHankel (n+1) 0).submatrix e e := by
    ext i j
    rcases i with i|i <;> rcases j with j|j
    · have hi : i=0 := Subsingleton.elim _ _
      have hj : j=0 := Subsingleton.elim _ _
      subst i;subst j
      rfl
    · have hi : i=0 := Subsingleton.elim _ _
      subst i
      change (Nat.factorial (j.val+1):ℚ)=
        (Nat.factorial ((e (Sum.inl 0)).val+(e (Sum.inr j)).val+0):ℚ)
      simp only [einl,einr,Fin.val_zero,Nat.zero_add,Nat.add_zero,Nat.add_comm]
    · have hj : j=0 := Subsingleton.elim _ _
      subst j
      change (Nat.factorial (i.val+1):ℚ)=
        (Nat.factorial ((e (Sum.inr i)).val+(e (Sum.inl 0)).val+0):ℚ)
      simp only [einl,einr,Fin.val_zero,Nat.zero_add,Nat.add_zero,Nat.add_comm]
    · simp only [Matrix.fromBlocks_apply₂₂,Matrix.submatrix_apply,D,factorialHankel,einr,Nat.add_zero]
      congr 2
      omega
  have hDn : D.det≠0 := by rw [show D.det=(factorialHankel n 2).det from rfl,h2det];exact factorial_product_ne_zero n 2
  letI : Invertible D := Matrix.invertibleOfIsUnitDet D (isUnit_iff_ne_zero.mpr hDn)
  have hd:=Matrix.det_fromBlocks₂₂ A B C D
  rw [he,Matrix.det_submatrix_equiv_self,Matrix.invOf_eq_nonsing_inv,Matrix.det_fin_one] at hd
  change (factorialHankel (n+1) 0).det=D.det*(1-(B*D⁻¹*C) 0 0) at hd
  rw [h0det,show D.det=(factorialHankel n 2).det from rfl,h2det] at hd
  have hD := factorial_product_ne_zero n 2
  have hN : (n:ℚ)+1≠0 := by exact_mod_cast Nat.succ_ne_zero n
  have hr : facProduct (n+1) 0/facProduct n 2=1/((n:ℚ)+1) := by
    apply (div_eq_div_iff hD hN).mpr
    simpa only [one_mul,mul_comm] using factorial_corner_ratio n
  have hv : 1-(B*D⁻¹*C) 0 0=1/((n:ℚ)+1) := by
    rw [hd,mul_div_cancel_left₀ _ hD] at hr
    exact hr
  change (B*D⁻¹*C) 0 0=_
  calc
    _=1-(1-(B*D⁻¹*C) 0 0) := by ring
    _=1-1/((n:ℚ)+1) := by rw [hv]
    _=(n:ℚ)/((n:ℚ)+1) := by field_simp;ring

private theorem boundary_schur {F : Type*} [Field F] (d n : ℕ)
    (A : Matrix (Fin (d+1)) (Fin (d+1)) F) (D : Matrix (Fin n) (Fin n) F)
    (b c : Fin n→F) (hD : D.det≠0) :
    let B : Matrix (Fin (d+1)) (Fin n) F := fun i j=>if i.val=d then b j else 0
    let C : Matrix (Fin n) (Fin (d+1)) F := fun i j=>if j.val=d then c i else 0
    let v := ((Matrix.of fun (_ : Fin 1) j=>b j)*D⁻¹*(Matrix.of fun i (_ : Fin 1)=>c i)) 0 0
    (Matrix.fromBlocks A B C D).det=D.det*
      (Matrix.of fun i j=>A i j-if i.val=d ∧ j.val=d then v else 0).det := by
  classical
  dsimp only
  let B : Matrix (Fin (d+1)) (Fin n) F := fun i j=>if i.val=d then b j else 0
  let C : Matrix (Fin n) (Fin (d+1)) F := fun i j=>if j.val=d then c i else 0
  let v := ((Matrix.of fun (_ : Fin 1) j=>b j)*D⁻¹*(Matrix.of fun i (_ : Fin 1)=>c i)) 0 0
  have hprod : B*D⁻¹*C=Matrix.of (fun i j=>if i.val=d ∧ j.val=d then v else 0) := by
    ext i j
    dsimp only [v]
    simp only [Matrix.mul_apply,Matrix.of_apply]
    by_cases hi : i.val=d <;> by_cases hj : j.val=d <;>
      simp [B,C,hi,hj]
  letI : Invertible D := Matrix.invertibleOfIsUnitDet D (isUnit_iff_ne_zero.mpr hD)
  change (Matrix.fromBlocks A B C D).det=_
  rw [Matrix.det_fromBlocks₂₂,Matrix.invOf_eq_nonsing_inv,hprod]
  rfl

theorem one_matrix_det_even (A : TypeKey) (hf : FactorialDetChecked A)
    (hh : 0≤h0 A) (heven : Even (h0 A)) (hs : oneH1 A+1≤A.size) :
    (oneMatrix A).det=(cornerHankel A).det*
      ∏ k : Fin (A.size-oneH1 A-1),(Nat.factorial k.val:ℚ)*(Nat.factorial (k.val+2):ℚ) := by
  classical
  have hEven : h0 A=2*(oneH1 A:ℤ) ∧ oneH1 A=oneH2 A := by
    obtain ⟨b,hb⟩:=heven
    unfold oneH1 oneH2
    omega
  let d := oneH1 A
  let n := A.size-d-1
  have hn : (d+1)+n=A.size := by dsimp [d,n];omega
  let e : Fin (d+1)⊕Fin n ≃ Fin A.size := finSumFinEquiv.trans (finCongr hn)
  have einl (i : Fin (d+1)) : (e (Sum.inl i)).val=i.val := rfl
  have einr (j : Fin n) : (e (Sum.inr j)).val=(d+1)+j.val := rfl
  let R := regularHankel A (d+1)
  let D := factorialHankel n 2
  let b : Fin n→ℚ := fun j=>(Nat.factorial (j.val+1):ℚ)
  let B : Matrix (Fin (d+1)) (Fin n) ℚ := fun i j=>if i.val=d then b j else 0
  let C : Matrix (Fin n) (Fin (d+1)) ℚ := fun i j=>if j.val=d then b i else 0
  have hR (i : Fin A.size) : oneR A i=oneC A i := by
    simp only [oneR,oneC,if_pos hh,hEven.2]
  have hsym (i j : Fin A.size) : oneMatrix A i j=oneMatrix A j i := by
    simp only [oneMatrix,hR,add_comm]
  have hTL (i j : Fin (d+1)) : oneMatrix A (e (Sum.inl i)) (e (Sum.inl j))=R i j := by
    have hi : ((e (Sum.inl i)):ℤ)≤oneH1 A := by change ((e (Sum.inl i)).val:ℤ)≤_;rw [einl];have hi:=i.isLt;dsimp [d] at hi;omega
    have hj : ((e (Sum.inl j)):ℤ)≤oneH2 A := by change ((e (Sum.inl j)).val:ℤ)≤_;rw [einl];have hj:=j.isLt;dsimp [d] at hj;omega
    have hp : ((e (Sum.inl i)):ℤ)+e (Sum.inl j)≤h0 A := by omega
    have hr : oneR A (e (Sum.inl i))=0 := by unfold oneR;rw [if_pos hh];omega
    have hc : oneC A (e (Sum.inl j))=0 := by unfold oneC;rw [if_pos hh];omega
    rw [oneMatrix,if_pos hp,hr,hc,zero_add,if_pos rfl]
    simp only [R,regularHankel,einl]
  have hTR (i : Fin (d+1)) (j : Fin n) : oneMatrix A (e (Sum.inl i)) (e (Sum.inr j))=B i j := by
    have hi:=i.isLt
    have hiv : ((e (Sum.inl i)):ℤ)=(i.val:ℤ) := congrArg (fun x:ℕ=>(x:ℤ)) (einl i)
    have hjv : ((e (Sum.inr j)):ℤ)=(d:ℤ)+1+j.val := by exact_mod_cast einr j
    by_cases hi0 : i.val=d
    · have hp : ¬((e (Sum.inl i)):ℤ)+e (Sum.inr j)≤h0 A := by dsimp [d] at hi0 hjv;omega
      have hw : oneR A (e (Sum.inl i))+oneC A (e (Sum.inr j))=
          -(((e (Sum.inl i)):ℤ)+e (Sum.inr j)-h0 A) := by
        unfold oneR oneC
        simp only [if_pos hh]
        dsimp [d] at hi0 hjv
        omega
      simp only [oneMatrix,if_neg hp,if_pos hw,B,if_pos hi0,b]
      congr 2
      dsimp [d] at hi0 hjv
      omega
    · change oneMatrix A (e (Sum.inl i)) (e (Sum.inr j))=if i.val=d then b j else 0
      rw [if_neg hi0]
      unfold oneMatrix oneR oneC
      simp only [if_pos hh]
      split_ifs with hp hw <;> try rfl
      all_goals exfalso;dsimp [d] at hi hi0 hjv;omega
  have hBR (i j : Fin n) : oneMatrix A (e (Sum.inr i)) (e (Sum.inr j))=D i j := by
    have hiv : ((e (Sum.inr i)):ℤ)=(d:ℤ)+1+i.val := by exact_mod_cast einr i
    have hjv : ((e (Sum.inr j)):ℤ)=(d:ℤ)+1+j.val := by exact_mod_cast einr j
    have hp : ¬((e (Sum.inr i)):ℤ)+e (Sum.inr j)≤h0 A := by dsimp [d] at hiv hjv;omega
    have hw : oneR A (e (Sum.inr i))+oneC A (e (Sum.inr j))=
        -(((e (Sum.inr i)):ℤ)+e (Sum.inr j)-h0 A) := by
      unfold oneR oneC
      simp only [if_pos hh]
      dsimp [d] at hiv hjv
      omega
    simp only [oneMatrix,if_neg hp,if_pos hw,D,factorialHankel]
    congr 2
    dsimp [d] at hiv hjv
    omega
  have hblock : Matrix.fromBlocks R B C D=(oneMatrix A).submatrix e e := by
    ext i j
    rcases i with i|i <;> rcases j with j|j
    · exact (hTL i j).symm
    · exact (hTR i j).symm
    · change C i j=oneMatrix A (e (Sum.inr i)) (e (Sum.inl j))
      rw [hsym]
      exact (hTR j i).symm
    · exact (hBR i j).symm
  have h2det : D.det=facProduct n 2 := hf n (by dsimp [n];omega) 2 (by simp)
  have h0det : (factorialHankel (n+1) 0).det=facProduct (n+1) 0 :=
    hf (n+1) (by dsimp only [n,d];omega) 0 (by simp)
  have hDn : D.det≠0 := by rw [h2det];exact factorial_product_ne_zero n 2
  have hv := factorial_schur_scalar n h0det h2det
  have hschur := boundary_schur d n R D b b hDn
  dsimp only at hv hschur
  have hv' : ((Matrix.of fun (_ : Fin 1) j=>b j)*D⁻¹*(Matrix.of fun i (_ : Fin 1)=>b i)) 0 0=(n:ℚ)/((n:ℚ)+1) := hv
  rw [hv'] at hschur
  have hcorner : (Matrix.of fun i j=>R i j-if i.val=d ∧ j.val=d then (n:ℚ)/((n:ℚ)+1) else 0)=cornerHankel A := rfl
  rw [hcorner] at hschur
  have hdet : (Matrix.fromBlocks R B C D).det=D.det*(cornerHankel A).det := hschur
  have hd:=congrArg Matrix.det hblock
  rw [Matrix.det_submatrix_equiv_self] at hd
  rw [←hd,hdet,h2det]
  exact mul_comm _ _

theorem one_matrix_det (A : TypeKey) (hf : FactorialDetChecked A) :
  (oneMatrix A).det=
    if h0 A<0 then
      ∏ k : Fin A.size,(Nat.factorial k.val:ℚ)*(Nat.factorial (k.val+(h0 A).natAbs):ℚ)
    else if Odd (h0 A) then
      if A.size≤oneH1 A then (regularHankel A A.size).det
      else (regularHankel A (oneH1 A)).det*
        ∏ k : Fin (A.size-oneH1 A),(Nat.factorial k.val:ℚ)*(Nat.factorial (k.val+1):ℚ)
    else if A.size≤oneH1 A+1 then (regularHankel A A.size).det
    else (cornerHankel A).det*
      ∏ k : Fin (A.size-oneH1 A-1),(Nat.factorial k.val:ℚ)*(Nat.factorial (k.val+2):ℚ) := by
  by_cases hneg : h0 A<0
  · rw [if_pos hneg]
    exact one_matrix_det_negative A hf hneg
  · rw [if_neg hneg]
    have hh : 0≤h0 A := by omega
    by_cases ho : Odd (h0 A)
    · rw [if_pos ho]
      by_cases hs : A.size≤oneH1 A
      · rw [if_pos hs]
        apply one_matrix_det_regular A hh
        have he : oneH1 A=oneH2 A+1 := by
          obtain ⟨b,hb⟩:=ho
          unfold oneH1 oneH2
          omega
        omega
      · rw [if_neg hs]
        exact one_matrix_det_odd A hf hh ho (by omega)
    · rw [if_neg ho]
      have he : Even (h0 A) := Int.not_odd_iff_even.mp ho
      by_cases hs : A.size≤oneH1 A+1
      · rw [if_pos hs]
        apply one_matrix_det_regular A hh
        have heq : oneH1 A=oneH2 A := by
          obtain ⟨b,hb⟩:=he
          unfold oneH1 oneH2
          omega
        omega
      · rw [if_neg hs]
        exact one_matrix_det_even A hf hh he (by omega)
#print axioms moment_at_one
#print axioms hankel_at_one
#print axioms one_matrix_det
end
end CatalanCore.Li2.NVMod
