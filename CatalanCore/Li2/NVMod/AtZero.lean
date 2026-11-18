module
public import CatalanCore.Li2.NVMod.Expansion
public import CatalanCore.Li2.NVMod.LaurentBounds
public import CatalanCore.Li2.NVMod.RationalMoments
public import CatalanCore.Li2.NVMod.MomentLinear
public import CatalanCore.Linalg.MonicGram
public import CatalanCore.Linalg.HahnDet
@[expose] public section
set_option Elab.async false
open Polynomial Finset
open scoped BigOperators
namespace CatalanCore.Li2.NVMod
noncomputable section
private theorem zero_hom_poly (P : ℚ[X]) :
    affineRFHahnQ 0 1 one_ne_zero (rfPoly P)=polyHahnQ P := by
  simp only [affineRFHahnQ,rfPoly,RatFunc.liftRingHom_algebraMap,
    affinePolyHahnQ,RingHom.comp_apply,Polynomial.coe_compRingHom_apply]
  simp only [map_one,map_zero,one_mul,add_zero,Polynomial.comp_X]
private theorem hX_ne_zero : (hX : HahnSeries ℤ ℚ)≠0 :=
  HahnSeries.single_ne_zero one_ne_zero
private theorem zero_omega_expansion (m : ℕ) :
    atZero (omegaRF m)=∑ b∈Icc 1 m,HahnSeries.single ((b:ℤ)-m) ((b:ℚ)^2)⁻¹ := by
  rw [atZero_eq_hom]
  unfold omegaRF
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro b hb
  simp only [map_div₀,map_zpow₀,rfX,zero_hom_poly,polyHahnQ_X,polyHahnQ_C]
  rw [zpow_sub₀ hX_ne_zero]
  simp only [zpow_natCast,hX,HahnSeries.single_pow,nsmul_eq_mul,mul_one,one_pow,
    div_eq_mul_inv,HahnSeries.C_apply,HahnSeries.inv_single]
  simp [sub_eq_add_neg]
private theorem coeff_sum_hahn {ι : Type*} (S : Finset ι)
    (f : ι→HahnSeries ℤ ℚ) (e : ℤ) :
    (∑ i∈S,f i).coeff e=∑ i∈S,(f i).coeff e := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih => simp only [Finset.sum_insert hi,HahnSeries.coeff_add,ih]
theorem omega_at_zero (m : ℕ) (hm : 1≤m) :
    Oge (atZero (omegaRF m)) (1-(m:ℤ)) ∧
      (atZero (omegaRF m)).coeff (1-(m:ℤ))=1 := by
  rw [zero_omega_expansion]
  constructor
  · intro e he
    rw [coeff_sum_hahn]
    apply Finset.sum_eq_zero
    intro b hb
    have hb1:= (Finset.mem_Icc.mp hb).1
    exact HahnSeries.coeff_single_of_ne (by omega)
  · rw [coeff_sum_hahn]
    rw [Finset.sum_eq_single 1]
    · norm_num
    · intro b hb hne
      exact HahnSeries.coeff_single_of_ne (by omega)
    · intro hn
      exact False.elim (hn (Finset.mem_Icc.mpr ⟨le_refl _,hm⟩))

private theorem zero_hom_rat (q : ℚ) :
    affineRFHahnQ 0 1 one_ne_zero (algebraMap ℚ (RatFunc ℚ) q)=HahnSeries.C q := by
  rw [eq_ratCast,map_ratCast]
  rfl
private theorem zero_hom_X : affineRFHahnQ 0 1 one_ne_zero (rfX : RatFunc ℚ)=hX := by
  rw [rfX,zero_hom_poly,polyHahnQ_X]
theorem moment_at_zero (A : TypeKey) (g : ℚ[X]) :
  Oge (atZero (momentRF A g)-
    ∑ m∈poleSet A,(HahnSeries.C (residue A m*g.eval (-(m:ℚ))))*
      atZero (omegaRF m)) 1 ∧
  ∀ m : ℕ,1≤m → Oge (atZero (omegaRF m)) (1-(m:ℤ)) ∧
    (atZero (omegaRF m)).coeff (1-(m:ℤ))=1 := by
  constructor
  · simp only [atZero_eq_hom]
    rw [momentRF_partial_fractions,map_add,map_sum]
    simp only [map_sum,map_mul,zero_hom_rat,map_natCast,liNeg_map,zero_hom_X]
    rw [add_sub_cancel_left]
    apply Oge.sum
    intro k hk
    have hnat : Oge (k : HahnSeries ℤ ℚ) 0 := Oge.single 0 k
    simpa only [zero_add] using (hnat.mul (Oge.C _)).mul (liNeg_at_hX (k-1))
  · exact omega_at_zero

private theorem zero_omega_zero : atZero (omegaRF 0)=0 := by
  simp only [omegaRF,Finset.Icc_eq_empty_of_lt (by omega : (0:ℕ)<1),Finset.sum_empty,
    atZero_eq_hom,map_zero]
private theorem zero_moment_leading (A : TypeKey) (g : ℚ[X]) (m0 : ℕ)
    (hm0 : m0∈poleSet A) (hpos : 1≤m0)
    (hvan : ∀ m∈poleSet A,m0<m → g.eval (-(m:ℚ))=0) :
    Oge (atZero (momentRF A g)) (1-(m0:ℤ)) ∧
      (atZero (momentRF A g)).coeff (1-(m0:ℤ))=residue A m0*g.eval (-(m0:ℚ)) := by
  classical
  let S : HahnSeries ℤ ℚ := ∑ m∈poleSet A,
    HahnSeries.C (residue A m*g.eval (-(m:ℚ)))*atZero (omegaRF m)
  have htail := (moment_at_zero A g).1
  have hs : Oge S (1-(m0:ℤ)) := by
    apply Oge.sum
    intro m hm
    by_cases hz : m=0
    · simp only [hz,zero_omega_zero,mul_zero]
      exact Oge.zero _
    by_cases hmgt : m0<m
    · simp only [hvan m hm hmgt,mul_zero,map_zero,zero_mul]
      exact Oge.zero _
    have ho := (omega_at_zero m (by omega)).1
    exact ((Oge.C _).mul ho).mono (by omega)
  have heq : atZero (momentRF A g)=(atZero (momentRF A g)-S)+S := by ring
  constructor
  · rw [heq]
    exact (htail.mono (by omega)).add hs
  · have ht : (atZero (momentRF A g)-S).coeff (1-(m0:ℤ))=0 := htail _ (by omega)
    rw [HahnSeries.coeff_sub] at ht
    rw [sub_eq_zero.mp ht]
    dsimp only [S]
    rw [coeff_sum_hahn]
    rw [Finset.sum_eq_single m0]
    · rw [HahnSeries.C_apply,HahnSeries.coeff_single_zero_mul,(omega_at_zero m0 hpos).2,mul_one]
    · intro m hm hne
      by_cases hz : m=0
      · simp only [hz,zero_omega_zero,mul_zero,HahnSeries.coeff_zero]
      by_cases hmgt : m0<m
      · simp only [hvan m hm hmgt,mul_zero,map_zero,zero_mul,HahnSeries.coeff_zero]
      rw [HahnSeries.C_apply,HahnSeries.coeff_single_zero_mul,
        (omega_at_zero m (by omega)).1 _ (by omega),mul_zero]
    · intro hnot
      exact False.elim (hnot hm0)

theorem polynomial_gram_monic {K : Type*} [CommRing K] [Algebra ℚ K]
    (n : ℕ) (φ : ℚ[X]→ₗ[ℚ]K) (P : Fin n→ℚ[X])
    (hmon : ∀ i,(P i).Monic) (hdeg : ∀ i,(P i).natDegree=i.val) :
    (Matrix.of fun i j : Fin n=>φ (P i*P j)).det=
      (Matrix.of fun i j : Fin n=>φ (X^(i.val+j.val))).det := by
  classical
  let T : Matrix (Fin n) (Fin n) K := fun i j=>algebraMap ℚ K ((P i).coeff j)
  let H : Matrix (Fin n) (Fin n) K := fun i j=>φ (X^(i.val+j.val))
  have he (i : Fin n) : P i=∑ a : Fin n,C ((P i).coeff a)*X^a.val := by
    exact ((P i).as_sum_range_C_mul_X_pow' (by rw [hdeg];exact i.isLt)).trans
      (Fin.sum_univ_eq_sum_range (fun a=>C ((P i).coeff a)*X^a) n).symm
  have hentry : T*H*T.transpose=Matrix.of (fun i j : Fin n=>φ (P i*P j)) := by
    ext i j
    change (T*H*T.transpose) i j=φ (P i*P j)
    conv_rhs => rw [he i,he j]
    simp only [Matrix.mul_apply,Matrix.transpose_apply,Finset.sum_mul,Finset.mul_sum,map_sum]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    have hmul : (C ((P i).coeff b)*X^b.val)*(C ((P j).coeff a)*X^a.val)=
        ((P i).coeff b*(P j).coeff a) • (X^(b.val+a.val):ℚ[X]) := by
      simp only [Polynomial.smul_eq_C_mul,map_mul,pow_add]
      ring
    rw [hmul,map_smul]
    dsimp only [T,H]
    simp only [Algebra.smul_def,map_mul]
    ring
  rw [←hentry]
  apply CatalanCore.Linalg.det_monic_basis
  · intro i j hij
    change algebraMap ℚ K ((P i).coeff j)=0
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hdeg];exact hij),map_zero]
  · intro i
    change algebraMap ℚ K ((P i).coeff i)=1
    rw [←hdeg i,Polynomial.coeff_natDegree,(hmon i),map_one]

private def newtonBasis {n : ℕ} (ms : Fin n→ℕ) (i : Fin n) : ℚ[X] :=
  ∏ l : Fin i.val,(X+C (ms ⟨l.val,lt_trans l.isLt i.isLt⟩:ℚ))
private theorem newton_monic {n : ℕ} (ms : Fin n→ℕ) (i : Fin n) : (newtonBasis ms i).Monic := by
  apply Polynomial.monic_prod_of_monic
  intro l hl
  exact Polynomial.monic_X_add_C _
private theorem newton_degree {n : ℕ} (ms : Fin n→ℕ) (i : Fin n) :
    (newtonBasis ms i).natDegree=i.val := by
  have hd := Polynomial.natDegree_prod_of_monic Finset.univ
    (fun l : Fin i.val=>(X+C (ms ⟨l.val,lt_trans l.isLt i.isLt⟩:ℚ)))
    (fun l hl=>Polynomial.monic_X_add_C _)
  simpa only [newtonBasis,Polynomial.natDegree_X_add_C,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,smul_eq_mul,mul_one] using hd
private theorem newton_eval_zero {n : ℕ} (ms : Fin n→ℕ) (i l : Fin n) (hl : l < i) :
    (newtonBasis ms i).eval (-(ms l:ℚ))=0 := by
  classical
  unfold newtonBasis
  rw [Polynomial.eval_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ (⟨l.val,hl⟩:Fin i.val))
  simp only [eval_add,eval_X,eval_C]
  have he : (⟨l.val,lt_trans hl i.isLt⟩:Fin n)=l := Fin.ext rfl
  rw [he]
  ring
private theorem newton_eval_diag {n : ℕ} (ms : Fin n→ℕ) (i : Fin n) :
    (newtonBasis ms i).eval (-(ms i:ℚ))=
      ∏ l : Fin i.val,((ms ⟨l.val,lt_trans l.isLt i.isLt⟩:ℚ)-ms i) := by
  simp only [newtonBasis,eval_prod,eval_add,eval_X,eval_C]
  apply Finset.prod_congr rfl
  intro l hl
  ring

theorem triangular_product {M : Type*} [CommMonoid M] (n : ℕ) (f : Fin n→Fin n→M) :
    (∏ i : Fin n,∏ l : Fin i.val,f ⟨l.val,lt_trans l.isLt i.isLt⟩ i)=
      ∏ i : Fin n,∏ j∈Finset.univ.filter (fun j=>i < j),f i j := by
  classical
  have hi (i : Fin n) :
      (∏ l : Fin i.val,f ⟨l.val,lt_trans l.isLt i.isLt⟩ i)=
        ∏ j∈Finset.univ.filter (fun j=>j < i),f j i := by
    let e : Fin i.val ≃ {j : Fin n // j < i} := {
      toFun := fun l=>⟨⟨l.val,lt_trans l.isLt i.isLt⟩,l.isLt⟩
      invFun := fun j=>⟨j.val.val,j.property⟩
      left_inv := by intro l;rfl
      right_inv := by intro j;rfl}
    calc
      _=∏ j : {j : Fin n // j < i},f j.val i := e.prod_comp (fun j=>f j.val i)
      _=∏ j∈Finset.univ.filter (fun j=>j < i),f j i :=
        (Finset.prod_subtype _ (by simp) (fun j=>f j i)).symm
  simp_rw [hi,Finset.prod_filter]
  exact Finset.prod_comm

theorem hankel_at_zero (A : TypeKey) (ms : Fin A.size→ℕ)
    (hmem : ∀ i,ms i∈poleSet A ∧ 1≤ms i) (hdec : StrictAnti ms)
    (htop : ∀ m∈poleSet A,1≤m → m∉Set.range ms → ∀ i,m<ms i) :
  let e : ℤ := Finset.sum Finset.univ (fun i : Fin A.size => 1-((ms i : ℕ):ℤ))
  Oge (atZero (constantRF A)) e ∧
    (atZero (constantRF A)).coeff e=
      (∏ i : Fin A.size,residue A (ms i))*
        ∏ i : Fin A.size,∏ j∈Finset.univ.filter (fun j=>i < j),(((ms i : ℕ):ℚ)-ms j)^2 := by
  classical
  let P := newtonBasis ms
  let M : Matrix (Fin A.size) (Fin A.size) (HahnSeries ℤ ℚ) :=
    fun i j=>atZero (momentRF A (P i*P j))
  have hvan (i j : Fin A.size) (m : ℕ) (hm : m∈poleSet A) (hgt : ms i<m) :
      (P i*P j).eval (-(m:ℚ))=0 := by
    by_cases hr : m∈Set.range ms
    · obtain ⟨l,rfl⟩:=hr
      have hli : l < i := by
        by_contra h
        have hh:=hdec.antitone (le_of_not_gt h)
        omega
      rw [eval_mul,newton_eval_zero ms i l hli,zero_mul]
    · have hh:=htop m hm (by have hp:=(hmem i).2;omega) hr i
      omega
  have hb (i j : Fin A.size) :=
    zero_moment_leading A (P i*P j) (ms i) (hmem i).1 (hmem i).2 (hvan i j)
  have hgram : (Matrix.of fun i j : Fin A.size=>momentRF A (P i*P j)).det=constantRF A :=
    polynomial_gram_monic A.size (momentRFLinear A) P (newton_monic ms) (newton_degree ms)
  have hM : M.det=atZero (constantRF A) := by
    calc
      M.det=affineRFHahnQ 0 1 one_ne_zero
          ((Matrix.of fun i j : Fin A.size=>momentRF A (P i*P j)).det) := by
        rw [RingHom.map_det]
        congr 1
        apply Matrix.ext
        intro i j
        exact atZero_eq_hom _
      _=affineRFHahnQ 0 1 one_ne_zero (constantRF A) := congrArg _ hgram
      _=atZero (constantRF A) := (atZero_eq_hom _).symm
  have hp := CatalanCore.Linalg.det_potential_coeff M (fun i=>1-(ms i:ℤ)) (fun _=>0)
    (fun i j e he=>(hb i j).1 e (by simpa only [add_zero] using he))
  simp only [Finset.sum_const_zero,add_zero] at hp
  have ht : (Matrix.of fun i j : Fin A.size=>(M i j).coeff (1-(ms i:ℤ))).IsLowerTriangular := by
    intro i j hij
    change (atZero (momentRF A (P i*P j))).coeff (1-(ms i:ℤ))=0
    rw [(hb i j).2,eval_mul,newton_eval_zero ms j i hij,mul_zero,mul_zero]
  have hdiag (i : Fin A.size) :
      (M i i).coeff (1-(ms i:ℤ))=residue A (ms i)*((P i).eval (-(ms i:ℚ)))^2 := by
    rw [(hb i i).2,eval_mul]
    ring
  have hvand : (∏ i : Fin A.size,((P i).eval (-(ms i:ℚ)))^2)=
      ∏ i : Fin A.size,∏ j∈Finset.univ.filter (fun j=>i < j),((ms i:ℚ)-ms j)^2 := by
    dsimp only [P]
    simp_rw [newton_eval_diag,←Finset.prod_pow]
    exact triangular_product A.size (fun i j=>((ms i:ℚ)-ms j)^2)
  constructor
  · rw [←hM]
    exact hp.1
  · rw [←hM,hp.2]
    change (Matrix.of fun i j : Fin A.size=>(M i j).coeff (1-(ms i:ℤ))).det=_
    rw [Matrix.det_of_isLowerTriangular _ ht]
    simp only [Matrix.of_apply,hdiag,Finset.prod_mul_distrib,hvand]
#print axioms moment_at_zero
#print axioms hankel_at_zero
#print axioms polynomial_gram_monic
#print axioms triangular_product
end
end CatalanCore.Li2.NVMod
