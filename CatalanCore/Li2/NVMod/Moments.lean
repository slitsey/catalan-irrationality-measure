module
public import CatalanCore.Li2.NVMod.Definitions
public import CatalanCore.Li2.NV.PartialFractions
public import CatalanCore.Li2.Port.Unified.Modular.Base.SimplePoles
public import Mathlib.Algebra.Polynomial.PartialFractions
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
@[expose] public section
set_option Elab.async false
open Polynomial Finset
open scoped BigOperators
namespace CatalanCore.Li2.NVMod
/-- A monic divisor of a product of distinct linear factors is the product of
exactly those factors at which it vanishes. This includes the constant divisor. -/
theorem monic_divisor_linear_product {K : Type*} [Field K]
    [DecidableEq K] (S : Finset K) (D : K[X]) (hD : D.Monic)
    (hd : D∣∏ x∈S,(X-C x)) :
    D=∏ x∈S.filter (fun x=>D.eval x=0),(X-C x) := by
  classical
  let Q : K[X]:=∏ x∈S,(X-C x)
  have hQ : Q≠0:=Finset.prod_ne_zero_iff.mpr (fun x hx=>X_sub_C_ne_zero x)
  have hQr : Q.roots=S.val:=Polynomial.roots_prod_X_sub_C S
  have hle : D.roots≤S.val:=by
    rw [←hQr]
    exact Polynomial.roots.le_of_dvd hQ hd
  have hNd : D.roots.Nodup:=Multiset.nodup_of_le hle S.nodup
  have hQS : Q.Splits:=Polynomial.Splits.prod (fun x hx=>Polynomial.Splits.X_sub_C x)
  have hDS : D.Splits:=hQS.of_dvd hQ hd
  have hset : D.roots.toFinset=S.filter (fun x=>D.eval x=0) := by
    ext x
    simp only [Multiset.mem_toFinset,Finset.mem_filter]
    constructor
    · intro hx
      exact ⟨Multiset.mem_of_le hle hx,(Polynomial.mem_roots hD.ne_zero).mp hx⟩
    · intro hx
      exact (Polynomial.mem_roots hD.ne_zero).mpr hx.2
  rw [←hset]
  have hval : D.roots.toFinset.val=D.roots := by
    change D.roots.dedup=D.roots
    exact hNd.dedup
  change D=(D.roots.toFinset.val.map (fun x=>X-C x)).prod
  rw [hval]
  exact hDS.eq_prod_roots_of_monic hD
private theorem poleProduct_roots (S : Finset ℕ) :
    (∏ m∈S,(X+C (m:ℚ))).roots=S.val.map (fun m : ℕ=>-(m:ℚ)) := by
  classical
  rw [Polynomial.roots_prod _ S (Finset.prod_ne_zero_iff.mpr (fun m hm=>X_add_C_ne_zero (m:ℚ)))]
  simp only [Polynomial.roots_X_add_C,Multiset.bind_singleton]
private theorem poleIndices_of_denom (F : RatFunc ℚ) (T : Finset ℕ)
    (hD : F.denom=∏ m∈T,(X+C (m:ℚ))) : poleIndices F=T := by
  classical
  unfold poleIndices
  rw [hD,poleProduct_roots]
  simp only [Multiset.toFinset_map,Finset.val_toFinset]
  have hf : (T.image (fun m : ℕ=>-(m:ℚ))).filter (fun x=>x≤0 ∧ x.den=1)=
      T.image (fun m : ℕ=>-(m:ℚ)) := by
    apply Finset.filter_eq_self.mpr
    intro x hx
    obtain ⟨m,hm,rfl⟩:=Finset.mem_image.mp hx
    simp
  rw [hf,Finset.image_image]
  simp [Function.comp_def]
/-- Canonical rational-function reduction removes precisely the cancelled
linear factors; its pole set is a checked subset of the original finite set. -/
theorem canonical_poles (F : RatFunc ℚ) (S : Finset ℕ)
    (hdiv : F.denom∣∏ m∈S,(X+C (m:ℚ))) :
    let T:=S.filter (fun m : ℕ=>F.denom.eval (-(m:ℚ))=0)
    F.denom=∏ m∈T,(X+C (m:ℚ)) ∧ poleIndices F=T := by
  classical
  let R:=S.image (fun m : ℕ=>-(m:ℚ))
  have hinj : Function.Injective (fun m : ℕ=>-(m:ℚ)) := by
    intro a b h
    exact_mod_cast (neg_injective h)
  have hQ : (∏ x∈R,(X-C x))=∏ m∈S,(X+C (m:ℚ)) := by
    unfold R
    rw [Finset.prod_image (fun a ha b hb h=>hinj h)]
    simp only [map_neg,sub_neg_eq_add]
  have hd:=monic_divisor_linear_product R F.denom (RatFunc.monic_denom F) (hQ.symm ▸ hdiv)
  unfold R at hd
  rw [Finset.filter_image,Finset.prod_image (fun a ha b hb h=>hinj h)] at hd
  simp only [map_neg,sub_neg_eq_add] at hd
  exact ⟨hd,poleIndices_of_denom F _ hd⟩
noncomputable def poleProd (S : Finset ℕ) : ℚ[X]:=∏ m∈S,(X+C (m:ℚ))
private theorem poleProd_monic (S : Finset ℕ) : (poleProd S).Monic :=
  Polynomial.monic_prod_of_monic _ _ (fun m hm=>monic_X_add_C _)
private theorem piPl_negative (S : Finset ℕ) :
    Port.Li2.SimplePoles.piPl (S.image (fun m : ℕ=>-(m:ℤ)))=poleProd S := by
  classical
  unfold Port.Li2.SimplePoles.piPl poleProd
  rw [Finset.prod_image (by intro a ha b hb h;exact_mod_cast (neg_injective h))]
  simp only [Int.cast_neg,Int.cast_natCast,map_neg,sub_neg_eq_add]
private theorem negative_nat_injective : Function.Injective (fun m : ℕ=>-(m:ℤ)) := by
  intro a b h
  exact_mod_cast (neg_injective h)
private theorem resP_negative (P : ℚ[X]) (S : Finset ℕ) (m : ℕ) :
    Port.Li2.SimplePoles.resP P (S.image (fun n : ℕ=>-(n:ℤ))) (-(m:ℤ))=
      P.eval (-(m:ℚ))/(∏ n∈S.erase m,((n:ℚ)-m)) := by
  classical
  unfold Port.Li2.SimplePoles.resP
  rw [←Finset.image_erase negative_nat_injective]
  rw [Finset.prod_image (fun a ha b hb h=>negative_nat_injective h)]
  simp only [Int.cast_neg,Int.cast_natCast,sub_neg_eq_add]
  congr 2
  funext n
  ring
/-- The finite polynomial identity reuses Tang's generic simple-pole decomposition. -/
theorem pole_polynomial_decomposition (P : ℚ[X]) (S : Finset ℕ) :
    P=(P /ₘ poleProd S)*poleProd S+
      ∑ m∈S,C (P.eval (-(m:ℚ))/∏ n∈S.erase m,((n:ℚ)-m))*poleProd (S.erase m) := by
  classical
  have h:=Port.Li2.SimplePoles.partial_fractionsP P (S.image (fun m : ℕ=>-(m:ℤ)))
  unfold Port.Li2.SimplePoles.polyPart at h
  rw [piPl_negative] at h
  rw [Finset.sum_image (fun a ha b hb h=>negative_nat_injective h)] at h
  convert h using 1
  congr 1
  apply Finset.sum_congr rfl
  intro m hm
  rw [resP_negative]
  congr 1
  change poleProd (S.erase m)=Port.Li2.SimplePoles.piPl ((S.image (fun n : ℕ=>-(n:ℤ))).erase (-(m:ℤ)))
  rw [←Finset.image_erase negative_nat_injective,piPl_negative]
private theorem poleProd_derivative (S : Finset ℕ) (m : ℕ) (hm : m∈S) :
    (poleProd S).derivative.eval (-(m:ℚ))=∏ n∈S.erase m,((n:ℚ)-m) := by
  classical
  have hp : poleProd S=(X+C (m:ℚ))*poleProd (S.erase m) :=
    (Finset.mul_prod_erase S (fun m : ℕ=>X+C (m:ℚ)) hm).symm
  rw [hp]
  simp [poleProd,derivative_mul,eval_prod,sub_eq_add_neg,add_comm]

noncomputable def poleCoeff (P : ℚ[X]) (S : Finset ℕ) (m : ℕ) : ℚ :=
  P.eval (-(m:ℚ))/(poleProd S).derivative.eval (-(m:ℚ))
/-- The finite partial-fraction identity in the actual rational-function field. -/
theorem pole_fraction_decomposition (P : ℚ[X]) (S : Finset ℕ) :
    rfPoly P/rfPoly (poleProd S)=rfPoly (P /ₘ poleProd S)+
      ∑ m∈S,rfPoly (C (poleCoeff P S m))/rfPoly (X+C (m:ℚ)) := by
  classical
  have hP : P=(P /ₘ poleProd S)*poleProd S+
      ∑ m∈S,C (poleCoeff P S m)*poleProd (S.erase m) := by
    calc
      P=(P /ₘ poleProd S)*poleProd S+
          ∑ m∈S,C (P.eval (-(m:ℚ))/∏ n∈S.erase m,((n:ℚ)-m))*poleProd (S.erase m) :=
        pole_polynomial_decomposition P S
      _=(P /ₘ poleProd S)*poleProd S+
          ∑ m∈S,C (poleCoeff P S m)*poleProd (S.erase m) := by
        congr 1
        apply Finset.sum_congr rfl
        intro m hm
        rw [poleCoeff,poleProd_derivative S m hm]
  let f : ℚ[X]→+*RatFunc ℚ:=algebraMap ℚ[X] (RatFunc ℚ)
  have heq : f P=f (P /ₘ poleProd S)*f (poleProd S)+
      ∑ m∈S,f (C (poleCoeff P S m))*f (poleProd (S.erase m)) := by
    simpa only [map_add,map_mul,map_sum] using congrArg f hP
  have hQ : f (poleProd S)≠0:=RatFunc.algebraMap_ne_zero (poleProd_monic S).ne_zero
  change f P/f (poleProd S)=f (P /ₘ poleProd S)+∑ m∈S,f (C (poleCoeff P S m))/f (X+C (m:ℚ))
  rw [heq,add_div,Finset.sum_div,mul_div_cancel_right₀ _ hQ]
  congr 1
  apply Finset.sum_congr rfl
  intro m hm
  have hfac : f (poleProd S)=f (X+C (m:ℚ))*f (poleProd (S.erase m)) := by
    have hh : poleProd S=(X+C (m:ℚ))*poleProd (S.erase m):=
      (Finset.mul_prod_erase S (fun m : ℕ=>X+C (m:ℚ)) hm).symm
    rw [hh,map_mul]
  have hE : f (poleProd (S.erase m))≠0:=RatFunc.algebraMap_ne_zero (poleProd_monic (S.erase m)).ne_zero
  have hL : f (X+C (m:ℚ))≠0:=RatFunc.algebraMap_ne_zero (X_add_C_ne_zero (m:ℚ))
  rw [hfac]
  field_simp
private theorem pole_factors_coprime (m n : ℕ) (hne : m≠n) :
    IsCoprime (X+C (m:ℚ)) (X+C (n:ℚ)) := by
  have hn : (m:ℚ)-(n:ℚ)≠0:=sub_ne_zero.mpr (by exact_mod_cast hne)
  refine ⟨C (1/((m:ℚ)-n)),-C (1/((m:ℚ)-n)),?_⟩
  calc
    C (1/((m:ℚ)-n))*(X+C (m:ℚ))+-C (1/((m:ℚ)-n))*(X+C (n:ℚ))=
        C (1/((m:ℚ)-n))*C ((m:ℚ)-n):=by rw [map_sub];ring
    _=1:=by rw [←map_mul,one_div_mul_cancel hn,map_one]
/-- Uniqueness is the canonical Mathlib theorem, specialized to constant residues. -/
theorem pole_fraction_unique (S : Finset ℕ) (q₁ q₂ : ℚ[X]) (r₁ r₂ : ℕ→ℚ)
    (h : rfPoly q₁+∑ m∈S,rfPoly (C (r₁ m))/rfPoly (X+C (m:ℚ))=
      rfPoly q₂+∑ m∈S,rfPoly (C (r₂ m))/rfPoly (X+C (m:ℚ))) :
    q₁=q₂ ∧ ∀ m∈S,r₁ m=r₂ m := by
  classical
  have hcop : Set.Pairwise (↑S : Set ℕ) (fun m n=>IsCoprime (X+C (m:ℚ)) (X+C (n:ℚ))) := by
    intro m hm n hn hne
    exact pole_factors_coprime m n hne
  have hr₁ : ∀ m∈S,(C (r₁ m)).degree<(X+C (m:ℚ)).degree := by
    intro m hm
    rw [degree_X_add_C]
    exact degree_C_le.trans_lt (by decide)
  have hr₂ : ∀ m∈S,(C (r₂ m)).degree<(X+C (m:ℚ)).degree := by
    intro m hm
    rw [degree_X_add_C]
    exact degree_C_le.trans_lt (by decide)
  have hu:=Polynomial.quo_add_sum_rem_div_unique (RatFunc ℚ)
    (g:=fun m : ℕ=>X+C (m:ℚ)) (s:=S) (fun m hm=>monic_X_add_C _) hcop hr₁ hr₂ h
  exact ⟨hu.1,fun m hm=>Polynomial.C_injective (hu.2 m hm)⟩

/-- Canonical and unreduced partial fractions have exactly the same coefficients. -/
theorem fraction_coefficients (P : ℚ[X]) (S : Finset ℕ) :
    let F:=rfPoly P/rfPoly (poleProd S)
    pp F=P /ₘ poleProd S ∧ ∀ m∈S,
      (if m∈poleIndices F then poleRes F m else 0)=poleCoeff P S m := by
  classical
  let F:=rfPoly P/rfPoly (poleProd S)
  have hdiv : F.denom∣poleProd S:=RatFunc.denom_div_dvd P (poleProd S)
  obtain ⟨hD,hI⟩:=canonical_poles F S hdiv
  let T:=S.filter (fun m : ℕ=>F.denom.eval (-(m:ℚ))=0)
  change F.denom=poleProd T at hD
  change poleIndices F=T at hI
  have ht : T⊆S:=Finset.filter_subset _ _
  have hCanon : F=rfPoly (pp F)+∑ m∈T,rfPoly (C (poleRes F m))/rfPoly (X+C (m:ℚ)) := by
    have hh:=pole_fraction_decomposition F.num T
    unfold poleCoeff at hh
    rw [←hD] at hh
    calc
      F=rfPoly F.num/rfPoly F.denom:=(RatFunc.num_div_denom F).symm
      _=rfPoly (pp F)+∑ m∈T,rfPoly (C (poleRes F m))/rfPoly (X+C (m:ℚ)):=by
        simpa only [pp,poleRes] using hh
  let r : ℕ→ℚ:=fun m=>if m∈T then poleRes F m else 0
  have hext : (∑ m∈S,rfPoly (C (r m))/rfPoly (X+C (m:ℚ)))=
      ∑ m∈T,rfPoly (C (poleRes F m))/rfPoly (X+C (m:ℚ)) := by
    have hh : (∑ m∈T,rfPoly (C (r m))/rfPoly (X+C (m:ℚ)))=
        ∑ m∈S,rfPoly (C (r m))/rfPoly (X+C (m:ℚ)) := by
      apply Finset.sum_subset ht
      intro m hmS hmT
      simp [r,hmT,rfPoly]
    rw [←hh]
    apply Finset.sum_congr rfl
    intro m hm
    simp only [r,if_pos hm]
  have heq : rfPoly (pp F)+∑ m∈S,rfPoly (C (r m))/rfPoly (X+C (m:ℚ))=
      rfPoly (P /ₘ poleProd S)+∑ m∈S,rfPoly (C (poleCoeff P S m))/rfPoly (X+C (m:ℚ)) := by
    rw [hext,←hCanon]
    exact pole_fraction_decomposition P S
  have hu:=pole_fraction_unique S (pp F) (P /ₘ poleProd S) r (poleCoeff P S) heq
  refine ⟨hu.1,?_⟩
  intro m hm
  rw [hI]
  exact hu.2 m hm
private theorem omega_factor (z : ℚ) (hz : z≠0) (m : ℕ) :
    omega z m=z^(-(m:ℤ))*tauK z m := by
  unfold omega tauK
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  rw [show (b:ℤ)-m=-(m:ℤ)+(b:ℤ) by omega,zpow_add₀ hz]
  simp only [zpow_natCast]
  ring

/-- Evaluation of the fixed functional may use any unreduced simple-pole denominator. -/
theorem regularV_fraction (P : ℚ[X]) (S : Finset ℕ) (z : ℚ) (hz : z≠0) :
    regularV z (rfPoly P/rfPoly (poleProd S))=
      (∑ m∈S,poleCoeff P S m*omega z m)+
        ∑ k∈Finset.Icc 1 (P /ₘ poleProd S).natDegree,
          (k:ℚ)*(P /ₘ poleProd S).coeff k*liNeg (k-1) z := by
  classical
  let F:=rfPoly P/rfPoly (poleProd S)
  have hc:=fraction_coefficients P S
  have hdiv : F.denom∣poleProd S:=RatFunc.denom_div_dvd P (poleProd S)
  obtain ⟨hD,hI⟩:=canonical_poles F S hdiv
  have hsub : poleIndices F⊆S := by rw [hI];exact Finset.filter_subset _ _
  change (∑ m∈poleIndices F,poleRes F m*z^(-(m:ℤ))*tauK z m)+
    (∑ k∈Finset.Icc 1 (pp F).natDegree,(k:ℚ)*(pp F).coeff k*liNeg (k-1) z)=_
  rw [hc.1]
  congr 1
  let f : ℕ→ℚ:=fun m=>(if m∈poleIndices F then poleRes F m else 0)*z^(-(m:ℤ))*tauK z m
  calc
    (∑ m∈poleIndices F,poleRes F m*z^(-(m:ℤ))*tauK z m)=∑ m∈poleIndices F,f m := by
      apply Finset.sum_congr rfl
      intro m hm
      simp only [f,if_pos hm]
    _=∑ m∈S,f m:=Finset.sum_subset hsub (fun m hmS hmI=>by simp [f,hmI])
    _=∑ m∈S,poleCoeff P S m*omega z m := by
      apply Finset.sum_congr rfl
      intro m hm
      dsimp only [f]
      rw [hc.2 m hm,omega_factor z hz m]
      ring
/-- R2: the polynomial determinant and scalar residue evaluation are the same matrix. -/
theorem eval_map_det {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℤ[X]) (p : ℕ) (r : ZMod p) :
    (M.det.map (Int.castRingHom (ZMod p))).eval r=
      Matrix.det (fun i j : ι=>((M i j).map (Int.castRingHom (ZMod p))).eval r) := by
  let f : ℤ[X]→+*ZMod p:=(Polynomial.evalRingHom r).comp (Polynomial.mapRingHom (Int.castRingHom (ZMod p)))
  change f M.det=(f.mapMatrix M).det
  exact f.map_det M
/-- R5: the paper's finite partial-fraction formula for the original functional. -/
theorem moment_partial_fractions (A : TypeKey) (g : ℚ[X]) (z : ℚ)
    (hz : z≠0) (h1 : z≠1) :
    L A z g=(∑ m∈poleSet A,residue A m*g.eval (-(m:ℚ))*omega z m)+
      ∑ k∈Finset.Icc 1 (polyPart A g).natDegree,(k:ℚ)*(polyPart A g).coeff k*liNeg (k-1) z := by
  classical
  unfold L
  have hf : rfPoly g*weight A=rfPoly (weightNum A*g)/rfPoly (poleProd (poleSet A)) := by
    simp only [weight,weightDen,poleProd,rfPoly,map_mul,div_eq_mul_inv]
    ring
  rw [hf]
  have hh:=regularV_fraction (weightNum A*g) (poleSet A) z hz
  have hc (m : ℕ) : poleCoeff (weightNum A*g) (poleSet A) m=residue A m*g.eval (-(m:ℚ)) := by
    simp only [poleCoeff,poleProd,residue,weightDen,eval_mul,div_eq_mul_inv]
    ring
  have hs : (∑ m∈poleSet A,poleCoeff (weightNum A*g) (poleSet A) m*omega z m)=
      ∑ m∈poleSet A,residue A m*g.eval (-(m:ℚ))*omega z m := by
    apply Finset.sum_congr rfl
    intro m hm
    rw [hc]
  rw [hs] at hh
  simpa only [polyPart,weightDen,poleProd] using hh

#print axioms monic_divisor_linear_product
#print axioms canonical_poles
#print axioms pole_polynomial_decomposition
#print axioms pole_fraction_decomposition
#print axioms pole_fraction_unique
#print axioms fraction_coefficients
#print axioms regularV_fraction
#print axioms eval_map_det
#print axioms moment_partial_fractions
end CatalanCore.Li2.NVMod
