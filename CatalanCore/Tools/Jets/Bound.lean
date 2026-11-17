module

public import CatalanCore.Tools.Jets.Collisions
public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Order.Interval.Finset.Fin

@[expose] public section
set_option Elab.async false
open Polynomial
open scoped BigOperators
namespace CatalanCore.Tools.Jets

noncomputable def jetPoly {M : ℕ} (J : Finset (Fin M)) (a b : Fin M → ℂ)
    (p : MvPolynomial (Fin M) ℂ) : MvPolynomial (Fin M) ℂ :=
  ∑ S ∈ J.powerset, ((∏ i ∈ J \ S, a i)*(∏ i ∈ S, b i)) • partials S p

theorem eval_jetPoly (M : ℕ) (J : Finset (Fin M)) (a b x : Fin M → ℂ)
    (p : MvPolynomial (Fin M) ℂ) :
    MvPolynomial.eval x (jetPoly J a b p)=mixedJet J a b x p := by
  classical
  simp [jetPoly, mixedJet, map_sum, mul_assoc]

theorem jetPoly_insert (M : ℕ) (J : Finset (Fin M)) (i : Fin M) (hi : i ∉ J)
    (a b : Fin M → ℂ) (p : MvPolynomial (Fin M) ℂ) :
    jetPoly (insert i J) a b p=jetOp (a i) (b i) i (jetPoly J a b p) := by
  classical
  unfold jetPoly
  rw [Finset.sum_powerset_insert hi]
  simp only [jetOp, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply]
  simp_rw [map_sum, map_smul, Finset.smul_sum]
  apply congrArg₂ (fun u v : MvPolynomial (Fin M) ℂ => u+v)
  · apply Finset.sum_congr rfl
    intro S hS
    have hiS : i ∉ S := fun h => hi ((Finset.mem_powerset.mp hS) h)
    have hs : insert i J \ S=insert i (J \ S) := by
      ext j
      by_cases hji : j=i <;> simp [hji,hiS]
    simp [hs,hi,hiS,smul_smul,mul_assoc]
  · apply Finset.sum_congr rfl
    intro S hS
    have hiS : i ∉ S := fun h => hi ((Finset.mem_powerset.mp hS) h)
    have hs : insert i J \ insert i S=J \ S := by
      ext j
      by_cases hji : j=i <;> simp [hji,hi]
    have hd : partials (insert i S) p=MvPolynomial.pderiv i (partials S p) := by
      simpa [hiS] using partials_last M (insert i S) i (by simp) p
    simp [hs,hd,hiS,smul_smul,mul_assoc,mul_comm,mul_left_comm]

theorem eval_update_hasDerivAt (M : ℕ) (p : MvPolynomial (Fin M) ℂ)
    (x : Fin M → ℂ) (i : Fin M) (z : ℂ) :
    HasDerivAt (fun w : ℂ => MvPolynomial.eval (Function.update x i w) p)
      (MvPolynomial.eval (Function.update x i z) (MvPolynomial.pderiv i p)) z := by
  classical
  induction p using MvPolynomial.induction_on with
  | C c => simpa using hasDerivAt_const z c
  | add p q hp hq =>
    convert hp.add hq using 1 <;> simp [Pi.add_apply, Pi.mul_apply, id_eq] <;> funext w <;> rfl
  | mul_X p j hp =>
    by_cases hj : j=i
    · subst j
      convert hp.mul (hasDerivAt_id z) using 1 <;> simp [Pi.add_apply, Pi.mul_apply, id_eq,mul_comm,add_comm] <;> funext w <;> rfl
    · convert hp.mul (hasDerivAt_const z (x j)) using 1 <;> simp [Pi.add_apply, Pi.mul_apply, id_eq,hj,Ne.symm hj,mul_comm] <;> funext w <;> rfl

theorem polynomial_jet_cauchy (M : ℕ) (p : MvPolynomial (Fin M) ℂ)
    (x : Fin M → ℂ) (i : Fin M) (a b : ℂ) (r C : ℝ) (hr : 0 < r)
    (hpoint : ‖MvPolynomial.eval x p‖ ≤ C)
    (hsphere : ∀ z ∈ Metric.sphere (x i) r,
      ‖MvPolynomial.eval (Function.update x i z) p‖ ≤ C) :
    ‖MvPolynomial.eval x (jetOp a b i p)‖ ≤ (‖a‖+‖b‖/r)*C := by
  classical
  let f : ℂ → ℂ := fun z => MvPolynomial.eval (Function.update x i z) p
  have hf : Differentiable ℂ f := fun z => (eval_update_hasDerivAt M p x i z).differentiableAt
  have hd := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr hf.diffContOnCl hsphere
  have heq : deriv f (x i)=MvPolynomial.eval x (MvPolynomial.pderiv i p) := by
    simpa [f] using (eval_update_hasDerivAt M p x i (x i)).deriv
  rw [heq] at hd
  have hv : MvPolynomial.eval x (jetOp a b i p)=
      a*MvPolynomial.eval x p+b*MvPolynomial.eval x (MvPolynomial.pderiv i p) := by
    simp [jetOp]
  rw [hv]
  calc
    _ ≤ ‖a‖*‖MvPolynomial.eval x p‖+‖b‖*‖MvPolynomial.eval x (MvPolynomial.pderiv i p)‖ := by
      simpa only [norm_mul] using norm_add_le (a*MvPolynomial.eval x p)
        (b*MvPolynomial.eval x (MvPolynomial.pderiv i p))
    _ ≤ ‖a‖*C+‖b‖*(C/r) :=
      add_le_add (mul_le_mul_of_nonneg_left hpoint (norm_nonneg _))
        (mul_le_mul_of_nonneg_left hd (norm_nonneg _))
    _=(‖a‖+‖b‖/r)*C := by ring

def JetDisc {M : ℕ} (J : Finset (Fin M)) (x : Fin M → ℂ) (r : ℝ)
    (y : Fin M → ℂ) : Prop :=
  ∀ i, if i ∈ J then ‖y i-x i‖ ≤ r else y i=x i

theorem JetDisc.self {M : ℕ} (J : Finset (Fin M)) (x : Fin M → ℂ)
    {r : ℝ} (hr : 0 ≤ r) : JetDisc J x r x := by
  intro i
  split <;> simp_all

theorem JetDisc.update {M : ℕ} (J : Finset (Fin M)) (x : Fin M → ℂ)
    (i : Fin M) (hi : i ∉ J) (r : ℝ) (z : ℂ) (hz : ‖z-x i‖ ≤ r)
    (y : Fin M → ℂ) (hy : JetDisc J (Function.update x i z) r y) :
    JetDisc (insert i J) x r y := by
  classical
  intro j
  have hj := hy j
  by_cases hji : j=i
  · subst j
    have he : y i=z := by simpa [hi] using hj
    simpa [he] using hz
  · simpa [hji] using hj

theorem mixedJet_cauchy_bound (M : ℕ) (J : Finset (Fin M)) (a b : Fin M → ℂ)
    (p : MvPolynomial (Fin M) ℂ) (r : ℝ) (hr : 0 < r) (C : ℝ)
    (x : Fin M → ℂ) (hP : ∀ y, JetDisc J x r y → ‖MvPolynomial.eval y p‖ ≤ C) :
    ‖mixedJet J a b x p‖ ≤ C*∏ i ∈ J, (‖a i‖+‖b i‖/r) := by
  classical
  rw [← eval_jetPoly]
  induction J using Finset.induction_on generalizing x with
  | empty =>
    simpa [jetPoly,partials,JetDisc] using hP x (JetDisc.self ∅ x hr.le)
  | @insert i J hi ih =>
    let B := C*∏ j ∈ J, (‖a j‖+‖b j‖/r)
    have hb (z : ℂ) (hz : ‖z-x i‖ ≤ r) :
        ‖MvPolynomial.eval (Function.update x i z) (jetPoly J a b p)‖ ≤ B := by
      apply ih
      intro y hy
      exact hP y (JetDisc.update J x i hi r z hz y hy)
    have hpoint : ‖MvPolynomial.eval x (jetPoly J a b p)‖ ≤ B := by
      simpa using hb (x i) (by simpa using hr.le)
    have hsphere : ∀ z ∈ Metric.sphere (x i) r,
        ‖MvPolynomial.eval (Function.update x i z) (jetPoly J a b p)‖ ≤ B := by
      intro z hz
      exact hb z (by simpa [Metric.mem_sphere,dist_eq_norm] using le_of_eq hz)
    rw [jetPoly_insert M J i hi]
    calc
      _ ≤ (‖a i‖+‖b i‖/r)*B :=
        polynomial_jet_cauchy M (jetPoly J a b p) x i (a i) (b i) r B hr hpoint hsphere
      _ = _ := by rw [Finset.prod_insert hi]; dsimp [B]; ring

theorem confluent_pair_card (M : ℕ) (c : ConfluentConfig M) (J : Finset (Fin M))
    (hp : ∀ i j, c.paired i j → i ∈ J ∧ j ∈ J) : 2*c.pairCount ≤ J.card := by
  classical
  let t : Fin M × Fin M → Finset (Fin M) := fun p => {p.1,p.2}
  have hd : (c.pairs : Set (Fin M × Fin M)).PairwiseDisjoint t := by
    intro p hp' q hq' hpq
    apply Finset.disjoint_left.mpr
    intro i hip hiq
    have hh := c.disjoint p hp' q hq' hpq
    simp only [t,Finset.mem_insert,Finset.mem_singleton] at hip hiq
    rcases hip with rfl | rfl <;> rcases hiq with h | h <;> simp_all
  have ht (p) (hp' : p ∈ c.pairs) : (t p).card=2 := by
    simp [t,ne_of_lt (c.ordered p hp')]
  have hs : c.pairs.biUnion t ⊆ J := by
    intro i hi
    obtain ⟨p,hp',hi⟩ := Finset.mem_biUnion.mp hi
    have hh := hp p.1 p.2 (Or.inl hp')
    simp only [t,Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl | rfl <;> tauto
  calc
    2*c.pairCount = ∑ p ∈ c.pairs, (t p).card := by
      symm
      calc
        _ = ∑ _p ∈ c.pairs, 2 := Finset.sum_congr rfl ht
        _ = _ := by simp [ConfluentConfig.pairCount,Nat.mul_comm]
    _ = (c.pairs.biUnion t).card := (Finset.card_biUnion hd).symm
    _ ≤ J.card := Finset.card_le_card hs

theorem complete_edge_product (M : ℕ) (a : Fin M → ℝ) :
    (∏ i : Fin M, ∏ j ∈ Finset.Ioi i, (a i*a j)^2) =
      ∏ i : Fin M, a i^(2*(M-1)) := by
  classical
  have hs : (∏ i : Fin M, ∏ j ∈ Finset.Ioi i, a j^2) =
      ∏ j : Fin M, ∏ i ∈ Finset.Iio j, a j^2 := by
    exact Finset.prod_comm' (fun i j => by simp)
  simp_rw [mul_pow,Finset.prod_mul_distrib]
  rw [hs,← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  simp only [Finset.prod_const,← pow_mul,← pow_add]
  congr 1
  rw [Fin.card_Ioi,Fin.card_Iio]
  have := i.isLt
  omega

theorem disc_edge_bound (M : ℕ) (J : Finset (Fin M)) (x y : Fin M → ℂ)
    (r δ : ℝ) (hr : 0 ≤ r) (hδ : 0 < δ) (hy : JetDisc J x r y)
    (i j : Fin M) (hgap : i ∈ J ∨ j ∈ J → δ ≤ ‖x i-x j‖) :
    ‖y i-y j‖ ≤ ‖x i-x j‖*(if i ∈ J then 1+r/δ else 1)*
      (if j ∈ J then 1+r/δ else 1) := by
  classical
  have htri : ‖y i-y j‖ ≤ ‖x i-x j‖+‖y i-x i‖+‖y j-x j‖ := by
    have heq : y i-y j=(x i-x j)+(y i-x i)-(y j-x j) := by ring
    rw [heq]
    exact (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
  have hi := hy i
  have hj := hy j
  have ht : 0 ≤ r/δ := div_nonneg hr hδ.le
  have hrd (h : i ∈ J ∨ j ∈ J) : r ≤ ‖x i-x j‖*(r/δ) := by
    calc
      r = δ*(r/δ) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (hgap h) ht
  by_cases hiJ : i ∈ J <;> by_cases hjJ : j ∈ J
  · simp only [hiJ,hjJ,if_true] at hi hj ⊢
    have hh := hrd (Or.inl hiJ)
    have hh' := mul_nonneg (norm_nonneg (x i-x j)) (sq_nonneg (r/δ))
    nlinarith
  · simp only [hiJ,hjJ,if_true,if_false] at hi hj ⊢
    rw [hj] at htri ⊢
    simp only [sub_self,norm_zero,add_zero] at htri
    have hh := hrd (Or.inl hiJ)
    nlinarith
  · simp only [hiJ,hjJ,if_true,if_false] at hi hj ⊢
    rw [hi] at htri ⊢
    simp only [sub_self,norm_zero,add_zero] at htri
    have hh := hrd (Or.inr hjJ)
    nlinarith
  · simp_all

theorem edge_prod (M : ℕ) (f : Fin M × Fin M → ℝ) :
    (∏ e ∈ vandEdges M, f e) = ∏ i : Fin M, ∏ j ∈ Finset.Ioi i, f (i,j) := by
  classical
  unfold vandEdges
  rw [Finset.prod_filter]
  refine (Finset.prod_product Finset.univ Finset.univ
    (fun e : Fin M × Fin M => if e.1 < e.2 then f e else 1)).trans ?_
  apply Finset.prod_congr rfl
  intro i hi
  have hs : Finset.Ioi i=Finset.univ.filter (fun j : Fin M => i < j) := by ext j; simp
  rw [hs,Finset.prod_filter]

theorem pairs_subset_edges (M : ℕ) (c : ConfluentConfig M) : c.pairs ⊆ vandEdges M := by
  intro p hp
  simpa [vandEdges] using c.ordered p hp

theorem reducedVand_norm_edges (M : ℕ) (c : ConfluentConfig M) :
    ‖c.reducedVand‖ = ∏ e ∈ vandEdges M,
      if e ∈ c.pairs then 1 else ‖c.x e.1-c.x e.2‖^2 := by
  classical
  rw [edge_prod]
  simp only [ConfluentConfig.reducedVand,norm_prod]
  apply Finset.prod_congr rfl
  intro i hi
  apply Finset.prod_congr rfl
  intro j hj
  split_ifs <;> simp

theorem vandSq_norm_edges (M : ℕ) (y : Fin M → ℂ) :
    ‖MvPolynomial.eval y (vandSq M)‖ =
      ∏ e ∈ vandEdges M, ‖y e.1-y e.2‖^2 := by
  classical
  simp [vandSq_edges,edgeFactor,map_prod,norm_prod]

theorem vand_disc_majorant (M : ℕ) (c : ConfluentConfig M) (J : Finset (Fin M))
    (r δ : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) (hδ : 0 < δ)
    (hgap : ∀ i j, i ≠ j → (i ∈ J ∨ j ∈ J) → ¬c.paired i j →
      δ ≤ ‖c.x i-c.x j‖)
    (hp : ∀ i j, c.paired i j → i ∈ J ∧ j ∈ J)
    (y : Fin M → ℂ) (hy : JetDisc J c.x r y) :
    ‖MvPolynomial.eval y (vandSq M)‖ ≤
      4^c.pairCount*‖c.reducedVand‖*((1+r/δ)^(2*(M-1)))^J.card := by
  classical
  let a : Fin M → ℝ := fun i => if i ∈ J then 1+r/δ else 1
  have ha (i) : 1 ≤ a i := by
    dsimp [a]
    split
    · exact le_add_of_nonneg_right (div_nonneg hr hδ.le)
    · exact le_rfl
  have ha0 (i) : 0 ≤ a i := (by norm_num : (0:ℝ)≤1).trans (ha i)
  have hedge (e) (he : e ∈ vandEdges M) :
      ‖y e.1-y e.2‖^2 ≤
      ((if e ∈ c.pairs then 4 else 1)*(if e ∈ c.pairs then 1 else ‖c.x e.1-c.x e.2‖^2))*
        (a e.1*a e.2)^2 := by
    have hij : e.1 < e.2 := by simpa [vandEdges] using he
    by_cases hep : e ∈ c.pairs
    · have hh := hp e.1 e.2 (Or.inl hep)
      have heq : c.x e.1=c.x e.2 := (c.diagonal e.1 e.2 (ne_of_lt hij)).2 (Or.inl hep)
      have h₁ : ‖y e.1-c.x e.1‖ ≤ r := by simpa [hh.1] using hy e.1
      have h₂ : ‖y e.2-c.x e.2‖ ≤ r := by simpa [hh.2] using hy e.2
      have hn : ‖y e.1-y e.2‖ ≤ 2 := by
        have h := norm_sub_le (y e.1-c.x e.1) (y e.2-c.x e.2)
        rw [heq] at h₁
        have hsame : (y e.1-c.x e.1)-(y e.2-c.x e.2)=y e.1-y e.2 := by rw [heq]; ring
        rw [hsame,heq] at h
        linarith
      have haa : 1 ≤ a e.1*a e.2 := by nlinarith [ha e.1,ha e.2]
      simp only [hep,ite_true,one_mul,mul_one]
      nlinarith [norm_nonneg (y e.1-y e.2),sq_nonneg (a e.1*a e.2-1)]
    · have hn : ¬c.paired e.1 e.2 := by
        rintro (h|h)
        · exact hep h
        · have hji : e.2 < e.1 := by simpa using c.ordered _ h
          exact (not_lt_of_ge hij.le) hji
      have hd := disc_edge_bound M J c.x y r δ hr hδ hy e.1 e.2
        (fun h => hgap e.1 e.2 (ne_of_lt hij) h hn)
      change ‖y e.1-y e.2‖ ≤ ‖c.x e.1-c.x e.2‖*a e.1*a e.2 at hd
      simp only [hep,ite_false,one_mul]
      nlinarith [norm_nonneg (y e.1-y e.2),norm_nonneg (c.x e.1-c.x e.2),
        mul_nonneg (ha0 e.1) (ha0 e.2)]
  have hprod : (∏ e ∈ vandEdges M, if e ∈ c.pairs then (4:ℝ) else 1)=4^c.pairCount := by
    rw [← Finset.prod_filter]
    have hs : (vandEdges M).filter (fun e => e ∈ c.pairs)=c.pairs := by
      ext e
      simp only [Finset.mem_filter]
      exact ⟨fun h => h.2,fun h => ⟨pairs_subset_edges M c h,h⟩⟩
    rw [hs,Finset.prod_const]
    rfl
  have haprod : (∏ e ∈ vandEdges M, (a e.1*a e.2)^2)=
      ((1+r/δ)^(2*(M-1)))^J.card := by
    rw [edge_prod,complete_edge_product]
    simp only [a,ite_pow,one_pow]
    rw [← Finset.prod_filter]
    simp
  rw [vandSq_norm_edges]
  calc
    _ ≤ ∏ e ∈ vandEdges M,
        ((if e ∈ c.pairs then 4 else 1)*(if e ∈ c.pairs then 1 else ‖c.x e.1-c.x e.2‖^2))*
          (a e.1*a e.2)^2 := Finset.prod_le_prod₀ (fun _ _ => sq_nonneg _) hedge
    _ = _ := by
      simp_rw [Finset.prod_mul_distrib]
      rw [hprod,← reducedVand_norm_edges,haprod]

theorem edge_factor_square (M : ℕ) (hM : 0 < M) (t : ℝ) (ht : 0 ≤ t)
    (ht' : t ≤ (2*(M:ℝ))⁻¹) :
    2*((1+t)^(2*(M-1)))^2 ≤ ((M:ℝ)+1)^2 := by
  have hb : 0 ≤ 1+t := by positivity
  have hsmall := pow_le_pow_left₀ hb (add_le_add (le_refl (1:ℝ)) ht') (2*(M-1))
  have hsquare := pow_le_pow_left₀ (pow_nonneg hb (2*(M-1))) hsmall 2
  by_cases hm : M < 4
  · interval_cases M <;> norm_num at hM ⊢
    all_goals norm_num at hsquare
    all_goals nlinarith only [hsquare]
  · have hfour : 4 ≤ M := by omega
    have hpow := pow_le_pow_right₀
      (show (1:ℝ) ≤ 1+(2*(M:ℝ))⁻¹ from
        le_add_of_nonneg_right (inv_nonneg.mpr (by positivity)))
      (show 2*(M-1) ≤ 2*M by omega)
    have hexp := Real.one_add_inv_pow_le_exp (n:=2*M)
    have he : (1+t)^(2*(M-1)) ≤ Real.exp 1 := by
      apply hsmall.trans
      apply hpow.trans
      simpa only [Nat.cast_mul,Nat.cast_ofNat] using hexp
    have hlt := he.trans_lt Real.exp_one_lt_three
    have hcast : (4:ℝ) ≤ (M:ℝ) := by exact_mod_cast hfour
    have hpos := pow_nonneg hb (2*(M-1))
    nlinarith

theorem absorb_pairs (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h : 2*A^2 ≤ B^2) (p k : ℕ) (hpk : 2*p ≤ k) :
    A^k*2^p ≤ B^k := by
  have hpow : (2:ℝ)^(2*p) ≤ 2^k := pow_le_pow_right₀ (by norm_num) hpk
  have hsq : (A^k*2^p)^2 ≤ (B^k)^2 := by
    calc
      _ = (A^2)^k*2^(2*p) := by
        rw [mul_pow,← pow_mul,← pow_mul,← pow_mul]
        congr 1 <;> congr 1 <;> omega
      _ ≤ (A^2)^k*2^k := mul_le_mul_of_nonneg_left hpow (pow_nonneg (sq_nonneg A) k)
      _ = (2*A^2)^k := by rw [mul_pow]; ring
      _ ≤ (B^2)^k := pow_le_pow_left₀ (by positivity) h k
      _ = (B^k)^2 := by rw [← pow_mul,← pow_mul]; congr 1; omega
  nlinarith [pow_nonneg hA k,pow_nonneg hB k,pow_nonneg (by norm_num : (0:ℝ)≤2) p]
theorem configuration_bound_radius (M : ℕ) (hM : 0 < M) (c : ConfluentConfig M)
    (J : Finset (Fin M)) (a b : Fin M → ℂ) (δ R r : ℝ)
    (hδ : 0 < δ) (hR : 0 ≤ R) (hr : 0 < r) (hr1 : r ≤ 1)
    (hrt : r/δ ≤ (2*(M:ℝ))⁻¹) (hri : 1/r ≤ 1+2*(M:ℝ)/δ)
    (hgap : ∀ i j, i ≠ j → (i ∈ J ∨ j ∈ J) → ¬c.paired i j → δ ≤ ‖c.x i-c.x j‖)
    (ha : ∀ i ∈ J, ‖a i‖ ≤ R*‖b i‖)
    (hp : ∀ i j, c.paired i j → i ∈ J ∧ j ∈ J) :
    ‖mixedJet J a b c.x (vandSq M)‖ ≤
      ((1+(M:ℝ))*(1+R+2*M/δ))^J.card*2^c.pairCount*
        (∏ i ∈ J, ‖b i‖)*‖c.reducedVand‖ := by
  classical
  let A := (1+r/δ)^(2*(M-1))
  let K := R+1/r
  let L := 1+R+2*(M:ℝ)/δ
  let C := 4^c.pairCount*‖c.reducedVand‖*A^J.card
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hKL : K ≤ L := by dsimp [K,L]; linarith
  have hAsq : 2*A^2 ≤ ((M:ℝ)+1)^2 := edge_factor_square M hM (r/δ)
    (div_nonneg hr.le hδ.le) hrt
  have hAbs := absorb_pairs A ((M:ℝ)+1) hA (by positivity) hAsq c.pairCount J.card
    (confluent_pair_card M c J hp)
  have hprod : (∏ i ∈ J, (‖a i‖+‖b i‖/r)) ≤ K^J.card*(∏ i ∈ J, ‖b i‖) := by
    calc
      _ ≤ ∏ i ∈ J, K*‖b i‖ := by
        apply Finset.prod_le_prod₀ (fun i hi => by positivity)
        intro i hi
        calc
          _ ≤ R*‖b i‖+‖b i‖/r := add_le_add (ha i hi) le_rfl
          _ = K*‖b i‖ := by dsimp [K]; ring
      _ = _ := by rw [Finset.prod_mul_distrib,Finset.prod_const]
  have hc : ‖mixedJet J a b c.x (vandSq M)‖ ≤ C*(∏ i ∈ J, (‖a i‖+‖b i‖/r)) := by
    apply mixedJet_cauchy_bound M J a b (vandSq M) r hr C c.x
    intro y hy
    exact vand_disc_majorant M c J r δ hr.le hr1 hδ hgap hp y hy
  calc
    _ ≤ C*(K^J.card*(∏ i ∈ J, ‖b i‖)) :=
      hc.trans (mul_le_mul_of_nonneg_left hprod hC)
    _ = (A^J.card*2^c.pairCount)*K^J.card*
        (2^c.pairCount*(∏ i ∈ J, ‖b i‖)*‖c.reducedVand‖) := by
      dsimp [C]
      have hfour : (4:ℝ)^c.pairCount=2^c.pairCount*2^c.pairCount := by
        rw [← mul_pow]; norm_num
      rw [hfour]; ring
    _ ≤ ((M:ℝ)+1)^J.card*L^J.card*
        (2^c.pairCount*(∏ i ∈ J, ‖b i‖)*‖c.reducedVand‖) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul hAbs (pow_le_pow_left₀ hK hKL J.card)
        (pow_nonneg hK J.card) (pow_nonneg (by positivity) J.card)
    _ = _ := by dsimp [L]; rw [← mul_pow]; ring

theorem jet_configuration_bound (M : ℕ) (c : ConfluentConfig M)
    (Jlat : Finset (Fin M)) (a b : Fin M → ℂ) (δ R : ℝ)
    (hδ : 0 < δ) (hR : 0 ≤ R)
    (hgap : ∀ i j, i ≠ j → (i ∈ Jlat ∨ j ∈ Jlat) → ¬c.paired i j → δ ≤ ‖c.x i-c.x j‖)
    (ha : ∀ i ∈ Jlat, ‖a i‖ ≤ R*‖b i‖)
    (hp : ∀ i j, c.paired i j → i ∈ Jlat ∧ j ∈ Jlat ∧ b i=b j) :
    ‖mixedJet Jlat a b c.x (vandSq M)‖ ≤
      ((1+(M:ℝ))*(1+R+2*M/δ))^Jlat.card*2^c.pairCount*
        (∏ i ∈ Jlat, ‖b i‖)*‖c.reducedVand‖ := by
  classical
  by_cases hM : M=0
  · subst M
    have hJ : Jlat=∅ := Finset.eq_empty_iff_forall_notMem.mpr (fun i _ => Fin.elim0 i)
    have hP : c.pairs=∅ := Finset.eq_empty_iff_forall_notMem.mpr (fun e _ => Fin.elim0 e.1)
    simp [hJ,hP,mixedJet,partials,vandSq,ConfluentConfig.pairCount,ConfluentConfig.reducedVand]
  · have hMpos : 0 < M := Nat.pos_of_ne_zero hM
    have hMR : (0:ℝ)<2*(M:ℝ) := by positivity
    let r := min 1 (δ/(2*(M:ℝ)))
    have hr : 0 < r := lt_min zero_lt_one (div_pos hδ hMR)
    have hr1 : r ≤ 1 := min_le_left _ _
    have hrδ : r ≤ δ/(2*(M:ℝ)) := min_le_right _ _
    have hrt : r/δ ≤ (2*(M:ℝ))⁻¹ := by
      apply (div_le_iff₀ hδ).2
      calc
        r ≤ δ/(2*(M:ℝ)) := hrδ
        _ = _ := by ring
    have hri : 1/r ≤ 1+2*(M:ℝ)/δ := by
      by_cases h : 1 ≤ δ/(2*(M:ℝ))
      · rw [show r=1 from min_eq_left h]
        simp only [div_one]
        linarith [div_nonneg hMR.le hδ.le]
      · rw [show r=δ/(2*(M:ℝ)) from min_eq_right (le_of_not_ge h)]
        have heq : 1/(δ/(2*(M:ℝ)))=2*(M:ℝ)/δ := by field_simp
        rw [heq]
        linarith
    exact configuration_bound_radius M hMpos c Jlat a b δ R r hδ hR hr hr1 hrt hri
      hgap ha (fun i j h => ⟨(hp i j h).1,(hp i j h).2.1⟩)

#print axioms jet_configuration_bound
end CatalanCore.Tools.Jets
