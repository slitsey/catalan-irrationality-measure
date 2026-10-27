module
public import CatalanCore.Rect.CharZeroNV.Barycentric

@[expose] public section
/-! Exact Hermite pair equations on arbitrary finite node sets. -/
open Polynomial Finset Matrix
open CatalanCore.Arith.Hybrid.FiniteFieldCorank
namespace CatalanCore.Uniform.NV
variable {K : Type*} [Field K] [DecidableEq K]
open CatalanCore.Rect.CharZeroNV

structure Hermite (Z C : Finset K) (f tau : K → K) (p q : K[X]) : Prop where
  value : ∀ x ∈ Z, q.eval x = f x * p.eval x
  jet : ∀ x ∈ C, q.derivative.eval x = f x * p.derivative.eval x + tau x * p.eval x

noncomputable def pairSpace (Z C : Finset K) (f tau : K → K) (d : ℕ) :
    Submodule K (K[X] × K[X]) where
  carrier := {v | v.1.natDegree ≤ d ∧ v.2.natDegree ≤ d ∧ Hermite Z C f tau v.1 v.2}
  zero_mem' := by simp; exact ⟨by intros; simp, by intros; simp⟩
  add_mem' := by
    rintro v w ⟨hpv, hqv, hv⟩ ⟨hpw, hqw, hw⟩
    refine ⟨(natDegree_add_le _ _).trans (max_le hpv hpw),
      (natDegree_add_le _ _).trans (max_le hqv hqw), ?_, ?_⟩
    · intro x hx
      simp only [Prod.fst_add, Prod.snd_add, eval_add, hv.value x hx, hw.value x hx]
      ring
    · intro x hx
      simp only [Prod.fst_add, Prod.snd_add, derivative_add, eval_add, hv.jet x hx, hw.jet x hx]
      ring
  smul_mem' := by
    rintro c v ⟨hp, hq, hv⟩
    refine ⟨(natDegree_smul_le _ _).trans hp, (natDegree_smul_le _ _).trans hq, ?_, ?_⟩
    · intro x hx
      change (c • v.2).eval x = f x * (c • v.1).eval x
      simp only [eval_smul, smul_eq_mul, hv.value x hx]
      ring
    · intro x hx
      change (c • v.2).derivative.eval x =
        f x * (c • v.1).derivative.eval x + tau x * (c • v.1).eval x
      simp only [derivative_smul, eval_smul, smul_eq_mul, hv.jet x hx]
      ring

/-- The actual value and jet equations force rational rank one. -/
theorem cross_product_eq_zero (Z C : Finset K) (hCZ : C ⊆ Z)
    (f tau : K → K) (d : ℕ) (hsize : 2*d < Z.card+C.card)
    (p q p' q' : K[X])
    (hp : p.natDegree ≤ d) (hq : q.natDegree ≤ d)
    (hp' : p'.natDegree ≤ d) (hq' : q'.natDegree ≤ d)
    (h : Hermite Z C f tau p q) (h' : Hermite Z C f tau p' q') :
    q*p' - q'*p = 0 := by
  apply eq_zero_of_hermite_roots Z C hCZ
  · intro x hx
    simp only [eval_sub, eval_mul, h.value x hx, h'.value x hx]
    ring
  · intro x hx
    simp only [derivative_sub, derivative_mul, eval_sub, eval_add, eval_mul,
      h.value x (hCZ hx), h'.value x (hCZ hx), h.jet x hx, h'.jet x hx]
    ring
  · have hd1 := natDegree_mul_le (p := q) (q := p')
    have hd2 := natDegree_mul_le (p := q') (q := p)
    have hd := natDegree_sub_le (q*p') (q'*p)
    omega

noncomputable def pairP (Z C : Finset K) (f tau : K → K) (d : ℕ) :
    pairSpace Z C f tau d →ₗ[K] K[X] :=
  (LinearMap.fst K K[X] K[X]).comp (pairSpace Z C f tau d).subtype

theorem pairP_injective (Z C : Finset K) (f tau : K → K) (d : ℕ) (hd : d < Z.card) :
    Function.Injective (pairP Z C f tau d) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro v hv
  have hp : v.val.1 = 0 := hv
  have hq : v.val.2 = 0 := by
    apply eq_zero_of_hermite_roots Z ∅ (by simp)
    · intro x hx
      simpa [hp] using v.property.2.2.value x hx
    · simp
    · simpa only [card_empty, add_zero] using v.property.2.1.trans_lt hd
  exact Subtype.ext (Prod.ext hp hq)

/-- Symmetric divided difference with its actual common-node jet. -/
noncomputable def loewnerEntry (f tau : K → K) (a b : K) : K :=
  if a = b then tau a else (f a-f b)/(a-b)
lemma loewnerEntry_symm (f tau : K → K) (a b : K) :
    loewnerEntry f tau a b = loewnerEntry f tau b a := by
  unfold loewnerEntry
  by_cases h : a = b
  · subst b;simp
  · rw [ite_eq_right h,ite_eq_right (Ne.symm h)]
    field_simp
    ring
/-- Actual rectangular Loewner matrix on arbitrary distinct field nodes. -/
noncomputable def loewner (R Q : Finset K) (f tau : K → K) : Matrix R Q K :=
  fun a b => loewnerEntry f tau a.val b.val
noncomputable def weights (Q : Finset K) (v : Q → K) (x : K) : K :=
  if hx : x ∈ Q then v ⟨x,hx⟩ else 0
@[simp] lemma weights_mem (Q : Finset K) (v : Q → K) (x : Q) : weights Q v x.val = v x := by
  simp [weights]

theorem row_eq_mulVec (R Q : Finset K) (f tau : K → K) (v : Q → K) (a : R) :
    loewnerRow Q f tau (weights Q v) a.val = (loewner R Q f tau *ᵥ v) a := by
  calc
    _ = ∑ b : Q, loewnerEntry f tau a.val b.val * weights Q v b.val :=
      (Finset.sum_coe_sort Q (fun b : K => loewnerEntry f tau a.val b * weights Q v b)).symm
    _ = _ := by simp [loewner,Matrix.mulVec,dotProduct]

theorem kernel_hermite (R Q : Finset K) (f tau : K → K)
    (v : Q → K) (hv : loewner R Q f tau *ᵥ v = 0) :
    Hermite (R ∪ Q) (R ∩ Q) f tau
      (numerator Q (weights Q v)) (numerator Q (fun b => weights Q v b * f b)) where
  value x hx := by
    by_cases hb : x ∈ Q
    · exact kernel_value_inside Q f (weights Q v) x hb
    · have ha : x ∈ R := (mem_union.mp hx).resolve_right hb
      apply kernel_value_outside Q f tau (weights Q v) x hb
      rw [row_eq_mulVec R Q f tau v ⟨x,ha⟩,hv]
      rfl
  jet x hx := by
    have ha := mem_inter.mp hx
    apply kernel_jet Q f tau (weights Q v) x ha.2
    rw [row_eq_mulVec R Q f tau v ⟨x,ha.1⟩,hv]
    rfl

noncomputable def coords (Q : Finset K) (p : K[X]) : Q → K :=
  fun b => p.eval b.val / (punctured Q b.val).eval b.val

/-- Exact recovery, including kernel vectors with zero coordinates. -/
theorem recover_kernel (Q : Finset K) (v : Q → K) :
    coords Q (numerator Q (weights Q v)) = v := by
  funext b
  change (numerator Q (weights Q v)).eval b.val / _ = v b
  rw [eval_numerator_punctured Q _ b.property, weights_mem]
  exact mul_div_cancel_right₀ _ (punctured_eval_ne_zero _ _)

/-- Every Hermite pair of the correct degree gives an actual right kernel vector. -/
theorem pair_gives_kernel (R Q : Finset K) (hQ : 1 ≤ Q.card) (f tau : K → K)
    (p q : K[X]) (hp : p.natDegree ≤ Q.card-1) (hq : q.natDegree ≤ Q.card-1)
    (h : Hermite (R ∪ Q) (R ∩ Q) f tau p q) :
    loewner R Q f tau *ᵥ coords Q p = 0 := by
  funext a
  change (loewner R Q f tau *ᵥ coords Q p) a = 0
  rw [← row_eq_mulVec]
  have he : loewnerRow Q f tau (weights Q (coords Q p)) a.val =
      loewnerRow Q f tau (fun b => p.eval b / (punctured Q b).eval b) a.val := by
    unfold loewnerRow
    apply Finset.sum_congr rfl
    intro b hb
    simp [weights,coords,hb]
  rw [he]
  apply pair_gives_kernel_row Q hQ f tau p q hp hq
  · intro b hb
    exact h.value b (mem_union.mpr (Or.inr hb))
  · exact h.value a.val (mem_union.mpr (Or.inl a.property))
  · intro hb
    exact h.jet a.val (mem_inter.mpr ⟨a.property,hb⟩)
end CatalanCore.Uniform.NV


