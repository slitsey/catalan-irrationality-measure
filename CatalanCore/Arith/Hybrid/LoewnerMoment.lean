module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Tactic

@[expose] public section
open Finset Matrix
namespace CatalanCore.Arith.Hybrid

/-- The second-order pole contraction is determined by four scalar moments. -/
theorem difference_moment_sum {K ι : Type*} [CommRing K] [Fintype ι]
    (v f t : ι→K) :
    (∑i,∑j,v i*v j*(f i-f j)*(t j-t i))=
      2*((∑i,v i*f i)*(∑i,v i*t i)-(∑i,v i)*(∑i,v i*f i*t i)) := by
  have he (i j) : v i*v j*(f i-f j)*(t j-t i)=
      (v i*f i)*(v j*t j)-(v i*f i*t i)*v j-
        v i*(v j*f j*t j)+(v i*t i)*(v j*f j) := by ring
  simp_rw [he]
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,←Finset.mul_sum,←Finset.sum_mul]
  ring

/-- A commutator identity and the source equation determine the local moment
which cancels the completed long-arc term. No rank conclusion is assumed. -/
theorem cleared_loewner_source_moment {K ι : Type*} [CommRing K] [Fintype ι]
    (Q : Matrix ι ι K) (g b f t : ι → K) (n l H : K)
    (hsolve : ∀i, ∑j,Q i j*g j=H*b i)
    (hcomm : ∀i j,n*(t i-t j)*Q i j=f j-f i)
    (hsource : ∀i,n*t i*b i=l-f i) :
    let A := H*l-∑i,g i*f i
    let B := H-∑i,g i
    let u := fun i=>A-B*f i
    (∀i, ∑j,Q i j*(n*t j*g j)=u i) ∧
      (∑i,u i*(n*t i*g i)) =
        n*((H-∑i,g i)*(-∑i,t i*f i*g i)-
          (H*l-∑i,g i*f i)*(-∑i,t i*g i)) := by
  dsimp only
  constructor
  · intro i
    have he (j) : Q i j*(n*t j*g j)=n*t i*(Q i j*g j)+(f i-f j)*g j := by
      linear_combination -(g j)*(hcomm i j)
    simp_rw [he]
    rw [sum_add_distrib,←mul_sum,hsolve,
      show n*t i*(H*b i)=H*(n*t i*b i) by ring,hsource]
    simp only [sub_mul,sum_sub_distrib,←mul_sum]
    have hs : (∑x,f x*g x)=∑x,g x*f x := by apply sum_congr rfl;intro x hx;ring
    rw [hs]
    ring
  · let A := H*l-∑i,g i*f i
    let B := H-∑i,g i
    change (∑i,(A-B*f i)*(n*t i*g i))=
      n*(B*(-∑i,t i*f i*g i)-A*(-∑i,t i*g i))
    have he (i) : (A-B*f i)*(n*t i*g i)=
        (n*A)*(t i*g i)-(n*B)*(t i*f i*g i) := by ring
    simp_rw [he]
    rw [sum_sub_distrib,←mul_sum,←mul_sum]
    ring

/-- The field version is a specialization of the denominator-free identity. -/
theorem loewner_source_moment {K ι : Type*} [Field K] [Fintype ι]
    (Q : Matrix ι ι K) (g b f t : ι → K) (n l : K)
    (hsolve : ∀i, ∑j,Q i j*g j=b i)
    (hcomm : ∀i j,n*(t i-t j)*Q i j=f j-f i)
    (hsource : ∀i,n*t i*b i=l-f i) :
    let A := l-∑i,g i*f i
    let B := 1-∑i,g i
    let u := fun i=>A-B*f i
    (∀i, ∑j,Q i j*(n*t j*g j)=u i) ∧
      (∑i,u i*(n*t i*g i)) =
        n*((1-∑i,g i)*(-∑i,t i*f i*g i)-
          (l-∑i,g i*f i)*(-∑i,t i*g i)) := by
  simpa only [one_mul] using
    cleared_loewner_source_moment Q g b f t n l 1 (by simpa using hsolve) hcomm hsource

/-- The appended source coordinate is already predicted by the cleared solution. -/
theorem cleared_loewner_source_extra {K ι : Type*} [CommRing K] [Fintype ι]
    (g b f t : ι→K) (n l H : K) (hsource : ∀i,n*t i*b i=l-f i) :
    (∑i,b i*(n*t i*g i))=
      (H*l-∑i,g i*f i)-(H-∑i,g i)*l := by
  have he (i) : b i*(n*t i*g i)=(l-f i)*g i := by
    linear_combination (g i)*(hsource i)
  simp_rw [he]
  simp only [sub_mul,sum_sub_distrib,←mul_sum]
  have hs : (∑i,f i*g i)=∑i,g i*f i := by apply sum_congr rfl;intro i hi;ring
  rw [hs]
  ring

theorem loewner_source_extra {K ι : Type*} [Field K] [Fintype ι]
    (g b f t : ι→K) (n l : K) (hsource : ∀i,n*t i*b i=l-f i) :
    (∑i,b i*(n*t i*g i))=
      (l-∑i,g i*f i)-(1-∑i,g i)*l := by
  simpa only [one_mul] using cleared_loewner_source_extra g b f t n l 1 hsource

/-- Appending a coordinate predicted by the old solution preserves the response. -/
theorem bordered_response_zero {K ι : Type*} [CommRing K] [Fintype ι]
    (Q : Matrix ι ι K) (b u v : ι→K) (d s : K)
    (hv : ∀i,∑j,Q i j*v j=u i) (hs : ∑i,b i*v i=s) :
    let Q' : Matrix (ι⊕Unit) (ι⊕Unit) K := fun i j=>match i,j with
      | Sum.inl a,Sum.inl c=>Q a c
      | Sum.inl a,Sum.inr _=>b a
      | Sum.inr _,Sum.inl c=>b c
      | Sum.inr _,Sum.inr _=>d
    let v' : ι⊕Unit→K:=Sum.elim v (fun _=>0)
    let u' : ι⊕Unit→K:=Sum.elim u (fun _=>s)
    (∀i,∑j,Q' i j*v' j=u' i) ∧ (∑i,u' i*v' i)=∑i,u i*v i := by
  dsimp only
  constructor
  · intro i
    cases i with
    | inl i=>simpa only [Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,
        mul_zero,Finset.sum_const_zero,add_zero] using hv i
    | inr i=>simpa only [Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,
        mul_zero,Finset.sum_const_zero,add_zero] using hs
  · simp only [Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,mul_zero,
      Finset.sum_const_zero,add_zero]

#print axioms loewner_source_moment
#print axioms loewner_source_extra
#print axioms bordered_response_zero
end CatalanCore.Arith.Hybrid
