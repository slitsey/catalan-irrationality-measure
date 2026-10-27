module
public import CatalanMeasure.GenD.Uniform.Prefix.RawResponseWindow
public import CatalanMeasure.GenD.Uniform.Prefix.RawResponseStep
@[expose] public section
set_option Elab.async false
set_option profiler true
namespace CatalanMeasure.GenD.Uniform.Prefix
open Polynomial Finset
noncomputable section
variable {p : ℕ} [Fact p.Prime]
local notation "Fp" => ZMod p

def sourcePstepPolynomial {ι : Type*} [Fintype ι] (H ah q J : ℕ) (S : ℤ)
    (a b F E : ι→Fp[X]) : Fp[X] :=
  ∑ t, (C (pstepCovector q (fun j s => sourcePsi H ah j s (a t) (b t)) J S)*F t+
    C (pstepCovector q (fun j s => sourcePsi H ah j s (a t) (b t)) J (S-1)-
      pstepCovector q (fun j s => sourcePsi H ah j s (a t) (b t)) J S)*E t)

/-- Actual p-step-compressed intrinsic responses are EXACTLY the observed
coefficient windows of a constant F/E covector minus the unique B prefix. -/
theorem pstep_source_covector_window {ι : Type*} [Fintype ι]
    (H ah q J ell : ℕ) (hell : ell<H) (a b F E : ι→Fp[X])
    (hF : ∀t,(F t).degree<p) (hE : ∀t,(E t).degree<p) (B : Fp[X]) :
    (sourcePstepPolynomial H ah q J (((H-1-ell)/p:ℕ):ℤ) a b F E-
      residuePolynomial (((H-1)%p:ℕ):Fp) B).coeff ((H-1-ell)%p)=
    (∑ k∈range (q+1),(-1:Fp)^(q-k)*(q.choose k:Fp)*
      (∑ t,intrinsicResponse H (J+k) ell
        (((a t)*(X-1)^ah).comp (X^p)*(F t+(X^p-1)*E t))
        (((b t)*(X-1)^ah).comp (X^p)*(F t+(X^p-1)*E t))))-B.eval (ell:Fp) := by
  rw [coeff_sub,coeff_residuePolynomial,if_pos (Nat.mod_lt _ (Fact.out:p.Prime).pos)]
  have he := intrinsic_residue_eta H p ell hell
  have he' : (((H-1)%p:ℕ):Fp)-(((H-1-ell)%p:ℕ):Fp)=(ell:Fp) := by rw [he];ring
  rw [he']
  congr 1
  simp only [sourcePstepPolynomial,finsetSum_coeff,coeff_add,coeff_C_mul]
  have ht (t : ι) :
      pstepCovector q (fun j s => sourcePsi H ah j s (a t) (b t)) J (((H-1-ell)/p:ℕ):ℤ)*
          (F t).coeff ((H-1-ell)%p)+
      (pstepCovector q (fun j s => sourcePsi H ah j s (a t) (b t)) J ((((H-1-ell)/p:ℕ):ℤ)-1)-
        pstepCovector q (fun j s => sourcePsi H ah j s (a t) (b t)) J (((H-1-ell)/p:ℕ):ℤ))*
          (E t).coeff ((H-1-ell)%p)=
      ∑ k∈range (q+1),(-1:Fp)^(q-k)*(q.choose k:Fp)*intrinsicResponse H (J+k) ell
        (((a t)*(X-1)^ah).comp (X^p)*(F t+(X^p-1)*E t))
        (((b t)*(X-1)^ah).comp (X^p)*(F t+(X^p-1)*E t)) := by
    rw [←pstep_response_contraction]
    exact Finset.sum_congr rfl (fun k _ => by
      rw [intrinsicResponse_normalized H ah (J+k) ell hell _ _ _ _ (hF t) (hE t)])
  simp_rw [ht]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun k _ => by rw [Finset.mul_sum])

#print axioms pstep_source_covector_window
end
end CatalanMeasure.GenD.Uniform.Prefix

