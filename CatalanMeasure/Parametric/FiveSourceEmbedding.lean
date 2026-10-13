module
public import CatalanMeasure.Parametric.KernelEmbeddingRank
@[expose] public section
namespace CatalanMeasure.Parametric
open Matrix
open scoped BigOperators
noncomputable section

def fiveSourceVector {K : Type*} [Field K] {g n : ℕ}
    (t s2 s1p s1m s0p s0m : Fin g → Fin n) (a b : K) (d : Fin g) : Fin n → K :=
  Pi.single (t d) 1-Pi.single (s2 d) 1-
    a • (Pi.single (s1p d) 1-Pi.single (s1m d) 1)+
    b • (Pi.single (s0p d) 1-Pi.single (s0m d) 1)

def fiveSourceEmbedding {K : Type*} [Field K] {g n : ℕ}
    (t s2 s1p s1m s0p s0m : Fin g → Fin n) (a b : K) :
    (Fin g → K) →ₗ[K] (Fin n → K) where
  toFun c :=∑ d,c d • fiveSourceVector t s2 s1p s1m s0p s0m a b d
  map_add' c c' :=by simp [Pi.add_apply,add_smul,Finset.sum_add_distrib]
  map_smul' k c :=by simp [Pi.smul_apply,smul_smul,Finset.smul_sum]

theorem fiveSourceEmbedding_apply {K : Type*} [Field K] {g n : ℕ}
    (t s2 s1p s1m s0p s0m : Fin g → Fin n) (a b : K) (c : Fin g → K) :
    fiveSourceEmbedding t s2 s1p s1m s0p s0m a b c=
      ∑ d,c d • fiveSourceVector t s2 s1p s1m s0p s0m a b d :=rfl

theorem fiveSourceEmbedding_projection {K : Type*} [Field K] {g n : ℕ}
    (t s2 s1p s1m s0p s0m : Fin g → Fin n) (a b : K)
    (ht : Function.Injective t)
    (hs : ∀ d e,t d≠s2 e ∧ t d≠s1p e ∧ t d≠s1m e ∧ t d≠s0p e ∧ t d≠s0m e)
    (c : Fin g → K) (d : Fin g) :
    fiveSourceEmbedding t s2 s1p s1m s0p s0m a b c (t d)=c d :=by
  classical
  have hvector (e : Fin g) : fiveSourceVector t s2 s1p s1m s0p s0m a b e (t d)=
      if d=e then 1 else 0 :=by
    have hh :=hs d e
    simp [fiveSourceVector,Pi.single_apply,hh.1,hh.2.1,hh.2.2.1,hh.2.2.2.1,hh.2.2.2.2,ht.eq_iff]
  rw [fiveSourceEmbedding_apply]
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,hvector]
  simp [mul_ite]

theorem fiveSourceEmbedding_injective {K : Type*} [Field K] {g n : ℕ}
    (t s2 s1p s1m s0p s0m : Fin g → Fin n) (a b : K)
    (ht : Function.Injective t)
    (hs : ∀ d e,t d≠s2 e ∧ t d≠s1p e ∧ t d≠s1m e ∧ t d≠s0p e ∧ t d≠s0m e) :
    Function.Injective (fiveSourceEmbedding t s2 s1p s1m s0p s0m a b) :=by
  intro c c' heq
  funext d
  have hh :=congrFun heq (t d)
  simpa only [fiveSourceEmbedding_projection t s2 s1p s1m s0p s0m a b ht hs] using hh

theorem fiveSourceEmbedding_mulVec {K : Type*} [Field K] {g n : ℕ}
    (R : Matrix (Fin n) (Fin n) K) (t s2 s1p s1m s0p s0m : Fin g → Fin n)
    (a b : K) (c : Fin g → K) (j : Fin n) :
    R.transpose.mulVecLin (fiveSourceEmbedding t s2 s1p s1m s0p s0m a b c) j=
      ∑ d,c d*(R (t d) j-R (s2 d) j-a*(R (s1p d) j-R (s1m d) j)+
        b*(R (s0p d) j-R (s0m d) j)) :=by
  rw [fiveSourceEmbedding_apply]
  simp [fiveSourceVector,map_sum,map_smul,Matrix.mulVecLin_apply,Matrix.mulVec_single_one,
    Matrix.mulVec_sub,Matrix.mulVec_add,Matrix.mulVec_smul]
  apply Finset.sum_congr rfl
  intro d hd
  ring

theorem weighted_sum_relation_zero {K : Type*} [Field K] {g : ℕ}
    (A B C : Fin g → K) (c : Fin g → K) (a b : K)
    (h : (∑ d,c d*A d)=a*(∑ d,c d*B d)-b*(∑ d,c d*C d)) :
    (∑ d,c d*(A d-a*B d+b*C d))=0 :=by
  have he : (∑ d,c d*(A d-a*B d+b*C d))=
      (∑ d,c d*A d)-a*(∑ d,c d*B d)+b*(∑ d,c d*C d) :=by
    rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_sub_distrib,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    ring
  rw [he,h]
  ring

end
end CatalanMeasure.Parametric
