module
public import CatalanArchive.CatalanMeasure.Parametric.RowDivisibility
@[expose] public section
namespace CatalanMeasure.Parametric
open Matrix Finset OAI.InternalCatalan
open scoped BigOperators
noncomputable section

def fiveSourceTransform {n : ℕ} (S : Finset (Fin n))
    (s2 s1p s1m s0p s0m : Fin n → Fin n) (a b : ℚ) : Matrix (Fin n) (Fin n) ℚ :=
  Matrix.of fun i j =>
    let delta (r : Fin n) : ℚ :=if j=r then 1 else 0
    if i∈S then delta i-delta (s2 i)-a*(delta (s1p i)-delta (s1m i))+
      b*(delta (s0p i)-delta (s0m i)) else delta i

theorem fiveSourceTransform_det {n : ℕ} (S : Finset (Fin n))
    (s2 s1p s1m s0p s0m : Fin n → Fin n) (a b : ℚ)
    (hs : ∀ i ∈ S,s2 i< i ∧ s1p i< i ∧ s1m i< i ∧ s0p i< i ∧ s0m i< i) :
    (fiveSourceTransform S s2 s1p s1m s0p s0m a b).det=1 := by
  classical
  have htri : (fiveSourceTransform S s2 s1p s1m s0p s0m a b).IsLowerTriangular :=by
    intro i j hij
    change i<j at hij
    simp only [fiveSourceTransform,Matrix.of_apply]
    by_cases hi : i∈S
    · have hh :=hs i hi
      have hji : j≠i :=ne_of_gt hij
      have h2 : j≠s2 i :=by order
      have h1p : j≠s1p i :=by order
      have h1m : j≠s1m i :=by order
      have h0p : j≠s0p i :=by order
      have h0m : j≠s0m i :=by order
      simp [hi,hji,h2,h1p,h1m,h0p,h0m]
    · simp [hi,ne_of_gt hij]
  rw [Matrix.det_of_isLowerTriangular _ htri]
  have hdiag (i : Fin n) : fiveSourceTransform S s2 s1p s1m s0p s0m a b i i=1 :=by
    simp only [fiveSourceTransform,Matrix.of_apply]
    by_cases hi : i∈S
    · have hh :=hs i hi
      simp [hi,ne_of_gt hh.1,ne_of_gt hh.2.1,ne_of_gt hh.2.2.1,
        ne_of_gt hh.2.2.2.1,ne_of_gt hh.2.2.2.2]
    · simp [hi]
  simp [hdiag]

theorem fiveSourceTransform_mul {n : ℕ} (S : Finset (Fin n))
    (s2 s1p s1m s0p s0m : Fin n → Fin n) (a b : ℚ)
    (Q : Matrix (Fin n) (Fin n) ℚ) (i j : Fin n) :
    (fiveSourceTransform S s2 s1p s1m s0p s0m a b*Q) i j=
      if i∈S then Q i j-Q (s2 i) j-a*(Q (s1p i) j-Q (s1m i) j)+
        b*(Q (s0p i) j-Q (s0m i) j) else Q i j := by
  classical
  rw [Matrix.mul_apply]
  simp only [fiveSourceTransform,Matrix.of_apply]
  by_cases hi : i∈S
  · simp only [ite_eq_left hi]
    simp_rw [add_mul,sub_mul,mul_assoc,mul_sub]
    simp [Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum,ite_mul]
    simp_rw [sub_mul,Finset.sum_sub_distrib]
    simp [ite_mul]
    ring
  · simp [hi,ite_mul]

theorem fiveSource_elimination_valuation {p n : ℕ} [hp : Fact p.Prime]
    (M : Matrix (Fin n) (Fin n) ℚ) (S : Finset (Fin n))
    (s2 s1p s1m s0p s0m : Fin n → Fin n) (a b : ℚ)
    (hs : ∀ i ∈ S,s2 i< i ∧ s1p i< i ∧ s1m i< i ∧ s0p i< i ∧ s0m i< i)
    (ha : (a.den : ZMod p)≠0) (hb : (b.den : ZMod p)≠0)
    (hM : ∀ i j,(((p:ℚ)^2*M i j).den : ZMod p)≠0)
    (hrel : ∀ i ∈ S,∀ j,
      palindromicRatResidue p ((p:ℚ)^2*M i j)-palindromicRatResidue p ((p:ℚ)^2*M (s2 i) j)=
      palindromicRatResidue p a*(palindromicRatResidue p ((p:ℚ)^2*M (s1p i) j)-
        palindromicRatResidue p ((p:ℚ)^2*M (s1m i) j))-
      palindromicRatResidue p b*(palindromicRatResidue p ((p:ℚ)^2*M (s0p i) j)-
        palindromicRatResidue p ((p:ℚ)^2*M (s0m i) j))) :
    -((2*n-S.card:ℕ):ℤ) ≤ padicValRat p M.det := by
  let T :=fiveSourceTransform S s2 s1p s1m s0p s0m a b
  let Q : Matrix (Fin n) (Fin n) ℚ :=(p:ℚ)^2 • M
  have hQ (i j) : ((Q i j).den : ZMod p)≠0 :=hM i j
  have hrow (i j : Fin n) (hi : i∈S) :
      (((T*Q) i j).den : ZMod p)≠0 ∧ palindromicRatResidue p ((T*Q) i j)=0 :=by
    dsimp only [T]
    rw [fiveSourceTransform_mul,ite_eq_left hi]
    have hd0 :=rational_residue_sub (hQ i j) (hQ (s2 i) j)
    have hd1 :=rational_residue_sub (hQ (s1p i) j) (hQ (s1m i) j)
    have hd2 :=rational_residue_sub (hQ (s0p i) j) (hQ (s0m i) j)
    have hda :=rational_residue_mul ha hd1.1
    have hdb :=rational_residue_mul hb hd2.1
    have hdiff :=rational_residue_sub hd0.1 hda.1
    refine ⟨(rational_residue_add hdiff.1 hdb.1).1,?_⟩
    rw [palindromicRatResidue_add hdiff.1 hdb.1,
      palindromicRatResidue_sub hd0.1 hda.1,
      palindromicRatResidue_sub (hQ i j) (hQ (s2 i) j),
      palindromicRatResidue_mul ha hd1.1,
      palindromicRatResidue_sub (hQ (s1p i) j) (hQ (s1m i) j),
      palindromicRatResidue_mul hb hd2.1,
      palindromicRatResidue_sub (hQ (s0p i) j) (hQ (s0m i) j)]
    have hh :=hrel i hi j
    change palindromicRatResidue p (Q i j)-palindromicRatResidue p (Q (s2 i) j)=
      palindromicRatResidue p a*(palindromicRatResidue p (Q (s1p i) j)-palindromicRatResidue p (Q (s1m i) j))-
      palindromicRatResidue p b*(palindromicRatResidue p (Q (s0p i) j)-palindromicRatResidue p (Q (s0m i) j)) at hh
    linear_combination hh
  apply row_elimination_valuation_lower M T S (fiveSourceTransform_det S s2 s1p s1m s0p s0m a b hs)
  · intro i j
    by_cases hi : i∈S
    · exact (hrow i j hi).1
    · dsimp only [T]
      rw [fiveSourceTransform_mul,ite_eq_right hi]
      exact hQ i j
  · intro i hi j
    exact (hrow i j hi).2

end
end CatalanMeasure.Parametric

