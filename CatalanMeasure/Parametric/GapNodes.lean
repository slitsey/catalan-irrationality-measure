module
public import CatalanMeasure.Parametric.GapBudgets
public import CatalanMeasure.Parametric.FullIntervalFormula
@[expose] public section
namespace CatalanMeasure.Parametric
open OAI.InternalCatalan Set
noncomputable section

private theorem gap_square_pos {a : ℝ} (ha0 : 0<a) (ha1 : a<1) : 0<1-a^2 := by
  have hh := mul_pos (sub_pos.mpr ha1) (by linarith only [ha0] : 0<1+a)
  nlinarith only [hh]

def gapIndex (N : ℕ) : Fin (9*N) ⊕ Fin (9*N) ≃ Fin (18*N) :=
  finSumFinEquiv.trans (finCongr (by omega))

def gapPositiveNode (a : ℝ) (N : ℕ) (i : Fin (9*N)) : ℝ :=
  Real.sqrt (a^2+(1-a^2)*(1+CatalanMeasure.chebX (9*N) i)/2)

def gapNodes (a : ℝ) (N : ℕ) : Fin (18*N) → ℝ :=
  (Sum.elim (gapPositiveNode a N) (fun i => -gapPositiveNode a N i)) ∘ (gapIndex N).symm

theorem gap_positive_node_sq {a : ℝ} (ha0 : 0<a) (ha1 : a<1)
    (N : ℕ) (i : Fin (9*N)) :
    (gapPositiveNode a N i)^2=a^2+(1-a^2)*(1+CatalanMeasure.chebX (9*N) i)/2 := by
  unfold gapPositiveNode
  apply Real.sq_sqrt
  have hi := CatalanMeasure.chebX_mem i
  have haa := gap_square_pos ha0 ha1
  have harg : 0<1+CatalanMeasure.chebX (9*N) i := by linarith only [hi.1]
  exact add_nonneg (sq_nonneg a) (div_nonneg (mul_nonneg haa.le harg.le) (by norm_num))

theorem gap_positive_node_bounds {a : ℝ} (ha0 : 0<a) (ha1 : a<1)
    (N : ℕ) (i : Fin (9*N)) : a<gapPositiveNode a N i ∧ gapPositiveNode a N i<1 := by
  have hsq := gap_positive_node_sq ha0 ha1 N i
  have hi := CatalanMeasure.chebX_mem i
  have hnn : 0≤gapPositiveNode a N i := Real.sqrt_nonneg _
  have haa := gap_square_pos ha0 ha1
  have hl := mul_pos haa (by linarith only [hi.1] : 0<1+CatalanMeasure.chebX (9*N) i)
  have hu := mul_lt_mul_of_pos_left (hi.2) haa
  constructor <;> nlinarith only [hsq,hnn,ha0,ha1,hl,hu]

theorem gap_positive_node_injective {a : ℝ} (ha0 : 0<a) (ha1 : a<1) (N : ℕ) :
    Function.Injective (gapPositiveNode a N) := by
  intro i j hij
  apply CatalanMeasure.chebX_injective (9*N)
  have hi := gap_positive_node_sq ha0 ha1 N i
  have hj := gap_positive_node_sq ha0 ha1 N j
  have haa : 1-a^2≠0 := (gap_square_pos ha0 ha1).ne'
  have he : (1-a^2)*(CatalanMeasure.chebX (9*N) i-CatalanMeasure.chebX (9*N) j)=0 := by
    nlinarith only [hi,hj,congrArg (fun x : ℝ => x^2) hij]
  exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left haa)

theorem gap_nodes_injective {a : ℝ} (ha0 : 0<a) (ha1 : a<1) (N : ℕ) :
    Function.Injective (gapNodes a N) := by
  have hp := gap_positive_node_injective ha0 ha1 N
  have hs : Function.Injective (Sum.elim (gapPositiveNode a N) (fun i => -gapPositiveNode a N i)) := by
    intro i j h
    cases i with
    | inl i =>
      cases j with
      | inl j => exact congrArg Sum.inl (hp h)
      | inr j =>
        have hi := (gap_positive_node_bounds ha0 ha1 N i).1
        have hj := (gap_positive_node_bounds ha0 ha1 N j).1
        simp only [Sum.elim_inl,Sum.elim_inr] at h
        linarith only [hi,hj,ha0,h]
    | inr i =>
      cases j with
      | inl j =>
        have hi := (gap_positive_node_bounds ha0 ha1 N i).1
        have hj := (gap_positive_node_bounds ha0 ha1 N j).1
        simp only [Sum.elim_inl,Sum.elim_inr] at h
        linarith only [hi,hj,ha0,h]
      | inr j => exact congrArg Sum.inr (hp (neg_inj.mp h))
  exact hs.comp (gapIndex N).symm.injective

theorem gap_nodes_bounds {a : ℝ} (ha0 : 0<a) (ha1 : a<1)
    (N : ℕ) (i : Fin (18*N)) : gapNodes a N i ∈ Ioo (-1:ℝ) 1 ∧ a < |gapNodes a N i| := by
  simp only [gapNodes,Function.comp_apply]
  cases h : (gapIndex N).symm i with
  | inl j =>
    have hj := gap_positive_node_bounds ha0 ha1 N j
    simp only [Sum.elim_inl]
    rw [abs_of_pos (lt_trans ha0 hj.1)]
    exact ⟨⟨by linarith only [ha0,hj.1],hj.2⟩,hj.1⟩
  | inr j =>
    have hj := gap_positive_node_bounds ha0 ha1 N j
    simp only [Sum.elim_inr,abs_neg]
    rw [abs_of_pos (lt_trans ha0 hj.1)]
    exact ⟨⟨by linarith only [hj.2],by linarith only [ha0,hj.1]⟩,hj.1⟩

theorem coordinate_gap_of_inverse_gap {g x : ℝ} (hg0 : 0≤g) (hg1 : g<1)
    (hx : |x|<1) (hh : 2*g/(1+g^2) ≤ |realCoordinateInv x|) : g≤|x| := by
  have hdx : 0<1+x^2 := by positivity
  have hdg : 0<1+g^2 := by positivity
  have ha : |realCoordinateInv x|=2*|x|/(1+x^2) := by
    simp [realCoordinateInv,abs_div,abs_mul,abs_of_pos hdx]
  rw [ha,div_le_div_iff₀ hdg hdx] at hh
  rw [← sq_abs x] at hh
  by_contra hn
  have hsmall : |x|<g := lt_of_not_ge hn
  have hgu : g*|x|<1 :=
    (mul_le_mul_of_nonneg_left hx.le hg0).trans_lt (by simpa using hg1)
  have hprod := mul_pos (sub_pos.mpr hsmall) (sub_pos.mpr hgu)
  nlinarith only [hh,hprod]

def twentyGapNodes (N : ℕ) : Fin (18*N) → ℝ := gapNodes (interpolationGap:ℝ) N

theorem twenty_gap_nodes_properties (N : ℕ) :
    Function.Injective (twentyGapNodes N) ∧
    ∀ i, twentyGapNodes N i ∈ Ioo (-1:ℝ) 1 ∧
      (physicalAtomGap:ℝ)≤|realCoordinate (twentyGapNodes N i)| := by
  have ha0 : (0:ℝ) < interpolationGap := by norm_num [interpolationGap]
  have ha1 : (interpolationGap:ℝ)<1 := by norm_num [interpolationGap]
  refine ⟨gap_nodes_injective ha0 ha1 N,?_⟩
  intro i
  have hi := gap_nodes_bounds ha0 ha1 N i
  refine ⟨hi.1,?_⟩
  apply coordinate_gap_of_inverse_gap
    (by norm_num [physicalAtomGap]) (by norm_num [physicalAtomGap])
    (abs_lt.mpr (realCoordinate_mem hi.1))
  rw [realCoordinate_right_inverse hi.1]
  have he : (2:ℝ)*(physicalAtomGap:ℝ)/(1+(physicalAtomGap:ℝ)^2)=(interpolationGap:ℝ) := by
    norm_num [physicalAtomGap,interpolationGap]
  rw [he]
  exact hi.2.le

end
end CatalanMeasure.Parametric
