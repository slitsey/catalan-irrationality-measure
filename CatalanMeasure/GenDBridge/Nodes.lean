module

public import CatalanMeasure.GenD.Analytic.GapWeights
public import CatalanMeasure.GenD.Analytic.FullWeights
public import CatalanMeasure.Parametric.GapNodes
public import CatalanMeasure.Parametric.GapNodal
public import CatalanMeasure.GapCircle.Bound
public import CatalanMeasure.Parametric.FullIntervalFormula

@[expose] public section

/-!
# Bridge (NOT part of `GenD`): P20 parity of the generic gap nodes and weight bound (group 4)

For `J = 18 N` (even) the generic nodes `gapNodesGen a J` are the old `Parametric.gapNodes a N`,
`gapPolyK a (9N)` is the old `gapPolynomial a N`, and the old `GapCircleBound`/`circle_bound`
gives the generic `GapCircleBound twenty` with `C = 1`, so `GapWeightBounds twenty` holds for every
`w > 17913/1000`.  Also `fullNodes (18N) = chebX (18N)`.
-/

namespace CatalanMeasure.GenDBridge

open CatalanMeasure.GenD.Analytic CatalanMeasure.Parametric

theorem posNode_eq (a : ℝ) (N : ℕ) (i : Fin (9 * N)) :
    posNode a (9 * N) i = gapPositiveNode a N i := rfl

theorem posNode_congr (a : ℝ) {K1 K2 : ℕ} (h : K1 = K2) (j : Fin K1) :
    posNode a K1 j = posNode a K2 (Fin.cast h j) := by subst h; rfl

theorem gapNodesGen_eq (a : ℝ) (N : ℕ) (i : Fin (18 * N)) :
    gapNodesGen a (18 * N) i = gapNodes a N i := by
  have hK : (18 * N + 1) / 2 = 9 * N := by omega
  have hL : 18 * N / 2 = 9 * N := by omega
  unfold gapNodes gapIndex gapNodesGen
  by_cases hi : (i : ℕ) < 9 * N
  · have e1 : (Fin.cast (by omega) i : Fin ((18 * N + 1) / 2 + 18 * N / 2)) =
        Fin.castAdd _ (Fin.cast hK.symm ⟨i, hi⟩) := Fin.ext rfl
    have e2 : (finCongr (by omega : 9 * N + 9 * N = 18 * N)).symm i =
        Fin.castAdd (9 * N) ⟨i, hi⟩ := Fin.ext rfl
    rw [e1, gapNodesKL_left]
    simp only [Function.comp_apply, Equiv.symm_trans_apply, e2, finSumFinEquiv_symm_apply_castAdd,
      Sum.elim_inl]
    exact (posNode_congr a hK.symm ⟨i, hi⟩).symm
  · have hi2 : (i : ℕ) - 9 * N < 9 * N := by have := i.isLt; omega
    have e1 : (Fin.cast (by omega) i : Fin ((18 * N + 1) / 2 + 18 * N / 2)) =
        Fin.natAdd ((18 * N + 1) / 2) (Fin.cast hL.symm ⟨(i : ℕ) - 9 * N, hi2⟩) :=
      Fin.ext (by simp; omega)
    have e2 : (finCongr (by omega : 9 * N + 9 * N = 18 * N)).symm i =
        Fin.natAdd (9 * N) ⟨(i : ℕ) - 9 * N, hi2⟩ := Fin.ext (by simp; omega)
    rw [e1, gapNodesKL_right]
    simp only [Function.comp_apply, Equiv.symm_trans_apply, e2, finSumFinEquiv_symm_apply_natAdd,
      Sum.elim_inr]
    congr 1
    exact (posNode_congr a hK.symm ⟨(i : ℕ) - 9 * N, hi2⟩).symm.trans (by
      congr 1)

theorem gapPolyK_eq_gapPolynomial (a : ℝ) (N : ℕ) :
    gapPolyK a (9 * N) = gapPolynomial a N := rfl

theorem twenty_gapCircleBound :
    GapCircleBound twenty (interpolationGap : ℝ) (1001 / 1000) 1 gapWeightCost := by
  intro N z hN hz
  have hK : (((twenty.n0 - twenty.g0) * N) + 1) / 2 = 9 * N := by
    change ((20 - 2) * N + 1) / 2 = 9 * N
    omega
  rw [hK, gapPolyK_eq_gapPolynomial, one_mul]
  have := GapCircle.circle_bound N z hz
  have e : twenty.h N + twenty.q N = 2 * N := by
    simp only [Parameters.h, Parameters.q, twenty]; ring
  rw [e]
  simpa using this

/-- P20: the generic weight bound holds for every `w` above the old cover constant `17.913`. -/
theorem twenty_gapWeightBounds {w : ℝ} (hw : gapWeightCost < w) :
    GapWeightBounds twenty (gapNodesD twenty (interpolationGap : ℝ)) w :=
  gap_weight_bounds twenty (by decide)
    (by norm_num [interpolationGap]) (by norm_num [interpolationGap])
    (by norm_num [interpolationGap]) (by norm_num) (by norm_num)
    twenty_gapCircleBound hw

theorem fullNodes_eq (N : ℕ) (i : Fin (18 * N)) :
    fullNodes (18 * N) i = CatalanMeasure.chebX (18 * N) i := by
  have hK : fullK (18 * N) = 18 * N := by unfold fullK; omega
  have key : ∀ (K : ℕ) (h : K = 18 * N) (hle : 18 * N ≤ K) (j : Fin (18 * N)),
      CatalanMeasure.chebX K (Fin.castLE hle j) = CatalanMeasure.chebX (18 * N) j := by
    intro K h; subst h; intro _ j; rfl
  exact key _ hK _ i

end CatalanMeasure.GenDBridge
