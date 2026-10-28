module
public import CatalanCore.Uniform.Decay.Nodes.Variation
@[expose] public section

/-!
# Uniform free-point potential discrepancy (Part 1, Lemma `free-potential`)

For a finite node set `A ⊆ ℕ` whose counting function is within `D` of the limiting CDF
`lamSum ps` of a list of pieces on `[0, b]`, and a point `z` at distance in `[δ, M]` from
`[0, b]`:

`|∑_{j∈A} elog z j - ∑_P w_P ∫_{lo}^{hi} elog z x dx| ≤ D (|kern z b| + 2 (log M - log δ))`.

This is in physical (unscaled) coordinates; the scaled statement of the paper is the same with
`z/r`.
-/

namespace CatalanCore.Uniform.Decay.Nodes
open Finset MeasureTheory Set intervalIntegral

/-- Cumulative function of a list of pieces. -/
noncomputable def lamSum (ps : List Piece) (t : ℝ) : ℝ :=
  (ps.map fun P => pieceLam P.w P.lo P.hi t).sum

theorem continuous_lamSum (ps : List Piece) : Continuous (lamSum ps) := by
  induction ps with
  | nil =>
    have : lamSum [] = fun _ => 0 := by funext t; simp [lamSum]
    rw [this]; exact continuous_const
  | cons P ps ih =>
    have : lamSum (P :: ps) = fun t => pieceLam P.w P.lo P.hi t + lamSum ps t := by
      funext t; simp only [lamSum, List.map_cons, List.sum_cons]
    rw [this]
    exact (continuous_pieceLam _ _ _).add ih

theorem ibp_list {g g' : ℝ → ℝ} {b : ℝ} (ps : List Piece)
    (hps : ∀ P ∈ ps, 0 ≤ P.lo ∧ P.lo ≤ P.hi ∧ P.hi ≤ b)
    (hg : ∀ t ∈ Icc 0 b, HasDerivAt g (g' t) t) (hg' : ContinuousOn g' (Icc 0 b)) :
    (ps.map fun P => P.w * ∫ t in P.lo..P.hi, g t).sum =
      g b * (ps.map fun P => P.w * (P.hi - P.lo)).sum - ∫ t in Ioc 0 b, g' t * lamSum ps t := by
  induction ps with
  | nil => simp [lamSum]
  | cons P ps ih =>
    have hP := hps P (List.mem_cons_self)
    have hrest : ∀ Q ∈ ps, 0 ≤ Q.lo ∧ Q.lo ≤ Q.hi ∧ Q.hi ≤ b :=
      fun Q hQ => hps Q (List.mem_cons_of_mem _ hQ)
    have hb0 : 0 ≤ b := hP.1.trans (hP.2.1.trans hP.2.2)
    have i1 := piece_ibp (w := P.w) hP.1 hP.2.1 hP.2.2 hg hg'
    have i2 := ih hrest
    have hint : ∀ f : ℝ → ℝ, Continuous f →
        IntegrableOn (fun t => g' t * f t) (Ioc 0 b) := fun f hf =>
      (ContinuousOn.integrableOn_Icc (hg'.mul hf.continuousOn)).mono_set Ioc_subset_Icc_self
    have h1 := hint (pieceLam P.w P.lo P.hi) (continuous_pieceLam _ _ _)
    have h2 := hint (lamSum ps) (continuous_lamSum ps)
    have hfun : (fun t => g' t * lamSum (P :: ps) t) =
        fun t => g' t * pieceLam P.w P.lo P.hi t + g' t * lamSum ps t := by
      funext t; simp only [lamSum, List.map_cons, List.sum_cons]; ring
    have hsplit : ∫ t in Ioc 0 b, g' t * lamSum (P :: ps) t =
        (∫ t in Ioc 0 b, g' t * pieceLam P.w P.lo P.hi t) + ∫ t in Ioc 0 b, g' t * lamSum ps t := by
      rw [hfun]; exact MeasureTheory.integral_add h1 h2
    rw [hsplit]
    simp only [List.map_cons, List.sum_cons]
    rw [i1]
    rw [i2]
    ring

/-- **Free-point potential discrepancy.** -/
theorem free_potential_discrepancy (A : Finset ℕ) (ps : List Piece) (z : ℂ) {b δ M D : ℝ}
    (hb : 0 ≤ b) (hδ : 0 < δ) (hd : ∀ t ∈ Icc (0 : ℝ) b, δ ≤ ‖z - (t : ℂ)‖)
    (hM : ∀ t ∈ Icc (0 : ℝ) b, ‖z - (t : ℂ)‖ ≤ M)
    (hps : ∀ P ∈ ps, 0 ≤ P.lo ∧ P.lo ≤ P.hi ∧ P.hi ≤ b)
    (hA : ∀ j ∈ A, (j : ℝ) ≤ b)
    (hD : ∀ t ∈ Icc (0 : ℝ) b,
      |((A.filter (fun j : ℕ => j ≤ ⌊t⌋₊)).card : ℝ) - lamSum ps t| ≤ D) :
    |(∑ j ∈ A, CatalanLambda.Decay.elog z (j : ℂ)) -
        (ps.map fun P => P.w * ∫ x in P.lo..P.hi, CatalanLambda.Decay.elog z (x : ℂ)).sum| ≤
      D * (|kern z b| + 2 * (Real.log M - Real.log δ)) := by
  have hg : ∀ t ∈ Icc (0 : ℝ) b, HasDerivAt (kern z) (kern' z t) t := by
    intro t ht
    have h2 : ‖z - (t : ℂ)‖ ^ 2 = (z.re - t) ^ 2 + z.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
    refine hasDerivAt_kern z t ?_
    rw [← h2]
    exact (pow_pos (hδ.trans_le (hd t ht)) 2).ne'
  have hg' := continuous_kern' z b δ hδ hd
  have habel := abel_discrepancy (indic A) (g := kern z) (g' := kern' z) (Λ := lamSum ps)
    (b := b) (D := D) hb hg hg' (continuous_lamSum ps)
    (fun t ht => by rw [sum_indic_Icc]; exact hD t ht)
  have hsum : ∑ k ∈ Icc 0 ⌊b⌋₊, kern z k * indic A k = ∑ j ∈ A, CatalanLambda.Decay.elog z (j : ℂ) := by
    rw [sum_mul_indic]
    have : A.filter (fun j : ℕ => j ≤ ⌊b⌋₊) = A := by
      apply Finset.filter_true_of_mem
      intro j hj
      exact Nat.le_floor (hA j hj)
    rw [this]
    exact Finset.sum_congr rfl (fun j _ => kern_eq_elog z j)
  have hlam : lamSum ps b = (ps.map fun P => P.w * (P.hi - P.lo)).sum := by
    unfold lamSum
    congr 1
    refine List.map_congr_left (fun P hP => ?_)
    have h := hps P hP
    unfold pieceLam
    rw [min_eq_right h.2.2, max_eq_right (by linarith [h.2.1])]
  have hibp := ibp_list ps hps hg hg'
  have hcongr : (ps.map fun P => P.w * ∫ x in P.lo..P.hi, CatalanLambda.Decay.elog z (x : ℂ)) =
      (ps.map fun P => P.w * ∫ x in P.lo..P.hi, kern z x) := by
    refine List.map_congr_left (fun P _ => ?_)
    simp_rw [kern_eq_elog]
  rw [hcongr, hibp]
  rw [hsum, hlam] at habel
  have hvar := kern_variation hb hδ hd hM
  have hD0 : 0 ≤ D := (abs_nonneg _).trans (hD 0 ⟨le_rfl, hb⟩)
  refine habel.trans ?_
  have : |kern z b| + ∫ t in Ioc 0 b, |kern' z t| ≤ |kern z b| + 2 * (Real.log M - Real.log δ) := by
    linarith
  exact mul_le_mul_of_nonneg_left this hD0

end CatalanCore.Uniform.Decay.Nodes
