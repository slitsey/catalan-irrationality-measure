module

public import CatalanCore.Uniform.Decay.Polygon.Deform

@[expose] public section

/-!
# The oriented polygon parameter (Part 2, Definition "oriented parameter measure")

A polygon `a → b₁ → ⋯ → b_m → tail d` is parametrised by one real parameter `u > 0`:
edge `j` is traversed on `u ∈ (j, j+1]` (affinely, with constant velocity `b_{j+1} - b_j`),
and the tail on `u > m` with velocity `d`.  Each traversal has its own parameter interval, so
edge multiplicities (repeated traversal, self-intersection) are kept; endpoint duplication has
measure zero.  With this choice the parameter space of a polygon is again `(0, ∞)`, and the
polygon source space is the old atoms-plus-two-rays space with new position and weight maps.

`pathInt_eq` : the parameter integral `∫_{u>0} f(γ(u)) γ'(u) du` is the chain integral plus the
improper tail integral (`polyI`).
-/

open MeasureTheory Set Filter Topology

namespace CatalanCore.Uniform.Decay.Polygon

/-- Position along the polygon `a → l → tail d` at parameter `u`. -/
noncomputable def pathPt (d : ℂ) : ℂ → List ℂ → ℝ → ℂ
  | a, [], u => a + (u : ℂ) * d
  | a, b :: l, u => if u ≤ 1 then a + (u : ℂ) * (b - a) else pathPt d b l (u - 1)

/-- Velocity along the polygon at parameter `u`. -/
noncomputable def pathDer (d : ℂ) : ℂ → List ℂ → ℝ → ℂ
  | _, [], _ => d
  | a, b :: l, u => if u ≤ 1 then b - a else pathDer d b l (u - 1)

/-- The union of the finite edges of the chain `a → l`. -/
def chainSet : ℂ → List ℂ → Set ℂ
  | _, [] => ∅
  | a, b :: l => segment ℝ a b ∪ chainSet b l

/-- The closed tail `{L + t d : t ≥ 0}`. -/
def tailSet (L d : ℂ) : Set ℂ := {z | ∃ t : ℝ, 0 ≤ t ∧ z = L + (t : ℂ) * d}

theorem setIntegral_Ioi_shift (g : ℝ → ℂ) (c : ℝ) :
    ∫ u in Ioi c, g (u - c) = ∫ u in Ioi (0 : ℝ), g u := by
  rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi]
  have e : (Ioi c).indicator (fun u => g (u - c)) = fun u => (Ioi (0 : ℝ)).indicator g (u - c) := by
    funext u
    by_cases h : c < u
    · rw [indicator_of_mem (show u ∈ Ioi c from h),
        indicator_of_mem (show u - c ∈ Ioi (0 : ℝ) from by simp only [mem_Ioi]; linarith)]
    · rw [indicator_of_notMem (show u ∉ Ioi c from h),
        indicator_of_notMem (show u - c ∉ Ioi (0 : ℝ) from by simp only [mem_Ioi]; linarith)]
  rw [e]
  exact integral_sub_right_eq_self _ c

theorem integrableOn_Ioi_shift {g : ℝ → ℂ} (c : ℝ) (hg : IntegrableOn g (Ioi 0)) :
    IntegrableOn (fun u => g (u - c)) (Ioi c) := by
  rw [← integrable_indicator_iff measurableSet_Ioi] at hg ⊢
  have e : (Ioi c).indicator (fun u => g (u - c)) = fun u => (Ioi (0 : ℝ)).indicator g (u - c) := by
    funext u
    by_cases h : c < u
    · rw [indicator_of_mem (show u ∈ Ioi c from h),
        indicator_of_mem (show u - c ∈ Ioi (0 : ℝ) from by simp only [mem_Ioi]; linarith)]
    · rw [indicator_of_notMem (show u ∉ Ioi c from h),
        indicator_of_notMem (show u - c ∉ Ioi (0 : ℝ) from by simp only [mem_Ioi]; linarith)]
  rw [e]
  exact hg.comp_sub_right c

theorem lineMap_eq (a b : ℂ) (u : ℝ) : AffineMap.lineMap a b u = a + (u : ℂ) * (b - a) := by
  rw [AffineMap.lineMap_apply]
  simp only [vsub_eq_sub, vadd_eq_add, Complex.real_smul]
  ring

/-- **Parameter integral of a polygon.**  If `f` is continuous on the finite edges and the tail
integrand is integrable, the parameter integrand is integrable and its integral is the chain
integral plus the improper tail integral. -/
theorem pathInt_eq (f : ℂ → ℂ) (d : ℂ) :
    ∀ (l : List ℂ) (a : ℂ), (∀ z ∈ chainSet a l, ContinuousAt f z) →
      IntegrableOn (fun u : ℝ => f ((a :: l).getLast (List.cons_ne_nil a l) + (u : ℂ) * d) * d)
        (Ioi 0) →
      IntegrableOn (fun u => f (pathPt d a l u) * pathDer d a l u) (Ioi 0) ∧
      ∫ u in Ioi (0 : ℝ), f (pathPt d a l u) * pathDer d a l u = polyI f a l d
  | [], a, _, hT => by
    refine ⟨?_, ?_⟩
    · simpa [pathPt, pathDer] using hT
    · simp [pathPt, pathDer, polyI, chainI, rayInt]
  | b :: l, a, hc, hT => by
    have hc' : ∀ z ∈ chainSet b l, ContinuousAt f z := fun z hz => hc z (Or.inr hz)
    have hT' : IntegrableOn
        (fun u : ℝ => f ((b :: l).getLast (List.cons_ne_nil b l) + (u : ℂ) * d) * d) (Ioi 0) := by
      simpa [List.getLast_cons_cons] using hT
    obtain ⟨hI, hE⟩ := pathInt_eq f d l b hc' hT'
    set F := fun u => f (pathPt d a (b :: l) u) * pathDer d a (b :: l) u with hF
    set h := fun u : ℝ => f (a + (u : ℂ) * (b - a)) * (b - a) with hh
    have hcont : ContinuousOn h (Icc 0 1) := by
      intro u hu
      refine ContinuousAt.continuousWithinAt (ContinuousAt.mul ?_ continuousAt_const)
      have hz : a + (u : ℂ) * (b - a) ∈ chainSet a (b :: l) := by
        left
        rw [segment_eq_image_lineMap]
        exact ⟨u, hu, lineMap_eq a b u⟩
      exact (hc _ hz).comp (f := fun u : ℝ => a + (u : ℂ) * (b - a)) (by fun_prop)
    have eq1 : EqOn F h (Ioc 0 1) := by
      intro u hu
      simp only [hF, hh, pathPt, pathDer, if_pos hu.2]
    have eq2 : EqOn F (fun u => f (pathPt d b l (u - 1)) * pathDer d b l (u - 1)) (Ioi 1) := by
      intro u hu
      have : ¬ u ≤ 1 := not_le.2 hu
      simp only [hF, pathPt, pathDer, if_neg this]
    have i1 : IntegrableOn F (Ioc 0 1) :=
      ((hcont.integrableOn_Icc).mono_set Ioc_subset_Icc_self).congr_fun eq1.symm measurableSet_Ioc
    have i2 : IntegrableOn F (Ioi 1) :=
      (integrableOn_Ioi_shift (g := fun u => f (pathPt d b l u) * pathDer d b l u) 1 hI).congr_fun
        eq2.symm measurableSet_Ioi
    have hU : Ioi (0 : ℝ) = Ioc 0 1 ∪ Ioi 1 := (Ioc_union_Ioi_eq_Ioi zero_le_one).symm
    refine ⟨?_, ?_⟩
    · rw [hU]; exact i1.union i2
    · rw [hU, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi i1 i2,
        setIntegral_congr_fun measurableSet_Ioc eq1, setIntegral_congr_fun measurableSet_Ioi eq2,
        setIntegral_Ioi_shift (fun u => f (pathPt d b l u) * pathDer d b l u) 1, hE]
      have hs : ∫ u in Ioc (0 : ℝ) 1, h u = segI f a b := by
        rw [segI_eq, intervalIntegral.integral_of_le zero_le_one]
        refine setIntegral_congr_fun measurableSet_Ioc (fun u _ => ?_)
        simp only [hh, lineMap_eq]
      rw [hs]
      unfold polyI
      rw [chainI_cons_cons, List.getLast_cons_cons]
      ring

/-- Every point of the parametrised polygon lies on a finite edge or on the tail. -/
theorem pathPt_mem (d : ℂ) :
    ∀ (l : List ℂ) (a : ℂ) {u : ℝ}, 0 ≤ u →
      pathPt d a l u ∈ chainSet a l ∪ tailSet ((a :: l).getLast (List.cons_ne_nil a l)) d
  | [], a, u, hu => Or.inr ⟨u, hu, rfl⟩
  | b :: l, a, u, hu => by
    by_cases h1 : u ≤ 1
    · left; left
      simp only [pathPt, if_pos h1]
      rw [segment_eq_image_lineMap]
      exact ⟨u, ⟨hu, h1⟩, lineMap_eq a b u⟩
    · simp only [pathPt, if_neg h1]
      rcases pathPt_mem d l b (u := u - 1) (by linarith) with h | h
      · left; right; exact h
      · right; rw [List.getLast_cons_cons]; exact h

/-- The velocity is either an edge vector or the tail direction. -/
theorem pathDer_mem (d : ℂ) :
    ∀ (l : List ℂ) (a : ℂ) (u : ℝ),
      pathDer d a l u = d ∨ ∃ x ∈ a :: l, ∃ y ∈ a :: l, pathDer d a l u = y - x
  | [], a, u => Or.inl rfl
  | b :: l, a, u => by
    by_cases h1 : u ≤ 1
    · right; simp only [pathDer, if_pos h1]
      exact ⟨a, by simp, b, by simp, rfl⟩
    · simp only [pathDer, if_neg h1]
      rcases pathDer_mem d l b (u - 1) with h | ⟨x, hx, y, hy, h⟩
      · exact Or.inl h
      · right; exact ⟨x, List.mem_cons_of_mem a hx, y, List.mem_cons_of_mem a hy, h⟩

theorem measurable_pathPt (d : ℂ) : ∀ (l : List ℂ) (a : ℂ), Measurable (pathPt d a l)
  | [], a => by show Measurable (fun u : ℝ => a + (u : ℂ) * d); fun_prop
  | b :: l, a => by
    have ih := measurable_pathPt d l b
    have : pathPt d a (b :: l) = fun u : ℝ => if u ≤ 1 then a + (u : ℂ) * (b - a)
        else pathPt d b l (u - 1) := by funext u; rfl
    rw [this]
    exact Measurable.ite measurableSet_Iic (by fun_prop) (ih.comp (by fun_prop))

theorem measurable_pathDer (d : ℂ) : ∀ (l : List ℂ) (a : ℂ), Measurable (pathDer d a l)
  | [], a => measurable_const
  | b :: l, a => by
    have ih := measurable_pathDer d l b
    have : pathDer d a (b :: l) = fun u : ℝ => if u ≤ 1 then b - a else pathDer d b l (u - 1) := by
      funext u; rfl
    rw [this]
    exact Measurable.ite measurableSet_Iic measurable_const (ih.comp (by fun_prop))

end CatalanCore.Uniform.Decay.Polygon
