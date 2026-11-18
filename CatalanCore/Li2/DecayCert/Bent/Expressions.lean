module
public import CatalanCore.Li2.DecayCert.Bent.VIntegral
public import CatalanCore.Li2.DecayCert.Bent.Geometry
@[expose] public section
set_option Elab.async false
open Polynomial MeasureTheory Set Filter Topology
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert
open CatalanCore.Li2.Decay
noncomputable section

theorem seSum_value (xs : List SE) : (seSum xs).value=(xs.map ScalarExpr.value).sum := by
  have hh : ∀ xs : List SE,∀ b : SE,(xs.foldl seAdd b).value=b.value+(xs.map ScalarExpr.value).sum := by
    intro xs
    induction xs with
    | nil => intro b; simp
    | cons a xs ih =>
      intro b
      simp only [List.foldl_cons,List.map_cons,List.sum_cons]
      rw [ih,seAdd_value]
      ring
  simpa only [seSum,seRat_value,Rat.cast_zero,zero_add] using hh xs (seRat 0)

theorem option_mapM_sum_values {α : Type*} (xs : List α) (f : α → Option SE) (g : α → ℝ) :
    ∀ es : List SE,(∀ a ∈ xs,∀ e,f a=some e → e.value=g a) → xs.mapM f=some es →
      (es.map ScalarExpr.value).sum=(xs.map g).sum := by
  induction xs with
  | nil =>
    intro es hf hm
    have he : ([]:List SE)=es := Option.some.inj hm
    subst es
    simp
  | cons a xs ih =>
    intro es hf hm
    cases ha : f a with
    | none => simp [ha] at hm
    | some b =>
      cases ht : xs.mapM f with
      | none => simp [ha,ht] at hm
      | some bs =>
        simp only [List.mapM_cons,ha,ht,Option.bind_some,Option.pure_def] at hm
        cases Option.some.inj hm
        simp only [List.map_cons,List.sum_cons]
        rw [hf a List.mem_cons_self b ha,ih bs (fun q hq => hf q (List.mem_cons_of_mem a hq)) ht]

theorem weighted_bent_integral (b : BentInput) (f : ℂ → ℝ)
    (hf : Integrable f b.data.dual.σ) (hconj : ∀ u,f (starRingEnd ℂ u)=f u) :
    (∑ j : Fin (baseSegments b).length,(if j.val < b.upper.length then (2:ℝ) else 1)*
      ∫ u,f u ∂((baseSegments b)[j]).measure)=∫ u,f u ∂b.data.dual.σ := by
  rw [integral_bent_sources b f hf hconj]
  calc
    _ = ∑ j : Fin (b.upper.length+b.atoms.length),(if j.val < b.upper.length then (2:ℝ) else 1)*
        ∫ u,f u ∂(b.upper++b.atoms)[j].measure := by
      apply Fintype.sum_equiv (finCongr (show (baseSegments b).length=b.upper.length+b.atoms.length from List.length_append))
      intro j
      rfl
    _ = _ := weighted_append_sum b.upper b.atoms (fun s => ∫ u,f u ∂s.measure)

def bentVRow (z : ℚ) (b : BentInput) (c : BentCert) (j : ℕ) : Option SE := do
  let s ← (baseSegments b)[j]?
  let w ← c.vSeeds[j]?
  if vintGeometryCheck s 1 w.1 && vintGeometryCheck s 0 w.2.1 && vintGeometryCheck s 4 w.2.2 then
    pure (seScale (if j < b.upper.length then 2 else 1) (oneVExpr z s w c.terms))
  else none

theorem bentVRow_value (z : ℚ) (hn : z < 0) (b : BentInput) (c : BentCert)
    (hd : datumCheck b.data c.density=true) (hp : placementCheck b=true)
    (j : ℕ) (hj : j < (baseSegments b).length) (e : SE) (he : bentVRow z b c j=some e) :
    e.value=((baseSegments b)[j]?.map (fun s =>
      (if j < b.upper.length then (2:ℝ) else 1)*(∫ u,V (z:ℝ) u ∂s.measure))).getD 0 := by
  have hs : (baseSegments b)[j]?=some ((baseSegments b)[j]) := List.getElem?_eq_getElem hj
  unfold bentVRow at he
  rw [hs] at he
  cases hw : c.vSeeds[j]? with
  | none => simp [hw] at he
  | some w =>
    rw [hw] at he
    change (if vintGeometryCheck _ _ _ && vintGeometryCheck _ _ _ && vintGeometryCheck _ _ _ then
      some (seScale (if j < b.upper.length then 2 else 1) (oneVExpr z ((baseSegments b)[j]) w c.terms)) else none)=some e at he
    split at he
    · rename_i hg
      have hg' := hg
      simp only [Bool.and_eq_true] at hg'
      have heq := Option.some.inj he
      rw [← heq,seScale_value]
      have hμ : ((baseSegments b)[j]).measure ≤ b.data.dual.σ := by
        rw [b.data.measure_eq]
        exact source_measure_le_sum _ _ (baseSegments_mem_data b _ (List.getElem_mem _))
      rw [oneVExpr_value z hn _ w c.terms b.data.dual hμ
        (baseSegments_positive b c.density hd _ (List.getElem_mem _))
        (base_source_im_nonneg b hp _ (List.getElem_mem _)) hg'.1.1 hg'.1.2 hg'.2]
      simp only [hs,Option.map_some,Option.getD_some]
      split_ifs <;> norm_num
    · simp at he

theorem bentVExpr_value (z : ℚ) (hn : z < 0) (b : BentInput) (c : BentCert)
    (hd : datumCheck b.data c.density=true) (hp : placementCheck b=true)
    (e : SE) (he : bentVExpr z b c=some e) :
    e.value=∫ u,V (z:ℝ) u ∂b.data.dual.σ := by
  have hform : bentVExpr z b c=(if c.vSeeds.length ≠ (baseSegments b).length then none else do
      let es ← (List.range (baseSegments b).length).mapM (bentVRow z b c)
      pure (seSum es)) := rfl
  rw [hform] at he
  split at he
  · simp at he
  · cases hm : (List.range (baseSegments b).length).mapM (bentVRow z b c) with
    | none => simp [hm] at he
    | some es =>
      rw [hm] at he
      change some (seSum es)=some e at he
      have heq := Option.some.inj he
      rw [← heq,seSum_value]
      let g : ℕ → ℝ := fun j => ((baseSegments b)[j]?.map (fun s =>
        (if j < b.upper.length then (2:ℝ) else 1)*(∫ u,V (z:ℝ) u ∂s.measure))).getD 0
      rw [option_mapM_sum_values (List.range (baseSegments b).length) (bentVRow z b c) g es
        (fun j hj => bentVRow_value z hn b c hd hp j (List.mem_range.mp hj)) hm]
      rw [list_sum_map_range,← Fin.sum_univ_eq_sum_range]
      have hh : (∑ j : Fin (baseSegments b).length,g j.val)=
          ∑ j : Fin (baseSegments b).length,(if j.val < b.upper.length then (2:ℝ) else 1)*
            ∫ u,V (z:ℝ) u ∂((baseSegments b)[j]).measure := by
        apply Finset.sum_congr rfl
        intro j hj
        simp only [g,List.getElem?_eq_getElem j.isLt,Option.map_some,Option.getD_some,Fin.getElem_fin]
      rw [hh]
      exact weighted_bent_integral b _ (datum_V_integrable (z:ℝ) b.data.dual) (V_conj (z:ℝ))
#print axioms option_mapM_sum_values
#print axioms bentVRow_value
#print axioms bentVExpr_value
end
end CatalanCore.Li2.DecayCert
