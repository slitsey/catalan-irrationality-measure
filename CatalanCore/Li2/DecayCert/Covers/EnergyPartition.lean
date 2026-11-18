module
public import CatalanCore.Li2.DecayCert.Covers.Partition
@[expose] public section
set_option Elab.async false
open Polynomial MeasureTheory Set Filter Topology
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert
noncomputable section

theorem energyCoverCheck_partition (b : BentInput) (es : List EnergyPiece)
    (hc : energyCoverCheck b es=true) (j : Fin (baseSegments b).length) :
    let μ := ((baseSegments b)[j]).parameterMeasure
    μ (⋃ i : Fin es.length,
      if (es[i]).segment=j.val then Icc ((es[i]).left.x:ℝ) ((es[i]).right.x:ℝ) else ∅)ᶜ=0 ∧
    ∀ i k : Fin es.length,i ≠ k → (es[i]).segment=j.val → (es[k]).segment=j.val →
      μ (Icc ((es[i]).left.x:ℝ) ((es[i]).right.x:ℝ) ∩ Icc ((es[k]).left.x:ℝ) ((es[k]).right.x:ℝ))=0 := by
  let μ := ((baseSegments b)[j]).parameterMeasure
  let selected := es.filter (fun e => e.segment==j.val)
  let interval : EnergyPiece → QInterval := fun e => ⟨e.left.x,e.right.x⟩
  let cs := selected.map interval
  have hcheck : chainCheck (-1) 1 cs=true := by
    have h := hc
    simp only [energyCoverCheck,Bool.and_eq_true] at h
    exact (List.all_eq_true.mp h.2) j.val (List.mem_range.mpr j.isLt)
  have hunion : (⋃ c ∈ cs,Icc (c.left:ℝ) (c.right:ℝ))=
      ⋃ i : Fin es.length,if (es[i]).segment=j.val then Icc ((es[i]).left.x:ℝ) ((es[i]).right.x:ℝ) else ∅ := by
    ext x
    constructor
    · intro hx
      rcases mem_iUnion.1 hx with ⟨c,hxc⟩
      rcases mem_iUnion.1 hxc with ⟨hc,hxc⟩
      rcases List.mem_map.mp hc with ⟨e,he,hce⟩
      rcases List.mem_filter.mp he with ⟨hem,helabel⟩
      have hej : e.segment=j.val := by simpa using helabel
      rcases List.getElem_of_mem hem with ⟨i,hi,hei⟩
      refine mem_iUnion.2 ⟨⟨i,hi⟩,?_⟩
      change x ∈ (if (es[i]'hi).segment=j.val then Icc ((es[i]'hi).left.x:ℝ) ((es[i]'hi).right.x:ℝ) else ∅)
      rw [hei,if_pos hej]
      simpa only [← hce,interval] using hxc
    · intro hx
      rcases mem_iUnion.1 hx with ⟨i,hxi⟩
      by_cases hi : (es[i]).segment=j.val
      · simp only [if_pos hi] at hxi
        refine mem_iUnion.2 ⟨interval es[i],mem_iUnion.2 ⟨?_,hxi⟩⟩
        refine List.mem_map.mpr ⟨es[i],?_,rfl⟩
        exact List.mem_filter.mpr ⟨List.getElem_mem _,by simpa using hi⟩
      · simp only [if_neg hi,mem_empty_iff_false] at hxi
  have hpair0 := (chainCheck_sound (-1) 1 cs hcheck).2.1
  have hpair : selected.Pairwise (fun e f => e.right.x ≤ f.left.x) := by
    change (selected.map interval).Pairwise (fun c d => c.right ≤ d.left) at hpair0
    simpa only [List.pairwise_map,interval] using hpair0
  have hfull : es.Pairwise (fun e f => e.segment=j.val → f.segment=j.val → e.right.x ≤ f.left.x) := by
    have h := List.pairwise_filter.mp hpair
    simpa only [beq_iff_eq] using h
  constructor
  · rw [← hunion]
    exact chainCheck_cover_ae μ (sourceParameter_atomless ((baseSegments b)[j])) (-1) 1 cs hcheck
      (by simpa only [Rat.cast_neg,Rat.cast_one] using sourceParameter_supported ((baseSegments b)[j]))
  · intro i k hik hi hk
    have hne : i.val ≠ k.val := by intro he; exact hik (Fin.ext he)
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · apply ordered_Icc_inter_null μ (sourceParameter_atomless ((baseSegments b)[j]))
      exact_mod_cast (List.Pairwise.rel_getElem_of_lt i.isLt k.isLt hfull hlt hi hk)
    · rw [inter_comm]
      apply ordered_Icc_inter_null μ (sourceParameter_atomless ((baseSegments b)[j]))
      exact_mod_cast (List.Pairwise.rel_getElem_of_lt k.isLt i.isLt hfull hlt hk hi)
#print axioms energyCoverCheck_partition
end
end CatalanCore.Li2.DecayCert
