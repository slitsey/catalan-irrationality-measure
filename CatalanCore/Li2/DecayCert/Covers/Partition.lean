module
public import CatalanCore.Li2.DecayCert.BentSpec
@[expose] public section
set_option Elab.async false
open Polynomial MeasureTheory Set Filter Topology
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert
noncomputable section

theorem ordered_Icc_inter_null (μ : Measure ℝ) (hatom : ∀ x : ℝ,μ {x}=0)
    (a b c d : ℝ) (hbc : b ≤ c) : μ (Icc a b ∩ Icc c d)=0 := by
  apply measure_mono_null _ (hatom b)
  intro x hx
  have hleft := hx.1.2
  have hright := hx.2.1
  exact mem_singleton_iff.mpr (by linarith)

theorem chainCheck_overlap_null (μ : Measure ℝ) (hatom : ∀ x : ℝ,μ {x}=0)
    (a b : ℚ) (cs : List QInterval) (hc : chainCheck a b cs=true)
    (i j : Fin cs.length) (hij : i ≠ j) :
    μ (Icc ((cs[i]).left:ℝ) ((cs[i]).right:ℝ) ∩ Icc ((cs[j]).left:ℝ) ((cs[j]).right:ℝ))=0 := by
  have hp := (chainCheck_sound a b cs hc).2.1
  have hne : i.val ≠ j.val := by intro he; exact hij (Fin.ext he)
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · apply ordered_Icc_inter_null μ hatom
    exact_mod_cast (List.Pairwise.rel_getElem_of_lt i.isLt j.isLt hp hlt)
  · rw [inter_comm]
    apply ordered_Icc_inter_null μ hatom
    exact_mod_cast (List.Pairwise.rel_getElem_of_lt j.isLt i.isLt hp hlt)

theorem chainCheck_cover_ae (μ : Measure ℝ) (hatom : ∀ x : ℝ,μ {x}=0)
    (a b : ℚ) (cs : List QInterval) (hc : chainCheck a b cs=true)
    (hsupp : μ (Icc (a:ℝ) (b:ℝ))ᶜ=0) :
    μ (⋃ c ∈ cs,Icc (c.left:ℝ) (c.right:ℝ))ᶜ=0 := by
  have hs : ∀ᵐ x ∂μ,x ∈ Icc (a:ℝ) (b:ℝ) := ae_iff.mpr hsupp
  have hn : ∀ᵐ x ∂μ,x ≠ (a:ℝ) := by
    simpa only [mem_singleton_iff] using measure_eq_zero_iff_ae_notMem.mp (hatom (a:ℝ))
  apply ae_iff.mp
  filter_upwards [hs,hn] with x hx hne
  have hxo : x ∈ Ioc (a:ℝ) (b:ℝ) := ⟨lt_of_le_of_ne hx.1 (Ne.symm hne),hx.2⟩
  rw [(chainCheck_sound a b cs hc).2.2.2] at hxo
  rcases mem_iUnion.1 hxo with ⟨c,hxc⟩
  rcases mem_iUnion.1 hxc with ⟨hc,hxc⟩
  exact mem_iUnion.2 ⟨c,mem_iUnion.2 ⟨hc,⟨hxc.1.le,hxc.2⟩⟩⟩
#print axioms ordered_Icc_inter_null
#print axioms chainCheck_overlap_null
#print axioms chainCheck_cover_ae
end
end CatalanCore.Li2.DecayCert
