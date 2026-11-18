module
public import CatalanCore.Li2.Uniform.FixedTable.Values.Entries
public import Mathlib.Order.Interval.Finset.Fin
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
open Set
namespace CatalanCore.Li2.Uniform
open FixedData

/-- Structural source metadata only. Per-entry checker records prove the bounds. -/
noncomputable def nodeTable : NodeTable where
  nodeCount := 37
  pairCount := 419
  nodes := fixedNodes
  entries := fixedEntries
  interpPairs := (Finset.univ : Finset (Fin 419 × Fin 419)).filter (fun p =>
    (fixedNodes (fixedEntries p.1).node).frame=(fixedNodes (fixedEntries p.2).node).frame ∧
    (fixedNodes (fixedEntries p.2).node).magnitude<(fixedNodes (fixedEntries p.1).node).magnitude ∧
    (fixedNodes (fixedEntries p.1).node).magnitude/(fixedNodes (fixedEntries p.2).node).magnitude≤logGapLow)
  slopes := [0,1/4,1/2,3/4,1]

instance nodeTable_pairCount_neZero : NeZero nodeTable.pairCount := ⟨by decide⟩
instance nodeTable_nodeCount_neZero : NeZero nodeTable.nodeCount := ⟨by decide⟩

/-- Membership is checked at one pair; no whole finite-filter evaluation is needed. -/
theorem nodeTable_mem_interpPairs (i j : Fin nodeTable.pairCount) :
    (i,j)∈nodeTable.interpPairs ↔
      (nodeTable.entryNode i).frame=(nodeTable.entryNode j).frame ∧
      (nodeTable.entryNode j).magnitude<(nodeTable.entryNode i).magnitude ∧
      (nodeTable.entryNode i).magnitude/(nodeTable.entryNode j).magnitude≤logGapLow := by
  exact ⟨fun h => (Finset.mem_filter.mp h).2,
    fun h => Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩⟩

theorem nodeTable_valid : TableValid nodeTable := by
  refine ⟨?_,?_,?_,?_,rfl,?_⟩
  · intro k
    exact ⟨fixedNodes_positive k,fixedNodes_lt_one k⟩
  · exact fixedEntries_positive
  · exact fixedEntries_injective
  · exact fixedEntries_cover
  · intro i j
    rw [nodeTable_mem_interpPairs]
    exact (node_allowed_iff _ _ (fixedNodes_positive (fixedEntries i).node)
      (fixedNodes_positive (fixedEntries j).node)
      (fixedNodes_gap (fixedEntries i).node (fixedEntries j).node)).symm

theorem nodeTable_shape : CampaignTableShape nodeTable := by
  have hn : (Finset.univ.filter (fun k : Fin 37 => (fixedNodes k).frame=.lattice))=
      Finset.Iio (⟨24,by decide⟩ : Fin 37) := by
    ext k
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_Iio]
    exact fixedNodes_lattice_iff k
  have he : (Finset.univ.filter (fun i : Fin 419 => (fixedNodes (fixedEntries i).node).frame=.lattice))=
      Finset.Iio (⟨151,by decide⟩ : Fin 419) := by
    ext i
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_Iio]
    exact fixedEntries_lattice_iff i
  have hnc : (Finset.univ.filter (fun k : Fin 37 => (fixedNodes k).frame=.lattice)).card=24 := by
    rw [hn,Fin.card_Iio]
  have hec : (Finset.univ.filter (fun i : Fin 419 => (fixedNodes (fixedEntries i).node).frame=.lattice)).card=151 := by
    rw [he,Fin.card_Iio]
  have hne : (Finset.univ.filter (fun i : Fin 419 => (fixedNodes (fixedEntries i).node).frame≠.lattice))=
      Finset.Ici (⟨151,by decide⟩ : Fin 419) := by
    ext i
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_Ici]
    exact (not_congr (fixedEntries_lattice_iff i)).trans not_lt
  refine ⟨rfl,rfl,hnc,hec,?_⟩
  change (Finset.univ.filter (fun i : Fin 419 => (fixedNodes (fixedEntries i).node).frame≠.lattice)).card=268
  rw [hne,Fin.card_Ici]
  norm_num
#print axioms nodeTable_valid
#print axioms nodeTable_shape
end CatalanCore.Li2.Uniform

namespace CatalanCore.Li2
open Uniform
inductive IsDlowCandidate : ℤ → ℝ → ℝ → ℝ → Prop
  | interp (i j : Fin nodeTable.pairCount) (s : ℤ) (t r l : ℝ)
      (hp : (i,j)∈nodeTable.interpPairs)
      (hsi : (nodeTable.entryNode i).usedFor s) (hsj : (nodeTable.entryNode j).usedFor s)
      (hl : l∈Icc 0 1)
      (ht : t=l*(nodeTable.entryNode i).t+(1-l)*(nodeTable.entryNode j).t)
      (hr : l*((nodeTable.entries i).rho:ℝ)+(1-l)*((nodeTable.entries j).rho:ℝ)≤r) :
      IsDlowCandidate s t r (l*((nodeTable.entries i).lower:ℝ)+(1-l)*((nodeTable.entries j).lower:ℝ))
  | transport (i : Fin nodeTable.pairCount) (s : ℤ) (t r : ℝ) (m : ℚ)
      (hs : (nodeTable.entryNode i).usedFor s) (ht : (nodeTable.entryNode i).t≤t)
      (hm : ((nodeTable.entryNode i).frame=.lattice ∧ m∈nodeTable.slopes) ∨ m=0)
      (hr : ((nodeTable.entries i).rho:ℝ)+(4+(m:ℝ))*(t-(nodeTable.entryNode i).t)≤r) :
      IsDlowCandidate s t r (((nodeTable.entries i).lower:ℝ)+(2*(m:ℝ)-(m:ℝ)^2)*(t-(nodeTable.entryNode i).t))

theorem public_candidate {s : ℤ} {t r D : ℝ} (h : IsDlowCandidate s t r D) : Candidate nodeTable s t r D := by
  cases h with
  | interp i j s t r l hp hsi hsj hl ht hr => exact Candidate.interp i j s t r l hp hsi hsj hl ht hr
  | transport i s t r m hs ht hm hr => exact Candidate.transport i s t r m hs ht hm hr
#print axioms public_candidate
end CatalanCore.Li2
