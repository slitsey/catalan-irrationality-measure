module
public import CatalanCore.Li2.DecayCert.Covers.Geometry
public import CatalanCore.Li2.DecayCert.Covers.Partition
@[expose] public section
set_option Elab.async false
open Polynomial MeasureTheory Set Filter Topology
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert
noncomputable section

theorem chainCheck_closed_cover (a b : ℚ) (cs : List QInterval) (hab : a < b) (hc : chainCheck a b cs=true) :
    Icc (a:ℝ) (b:ℝ)=⋃ c ∈ cs,Icc (c.left:ℝ) (c.right:ℝ) := by
  have h := chainCheck_sound a b cs hc
  ext x
  constructor
  · intro hx
    by_cases he : x=(a:ℝ)
    · cases cs with
      | nil => have hh : a=b := of_decide_eq_true hc; linarith
      | cons c cs =>
        have hh := hc
        simp only [chainCheck,Bool.and_eq_true,decide_eq_true_eq] at hh
        refine mem_iUnion.2 ⟨c,mem_iUnion.2 ⟨List.mem_cons_self,?_⟩⟩
        have hl : (c.left:ℝ)=(a:ℝ) := by exact_mod_cast hh.1.1
        have hr : (c.left:ℝ)<(c.right:ℝ) := by exact_mod_cast hh.1.2.1
        constructor <;> linarith
    · have hxo : x ∈ Ioc (a:ℝ) (b:ℝ) := ⟨lt_of_le_of_ne hx.1 (Ne.symm he),hx.2⟩
      rw [h.2.2.2] at hxo
      rcases mem_iUnion.1 hxo with ⟨c,hxc⟩
      rcases mem_iUnion.1 hxc with ⟨hc,hxc⟩
      exact mem_iUnion.2 ⟨c,mem_iUnion.2 ⟨hc,hxc.1.le,hxc.2⟩⟩
  · intro hx
    rcases mem_iUnion.1 hx with ⟨c,hxc⟩
    rcases mem_iUnion.1 hxc with ⟨hc,hxc⟩
    have hb := h.2.2.1 c hc
    have hlR : (a:ℝ) ≤ (c.left:ℝ) := by exact_mod_cast hb.1
    have hrR : (c.right:ℝ) ≤ (b:ℝ) := by exact_mod_cast hb.2.2
    exact ⟨hlR.trans hxc.1,hxc.2.trans hrR⟩

def atomLineCell (c : AtomCell) (hwidth : 0 ≤ c.right-c.left) : LineCell where
  start := c.start
  len := c.right-c.left
  dir := c.dir
  a := c.witness.a
  b := c.witness.b
  len_nonneg := hwidth
  direction := by cases hb : c.backwards <;> simp [AtomCell.dir,hb]

theorem atomLineCell_support (c : AtomCell) (hwidth : 0 ≤ c.right-c.left) :
    (atomLineCell c hwidth).support=Icc (c.left:ℝ) (c.right:ℝ) := by
  cases hb : c.backwards
  · rw [LineCell.support_forward _ (by simp [atomLineCell,AtomCell.dir,hb])]
    simp only [atomLineCell,AtomCell.start,hb,Bool.false_eq_true,ite_false,Rat.cast_sub]
    congr 2 <;> ring
  · rw [LineCell.support_backward _ (by simp [atomLineCell,AtomCell.dir,hb])]
    simp only [atomLineCell,AtomCell.start,hb,ite_true,Rat.cast_sub]
    congr 2 <;> ring

theorem atomLineCell_ne_of_order (a b : AtomCell) (ha : 0 ≤ a.right-a.left) (hb : 0 ≤ b.right-b.left)
    (hstrict : a.left < a.right) (horder : a.right ≤ b.left) : atomLineCell a ha ≠ atomLineCell b hb := by
  intro he
  have hs := congrArg LineCell.support he
  rw [atomLineCell_support,atomLineCell_support] at hs
  have hstrictR : (a.left:ℝ)<(a.right:ℝ) := by exact_mod_cast hstrict
  have horderR : (a.right:ℝ) ≤ (b.left:ℝ) := by exact_mod_cast horder
  have hmid : ((a.left:ℝ)+(a.right:ℝ))/2 ∈ Icc (a.left:ℝ) (a.right:ℝ) := by constructor <;> linarith
  rw [hs] at hmid
  linarith [hmid.1]

theorem checkedLinePartition_exists (z : ℚ) (d : SegmentDatum) (cs : List AtomCell)
    (hc : atomCoverCheck z d cs=true) :
    ∃ P : LinePartition 1 4,P.cells.map (fun c => (c.start,c.len,c.dir,c.a,c.b))=
      cs.map (fun c => (c.start,c.right-c.left,c.dir,c.witness.a,c.witness.b)) := by
  have hcheck : chainCheck 1 4 (cs.map (fun c => (⟨c.left,c.right⟩:QInterval)))=true := by
    have h := hc
    simp only [atomCoverCheck,Bool.and_eq_true] at h
    exact h.1
  have hs := chainCheck_sound 1 4 (cs.map (fun c => (⟨c.left,c.right⟩:QInterval))) hcheck
  have hstrict (c : AtomCell) (hc : c ∈ cs) : c.left < c.right :=
    (hs.2.2.1 ⟨c.left,c.right⟩ (List.mem_map.mpr ⟨c,hc,rfl⟩)).2.1
  have hwidth (c : AtomCell) (hc : c ∈ cs) : 0 ≤ c.right-c.left := sub_nonneg.mpr (hstrict c hc).le
  let cells := cs.attach.map (fun c => atomLineCell c.val (hwidth c.val c.property))
  have hordered : cs.Pairwise (fun c d => c.right ≤ d.left) := by simpa only [List.pairwise_map] using hs.2.1
  have horderedA : cs.attach.Pairwise (fun c d => c.val.right ≤ d.val.left) := by
    apply List.pairwise_iff_getElem.mpr
    intro i j hi hj hij
    have hi' : i < cs.length := by simpa using hi
    have hj' : j < cs.length := by simpa using hj
    simpa only [List.getElem_attach] using (List.Pairwise.rel_getElem_of_lt hi' hj' hordered hij)
  have hnodup : cells.Nodup := by
    rw [List.nodup_iff_pairwise_ne,List.pairwise_map]
    apply horderedA.imp
    intro a b hab
    exact atomLineCell_ne_of_order a.val b.val _ _ (hstrict a.val a.property) hab
  have hunion : (⋃ c ∈ cells,c.support)=⋃ c ∈ cs,Icc (c.left:ℝ) (c.right:ℝ) := by
    ext x
    constructor
    · intro hx
      rcases mem_iUnion.1 hx with ⟨c,hxc⟩
      rcases mem_iUnion.1 hxc with ⟨hc,hxc⟩
      rcases List.mem_map.mp hc with ⟨a,ha,rfl⟩
      rw [atomLineCell_support] at hxc
      exact mem_iUnion.2 ⟨a.val,mem_iUnion.2 ⟨a.property,hxc⟩⟩
    · intro hx
      rcases mem_iUnion.1 hx with ⟨c,hxc⟩
      rcases mem_iUnion.1 hxc with ⟨hc,hxc⟩
      refine mem_iUnion.2 ⟨atomLineCell c (hwidth c hc),mem_iUnion.2 ⟨?_,?_⟩⟩
      · exact List.mem_map.mpr ⟨⟨c,hc⟩,by simp,rfl⟩
      · rwa [atomLineCell_support]
  have hcover : (⋃ c ∈ cells,c.support)=Icc (1:ℝ) 4 := by
    rw [hunion]
    have hh := chainCheck_closed_cover 1 4 (cs.map (fun c => (⟨c.left,c.right⟩:QInterval))) (by norm_num) hcheck
    norm_num only [Rat.cast_ofNat] at hh
    rw [hh]
    ext x
    simp
  have hnull : ∀ c ∈ cells,∀ e ∈ cells,c ≠ e → volume (c.support ∩ e.support)=0 := by
    intro c hc e he hne
    rcases List.mem_map.mp hc with ⟨a,ha,rfl⟩
    rcases List.mem_map.mp he with ⟨b,hb,rfl⟩
    rcases List.getElem_of_mem ha with ⟨i,hi,hei⟩
    rcases List.getElem_of_mem hb with ⟨j,hj,hej⟩
    have hij : i ≠ j := by
      intro hij
      have hidx : cs.attach[i] = cs.attach[j] := by cases hij; rfl
      have hab : a=b := hei.symm.trans (hidx.trans hej)
      exact hne (congrArg (fun q : {c // c ∈ cs} => atomLineCell q.val (hwidth q.val q.property)) hab)
    rw [atomLineCell_support,atomLineCell_support]
    rcases lt_or_gt_of_ne hij with hlt | hlt
    · have hord := List.Pairwise.rel_getElem_of_lt hi hj horderedA hlt
      rw [hei,hej] at hord
      apply ordered_Icc_inter_null volume (by intro x; simp)
      exact_mod_cast hord
    · have hord := List.Pairwise.rel_getElem_of_lt hj hi horderedA hlt
      rw [hej,hei] at hord
      rw [inter_comm]
      apply ordered_Icc_inter_null volume (by intro x; simp)
      exact_mod_cast hord
  refine ⟨⟨cells,hnodup,hcover,hnull⟩,?_⟩
  change (cells.map (fun c => (c.start,c.len,c.dir,c.a,c.b)))=_
  dsimp only [cells]
  rw [List.map_map]
  simpa only [Function.comp_def,atomLineCell] using (List.attach_map_val (l:=cs)
    (f:=fun c : AtomCell => (c.start,c.right-c.left,c.dir,c.witness.a,c.witness.b)))

noncomputable def linePartitionOfCheckedCells (z : ℚ) (d : SegmentDatum) (cs : List AtomCell)
    (hc : atomCoverCheck z d cs=true) : LinePartition 1 4 := Classical.choose (checkedLinePartition_exists z d cs hc)
#print axioms chainCheck_closed_cover
#print axioms atomLineCell_support
#print axioms atomLineCell_ne_of_order
#print axioms checkedLinePartition_exists
end
end CatalanCore.Li2.DecayCert
