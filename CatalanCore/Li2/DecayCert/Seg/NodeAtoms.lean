module
public import CatalanCore.Li2.DecayCert.Seg.NodeEnergy
public import CatalanCore.Li2.DecayCert.Assembly.Base
@[expose] public section
set_option Elab.async false
open Polynomial MeasureTheory Set Filter Topology
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert.Seg
open CatalanCore.Li2.DecayCert CatalanCore.Li2.Decay
noncomputable section

variable {AC : Type} [AtomProj AC]

def nodeAtomLineCell (x : AC × AtomOut) (hwidth : 0 ≤ AtomProj.right x.1-AtomProj.left x.1) : LineCell where
  start := x.2.start (AtomProj.left x.1) (AtomProj.right x.1)
  len := AtomProj.right x.1-AtomProj.left x.1
  dir := x.2.dir
  a := x.2.a
  b := x.2.b
  len_nonneg := hwidth
  direction := by cases hb : x.2.backwards <;> simp [AtomOut.dir,hb]

theorem nodeAtomLineCell_support (x : AC × AtomOut) (hwidth : 0 ≤ AtomProj.right x.1-AtomProj.left x.1) :
    (nodeAtomLineCell x hwidth).support=Icc ((AtomProj.left x.1:ℚ):ℝ) ((AtomProj.right x.1:ℚ):ℝ) := by
  cases hb : x.2.backwards
  · rw [LineCell.support_forward _ (by simp [nodeAtomLineCell,AtomOut.dir,hb])]
    simp only [nodeAtomLineCell,AtomOut.start,hb,Bool.false_eq_true,ite_false,Rat.cast_sub]
    congr 2 <;> ring
  · rw [LineCell.support_backward _ (by simp [nodeAtomLineCell,AtomOut.dir,hb])]
    simp only [nodeAtomLineCell,AtomOut.start,hb,ite_true,Rat.cast_sub]
    congr 2 <;> ring

theorem nodeAtomLineCell_ne_of_order (x y : AC × AtomOut)
    (hx : 0 ≤ AtomProj.right x.1-AtomProj.left x.1) (hy : 0 ≤ AtomProj.right y.1-AtomProj.left y.1)
    (hstrict : AtomProj.left x.1 < AtomProj.right x.1) (horder : AtomProj.right x.1 ≤ AtomProj.left y.1) :
    nodeAtomLineCell x hx ≠ nodeAtomLineCell y hy := by
  intro he
  have hs := congrArg LineCell.support he
  rw [nodeAtomLineCell_support,nodeAtomLineCell_support] at hs
  have hstrictR : ((AtomProj.left x.1:ℚ):ℝ)<((AtomProj.right x.1:ℚ):ℝ) := by exact_mod_cast hstrict
  have horderR : ((AtomProj.right x.1:ℚ):ℝ) ≤ ((AtomProj.left y.1:ℚ):ℝ) := by exact_mod_cast horder
  have hmid : (((AtomProj.left x.1:ℚ):ℝ)+((AtomProj.right x.1:ℚ):ℝ))/2 ∈
      Icc ((AtomProj.left x.1:ℚ):ℝ) ((AtomProj.right x.1:ℚ):ℝ) := by constructor <;> linarith
  rw [hs] at hmid
  linarith [hmid.1]

theorem nodeLinePartition_exists (cs : List (AC × AtomOut)) (hc : nodeAtomCoverCheck cs=true) :
    ∃ P : LinePartition 1 4,P.cells.map (fun c => (c.start,c.len,c.dir,c.a,c.b))=
      cs.map (fun c => (c.2.start (AtomProj.left c.1) (AtomProj.right c.1),
        AtomProj.right c.1-AtomProj.left c.1,c.2.dir,c.2.a,c.2.b)) := by
  have hcheck : chainCheck 1 4 (cs.map (fun c => (⟨AtomProj.left c.1,AtomProj.right c.1⟩:QInterval)))=true := hc
  have hs := chainCheck_sound 1 4 (cs.map (fun c => (⟨AtomProj.left c.1,AtomProj.right c.1⟩:QInterval))) hcheck
  have hstrict (c : AC × AtomOut) (hc : c ∈ cs) : AtomProj.left c.1 < AtomProj.right c.1 :=
    (hs.2.2.1 ⟨AtomProj.left c.1,AtomProj.right c.1⟩ (List.mem_map.mpr ⟨c,hc,rfl⟩)).2.1
  have hwidth (c : AC × AtomOut) (hc : c ∈ cs) : 0 ≤ AtomProj.right c.1-AtomProj.left c.1 :=
    sub_nonneg.mpr (hstrict c hc).le
  let cells := cs.attach.map (fun c => nodeAtomLineCell c.val (hwidth c.val c.property))
  have hordered : cs.Pairwise (fun c d => AtomProj.right c.1 ≤ AtomProj.left d.1) := by
    simpa only [List.pairwise_map] using hs.2.1
  have horderedA : cs.attach.Pairwise (fun c d => AtomProj.right c.val.1 ≤ AtomProj.left d.val.1) := by
    apply List.pairwise_iff_getElem.mpr
    intro i j hi hj hij
    have hi' : i < cs.length := by simpa using hi
    have hj' : j < cs.length := by simpa using hj
    simpa only [List.getElem_attach] using (List.Pairwise.rel_getElem_of_lt hi' hj' hordered hij)
  have hnodup : cells.Nodup := by
    rw [List.nodup_iff_pairwise_ne,List.pairwise_map]
    apply horderedA.imp
    intro a b hab
    exact nodeAtomLineCell_ne_of_order a.val b.val _ _ (hstrict a.val a.property) hab
  have hunion : (⋃ c ∈ cells,c.support)=⋃ c ∈ cs,Icc ((AtomProj.left c.1:ℚ):ℝ) ((AtomProj.right c.1:ℚ):ℝ) := by
    ext x
    constructor
    · intro hx
      rcases mem_iUnion.1 hx with ⟨c,hxc⟩
      rcases mem_iUnion.1 hxc with ⟨hc,hxc⟩
      rcases List.mem_map.mp hc with ⟨a,ha,rfl⟩
      rw [nodeAtomLineCell_support] at hxc
      exact mem_iUnion.2 ⟨a.val,mem_iUnion.2 ⟨a.property,hxc⟩⟩
    · intro hx
      rcases mem_iUnion.1 hx with ⟨c,hxc⟩
      rcases mem_iUnion.1 hxc with ⟨hc,hxc⟩
      refine mem_iUnion.2 ⟨nodeAtomLineCell c (hwidth c hc),mem_iUnion.2 ⟨?_,?_⟩⟩
      · exact List.mem_map.mpr ⟨⟨c,hc⟩,by simp,rfl⟩
      · rwa [nodeAtomLineCell_support]
  have hcover : (⋃ c ∈ cells,c.support)=Icc (1:ℝ) 4 := by
    rw [hunion]
    have hh := chainCheck_closed_cover 1 4 (cs.map (fun c => (⟨AtomProj.left c.1,AtomProj.right c.1⟩:QInterval)))
      (by norm_num) hcheck
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
      exact hne (congrArg (fun q : {c // c ∈ cs} => nodeAtomLineCell q.val (hwidth q.val q.property)) hab)
    rw [nodeAtomLineCell_support,nodeAtomLineCell_support]
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
  simpa only [Function.comp_def,nodeAtomLineCell] using (List.attach_map_val (l:=cs)
    (f:=fun c : AC × AtomOut => (c.2.start (AtomProj.left c.1) (AtomProj.right c.1),
      AtomProj.right c.1-AtomProj.left c.1,c.2.dir,c.2.a,c.2.b)))

theorem nodeAtomPosSum_upper (z : ℚ) (b : BentInput) (cs : List (AC × AtomOut))
    (hc : nodeAtomCoverCheck cs=true) (hline : NodeAtomLinePhysical z b cs) (ρ lam : ℚ) :
    atomPenalty (z:ℝ) (ρ:ℝ) b.data.dual.σ (lam:ℝ) ≤ (nodeAtomPosSum cs ρ lam:ℝ) := by
  obtain ⟨P,hP⟩ := nodeLinePartition_exists cs hc
  have hcell : ∀ c∈P.cells,∀ u∈Icc 0 (c.len:ℝ),
      omega (z:ℝ) ((c.start:ℝ)+(c.dir:ℝ)*u)-2*U b.data.dual.σ (-(((c.start:ℝ)+(c.dir:ℝ)*u:ℝ):ℂ))≤(c.a:ℝ)+(c.b:ℝ)*u := by
    intro c hc u hu
    have hm : (c.start,c.len,c.dir,c.a,c.b)∈cs.map (fun c => (c.2.start (AtomProj.left c.1) (AtomProj.right c.1),
        AtomProj.right c.1-AtomProj.left c.1,c.2.dir,c.2.a,c.2.b)) := by
      rw [← hP]
      exact List.mem_map.mpr ⟨c,hc,rfl⟩
    rcases List.mem_map.mp hm with ⟨a,ha,he⟩
    simp only [Prod.mk.injEq] at he
    rcases he with ⟨hs,hl,hd',ha',hb'⟩
    rw [← hs,← hd',← ha',← hb']
    exact hline a ha u (by simpa only [← hl] using hu)
  have hf : Continuous (fun x : ℝ => omega (z:ℝ) x-2*U b.data.dual.σ (-(x:ℂ))) := by
    convert continuous_A_real (z:ℝ) 0 b.data.dual using 1
    funext x
    simp only [A,sub_zero]
  have hi := Dsum_spec _ P hf.continuousOn hcell ρ lam
  have hsum : P.posSumQ ρ lam=nodeAtomPosSum cs ρ lam := by
    have he := congrArg (fun xs : List (ℚ×ℚ×ℚ×ℚ×ℚ) =>
      (xs.map (fun q => linePos q.2.2.2.1 q.2.2.2.2 q.2.1 (ρ+lam))).sum) hP
    simpa only [LinePartition.posSumQ,nodeAtomPosSum,List.map_map,Function.comp_def] using he
  rw [hsum] at hi
  unfold atomPenalty
  convert hi using 1
  congr 1
  funext x
  congr 1
  unfold A
  ring
#print axioms nodeLinePartition_exists
#print axioms nodeAtomPosSum_upper
end
end CatalanCore.Li2.DecayCert.Seg
