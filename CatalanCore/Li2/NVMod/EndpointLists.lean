module
public import CatalanCore.Li2.NVMod.AtZero
public import CatalanCore.Linalg.Bareiss
@[expose] public section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
open Polynomial Finset
open scoped BigOperators
namespace CatalanCore.Li2.NVMod
noncomputable section

def positivePoles (A : TypeKey) : List ℕ :=
  (List.range (A.c+1)).filter (fun m=>1≤m ∧ m∈poleSet A)
def descendingPoles (A : TypeKey) : List ℕ := (positivePoles A).reverse
def topPoles (A : TypeKey) : List ℕ := (descendingPoles A).take A.size
def zeroOrder (A : TypeKey) : ℤ := ((topPoles A).map (fun m=>1-(m:ℤ))).sum
def diffProduct : List ℕ→ℚ
  | []=>1
  | m::ms=>(ms.map (fun k=>((m:ℚ)-k)^2)).prod*diffProduct ms
def zeroLead (A : TypeKey) : ℚ := ((topPoles A).map (residue A)).prod*diffProduct (topPoles A)

theorem mem_positivePoles (A : TypeKey) (m : ℕ) : m∈positivePoles A↔1≤m ∧ m∈poleSet A := by
  simp only [positivePoles,List.mem_filter,List.mem_range,decide_eq_true_eq]
  constructor
  · exact fun h=>h.2
  · intro hm
    refine ⟨?_,hm⟩
    have hp := hm.2
    cases hk : A.kind <;> simp only [poleSet,hk,Finset.mem_Ico,Finset.mem_Ioc] at hp <;> omega

theorem descendingPoles_pairwise (A : TypeKey) : (descendingPoles A).Pairwise (·>·) := by
  exact (List.pairwise_lt_range.filter _).reverse

def topPole (A : TypeKey) (hs : (topPoles A).length=A.size) (i : Fin A.size) : ℕ :=
  (topPoles A).get ⟨i.val,by rw [hs]; exact i.isLt⟩

theorem topPole_mem (A : TypeKey) (hs : (topPoles A).length=A.size) (i : Fin A.size) :
    topPole A hs i∈poleSet A ∧ 1≤topPole A hs i := by
  have ht : topPole A hs i∈topPoles A := List.get_mem _ _
  have hd : topPole A hs i∈descendingPoles A := List.mem_of_mem_take ht
  have hp : topPole A hs i∈positivePoles A := List.mem_reverse.mp hd
  exact ((mem_positivePoles A _).mp hp).symm

theorem topPole_strictAnti (A : TypeKey) (hs : (topPoles A).length=A.size) :
    StrictAnti (topPole A hs) := by
  intro i j hij
  have hp : (topPoles A).Pairwise (·>·) := (descendingPoles_pairwise A).take
  exact hp.rel_get_of_lt (by exact hij)

theorem ofFn_topPole (A : TypeKey) (hs : (topPoles A).length=A.size) :
    List.ofFn (topPole A hs)=topPoles A := by
  apply List.ext_get
  · simpa using hs.symm
  · intro i hi1 hi2
    simp only [List.get_ofFn,topPole]
    congr 1

theorem topPole_top (A : TypeKey) (hs : (topPoles A).length=A.size)
    (m : ℕ) (hm : m∈poleSet A) (hm1 : 1≤m) (hr : m∉Set.range (topPole A hs))
    (i : Fin A.size) : m<topPole A hs i := by
  have hmfull : m∈descendingPoles A := List.mem_reverse.mpr ((mem_positivePoles A m).mpr ⟨hm1,hm⟩)
  have hmnot : m∉topPoles A := by
    rw [←ofFn_topPole A hs,List.mem_ofFn]
    exact hr
  have hmjoin : m∈topPoles A++(descendingPoles A).drop A.size := by
    simpa only [topPoles,List.take_append_drop] using hmfull
  have hmdrop : m∈(descendingPoles A).drop A.size := (List.mem_append.mp hmjoin).resolve_left hmnot
  have hpair : (topPoles A++(descendingPoles A).drop A.size).Pairwise (·>·) := by
    simpa only [topPoles,List.take_append_drop] using descendingPoles_pairwise A
  exact (List.pairwise_append.mp hpair).2.2 _ (List.get_mem _ _) _ hmdrop

theorem diffProduct_ofFn (n : ℕ) (f : Fin n→ℕ) :
    diffProduct (List.ofFn f)=
      ∏ i : Fin n,∏ j∈Finset.univ.filter (fun j=>i<j),((f i:ℚ)-f j)^2 := by
  induction n with
  | zero => simp [diffProduct]
  | succ n ih =>
    rw [List.ofFn_succ,diffProduct]
    simp only [bind_pure_comp,List.map_map,List.map_ofFn,List.prod_ofFn]
    rw [ih]
    simp [List.prod_ofFn,Finset.prod_filter,Fin.prod_univ_succ,Function.comp_def]

theorem hankel_zero_lead (A : TypeKey) (hs : (topPoles A).length=A.size) :
    Oge (atZero (constantRF A)) (zeroOrder A) ∧
      (atZero (constantRF A)).coeff (zeroOrder A)=zeroLead A := by
  have hh := hankel_at_zero A (topPole A hs) (topPole_mem A hs) (topPole_strictAnti A hs)
    (topPole_top A hs)
  have hord : zeroOrder A=Finset.sum Finset.univ (fun i : Fin A.size=>1-(topPole A hs i:ℤ)) := by
    rw [zeroOrder,←ofFn_topPole A hs]
    simp only [bind_pure_comp]
    change (((List.ofFn (topPole A hs)).map (fun m : ℕ=>(m:ℤ))).map (fun m : ℤ=>1-m)).sum=_
    rw [List.map_map,List.map_ofFn,List.sum_ofFn]
    rfl
  have hlead : zeroLead A=(∏ i : Fin A.size,residue A (topPole A hs i))*
      ∏ i : Fin A.size,∏ j∈Finset.univ.filter (fun j=>i<j),
        ((topPole A hs i:ℚ)-topPole A hs j)^2 := by
    rw [zeroLead,←ofFn_topPole A hs,List.map_ofFn,List.prod_ofFn,diffProduct_ofFn]
    rfl
  rw [hord,hlead]
  exact hh

#print axioms topPole_top
#print axioms diffProduct_ofFn
#print axioms hankel_zero_lead
end
end CatalanCore.Li2.NVMod
