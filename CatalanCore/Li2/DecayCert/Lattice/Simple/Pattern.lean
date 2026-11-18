module
public import CatalanCore.Li2.DecayCert.RealCells.Sign
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 800000
open Polynomial MeasureTheory Set Filter Topology
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert.LatticeSimple
open CatalanCore.Li2.Decay

structure Pattern where
  gaps : ℕ
  node : ℕ → ℚ
  positive : ℕ → Bool
  delta : ℕ → ℚ

def Pattern.check (s : Pattern) (a b : ℚ) : Bool :=
  decide (0 < s.gaps ∧ s.node 0=a ∧ s.node s.gaps=b) &&
  (List.range (s.gaps+1)).all (fun j=>(List.range j).all (fun i=>decide (s.node i < s.node j))) &&
  (List.range (s.gaps-1)).all (fun i=>decide (s.positive (i+1)= !s.positive i)) &&
  (List.range (s.gaps-1)).all (fun i=>decide (0 < s.delta (i+1) ∧
    2*s.delta (i+1) < min (s.node (i+1)-s.node i) (s.node (i+2)-s.node (i+1))))

theorem Pattern.check_parts (s : Pattern) (a b : ℚ) (hc : s.check a b=true) :
    (0 < s.gaps ∧ s.node 0=a ∧ s.node s.gaps=b) ∧
    (∀ i j,i < j → j ≤ s.gaps → s.node i < s.node j) ∧
    (∀ i,i+1 < s.gaps → s.positive (i+1)= !s.positive i) ∧
    (∀ i,0 < i → i < s.gaps → 0 < s.delta i ∧
      2*s.delta i < min (s.node i-s.node (i-1)) (s.node (i+1)-s.node i)) := by
  have hh:=hc
  simp only [Pattern.check,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true] at hh
  rcases hh with ⟨⟨⟨hshape,hinc⟩,halt⟩,hdelta⟩
  refine ⟨hshape,?_,?_,?_⟩
  · intro i j hij hj
    exact hinc j (List.mem_range.mpr (by omega)) i (List.mem_range.mpr hij)
  · intro i hi
    exact halt i (List.mem_range.mpr (by omega))
  · intro i hi hig
    have h:=hdelta (i-1) (List.mem_range.mpr (by omega))
    have he : i-1+1=i := by omega
    have he' : i-1+2=i+1 := by omega
    simpa only [he,he'] using h

noncomputable def Pattern.toSignPartition (s : Pattern) (a b : ℚ) (hc : s.check a b=true) :
    SignPartition (a:ℝ) (b:ℝ) where
  gaps:=s.gaps
  gaps_pos:=(s.check_parts a b hc).1.1
  node:=fun i=>(s.node i:ℝ)
  first:=congrArg (fun q : ℚ=>(q:ℝ)) (s.check_parts a b hc).1.2.1
  last:=congrArg (fun q : ℚ=>(q:ℝ)) (s.check_parts a b hc).1.2.2
  increasing:=by
    intro i j hij hj
    exact_mod_cast (s.check_parts a b hc).2.1 i j hij hj
  positive:=s.positive
  alternating:=(s.check_parts a b hc).2.2.1
  delta:=fun i=>(s.delta i:ℝ)
  delta_pos:=by
    intro i hi hig
    exact_mod_cast ((s.check_parts a b hc).2.2.2 i hi hig).1
  separated:=by
    intro i hi hig
    exact_mod_cast ((s.check_parts a b hc).2.2.2 i hi hig).2

noncomputable def Pattern.rootCount (s : Pattern) : ℕ := s.gaps-1

def Pattern.plusCap (s : Pattern) (cap : ℕ → ℚ) : ℚ :=
  ((List.range s.gaps).map (fun i=>if s.positive i then cap i else 0)).sum

def Pattern.rootCap (s : Pattern) (ep em : ℕ → ℚ) : ℚ :=
  ((List.range (s.gaps-1)).map (fun i=>2*s.delta (i+1)*ep i+s.delta (i+1)*em i)).sum

theorem list_range_sum {M : Type*} [AddCommMonoid M] (f : ℕ→M) (n : ℕ) :
    ((List.range n).map f).sum=∑i∈Finset.range n,f i := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ,ih,Finset.sum_range_succ]

theorem Pattern.plusIntegral_le (s : Pattern) (a b : ℚ) (hc : s.check a b=true)
    (f : ℝ → ℝ) (cap : ℕ → ℚ)
    (hcap : ∀ i,i < s.gaps → s.positive i=true → 
      (∫x in (s.node i:ℝ)..(s.node (i+1):ℝ),f x) ≤ (cap i:ℝ)) :
    (s.toSignPartition a b hc).plusIntegral f ≤ (s.plusCap cap:ℝ) := by
  unfold SignPartition.plusIntegral Pattern.plusCap
  rw [Rat.cast_list_sum]
  simp only [List.map_map,Function.comp_def,list_range_sum]
  apply Finset.sum_le_sum
  intro i hi
  by_cases hp : s.positive i=true
  · simpa [Pattern.toSignPartition,hp] using hcap i (Finset.mem_range.mp hi) hp
  · simp [Pattern.toSignPartition,hp]

theorem Pattern.rootError_eq (s : Pattern) (a b : ℚ) (hc : s.check a b=true)
    (ep em : ℕ → ℚ) :
    (s.toSignPartition a b hc).rootError (fun i=>(ep i:ℝ)) (fun i=>(em i:ℝ))=
      (s.rootCap ep em:ℝ) := by
  have he := Fin.sum_univ_eq_sum_range
    (fun i : ℕ=>2*s.delta (i+1)*ep i+s.delta (i+1)*em i) (s.gaps-1)
  rw [←list_range_sum] at he
  change (∑i : Fin (s.gaps-1),
    ((2:ℝ)*(s.delta (i+1):ℝ)*(ep i:ℝ)+(s.delta (i+1):ℝ)*(em i:ℝ)))=(s.rootCap ep em:ℝ)
  exact_mod_cast he

theorem signPattern_bound (s : Pattern) (a b total : ℚ) (hc : s.check a b=true)
    (hab : a ≤ b) (f : ℝ → ℝ) (hf : ContinuousOn f (Icc (a:ℝ) (b:ℝ)))
    (hsgn : (s.toSignPartition a b hc).signAway f) (cap ep em : ℕ → ℚ)
    (hcap : ∀ i,i < s.gaps → s.positive i=true → 
      (∫x in (s.node i:ℝ)..(s.node (i+1):ℝ),f x) ≤ (cap i:ℝ))
    (hep : ∀ i,i < s.gaps-1 → 0 ≤ ep i) (hem : ∀ i,i < s.gaps-1 → 0 ≤ em i)
    (hp : ∀ i : Fin (s.gaps-1),∀x∈(s.toSignPartition a b hc).rootCell i,f x ≤ (ep i:ℝ))
    (hm : ∀ i : Fin (s.gaps-1),∀x∈(s.toSignPartition a b hc).rootCell i,-f x ≤ (em i:ℝ))
    (hscalar : decide (s.plusCap cap+s.rootCap ep em ≤ total)=true) :
    (∫x in (a:ℝ)..(b:ℝ),pos (f x)) ≤ (total:ℝ) := by
  have habR : (a:ℝ) ≤ (b:ℝ) := by exact_mod_cast hab
  have hb := int_pos_le_signPattern (a:ℝ) (b:ℝ) habR f hf (s.toSignPartition a b hc)
    hsgn (fun i=>(ep i:ℝ)) (fun i=>(em i:ℝ))
    (fun i=>by exact_mod_cast hep i i.isLt) (fun i=>by exact_mod_cast hem i i.isLt) hp hm
  rw [s.rootError_eq a b hc ep em] at hb
  have hc' := s.plusIntegral_le a b hc f cap hcap
  have hs : (s.plusCap cap:ℝ)+(s.rootCap ep em:ℝ) ≤ (total:ℝ) := by
    exact_mod_cast (of_decide_eq_true hscalar)
  linarith
#print axioms Pattern.toSignPartition
#print axioms signPattern_bound
end CatalanCore.Li2.DecayCert.LatticeSimple
