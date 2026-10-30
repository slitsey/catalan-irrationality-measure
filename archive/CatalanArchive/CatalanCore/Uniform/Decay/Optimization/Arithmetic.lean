import CatalanCore.Uniform.Decay.PilotArithmetic
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 50
namespace CatalanCore.Uniform.Decay.Optimization
open CatalanCore.Uniform.Decay.SignedPilot
abbrev Weight := Int × Nat
abbrev State := Int × Nat × Bool
abbrev Entry := ((Int × Nat) × Nat) × Weight

def entries (table : List (Int × Nat)) (weights : List Weight) : List Entry :=
  table.zipIdx.zip weights

def indexedTerms (table : List (Int × Nat)) (weights : List Weight) : List (Nat × Int × Nat) :=
  (entries table weights).map (fun x => (x.1.2,x.2.1,x.2.2))

def streamStep (len : Nat) (s : State) (x : Entry) : State :=
  let ((tv,te),idx) := x.1
  let (n,d) := x.2
  let (v,err,ok) := s
  (v + n*tv/(d : Int), err + (n.natAbs*te+d-1)/d+1,
    ok && decide (idx < len) && decide (0 < d))

def streamExpression (table : List (Int × Nat)) (num : Int) (den : Nat)
    (weights : List Weight) : State :=
  (entries table weights).foldl (streamStep table.length)
    (num*(scale : Int)/(den : Int),1,decide (0 < den))

private theorem foldl_eq {A B : Type} (f g : A → B → A) (xs : List B)
    (h : ∀ s x, x ∈ xs → f s x = g s x) (s : A) : xs.foldl f s = xs.foldl g s := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rw [h s x (by simp)]
    exact ih (fun s y hy => h s y (by simp [hy])) _

/-- Exact equality to the original checker. No new interval/error analysis. -/
theorem evalExpression_indexedTerms (table : List (Int × Nat)) (num : Int) (den : Nat)
    (weights : List Weight) :
    evalExpression table (num,den,indexedTerms table weights) =
      streamExpression table num den weights := by
  unfold evalExpression indexedTerms streamExpression
  dsimp only
  rw [List.foldl_map]
  apply foldl_eq
  intro s x hx
  have hm := (List.of_mem_zip hx).1
  have hv := List.mem_zipIdx_iff_getElem?.mp hm
  have hd : table.getD x.1.2 (0,0) = x.1.1 := by
    rw [List.getD_eq_getElem?_getD, hv]
    rfl
  simp only [hd,streamStep]


def streamCheck (table : List (Int × Nat)) (num : Int) (den : Nat)
    (weights : List Weight) (lo hi : Int) : Bool :=
  let (v,e,ok) := streamExpression table num den weights
  ok && decide (lo ≤ v-(e : Int)) && decide (v+(e : Int) ≤ hi)

/-- Transfer a streamed check to the unchanged single-row checker. -/
theorem checkRows_stream (table : List (Int × Nat)) (num : Int) (den : Nat)
    (weights : List Weight) (lo hi : Int) :
    checkRows table [(num,den,indexedTerms table weights)] [(lo,hi)] =
      streamCheck table num den weights lo hi := by
  simp only [checkRows,evalExpression_indexedTerms]
  simp [streamCheck]

#print axioms evalExpression_indexedTerms
end CatalanCore.Uniform.Decay.Optimization

