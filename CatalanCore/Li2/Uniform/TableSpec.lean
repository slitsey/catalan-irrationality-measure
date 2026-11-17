module

public import CatalanCore.Li2.Uniform.Spec

@[expose] public section

/-! Generic pre-data table schema. Fixed literals belong to Uniform.FixedTable in W3. -/
open Set
open scoped Topology BigOperators

namespace CatalanCore.Li2.Uniform

inductive FrameKey | lattice | G2 | G3 | G4 | G15
  deriving DecidableEq
structure Node where
  magnitude : ℚ
  frame : FrameKey
structure PairEntry (N : ℕ) where
  node : Fin N
  localIndex : ℕ
  rho : ℚ
  lower : ℚ
structure NodeTable where
  nodeCount : ℕ
  pairCount : ℕ
  nodes : Fin nodeCount → Node
  entries : Fin pairCount → PairEntry nodeCount
  interpPairs : Finset (Fin pairCount × Fin pairCount)
  slopes : List ℚ
noncomputable def Node.t (k : Node) : ℝ := Real.log (1 / (k.magnitude : ℝ))
def Node.usedFor (k : Node) (s : ℤ) : Prop :=
  (s = 1 ∨ s = -1) ∧ (k.frame = .lattice ∨ s = -1)
def Node.sign (k : Node) : ℤ := if k.frame = .lattice then 1 else -1
def NodeTable.entryNode (T : NodeTable) (i : Fin T.pairCount) : Node :=
  T.nodes (T.entries i).node
noncomputable def AllowedInterp (T : NodeTable) (i j : Fin T.pairCount) : Prop :=
  (T.entryNode i).frame = (T.entryNode j).frame ∧
    (T.entryNode i).t < (T.entryNode j).t ∧
    (T.entryNode j).t - (T.entryNode i).t ≤ (4 / 5 : ℝ)
def TableValid (T : NodeTable) : Prop :=
  (∀ k, 0 < (T.nodes k).magnitude ∧ (T.nodes k).magnitude < 1) ∧
    (∀ i, 0 < (T.entries i).rho) ∧
    Function.Injective (fun i => ((T.entries i).node, (T.entries i).localIndex)) ∧
    (∀ k, ∃ i, (T.entries i).node = k) ∧
    T.slopes = [0, 1 / 4, 1 / 2, 3 / 4, 1] ∧
    (∀ i j, (i, j) ∈ T.interpPairs ↔ AllowedInterp T i j)
def CampaignTableShape (T : NodeTable) : Prop :=
  T.nodeCount = 37 ∧ T.pairCount = 419 ∧
    (Finset.univ.filter (fun k => (T.nodes k).frame = .lattice)).card = 24 ∧
    (Finset.univ.filter (fun i => (T.entryNode i).frame = .lattice)).card = 151 ∧
    (Finset.univ.filter (fun i => (T.entryNode i).frame ≠ .lattice)).card = 268

end CatalanCore.Li2.Uniform

#print axioms CatalanCore.Li2.Uniform.AllowedInterp
#print axioms CatalanCore.Li2.Uniform.TableValid
