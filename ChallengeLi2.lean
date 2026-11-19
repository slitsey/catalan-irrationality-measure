module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Order.Interval.Finset.Fin

@[expose] public section

/-! The Li₂ challenge uses the 37 nodes and 419 decay entries of the published table,
written as rational literals. The solution proves the single theorem below. -/

set_option Elab.async false
set_option maxRecDepth 100000
open Set

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
def NodeTable.entryNode (T : NodeTable) (i : Fin T.pairCount) : Node :=
  T.nodes (T.entries i).node

namespace FixedData

def magnitude0 : ℚ := ((([Int.ofNat (nat_lit 1)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 2)] : List ℤ)).headD 0:ℚ)
def node0 : Node := ⟨magnitude0,.lattice⟩
def magnitude1 : ℚ := ((([Int.ofNat (nat_lit 1)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 3)] : List ℤ)).headD 0:ℚ)
def node1 : Node := ⟨magnitude1,.lattice⟩
def magnitude2 : ℚ := ((([Int.ofNat (nat_lit 1)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 4)] : List ℤ)).headD 0:ℚ)
def node2 : Node := ⟨magnitude2,.lattice⟩
def magnitude3 : ℚ := ((([Int.ofNat (nat_lit 1)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 5)] : List ℤ)).headD 0:ℚ)
def node3 : Node := ⟨magnitude3,.lattice⟩
def magnitude4 : ℚ := ((([Int.ofNat (nat_lit 1)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 6)] : List ℤ)).headD 0:ℚ)
def node4 : Node := ⟨magnitude4,.lattice⟩
def magnitude5 : ℚ := ((([Int.ofNat (nat_lit 1)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 8)] : List ℤ)).headD 0:ℚ)
def node5 : Node := ⟨magnitude5,.lattice⟩
def magnitude6 : ℚ := ((([Int.ofNat (nat_lit 2)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 15)] : List ℤ)).headD 0:ℚ)
def node6 : Node := ⟨magnitude6,.lattice⟩
def magnitude7 : ℚ := ((([Int.ofNat (nat_lit 2)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 17)] : List ℤ)).headD 0:ℚ)
def node7 : Node := ⟨magnitude7,.lattice⟩
def magnitude8 : ℚ := ((([Int.ofNat (nat_lit 2)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 13)] : List ℤ)).headD 0:ℚ)
def node8 : Node := ⟨magnitude8,.lattice⟩
def magnitude9 : ℚ := ((([Int.ofNat (nat_lit 2)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 19)] : List ℤ)).headD 0:ℚ)
def node9 : Node := ⟨magnitude9,.lattice⟩
def magnitude10 : ℚ := ((([Int.ofNat (nat_lit 2)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 23)] : List ℤ)).headD 0:ℚ)
def node10 : Node := ⟨magnitude10,.lattice⟩
def magnitude11 : ℚ := ((([Int.ofNat (nat_lit 2)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 25)] : List ℤ)).headD 0:ℚ)
def node11 : Node := ⟨magnitude11,.lattice⟩
def magnitude12 : ℚ := ((([Int.ofNat (nat_lit 2)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 33)] : List ℤ)).headD 0:ℚ)
def node12 : Node := ⟨magnitude12,.lattice⟩
def magnitude13 : ℚ := ((([Int.ofNat (nat_lit 2)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 37)] : List ℤ)).headD 0:ℚ)
def node13 : Node := ⟨magnitude13,.lattice⟩
def magnitude14 : ℚ := ((([Int.ofNat (nat_lit 2)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 39)] : List ℤ)).headD 0:ℚ)
def node14 : Node := ⟨magnitude14,.lattice⟩
def magnitude15 : ℚ := ((([Int.ofNat (nat_lit 1)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 10)] : List ℤ)).headD 0:ℚ)
def node15 : Node := ⟨magnitude15,.lattice⟩
def magnitude16 : ℚ := ((([Int.ofNat (nat_lit 1)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 148)] : List ℤ)).headD 0:ℚ)
def node16 : Node := ⟨magnitude16,.lattice⟩
def magnitude17 : ℚ := ((([Int.ofNat (nat_lit 1)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 14)] : List ℤ)).headD 0:ℚ)
def node17 : Node := ⟨magnitude17,.lattice⟩
def magnitude18 : ℚ := ((([Int.ofNat (nat_lit 1)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 20)] : List ℤ)).headD 0:ℚ)
def node18 : Node := ⟨magnitude18,.lattice⟩
def magnitude19 : ℚ := ((([Int.ofNat (nat_lit 1)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 26)] : List ℤ)).headD 0:ℚ)
def node19 : Node := ⟨magnitude19,.lattice⟩
def magnitude20 : ℚ := ((([Int.ofNat (nat_lit 1)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 33)] : List ℤ)).headD 0:ℚ)
def node20 : Node := ⟨magnitude20,.lattice⟩
def magnitude21 : ℚ := ((([Int.ofNat (nat_lit 1)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 403)] : List ℤ)).headD 0:ℚ)
def node21 : Node := ⟨magnitude21,.lattice⟩
def magnitude22 : ℚ := ((([Int.ofNat (nat_lit 1)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 55)] : List ℤ)).headD 0:ℚ)
def node22 : Node := ⟨magnitude22,.lattice⟩
def magnitude23 : ℚ := ((([Int.ofNat (nat_lit 1)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 90)] : List ℤ)).headD 0:ℚ)
def node23 : Node := ⟨magnitude23,.lattice⟩
def magnitude24 : ℚ := ((([Int.ofNat (nat_lit 1)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 2)] : List ℤ)).headD 0:ℚ)
def node24 : Node := ⟨magnitude24,.G2⟩
def magnitude25 : ℚ := ((([Int.ofNat (nat_lit 1)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 3)] : List ℤ)).headD 0:ℚ)
def node25 : Node := ⟨magnitude25,.G3⟩
def magnitude26 : ℚ := ((([Int.ofNat (nat_lit 1)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 4)] : List ℤ)).headD 0:ℚ)
def node26 : Node := ⟨magnitude26,.G4⟩
def magnitude27 : ℚ := ((([Int.ofNat (nat_lit 1)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 13)] : List ℤ)).headD 0:ℚ)
def node27 : Node := ⟨magnitude27,.G15⟩
def magnitude28 : ℚ := ((([Int.ofNat (nat_lit 1)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 20)] : List ℤ)).headD 0:ℚ)
def node28 : Node := ⟨magnitude28,.G15⟩
def magnitude29 : ℚ := ((([Int.ofNat (nat_lit 1)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 33)] : List ℤ)).headD 0:ℚ)
def node29 : Node := ⟨magnitude29,.G15⟩
def magnitude30 : ℚ := ((([Int.ofNat (nat_lit 1)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 6)] : List ℤ)).headD 0:ℚ)
def node30 : Node := ⟨magnitude30,.G15⟩
def magnitude31 : ℚ := ((([Int.ofNat (nat_lit 2)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 11)] : List ℤ)).headD 0:ℚ)
def node31 : Node := ⟨magnitude31,.G15⟩
def magnitude32 : ℚ := ((([Int.ofNat (nat_lit 2)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 15)] : List ℤ)).headD 0:ℚ)
def node32 : Node := ⟨magnitude32,.G15⟩
def magnitude33 : ℚ := ((([Int.ofNat (nat_lit 2)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 25)] : List ℤ)).headD 0:ℚ)
def node33 : Node := ⟨magnitude33,.G15⟩
def magnitude34 : ℚ := ((([Int.ofNat (nat_lit 2)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 41)] : List ℤ)).headD 0:ℚ)
def node34 : Node := ⟨magnitude34,.G15⟩
def magnitude35 : ℚ := ((([Int.ofNat (nat_lit 2)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 65)] : List ℤ)).headD 0:ℚ)
def node35 : Node := ⟨magnitude35,.G15⟩
def magnitude36 : ℚ := ((([Int.ofNat (nat_lit 1)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 5)] : List ℤ)).headD 0:ℚ)
def node36 : Node := ⟨magnitude36,.G4⟩
def nodeValues : List Node := [node0,node1,node2,node3,node4,node5,node6,node7,node8,node9,node10,node11,node12,node13,node14,node15,node16,node17,node18,node19,node20,node21,node22,node23,node24,node25,node26,node27,node28,node29,node30,node31,node32,node33,node34,node35,node36]
theorem nodeValues_length : nodeValues.length=37 := by rfl
def fixedNodes (i : Fin 37) : Node := nodeValues[i.val]'(by rw [nodeValues_length]; exact i.isLt)

def entryQ0 : ℚ := ((([Int.ofNat (nat_lit 29)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 2)] : List ℤ)).headD 0:ℚ)
def entryQ1 : ℚ := ((([Int.negSucc (nat_lit 464852112238019382)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 100000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ2 : ℚ := ((([Int.ofNat (nat_lit 61)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 4)] : List ℤ)).headD 0:ℚ)
def entryQ3 : ℚ := ((([Int.negSucc (nat_lit 229923413531863742)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 50000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ4 : ℚ := ((([Int.ofNat (nat_lit 31)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 2)] : List ℤ)).headD 0:ℚ)
def entryQ5 : ℚ := ((([Int.negSucc (nat_lit 459361275526233186)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 100000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ6 : ℚ := ((([Int.ofNat (nat_lit 63)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 4)] : List ℤ)).headD 0:ℚ)
def entryQ7 : ℚ := ((([Int.negSucc (nat_lit 9186485096697008)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 2000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ8 : ℚ := ((([Int.ofNat (nat_lit 15)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 1)] : List ℤ)).headD 0:ℚ)
def entryQ9 : ℚ := ((([Int.negSucc (nat_lit 460895440635140456)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 100000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ10 : ℚ := ((([Int.ofNat (nat_lit 16)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 1)] : List ℤ)).headD 0:ℚ)
def entryQ11 : ℚ := ((([Int.negSucc (nat_lit 4593158459155280768)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 1000000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ12 : ℚ := ((([Int.ofNat (nat_lit 35)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 2)] : List ℤ)).headD 0:ℚ)
def entryQ13 : ℚ := ((([Int.negSucc (nat_lit 262433672871241212)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 100000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ14 : ℚ := ((([Int.ofNat (nat_lit 37)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 2)] : List ℤ)).headD 0:ℚ)
def entryQ15 : ℚ := ((([Int.negSucc (nat_lit 6659850798186092)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 4000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ16 : ℚ := ((([Int.ofNat (nat_lit 20)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 1)] : List ℤ)).headD 0:ℚ)
def entryQ17 : ℚ := ((([Int.negSucc (nat_lit 14881628031130302)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 15625000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ18 : ℚ := ((([Int.ofNat (nat_lit 41)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 2)] : List ℤ)).headD 0:ℚ)
def entryQ19 : ℚ := ((([Int.negSucc (nat_lit 537924297486366210)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 1000000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ20 : ℚ := ((([Int.ofNat (nat_lit 22)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 1)] : List ℤ)).headD 0:ℚ)
def entryQ21 : ℚ := ((([Int.ofNat (nat_lit 147217855222220659)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 1000000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ22 : ℚ := ((([Int.ofNat (nat_lit 45)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 2)] : List ℤ)).headD 0:ℚ)
def entryQ23 : ℚ := ((([Int.ofNat (nat_lit 6289135191464343)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 50000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ24 : ℚ := ((([Int.ofNat (nat_lit 47)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 2)] : List ℤ)).headD 0:ℚ)
def entryQ25 : ℚ := ((([Int.ofNat (nat_lit 97979953965457307)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 500000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ26 : ℚ := ((([Int.ofNat (nat_lit 237)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 10)] : List ℤ)).headD 0:ℚ)
def entryQ27 : ℚ := ((([Int.ofNat (nat_lit 200450144360276693)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 1000000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ28 : ℚ := ((([Int.ofNat (nat_lit 477)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 20)] : List ℤ)).headD 0:ℚ)
def entryQ29 : ℚ := ((([Int.ofNat (nat_lit 20188373953878259)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 100000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ30 : ℚ := ((([Int.ofNat (nat_lit 23)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 1)] : List ℤ)).headD 0:ℚ)
def entryQ31 : ℚ := ((([Int.ofNat (nat_lit 21429190225654819)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 125000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ32 : ℚ := ((([Int.ofNat (nat_lit 49)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 2)] : List ℤ)).headD 0:ℚ)
def entryQ33 : ℚ := ((([Int.ofNat (nat_lit 201998417818239627)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 1000000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ34 : ℚ := ((([Int.ofNat (nat_lit 24)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 1)] : List ℤ)).headD 0:ℚ)
def entryQ35 : ℚ := ((([Int.ofNat (nat_lit 221963873650900849)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 500000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ36 : ℚ := ((([Int.ofNat (nat_lit 97)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 4)] : List ℤ)).headD 0:ℚ)
def entryQ37 : ℚ := ((([Int.ofNat (nat_lit 12138653203998949)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 25000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ38 : ℚ := ((([Int.ofNat (nat_lit 9799931862480773)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 20000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ39 : ℚ := ((([Int.ofNat (nat_lit 99)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 4)] : List ℤ)).headD 0:ℚ)
def entryQ40 : ℚ := ((([Int.ofNat (nat_lit 98099290316412773)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 200000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ41 : ℚ := ((([Int.ofNat (nat_lit 47649986542606453)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 100000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ42 : ℚ := ((([Int.ofNat (nat_lit 25)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 1)] : List ℤ)).headD 0:ℚ)
def entryQ43 : ℚ := ((([Int.ofNat (nat_lit 223)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 10)] : List ℤ)).headD 0:ℚ)
def entryQ44 : ℚ := ((([Int.negSucc (nat_lit 170573903228162178)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 1000000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ45 : ℚ := ((([Int.ofNat (nat_lit 451)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 20)] : List ℤ)).headD 0:ℚ)
def entryQ46 : ℚ := ((([Int.negSucc (nat_lit 79076011798516562)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 500000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ47 : ℚ := ((([Int.ofNat (nat_lit 114)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 5)] : List ℤ)).headD 0:ℚ)
def entryQ48 : ℚ := ((([Int.negSucc (nat_lit 150514827314696328)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 1000000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ49 : ℚ := ((([Int.ofNat (nat_lit 457)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 20)] : List ℤ)).headD 0:ℚ)
def entryQ50 : ℚ := ((([Int.negSucc (nat_lit 93471745908987512)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 625000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ51 : ℚ := ((([Int.ofNat (nat_lit 229)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 10)] : List ℤ)).headD 0:ℚ)
def entryQ52 : ℚ := ((([Int.negSucc (nat_lit 1860019786949988)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 12500000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ53 : ℚ := ((([Int.ofNat (nat_lit 459)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 20)] : List ℤ)).headD 0:ℚ)
def entryQ54 : ℚ := ((([Int.negSucc (nat_lit 5928960918633806)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 40000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ55 : ℚ := ((([Int.ofNat (nat_lit 461)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 20)] : List ℤ)).headD 0:ℚ)
def entryQ56 : ℚ := ((([Int.negSucc (nat_lit 1476244001016700890)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 10000000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ57 : ℚ := ((([Int.ofNat (nat_lit 231)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 10)] : List ℤ)).headD 0:ℚ)
def entryQ58 : ℚ := ((([Int.negSucc (nat_lit 7378191051888570)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 50000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ59 : ℚ := ((([Int.ofNat (nat_lit 463)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 20)] : List ℤ)).headD 0:ℚ)
def entryQ60 : ℚ := ((([Int.negSucc (nat_lit 73781504589347060)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 500000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ61 : ℚ := ((([Int.ofNat (nat_lit 116)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 5)] : List ℤ)).headD 0:ℚ)
def entryQ62 : ℚ := ((([Int.ofNat (nat_lit 93)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 4)] : List ℤ)).headD 0:ℚ)
def entryQ63 : ℚ := ((([Int.ofNat (nat_lit 233)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 10)] : List ℤ)).headD 0:ℚ)
def entryQ64 : ℚ := ((([Int.ofNat (nat_lit 471)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 20)] : List ℤ)).headD 0:ℚ)
def entryQ65 : ℚ := ((([Int.negSucc (nat_lit 73916625360096606)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 500000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ66 : ℚ := ((([Int.ofNat (nat_lit 479)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 20)] : List ℤ)).headD 0:ℚ)
def entryQ67 : ℚ := ((([Int.ofNat (nat_lit 336348124695372797)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 500000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ68 : ℚ := ((([Int.ofNat (nat_lit 121)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 5)] : List ℤ)).headD 0:ℚ)
def entryQ69 : ℚ := ((([Int.ofNat (nat_lit 347442974753174431)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 500000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ70 : ℚ := ((([Int.ofNat (nat_lit 489)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 20)] : List ℤ)).headD 0:ℚ)
def entryQ71 : ℚ := ((([Int.ofNat (nat_lit 71186586571008471)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 100000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ72 : ℚ := ((([Int.ofNat (nat_lit 142937179692171353)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 200000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ73 : ℚ := ((([Int.ofNat (nat_lit 491)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 20)] : List ℤ)).headD 0:ℚ)
def entryQ74 : ℚ := ((([Int.ofNat (nat_lit 143468425811947717)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 200000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ75 : ℚ := ((([Int.ofNat (nat_lit 123)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 5)] : List ℤ)).headD 0:ℚ)
def entryQ76 : ℚ := ((([Int.ofNat (nat_lit 359889584396299969)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 500000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ77 : ℚ := ((([Int.ofNat (nat_lit 493)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 20)] : List ℤ)).headD 0:ℚ)
def entryQ78 : ℚ := ((([Int.ofNat (nat_lit 36101824855103549531)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 50000000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ79 : ℚ := ((([Int.ofNat (nat_lit 247)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 10)] : List ℤ)).headD 0:ℚ)
def entryQ80 : ℚ := ((([Int.ofNat (nat_lit 724113394056754857)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 1000000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ81 : ℚ := ((([Int.ofNat (nat_lit 726014291028130823)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 1000000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ82 : ℚ := ((([Int.ofNat (nat_lit 124)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 5)] : List ℤ)).headD 0:ℚ)
def entryQ83 : ℚ := ((([Int.ofNat (nat_lit 727712313724475853)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 1000000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ84 : ℚ := ((([Int.ofNat (nat_lit 497)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 20)] : List ℤ)).headD 0:ℚ)
def entryQ85 : ℚ := ((([Int.ofNat (nat_lit 3646262433383324559)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 5000000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ86 : ℚ := ((([Int.ofNat (nat_lit 249)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 10)] : List ℤ)).headD 0:ℚ)
def entryQ87 : ℚ := ((([Int.ofNat (nat_lit 29224120378645631)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 40000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ88 : ℚ := ((([Int.ofNat (nat_lit 499)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 20)] : List ℤ)).headD 0:ℚ)
def entryQ89 : ℚ := ((([Int.ofNat (nat_lit 36587931021201587)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 50000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ90 : ℚ := ((([Int.ofNat (nat_lit 126)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 5)] : List ℤ)).headD 0:ℚ)
def entryQ91 : ℚ := ((([Int.ofNat (nat_lit 367416352677002407)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 500000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ92 : ℚ := ((([Int.ofNat (nat_lit 524041093710704821)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 500000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ93 : ℚ := ((([Int.ofNat (nat_lit 501)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 20)] : List ℤ)).headD 0:ℚ)
def entryQ94 : ℚ := ((([Int.ofNat (nat_lit 53705588864403927)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 50000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ95 : ℚ := ((([Int.ofNat (nat_lit 253)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 10)] : List ℤ)).headD 0:ℚ)
def entryQ96 : ℚ := ((([Int.ofNat (nat_lit 109490598677174851)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 100000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ97 : ℚ := ((([Int.ofNat (nat_lit 507)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 20)] : List ℤ)).headD 0:ℚ)
def entryQ98 : ℚ := ((([Int.ofNat (nat_lit 21969199517024979)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 20000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ99 : ℚ := ((([Int.ofNat (nat_lit 127)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 5)] : List ℤ)).headD 0:ℚ)
def entryQ100 : ℚ := ((([Int.ofNat (nat_lit 1101905936463959127)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 1000000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ101 : ℚ := ((([Int.ofNat (nat_lit 509)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 20)] : List ℤ)).headD 0:ℚ)
def entryQ102 : ℚ := ((([Int.ofNat (nat_lit 22102109301229787)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 20000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ103 : ℚ := ((([Int.ofNat (nat_lit 51)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 2)] : List ℤ)).headD 0:ℚ)
def entryQ104 : ℚ := ((([Int.ofNat (nat_lit 277032110660122439)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 250000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ105 : ℚ := ((([Int.ofNat (nat_lit 511)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 20)] : List ℤ)).headD 0:ℚ)
def entryQ106 : ℚ := ((([Int.ofNat (nat_lit 55547763776861427)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 50000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ107 : ℚ := ((([Int.ofNat (nat_lit 128)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 5)] : List ℤ)).headD 0:ℚ)
def entryQ108 : ℚ := ((([Int.ofNat (nat_lit 4454394842104749)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 4000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ109 : ℚ := ((([Int.ofNat (nat_lit 513)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 20)] : List ℤ)).headD 0:ℚ)
def entryQ110 : ℚ := ((([Int.ofNat (nat_lit 22321753974841309)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 20000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ111 : ℚ := ((([Int.ofNat (nat_lit 257)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 10)] : List ℤ)).headD 0:ℚ)
def entryQ112 : ℚ := ((([Int.ofNat (nat_lit 111840351384526699)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 100000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ113 : ℚ := ((([Int.ofNat (nat_lit 103)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 4)] : List ℤ)).headD 0:ℚ)
def entryQ114 : ℚ := ((([Int.ofNat (nat_lit 1120485693004829153)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 1000000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ115 : ℚ := ((([Int.ofNat (nat_lit 129)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 5)] : List ℤ)).headD 0:ℚ)
def entryQ116 : ℚ := ((([Int.ofNat (nat_lit 11224144939740099869)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 10000000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ117 : ℚ := ((([Int.ofNat (nat_lit 521)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 20)] : List ℤ)).headD 0:ℚ)
def entryQ118 : ℚ := ((([Int.ofNat (nat_lit 564675425672564931)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 500000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ119 : ℚ := ((([Int.ofNat (nat_lit 60348571058241263)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 50000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ120 : ℚ := ((([Int.ofNat (nat_lit 123413390903737747)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 100000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ121 : ℚ := ((([Int.ofNat (nat_lit 7847516224247107)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 6250000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ122 : ℚ := ((([Int.ofNat (nat_lit 259)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 10)] : List ℤ)).headD 0:ℚ)
def entryQ123 : ℚ := ((([Int.ofNat (nat_lit 1015725380415967)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 800000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ124 : ℚ := ((([Int.ofNat (nat_lit 519)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 20)] : List ℤ)).headD 0:ℚ)
def entryQ125 : ℚ := ((([Int.ofNat (nat_lit 15842076766455567)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 12500000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ126 : ℚ := ((([Int.ofNat (nat_lit 127830113189543689)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 100000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ127 : ℚ := ((([Int.ofNat (nat_lit 261)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 10)] : List ℤ)).headD 0:ℚ)
def entryQ128 : ℚ := ((([Int.ofNat (nat_lit 16025754601440067)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 12500000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ129 : ℚ := ((([Int.ofNat (nat_lit 523)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 20)] : List ℤ)).headD 0:ℚ)
def entryQ130 : ℚ := ((([Int.ofNat (nat_lit 128310018339116841)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 100000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ131 : ℚ := ((([Int.ofNat (nat_lit 131)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 5)] : List ℤ)).headD 0:ℚ)
def entryQ132 : ℚ := ((([Int.ofNat (nat_lit 32160995810974953)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 25000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ133 : ℚ := ((([Int.ofNat (nat_lit 105)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 4)] : List ℤ)).headD 0:ℚ)
def entryQ134 : ℚ := ((([Int.ofNat (nat_lit 64359647360917839)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 50000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ135 : ℚ := ((([Int.ofNat (nat_lit 263)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 10)] : List ℤ)).headD 0:ℚ)
def entryQ136 : ℚ := ((([Int.ofNat (nat_lit 503507784594659)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 390625000000000)] : List ℤ)).headD 0:ℚ)
def entryQ137 : ℚ := ((([Int.ofNat (nat_lit 527)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 20)] : List ℤ)).headD 0:ℚ)
def entryQ138 : ℚ := ((([Int.ofNat (nat_lit 129059673106029777)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 100000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ139 : ℚ := ((([Int.ofNat (nat_lit 132)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 5)] : List ℤ)).headD 0:ℚ)
def entryQ140 : ℚ := ((([Int.ofNat (nat_lit 12919998664793659)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 10000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ141 : ℚ := ((([Int.ofNat (nat_lit 529)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 20)] : List ℤ)).headD 0:ℚ)
def entryQ142 : ℚ := ((([Int.ofNat (nat_lit 129326098943803867)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 100000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ143 : ℚ := ((([Int.ofNat (nat_lit 26)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 1)] : List ℤ)).headD 0:ℚ)
def entryQ144 : ℚ := ((([Int.ofNat (nat_lit 15944492187506453)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 12500000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ145 : ℚ := ((([Int.ofNat (nat_lit 21191485058148087)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 12500000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ146 : ℚ := ((([Int.ofNat (nat_lit 267)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 10)] : List ℤ)).headD 0:ℚ)
def entryQ147 : ℚ := ((([Int.ofNat (nat_lit 17266080303500399041)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 10000000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ148 : ℚ := ((([Int.ofNat (nat_lit 539)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 20)] : List ℤ)).headD 0:ℚ)
def entryQ149 : ℚ := ((([Int.ofNat (nat_lit 175289841756587539)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 100000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ150 : ℚ := ((([Int.ofNat (nat_lit 541)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 20)] : List ℤ)).headD 0:ℚ)
def entryQ151 : ℚ := ((([Int.ofNat (nat_lit 44051531514847387)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 25000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ152 : ℚ := ((([Int.ofNat (nat_lit 271)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 10)] : List ℤ)).headD 0:ℚ)
def entryQ153 : ℚ := ((([Int.ofNat (nat_lit 35328176752851713)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 20000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ154 : ℚ := ((([Int.ofNat (nat_lit 543)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 20)] : List ℤ)).headD 0:ℚ)
def entryQ155 : ℚ := ((([Int.ofNat (nat_lit 1770563340392219311)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 1000000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ156 : ℚ := ((([Int.ofNat (nat_lit 136)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 5)] : List ℤ)).headD 0:ℚ)
def entryQ157 : ℚ := ((([Int.ofNat (nat_lit 22180952104486569)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 12500000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ158 : ℚ := ((([Int.ofNat (nat_lit 109)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 4)] : List ℤ)).headD 0:ℚ)
def entryQ159 : ℚ := ((([Int.ofNat (nat_lit 11114149855194991)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 6250000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ160 : ℚ := ((([Int.ofNat (nat_lit 273)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 10)] : List ℤ)).headD 0:ℚ)
def entryQ161 : ℚ := ((([Int.ofNat (nat_lit 89092575774796829)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 50000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ162 : ℚ := ((([Int.ofNat (nat_lit 547)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 20)] : List ℤ)).headD 0:ℚ)
def entryQ163 : ℚ := ((([Int.ofNat (nat_lit 178527233610845581)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 100000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ164 : ℚ := ((([Int.ofNat (nat_lit 137)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 5)] : List ℤ)).headD 0:ℚ)
def entryQ165 : ℚ := ((([Int.ofNat (nat_lit 71540307545298377)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 40000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ166 : ℚ := ((([Int.ofNat (nat_lit 549)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 20)] : List ℤ)).headD 0:ℚ)
def entryQ167 : ℚ := ((([Int.ofNat (nat_lit 179153207413587633)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 100000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ168 : ℚ := ((([Int.ofNat (nat_lit 277)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 10)] : List ℤ)).headD 0:ℚ)
def entryQ169 : ℚ := ((([Int.ofNat (nat_lit 36082774630820127)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 20000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ170 : ℚ := ((([Int.ofNat (nat_lit 27)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 1)] : List ℤ)).headD 0:ℚ)
def entryQ171 : ℚ := ((([Int.ofNat (nat_lit 175757402798266673)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 100000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ172 : ℚ := ((([Int.ofNat (nat_lit 23435575677652341)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 12500000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ173 : ℚ := ((([Int.ofNat (nat_lit 190963575957808897)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 100000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ174 : ℚ := ((([Int.ofNat (nat_lit 97190921988625771)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 50000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ175 : ℚ := ((([Int.ofNat (nat_lit 138)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 5)] : List ℤ)).headD 0:ℚ)
def entryQ176 : ℚ := ((([Int.ofNat (nat_lit 48838392896965941)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 25000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ177 : ℚ := ((([Int.ofNat (nat_lit 553)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 20)] : List ℤ)).headD 0:ℚ)
def entryQ178 : ℚ := ((([Int.ofNat (nat_lit 196304614819067613)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 100000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ179 : ℚ := ((([Int.ofNat (nat_lit 196300380784120523)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 100000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ180 : ℚ := ((([Int.ofNat (nat_lit 111)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 4)] : List ℤ)).headD 0:ℚ)
def entryQ181 : ℚ := ((([Int.ofNat (nat_lit 492899589510462329)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 250000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ182 : ℚ := ((([Int.ofNat (nat_lit 139)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 5)] : List ℤ)).headD 0:ℚ)
def entryQ183 : ℚ := ((([Int.ofNat (nat_lit 197656108042224549)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 100000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ184 : ℚ := ((([Int.ofNat (nat_lit 557)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 20)] : List ℤ)).headD 0:ℚ)
def entryQ185 : ℚ := ((([Int.ofNat (nat_lit 24742346899887071)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 12500000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ186 : ℚ := ((([Int.ofNat (nat_lit 279)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 10)] : List ℤ)).headD 0:ℚ)
def entryQ187 : ℚ := ((([Int.ofNat (nat_lit 198299007326540763)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 100000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ188 : ℚ := ((([Int.ofNat (nat_lit 559)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 20)] : List ℤ)).headD 0:ℚ)
def entryQ189 : ℚ := ((([Int.ofNat (nat_lit 39729804069096129)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 20000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ190 : ℚ := ((([Int.ofNat (nat_lit 561)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 20)] : List ℤ)).headD 0:ℚ)
def entryQ191 : ℚ := ((([Int.ofNat (nat_lit 99641806629749391)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 50000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ192 : ℚ := ((([Int.ofNat (nat_lit 281)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 10)] : List ℤ)).headD 0:ℚ)
def entryQ193 : ℚ := ((([Int.ofNat (nat_lit 7983020486002141)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 4000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ194 : ℚ := ((([Int.ofNat (nat_lit 563)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 20)] : List ℤ)).headD 0:ℚ)
def entryQ195 : ℚ := ((([Int.ofNat (nat_lit 199850725310874583)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 100000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ196 : ℚ := ((([Int.ofNat (nat_lit 141)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 5)] : List ℤ)).headD 0:ℚ)
def entryQ197 : ℚ := ((([Int.ofNat (nat_lit 200108010130979743)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 100000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ198 : ℚ := ((([Int.ofNat (nat_lit 28)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 1)] : List ℤ)).headD 0:ℚ)
def entryQ199 : ℚ := ((([Int.ofNat (nat_lit 99487343308639339)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 50000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ200 : ℚ := ((([Int.ofNat (nat_lit 196160549516997733)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 100000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ201 : ℚ := ((([Int.ofNat (nat_lit 2000377162944169173)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 1000000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ202 : ℚ := ((([Int.ofNat (nat_lit 63190871096339)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 31250000000000)] : List ℤ)).headD 0:ℚ)
def entryQ203 : ℚ := ((([Int.ofNat (nat_lit 203736249544218841)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 100000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ204 : ℚ := ((([Int.ofNat (nat_lit 101858330923955449)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 50000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ205 : ℚ := ((([Int.ofNat (nat_lit 101767200701507873)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 50000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ206 : ℚ := ((([Int.ofNat (nat_lit 205114705069062849)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 100000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ207 : ℚ := ((([Int.ofNat (nat_lit 204826276344965603)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 100000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ208 : ℚ := ((([Int.ofNat (nat_lit 41282454971716113)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 20000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ209 : ℚ := ((([Int.ofNat (nat_lit 12911143282939679)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 6250000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ210 : ℚ := ((([Int.ofNat (nat_lit 103583906325186903)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 50000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ211 : ℚ := ((([Int.ofNat (nat_lit 2587661146404433)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 1250000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ212 : ℚ := ((([Int.ofNat (nat_lit 113)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 4)] : List ℤ)).headD 0:ℚ)
def entryQ213 : ℚ := ((([Int.ofNat (nat_lit 207859467656573821)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 100000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ214 : ℚ := ((([Int.ofNat (nat_lit 283)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 10)] : List ℤ)).headD 0:ℚ)
def entryQ215 : ℚ := ((([Int.ofNat (nat_lit 2075802500216599639)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 1000000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ216 : ℚ := ((([Int.ofNat (nat_lit 567)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 20)] : List ℤ)).headD 0:ℚ)
def entryQ217 : ℚ := ((([Int.ofNat (nat_lit 104242756499875259)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 50000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ218 : ℚ := ((([Int.ofNat (nat_lit 142)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 5)] : List ℤ)).headD 0:ℚ)
def entryQ219 : ℚ := ((([Int.ofNat (nat_lit 208225433460817887)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 100000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ220 : ℚ := ((([Int.ofNat (nat_lit 569)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 20)] : List ℤ)).headD 0:ℚ)
def entryQ221 : ℚ := ((([Int.ofNat (nat_lit 209038273788430981)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 100000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ222 : ℚ := ((([Int.ofNat (nat_lit 205839837514173639)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 100000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ223 : ℚ := ((([Int.ofNat (nat_lit 11477675948479997)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 20000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ224 : ℚ := ((([Int.ofNat (nat_lit 67)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 2)] : List ℤ)).headD 0:ℚ)
def entryQ225 : ℚ := ((([Int.ofNat (nat_lit 375886797228736821)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 100000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ226 : ℚ := ((([Int.ofNat (nat_lit 73)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 2)] : List ℤ)).headD 0:ℚ)
def entryQ227 : ℚ := ((([Int.ofNat (nat_lit 4653781375820009341)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 1000000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ228 : ℚ := ((([Int.ofNat (nat_lit 77)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 2)] : List ℤ)).headD 0:ℚ)
def entryQ229 : ℚ := ((([Int.ofNat (nat_lit 492978170428383731)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 100000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ230 : ℚ := ((([Int.ofNat (nat_lit 117)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 5)] : List ℤ)).headD 0:ℚ)
def entryQ231 : ℚ := ((([Int.ofNat (nat_lit 179555424135286571)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 200000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ232 : ℚ := ((([Int.ofNat (nat_lit 859146550435054571)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 1000000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ233 : ℚ := ((([Int.ofNat (nat_lit 223885880968830893)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 250000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ234 : ℚ := ((([Int.ofNat (nat_lit 29)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 1)] : List ℤ)).headD 0:ℚ)
def entryQ235 : ℚ := ((([Int.ofNat (nat_lit 2482543310154709473)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 1000000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ236 : ℚ := ((([Int.ofNat (nat_lit 30)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 1)] : List ℤ)).headD 0:ℚ)
def entryQ237 : ℚ := ((([Int.ofNat (nat_lit 6418767682681867)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 2500000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ238 : ℚ := ((([Int.ofNat (nat_lit 903136292873497719)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 1000000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ239 : ℚ := ((([Int.ofNat (nat_lit 14312590757418851)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 10000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ240 : ℚ := ((([Int.ofNat (nat_lit 57)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 2)] : List ℤ)).headD 0:ℚ)
def entryQ241 : ℚ := ((([Int.ofNat (nat_lit 2534131036744789187)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 1000000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ242 : ℚ := ((([Int.ofNat (nat_lit 61)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 2)] : List ℤ)).headD 0:ℚ)
def entryQ243 : ℚ := ((([Int.ofNat (nat_lit 288175933432773529)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 100000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ244 : ℚ := ((([Int.ofNat (nat_lit 99994373942340753)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 20000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ245 : ℚ := ((([Int.ofNat (nat_lit 83)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 2)] : List ℤ)).headD 0:ℚ)
def entryQ246 : ℚ := ((([Int.ofNat (nat_lit 58344017610232471)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 10000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ247 : ℚ := ((([Int.ofNat (nat_lit 87)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 2)] : List ℤ)).headD 0:ℚ)
def entryQ248 : ℚ := ((([Int.ofNat (nat_lit 121976399502802507)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 20000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ249 : ℚ := ((([Int.ofNat (nat_lit 47955886095258117)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 20000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ250 : ℚ := ((([Int.ofNat (nat_lit 63)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 2)] : List ℤ)).headD 0:ℚ)
def entryQ251 : ℚ := ((([Int.ofNat (nat_lit 42075669489343941)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 12500000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ252 : ℚ := ((([Int.ofNat (nat_lit 3653930278096959887)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 1000000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ253 : ℚ := ((([Int.ofNat (nat_lit 31)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 1)] : List ℤ)).headD 0:ℚ)
def entryQ254 : ℚ := ((([Int.ofNat (nat_lit 309781285589842741)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 100000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ255 : ℚ := ((([Int.ofNat (nat_lit 34)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 1)] : List ℤ)).headD 0:ℚ)
def entryQ256 : ℚ := ((([Int.ofNat (nat_lit 402732334213346889)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 100000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ257 : ℚ := ((([Int.ofNat (nat_lit 36)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 1)] : List ℤ)).headD 0:ℚ)
def entryQ258 : ℚ := ((([Int.ofNat (nat_lit 215477965748259843)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 50000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ259 : ℚ := ((([Int.ofNat (nat_lit 27)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 2)] : List ℤ)).headD 0:ℚ)
def entryQ260 : ℚ := ((([Int.negSucc (nat_lit 4500866734538660)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 1000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ261 : ℚ := ((([Int.ofNat (nat_lit 55)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 4)] : List ℤ)).headD 0:ℚ)
def entryQ262 : ℚ := ((([Int.negSucc (nat_lit 4005347421310212)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 1000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ263 : ℚ := ((([Int.ofNat (nat_lit 14)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 1)] : List ℤ)).headD 0:ℚ)
def entryQ264 : ℚ := ((([Int.negSucc (nat_lit 440660509127092)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 125000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ265 : ℚ := ((([Int.ofNat (nat_lit 57)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 4)] : List ℤ)).headD 0:ℚ)
def entryQ266 : ℚ := ((([Int.negSucc (nat_lit 7654862203517230)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 2500000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ267 : ℚ := ((([Int.negSucc (nat_lit 654065877552552)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 250000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ268 : ℚ := ((([Int.ofNat (nat_lit 59)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 4)] : List ℤ)).headD 0:ℚ)
def entryQ269 : ℚ := ((([Int.negSucc (nat_lit 21892988792295966)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 10000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ270 : ℚ := ((([Int.negSucc (nat_lit 8911436371588898)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 5000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ271 : ℚ := ((([Int.negSucc (nat_lit 1745862592710506)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 1250000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ272 : ℚ := ((([Int.negSucc (nat_lit 2068619623231112)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 2000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ273 : ℚ := ((([Int.negSucc (nat_lit 1394923796892200)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 2000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ274 : ℚ := ((([Int.negSucc (nat_lit 19467834232574462)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 50000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ275 : ℚ := ((([Int.ofNat (nat_lit 65)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 4)] : List ℤ)).headD 0:ℚ)
def entryQ276 : ℚ := ((([Int.negSucc (nat_lit 719203704411580)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 6250000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ277 : ℚ := ((([Int.ofNat (nat_lit 33)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 2)] : List ℤ)).headD 0:ℚ)
def entryQ278 : ℚ := ((([Int.ofNat (nat_lit 11346453159402803)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 100000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ279 : ℚ := ((([Int.ofNat (nat_lit 67)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 4)] : List ℤ)).headD 0:ℚ)
def entryQ280 : ℚ := ((([Int.ofNat (nat_lit 12263572206099073)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 100000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ281 : ℚ := ((([Int.ofNat (nat_lit 17)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 1)] : List ℤ)).headD 0:ℚ)
def entryQ282 : ℚ := ((([Int.ofNat (nat_lit 69)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 4)] : List ℤ)).headD 0:ℚ)
def entryQ283 : ℚ := ((([Int.ofNat (nat_lit 71)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 4)] : List ℤ)).headD 0:ℚ)
def entryQ284 : ℚ := ((([Int.ofNat (nat_lit 18)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 1)] : List ℤ)).headD 0:ℚ)
def entryQ285 : ℚ := ((([Int.ofNat (nat_lit 73)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 4)] : List ℤ)).headD 0:ℚ)
def entryQ286 : ℚ := ((([Int.negSucc (nat_lit 1994987315586998)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 500000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ287 : ℚ := ((([Int.negSucc (nat_lit 704113538576706)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 200000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ288 : ℚ := ((([Int.negSucc (nat_lit 15334870906413928)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 5000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ289 : ℚ := ((([Int.negSucc (nat_lit 164372369026248)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 62500000000000)] : List ℤ)).headD 0:ℚ)
def entryQ290 : ℚ := ((([Int.negSucc (nat_lit 1381484645765300)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 625000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ291 : ℚ := ((([Int.negSucc (nat_lit 9045998988189140)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 5000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ292 : ℚ := ((([Int.negSucc (nat_lit 7137793651975182)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 5000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ293 : ℚ := ((([Int.negSucc (nat_lit 5333940012156442)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 5000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ294 : ℚ := ((([Int.negSucc (nat_lit 1821322557892290)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 2500000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ295 : ℚ := ((([Int.negSucc (nat_lit 207443953954360)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 500000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ296 : ℚ := ((([Int.negSucc (nat_lit 12877762584931642)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 100000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ297 : ℚ := ((([Int.ofNat (nat_lit 12520155191515053)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 100000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ298 : ℚ := ((([Int.ofNat (nat_lit 841063429864643)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 2500000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ299 : ℚ := ((([Int.ofNat (nat_lit 1732487742583769)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 5000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ300 : ℚ := ((([Int.ofNat (nat_lit 75)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 4)] : List ℤ)).headD 0:ℚ)
def entryQ301 : ℚ := ((([Int.ofNat (nat_lit 19)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 1)] : List ℤ)).headD 0:ℚ)
def entryQ302 : ℚ := ((([Int.ofNat (nat_lit 77)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 4)] : List ℤ)).headD 0:ℚ)
def entryQ303 : ℚ := ((([Int.ofNat (nat_lit 39)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 2)] : List ℤ)).headD 0:ℚ)
def entryQ304 : ℚ := ((([Int.ofNat (nat_lit 79)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 4)] : List ℤ)).headD 0:ℚ)
def entryQ305 : ℚ := ((([Int.negSucc (nat_lit 73142665452862)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 20000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ306 : ℚ := ((([Int.negSucc (nat_lit 50057287114126)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 15625000000000)] : List ℤ)).headD 0:ℚ)
def entryQ307 : ℚ := ((([Int.negSucc (nat_lit 13829166798460456)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 5000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ308 : ℚ := ((([Int.negSucc (nat_lit 4688701678944210)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 2000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ309 : ℚ := ((([Int.negSucc (nat_lit 19400195964234742)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 10000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ310 : ℚ := ((([Int.negSucc (nat_lit 3884381881195182)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 2500000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ311 : ℚ := ((([Int.negSucc (nat_lit 593302964643950)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 500000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ312 : ℚ := ((([Int.negSucc (nat_lit 2099582509087016)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 2500000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ313 : ℚ := ((([Int.negSucc (nat_lit 5149672888016192)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 10000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ314 : ℚ := ((([Int.negSucc (nat_lit 10699287389524788)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 50000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ315 : ℚ := ((([Int.ofNat (nat_lit 6037442102992293)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 100000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ316 : ℚ := ((([Int.ofNat (nat_lit 1518878282780793)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 5000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ317 : ℚ := ((([Int.ofNat (nat_lit 2529326601128319)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 5000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ318 : ℚ := ((([Int.ofNat (nat_lit 1021805502392699)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 2000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ319 : ℚ := ((([Int.ofNat (nat_lit 81)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 4)] : List ℤ)).headD 0:ℚ)
def entryQ320 : ℚ := ((([Int.ofNat (nat_lit 83)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 4)] : List ℤ)).headD 0:ℚ)
def entryQ321 : ℚ := ((([Int.ofNat (nat_lit 21)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 1)] : List ℤ)).headD 0:ℚ)
def entryQ322 : ℚ := ((([Int.negSucc (nat_lit 570215561839502)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 250000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ323 : ℚ := ((([Int.negSucc (nat_lit 9407797714911306)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 5000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ324 : ℚ := ((([Int.negSucc (nat_lit 149674954082558)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 100000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ325 : ℚ := ((([Int.negSucc (nat_lit 11269903616037728)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 10000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ326 : ℚ := ((([Int.negSucc (nat_lit 7729086398502888)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 10000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ327 : ℚ := ((([Int.ofNat (nat_lit 85)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 4)] : List ℤ)).headD 0:ℚ)
def entryQ328 : ℚ := ((([Int.negSucc (nat_lit 544024452738352)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 1250000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ329 : ℚ := ((([Int.ofNat (nat_lit 43)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 2)] : List ℤ)).headD 0:ℚ)
def entryQ330 : ℚ := ((([Int.negSucc (nat_lit 2869077134250280)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 25000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ331 : ℚ := ((([Int.ofNat (nat_lit 87)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 4)] : List ℤ)).headD 0:ℚ)
def entryQ332 : ℚ := ((([Int.ofNat (nat_lit 18746386885114413)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 100000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ333 : ℚ := ((([Int.ofNat (nat_lit 1175515328835431)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 2500000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ334 : ℚ := ((([Int.ofNat (nat_lit 89)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 4)] : List ℤ)).headD 0:ℚ)
def entryQ335 : ℚ := ((([Int.ofNat (nat_lit 7318179773627433)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 10000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ336 : ℚ := ((([Int.ofNat (nat_lit 9699172182006769)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 10000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ337 : ℚ := ((([Int.ofNat (nat_lit 91)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 4)] : List ℤ)).headD 0:ℚ)
def entryQ338 : ℚ := ((([Int.ofNat (nat_lit 236069021535663)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 200000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ339 : ℚ := ((([Int.ofNat (nat_lit 6553673045179317)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 5000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ340 : ℚ := ((([Int.ofNat (nat_lit 105684567309793)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 80000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ341 : ℚ := ((([Int.ofNat (nat_lit 13212226625039731)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 10000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ342 : ℚ := ((([Int.ofNat (nat_lit 95)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 4)] : List ℤ)).headD 0:ℚ)
def entryQ343 : ℚ := ((([Int.negSucc (nat_lit 30754270026076526)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 10000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ344 : ℚ := ((([Int.negSucc (nat_lit 2654438252611172)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 1000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ345 : ℚ := ((([Int.negSucc (nat_lit 11234624818890896)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 5000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ346 : ℚ := ((([Int.negSucc (nat_lit 74134901913902)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 40000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ347 : ℚ := ((([Int.negSucc (nat_lit 1474325599161920)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 1000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ348 : ℚ := ((([Int.negSucc (nat_lit 11104009511539182)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 10000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ349 : ℚ := ((([Int.negSucc (nat_lit 3811565104145202)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 5000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ350 : ℚ := ((([Int.negSucc (nat_lit 4309056338917302)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 10000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ351 : ℚ := ((([Int.negSucc (nat_lit 468883046977298)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 4000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ352 : ℚ := ((([Int.ofNat (nat_lit 354820112637231)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 2000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ353 : ℚ := ((([Int.ofNat (nat_lit 1127831827370001)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 2500000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ354 : ℚ := ((([Int.ofNat (nat_lit 7010077705057003)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 10000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ355 : ℚ := ((([Int.ofNat (nat_lit 18405468628793)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 20000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ356 : ℚ := ((([Int.ofNat (nat_lit 1973796164114189)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 2000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ357 : ℚ := ((([Int.ofNat (nat_lit 2544471603372293)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 2500000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ358 : ℚ := ((([Int.ofNat (nat_lit 515838730373839)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 500000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ359 : ℚ := ((([Int.ofNat (nat_lit 5168769389219743)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 5000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ360 : ℚ := ((([Int.negSucc (nat_lit 711942292974642)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 250000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ361 : ℚ := ((([Int.negSucc (nat_lit 2442690449945108)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 1000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ362 : ℚ := ((([Int.negSucc (nat_lit 256310685698476)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 125000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ363 : ℚ := ((([Int.negSucc (nat_lit 1671584842635438)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 1000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ364 : ℚ := ((([Int.negSucc (nat_lit 2612947632966696)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 2000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ365 : ℚ := ((([Int.negSucc (nat_lit 9557021491219060)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 10000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ366 : ℚ := ((([Int.negSucc (nat_lit 774884938940352)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 1250000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ367 : ℚ := ((([Int.negSucc (nat_lit 29984692713753712)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 100000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ368 : ℚ := ((([Int.ofNat (nat_lit 1775678659518131)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 500000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ369 : ℚ := ((([Int.ofNat (nat_lit 14454239557263887)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 50000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ370 : ℚ := ((([Int.ofNat (nat_lit 5550856105237577)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 10000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ371 : ℚ := ((([Int.ofNat (nat_lit 1997241518400393)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 2500000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ372 : ℚ := ((([Int.ofNat (nat_lit 10143240159287459)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 10000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ373 : ℚ := ((([Int.ofNat (nat_lit 2200650179057729)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 2000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ374 : ℚ := ((([Int.ofNat (nat_lit 11519962719454309)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 10000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ375 : ℚ := ((([Int.ofNat (nat_lit 101)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 4)] : List ℤ)).headD 0:ℚ)
def entryQ376 : ℚ := ((([Int.ofNat (nat_lit 5928348272884947)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 5000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ377 : ℚ := ((([Int.ofNat (nat_lit 12047165250008731)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 10000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ378 : ℚ := ((([Int.ofNat (nat_lit 6058086160754269)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 5000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ379 : ℚ := ((([Int.ofNat (nat_lit 605915562414817)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 500000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ380 : ℚ := ((([Int.ofNat (nat_lit 53)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 2)] : List ℤ)).headD 0:ℚ)
def entryQ381 : ℚ := ((([Int.negSucc (nat_lit 3358435735985228)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 1250000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ382 : ℚ := ((([Int.negSucc (nat_lit 22747394374759996)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 10000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ383 : ℚ := ((([Int.negSucc (nat_lit 9392104260271700)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 5000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ384 : ℚ := ((([Int.negSucc (nat_lit 3746155957971456)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 2500000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ385 : ℚ := ((([Int.negSucc (nat_lit 2839024475190486)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 2500000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ386 : ℚ := ((([Int.negSucc (nat_lit 3953588878178606)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 5000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ387 : ℚ := ((([Int.negSucc (nat_lit 46477778852014256)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 100000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ388 : ℚ := ((([Int.negSucc (nat_lit 3974245907253526)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 25000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ389 : ℚ := ((([Int.ofNat (nat_lit 6262246320920263)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 50000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ390 : ℚ := ((([Int.ofNat (nat_lit 1929856840454063)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 5000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ391 : ℚ := ((([Int.ofNat (nat_lit 6205445387559149)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 10000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ392 : ℚ := ((([Int.ofNat (nat_lit 4122804064588263)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 5000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ393 : ℚ := ((([Int.ofNat (nat_lit 4834215191273419)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 5000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ394 : ℚ := ((([Int.ofNat (nat_lit 9668597973381947)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 10000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ395 : ℚ := ((([Int.negSucc (nat_lit 18282504830588088)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 10000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ396 : ℚ := ((([Int.negSucc (nat_lit 2944407223349398)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 2000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ397 : ℚ := ((([Int.negSucc (nat_lit 11329706710126902)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 10000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ398 : ℚ := ((([Int.negSucc (nat_lit 1622528826980872)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 2000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ399 : ℚ := ((([Int.negSucc (nat_lit 5078947322773528)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 10000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ400 : ℚ := ((([Int.negSucc (nat_lit 1118907409776300)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 5000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ401 : ℚ := ((([Int.ofNat (nat_lit 19999387716898947)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 500000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ402 : ℚ := ((([Int.ofNat (nat_lit 2821617603291573)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 10000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ403 : ℚ := ((([Int.ofNat (nat_lit 501121995884643)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 1000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ404 : ℚ := ((([Int.ofNat (nat_lit 6947893486886031)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 10000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ405 : ℚ := ((([Int.ofNat (nat_lit 4300976237284489)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 5000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ406 : ℚ := ((([Int.ofNat (nat_lit 9923848894251387)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 10000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ407 : ℚ := ((([Int.ofNat (nat_lit 5335835236283847)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 5000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ408 : ℚ := ((([Int.negSucc (nat_lit 11940652742132262)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 10000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ409 : ℚ := ((([Int.negSucc (nat_lit 860617070546280)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 1000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ410 : ℚ := ((([Int.negSucc (nat_lit 2718627031000686)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 5000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ411 : ℚ := ((([Int.negSucc (nat_lit 2440729925517366)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 10000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ412 : ℚ := ((([Int.ofNat (nat_lit 3755768928506123)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 100000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ413 : ℚ := ((([Int.ofNat (nat_lit 3002703352291777)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 10000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ414 : ℚ := ((([Int.ofNat (nat_lit 5430109840855073)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 10000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ415 : ℚ := ((([Int.ofNat (nat_lit 152899748592287)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 200000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ416 : ℚ := ((([Int.ofNat (nat_lit 9630970244754209)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 10000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ417 : ℚ := ((([Int.ofNat (nat_lit 2273161706352373)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 2000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ418 : ℚ := ((([Int.ofNat (nat_lit 320386775581511)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 250000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ419 : ℚ := ((([Int.ofNat (nat_lit 13911122253581611)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 10000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ420 : ℚ := ((([Int.ofNat (nat_lit 705086338130317)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 500000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ421 : ℚ := ((([Int.negSucc (nat_lit 160028953638476)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 250000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ422 : ℚ := ((([Int.negSucc (nat_lit 3259561706252582)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 10000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ423 : ℚ := ((([Int.negSucc (nat_lit 2702645927269856)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 100000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ424 : ℚ := ((([Int.ofNat (nat_lit 640342967699953)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 2500000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ425 : ℚ := ((([Int.ofNat (nat_lit 5229369433649907)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 10000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ426 : ℚ := ((([Int.ofNat (nat_lit 7726940195444811)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 10000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ427 : ℚ := ((([Int.ofNat (nat_lit 10046334896111981)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 10000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ428 : ℚ := ((([Int.ofNat (nat_lit 3044559329290813)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 2500000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ429 : ℚ := ((([Int.ofNat (nat_lit 3527831890322643)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 2500000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ430 : ℚ := ((([Int.ofNat (nat_lit 15831000449991293)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 10000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ431 : ℚ := ((([Int.ofNat (nat_lit 8658523890922071)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 5000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ432 : ℚ := ((([Int.ofNat (nat_lit 18537508479358051)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 10000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ433 : ℚ := ((([Int.ofNat (nat_lit 1941710588070507)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 1000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ434 : ℚ := ((([Int.ofNat (nat_lit 777970304709281)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 400000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ435 : ℚ := ((([Int.ofNat (nat_lit 107)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 4)] : List ℤ)).headD 0:ℚ)
def entryQ436 : ℚ := ((([Int.ofNat (nat_lit 55)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 2)] : List ℤ)).headD 0:ℚ)
def entryQ437 : ℚ := ((([Int.ofNat (nat_lit 10278898826479189)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 500000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ438 : ℚ := ((([Int.ofNat (nat_lit 622972812096537)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 2000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ439 : ℚ := ((([Int.ofNat (nat_lit 5880518464762291)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 10000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ440 : ℚ := ((([Int.ofNat (nat_lit 424896830725179)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 500000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ441 : ℚ := ((([Int.ofNat (nat_lit 2192406303034121)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 2000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ442 : ℚ := ((([Int.ofNat (nat_lit 6633533192764801)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 5000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ443 : ℚ := ((([Int.ofNat (nat_lit 3851579738095487)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 2500000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ444 : ℚ := ((([Int.ofNat (nat_lit 347437474314543)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 200000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ445 : ℚ := ((([Int.ofNat (nat_lit 9577016407317511)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 5000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ446 : ℚ := ((([Int.ofNat (nat_lit 414806531162721)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 200000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ447 : ℚ := ((([Int.ofNat (nat_lit 2211352095914813)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 1000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ448 : ℚ := ((([Int.ofNat (nat_lit 581158203934269)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 250000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ449 : ℚ := ((([Int.ofNat (nat_lit 4814920897894547)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 2000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ450 : ℚ := ((([Int.ofNat (nat_lit 964515621528591)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 400000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ451 : ℚ := ((([Int.ofNat (nat_lit 115)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 4)] : List ℤ)).headD 0:ℚ)
def entryQ452 : ℚ := ((([Int.ofNat (nat_lit 117)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 4)] : List ℤ)).headD 0:ℚ)
def entryQ453 : ℚ := ((([Int.ofNat (nat_lit 59)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 2)] : List ℤ)).headD 0:ℚ)
def entryQ454 : ℚ := ((([Int.ofNat (nat_lit 119)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 4)] : List ℤ)).headD 0:ℚ)
def entryQ455 : ℚ := ((([Int.ofNat (nat_lit 843361546376097)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 1000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ456 : ℚ := ((([Int.ofNat (nat_lit 2745351915573087)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 2500000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ457 : ℚ := ((([Int.ofNat (nat_lit 6696251983606307)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 5000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ458 : ℚ := ((([Int.ofNat (nat_lit 1957868003470847)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 1250000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ459 : ℚ := ((([Int.ofNat (nat_lit 17788314861205659)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 10000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ460 : ℚ := ((([Int.ofNat (nat_lit 617612808532967)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 312500000000000)] : List ℤ)).headD 0:ℚ)
def entryQ461 : ℚ := ((([Int.ofNat (nat_lit 2697878943119203)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 1250000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ462 : ℚ := ((([Int.ofNat (nat_lit 290497102740881)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 125000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ463 : ℚ := ((([Int.ofNat (nat_lit 12362705601243227)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 5000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ464 : ℚ := ((([Int.ofNat (nat_lit 2602924569240033)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 1000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ465 : ℚ := ((([Int.ofNat (nat_lit 339205354920383)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 125000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ466 : ℚ := ((([Int.ofNat (nat_lit 121)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 4)] : List ℤ)).headD 0:ℚ)
def entryQ467 : ℚ := ((([Int.ofNat (nat_lit 28023399869543297)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 10000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ468 : ℚ := ((([Int.ofNat (nat_lit 572693717369611)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 200000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ469 : ℚ := ((([Int.ofNat (nat_lit 123)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 4)] : List ℤ)).headD 0:ℚ)
def entryQ470 : ℚ := ((([Int.ofNat (nat_lit 5731656437353017)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 2000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ471 : ℚ := ((([Int.ofNat (nat_lit 125)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 4)] : List ℤ)).headD 0:ℚ)
def entryQ472 : ℚ := ((([Int.ofNat (nat_lit 127)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 4)] : List ℤ)).headD 0:ℚ)
def entryQ473 : ℚ := ((([Int.ofNat (nat_lit 32)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 1)] : List ℤ)).headD 0:ℚ)
def entryQ474 : ℚ := ((([Int.ofNat (nat_lit 129)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 4)] : List ℤ)).headD 0:ℚ)
def entryQ475 : ℚ := ((([Int.ofNat (nat_lit 65)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 2)] : List ℤ)).headD 0:ℚ)
def entryQ476 : ℚ := ((([Int.negSucc (nat_lit 7527872121031798)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 2500000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ477 : ℚ := ((([Int.negSucc (nat_lit 25877683782988282)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 10000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ478 : ℚ := ((([Int.negSucc (nat_lit 4360323815246466)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 2000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ479 : ℚ := ((([Int.negSucc (nat_lit 4472554855611946)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 2500000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ480 : ℚ := ((([Int.negSucc (nat_lit 1415129127440262)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 1000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ481 : ℚ := ((([Int.negSucc (nat_lit 1059367198691290)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 1000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ482 : ℚ := ((([Int.negSucc (nat_lit 7227671572750792)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 10000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ483 : ℚ := ((([Int.negSucc (nat_lit 40655557856953716)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 100000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ484 : ℚ := ((([Int.negSucc (nat_lit 1122448731829036)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 10000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ485 : ℚ := ((([Int.ofNat (nat_lit 15819408340854227)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 100000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ486 : ℚ := ((([Int.ofNat (nat_lit 502498360750509)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 1250000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ487 : ℚ := ((([Int.ofNat (nat_lit 614635776073781)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 1000000000000000)] : List ℤ)).headD 0:ℚ)
def entryQ488 : ℚ := ((([Int.ofNat (nat_lit 1531461719575251)] : List ℤ)).headD 0:ℚ)/((([Int.ofNat (nat_lit 2000000000000000)] : List ℤ)).headD 0:ℚ)
def entry0 : PairEntry 37 := ⟨⟨0,by decide⟩,0,entryQ0,entryQ1⟩
def entry1 : PairEntry 37 := ⟨⟨0,by decide⟩,1,entryQ2,entryQ3⟩
def entry2 : PairEntry 37 := ⟨⟨0,by decide⟩,2,entryQ4,entryQ5⟩
def entry3 : PairEntry 37 := ⟨⟨0,by decide⟩,3,entryQ6,entryQ7⟩
def entry4 : PairEntry 37 := ⟨⟨0,by decide⟩,4,entryQ8,entryQ9⟩
def entry5 : PairEntry 37 := ⟨⟨0,by decide⟩,5,entryQ10,entryQ11⟩
def entry6 : PairEntry 37 := ⟨⟨1,by decide⟩,0,entryQ12,entryQ13⟩
def entry7 : PairEntry 37 := ⟨⟨2,by decide⟩,0,entryQ14,entryQ15⟩
def entry8 : PairEntry 37 := ⟨⟨3,by decide⟩,0,entryQ16,entryQ17⟩
def entry9 : PairEntry 37 := ⟨⟨4,by decide⟩,0,entryQ18,entryQ19⟩
def entry10 : PairEntry 37 := ⟨⟨5,by decide⟩,0,entryQ20,entryQ21⟩
def entry11 : PairEntry 37 := ⟨⟨6,by decide⟩,0,entryQ22,entryQ23⟩
def entry12 : PairEntry 37 := ⟨⟨6,by decide⟩,1,entryQ24,entryQ25⟩
def entry13 : PairEntry 37 := ⟨⟨6,by decide⟩,2,entryQ26,entryQ27⟩
def entry14 : PairEntry 37 := ⟨⟨6,by decide⟩,3,entryQ28,entryQ29⟩
def entry15 : PairEntry 37 := ⟨⟨6,by decide⟩,4,entryQ30,entryQ31⟩
def entry16 : PairEntry 37 := ⟨⟨6,by decide⟩,5,entryQ32,entryQ33⟩
def entry17 : PairEntry 37 := ⟨⟨6,by decide⟩,6,entryQ34,entryQ33⟩
def entry18 : PairEntry 37 := ⟨⟨7,by decide⟩,0,entryQ24,entryQ35⟩
def entry19 : PairEntry 37 := ⟨⟨7,by decide⟩,1,entryQ36,entryQ37⟩
def entry20 : PairEntry 37 := ⟨⟨7,by decide⟩,2,entryQ32,entryQ38⟩
def entry21 : PairEntry 37 := ⟨⟨7,by decide⟩,3,entryQ39,entryQ40⟩
def entry22 : PairEntry 37 := ⟨⟨7,by decide⟩,4,entryQ34,entryQ41⟩
def entry23 : PairEntry 37 := ⟨⟨7,by decide⟩,5,entryQ42,entryQ40⟩
def entry24 : PairEntry 37 := ⟨⟨8,by decide⟩,0,entryQ43,entryQ44⟩
def entry25 : PairEntry 37 := ⟨⟨8,by decide⟩,1,entryQ45,entryQ46⟩
def entry26 : PairEntry 37 := ⟨⟨8,by decide⟩,2,entryQ47,entryQ48⟩
def entry27 : PairEntry 37 := ⟨⟨8,by decide⟩,3,entryQ49,entryQ50⟩
def entry28 : PairEntry 37 := ⟨⟨8,by decide⟩,4,entryQ51,entryQ52⟩
def entry29 : PairEntry 37 := ⟨⟨8,by decide⟩,5,entryQ53,entryQ54⟩
def entry30 : PairEntry 37 := ⟨⟨8,by decide⟩,6,entryQ55,entryQ56⟩
def entry31 : PairEntry 37 := ⟨⟨8,by decide⟩,7,entryQ57,entryQ58⟩
def entry32 : PairEntry 37 := ⟨⟨8,by decide⟩,8,entryQ59,entryQ60⟩
def entry33 : PairEntry 37 := ⟨⟨8,by decide⟩,9,entryQ61,entryQ60⟩
def entry34 : PairEntry 37 := ⟨⟨8,by decide⟩,10,entryQ62,entryQ60⟩
def entry35 : PairEntry 37 := ⟨⟨8,by decide⟩,11,entryQ63,entryQ60⟩
def entry36 : PairEntry 37 := ⟨⟨8,by decide⟩,12,entryQ64,entryQ60⟩
def entry37 : PairEntry 37 := ⟨⟨8,by decide⟩,13,entryQ30,entryQ65⟩
def entry38 : PairEntry 37 := ⟨⟨9,by decide⟩,0,entryQ66,entryQ67⟩
def entry39 : PairEntry 37 := ⟨⟨9,by decide⟩,1,entryQ68,entryQ69⟩
def entry40 : PairEntry 37 := ⟨⟨9,by decide⟩,2,entryQ70,entryQ71⟩
def entry41 : PairEntry 37 := ⟨⟨9,by decide⟩,3,entryQ32,entryQ72⟩
def entry42 : PairEntry 37 := ⟨⟨9,by decide⟩,4,entryQ73,entryQ74⟩
def entry43 : PairEntry 37 := ⟨⟨9,by decide⟩,5,entryQ75,entryQ76⟩
def entry44 : PairEntry 37 := ⟨⟨9,by decide⟩,6,entryQ77,entryQ78⟩
def entry45 : PairEntry 37 := ⟨⟨9,by decide⟩,7,entryQ79,entryQ80⟩
def entry46 : PairEntry 37 := ⟨⟨9,by decide⟩,8,entryQ39,entryQ81⟩
def entry47 : PairEntry 37 := ⟨⟨9,by decide⟩,9,entryQ82,entryQ83⟩
def entry48 : PairEntry 37 := ⟨⟨9,by decide⟩,10,entryQ84,entryQ85⟩
def entry49 : PairEntry 37 := ⟨⟨9,by decide⟩,11,entryQ86,entryQ87⟩
def entry50 : PairEntry 37 := ⟨⟨9,by decide⟩,12,entryQ88,entryQ89⟩
def entry51 : PairEntry 37 := ⟨⟨9,by decide⟩,13,entryQ90,entryQ91⟩
def entry52 : PairEntry 37 := ⟨⟨10,by decide⟩,0,entryQ82,entryQ92⟩
def entry53 : PairEntry 37 := ⟨⟨10,by decide⟩,1,entryQ93,entryQ94⟩
def entry54 : PairEntry 37 := ⟨⟨10,by decide⟩,2,entryQ95,entryQ96⟩
def entry55 : PairEntry 37 := ⟨⟨10,by decide⟩,3,entryQ97,entryQ98⟩
def entry56 : PairEntry 37 := ⟨⟨10,by decide⟩,4,entryQ99,entryQ100⟩
def entry57 : PairEntry 37 := ⟨⟨10,by decide⟩,5,entryQ101,entryQ102⟩
def entry58 : PairEntry 37 := ⟨⟨10,by decide⟩,6,entryQ103,entryQ104⟩
def entry59 : PairEntry 37 := ⟨⟨10,by decide⟩,7,entryQ105,entryQ106⟩
def entry60 : PairEntry 37 := ⟨⟨10,by decide⟩,8,entryQ107,entryQ108⟩
def entry61 : PairEntry 37 := ⟨⟨10,by decide⟩,9,entryQ109,entryQ110⟩
def entry62 : PairEntry 37 := ⟨⟨10,by decide⟩,10,entryQ111,entryQ112⟩
def entry63 : PairEntry 37 := ⟨⟨10,by decide⟩,11,entryQ113,entryQ114⟩
def entry64 : PairEntry 37 := ⟨⟨10,by decide⟩,12,entryQ115,entryQ116⟩
def entry65 : PairEntry 37 := ⟨⟨10,by decide⟩,13,entryQ117,entryQ118⟩
def entry66 : PairEntry 37 := ⟨⟨11,by decide⟩,0,entryQ90,entryQ119⟩
def entry67 : PairEntry 37 := ⟨⟨11,by decide⟩,1,entryQ101,entryQ120⟩
def entry68 : PairEntry 37 := ⟨⟨11,by decide⟩,2,entryQ111,entryQ121⟩
def entry69 : PairEntry 37 := ⟨⟨11,by decide⟩,3,entryQ122,entryQ123⟩
def entry70 : PairEntry 37 := ⟨⟨11,by decide⟩,4,entryQ124,entryQ125⟩
def entry71 : PairEntry 37 := ⟨⟨11,by decide⟩,5,entryQ117,entryQ126⟩
def entry72 : PairEntry 37 := ⟨⟨11,by decide⟩,6,entryQ127,entryQ128⟩
def entry73 : PairEntry 37 := ⟨⟨11,by decide⟩,7,entryQ129,entryQ130⟩
def entry74 : PairEntry 37 := ⟨⟨11,by decide⟩,8,entryQ131,entryQ132⟩
def entry75 : PairEntry 37 := ⟨⟨11,by decide⟩,9,entryQ133,entryQ134⟩
def entry76 : PairEntry 37 := ⟨⟨11,by decide⟩,10,entryQ135,entryQ136⟩
def entry77 : PairEntry 37 := ⟨⟨11,by decide⟩,11,entryQ137,entryQ138⟩
def entry78 : PairEntry 37 := ⟨⟨11,by decide⟩,12,entryQ139,entryQ140⟩
def entry79 : PairEntry 37 := ⟨⟨11,by decide⟩,13,entryQ141,entryQ142⟩
def entry80 : PairEntry 37 := ⟨⟨11,by decide⟩,14,entryQ143,entryQ144⟩
def entry81 : PairEntry 37 := ⟨⟨12,by decide⟩,0,entryQ141,entryQ145⟩
def entry82 : PairEntry 37 := ⟨⟨12,by decide⟩,1,entryQ146,entryQ147⟩
def entry83 : PairEntry 37 := ⟨⟨12,by decide⟩,2,entryQ148,entryQ149⟩
def entry84 : PairEntry 37 := ⟨⟨12,by decide⟩,3,entryQ150,entryQ151⟩
def entry85 : PairEntry 37 := ⟨⟨12,by decide⟩,4,entryQ152,entryQ153⟩
def entry86 : PairEntry 37 := ⟨⟨12,by decide⟩,5,entryQ154,entryQ155⟩
def entry87 : PairEntry 37 := ⟨⟨12,by decide⟩,6,entryQ156,entryQ157⟩
def entry88 : PairEntry 37 := ⟨⟨12,by decide⟩,7,entryQ158,entryQ159⟩
def entry89 : PairEntry 37 := ⟨⟨12,by decide⟩,8,entryQ160,entryQ161⟩
def entry90 : PairEntry 37 := ⟨⟨12,by decide⟩,9,entryQ162,entryQ163⟩
def entry91 : PairEntry 37 := ⟨⟨12,by decide⟩,10,entryQ164,entryQ165⟩
def entry92 : PairEntry 37 := ⟨⟨12,by decide⟩,11,entryQ166,entryQ167⟩
def entry93 : PairEntry 37 := ⟨⟨12,by decide⟩,12,entryQ168,entryQ169⟩
def entry94 : PairEntry 37 := ⟨⟨12,by decide⟩,13,entryQ170,entryQ171⟩
def entry95 : PairEntry 37 := ⟨⟨13,by decide⟩,0,entryQ148,entryQ172⟩
def entry96 : PairEntry 37 := ⟨⟨13,by decide⟩,1,entryQ156,entryQ173⟩
def entry97 : PairEntry 37 := ⟨⟨13,by decide⟩,2,entryQ166,entryQ174⟩
def entry98 : PairEntry 37 := ⟨⟨13,by decide⟩,3,entryQ175,entryQ176⟩
def entry99 : PairEntry 37 := ⟨⟨13,by decide⟩,4,entryQ177,entryQ178⟩
def entry100 : PairEntry 37 := ⟨⟨13,by decide⟩,5,entryQ168,entryQ179⟩
def entry101 : PairEntry 37 := ⟨⟨13,by decide⟩,6,entryQ180,entryQ181⟩
def entry102 : PairEntry 37 := ⟨⟨13,by decide⟩,7,entryQ182,entryQ183⟩
def entry103 : PairEntry 37 := ⟨⟨13,by decide⟩,8,entryQ184,entryQ185⟩
def entry104 : PairEntry 37 := ⟨⟨13,by decide⟩,9,entryQ186,entryQ187⟩
def entry105 : PairEntry 37 := ⟨⟨13,by decide⟩,10,entryQ188,entryQ189⟩
def entry106 : PairEntry 37 := ⟨⟨13,by decide⟩,11,entryQ190,entryQ191⟩
def entry107 : PairEntry 37 := ⟨⟨13,by decide⟩,12,entryQ192,entryQ193⟩
def entry108 : PairEntry 37 := ⟨⟨13,by decide⟩,13,entryQ194,entryQ195⟩
def entry109 : PairEntry 37 := ⟨⟨13,by decide⟩,14,entryQ196,entryQ197⟩
def entry110 : PairEntry 37 := ⟨⟨13,by decide⟩,15,entryQ198,entryQ199⟩
def entry111 : PairEntry 37 := ⟨⟨14,by decide⟩,0,entryQ156,entryQ200⟩
def entry112 : PairEntry 37 := ⟨⟨14,by decide⟩,1,entryQ166,entryQ201⟩
def entry113 : PairEntry 37 := ⟨⟨14,by decide⟩,2,entryQ168,entryQ202⟩
def entry114 : PairEntry 37 := ⟨⟨14,by decide⟩,3,entryQ180,entryQ203⟩
def entry115 : PairEntry 37 := ⟨⟨14,by decide⟩,4,entryQ182,entryQ204⟩
def entry116 : PairEntry 37 := ⟨⟨14,by decide⟩,5,entryQ184,entryQ205⟩
def entry117 : PairEntry 37 := ⟨⟨14,by decide⟩,6,entryQ186,entryQ206⟩
def entry118 : PairEntry 37 := ⟨⟨14,by decide⟩,7,entryQ188,entryQ207⟩
def entry119 : PairEntry 37 := ⟨⟨14,by decide⟩,8,entryQ190,entryQ208⟩
def entry120 : PairEntry 37 := ⟨⟨14,by decide⟩,9,entryQ192,entryQ209⟩
def entry121 : PairEntry 37 := ⟨⟨14,by decide⟩,10,entryQ194,entryQ210⟩
def entry122 : PairEntry 37 := ⟨⟨14,by decide⟩,11,entryQ196,entryQ211⟩
def entry123 : PairEntry 37 := ⟨⟨14,by decide⟩,12,entryQ212,entryQ213⟩
def entry124 : PairEntry 37 := ⟨⟨14,by decide⟩,13,entryQ214,entryQ215⟩
def entry125 : PairEntry 37 := ⟨⟨14,by decide⟩,14,entryQ216,entryQ217⟩
def entry126 : PairEntry 37 := ⟨⟨14,by decide⟩,15,entryQ218,entryQ219⟩
def entry127 : PairEntry 37 := ⟨⟨14,by decide⟩,16,entryQ220,entryQ221⟩
def entry128 : PairEntry 37 := ⟨⟨14,by decide⟩,17,entryQ198,entryQ222⟩
def entry129 : PairEntry 37 := ⟨⟨15,by decide⟩,0,entryQ51,entryQ223⟩
def entry130 : PairEntry 37 := ⟨⟨16,by decide⟩,0,entryQ224,entryQ225⟩
def entry131 : PairEntry 37 := ⟨⟨16,by decide⟩,1,entryQ226,entryQ227⟩
def entry132 : PairEntry 37 := ⟨⟨16,by decide⟩,2,entryQ228,entryQ229⟩
def entry133 : PairEntry 37 := ⟨⟨17,by decide⟩,0,entryQ230,entryQ231⟩
def entry134 : PairEntry 37 := ⟨⟨18,by decide⟩,0,entryQ24,entryQ232⟩
def entry135 : PairEntry 37 := ⟨⟨19,by decide⟩,0,entryQ34,entryQ233⟩
def entry136 : PairEntry 37 := ⟨⟨19,by decide⟩,1,entryQ234,entryQ235⟩
def entry137 : PairEntry 37 := ⟨⟨19,by decide⟩,2,entryQ236,entryQ237⟩
def entry138 : PairEntry 37 := ⟨⟨20,by decide⟩,0,entryQ32,entryQ238⟩
def entry139 : PairEntry 37 := ⟨⟨20,by decide⟩,1,entryQ103,entryQ239⟩
def entry140 : PairEntry 37 := ⟨⟨20,by decide⟩,2,entryQ240,entryQ241⟩
def entry141 : PairEntry 37 := ⟨⟨20,by decide⟩,3,entryQ242,entryQ243⟩
def entry142 : PairEntry 37 := ⟨⟨21,by decide⟩,0,entryQ228,entryQ244⟩
def entry143 : PairEntry 37 := ⟨⟨21,by decide⟩,1,entryQ245,entryQ246⟩
def entry144 : PairEntry 37 := ⟨⟨21,by decide⟩,2,entryQ247,entryQ248⟩
def entry145 : PairEntry 37 := ⟨⟨22,by decide⟩,0,entryQ240,entryQ249⟩
def entry146 : PairEntry 37 := ⟨⟨22,by decide⟩,1,entryQ250,entryQ251⟩
def entry147 : PairEntry 37 := ⟨⟨22,by decide⟩,2,entryQ224,entryQ252⟩
def entry148 : PairEntry 37 := ⟨⟨23,by decide⟩,0,entryQ253,entryQ254⟩
def entry149 : PairEntry 37 := ⟨⟨23,by decide⟩,1,entryQ255,entryQ256⟩
def entry150 : PairEntry 37 := ⟨⟨23,by decide⟩,2,entryQ257,entryQ258⟩
def entry151 : PairEntry 37 := ⟨⟨24,by decide⟩,0,entryQ259,entryQ260⟩
def entry152 : PairEntry 37 := ⟨⟨24,by decide⟩,1,entryQ261,entryQ262⟩
def entry153 : PairEntry 37 := ⟨⟨24,by decide⟩,2,entryQ263,entryQ264⟩
def entry154 : PairEntry 37 := ⟨⟨24,by decide⟩,3,entryQ265,entryQ266⟩
def entry155 : PairEntry 37 := ⟨⟨24,by decide⟩,4,entryQ0,entryQ267⟩
def entry156 : PairEntry 37 := ⟨⟨24,by decide⟩,5,entryQ268,entryQ269⟩
def entry157 : PairEntry 37 := ⟨⟨24,by decide⟩,6,entryQ8,entryQ270⟩
def entry158 : PairEntry 37 := ⟨⟨24,by decide⟩,7,entryQ2,entryQ271⟩
def entry159 : PairEntry 37 := ⟨⟨24,by decide⟩,8,entryQ4,entryQ272⟩
def entry160 : PairEntry 37 := ⟨⟨24,by decide⟩,9,entryQ6,entryQ273⟩
def entry161 : PairEntry 37 := ⟨⟨24,by decide⟩,10,entryQ10,entryQ274⟩
def entry162 : PairEntry 37 := ⟨⟨24,by decide⟩,11,entryQ275,entryQ276⟩
def entry163 : PairEntry 37 := ⟨⟨24,by decide⟩,12,entryQ277,entryQ278⟩
def entry164 : PairEntry 37 := ⟨⟨24,by decide⟩,13,entryQ279,entryQ280⟩
def entry165 : PairEntry 37 := ⟨⟨24,by decide⟩,14,entryQ281,entryQ280⟩
def entry166 : PairEntry 37 := ⟨⟨24,by decide⟩,15,entryQ282,entryQ280⟩
def entry167 : PairEntry 37 := ⟨⟨24,by decide⟩,16,entryQ12,entryQ280⟩
def entry168 : PairEntry 37 := ⟨⟨24,by decide⟩,17,entryQ283,entryQ280⟩
def entry169 : PairEntry 37 := ⟨⟨24,by decide⟩,18,entryQ284,entryQ280⟩
def entry170 : PairEntry 37 := ⟨⟨24,by decide⟩,19,entryQ285,entryQ280⟩
def entry171 : PairEntry 37 := ⟨⟨24,by decide⟩,20,entryQ14,entryQ280⟩
def entry172 : PairEntry 37 := ⟨⟨25,by decide⟩,0,entryQ8,entryQ286⟩
def entry173 : PairEntry 37 := ⟨⟨25,by decide⟩,1,entryQ2,entryQ287⟩
def entry174 : PairEntry 37 := ⟨⟨25,by decide⟩,2,entryQ4,entryQ288⟩
def entry175 : PairEntry 37 := ⟨⟨25,by decide⟩,3,entryQ6,entryQ289⟩
def entry176 : PairEntry 37 := ⟨⟨25,by decide⟩,4,entryQ10,entryQ290⟩
def entry177 : PairEntry 37 := ⟨⟨25,by decide⟩,5,entryQ275,entryQ291⟩
def entry178 : PairEntry 37 := ⟨⟨25,by decide⟩,6,entryQ277,entryQ292⟩
def entry179 : PairEntry 37 := ⟨⟨25,by decide⟩,7,entryQ279,entryQ293⟩
def entry180 : PairEntry 37 := ⟨⟨25,by decide⟩,8,entryQ281,entryQ294⟩
def entry181 : PairEntry 37 := ⟨⟨25,by decide⟩,9,entryQ282,entryQ295⟩
def entry182 : PairEntry 37 := ⟨⟨25,by decide⟩,10,entryQ12,entryQ296⟩
def entry183 : PairEntry 37 := ⟨⟨25,by decide⟩,11,entryQ283,entryQ297⟩
def entry184 : PairEntry 37 := ⟨⟨25,by decide⟩,12,entryQ284,entryQ298⟩
def entry185 : PairEntry 37 := ⟨⟨25,by decide⟩,13,entryQ285,entryQ299⟩
def entry186 : PairEntry 37 := ⟨⟨25,by decide⟩,14,entryQ14,entryQ299⟩
def entry187 : PairEntry 37 := ⟨⟨25,by decide⟩,15,entryQ300,entryQ299⟩
def entry188 : PairEntry 37 := ⟨⟨25,by decide⟩,16,entryQ301,entryQ299⟩
def entry189 : PairEntry 37 := ⟨⟨25,by decide⟩,17,entryQ302,entryQ299⟩
def entry190 : PairEntry 37 := ⟨⟨25,by decide⟩,18,entryQ303,entryQ299⟩
def entry191 : PairEntry 37 := ⟨⟨25,by decide⟩,19,entryQ304,entryQ299⟩
def entry192 : PairEntry 37 := ⟨⟨25,by decide⟩,20,entryQ16,entryQ299⟩
def entry193 : PairEntry 37 := ⟨⟨26,by decide⟩,0,entryQ10,entryQ305⟩
def entry194 : PairEntry 37 := ⟨⟨26,by decide⟩,1,entryQ275,entryQ306⟩
def entry195 : PairEntry 37 := ⟨⟨26,by decide⟩,2,entryQ277,entryQ307⟩
def entry196 : PairEntry 37 := ⟨⟨26,by decide⟩,3,entryQ279,entryQ308⟩
def entry197 : PairEntry 37 := ⟨⟨26,by decide⟩,4,entryQ281,entryQ309⟩
def entry198 : PairEntry 37 := ⟨⟨26,by decide⟩,5,entryQ282,entryQ310⟩
def entry199 : PairEntry 37 := ⟨⟨26,by decide⟩,6,entryQ12,entryQ311⟩
def entry200 : PairEntry 37 := ⟨⟨26,by decide⟩,7,entryQ283,entryQ312⟩
def entry201 : PairEntry 37 := ⟨⟨26,by decide⟩,8,entryQ284,entryQ313⟩
def entry202 : PairEntry 37 := ⟨⟨26,by decide⟩,9,entryQ285,entryQ314⟩
def entry203 : PairEntry 37 := ⟨⟨26,by decide⟩,10,entryQ14,entryQ315⟩
def entry204 : PairEntry 37 := ⟨⟨26,by decide⟩,11,entryQ300,entryQ316⟩
def entry205 : PairEntry 37 := ⟨⟨26,by decide⟩,12,entryQ301,entryQ317⟩
def entry206 : PairEntry 37 := ⟨⟨26,by decide⟩,13,entryQ302,entryQ318⟩
def entry207 : PairEntry 37 := ⟨⟨26,by decide⟩,14,entryQ303,entryQ318⟩
def entry208 : PairEntry 37 := ⟨⟨26,by decide⟩,15,entryQ304,entryQ318⟩
def entry209 : PairEntry 37 := ⟨⟨26,by decide⟩,16,entryQ16,entryQ318⟩
def entry210 : PairEntry 37 := ⟨⟨26,by decide⟩,17,entryQ319,entryQ318⟩
def entry211 : PairEntry 37 := ⟨⟨26,by decide⟩,18,entryQ18,entryQ318⟩
def entry212 : PairEntry 37 := ⟨⟨26,by decide⟩,19,entryQ320,entryQ318⟩
def entry213 : PairEntry 37 := ⟨⟨26,by decide⟩,20,entryQ321,entryQ318⟩
def entry214 : PairEntry 37 := ⟨⟨27,by decide⟩,0,entryQ16,entryQ322⟩
def entry215 : PairEntry 37 := ⟨⟨27,by decide⟩,1,entryQ319,entryQ323⟩
def entry216 : PairEntry 37 := ⟨⟨27,by decide⟩,2,entryQ18,entryQ324⟩
def entry217 : PairEntry 37 := ⟨⟨27,by decide⟩,3,entryQ320,entryQ325⟩
def entry218 : PairEntry 37 := ⟨⟨27,by decide⟩,4,entryQ321,entryQ326⟩
def entry219 : PairEntry 37 := ⟨⟨27,by decide⟩,5,entryQ327,entryQ328⟩
def entry220 : PairEntry 37 := ⟨⟨27,by decide⟩,6,entryQ329,entryQ330⟩
def entry221 : PairEntry 37 := ⟨⟨27,by decide⟩,7,entryQ331,entryQ332⟩
def entry222 : PairEntry 37 := ⟨⟨27,by decide⟩,8,entryQ20,entryQ333⟩
def entry223 : PairEntry 37 := ⟨⟨27,by decide⟩,9,entryQ334,entryQ335⟩
def entry224 : PairEntry 37 := ⟨⟨27,by decide⟩,10,entryQ22,entryQ336⟩
def entry225 : PairEntry 37 := ⟨⟨27,by decide⟩,11,entryQ337,entryQ338⟩
def entry226 : PairEntry 37 := ⟨⟨27,by decide⟩,12,entryQ30,entryQ339⟩
def entry227 : PairEntry 37 := ⟨⟨27,by decide⟩,13,entryQ62,entryQ340⟩
def entry228 : PairEntry 37 := ⟨⟨27,by decide⟩,14,entryQ24,entryQ341⟩
def entry229 : PairEntry 37 := ⟨⟨27,by decide⟩,15,entryQ342,entryQ341⟩
def entry230 : PairEntry 37 := ⟨⟨27,by decide⟩,16,entryQ34,entryQ341⟩
def entry231 : PairEntry 37 := ⟨⟨27,by decide⟩,17,entryQ36,entryQ341⟩
def entry232 : PairEntry 37 := ⟨⟨27,by decide⟩,18,entryQ32,entryQ341⟩
def entry233 : PairEntry 37 := ⟨⟨27,by decide⟩,19,entryQ39,entryQ341⟩
def entry234 : PairEntry 37 := ⟨⟨28,by decide⟩,0,entryQ16,entryQ343⟩
def entry235 : PairEntry 37 := ⟨⟨28,by decide⟩,1,entryQ319,entryQ344⟩
def entry236 : PairEntry 37 := ⟨⟨28,by decide⟩,2,entryQ18,entryQ345⟩
def entry237 : PairEntry 37 := ⟨⟨28,by decide⟩,3,entryQ320,entryQ346⟩
def entry238 : PairEntry 37 := ⟨⟨28,by decide⟩,4,entryQ321,entryQ347⟩
def entry239 : PairEntry 37 := ⟨⟨28,by decide⟩,5,entryQ327,entryQ348⟩
def entry240 : PairEntry 37 := ⟨⟨28,by decide⟩,6,entryQ329,entryQ349⟩
def entry241 : PairEntry 37 := ⟨⟨28,by decide⟩,7,entryQ331,entryQ350⟩
def entry242 : PairEntry 37 := ⟨⟨28,by decide⟩,8,entryQ20,entryQ351⟩
def entry243 : PairEntry 37 := ⟨⟨28,by decide⟩,9,entryQ334,entryQ352⟩
def entry244 : PairEntry 37 := ⟨⟨28,by decide⟩,10,entryQ22,entryQ353⟩
def entry245 : PairEntry 37 := ⟨⟨28,by decide⟩,11,entryQ337,entryQ354⟩
def entry246 : PairEntry 37 := ⟨⟨28,by decide⟩,12,entryQ30,entryQ355⟩
def entry247 : PairEntry 37 := ⟨⟨28,by decide⟩,13,entryQ62,entryQ356⟩
def entry248 : PairEntry 37 := ⟨⟨28,by decide⟩,14,entryQ24,entryQ357⟩
def entry249 : PairEntry 37 := ⟨⟨28,by decide⟩,15,entryQ342,entryQ358⟩
def entry250 : PairEntry 37 := ⟨⟨28,by decide⟩,16,entryQ34,entryQ359⟩
def entry251 : PairEntry 37 := ⟨⟨28,by decide⟩,17,entryQ36,entryQ359⟩
def entry252 : PairEntry 37 := ⟨⟨28,by decide⟩,18,entryQ32,entryQ359⟩
def entry253 : PairEntry 37 := ⟨⟨28,by decide⟩,19,entryQ39,entryQ359⟩
def entry254 : PairEntry 37 := ⟨⟨28,by decide⟩,20,entryQ42,entryQ359⟩
def entry255 : PairEntry 37 := ⟨⟨29,by decide⟩,0,entryQ329,entryQ360⟩
def entry256 : PairEntry 37 := ⟨⟨29,by decide⟩,1,entryQ331,entryQ361⟩
def entry257 : PairEntry 37 := ⟨⟨29,by decide⟩,2,entryQ20,entryQ362⟩
def entry258 : PairEntry 37 := ⟨⟨29,by decide⟩,3,entryQ334,entryQ363⟩
def entry259 : PairEntry 37 := ⟨⟨29,by decide⟩,4,entryQ22,entryQ364⟩
def entry260 : PairEntry 37 := ⟨⟨29,by decide⟩,5,entryQ337,entryQ365⟩
def entry261 : PairEntry 37 := ⟨⟨29,by decide⟩,6,entryQ30,entryQ366⟩
def entry262 : PairEntry 37 := ⟨⟨29,by decide⟩,7,entryQ62,entryQ367⟩
def entry263 : PairEntry 37 := ⟨⟨29,by decide⟩,8,entryQ24,entryQ368⟩
def entry264 : PairEntry 37 := ⟨⟨29,by decide⟩,9,entryQ342,entryQ369⟩
def entry265 : PairEntry 37 := ⟨⟨29,by decide⟩,10,entryQ34,entryQ370⟩
def entry266 : PairEntry 37 := ⟨⟨29,by decide⟩,11,entryQ36,entryQ371⟩
def entry267 : PairEntry 37 := ⟨⟨29,by decide⟩,12,entryQ32,entryQ372⟩
def entry268 : PairEntry 37 := ⟨⟨29,by decide⟩,13,entryQ39,entryQ373⟩
def entry269 : PairEntry 37 := ⟨⟨29,by decide⟩,14,entryQ42,entryQ374⟩
def entry270 : PairEntry 37 := ⟨⟨29,by decide⟩,15,entryQ375,entryQ376⟩
def entry271 : PairEntry 37 := ⟨⟨29,by decide⟩,16,entryQ103,entryQ377⟩
def entry272 : PairEntry 37 := ⟨⟨29,by decide⟩,17,entryQ113,entryQ378⟩
def entry273 : PairEntry 37 := ⟨⟨29,by decide⟩,18,entryQ143,entryQ379⟩
def entry274 : PairEntry 37 := ⟨⟨29,by decide⟩,19,entryQ133,entryQ379⟩
def entry275 : PairEntry 37 := ⟨⟨29,by decide⟩,20,entryQ380,entryQ379⟩
def entry276 : PairEntry 37 := ⟨⟨30,by decide⟩,0,entryQ285,entryQ381⟩
def entry277 : PairEntry 37 := ⟨⟨30,by decide⟩,1,entryQ14,entryQ382⟩
def entry278 : PairEntry 37 := ⟨⟨30,by decide⟩,2,entryQ300,entryQ383⟩
def entry279 : PairEntry 37 := ⟨⟨30,by decide⟩,3,entryQ301,entryQ384⟩
def entry280 : PairEntry 37 := ⟨⟨30,by decide⟩,4,entryQ302,entryQ385⟩
def entry281 : PairEntry 37 := ⟨⟨30,by decide⟩,5,entryQ303,entryQ386⟩
def entry282 : PairEntry 37 := ⟨⟨30,by decide⟩,6,entryQ304,entryQ387⟩
def entry283 : PairEntry 37 := ⟨⟨30,by decide⟩,7,entryQ16,entryQ388⟩
def entry284 : PairEntry 37 := ⟨⟨30,by decide⟩,8,entryQ319,entryQ389⟩
def entry285 : PairEntry 37 := ⟨⟨30,by decide⟩,9,entryQ18,entryQ390⟩
def entry286 : PairEntry 37 := ⟨⟨30,by decide⟩,10,entryQ320,entryQ391⟩
def entry287 : PairEntry 37 := ⟨⟨30,by decide⟩,11,entryQ321,entryQ392⟩
def entry288 : PairEntry 37 := ⟨⟨30,by decide⟩,12,entryQ327,entryQ393⟩
def entry289 : PairEntry 37 := ⟨⟨30,by decide⟩,13,entryQ329,entryQ394⟩
def entry290 : PairEntry 37 := ⟨⟨30,by decide⟩,14,entryQ331,entryQ394⟩
def entry291 : PairEntry 37 := ⟨⟨30,by decide⟩,15,entryQ20,entryQ394⟩
def entry292 : PairEntry 37 := ⟨⟨30,by decide⟩,16,entryQ334,entryQ394⟩
def entry293 : PairEntry 37 := ⟨⟨30,by decide⟩,17,entryQ22,entryQ394⟩
def entry294 : PairEntry 37 := ⟨⟨30,by decide⟩,18,entryQ337,entryQ394⟩
def entry295 : PairEntry 37 := ⟨⟨30,by decide⟩,19,entryQ30,entryQ394⟩
def entry296 : PairEntry 37 := ⟨⟨31,by decide⟩,0,entryQ304,entryQ395⟩
def entry297 : PairEntry 37 := ⟨⟨31,by decide⟩,1,entryQ16,entryQ396⟩
def entry298 : PairEntry 37 := ⟨⟨31,by decide⟩,2,entryQ319,entryQ397⟩
def entry299 : PairEntry 37 := ⟨⟨31,by decide⟩,3,entryQ18,entryQ398⟩
def entry300 : PairEntry 37 := ⟨⟨31,by decide⟩,4,entryQ320,entryQ399⟩
def entry301 : PairEntry 37 := ⟨⟨31,by decide⟩,5,entryQ321,entryQ400⟩
def entry302 : PairEntry 37 := ⟨⟨31,by decide⟩,6,entryQ327,entryQ401⟩
def entry303 : PairEntry 37 := ⟨⟨31,by decide⟩,7,entryQ329,entryQ402⟩
def entry304 : PairEntry 37 := ⟨⟨31,by decide⟩,8,entryQ331,entryQ403⟩
def entry305 : PairEntry 37 := ⟨⟨31,by decide⟩,9,entryQ20,entryQ404⟩
def entry306 : PairEntry 37 := ⟨⟨31,by decide⟩,10,entryQ334,entryQ405⟩
def entry307 : PairEntry 37 := ⟨⟨31,by decide⟩,11,entryQ22,entryQ406⟩
def entry308 : PairEntry 37 := ⟨⟨31,by decide⟩,12,entryQ337,entryQ407⟩
def entry309 : PairEntry 37 := ⟨⟨31,by decide⟩,13,entryQ30,entryQ407⟩
def entry310 : PairEntry 37 := ⟨⟨31,by decide⟩,14,entryQ62,entryQ407⟩
def entry311 : PairEntry 37 := ⟨⟨31,by decide⟩,15,entryQ24,entryQ407⟩
def entry312 : PairEntry 37 := ⟨⟨31,by decide⟩,16,entryQ342,entryQ407⟩
def entry313 : PairEntry 37 := ⟨⟨31,by decide⟩,17,entryQ34,entryQ407⟩
def entry314 : PairEntry 37 := ⟨⟨31,by decide⟩,18,entryQ36,entryQ407⟩
def entry315 : PairEntry 37 := ⟨⟨31,by decide⟩,19,entryQ32,entryQ407⟩
def entry316 : PairEntry 37 := ⟨⟨32,by decide⟩,0,entryQ321,entryQ408⟩
def entry317 : PairEntry 37 := ⟨⟨32,by decide⟩,1,entryQ327,entryQ409⟩
def entry318 : PairEntry 37 := ⟨⟨32,by decide⟩,2,entryQ329,entryQ410⟩
def entry319 : PairEntry 37 := ⟨⟨32,by decide⟩,3,entryQ331,entryQ411⟩
def entry320 : PairEntry 37 := ⟨⟨32,by decide⟩,4,entryQ20,entryQ412⟩
def entry321 : PairEntry 37 := ⟨⟨32,by decide⟩,5,entryQ334,entryQ413⟩
def entry322 : PairEntry 37 := ⟨⟨32,by decide⟩,6,entryQ22,entryQ414⟩
def entry323 : PairEntry 37 := ⟨⟨32,by decide⟩,7,entryQ337,entryQ415⟩
def entry324 : PairEntry 37 := ⟨⟨32,by decide⟩,8,entryQ30,entryQ416⟩
def entry325 : PairEntry 37 := ⟨⟨32,by decide⟩,9,entryQ62,entryQ417⟩
def entry326 : PairEntry 37 := ⟨⟨32,by decide⟩,10,entryQ24,entryQ418⟩
def entry327 : PairEntry 37 := ⟨⟨32,by decide⟩,11,entryQ342,entryQ419⟩
def entry328 : PairEntry 37 := ⟨⟨32,by decide⟩,12,entryQ34,entryQ420⟩
def entry329 : PairEntry 37 := ⟨⟨32,by decide⟩,13,entryQ36,entryQ420⟩
def entry330 : PairEntry 37 := ⟨⟨32,by decide⟩,14,entryQ32,entryQ420⟩
def entry331 : PairEntry 37 := ⟨⟨32,by decide⟩,15,entryQ39,entryQ420⟩
def entry332 : PairEntry 37 := ⟨⟨32,by decide⟩,16,entryQ42,entryQ420⟩
def entry333 : PairEntry 37 := ⟨⟨32,by decide⟩,17,entryQ375,entryQ420⟩
def entry334 : PairEntry 37 := ⟨⟨32,by decide⟩,18,entryQ103,entryQ420⟩
def entry335 : PairEntry 37 := ⟨⟨32,by decide⟩,19,entryQ113,entryQ420⟩
def entry336 : PairEntry 37 := ⟨⟨33,by decide⟩,0,entryQ30,entryQ421⟩
def entry337 : PairEntry 37 := ⟨⟨33,by decide⟩,1,entryQ62,entryQ422⟩
def entry338 : PairEntry 37 := ⟨⟨33,by decide⟩,2,entryQ24,entryQ423⟩
def entry339 : PairEntry 37 := ⟨⟨33,by decide⟩,3,entryQ342,entryQ424⟩
def entry340 : PairEntry 37 := ⟨⟨33,by decide⟩,4,entryQ34,entryQ425⟩
def entry341 : PairEntry 37 := ⟨⟨33,by decide⟩,5,entryQ36,entryQ426⟩
def entry342 : PairEntry 37 := ⟨⟨33,by decide⟩,6,entryQ32,entryQ427⟩
def entry343 : PairEntry 37 := ⟨⟨33,by decide⟩,7,entryQ39,entryQ428⟩
def entry344 : PairEntry 37 := ⟨⟨33,by decide⟩,8,entryQ42,entryQ429⟩
def entry345 : PairEntry 37 := ⟨⟨33,by decide⟩,9,entryQ375,entryQ430⟩
def entry346 : PairEntry 37 := ⟨⟨33,by decide⟩,10,entryQ103,entryQ431⟩
def entry347 : PairEntry 37 := ⟨⟨33,by decide⟩,11,entryQ113,entryQ432⟩
def entry348 : PairEntry 37 := ⟨⟨33,by decide⟩,12,entryQ143,entryQ433⟩
def entry349 : PairEntry 37 := ⟨⟨33,by decide⟩,13,entryQ133,entryQ434⟩
def entry350 : PairEntry 37 := ⟨⟨33,by decide⟩,14,entryQ380,entryQ434⟩
def entry351 : PairEntry 37 := ⟨⟨33,by decide⟩,15,entryQ435,entryQ434⟩
def entry352 : PairEntry 37 := ⟨⟨33,by decide⟩,16,entryQ170,entryQ434⟩
def entry353 : PairEntry 37 := ⟨⟨33,by decide⟩,17,entryQ158,entryQ434⟩
def entry354 : PairEntry 37 := ⟨⟨33,by decide⟩,18,entryQ436,entryQ434⟩
def entry355 : PairEntry 37 := ⟨⟨33,by decide⟩,19,entryQ180,entryQ434⟩
def entry356 : PairEntry 37 := ⟨⟨33,by decide⟩,20,entryQ198,entryQ434⟩
def entry357 : PairEntry 37 := ⟨⟨34,by decide⟩,0,entryQ42,entryQ437⟩
def entry358 : PairEntry 37 := ⟨⟨34,by decide⟩,1,entryQ375,entryQ438⟩
def entry359 : PairEntry 37 := ⟨⟨34,by decide⟩,2,entryQ103,entryQ439⟩
def entry360 : PairEntry 37 := ⟨⟨34,by decide⟩,3,entryQ113,entryQ440⟩
def entry361 : PairEntry 37 := ⟨⟨34,by decide⟩,4,entryQ143,entryQ441⟩
def entry362 : PairEntry 37 := ⟨⟨34,by decide⟩,5,entryQ133,entryQ442⟩
def entry363 : PairEntry 37 := ⟨⟨34,by decide⟩,6,entryQ380,entryQ443⟩
def entry364 : PairEntry 37 := ⟨⟨34,by decide⟩,7,entryQ435,entryQ444⟩
def entry365 : PairEntry 37 := ⟨⟨34,by decide⟩,8,entryQ170,entryQ445⟩
def entry366 : PairEntry 37 := ⟨⟨34,by decide⟩,9,entryQ158,entryQ446⟩
def entry367 : PairEntry 37 := ⟨⟨34,by decide⟩,10,entryQ436,entryQ447⟩
def entry368 : PairEntry 37 := ⟨⟨34,by decide⟩,11,entryQ180,entryQ448⟩
def entry369 : PairEntry 37 := ⟨⟨34,by decide⟩,12,entryQ198,entryQ449⟩
def entry370 : PairEntry 37 := ⟨⟨34,by decide⟩,13,entryQ212,entryQ450⟩
def entry371 : PairEntry 37 := ⟨⟨34,by decide⟩,14,entryQ240,entryQ450⟩
def entry372 : PairEntry 37 := ⟨⟨34,by decide⟩,15,entryQ451,entryQ450⟩
def entry373 : PairEntry 37 := ⟨⟨34,by decide⟩,16,entryQ234,entryQ450⟩
def entry374 : PairEntry 37 := ⟨⟨34,by decide⟩,17,entryQ452,entryQ450⟩
def entry375 : PairEntry 37 := ⟨⟨34,by decide⟩,18,entryQ453,entryQ450⟩
def entry376 : PairEntry 37 := ⟨⟨34,by decide⟩,19,entryQ454,entryQ450⟩
def entry377 : PairEntry 37 := ⟨⟨34,by decide⟩,20,entryQ236,entryQ450⟩
def entry378 : PairEntry 37 := ⟨⟨35,by decide⟩,0,entryQ436,entryQ455⟩
def entry379 : PairEntry 37 := ⟨⟨35,by decide⟩,1,entryQ180,entryQ456⟩
def entry380 : PairEntry 37 := ⟨⟨35,by decide⟩,2,entryQ198,entryQ457⟩
def entry381 : PairEntry 37 := ⟨⟨35,by decide⟩,3,entryQ212,entryQ458⟩
def entry382 : PairEntry 37 := ⟨⟨35,by decide⟩,4,entryQ240,entryQ459⟩
def entry383 : PairEntry 37 := ⟨⟨35,by decide⟩,5,entryQ451,entryQ460⟩
def entry384 : PairEntry 37 := ⟨⟨35,by decide⟩,6,entryQ234,entryQ461⟩
def entry385 : PairEntry 37 := ⟨⟨35,by decide⟩,7,entryQ452,entryQ462⟩
def entry386 : PairEntry 37 := ⟨⟨35,by decide⟩,8,entryQ453,entryQ463⟩
def entry387 : PairEntry 37 := ⟨⟨35,by decide⟩,9,entryQ454,entryQ464⟩
def entry388 : PairEntry 37 := ⟨⟨35,by decide⟩,10,entryQ236,entryQ465⟩
def entry389 : PairEntry 37 := ⟨⟨35,by decide⟩,11,entryQ466,entryQ467⟩
def entry390 : PairEntry 37 := ⟨⟨35,by decide⟩,12,entryQ242,entryQ468⟩
def entry391 : PairEntry 37 := ⟨⟨35,by decide⟩,13,entryQ469,entryQ470⟩
def entry392 : PairEntry 37 := ⟨⟨35,by decide⟩,14,entryQ253,entryQ470⟩
def entry393 : PairEntry 37 := ⟨⟨35,by decide⟩,15,entryQ471,entryQ470⟩
def entry394 : PairEntry 37 := ⟨⟨35,by decide⟩,16,entryQ250,entryQ470⟩
def entry395 : PairEntry 37 := ⟨⟨35,by decide⟩,17,entryQ472,entryQ470⟩
def entry396 : PairEntry 37 := ⟨⟨35,by decide⟩,18,entryQ473,entryQ470⟩
def entry397 : PairEntry 37 := ⟨⟨35,by decide⟩,19,entryQ474,entryQ470⟩
def entry398 : PairEntry 37 := ⟨⟨35,by decide⟩,20,entryQ475,entryQ470⟩
def entry399 : PairEntry 37 := ⟨⟨36,by decide⟩,0,entryQ282,entryQ476⟩
def entry400 : PairEntry 37 := ⟨⟨36,by decide⟩,1,entryQ12,entryQ477⟩
def entry401 : PairEntry 37 := ⟨⟨36,by decide⟩,2,entryQ283,entryQ478⟩
def entry402 : PairEntry 37 := ⟨⟨36,by decide⟩,3,entryQ284,entryQ479⟩
def entry403 : PairEntry 37 := ⟨⟨36,by decide⟩,4,entryQ285,entryQ480⟩
def entry404 : PairEntry 37 := ⟨⟨36,by decide⟩,5,entryQ14,entryQ481⟩
def entry405 : PairEntry 37 := ⟨⟨36,by decide⟩,6,entryQ300,entryQ482⟩
def entry406 : PairEntry 37 := ⟨⟨36,by decide⟩,7,entryQ301,entryQ483⟩
def entry407 : PairEntry 37 := ⟨⟨36,by decide⟩,8,entryQ302,entryQ484⟩
def entry408 : PairEntry 37 := ⟨⟨36,by decide⟩,9,entryQ303,entryQ485⟩
def entry409 : PairEntry 37 := ⟨⟨36,by decide⟩,10,entryQ304,entryQ486⟩
def entry410 : PairEntry 37 := ⟨⟨36,by decide⟩,11,entryQ16,entryQ487⟩
def entry411 : PairEntry 37 := ⟨⟨36,by decide⟩,12,entryQ319,entryQ488⟩
def entry412 : PairEntry 37 := ⟨⟨36,by decide⟩,13,entryQ18,entryQ488⟩
def entry413 : PairEntry 37 := ⟨⟨36,by decide⟩,14,entryQ320,entryQ488⟩
def entry414 : PairEntry 37 := ⟨⟨36,by decide⟩,15,entryQ321,entryQ488⟩
def entry415 : PairEntry 37 := ⟨⟨36,by decide⟩,16,entryQ327,entryQ488⟩
def entry416 : PairEntry 37 := ⟨⟨36,by decide⟩,17,entryQ329,entryQ488⟩
def entry417 : PairEntry 37 := ⟨⟨36,by decide⟩,18,entryQ331,entryQ488⟩
def entry418 : PairEntry 37 := ⟨⟨36,by decide⟩,19,entryQ20,entryQ488⟩
def entryTail419 : List (PairEntry 37) := []
theorem entryTail419_length : entryTail419.length=0 := rfl
def entryTail418 : List (PairEntry 37) := entry418::entryTail419
theorem entryTail418_length : entryTail418.length=1 := by
  change entryTail419.length+1=1
  rw [entryTail419_length]
def entryTail417 : List (PairEntry 37) := entry417::entryTail418
theorem entryTail417_length : entryTail417.length=2 := by
  change entryTail418.length+1=2
  rw [entryTail418_length]
def entryTail416 : List (PairEntry 37) := entry416::entryTail417
theorem entryTail416_length : entryTail416.length=3 := by
  change entryTail417.length+1=3
  rw [entryTail417_length]
def entryTail415 : List (PairEntry 37) := entry415::entryTail416
theorem entryTail415_length : entryTail415.length=4 := by
  change entryTail416.length+1=4
  rw [entryTail416_length]
def entryTail414 : List (PairEntry 37) := entry414::entryTail415
theorem entryTail414_length : entryTail414.length=5 := by
  change entryTail415.length+1=5
  rw [entryTail415_length]
def entryTail413 : List (PairEntry 37) := entry413::entryTail414
theorem entryTail413_length : entryTail413.length=6 := by
  change entryTail414.length+1=6
  rw [entryTail414_length]
def entryTail412 : List (PairEntry 37) := entry412::entryTail413
theorem entryTail412_length : entryTail412.length=7 := by
  change entryTail413.length+1=7
  rw [entryTail413_length]
def entryTail411 : List (PairEntry 37) := entry411::entryTail412
theorem entryTail411_length : entryTail411.length=8 := by
  change entryTail412.length+1=8
  rw [entryTail412_length]
def entryTail410 : List (PairEntry 37) := entry410::entryTail411
theorem entryTail410_length : entryTail410.length=9 := by
  change entryTail411.length+1=9
  rw [entryTail411_length]
def entryTail409 : List (PairEntry 37) := entry409::entryTail410
theorem entryTail409_length : entryTail409.length=10 := by
  change entryTail410.length+1=10
  rw [entryTail410_length]
def entryTail408 : List (PairEntry 37) := entry408::entryTail409
theorem entryTail408_length : entryTail408.length=11 := by
  change entryTail409.length+1=11
  rw [entryTail409_length]
def entryTail407 : List (PairEntry 37) := entry407::entryTail408
theorem entryTail407_length : entryTail407.length=12 := by
  change entryTail408.length+1=12
  rw [entryTail408_length]
def entryTail406 : List (PairEntry 37) := entry406::entryTail407
theorem entryTail406_length : entryTail406.length=13 := by
  change entryTail407.length+1=13
  rw [entryTail407_length]
def entryTail405 : List (PairEntry 37) := entry405::entryTail406
theorem entryTail405_length : entryTail405.length=14 := by
  change entryTail406.length+1=14
  rw [entryTail406_length]
def entryTail404 : List (PairEntry 37) := entry404::entryTail405
theorem entryTail404_length : entryTail404.length=15 := by
  change entryTail405.length+1=15
  rw [entryTail405_length]
def entryTail403 : List (PairEntry 37) := entry403::entryTail404
theorem entryTail403_length : entryTail403.length=16 := by
  change entryTail404.length+1=16
  rw [entryTail404_length]
def entryTail402 : List (PairEntry 37) := entry402::entryTail403
theorem entryTail402_length : entryTail402.length=17 := by
  change entryTail403.length+1=17
  rw [entryTail403_length]
def entryTail401 : List (PairEntry 37) := entry401::entryTail402
theorem entryTail401_length : entryTail401.length=18 := by
  change entryTail402.length+1=18
  rw [entryTail402_length]
def entryTail400 : List (PairEntry 37) := entry400::entryTail401
theorem entryTail400_length : entryTail400.length=19 := by
  change entryTail401.length+1=19
  rw [entryTail401_length]
def entryTail399 : List (PairEntry 37) := entry399::entryTail400
theorem entryTail399_length : entryTail399.length=20 := by
  change entryTail400.length+1=20
  rw [entryTail400_length]
def entryTail398 : List (PairEntry 37) := entry398::entryTail399
theorem entryTail398_length : entryTail398.length=21 := by
  change entryTail399.length+1=21
  rw [entryTail399_length]
def entryTail397 : List (PairEntry 37) := entry397::entryTail398
theorem entryTail397_length : entryTail397.length=22 := by
  change entryTail398.length+1=22
  rw [entryTail398_length]
def entryTail396 : List (PairEntry 37) := entry396::entryTail397
theorem entryTail396_length : entryTail396.length=23 := by
  change entryTail397.length+1=23
  rw [entryTail397_length]
def entryTail395 : List (PairEntry 37) := entry395::entryTail396
theorem entryTail395_length : entryTail395.length=24 := by
  change entryTail396.length+1=24
  rw [entryTail396_length]
def entryTail394 : List (PairEntry 37) := entry394::entryTail395
theorem entryTail394_length : entryTail394.length=25 := by
  change entryTail395.length+1=25
  rw [entryTail395_length]
def entryTail393 : List (PairEntry 37) := entry393::entryTail394
theorem entryTail393_length : entryTail393.length=26 := by
  change entryTail394.length+1=26
  rw [entryTail394_length]
def entryTail392 : List (PairEntry 37) := entry392::entryTail393
theorem entryTail392_length : entryTail392.length=27 := by
  change entryTail393.length+1=27
  rw [entryTail393_length]
def entryTail391 : List (PairEntry 37) := entry391::entryTail392
theorem entryTail391_length : entryTail391.length=28 := by
  change entryTail392.length+1=28
  rw [entryTail392_length]
def entryTail390 : List (PairEntry 37) := entry390::entryTail391
theorem entryTail390_length : entryTail390.length=29 := by
  change entryTail391.length+1=29
  rw [entryTail391_length]
def entryTail389 : List (PairEntry 37) := entry389::entryTail390
theorem entryTail389_length : entryTail389.length=30 := by
  change entryTail390.length+1=30
  rw [entryTail390_length]
def entryTail388 : List (PairEntry 37) := entry388::entryTail389
theorem entryTail388_length : entryTail388.length=31 := by
  change entryTail389.length+1=31
  rw [entryTail389_length]
def entryTail387 : List (PairEntry 37) := entry387::entryTail388
theorem entryTail387_length : entryTail387.length=32 := by
  change entryTail388.length+1=32
  rw [entryTail388_length]
def entryTail386 : List (PairEntry 37) := entry386::entryTail387
theorem entryTail386_length : entryTail386.length=33 := by
  change entryTail387.length+1=33
  rw [entryTail387_length]
def entryTail385 : List (PairEntry 37) := entry385::entryTail386
theorem entryTail385_length : entryTail385.length=34 := by
  change entryTail386.length+1=34
  rw [entryTail386_length]
def entryTail384 : List (PairEntry 37) := entry384::entryTail385
theorem entryTail384_length : entryTail384.length=35 := by
  change entryTail385.length+1=35
  rw [entryTail385_length]
def entryTail383 : List (PairEntry 37) := entry383::entryTail384
theorem entryTail383_length : entryTail383.length=36 := by
  change entryTail384.length+1=36
  rw [entryTail384_length]
def entryTail382 : List (PairEntry 37) := entry382::entryTail383
theorem entryTail382_length : entryTail382.length=37 := by
  change entryTail383.length+1=37
  rw [entryTail383_length]
def entryTail381 : List (PairEntry 37) := entry381::entryTail382
theorem entryTail381_length : entryTail381.length=38 := by
  change entryTail382.length+1=38
  rw [entryTail382_length]
def entryTail380 : List (PairEntry 37) := entry380::entryTail381
theorem entryTail380_length : entryTail380.length=39 := by
  change entryTail381.length+1=39
  rw [entryTail381_length]
def entryTail379 : List (PairEntry 37) := entry379::entryTail380
theorem entryTail379_length : entryTail379.length=40 := by
  change entryTail380.length+1=40
  rw [entryTail380_length]
def entryTail378 : List (PairEntry 37) := entry378::entryTail379
theorem entryTail378_length : entryTail378.length=41 := by
  change entryTail379.length+1=41
  rw [entryTail379_length]
def entryTail377 : List (PairEntry 37) := entry377::entryTail378
theorem entryTail377_length : entryTail377.length=42 := by
  change entryTail378.length+1=42
  rw [entryTail378_length]
def entryTail376 : List (PairEntry 37) := entry376::entryTail377
theorem entryTail376_length : entryTail376.length=43 := by
  change entryTail377.length+1=43
  rw [entryTail377_length]
def entryTail375 : List (PairEntry 37) := entry375::entryTail376
theorem entryTail375_length : entryTail375.length=44 := by
  change entryTail376.length+1=44
  rw [entryTail376_length]
def entryTail374 : List (PairEntry 37) := entry374::entryTail375
theorem entryTail374_length : entryTail374.length=45 := by
  change entryTail375.length+1=45
  rw [entryTail375_length]
def entryTail373 : List (PairEntry 37) := entry373::entryTail374
theorem entryTail373_length : entryTail373.length=46 := by
  change entryTail374.length+1=46
  rw [entryTail374_length]
def entryTail372 : List (PairEntry 37) := entry372::entryTail373
theorem entryTail372_length : entryTail372.length=47 := by
  change entryTail373.length+1=47
  rw [entryTail373_length]
def entryTail371 : List (PairEntry 37) := entry371::entryTail372
theorem entryTail371_length : entryTail371.length=48 := by
  change entryTail372.length+1=48
  rw [entryTail372_length]
def entryTail370 : List (PairEntry 37) := entry370::entryTail371
theorem entryTail370_length : entryTail370.length=49 := by
  change entryTail371.length+1=49
  rw [entryTail371_length]
def entryTail369 : List (PairEntry 37) := entry369::entryTail370
theorem entryTail369_length : entryTail369.length=50 := by
  change entryTail370.length+1=50
  rw [entryTail370_length]
def entryTail368 : List (PairEntry 37) := entry368::entryTail369
theorem entryTail368_length : entryTail368.length=51 := by
  change entryTail369.length+1=51
  rw [entryTail369_length]
def entryTail367 : List (PairEntry 37) := entry367::entryTail368
theorem entryTail367_length : entryTail367.length=52 := by
  change entryTail368.length+1=52
  rw [entryTail368_length]
def entryTail366 : List (PairEntry 37) := entry366::entryTail367
theorem entryTail366_length : entryTail366.length=53 := by
  change entryTail367.length+1=53
  rw [entryTail367_length]
def entryTail365 : List (PairEntry 37) := entry365::entryTail366
theorem entryTail365_length : entryTail365.length=54 := by
  change entryTail366.length+1=54
  rw [entryTail366_length]
def entryTail364 : List (PairEntry 37) := entry364::entryTail365
theorem entryTail364_length : entryTail364.length=55 := by
  change entryTail365.length+1=55
  rw [entryTail365_length]
def entryTail363 : List (PairEntry 37) := entry363::entryTail364
theorem entryTail363_length : entryTail363.length=56 := by
  change entryTail364.length+1=56
  rw [entryTail364_length]
def entryTail362 : List (PairEntry 37) := entry362::entryTail363
theorem entryTail362_length : entryTail362.length=57 := by
  change entryTail363.length+1=57
  rw [entryTail363_length]
def entryTail361 : List (PairEntry 37) := entry361::entryTail362
theorem entryTail361_length : entryTail361.length=58 := by
  change entryTail362.length+1=58
  rw [entryTail362_length]
def entryTail360 : List (PairEntry 37) := entry360::entryTail361
theorem entryTail360_length : entryTail360.length=59 := by
  change entryTail361.length+1=59
  rw [entryTail361_length]
def entryTail359 : List (PairEntry 37) := entry359::entryTail360
theorem entryTail359_length : entryTail359.length=60 := by
  change entryTail360.length+1=60
  rw [entryTail360_length]
def entryTail358 : List (PairEntry 37) := entry358::entryTail359
theorem entryTail358_length : entryTail358.length=61 := by
  change entryTail359.length+1=61
  rw [entryTail359_length]
def entryTail357 : List (PairEntry 37) := entry357::entryTail358
theorem entryTail357_length : entryTail357.length=62 := by
  change entryTail358.length+1=62
  rw [entryTail358_length]
def entryTail356 : List (PairEntry 37) := entry356::entryTail357
theorem entryTail356_length : entryTail356.length=63 := by
  change entryTail357.length+1=63
  rw [entryTail357_length]
def entryTail355 : List (PairEntry 37) := entry355::entryTail356
theorem entryTail355_length : entryTail355.length=64 := by
  change entryTail356.length+1=64
  rw [entryTail356_length]
def entryTail354 : List (PairEntry 37) := entry354::entryTail355
theorem entryTail354_length : entryTail354.length=65 := by
  change entryTail355.length+1=65
  rw [entryTail355_length]
def entryTail353 : List (PairEntry 37) := entry353::entryTail354
theorem entryTail353_length : entryTail353.length=66 := by
  change entryTail354.length+1=66
  rw [entryTail354_length]
def entryTail352 : List (PairEntry 37) := entry352::entryTail353
theorem entryTail352_length : entryTail352.length=67 := by
  change entryTail353.length+1=67
  rw [entryTail353_length]
def entryTail351 : List (PairEntry 37) := entry351::entryTail352
theorem entryTail351_length : entryTail351.length=68 := by
  change entryTail352.length+1=68
  rw [entryTail352_length]
def entryTail350 : List (PairEntry 37) := entry350::entryTail351
theorem entryTail350_length : entryTail350.length=69 := by
  change entryTail351.length+1=69
  rw [entryTail351_length]
def entryTail349 : List (PairEntry 37) := entry349::entryTail350
theorem entryTail349_length : entryTail349.length=70 := by
  change entryTail350.length+1=70
  rw [entryTail350_length]
def entryTail348 : List (PairEntry 37) := entry348::entryTail349
theorem entryTail348_length : entryTail348.length=71 := by
  change entryTail349.length+1=71
  rw [entryTail349_length]
def entryTail347 : List (PairEntry 37) := entry347::entryTail348
theorem entryTail347_length : entryTail347.length=72 := by
  change entryTail348.length+1=72
  rw [entryTail348_length]
def entryTail346 : List (PairEntry 37) := entry346::entryTail347
theorem entryTail346_length : entryTail346.length=73 := by
  change entryTail347.length+1=73
  rw [entryTail347_length]
def entryTail345 : List (PairEntry 37) := entry345::entryTail346
theorem entryTail345_length : entryTail345.length=74 := by
  change entryTail346.length+1=74
  rw [entryTail346_length]
def entryTail344 : List (PairEntry 37) := entry344::entryTail345
theorem entryTail344_length : entryTail344.length=75 := by
  change entryTail345.length+1=75
  rw [entryTail345_length]
def entryTail343 : List (PairEntry 37) := entry343::entryTail344
theorem entryTail343_length : entryTail343.length=76 := by
  change entryTail344.length+1=76
  rw [entryTail344_length]
def entryTail342 : List (PairEntry 37) := entry342::entryTail343
theorem entryTail342_length : entryTail342.length=77 := by
  change entryTail343.length+1=77
  rw [entryTail343_length]
def entryTail341 : List (PairEntry 37) := entry341::entryTail342
theorem entryTail341_length : entryTail341.length=78 := by
  change entryTail342.length+1=78
  rw [entryTail342_length]
def entryTail340 : List (PairEntry 37) := entry340::entryTail341
theorem entryTail340_length : entryTail340.length=79 := by
  change entryTail341.length+1=79
  rw [entryTail341_length]
def entryTail339 : List (PairEntry 37) := entry339::entryTail340
theorem entryTail339_length : entryTail339.length=80 := by
  change entryTail340.length+1=80
  rw [entryTail340_length]
def entryTail338 : List (PairEntry 37) := entry338::entryTail339
theorem entryTail338_length : entryTail338.length=81 := by
  change entryTail339.length+1=81
  rw [entryTail339_length]
def entryTail337 : List (PairEntry 37) := entry337::entryTail338
theorem entryTail337_length : entryTail337.length=82 := by
  change entryTail338.length+1=82
  rw [entryTail338_length]
def entryTail336 : List (PairEntry 37) := entry336::entryTail337
theorem entryTail336_length : entryTail336.length=83 := by
  change entryTail337.length+1=83
  rw [entryTail337_length]
def entryTail335 : List (PairEntry 37) := entry335::entryTail336
theorem entryTail335_length : entryTail335.length=84 := by
  change entryTail336.length+1=84
  rw [entryTail336_length]
def entryTail334 : List (PairEntry 37) := entry334::entryTail335
theorem entryTail334_length : entryTail334.length=85 := by
  change entryTail335.length+1=85
  rw [entryTail335_length]
def entryTail333 : List (PairEntry 37) := entry333::entryTail334
theorem entryTail333_length : entryTail333.length=86 := by
  change entryTail334.length+1=86
  rw [entryTail334_length]
def entryTail332 : List (PairEntry 37) := entry332::entryTail333
theorem entryTail332_length : entryTail332.length=87 := by
  change entryTail333.length+1=87
  rw [entryTail333_length]
def entryTail331 : List (PairEntry 37) := entry331::entryTail332
theorem entryTail331_length : entryTail331.length=88 := by
  change entryTail332.length+1=88
  rw [entryTail332_length]
def entryTail330 : List (PairEntry 37) := entry330::entryTail331
theorem entryTail330_length : entryTail330.length=89 := by
  change entryTail331.length+1=89
  rw [entryTail331_length]
def entryTail329 : List (PairEntry 37) := entry329::entryTail330
theorem entryTail329_length : entryTail329.length=90 := by
  change entryTail330.length+1=90
  rw [entryTail330_length]
def entryTail328 : List (PairEntry 37) := entry328::entryTail329
theorem entryTail328_length : entryTail328.length=91 := by
  change entryTail329.length+1=91
  rw [entryTail329_length]
def entryTail327 : List (PairEntry 37) := entry327::entryTail328
theorem entryTail327_length : entryTail327.length=92 := by
  change entryTail328.length+1=92
  rw [entryTail328_length]
def entryTail326 : List (PairEntry 37) := entry326::entryTail327
theorem entryTail326_length : entryTail326.length=93 := by
  change entryTail327.length+1=93
  rw [entryTail327_length]
def entryTail325 : List (PairEntry 37) := entry325::entryTail326
theorem entryTail325_length : entryTail325.length=94 := by
  change entryTail326.length+1=94
  rw [entryTail326_length]
def entryTail324 : List (PairEntry 37) := entry324::entryTail325
theorem entryTail324_length : entryTail324.length=95 := by
  change entryTail325.length+1=95
  rw [entryTail325_length]
def entryTail323 : List (PairEntry 37) := entry323::entryTail324
theorem entryTail323_length : entryTail323.length=96 := by
  change entryTail324.length+1=96
  rw [entryTail324_length]
def entryTail322 : List (PairEntry 37) := entry322::entryTail323
theorem entryTail322_length : entryTail322.length=97 := by
  change entryTail323.length+1=97
  rw [entryTail323_length]
def entryTail321 : List (PairEntry 37) := entry321::entryTail322
theorem entryTail321_length : entryTail321.length=98 := by
  change entryTail322.length+1=98
  rw [entryTail322_length]
def entryTail320 : List (PairEntry 37) := entry320::entryTail321
theorem entryTail320_length : entryTail320.length=99 := by
  change entryTail321.length+1=99
  rw [entryTail321_length]
def entryTail319 : List (PairEntry 37) := entry319::entryTail320
theorem entryTail319_length : entryTail319.length=100 := by
  change entryTail320.length+1=100
  rw [entryTail320_length]
def entryTail318 : List (PairEntry 37) := entry318::entryTail319
theorem entryTail318_length : entryTail318.length=101 := by
  change entryTail319.length+1=101
  rw [entryTail319_length]
def entryTail317 : List (PairEntry 37) := entry317::entryTail318
theorem entryTail317_length : entryTail317.length=102 := by
  change entryTail318.length+1=102
  rw [entryTail318_length]
def entryTail316 : List (PairEntry 37) := entry316::entryTail317
theorem entryTail316_length : entryTail316.length=103 := by
  change entryTail317.length+1=103
  rw [entryTail317_length]
def entryTail315 : List (PairEntry 37) := entry315::entryTail316
theorem entryTail315_length : entryTail315.length=104 := by
  change entryTail316.length+1=104
  rw [entryTail316_length]
def entryTail314 : List (PairEntry 37) := entry314::entryTail315
theorem entryTail314_length : entryTail314.length=105 := by
  change entryTail315.length+1=105
  rw [entryTail315_length]
def entryTail313 : List (PairEntry 37) := entry313::entryTail314
theorem entryTail313_length : entryTail313.length=106 := by
  change entryTail314.length+1=106
  rw [entryTail314_length]
def entryTail312 : List (PairEntry 37) := entry312::entryTail313
theorem entryTail312_length : entryTail312.length=107 := by
  change entryTail313.length+1=107
  rw [entryTail313_length]
def entryTail311 : List (PairEntry 37) := entry311::entryTail312
theorem entryTail311_length : entryTail311.length=108 := by
  change entryTail312.length+1=108
  rw [entryTail312_length]
def entryTail310 : List (PairEntry 37) := entry310::entryTail311
theorem entryTail310_length : entryTail310.length=109 := by
  change entryTail311.length+1=109
  rw [entryTail311_length]
def entryTail309 : List (PairEntry 37) := entry309::entryTail310
theorem entryTail309_length : entryTail309.length=110 := by
  change entryTail310.length+1=110
  rw [entryTail310_length]
def entryTail308 : List (PairEntry 37) := entry308::entryTail309
theorem entryTail308_length : entryTail308.length=111 := by
  change entryTail309.length+1=111
  rw [entryTail309_length]
def entryTail307 : List (PairEntry 37) := entry307::entryTail308
theorem entryTail307_length : entryTail307.length=112 := by
  change entryTail308.length+1=112
  rw [entryTail308_length]
def entryTail306 : List (PairEntry 37) := entry306::entryTail307
theorem entryTail306_length : entryTail306.length=113 := by
  change entryTail307.length+1=113
  rw [entryTail307_length]
def entryTail305 : List (PairEntry 37) := entry305::entryTail306
theorem entryTail305_length : entryTail305.length=114 := by
  change entryTail306.length+1=114
  rw [entryTail306_length]
def entryTail304 : List (PairEntry 37) := entry304::entryTail305
theorem entryTail304_length : entryTail304.length=115 := by
  change entryTail305.length+1=115
  rw [entryTail305_length]
def entryTail303 : List (PairEntry 37) := entry303::entryTail304
theorem entryTail303_length : entryTail303.length=116 := by
  change entryTail304.length+1=116
  rw [entryTail304_length]
def entryTail302 : List (PairEntry 37) := entry302::entryTail303
theorem entryTail302_length : entryTail302.length=117 := by
  change entryTail303.length+1=117
  rw [entryTail303_length]
def entryTail301 : List (PairEntry 37) := entry301::entryTail302
theorem entryTail301_length : entryTail301.length=118 := by
  change entryTail302.length+1=118
  rw [entryTail302_length]
def entryTail300 : List (PairEntry 37) := entry300::entryTail301
theorem entryTail300_length : entryTail300.length=119 := by
  change entryTail301.length+1=119
  rw [entryTail301_length]
def entryTail299 : List (PairEntry 37) := entry299::entryTail300
theorem entryTail299_length : entryTail299.length=120 := by
  change entryTail300.length+1=120
  rw [entryTail300_length]
def entryTail298 : List (PairEntry 37) := entry298::entryTail299
theorem entryTail298_length : entryTail298.length=121 := by
  change entryTail299.length+1=121
  rw [entryTail299_length]
def entryTail297 : List (PairEntry 37) := entry297::entryTail298
theorem entryTail297_length : entryTail297.length=122 := by
  change entryTail298.length+1=122
  rw [entryTail298_length]
def entryTail296 : List (PairEntry 37) := entry296::entryTail297
theorem entryTail296_length : entryTail296.length=123 := by
  change entryTail297.length+1=123
  rw [entryTail297_length]
def entryTail295 : List (PairEntry 37) := entry295::entryTail296
theorem entryTail295_length : entryTail295.length=124 := by
  change entryTail296.length+1=124
  rw [entryTail296_length]
def entryTail294 : List (PairEntry 37) := entry294::entryTail295
theorem entryTail294_length : entryTail294.length=125 := by
  change entryTail295.length+1=125
  rw [entryTail295_length]
def entryTail293 : List (PairEntry 37) := entry293::entryTail294
theorem entryTail293_length : entryTail293.length=126 := by
  change entryTail294.length+1=126
  rw [entryTail294_length]
def entryTail292 : List (PairEntry 37) := entry292::entryTail293
theorem entryTail292_length : entryTail292.length=127 := by
  change entryTail293.length+1=127
  rw [entryTail293_length]
def entryTail291 : List (PairEntry 37) := entry291::entryTail292
theorem entryTail291_length : entryTail291.length=128 := by
  change entryTail292.length+1=128
  rw [entryTail292_length]
def entryTail290 : List (PairEntry 37) := entry290::entryTail291
theorem entryTail290_length : entryTail290.length=129 := by
  change entryTail291.length+1=129
  rw [entryTail291_length]
def entryTail289 : List (PairEntry 37) := entry289::entryTail290
theorem entryTail289_length : entryTail289.length=130 := by
  change entryTail290.length+1=130
  rw [entryTail290_length]
def entryTail288 : List (PairEntry 37) := entry288::entryTail289
theorem entryTail288_length : entryTail288.length=131 := by
  change entryTail289.length+1=131
  rw [entryTail289_length]
def entryTail287 : List (PairEntry 37) := entry287::entryTail288
theorem entryTail287_length : entryTail287.length=132 := by
  change entryTail288.length+1=132
  rw [entryTail288_length]
def entryTail286 : List (PairEntry 37) := entry286::entryTail287
theorem entryTail286_length : entryTail286.length=133 := by
  change entryTail287.length+1=133
  rw [entryTail287_length]
def entryTail285 : List (PairEntry 37) := entry285::entryTail286
theorem entryTail285_length : entryTail285.length=134 := by
  change entryTail286.length+1=134
  rw [entryTail286_length]
def entryTail284 : List (PairEntry 37) := entry284::entryTail285
theorem entryTail284_length : entryTail284.length=135 := by
  change entryTail285.length+1=135
  rw [entryTail285_length]
def entryTail283 : List (PairEntry 37) := entry283::entryTail284
theorem entryTail283_length : entryTail283.length=136 := by
  change entryTail284.length+1=136
  rw [entryTail284_length]
def entryTail282 : List (PairEntry 37) := entry282::entryTail283
theorem entryTail282_length : entryTail282.length=137 := by
  change entryTail283.length+1=137
  rw [entryTail283_length]
def entryTail281 : List (PairEntry 37) := entry281::entryTail282
theorem entryTail281_length : entryTail281.length=138 := by
  change entryTail282.length+1=138
  rw [entryTail282_length]
def entryTail280 : List (PairEntry 37) := entry280::entryTail281
theorem entryTail280_length : entryTail280.length=139 := by
  change entryTail281.length+1=139
  rw [entryTail281_length]
def entryTail279 : List (PairEntry 37) := entry279::entryTail280
theorem entryTail279_length : entryTail279.length=140 := by
  change entryTail280.length+1=140
  rw [entryTail280_length]
def entryTail278 : List (PairEntry 37) := entry278::entryTail279
theorem entryTail278_length : entryTail278.length=141 := by
  change entryTail279.length+1=141
  rw [entryTail279_length]
def entryTail277 : List (PairEntry 37) := entry277::entryTail278
theorem entryTail277_length : entryTail277.length=142 := by
  change entryTail278.length+1=142
  rw [entryTail278_length]
def entryTail276 : List (PairEntry 37) := entry276::entryTail277
theorem entryTail276_length : entryTail276.length=143 := by
  change entryTail277.length+1=143
  rw [entryTail277_length]
def entryTail275 : List (PairEntry 37) := entry275::entryTail276
theorem entryTail275_length : entryTail275.length=144 := by
  change entryTail276.length+1=144
  rw [entryTail276_length]
def entryTail274 : List (PairEntry 37) := entry274::entryTail275
theorem entryTail274_length : entryTail274.length=145 := by
  change entryTail275.length+1=145
  rw [entryTail275_length]
def entryTail273 : List (PairEntry 37) := entry273::entryTail274
theorem entryTail273_length : entryTail273.length=146 := by
  change entryTail274.length+1=146
  rw [entryTail274_length]
def entryTail272 : List (PairEntry 37) := entry272::entryTail273
theorem entryTail272_length : entryTail272.length=147 := by
  change entryTail273.length+1=147
  rw [entryTail273_length]
def entryTail271 : List (PairEntry 37) := entry271::entryTail272
theorem entryTail271_length : entryTail271.length=148 := by
  change entryTail272.length+1=148
  rw [entryTail272_length]
def entryTail270 : List (PairEntry 37) := entry270::entryTail271
theorem entryTail270_length : entryTail270.length=149 := by
  change entryTail271.length+1=149
  rw [entryTail271_length]
def entryTail269 : List (PairEntry 37) := entry269::entryTail270
theorem entryTail269_length : entryTail269.length=150 := by
  change entryTail270.length+1=150
  rw [entryTail270_length]
def entryTail268 : List (PairEntry 37) := entry268::entryTail269
theorem entryTail268_length : entryTail268.length=151 := by
  change entryTail269.length+1=151
  rw [entryTail269_length]
def entryTail267 : List (PairEntry 37) := entry267::entryTail268
theorem entryTail267_length : entryTail267.length=152 := by
  change entryTail268.length+1=152
  rw [entryTail268_length]
def entryTail266 : List (PairEntry 37) := entry266::entryTail267
theorem entryTail266_length : entryTail266.length=153 := by
  change entryTail267.length+1=153
  rw [entryTail267_length]
def entryTail265 : List (PairEntry 37) := entry265::entryTail266
theorem entryTail265_length : entryTail265.length=154 := by
  change entryTail266.length+1=154
  rw [entryTail266_length]
def entryTail264 : List (PairEntry 37) := entry264::entryTail265
theorem entryTail264_length : entryTail264.length=155 := by
  change entryTail265.length+1=155
  rw [entryTail265_length]
def entryTail263 : List (PairEntry 37) := entry263::entryTail264
theorem entryTail263_length : entryTail263.length=156 := by
  change entryTail264.length+1=156
  rw [entryTail264_length]
def entryTail262 : List (PairEntry 37) := entry262::entryTail263
theorem entryTail262_length : entryTail262.length=157 := by
  change entryTail263.length+1=157
  rw [entryTail263_length]
def entryTail261 : List (PairEntry 37) := entry261::entryTail262
theorem entryTail261_length : entryTail261.length=158 := by
  change entryTail262.length+1=158
  rw [entryTail262_length]
def entryTail260 : List (PairEntry 37) := entry260::entryTail261
theorem entryTail260_length : entryTail260.length=159 := by
  change entryTail261.length+1=159
  rw [entryTail261_length]
def entryTail259 : List (PairEntry 37) := entry259::entryTail260
theorem entryTail259_length : entryTail259.length=160 := by
  change entryTail260.length+1=160
  rw [entryTail260_length]
def entryTail258 : List (PairEntry 37) := entry258::entryTail259
theorem entryTail258_length : entryTail258.length=161 := by
  change entryTail259.length+1=161
  rw [entryTail259_length]
def entryTail257 : List (PairEntry 37) := entry257::entryTail258
theorem entryTail257_length : entryTail257.length=162 := by
  change entryTail258.length+1=162
  rw [entryTail258_length]
def entryTail256 : List (PairEntry 37) := entry256::entryTail257
theorem entryTail256_length : entryTail256.length=163 := by
  change entryTail257.length+1=163
  rw [entryTail257_length]
def entryTail255 : List (PairEntry 37) := entry255::entryTail256
theorem entryTail255_length : entryTail255.length=164 := by
  change entryTail256.length+1=164
  rw [entryTail256_length]
def entryTail254 : List (PairEntry 37) := entry254::entryTail255
theorem entryTail254_length : entryTail254.length=165 := by
  change entryTail255.length+1=165
  rw [entryTail255_length]
def entryTail253 : List (PairEntry 37) := entry253::entryTail254
theorem entryTail253_length : entryTail253.length=166 := by
  change entryTail254.length+1=166
  rw [entryTail254_length]
def entryTail252 : List (PairEntry 37) := entry252::entryTail253
theorem entryTail252_length : entryTail252.length=167 := by
  change entryTail253.length+1=167
  rw [entryTail253_length]
def entryTail251 : List (PairEntry 37) := entry251::entryTail252
theorem entryTail251_length : entryTail251.length=168 := by
  change entryTail252.length+1=168
  rw [entryTail252_length]
def entryTail250 : List (PairEntry 37) := entry250::entryTail251
theorem entryTail250_length : entryTail250.length=169 := by
  change entryTail251.length+1=169
  rw [entryTail251_length]
def entryTail249 : List (PairEntry 37) := entry249::entryTail250
theorem entryTail249_length : entryTail249.length=170 := by
  change entryTail250.length+1=170
  rw [entryTail250_length]
def entryTail248 : List (PairEntry 37) := entry248::entryTail249
theorem entryTail248_length : entryTail248.length=171 := by
  change entryTail249.length+1=171
  rw [entryTail249_length]
def entryTail247 : List (PairEntry 37) := entry247::entryTail248
theorem entryTail247_length : entryTail247.length=172 := by
  change entryTail248.length+1=172
  rw [entryTail248_length]
def entryTail246 : List (PairEntry 37) := entry246::entryTail247
theorem entryTail246_length : entryTail246.length=173 := by
  change entryTail247.length+1=173
  rw [entryTail247_length]
def entryTail245 : List (PairEntry 37) := entry245::entryTail246
theorem entryTail245_length : entryTail245.length=174 := by
  change entryTail246.length+1=174
  rw [entryTail246_length]
def entryTail244 : List (PairEntry 37) := entry244::entryTail245
theorem entryTail244_length : entryTail244.length=175 := by
  change entryTail245.length+1=175
  rw [entryTail245_length]
def entryTail243 : List (PairEntry 37) := entry243::entryTail244
theorem entryTail243_length : entryTail243.length=176 := by
  change entryTail244.length+1=176
  rw [entryTail244_length]
def entryTail242 : List (PairEntry 37) := entry242::entryTail243
theorem entryTail242_length : entryTail242.length=177 := by
  change entryTail243.length+1=177
  rw [entryTail243_length]
def entryTail241 : List (PairEntry 37) := entry241::entryTail242
theorem entryTail241_length : entryTail241.length=178 := by
  change entryTail242.length+1=178
  rw [entryTail242_length]
def entryTail240 : List (PairEntry 37) := entry240::entryTail241
theorem entryTail240_length : entryTail240.length=179 := by
  change entryTail241.length+1=179
  rw [entryTail241_length]
def entryTail239 : List (PairEntry 37) := entry239::entryTail240
theorem entryTail239_length : entryTail239.length=180 := by
  change entryTail240.length+1=180
  rw [entryTail240_length]
def entryTail238 : List (PairEntry 37) := entry238::entryTail239
theorem entryTail238_length : entryTail238.length=181 := by
  change entryTail239.length+1=181
  rw [entryTail239_length]
def entryTail237 : List (PairEntry 37) := entry237::entryTail238
theorem entryTail237_length : entryTail237.length=182 := by
  change entryTail238.length+1=182
  rw [entryTail238_length]
def entryTail236 : List (PairEntry 37) := entry236::entryTail237
theorem entryTail236_length : entryTail236.length=183 := by
  change entryTail237.length+1=183
  rw [entryTail237_length]
def entryTail235 : List (PairEntry 37) := entry235::entryTail236
theorem entryTail235_length : entryTail235.length=184 := by
  change entryTail236.length+1=184
  rw [entryTail236_length]
def entryTail234 : List (PairEntry 37) := entry234::entryTail235
theorem entryTail234_length : entryTail234.length=185 := by
  change entryTail235.length+1=185
  rw [entryTail235_length]
def entryTail233 : List (PairEntry 37) := entry233::entryTail234
theorem entryTail233_length : entryTail233.length=186 := by
  change entryTail234.length+1=186
  rw [entryTail234_length]
def entryTail232 : List (PairEntry 37) := entry232::entryTail233
theorem entryTail232_length : entryTail232.length=187 := by
  change entryTail233.length+1=187
  rw [entryTail233_length]
def entryTail231 : List (PairEntry 37) := entry231::entryTail232
theorem entryTail231_length : entryTail231.length=188 := by
  change entryTail232.length+1=188
  rw [entryTail232_length]
def entryTail230 : List (PairEntry 37) := entry230::entryTail231
theorem entryTail230_length : entryTail230.length=189 := by
  change entryTail231.length+1=189
  rw [entryTail231_length]
def entryTail229 : List (PairEntry 37) := entry229::entryTail230
theorem entryTail229_length : entryTail229.length=190 := by
  change entryTail230.length+1=190
  rw [entryTail230_length]
def entryTail228 : List (PairEntry 37) := entry228::entryTail229
theorem entryTail228_length : entryTail228.length=191 := by
  change entryTail229.length+1=191
  rw [entryTail229_length]
def entryTail227 : List (PairEntry 37) := entry227::entryTail228
theorem entryTail227_length : entryTail227.length=192 := by
  change entryTail228.length+1=192
  rw [entryTail228_length]
def entryTail226 : List (PairEntry 37) := entry226::entryTail227
theorem entryTail226_length : entryTail226.length=193 := by
  change entryTail227.length+1=193
  rw [entryTail227_length]
def entryTail225 : List (PairEntry 37) := entry225::entryTail226
theorem entryTail225_length : entryTail225.length=194 := by
  change entryTail226.length+1=194
  rw [entryTail226_length]
def entryTail224 : List (PairEntry 37) := entry224::entryTail225
theorem entryTail224_length : entryTail224.length=195 := by
  change entryTail225.length+1=195
  rw [entryTail225_length]
def entryTail223 : List (PairEntry 37) := entry223::entryTail224
theorem entryTail223_length : entryTail223.length=196 := by
  change entryTail224.length+1=196
  rw [entryTail224_length]
def entryTail222 : List (PairEntry 37) := entry222::entryTail223
theorem entryTail222_length : entryTail222.length=197 := by
  change entryTail223.length+1=197
  rw [entryTail223_length]
def entryTail221 : List (PairEntry 37) := entry221::entryTail222
theorem entryTail221_length : entryTail221.length=198 := by
  change entryTail222.length+1=198
  rw [entryTail222_length]
def entryTail220 : List (PairEntry 37) := entry220::entryTail221
theorem entryTail220_length : entryTail220.length=199 := by
  change entryTail221.length+1=199
  rw [entryTail221_length]
def entryTail219 : List (PairEntry 37) := entry219::entryTail220
theorem entryTail219_length : entryTail219.length=200 := by
  change entryTail220.length+1=200
  rw [entryTail220_length]
def entryTail218 : List (PairEntry 37) := entry218::entryTail219
theorem entryTail218_length : entryTail218.length=201 := by
  change entryTail219.length+1=201
  rw [entryTail219_length]
def entryTail217 : List (PairEntry 37) := entry217::entryTail218
theorem entryTail217_length : entryTail217.length=202 := by
  change entryTail218.length+1=202
  rw [entryTail218_length]
def entryTail216 : List (PairEntry 37) := entry216::entryTail217
theorem entryTail216_length : entryTail216.length=203 := by
  change entryTail217.length+1=203
  rw [entryTail217_length]
def entryTail215 : List (PairEntry 37) := entry215::entryTail216
theorem entryTail215_length : entryTail215.length=204 := by
  change entryTail216.length+1=204
  rw [entryTail216_length]
def entryTail214 : List (PairEntry 37) := entry214::entryTail215
theorem entryTail214_length : entryTail214.length=205 := by
  change entryTail215.length+1=205
  rw [entryTail215_length]
def entryTail213 : List (PairEntry 37) := entry213::entryTail214
theorem entryTail213_length : entryTail213.length=206 := by
  change entryTail214.length+1=206
  rw [entryTail214_length]
def entryTail212 : List (PairEntry 37) := entry212::entryTail213
theorem entryTail212_length : entryTail212.length=207 := by
  change entryTail213.length+1=207
  rw [entryTail213_length]
def entryTail211 : List (PairEntry 37) := entry211::entryTail212
theorem entryTail211_length : entryTail211.length=208 := by
  change entryTail212.length+1=208
  rw [entryTail212_length]
def entryTail210 : List (PairEntry 37) := entry210::entryTail211
theorem entryTail210_length : entryTail210.length=209 := by
  change entryTail211.length+1=209
  rw [entryTail211_length]
def entryTail209 : List (PairEntry 37) := entry209::entryTail210
theorem entryTail209_length : entryTail209.length=210 := by
  change entryTail210.length+1=210
  rw [entryTail210_length]
def entryTail208 : List (PairEntry 37) := entry208::entryTail209
theorem entryTail208_length : entryTail208.length=211 := by
  change entryTail209.length+1=211
  rw [entryTail209_length]
def entryTail207 : List (PairEntry 37) := entry207::entryTail208
theorem entryTail207_length : entryTail207.length=212 := by
  change entryTail208.length+1=212
  rw [entryTail208_length]
def entryTail206 : List (PairEntry 37) := entry206::entryTail207
theorem entryTail206_length : entryTail206.length=213 := by
  change entryTail207.length+1=213
  rw [entryTail207_length]
def entryTail205 : List (PairEntry 37) := entry205::entryTail206
theorem entryTail205_length : entryTail205.length=214 := by
  change entryTail206.length+1=214
  rw [entryTail206_length]
def entryTail204 : List (PairEntry 37) := entry204::entryTail205
theorem entryTail204_length : entryTail204.length=215 := by
  change entryTail205.length+1=215
  rw [entryTail205_length]
def entryTail203 : List (PairEntry 37) := entry203::entryTail204
theorem entryTail203_length : entryTail203.length=216 := by
  change entryTail204.length+1=216
  rw [entryTail204_length]
def entryTail202 : List (PairEntry 37) := entry202::entryTail203
theorem entryTail202_length : entryTail202.length=217 := by
  change entryTail203.length+1=217
  rw [entryTail203_length]
def entryTail201 : List (PairEntry 37) := entry201::entryTail202
theorem entryTail201_length : entryTail201.length=218 := by
  change entryTail202.length+1=218
  rw [entryTail202_length]
def entryTail200 : List (PairEntry 37) := entry200::entryTail201
theorem entryTail200_length : entryTail200.length=219 := by
  change entryTail201.length+1=219
  rw [entryTail201_length]
def entryTail199 : List (PairEntry 37) := entry199::entryTail200
theorem entryTail199_length : entryTail199.length=220 := by
  change entryTail200.length+1=220
  rw [entryTail200_length]
def entryTail198 : List (PairEntry 37) := entry198::entryTail199
theorem entryTail198_length : entryTail198.length=221 := by
  change entryTail199.length+1=221
  rw [entryTail199_length]
def entryTail197 : List (PairEntry 37) := entry197::entryTail198
theorem entryTail197_length : entryTail197.length=222 := by
  change entryTail198.length+1=222
  rw [entryTail198_length]
def entryTail196 : List (PairEntry 37) := entry196::entryTail197
theorem entryTail196_length : entryTail196.length=223 := by
  change entryTail197.length+1=223
  rw [entryTail197_length]
def entryTail195 : List (PairEntry 37) := entry195::entryTail196
theorem entryTail195_length : entryTail195.length=224 := by
  change entryTail196.length+1=224
  rw [entryTail196_length]
def entryTail194 : List (PairEntry 37) := entry194::entryTail195
theorem entryTail194_length : entryTail194.length=225 := by
  change entryTail195.length+1=225
  rw [entryTail195_length]
def entryTail193 : List (PairEntry 37) := entry193::entryTail194
theorem entryTail193_length : entryTail193.length=226 := by
  change entryTail194.length+1=226
  rw [entryTail194_length]
def entryTail192 : List (PairEntry 37) := entry192::entryTail193
theorem entryTail192_length : entryTail192.length=227 := by
  change entryTail193.length+1=227
  rw [entryTail193_length]
def entryTail191 : List (PairEntry 37) := entry191::entryTail192
theorem entryTail191_length : entryTail191.length=228 := by
  change entryTail192.length+1=228
  rw [entryTail192_length]
def entryTail190 : List (PairEntry 37) := entry190::entryTail191
theorem entryTail190_length : entryTail190.length=229 := by
  change entryTail191.length+1=229
  rw [entryTail191_length]
def entryTail189 : List (PairEntry 37) := entry189::entryTail190
theorem entryTail189_length : entryTail189.length=230 := by
  change entryTail190.length+1=230
  rw [entryTail190_length]
def entryTail188 : List (PairEntry 37) := entry188::entryTail189
theorem entryTail188_length : entryTail188.length=231 := by
  change entryTail189.length+1=231
  rw [entryTail189_length]
def entryTail187 : List (PairEntry 37) := entry187::entryTail188
theorem entryTail187_length : entryTail187.length=232 := by
  change entryTail188.length+1=232
  rw [entryTail188_length]
def entryTail186 : List (PairEntry 37) := entry186::entryTail187
theorem entryTail186_length : entryTail186.length=233 := by
  change entryTail187.length+1=233
  rw [entryTail187_length]
def entryTail185 : List (PairEntry 37) := entry185::entryTail186
theorem entryTail185_length : entryTail185.length=234 := by
  change entryTail186.length+1=234
  rw [entryTail186_length]
def entryTail184 : List (PairEntry 37) := entry184::entryTail185
theorem entryTail184_length : entryTail184.length=235 := by
  change entryTail185.length+1=235
  rw [entryTail185_length]
def entryTail183 : List (PairEntry 37) := entry183::entryTail184
theorem entryTail183_length : entryTail183.length=236 := by
  change entryTail184.length+1=236
  rw [entryTail184_length]
def entryTail182 : List (PairEntry 37) := entry182::entryTail183
theorem entryTail182_length : entryTail182.length=237 := by
  change entryTail183.length+1=237
  rw [entryTail183_length]
def entryTail181 : List (PairEntry 37) := entry181::entryTail182
theorem entryTail181_length : entryTail181.length=238 := by
  change entryTail182.length+1=238
  rw [entryTail182_length]
def entryTail180 : List (PairEntry 37) := entry180::entryTail181
theorem entryTail180_length : entryTail180.length=239 := by
  change entryTail181.length+1=239
  rw [entryTail181_length]
def entryTail179 : List (PairEntry 37) := entry179::entryTail180
theorem entryTail179_length : entryTail179.length=240 := by
  change entryTail180.length+1=240
  rw [entryTail180_length]
def entryTail178 : List (PairEntry 37) := entry178::entryTail179
theorem entryTail178_length : entryTail178.length=241 := by
  change entryTail179.length+1=241
  rw [entryTail179_length]
def entryTail177 : List (PairEntry 37) := entry177::entryTail178
theorem entryTail177_length : entryTail177.length=242 := by
  change entryTail178.length+1=242
  rw [entryTail178_length]
def entryTail176 : List (PairEntry 37) := entry176::entryTail177
theorem entryTail176_length : entryTail176.length=243 := by
  change entryTail177.length+1=243
  rw [entryTail177_length]
def entryTail175 : List (PairEntry 37) := entry175::entryTail176
theorem entryTail175_length : entryTail175.length=244 := by
  change entryTail176.length+1=244
  rw [entryTail176_length]
def entryTail174 : List (PairEntry 37) := entry174::entryTail175
theorem entryTail174_length : entryTail174.length=245 := by
  change entryTail175.length+1=245
  rw [entryTail175_length]
def entryTail173 : List (PairEntry 37) := entry173::entryTail174
theorem entryTail173_length : entryTail173.length=246 := by
  change entryTail174.length+1=246
  rw [entryTail174_length]
def entryTail172 : List (PairEntry 37) := entry172::entryTail173
theorem entryTail172_length : entryTail172.length=247 := by
  change entryTail173.length+1=247
  rw [entryTail173_length]
def entryTail171 : List (PairEntry 37) := entry171::entryTail172
theorem entryTail171_length : entryTail171.length=248 := by
  change entryTail172.length+1=248
  rw [entryTail172_length]
def entryTail170 : List (PairEntry 37) := entry170::entryTail171
theorem entryTail170_length : entryTail170.length=249 := by
  change entryTail171.length+1=249
  rw [entryTail171_length]
def entryTail169 : List (PairEntry 37) := entry169::entryTail170
theorem entryTail169_length : entryTail169.length=250 := by
  change entryTail170.length+1=250
  rw [entryTail170_length]
def entryTail168 : List (PairEntry 37) := entry168::entryTail169
theorem entryTail168_length : entryTail168.length=251 := by
  change entryTail169.length+1=251
  rw [entryTail169_length]
def entryTail167 : List (PairEntry 37) := entry167::entryTail168
theorem entryTail167_length : entryTail167.length=252 := by
  change entryTail168.length+1=252
  rw [entryTail168_length]
def entryTail166 : List (PairEntry 37) := entry166::entryTail167
theorem entryTail166_length : entryTail166.length=253 := by
  change entryTail167.length+1=253
  rw [entryTail167_length]
def entryTail165 : List (PairEntry 37) := entry165::entryTail166
theorem entryTail165_length : entryTail165.length=254 := by
  change entryTail166.length+1=254
  rw [entryTail166_length]
def entryTail164 : List (PairEntry 37) := entry164::entryTail165
theorem entryTail164_length : entryTail164.length=255 := by
  change entryTail165.length+1=255
  rw [entryTail165_length]
def entryTail163 : List (PairEntry 37) := entry163::entryTail164
theorem entryTail163_length : entryTail163.length=256 := by
  change entryTail164.length+1=256
  rw [entryTail164_length]
def entryTail162 : List (PairEntry 37) := entry162::entryTail163
theorem entryTail162_length : entryTail162.length=257 := by
  change entryTail163.length+1=257
  rw [entryTail163_length]
def entryTail161 : List (PairEntry 37) := entry161::entryTail162
theorem entryTail161_length : entryTail161.length=258 := by
  change entryTail162.length+1=258
  rw [entryTail162_length]
def entryTail160 : List (PairEntry 37) := entry160::entryTail161
theorem entryTail160_length : entryTail160.length=259 := by
  change entryTail161.length+1=259
  rw [entryTail161_length]
def entryTail159 : List (PairEntry 37) := entry159::entryTail160
theorem entryTail159_length : entryTail159.length=260 := by
  change entryTail160.length+1=260
  rw [entryTail160_length]
def entryTail158 : List (PairEntry 37) := entry158::entryTail159
theorem entryTail158_length : entryTail158.length=261 := by
  change entryTail159.length+1=261
  rw [entryTail159_length]
def entryTail157 : List (PairEntry 37) := entry157::entryTail158
theorem entryTail157_length : entryTail157.length=262 := by
  change entryTail158.length+1=262
  rw [entryTail158_length]
def entryTail156 : List (PairEntry 37) := entry156::entryTail157
theorem entryTail156_length : entryTail156.length=263 := by
  change entryTail157.length+1=263
  rw [entryTail157_length]
def entryTail155 : List (PairEntry 37) := entry155::entryTail156
theorem entryTail155_length : entryTail155.length=264 := by
  change entryTail156.length+1=264
  rw [entryTail156_length]
def entryTail154 : List (PairEntry 37) := entry154::entryTail155
theorem entryTail154_length : entryTail154.length=265 := by
  change entryTail155.length+1=265
  rw [entryTail155_length]
def entryTail153 : List (PairEntry 37) := entry153::entryTail154
theorem entryTail153_length : entryTail153.length=266 := by
  change entryTail154.length+1=266
  rw [entryTail154_length]
def entryTail152 : List (PairEntry 37) := entry152::entryTail153
theorem entryTail152_length : entryTail152.length=267 := by
  change entryTail153.length+1=267
  rw [entryTail153_length]
def entryTail151 : List (PairEntry 37) := entry151::entryTail152
theorem entryTail151_length : entryTail151.length=268 := by
  change entryTail152.length+1=268
  rw [entryTail152_length]
def entryTail150 : List (PairEntry 37) := entry150::entryTail151
theorem entryTail150_length : entryTail150.length=269 := by
  change entryTail151.length+1=269
  rw [entryTail151_length]
def entryTail149 : List (PairEntry 37) := entry149::entryTail150
theorem entryTail149_length : entryTail149.length=270 := by
  change entryTail150.length+1=270
  rw [entryTail150_length]
def entryTail148 : List (PairEntry 37) := entry148::entryTail149
theorem entryTail148_length : entryTail148.length=271 := by
  change entryTail149.length+1=271
  rw [entryTail149_length]
def entryTail147 : List (PairEntry 37) := entry147::entryTail148
theorem entryTail147_length : entryTail147.length=272 := by
  change entryTail148.length+1=272
  rw [entryTail148_length]
def entryTail146 : List (PairEntry 37) := entry146::entryTail147
theorem entryTail146_length : entryTail146.length=273 := by
  change entryTail147.length+1=273
  rw [entryTail147_length]
def entryTail145 : List (PairEntry 37) := entry145::entryTail146
theorem entryTail145_length : entryTail145.length=274 := by
  change entryTail146.length+1=274
  rw [entryTail146_length]
def entryTail144 : List (PairEntry 37) := entry144::entryTail145
theorem entryTail144_length : entryTail144.length=275 := by
  change entryTail145.length+1=275
  rw [entryTail145_length]
def entryTail143 : List (PairEntry 37) := entry143::entryTail144
theorem entryTail143_length : entryTail143.length=276 := by
  change entryTail144.length+1=276
  rw [entryTail144_length]
def entryTail142 : List (PairEntry 37) := entry142::entryTail143
theorem entryTail142_length : entryTail142.length=277 := by
  change entryTail143.length+1=277
  rw [entryTail143_length]
def entryTail141 : List (PairEntry 37) := entry141::entryTail142
theorem entryTail141_length : entryTail141.length=278 := by
  change entryTail142.length+1=278
  rw [entryTail142_length]
def entryTail140 : List (PairEntry 37) := entry140::entryTail141
theorem entryTail140_length : entryTail140.length=279 := by
  change entryTail141.length+1=279
  rw [entryTail141_length]
def entryTail139 : List (PairEntry 37) := entry139::entryTail140
theorem entryTail139_length : entryTail139.length=280 := by
  change entryTail140.length+1=280
  rw [entryTail140_length]
def entryTail138 : List (PairEntry 37) := entry138::entryTail139
theorem entryTail138_length : entryTail138.length=281 := by
  change entryTail139.length+1=281
  rw [entryTail139_length]
def entryTail137 : List (PairEntry 37) := entry137::entryTail138
theorem entryTail137_length : entryTail137.length=282 := by
  change entryTail138.length+1=282
  rw [entryTail138_length]
def entryTail136 : List (PairEntry 37) := entry136::entryTail137
theorem entryTail136_length : entryTail136.length=283 := by
  change entryTail137.length+1=283
  rw [entryTail137_length]
def entryTail135 : List (PairEntry 37) := entry135::entryTail136
theorem entryTail135_length : entryTail135.length=284 := by
  change entryTail136.length+1=284
  rw [entryTail136_length]
def entryTail134 : List (PairEntry 37) := entry134::entryTail135
theorem entryTail134_length : entryTail134.length=285 := by
  change entryTail135.length+1=285
  rw [entryTail135_length]
def entryTail133 : List (PairEntry 37) := entry133::entryTail134
theorem entryTail133_length : entryTail133.length=286 := by
  change entryTail134.length+1=286
  rw [entryTail134_length]
def entryTail132 : List (PairEntry 37) := entry132::entryTail133
theorem entryTail132_length : entryTail132.length=287 := by
  change entryTail133.length+1=287
  rw [entryTail133_length]
def entryTail131 : List (PairEntry 37) := entry131::entryTail132
theorem entryTail131_length : entryTail131.length=288 := by
  change entryTail132.length+1=288
  rw [entryTail132_length]
def entryTail130 : List (PairEntry 37) := entry130::entryTail131
theorem entryTail130_length : entryTail130.length=289 := by
  change entryTail131.length+1=289
  rw [entryTail131_length]
def entryTail129 : List (PairEntry 37) := entry129::entryTail130
theorem entryTail129_length : entryTail129.length=290 := by
  change entryTail130.length+1=290
  rw [entryTail130_length]
def entryTail128 : List (PairEntry 37) := entry128::entryTail129
theorem entryTail128_length : entryTail128.length=291 := by
  change entryTail129.length+1=291
  rw [entryTail129_length]
def entryTail127 : List (PairEntry 37) := entry127::entryTail128
theorem entryTail127_length : entryTail127.length=292 := by
  change entryTail128.length+1=292
  rw [entryTail128_length]
def entryTail126 : List (PairEntry 37) := entry126::entryTail127
theorem entryTail126_length : entryTail126.length=293 := by
  change entryTail127.length+1=293
  rw [entryTail127_length]
def entryTail125 : List (PairEntry 37) := entry125::entryTail126
theorem entryTail125_length : entryTail125.length=294 := by
  change entryTail126.length+1=294
  rw [entryTail126_length]
def entryTail124 : List (PairEntry 37) := entry124::entryTail125
theorem entryTail124_length : entryTail124.length=295 := by
  change entryTail125.length+1=295
  rw [entryTail125_length]
def entryTail123 : List (PairEntry 37) := entry123::entryTail124
theorem entryTail123_length : entryTail123.length=296 := by
  change entryTail124.length+1=296
  rw [entryTail124_length]
def entryTail122 : List (PairEntry 37) := entry122::entryTail123
theorem entryTail122_length : entryTail122.length=297 := by
  change entryTail123.length+1=297
  rw [entryTail123_length]
def entryTail121 : List (PairEntry 37) := entry121::entryTail122
theorem entryTail121_length : entryTail121.length=298 := by
  change entryTail122.length+1=298
  rw [entryTail122_length]
def entryTail120 : List (PairEntry 37) := entry120::entryTail121
theorem entryTail120_length : entryTail120.length=299 := by
  change entryTail121.length+1=299
  rw [entryTail121_length]
def entryTail119 : List (PairEntry 37) := entry119::entryTail120
theorem entryTail119_length : entryTail119.length=300 := by
  change entryTail120.length+1=300
  rw [entryTail120_length]
def entryTail118 : List (PairEntry 37) := entry118::entryTail119
theorem entryTail118_length : entryTail118.length=301 := by
  change entryTail119.length+1=301
  rw [entryTail119_length]
def entryTail117 : List (PairEntry 37) := entry117::entryTail118
theorem entryTail117_length : entryTail117.length=302 := by
  change entryTail118.length+1=302
  rw [entryTail118_length]
def entryTail116 : List (PairEntry 37) := entry116::entryTail117
theorem entryTail116_length : entryTail116.length=303 := by
  change entryTail117.length+1=303
  rw [entryTail117_length]
def entryTail115 : List (PairEntry 37) := entry115::entryTail116
theorem entryTail115_length : entryTail115.length=304 := by
  change entryTail116.length+1=304
  rw [entryTail116_length]
def entryTail114 : List (PairEntry 37) := entry114::entryTail115
theorem entryTail114_length : entryTail114.length=305 := by
  change entryTail115.length+1=305
  rw [entryTail115_length]
def entryTail113 : List (PairEntry 37) := entry113::entryTail114
theorem entryTail113_length : entryTail113.length=306 := by
  change entryTail114.length+1=306
  rw [entryTail114_length]
def entryTail112 : List (PairEntry 37) := entry112::entryTail113
theorem entryTail112_length : entryTail112.length=307 := by
  change entryTail113.length+1=307
  rw [entryTail113_length]
def entryTail111 : List (PairEntry 37) := entry111::entryTail112
theorem entryTail111_length : entryTail111.length=308 := by
  change entryTail112.length+1=308
  rw [entryTail112_length]
def entryTail110 : List (PairEntry 37) := entry110::entryTail111
theorem entryTail110_length : entryTail110.length=309 := by
  change entryTail111.length+1=309
  rw [entryTail111_length]
def entryTail109 : List (PairEntry 37) := entry109::entryTail110
theorem entryTail109_length : entryTail109.length=310 := by
  change entryTail110.length+1=310
  rw [entryTail110_length]
def entryTail108 : List (PairEntry 37) := entry108::entryTail109
theorem entryTail108_length : entryTail108.length=311 := by
  change entryTail109.length+1=311
  rw [entryTail109_length]
def entryTail107 : List (PairEntry 37) := entry107::entryTail108
theorem entryTail107_length : entryTail107.length=312 := by
  change entryTail108.length+1=312
  rw [entryTail108_length]
def entryTail106 : List (PairEntry 37) := entry106::entryTail107
theorem entryTail106_length : entryTail106.length=313 := by
  change entryTail107.length+1=313
  rw [entryTail107_length]
def entryTail105 : List (PairEntry 37) := entry105::entryTail106
theorem entryTail105_length : entryTail105.length=314 := by
  change entryTail106.length+1=314
  rw [entryTail106_length]
def entryTail104 : List (PairEntry 37) := entry104::entryTail105
theorem entryTail104_length : entryTail104.length=315 := by
  change entryTail105.length+1=315
  rw [entryTail105_length]
def entryTail103 : List (PairEntry 37) := entry103::entryTail104
theorem entryTail103_length : entryTail103.length=316 := by
  change entryTail104.length+1=316
  rw [entryTail104_length]
def entryTail102 : List (PairEntry 37) := entry102::entryTail103
theorem entryTail102_length : entryTail102.length=317 := by
  change entryTail103.length+1=317
  rw [entryTail103_length]
def entryTail101 : List (PairEntry 37) := entry101::entryTail102
theorem entryTail101_length : entryTail101.length=318 := by
  change entryTail102.length+1=318
  rw [entryTail102_length]
def entryTail100 : List (PairEntry 37) := entry100::entryTail101
theorem entryTail100_length : entryTail100.length=319 := by
  change entryTail101.length+1=319
  rw [entryTail101_length]
def entryTail99 : List (PairEntry 37) := entry99::entryTail100
theorem entryTail99_length : entryTail99.length=320 := by
  change entryTail100.length+1=320
  rw [entryTail100_length]
def entryTail98 : List (PairEntry 37) := entry98::entryTail99
theorem entryTail98_length : entryTail98.length=321 := by
  change entryTail99.length+1=321
  rw [entryTail99_length]
def entryTail97 : List (PairEntry 37) := entry97::entryTail98
theorem entryTail97_length : entryTail97.length=322 := by
  change entryTail98.length+1=322
  rw [entryTail98_length]
def entryTail96 : List (PairEntry 37) := entry96::entryTail97
theorem entryTail96_length : entryTail96.length=323 := by
  change entryTail97.length+1=323
  rw [entryTail97_length]
def entryTail95 : List (PairEntry 37) := entry95::entryTail96
theorem entryTail95_length : entryTail95.length=324 := by
  change entryTail96.length+1=324
  rw [entryTail96_length]
def entryTail94 : List (PairEntry 37) := entry94::entryTail95
theorem entryTail94_length : entryTail94.length=325 := by
  change entryTail95.length+1=325
  rw [entryTail95_length]
def entryTail93 : List (PairEntry 37) := entry93::entryTail94
theorem entryTail93_length : entryTail93.length=326 := by
  change entryTail94.length+1=326
  rw [entryTail94_length]
def entryTail92 : List (PairEntry 37) := entry92::entryTail93
theorem entryTail92_length : entryTail92.length=327 := by
  change entryTail93.length+1=327
  rw [entryTail93_length]
def entryTail91 : List (PairEntry 37) := entry91::entryTail92
theorem entryTail91_length : entryTail91.length=328 := by
  change entryTail92.length+1=328
  rw [entryTail92_length]
def entryTail90 : List (PairEntry 37) := entry90::entryTail91
theorem entryTail90_length : entryTail90.length=329 := by
  change entryTail91.length+1=329
  rw [entryTail91_length]
def entryTail89 : List (PairEntry 37) := entry89::entryTail90
theorem entryTail89_length : entryTail89.length=330 := by
  change entryTail90.length+1=330
  rw [entryTail90_length]
def entryTail88 : List (PairEntry 37) := entry88::entryTail89
theorem entryTail88_length : entryTail88.length=331 := by
  change entryTail89.length+1=331
  rw [entryTail89_length]
def entryTail87 : List (PairEntry 37) := entry87::entryTail88
theorem entryTail87_length : entryTail87.length=332 := by
  change entryTail88.length+1=332
  rw [entryTail88_length]
def entryTail86 : List (PairEntry 37) := entry86::entryTail87
theorem entryTail86_length : entryTail86.length=333 := by
  change entryTail87.length+1=333
  rw [entryTail87_length]
def entryTail85 : List (PairEntry 37) := entry85::entryTail86
theorem entryTail85_length : entryTail85.length=334 := by
  change entryTail86.length+1=334
  rw [entryTail86_length]
def entryTail84 : List (PairEntry 37) := entry84::entryTail85
theorem entryTail84_length : entryTail84.length=335 := by
  change entryTail85.length+1=335
  rw [entryTail85_length]
def entryTail83 : List (PairEntry 37) := entry83::entryTail84
theorem entryTail83_length : entryTail83.length=336 := by
  change entryTail84.length+1=336
  rw [entryTail84_length]
def entryTail82 : List (PairEntry 37) := entry82::entryTail83
theorem entryTail82_length : entryTail82.length=337 := by
  change entryTail83.length+1=337
  rw [entryTail83_length]
def entryTail81 : List (PairEntry 37) := entry81::entryTail82
theorem entryTail81_length : entryTail81.length=338 := by
  change entryTail82.length+1=338
  rw [entryTail82_length]
def entryTail80 : List (PairEntry 37) := entry80::entryTail81
theorem entryTail80_length : entryTail80.length=339 := by
  change entryTail81.length+1=339
  rw [entryTail81_length]
def entryTail79 : List (PairEntry 37) := entry79::entryTail80
theorem entryTail79_length : entryTail79.length=340 := by
  change entryTail80.length+1=340
  rw [entryTail80_length]
def entryTail78 : List (PairEntry 37) := entry78::entryTail79
theorem entryTail78_length : entryTail78.length=341 := by
  change entryTail79.length+1=341
  rw [entryTail79_length]
def entryTail77 : List (PairEntry 37) := entry77::entryTail78
theorem entryTail77_length : entryTail77.length=342 := by
  change entryTail78.length+1=342
  rw [entryTail78_length]
def entryTail76 : List (PairEntry 37) := entry76::entryTail77
theorem entryTail76_length : entryTail76.length=343 := by
  change entryTail77.length+1=343
  rw [entryTail77_length]
def entryTail75 : List (PairEntry 37) := entry75::entryTail76
theorem entryTail75_length : entryTail75.length=344 := by
  change entryTail76.length+1=344
  rw [entryTail76_length]
def entryTail74 : List (PairEntry 37) := entry74::entryTail75
theorem entryTail74_length : entryTail74.length=345 := by
  change entryTail75.length+1=345
  rw [entryTail75_length]
def entryTail73 : List (PairEntry 37) := entry73::entryTail74
theorem entryTail73_length : entryTail73.length=346 := by
  change entryTail74.length+1=346
  rw [entryTail74_length]
def entryTail72 : List (PairEntry 37) := entry72::entryTail73
theorem entryTail72_length : entryTail72.length=347 := by
  change entryTail73.length+1=347
  rw [entryTail73_length]
def entryTail71 : List (PairEntry 37) := entry71::entryTail72
theorem entryTail71_length : entryTail71.length=348 := by
  change entryTail72.length+1=348
  rw [entryTail72_length]
def entryTail70 : List (PairEntry 37) := entry70::entryTail71
theorem entryTail70_length : entryTail70.length=349 := by
  change entryTail71.length+1=349
  rw [entryTail71_length]
def entryTail69 : List (PairEntry 37) := entry69::entryTail70
theorem entryTail69_length : entryTail69.length=350 := by
  change entryTail70.length+1=350
  rw [entryTail70_length]
def entryTail68 : List (PairEntry 37) := entry68::entryTail69
theorem entryTail68_length : entryTail68.length=351 := by
  change entryTail69.length+1=351
  rw [entryTail69_length]
def entryTail67 : List (PairEntry 37) := entry67::entryTail68
theorem entryTail67_length : entryTail67.length=352 := by
  change entryTail68.length+1=352
  rw [entryTail68_length]
def entryTail66 : List (PairEntry 37) := entry66::entryTail67
theorem entryTail66_length : entryTail66.length=353 := by
  change entryTail67.length+1=353
  rw [entryTail67_length]
def entryTail65 : List (PairEntry 37) := entry65::entryTail66
theorem entryTail65_length : entryTail65.length=354 := by
  change entryTail66.length+1=354
  rw [entryTail66_length]
def entryTail64 : List (PairEntry 37) := entry64::entryTail65
theorem entryTail64_length : entryTail64.length=355 := by
  change entryTail65.length+1=355
  rw [entryTail65_length]
def entryTail63 : List (PairEntry 37) := entry63::entryTail64
theorem entryTail63_length : entryTail63.length=356 := by
  change entryTail64.length+1=356
  rw [entryTail64_length]
def entryTail62 : List (PairEntry 37) := entry62::entryTail63
theorem entryTail62_length : entryTail62.length=357 := by
  change entryTail63.length+1=357
  rw [entryTail63_length]
def entryTail61 : List (PairEntry 37) := entry61::entryTail62
theorem entryTail61_length : entryTail61.length=358 := by
  change entryTail62.length+1=358
  rw [entryTail62_length]
def entryTail60 : List (PairEntry 37) := entry60::entryTail61
theorem entryTail60_length : entryTail60.length=359 := by
  change entryTail61.length+1=359
  rw [entryTail61_length]
def entryTail59 : List (PairEntry 37) := entry59::entryTail60
theorem entryTail59_length : entryTail59.length=360 := by
  change entryTail60.length+1=360
  rw [entryTail60_length]
def entryTail58 : List (PairEntry 37) := entry58::entryTail59
theorem entryTail58_length : entryTail58.length=361 := by
  change entryTail59.length+1=361
  rw [entryTail59_length]
def entryTail57 : List (PairEntry 37) := entry57::entryTail58
theorem entryTail57_length : entryTail57.length=362 := by
  change entryTail58.length+1=362
  rw [entryTail58_length]
def entryTail56 : List (PairEntry 37) := entry56::entryTail57
theorem entryTail56_length : entryTail56.length=363 := by
  change entryTail57.length+1=363
  rw [entryTail57_length]
def entryTail55 : List (PairEntry 37) := entry55::entryTail56
theorem entryTail55_length : entryTail55.length=364 := by
  change entryTail56.length+1=364
  rw [entryTail56_length]
def entryTail54 : List (PairEntry 37) := entry54::entryTail55
theorem entryTail54_length : entryTail54.length=365 := by
  change entryTail55.length+1=365
  rw [entryTail55_length]
def entryTail53 : List (PairEntry 37) := entry53::entryTail54
theorem entryTail53_length : entryTail53.length=366 := by
  change entryTail54.length+1=366
  rw [entryTail54_length]
def entryTail52 : List (PairEntry 37) := entry52::entryTail53
theorem entryTail52_length : entryTail52.length=367 := by
  change entryTail53.length+1=367
  rw [entryTail53_length]
def entryTail51 : List (PairEntry 37) := entry51::entryTail52
theorem entryTail51_length : entryTail51.length=368 := by
  change entryTail52.length+1=368
  rw [entryTail52_length]
def entryTail50 : List (PairEntry 37) := entry50::entryTail51
theorem entryTail50_length : entryTail50.length=369 := by
  change entryTail51.length+1=369
  rw [entryTail51_length]
def entryTail49 : List (PairEntry 37) := entry49::entryTail50
theorem entryTail49_length : entryTail49.length=370 := by
  change entryTail50.length+1=370
  rw [entryTail50_length]
def entryTail48 : List (PairEntry 37) := entry48::entryTail49
theorem entryTail48_length : entryTail48.length=371 := by
  change entryTail49.length+1=371
  rw [entryTail49_length]
def entryTail47 : List (PairEntry 37) := entry47::entryTail48
theorem entryTail47_length : entryTail47.length=372 := by
  change entryTail48.length+1=372
  rw [entryTail48_length]
def entryTail46 : List (PairEntry 37) := entry46::entryTail47
theorem entryTail46_length : entryTail46.length=373 := by
  change entryTail47.length+1=373
  rw [entryTail47_length]
def entryTail45 : List (PairEntry 37) := entry45::entryTail46
theorem entryTail45_length : entryTail45.length=374 := by
  change entryTail46.length+1=374
  rw [entryTail46_length]
def entryTail44 : List (PairEntry 37) := entry44::entryTail45
theorem entryTail44_length : entryTail44.length=375 := by
  change entryTail45.length+1=375
  rw [entryTail45_length]
def entryTail43 : List (PairEntry 37) := entry43::entryTail44
theorem entryTail43_length : entryTail43.length=376 := by
  change entryTail44.length+1=376
  rw [entryTail44_length]
def entryTail42 : List (PairEntry 37) := entry42::entryTail43
theorem entryTail42_length : entryTail42.length=377 := by
  change entryTail43.length+1=377
  rw [entryTail43_length]
def entryTail41 : List (PairEntry 37) := entry41::entryTail42
theorem entryTail41_length : entryTail41.length=378 := by
  change entryTail42.length+1=378
  rw [entryTail42_length]
def entryTail40 : List (PairEntry 37) := entry40::entryTail41
theorem entryTail40_length : entryTail40.length=379 := by
  change entryTail41.length+1=379
  rw [entryTail41_length]
def entryTail39 : List (PairEntry 37) := entry39::entryTail40
theorem entryTail39_length : entryTail39.length=380 := by
  change entryTail40.length+1=380
  rw [entryTail40_length]
def entryTail38 : List (PairEntry 37) := entry38::entryTail39
theorem entryTail38_length : entryTail38.length=381 := by
  change entryTail39.length+1=381
  rw [entryTail39_length]
def entryTail37 : List (PairEntry 37) := entry37::entryTail38
theorem entryTail37_length : entryTail37.length=382 := by
  change entryTail38.length+1=382
  rw [entryTail38_length]
def entryTail36 : List (PairEntry 37) := entry36::entryTail37
theorem entryTail36_length : entryTail36.length=383 := by
  change entryTail37.length+1=383
  rw [entryTail37_length]
def entryTail35 : List (PairEntry 37) := entry35::entryTail36
theorem entryTail35_length : entryTail35.length=384 := by
  change entryTail36.length+1=384
  rw [entryTail36_length]
def entryTail34 : List (PairEntry 37) := entry34::entryTail35
theorem entryTail34_length : entryTail34.length=385 := by
  change entryTail35.length+1=385
  rw [entryTail35_length]
def entryTail33 : List (PairEntry 37) := entry33::entryTail34
theorem entryTail33_length : entryTail33.length=386 := by
  change entryTail34.length+1=386
  rw [entryTail34_length]
def entryTail32 : List (PairEntry 37) := entry32::entryTail33
theorem entryTail32_length : entryTail32.length=387 := by
  change entryTail33.length+1=387
  rw [entryTail33_length]
def entryTail31 : List (PairEntry 37) := entry31::entryTail32
theorem entryTail31_length : entryTail31.length=388 := by
  change entryTail32.length+1=388
  rw [entryTail32_length]
def entryTail30 : List (PairEntry 37) := entry30::entryTail31
theorem entryTail30_length : entryTail30.length=389 := by
  change entryTail31.length+1=389
  rw [entryTail31_length]
def entryTail29 : List (PairEntry 37) := entry29::entryTail30
theorem entryTail29_length : entryTail29.length=390 := by
  change entryTail30.length+1=390
  rw [entryTail30_length]
def entryTail28 : List (PairEntry 37) := entry28::entryTail29
theorem entryTail28_length : entryTail28.length=391 := by
  change entryTail29.length+1=391
  rw [entryTail29_length]
def entryTail27 : List (PairEntry 37) := entry27::entryTail28
theorem entryTail27_length : entryTail27.length=392 := by
  change entryTail28.length+1=392
  rw [entryTail28_length]
def entryTail26 : List (PairEntry 37) := entry26::entryTail27
theorem entryTail26_length : entryTail26.length=393 := by
  change entryTail27.length+1=393
  rw [entryTail27_length]
def entryTail25 : List (PairEntry 37) := entry25::entryTail26
theorem entryTail25_length : entryTail25.length=394 := by
  change entryTail26.length+1=394
  rw [entryTail26_length]
def entryTail24 : List (PairEntry 37) := entry24::entryTail25
theorem entryTail24_length : entryTail24.length=395 := by
  change entryTail25.length+1=395
  rw [entryTail25_length]
def entryTail23 : List (PairEntry 37) := entry23::entryTail24
theorem entryTail23_length : entryTail23.length=396 := by
  change entryTail24.length+1=396
  rw [entryTail24_length]
def entryTail22 : List (PairEntry 37) := entry22::entryTail23
theorem entryTail22_length : entryTail22.length=397 := by
  change entryTail23.length+1=397
  rw [entryTail23_length]
def entryTail21 : List (PairEntry 37) := entry21::entryTail22
theorem entryTail21_length : entryTail21.length=398 := by
  change entryTail22.length+1=398
  rw [entryTail22_length]
def entryTail20 : List (PairEntry 37) := entry20::entryTail21
theorem entryTail20_length : entryTail20.length=399 := by
  change entryTail21.length+1=399
  rw [entryTail21_length]
def entryTail19 : List (PairEntry 37) := entry19::entryTail20
theorem entryTail19_length : entryTail19.length=400 := by
  change entryTail20.length+1=400
  rw [entryTail20_length]
def entryTail18 : List (PairEntry 37) := entry18::entryTail19
theorem entryTail18_length : entryTail18.length=401 := by
  change entryTail19.length+1=401
  rw [entryTail19_length]
def entryTail17 : List (PairEntry 37) := entry17::entryTail18
theorem entryTail17_length : entryTail17.length=402 := by
  change entryTail18.length+1=402
  rw [entryTail18_length]
def entryTail16 : List (PairEntry 37) := entry16::entryTail17
theorem entryTail16_length : entryTail16.length=403 := by
  change entryTail17.length+1=403
  rw [entryTail17_length]
def entryTail15 : List (PairEntry 37) := entry15::entryTail16
theorem entryTail15_length : entryTail15.length=404 := by
  change entryTail16.length+1=404
  rw [entryTail16_length]
def entryTail14 : List (PairEntry 37) := entry14::entryTail15
theorem entryTail14_length : entryTail14.length=405 := by
  change entryTail15.length+1=405
  rw [entryTail15_length]
def entryTail13 : List (PairEntry 37) := entry13::entryTail14
theorem entryTail13_length : entryTail13.length=406 := by
  change entryTail14.length+1=406
  rw [entryTail14_length]
def entryTail12 : List (PairEntry 37) := entry12::entryTail13
theorem entryTail12_length : entryTail12.length=407 := by
  change entryTail13.length+1=407
  rw [entryTail13_length]
def entryTail11 : List (PairEntry 37) := entry11::entryTail12
theorem entryTail11_length : entryTail11.length=408 := by
  change entryTail12.length+1=408
  rw [entryTail12_length]
def entryTail10 : List (PairEntry 37) := entry10::entryTail11
theorem entryTail10_length : entryTail10.length=409 := by
  change entryTail11.length+1=409
  rw [entryTail11_length]
def entryTail9 : List (PairEntry 37) := entry9::entryTail10
theorem entryTail9_length : entryTail9.length=410 := by
  change entryTail10.length+1=410
  rw [entryTail10_length]
def entryTail8 : List (PairEntry 37) := entry8::entryTail9
theorem entryTail8_length : entryTail8.length=411 := by
  change entryTail9.length+1=411
  rw [entryTail9_length]
def entryTail7 : List (PairEntry 37) := entry7::entryTail8
theorem entryTail7_length : entryTail7.length=412 := by
  change entryTail8.length+1=412
  rw [entryTail8_length]
def entryTail6 : List (PairEntry 37) := entry6::entryTail7
theorem entryTail6_length : entryTail6.length=413 := by
  change entryTail7.length+1=413
  rw [entryTail7_length]
def entryTail5 : List (PairEntry 37) := entry5::entryTail6
theorem entryTail5_length : entryTail5.length=414 := by
  change entryTail6.length+1=414
  rw [entryTail6_length]
def entryTail4 : List (PairEntry 37) := entry4::entryTail5
theorem entryTail4_length : entryTail4.length=415 := by
  change entryTail5.length+1=415
  rw [entryTail5_length]
def entryTail3 : List (PairEntry 37) := entry3::entryTail4
theorem entryTail3_length : entryTail3.length=416 := by
  change entryTail4.length+1=416
  rw [entryTail4_length]
def entryTail2 : List (PairEntry 37) := entry2::entryTail3
theorem entryTail2_length : entryTail2.length=417 := by
  change entryTail3.length+1=417
  rw [entryTail3_length]
def entryTail1 : List (PairEntry 37) := entry1::entryTail2
theorem entryTail1_length : entryTail1.length=418 := by
  change entryTail2.length+1=418
  rw [entryTail2_length]
def entryTail0 : List (PairEntry 37) := entry0::entryTail1
theorem entryTail0_length : entryTail0.length=419 := by
  change entryTail1.length+1=419
  rw [entryTail1_length]
def entryValues : List (PairEntry 37) := entryTail0
theorem entryValues_length : entryValues.length=419 := entryTail0_length
def fixedEntries (i : Fin 419) : PairEntry 37 := entryValues[i.val]'(by rw [entryValues_length]; exact i.isLt)

def logGapLow : ℚ := 111277 / 50000

end FixedData

open FixedData

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

inductive Candidate (T : NodeTable) : ℤ → ℝ → ℝ → ℝ → Prop
  | interp (i j : Fin T.pairCount) (s : ℤ) (t r l : ℝ)
      (hp : (i, j) ∈ T.interpPairs)
      (hsi : (T.entryNode i).usedFor s) (hsj : (T.entryNode j).usedFor s)
      (hl : l ∈ Icc 0 1)
      (ht : t = l * (T.entryNode i).t + (1 - l) * (T.entryNode j).t)
      (hr : l * ((T.entries i).rho : ℝ) + (1 - l) * ((T.entries j).rho : ℝ) ≤ r) :
      Candidate T s t r (l * ((T.entries i).lower : ℝ) + (1 - l) * ((T.entries j).lower : ℝ))
  | transport (i : Fin T.pairCount) (s : ℤ) (t r : ℝ) (m : ℚ)
      (hs : (T.entryNode i).usedFor s) (ht : (T.entryNode i).t ≤ t)
      (hm : ((T.entryNode i).frame = .lattice ∧ m ∈ T.slopes) ∨ m = 0)
      (hr : ((T.entries i).rho : ℝ) + (4 + (m : ℝ)) * (t - (T.entryNode i).t) ≤ r) :
      Candidate T s t r (((T.entries i).lower : ℝ) +
        (2 * (m : ℝ) - (m : ℝ) ^ 2) * (t - (T.entryNode i).t))

end CatalanCore.Li2.Uniform

namespace CatalanCore.Li2

noncomputable def cRate (a b : ℤ) : ℝ :=
  7 / 2 - 523 / 840 + (8 / 3) * Real.log (b : ℝ) -
    6 * Real.log |(a : ℝ)| - (9 / 4) * Real.log |((b - a : ℤ) : ℝ)|

end CatalanCore.Li2

namespace Li2IrrationalityMeasure

open CatalanCore.Li2 CatalanCore.Li2.Uniform

theorem li2_measure_general (a b : ℤ) (hb : 0 < b) (hab : IsCoprime a b) (ha : a ≠ 0)
    (h2 : 2 * |a| ≤ b) (ρ D μ : ℝ) (hρ : 0 < ρ)
    (hD : Candidate nodeTable (Int.sign a) (Real.log ((b : ℝ) / |(a : ℝ)|)) ρ D)
    (hη : 0 < D + cRate a b) (hμ : ρ * max (2 / (D + cRate a b)) (39 / 98) < μ) :
    ∀ᶠ q : ℕ in Filter.atTop, ∀ p : ℤ, (q : ℝ) ^ (-μ) <
      |(∑' k : ℕ, ((a : ℝ) / b) ^ (k + 1) / ((k : ℝ) + 1) ^ 2) - (p : ℝ) / q| := by
  sorry

end Li2IrrationalityMeasure
