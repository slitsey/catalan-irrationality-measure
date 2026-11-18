module
public import CatalanCore.Li2.DecayCert.Bent
public import CatalanCore.Li2.DecayCert.Lattice
public import CatalanCore.Li2.DecayCert.Seg.Node
public import CatalanCore.Li2.DecayCert.Seg.NodeCells
public import CatalanCore.Li2.DecayCert.Seg.NodeFast
public import CatalanCore.Li2.Uniform.TableSpec
@[expose] public section
set_option Elab.async false
namespace CatalanCore.Li2.DecayCert
structure LatticePackage where
  z : ℚ
  input : LatticeInput
  setup : LatticeSetup
  checked : latticeSetupCheck z input setup=true
/-- A bent node: its input, the node certificate with stored cell outputs, and for every cell
valid segment tables (`sharedOK`) under which the cell checks against its stored output. -/
structure BentPackage where
  z : ℚ
  input : BentInput
  setup : Seg.NodeCert Seg.ContourCellN Seg.AtomCellN
  S : ℤ
  G : ℤ
  hS : 0 < S
  hG : 0 < G
  checked : Seg.nodeSegmentCheck z input setup=true
  contourOK : ∀ x ∈ setup.contour,∃ ss,Seg.sharedOK S input.data.segments ss=true ∧
    Seg.contourCellOK S G z input ss x.1 x.2=true
  atomOK : ∀ x ∈ setup.atoms,∃ ss,Seg.sharedOK S input.data.segments ss=true ∧
    Seg.atomCellNOK S G z input ss x.1 x.2=true

inductive EntryUse (T : CatalanCore.Li2.Uniform.NodeTable) (frames : CatalanCore.Li2.Uniform.FrameKey → CatalanCore.Li2.Uniform.DualFrame)
    {L : ℕ} (LP : Fin L → LatticePackage)
    (BP : Fin T.nodeCount → Option BentPackage) (i : Fin T.pairCount) : Type
  | lattice (pool : Fin L) (p : LatticeCert)
      (hframe : (T.entryNode i).frame=.lattice)
      (hz : (LP pool).z=(T.entryNode i).magnitude)
      (hr : p.rho=(T.entries i).rho) (hD : p.lower=(T.entries i).lower)
      (sourceIndex : ℕ) (hindex : sourceIndex=(T.entries i).localIndex)
      (checked : latticeCheck (LP pool).z (LP pool).input (LP pool).setup p=true) :
      EntryUse T frames LP BP i
  | bent (b : BentPackage)
      (hframe : (T.entryNode i).frame ≠ .lattice)
      (hpool : BP (T.entries i).node=some b)
      (hz : b.z= -(T.entryNode i).magnitude)
      (hf : b.input.geom.frame=frames (T.entryNode i).frame)
      (level : ℚ) (sourceIndex : ℕ) (hindex : sourceIndex=(T.entries i).localIndex)
      (checked : Seg.nodePairCheck b.setup (T.entries i).rho level (T.entries i).lower=true) :
      EntryUse T frames LP BP i

structure DecayCertificates (T : CatalanCore.Li2.Uniform.NodeTable) where
  valid : CatalanCore.Li2.Uniform.TableValid T
  frames : CatalanCore.Li2.Uniform.FrameKey → CatalanCore.Li2.Uniform.DualFrame
  geometry : ∀ f : CatalanCore.Li2.Uniform.FrameKey, CatalanCore.Li2.Uniform.FrameGeometry (frames f)
  pure_frame : (frames .lattice).pure=true
  bent_cut : ∀ f : CatalanCore.Li2.Uniform.FrameKey, f ≠ .lattice → CatalanCore.Li2.Uniform.frameCut (geometry f)=some 0
  latticeCount : ℕ
  latticeSetup : Fin latticeCount → LatticePackage
  bentSetup : Fin T.nodeCount → Option BentPackage
  bent_present : ∀ k : Fin T.nodeCount, (T.nodes k).frame ≠ .lattice →
    ∃ b, bentSetup k=some b ∧ b.z= -(T.nodes k).magnitude ∧
      b.input.geom.frame=frames (T.nodes k).frame
  entry : (i : Fin T.pairCount) → EntryUse T frames latticeSetup bentSetup i

noncomputable def EntryUse.datum {T frames L LP BP i}
    (e : @EntryUse T frames L LP BP i) : CatalanCore.Li2.Uniform.DualDatum :=
  match e with
  | .lattice pool _ _ _ _ _ _ _ _ => (LP pool).input.data.dual
  | .bent b _ _ _ _ _ _ _ _ => b.input.data.dual
noncomputable def EntryUse.level {T frames L LP BP i}
    (e : @EntryUse T frames L LP BP i) : ℝ :=
  match e with
  | .lattice pool _ _ _ _ _ _ _ _ => ((LP pool).setup.theta:ℝ)
  | .bent _ _ _ _ _ level _ _ _ => (level:ℝ)


#print axioms EntryUse.datum
#print axioms EntryUse.level
end CatalanCore.Li2.DecayCert
