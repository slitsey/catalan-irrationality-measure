module
public import CatalanCore.Li2.DecayCert.TableSound
public import CatalanCore.Li2.DecayCert.Simple.Cert
/-! The decay table certified on any mix of the cell, SIMPLE and bent routes. `EntryUseS` adds the SIMPLE
lattice route to `EntryUse`; `decayCertificatesS_candidate` concludes the decay bound as `decayCertificates_candidate`. -/
@[expose] public section
set_option Elab.async false
open Polynomial MeasureTheory Set Filter Topology
namespace CatalanCore.Li2.DecayCert
open CatalanCore.Li2.Decay CatalanCore.Li2.DecayCert.Simple
noncomputable section

/-- The window and dual bound of a SIMPLE lattice certificate, as `latticeCert_window` gives them for the
cell route. -/
theorem latticeSimple_window (z : ℚ) (d : LatticeInput) (c : SimpleSetup) (p : SimplePairCert)
    (hc : simpleSetupCheck z d c=true) (hp : simplePairCheck c p=true)
    (F : CatalanCore.Li2.Uniform.DualFrame) (g : CatalanCore.Li2.Uniform.FrameGeometry F) (hF : F.pure=true) :
    (p.lower:ℝ)≤CatalanCore.Li2.Uniform.dual F (CatalanCore.Li2.Uniform.signOf (z:ℝ))
      (Real.log (1/|(z:ℝ)|)) (p.rho:ℝ) d.data.dual (c.source.theta:ℝ) ∧
      CatalanCore.Li2.Uniform.WindowBound z (p.rho:ℝ) (p.lower:ℝ) := by
  have hc' := hc
  simp only [simpleSetupCheck,Bool.and_eq_true] at hc'
  have ha := of_decide_eq_true hc'.1.1.1.1.1.1.1.1.1.1.1.1
  have hz : ValidZ (z:ℝ) := by
    constructor
    · exact_mod_cast ha.1
    · exact_mod_cast ha.2.1
  have hfree : FreeBound (z:ℝ) F d.data.dual (c.source.theta:ℝ) := by
    intro u hu
    change u∈F.free (CatalanCore.Li2.Uniform.signOf (z:ℝ)) at hu
    rw [F.pure_free hF] at hu
    exact False.elim hu
  have hp' := hp
  simp only [simplePairCheck,Bool.and_eq_true] at hp'
  have hρ : (0:ℝ)<(p.rho:ℝ) := by exact_mod_cast of_decide_eq_true hp'.1.1.1.1
  have hbound : (p.lower:ℝ)≤dualValue (z:ℝ) (p.rho:ℝ) F d.data.dual.σ (c.source.theta:ℝ) := by
    have hb := latticeSimple_D_ge z d c p hc hp
    simpa only [dualValue,latPenalty,lat,CatalanCore.Li2.Uniform.lat,F.pure_lattice hF] using hb
  refine ⟨?_,family_window_bound z hz _ _
    ((li2_window_decay (z:ℝ) hz F g d.data.dual c.source.theta p.rho hρ hfree).mono hbound)⟩
  rwa [CatalanCore.Li2.Uniform.decay_dual_eq (z:ℝ) p.rho hz F d.data.dual c.source.theta] at hbound

/-- A lattice datum certified on the SIMPLE route. -/
structure LatticeSimplePackage where
  z : ℚ
  input : LatticeInput
  setup : SimpleSetup
  checked : simpleSetupCheck z input setup=true

/-- A table entry certified by the existing routes or by a SIMPLE lattice package. -/
inductive EntryUseS (T : CatalanCore.Li2.Uniform.NodeTable)
    (frames : CatalanCore.Li2.Uniform.FrameKey → CatalanCore.Li2.Uniform.DualFrame)
    {L M : ℕ} (LP : Fin L → LatticePackage) (SP : Fin M → LatticeSimplePackage)
    (BP : Fin T.nodeCount → Option BentPackage) (i : Fin T.pairCount) : Type
  | old (e : EntryUse T frames LP BP i) : EntryUseS T frames LP SP BP i
  | simple (pool : Fin M) (p : SimplePairCert)
      (hframe : (T.entryNode i).frame=.lattice)
      (hz : (SP pool).z=(T.entryNode i).magnitude)
      (hr : p.rho=(T.entries i).rho) (hD : p.lower=(T.entries i).lower)
      (checked : simplePairCheck (SP pool).setup p=true) : EntryUseS T frames LP SP BP i

structure DecayCertificatesS (T : CatalanCore.Li2.Uniform.NodeTable) where
  valid : CatalanCore.Li2.Uniform.TableValid T
  frames : CatalanCore.Li2.Uniform.FrameKey → CatalanCore.Li2.Uniform.DualFrame
  geometry : ∀ f : CatalanCore.Li2.Uniform.FrameKey, CatalanCore.Li2.Uniform.FrameGeometry (frames f)
  pure_frame : (frames .lattice).pure=true
  bent_cut : ∀ f : CatalanCore.Li2.Uniform.FrameKey, f ≠ .lattice →
    CatalanCore.Li2.Uniform.frameCut (geometry f)=some 0
  latticeCount : ℕ
  latticeSetup : Fin latticeCount → LatticePackage
  simpleCount : ℕ
  simpleSetup : Fin simpleCount → LatticeSimplePackage
  bentSetup : Fin T.nodeCount → Option BentPackage
  bent_present : ∀ k : Fin T.nodeCount, (T.nodes k).frame ≠ .lattice →
    ∃ b, bentSetup k=some b ∧ b.z= -(T.nodes k).magnitude ∧
      b.input.geom.frame=frames (T.nodes k).frame
  entry : (i : Fin T.pairCount) → EntryUseS T frames latticeSetup simpleSetup bentSetup i

noncomputable def EntryUseS.datum {T frames L M LP SP BP i}
    (e : @EntryUseS T frames L M LP SP BP i) : CatalanCore.Li2.Uniform.DualDatum :=
  match e with
  | .old e => e.datum
  | .simple pool _ _ _ _ _ _ => (SP pool).input.data.dual

noncomputable def EntryUseS.level {T frames L M LP SP BP i}
    (e : @EntryUseS T frames L M LP SP BP i) : ℝ :=
  match e with
  | .old e => e.level
  | .simple pool _ _ _ _ _ _ => ((SP pool).setup.source.theta:ℝ)

theorem entryUseS_sound (T : CatalanCore.Li2.Uniform.NodeTable) (c : DecayCertificatesS T) (i : Fin T.pairCount) :
    CatalanCore.Li2.Uniform.Admissible (c.frames (T.entryNode i).frame) (T.entryNode i).sign
      (T.entryNode i).t (c.entry i).datum (c.entry i).level ∧
    ((T.entries i).lower:ℝ)≤CatalanCore.Li2.Uniform.dual (c.frames (T.entryNode i).frame)
      (T.entryNode i).sign (T.entryNode i).t ((T.entries i).rho:ℝ) (c.entry i).datum (c.entry i).level := by
  have hm : 0<(T.entryNode i).magnitude := (c.valid.1 (T.entries i).node).1
  have hmR : (0:ℝ)<((T.entryNode i).magnitude:ℝ) := by exact_mod_cast hm
  cases he : c.entry i with
  | old e =>
    simp only [EntryUseS.datum,EntryUseS.level]
    cases he2 : e with
    | lattice pool p hframe hz hr hD sourceIndex hindex hchecked =>
      simp only [EntryUse.datum,EntryUse.level]
      have hpure : (c.frames (T.entryNode i).frame).pure=true := by rw [hframe]; exact c.pure_frame
      have hb := (latticeCert_window (c.latticeSetup pool).z (c.latticeSetup pool).input
        (c.latticeSetup pool).setup p (c.latticeSetup pool).checked hchecked
        (c.frames (T.entryNode i).frame) (c.geometry (T.entryNode i).frame) hpure).1
      have hzR : (0:ℝ)<((c.latticeSetup pool).z:ℝ) := by rw [hz]; exact hmR
      have hs : CatalanCore.Li2.Uniform.signOf ((c.latticeSetup pool).z:ℝ)=(T.entryNode i).sign := by
        simp only [CatalanCore.Li2.Uniform.signOf,if_pos hzR,CatalanCore.Li2.Uniform.Node.sign,hframe,if_true]
      have ht : Real.log (1/|((c.latticeSetup pool).z:ℝ)|)=(T.entryNode i).t := by
        rw [hz,abs_of_pos hmR]
        rfl
      rw [hs,ht,hr,hD] at hb
      refine ⟨?_,hb⟩
      intro u hu
      rw [(c.frames (T.entryNode i).frame).pure_free hpure] at hu
      exact False.elim hu
    | bent b hframe hpool hz hf level sourceIndex hindex hchecked =>
      simp only [EntryUse.datum,EntryUse.level]
      have hzvalid := Seg.nodeCheck_validZ b.z b.input b.setup b.checked
      have hparts := Seg.nodeSegmentCheck_parts b.z b.input b.setup b.checked
      have hz0 : b.z ≠ 0 := ne_of_lt hparts.1.2.1
      have hcont := Seg.nodeContourPhysical_of_cellsE b.S b.G b.hS b.hG b.z hz0 b.input b.setup.density
        hparts.2.1 b.setup.contour b.contourOK
      have hat := Seg.nodeAtomPhysical_of_cellsE b.S b.G b.hS b.hG b.z hz0 b.input b.setup.density
        hparts.2.1 b.setup.atoms b.atomOK
      have hb := Seg.nodeCert_D_ge b.z b.input b.setup b.checked hcont hat.1 hat.2
        (T.entries i).rho level (T.entries i).lower hchecked
      have hzR : (b.z:ℝ)<0 := by rw [hz,Rat.cast_neg]; linarith
      have hs : CatalanCore.Li2.Uniform.signOf (b.z:ℝ)= -1 := by
        simp only [CatalanCore.Li2.Uniform.signOf,if_neg (not_lt.mpr hzR.le)]
      have ht : Real.log (1/|(b.z:ℝ)|)=(T.entryNode i).t := by
        rw [hz,Rat.cast_neg,abs_neg,abs_of_pos hmR]
        rfl
      have hsign : (T.entryNode i).sign= -1 := by
        simp only [CatalanCore.Li2.Uniform.Node.sign,if_neg hframe]
      have hd := hb.1
      rw [CatalanCore.Li2.Uniform.decay_dual_eq (b.z:ℝ) (T.entries i).rho hzvalid b.input.geom.frame
        b.input.data.dual level,hs,ht,hf] at hd
      have ha := hb.2
      rw [ht,hf] at ha
      rw [hsign]
      exact ⟨ha,hd⟩
  | simple pool p hframe hz hr hD hchecked =>
    simp only [EntryUseS.datum,EntryUseS.level]
    have hpure : (c.frames (T.entryNode i).frame).pure=true := by rw [hframe]; exact c.pure_frame
    have hb := (latticeSimple_window (c.simpleSetup pool).z (c.simpleSetup pool).input
      (c.simpleSetup pool).setup p (c.simpleSetup pool).checked hchecked
      (c.frames (T.entryNode i).frame) (c.geometry (T.entryNode i).frame) hpure).1
    have hzR : (0:ℝ)<((c.simpleSetup pool).z:ℝ) := by rw [hz]; exact hmR
    have hs : CatalanCore.Li2.Uniform.signOf ((c.simpleSetup pool).z:ℝ)=(T.entryNode i).sign := by
      simp only [CatalanCore.Li2.Uniform.signOf,if_pos hzR,CatalanCore.Li2.Uniform.Node.sign,hframe,if_true]
    have ht : Real.log (1/|((c.simpleSetup pool).z:ℝ)|)=(T.entryNode i).t := by
      rw [hz,abs_of_pos hmR]
      rfl
    rw [hs,ht,hr,hD] at hb
    refine ⟨?_,hb⟩
    intro u hu
    rw [(c.frames (T.entryNode i).frame).pure_free hpure] at hu
    exact False.elim hu

theorem tableSoundS_exists (T : CatalanCore.Li2.Uniform.NodeTable) (c : DecayCertificatesS T) :
    ∃ H : CatalanCore.Li2.Uniform.TableSound T,H.frames=c.frames ∧
      (∀ i,H.datum i=(c.entry i).datum) ∧ (∀ i,H.level i=(c.entry i).level) := by
  let H : CatalanCore.Li2.Uniform.TableSound T := {
    valid := c.valid
    frames := c.frames
    geometry := c.geometry
    pure_frame := c.pure_frame
    bent_cut := c.bent_cut
    datum := fun i => (c.entry i).datum
    level := fun i => (c.entry i).level
    admissible := fun i => (entryUseS_sound T c i).1
    bound := fun i => (entryUseS_sound T c i).2 }
  exact ⟨H,rfl,fun _ => rfl,fun _ => rfl⟩

noncomputable def tableSoundOfCertificatesS (T : CatalanCore.Li2.Uniform.NodeTable)
    (c : DecayCertificatesS T) : CatalanCore.Li2.Uniform.TableSound T := Classical.choose (tableSoundS_exists T c)

/-- The decay bound from a table certified on any mix of the cell, SIMPLE and bent routes. -/
theorem decayCertificatesS_candidate (T : CatalanCore.Li2.Uniform.NodeTable) (c : DecayCertificatesS T)
    (z : ℚ) (hz0 : z≠0) (hz1 : |(z:ℝ)|<1) (ρ D : ℝ) (hρ : 0<ρ)
    (hD : CatalanCore.Li2.Uniform.Candidate T (Int.sign z.num) (Real.log (1/|(z:ℝ)|)) ρ D) :
    CatalanCore.Uniform.HasScaledDecay (CatalanCore.Li2.li2Family z) CatalanCore.Li2.scale D ρ :=
  CatalanCore.Li2.Uniform.D_ge_of_candidate T (tableSoundOfCertificatesS T c) z hz0 hz1 ρ D hρ hD

end
end CatalanCore.Li2.DecayCert
