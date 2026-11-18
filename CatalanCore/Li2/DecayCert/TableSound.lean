module
public import CatalanCore.Li2.DecayCert.Table
public import CatalanCore.Li2.DecayCert.Assembly
public import CatalanCore.Li2.Uniform.Candidate
@[expose] public section
set_option Elab.async false
open Polynomial MeasureTheory Set Filter Topology
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert
open CatalanCore.Li2.Decay
noncomputable section

theorem entryUse_sound (T : CatalanCore.Li2.Uniform.NodeTable) (c : DecayCertificates T) (i : Fin T.pairCount) :
    CatalanCore.Li2.Uniform.Admissible (c.frames (T.entryNode i).frame) (T.entryNode i).sign
      (T.entryNode i).t (c.entry i).datum (c.entry i).level ∧
    ((T.entries i).lower:ℝ)≤CatalanCore.Li2.Uniform.dual (c.frames (T.entryNode i).frame)
      (T.entryNode i).sign (T.entryNode i).t ((T.entries i).rho:ℝ) (c.entry i).datum (c.entry i).level := by
  have hm : 0<(T.entryNode i).magnitude := (c.valid.1 (T.entries i).node).1
  have hmR : (0:ℝ)<((T.entryNode i).magnitude:ℝ) := by exact_mod_cast hm
  cases he : c.entry i with
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
    have hcont := Seg.nodeContourPhysical_of_cells b.S b.G b.hS b.hG b.z hz0 b.input b.setup.density
      hparts.2.1 b.shared b.sharedOK b.setup.contour b.contourOK
    have hat := Seg.nodeAtomPhysical_of_cells b.S b.G b.hS b.hG b.z hz0 b.input b.setup.density
      hparts.2.1 b.shared b.sharedOK b.setup.atoms b.atomOK
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
    rw [CatalanCore.Li2.Uniform.decay_dual_eq (b.z:ℝ) (T.entries i).rho hzvalid b.input.geom.frame b.input.data.dual level,
      hs,ht,hf] at hd
    have ha := hb.2
    rw [ht,hf] at ha
    rw [hsign]
    exact ⟨ha,hd⟩

theorem tableSound_exists (T : CatalanCore.Li2.Uniform.NodeTable) (c : DecayCertificates T) :
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
    admissible := fun i => (entryUse_sound T c i).1
    bound := fun i => (entryUse_sound T c i).2 }
  exact ⟨H,rfl,fun _ => rfl,fun _ => rfl⟩
noncomputable def tableSoundOfCertificates (T : CatalanCore.Li2.Uniform.NodeTable)
    (c : DecayCertificates T) : CatalanCore.Li2.Uniform.TableSound T := Classical.choose (tableSound_exists T c)

theorem tableSoundOfCertificates_frames (T : CatalanCore.Li2.Uniform.NodeTable) (c : DecayCertificates T) :
    (tableSoundOfCertificates T c).frames=c.frames := (Classical.choose_spec (tableSound_exists T c)).1

theorem tableSoundOfCertificates_datum (T : CatalanCore.Li2.Uniform.NodeTable) (c : DecayCertificates T) (i : Fin T.pairCount) :
    (tableSoundOfCertificates T c).datum i=(c.entry i).datum := (Classical.choose_spec (tableSound_exists T c)).2.1 i

theorem tableSoundOfCertificates_level (T : CatalanCore.Li2.Uniform.NodeTable) (c : DecayCertificates T) (i : Fin T.pairCount) :
    (tableSoundOfCertificates T c).level i=(c.entry i).level := (Classical.choose_spec (tableSound_exists T c)).2.2 i

theorem decayCertificates_candidate (T : CatalanCore.Li2.Uniform.NodeTable) (c : DecayCertificates T)
    (z : ℚ) (hz0 : z≠0) (hz1 : |(z:ℝ)|<1) (ρ D : ℝ) (hρ : 0<ρ)
    (hD : CatalanCore.Li2.Uniform.Candidate T (Int.sign z.num) (Real.log (1/|(z:ℝ)|)) ρ D) :
    CatalanCore.Uniform.HasScaledDecay (CatalanCore.Li2.li2Family z) CatalanCore.Li2.scale D ρ :=
  CatalanCore.Li2.Uniform.D_ge_of_candidate T (tableSoundOfCertificates T c) z hz0 hz1 ρ D hρ hD
#print axioms entryUse_sound
#print axioms tableSound_exists
#print axioms decayCertificates_candidate
end
end CatalanCore.Li2.DecayCert
