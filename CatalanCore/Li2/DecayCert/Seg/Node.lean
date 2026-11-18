module
public import CatalanCore.Li2.DecayCert.Seg.NodeAtoms
public import CatalanCore.Li2.DecayCert.Assembly
@[expose] public section
set_option Elab.async false
open Polynomial MeasureTheory Set Filter Topology
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert.Seg
open CatalanCore.Li2.DecayCert CatalanCore.Li2.Decay
noncomputable section

variable {CC AC : Type} [ContourProj CC] [AtomProj AC]

theorem nodeSegmentCheck_parts (z : ℚ) (b : BentInput) (c : NodeCert CC AC)
    (hc : nodeSegmentCheck z b c=true) :
    (-1 < z ∧ z < 0 ∧ c.atomCaps.length=b.atoms.length) ∧
    datumCheck b.data c.density=true ∧ placementCheck b=true ∧
    nodeContourCoverCheck b c.contour=true ∧
    (∀ x ∈ c.contour,x.2.2 ≤ c.ell) ∧
    nodeAtomCoverCheck c.atoms=true ∧ energyCoverCheck b c.energyCells=true ∧
    scalarUpperCheck (bentTailExpr b c.toBent) c.ell=true ∧
    ∃ e,nodeEnergyExpr z b c=some e ∧ scalarUpperCheck e c.Iup=true := by
  have h := hc
  simp only [nodeSegmentCheck,Bool.and_eq_true,decide_eq_true_eq] at h
  rcases h with ⟨⟨⟨⟨⟨⟨⟨⟨⟨hshape,hatoms⟩,hd⟩,hp⟩,hcover⟩,hbounds⟩,hatomcover⟩,henergycover⟩,htail⟩,henergy⟩
  refine ⟨hshape,hd,hp,hcover,?_,hatomcover,henergycover,htail,?_⟩
  · intro x hx
    have hrow := (List.all_eq_true.mp hbounds) x hx
    simpa using hrow
  · cases he : nodeEnergyExpr z b c with
    | none => simp [he] at henergy
    | some e => exact ⟨e,rfl,by simpa only [he] using henergy⟩

theorem nodeSegmentCheck_sound (z : ℚ) (b : BentInput) (c : NodeCert CC AC)
    (hc : nodeSegmentCheck z b c=true)
    (hcont : NodeContourPhysical z b c.contour) (hatW : NodeAtomWPhysical z b c.atoms) :
    FreeBound (z:ℝ) b.geom.frame b.data.dual c.ell ∧ I b.data.dual.σ ≤ (c.Iup:ℝ) := by
  rcases nodeSegmentCheck_parts z b c hc with
    ⟨hshape,hd,hp,hcover,hbounds,hatomcover,henergycover,htail,e,he,hscalar⟩
  have hz : ValidZ (z:ℝ) := by
    have hn : (z:ℝ) < 0 := by exact_mod_cast hshape.2.1
    have hl : (-1:ℝ) < (z:ℝ) := by exact_mod_cast hshape.1
    constructor
    · exact abs_pos.mpr hn.ne
    · rw [abs_of_neg hn]
      linarith
  refine ⟨node_free_bound z hz hshape.2.1 b c hd hp hcover hbounds hcont htail,?_⟩
  exact (nodeEnergyExpr_upper z hshape.2.1 b c hd hp hcont hatW henergycover e he).trans
    (scalarUpperCheck_sound e c.Iup hscalar)

theorem nodeCheck_validZ (z : ℚ) (b : BentInput) (c : NodeCert CC AC) (hc : nodeSegmentCheck z b c=true) :
    ValidZ (z:ℝ) := by
  have hs := (nodeSegmentCheck_parts z b c hc).1
  have hn : (z:ℝ)<0 := by exact_mod_cast hs.2.1
  have hl : (-1:ℝ)<(z:ℝ) := by exact_mod_cast hs.1
  exact ⟨abs_pos.mpr hn.ne,by rw [abs_of_neg hn]; linarith⟩

theorem nodeCert_D_ge (z : ℚ) (b : BentInput) (c : NodeCert CC AC)
    (hc : nodeSegmentCheck z b c=true)
    (hcont : NodeContourPhysical z b c.contour) (hatW : NodeAtomWPhysical z b c.atoms)
    (hatL : NodeAtomLinePhysical z b c.atoms)
    (ρ lam D : ℚ) (hp : nodePairCheck c ρ lam D=true) :
    (D:ℝ)≤dualValue (z:ℝ) (ρ:ℝ) b.geom.frame b.data.dual.σ (lam:ℝ) ∧
      CatalanCore.Li2.Uniform.Admissible b.geom.frame (-1) (Real.log (1/|(z:ℝ)|)) b.data.dual (lam:ℝ) := by
  have hz := nodeCheck_validZ z b c hc
  have hn : (z:ℝ)<0 := by exact_mod_cast (nodeSegmentCheck_parts z b c hc).1.2.1
  have hparts := nodeSegmentCheck_parts z b c hc
  have hpair := hp
  simp only [nodePairCheck,Bool.and_eq_true,decide_eq_true_eq] at hpair
  have hlam : (c.ell:ℝ)≤(lam:ℝ) := by exact_mod_cast hpair.1.2
  have hs := nodeSegmentCheck_sound z b c hc hcont hatW
  have hfree : FreeBound (z:ℝ) b.geom.frame b.data.dual (lam:ℝ) := fun u hu => (hs.1 u hu).trans hlam
  have hA := nodeAtomPosSum_upper z b c.atoms hparts.2.2.2.2.2.1 hatL ρ lam
  have hscalar := scalarLowerCheck_sound _ _ hpair.2
  simp only [seSum_value,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    seScale_value,ScalarExpr.value,seRat_value,Rat.cast_neg,Rat.cast_ofNat] at hscalar
  push_cast at hscalar
  have hcut : CatalanCore.Li2.Uniform.frameCut b.geom.geometry=some 0 := by
    simp only [BentFrame.geometry,CatalanCore.Li2.Uniform.frameCut,b.geom.cut_zero]
  refine ⟨?_,?_⟩
  · unfold dualValue
    rw [frameCut_zero_latPenalty _ b.geom.geometry hcut]
    linarith [hs.2]
  · have hadm := (CatalanCore.Li2.Uniform.decay_freeBound_iff (z:ℝ) hz b.geom.frame b.data.dual lam).mp hfree
    have hsign : CatalanCore.Li2.Uniform.signOf (z:ℝ)= -1 := by simp [CatalanCore.Li2.Uniform.signOf,not_lt.mpr hn.le]
    rwa [hsign] at hadm

theorem nodeCert_window (z : ℚ) (b : BentInput) (c : NodeCert CC AC)
    (hc : nodeSegmentCheck z b c=true)
    (hcont : NodeContourPhysical z b c.contour) (hatW : NodeAtomWPhysical z b c.atoms)
    (hatL : NodeAtomLinePhysical z b c.atoms)
    (ρ lam D : ℚ) (hp : nodePairCheck c ρ lam D=true) :
    CatalanCore.Li2.Uniform.WindowBound z (ρ:ℝ) (D:ℝ) := by
  have hz := nodeCheck_validZ z b c hc
  have hpair := hp
  simp only [nodePairCheck,Bool.and_eq_true,decide_eq_true_eq] at hpair
  have hρ : (0:ℝ)<(ρ:ℝ) := by exact_mod_cast hpair.1.1
  have hlam : (c.ell:ℝ)≤(lam:ℝ) := by exact_mod_cast hpair.1.2
  have hs := nodeSegmentCheck_sound z b c hc hcont hatW
  have hfree : FreeBound (z:ℝ) b.geom.frame b.data.dual (lam:ℝ) := fun u hu => (hs.1 u hu).trans hlam
  exact family_window_bound z hz D ρ ((li2_window_decay (z:ℝ) hz b.geom.frame b.geom.geometry b.data.dual lam ρ hρ hfree).mono
    (nodeCert_D_ge z b c hc hcont hatW hatL ρ lam D hp).1)
#print axioms nodeCert_D_ge
#print axioms nodeCert_window
end
end CatalanCore.Li2.DecayCert.Seg
