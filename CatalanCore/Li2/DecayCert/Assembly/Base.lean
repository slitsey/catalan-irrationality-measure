module
public import CatalanCore.Li2.DecayCert.Bent
public import CatalanCore.Li2.Decay.Assembly
public import CatalanCore.Li2.DecayCert.Lattice.Cert
@[expose] public section
set_option Elab.async false
open Polynomial MeasureTheory Set Filter Topology
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert
open CatalanCore.Li2.Decay
noncomputable section

theorem frameCut_zero_latPenalty (F : CatalanCore.Li2.Decay.Frame) (g : CatalanCore.Li2.Uniform.FrameGeometry F)
    (hc : CatalanCore.Li2.Uniform.frameCut g=some 0) (z : ℝ) (σ : Measure ℂ) (θ : ℝ) :
    latPenalty z F σ θ=0 := by
  cases g with
  | pure hp hl hf => simp only [CatalanCore.Li2.Uniform.frameCut] at hc; cases hc
  | polygon p hp hl hf =>
    have he : p.cut=0 := Option.some.inj hc
    change (∫ x in F.lattice,pos (W z σ (x:ℂ)-θ))=0
    rw [hl,he,integral_Icc_eq_integral_Ioc,Ioc_self,setIntegral_empty]

theorem atomPosSum_upper (z : ℚ) (hz : z≠0) (d : SegmentDatum) (dw : DensityWitness)
    (hd : datumCheck d dw=true) (cs : List AtomCell) (hc : atomCoverCheck z d cs=true) (ρ lam : ℚ) :
    atomPenalty (z:ℝ) (ρ:ℝ) d.dual.σ (lam:ℝ)≤(atomPosSum cs ρ lam:ℝ) := by
  obtain ⟨P,hP⟩ := checkedLinePartition_exists z d cs hc
  have hchecks : ∀ c∈cs,atomCellCheck z d c=true := by
    have hh := hc
    simp only [atomCoverCheck,Bool.and_eq_true,List.all_eq_true] at hh
    exact hh.2
  have hline : ∀ c∈P.cells,∀ u∈Icc 0 (c.len:ℝ),
      omega (z:ℝ) ((c.start:ℝ)+(c.dir:ℝ)*u)-2*U d.dual.σ (-(((c.start:ℝ)+(c.dir:ℝ)*u:ℝ):ℂ))≤(c.a:ℝ)+(c.b:ℝ)*u := by
    intro c hc u hu
    have hm : (c.start,c.len,c.dir,c.a,c.b)∈cs.map (fun c => (c.start,c.right-c.left,c.dir,c.witness.a,c.witness.b)) := by
      rw [← hP]
      exact List.mem_map.mpr ⟨c,hc,rfl⟩
    rcases List.mem_map.mp hm with ⟨a,ha,he⟩
    simp only [Prod.mk.injEq] at he
    rcases he with ⟨hs,hl,hd',ha',hb'⟩
    rw [← hs,← hd',← ha',← hb']
    exact lineCell_atomPoly z hz d dw hd a (hchecks a ha) u (by simpa only [← hl] using hu)
  have hf : Continuous (fun x : ℝ => omega (z:ℝ) x-2*U d.dual.σ (-(x:ℂ))) := by
    convert continuous_A_real (z:ℝ) 0 d.dual using 1
    funext x
    simp only [A,sub_zero]
  have hi := Dsum_spec _ P hf.continuousOn hline ρ lam
  have hsum : P.posSumQ ρ lam=atomPosSum cs ρ lam := by
    have he := congrArg (fun xs : List (ℚ×ℚ×ℚ×ℚ×ℚ) =>
      (xs.map (fun q => linePos q.2.2.2.1 q.2.2.2.2 q.2.1 (ρ+lam))).sum) hP
    simpa only [LinePartition.posSumQ,atomPosSum,List.map_map,Function.comp_def] using he
  rw [hsum] at hi
  unfold atomPenalty
  convert hi using 1
  congr 1
  funext x
  congr 1
  unfold A
  ring
end
end CatalanCore.Li2.DecayCert

namespace CatalanCore.Li2.Decay
open CatalanCore.Li2.DecayCert
noncomputable section

theorem bent_certificate_decay (z : ℝ) (hz : ValidZ z) (hneg : z<0)
    (F : CatalanCore.Li2.Decay.Frame) (g : CatalanCore.Li2.Uniform.FrameGeometry F)
    (hc : CatalanCore.Li2.Uniform.frameCut g=some 0) (d : DualDatum) (ℓ lam ρ Iup D : ℝ)
    (hρ : 0<ρ) (hlam : ℓ≤lam) (hF : FreeBound z F d ℓ)
    (hI : I d.σ≤Iup) (cells : LinePartition 1 4)
    (hcell : ∀ c∈cells.cells,∀ u∈Icc 0 (c.len:ℝ),
      omega z ((c.start:ℝ)+(c.dir:ℝ)*u)-2*U d.σ (-(((c.start:ℝ)+(c.dir:ℝ)*u:ℝ):ℂ))≤(c.a:ℝ)+(c.b:ℝ)*u)
    (hD : D≤ -(12*Real.log 2+4)-Iup-2*lam-cells.posSum ρ lam) :
    WindowDecay (normalizedQ z) (li2 z) D ρ := by
  have hf : Continuous (fun x : ℝ => omega z x-2*U d.σ (-(x:ℂ))) := by
    convert continuous_A_real z 0 d using 1
    funext x
    simp only [A,sub_zero]
  have hA := Dsum_spec_real _ cells hf.continuousOn hcell ρ lam
  have hA' : atomPenalty z ρ d.σ lam≤cells.posSum ρ lam := by
    unfold atomPenalty
    convert hA using 1
    congr 1
    funext x
    congr 1
    unfold A
    ring
  have hbound : D≤dualValue z ρ F d.σ lam := by
    unfold dualValue
    rw [frameCut_zero_latPenalty F g hc]
    linarith
  exact (li2_window_decay z hz F g d lam ρ hρ (fun u hu => (hF u hu).trans hlam)).mono hbound
#print axioms bent_certificate_decay
end
end CatalanCore.Li2.Decay
#print axioms CatalanCore.Li2.DecayCert.atomPosSum_upper
