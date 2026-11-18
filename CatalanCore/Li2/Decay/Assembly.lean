module
public import CatalanCore.Li2.Decay.Contour
public import CatalanCore.Li2.Decay.Dual
public import CatalanCore.Tools.IntegratedJets
public import CatalanCore.Tools.JetConfigurations
public import CatalanLambda.Decay.AndreiefSum
public import CatalanCore.Li2.Port.Unified.Modular.Base.PoleFamily
public import CatalanCore.Li2.Port.Unified.Modular.Base.ParameterDifferentialDissection
public import CatalanCore.Li2.Uniform.DecayBridge
public import CatalanCore.Uniform.Measure.NV0
public import CatalanCore.Li2.Family
public import CatalanCore.Li2.Decay.Series
public import CatalanCore.Li2.Port.Unified.Modular.Base.ParameterPolynomialSeries
public import CatalanCore.Li2.Port.Unified.Modular.Base.PoleDissectionWindow
public import CatalanCore.Decay.TheoremA
public import CatalanCore.Li2.Decay.WindowSpec
public import CatalanCore.Tools.FactorialProducts
@[expose] public section
set_option Elab.async false
open MeasureTheory Set Filter Polynomial
open scoped Topology BigOperators
namespace CatalanCore.Li2.Decay.HeineSource
open CatalanCore.Li2.Uniform CatalanCore.Decay.CurveFamily
open CatalanLambda.Decay (sumM integrable_sumM_iff integral_sumM)

noncomputable def orientedPieces {F : Frame} (g : FrameGeometry F) (n : ℕ) : List (Piece × ℂ) :=
  match g with
  | .pure _ _ _ => []
  | .polygon p _ _ _ => (upperModified p n).map (fun q => (q,-1)) ++
      ((upperModified p n).map Piece.conj).map (fun q => (q,1))

abbrev LatticeIdx (F : Frame) (n : ℕ) := {x : ℕ // 1 ≤ x ∧ (x:ℝ)/(n:ℝ) ∈ F.lattice}
abbrev AtomIdx (n : ℕ) := {j : ℕ // j ∈ Finset.Icc (n+1) (4*n)}
abbrev SourceSpace {F : Frame} (g : FrameGeometry F) (n : ℕ) :=
  LatticeIdx F n ⊕ ((Fin (orientedPieces g n).length × ℝ) ⊕ (ℝ ⊕ AtomIdx n))

noncomputable def curveMeasure {F : Frame} (g : FrameGeometry F) (n : ℕ)
    (i : Fin (orientedPieces g n).length) : Measure ℝ :=
  NNReal.mk ‖((orientedPieces g n).get i).1.D‖ (norm_nonneg _) • ((orientedPieces g n).get i).1.nu

instance curveMeasure_sigmaFinite {F : Frame} (g : FrameGeometry F) (n : ℕ)
    (i : Fin (orientedPieces g n).length) : SigmaFinite (curveMeasure g n i) := by
  unfold curveMeasure
  infer_instance

noncomputable def rayMeasure {F : Frame} (g : FrameGeometry F) (z : ℝ) (n : ℕ) : Measure ℝ :=
  match g with
  | .pure _ _ _ => 0
  | .polygon p _ _ _ => if 0 < z then volume.restrict (Ici ((Nat.floor (p.cut*n):ℝ)+1/2)) else 0

instance rayMeasure_sigmaFinite {F : Frame} (g : FrameGeometry F) (z : ℝ) (n : ℕ) :
    SigmaFinite (rayMeasure g z n) := by
  cases g with
  | pure hp hl hf => unfold rayMeasure; infer_instance
  | polygon p hp hl hf => unfold rayMeasure; split_ifs <;> infer_instance

noncomputable def sourceMeasure {F : Frame} (g : FrameGeometry F) (z : ℝ) (n : ℕ) :
    Measure (SourceSpace g n) :=
  sumM (Measure.count : Measure (LatticeIdx F n))
    (sumM (famMeasure (curveMeasure g n))
      (sumM (rayMeasure g z n) (Measure.count : Measure (AtomIdx n))))

instance sourceMeasure_sigmaFinite {F : Frame} (g : FrameGeometry F) (z : ℝ) (n : ℕ) :
    SigmaFinite (sourceMeasure g z n) := by
  unfold sourceMeasure
  infer_instance

noncomputable def sourceParticle {F : Frame} (g : FrameGeometry F) (n : ℕ) : SourceSpace g n → Particle
  | .inl x => .lattice x.val
  | .inr (.inl r) => .contour (((orientedPieces g n).get r.1).1.zeta r.2)
  | .inr (.inr (.inl x)) => .ray x
  | .inr (.inr (.inr j)) => .atom j.val

noncomputable def sourceJet {F : Frame} (g : FrameGeometry F) (z : ℝ) (n : ℕ) (t : ℝ) :
    SourceSpace g n → (ℂ[X] →ₗ[ℂ] ℂ)
  | .inl x => latticeA z n x.val • Polynomial.leval (x.val:ℂ)+
      latticeB z n x.val • ((Polynomial.leval (x.val:ℂ)).comp Polynomial.derivative)
  | .inr (.inl r) =>
      let q := ((orientedPieces g n).get r.1).1
      let s := ((orientedPieces g n).get r.1).2
      (s*(q.D/(‖q.D‖:ℂ))*contourDensity z n 1 (q.zeta r.2)) • Polynomial.leval (q.zeta r.2)
  | .inr (.inr (.inl x)) => rayDensity z n (x:ℂ) • Polynomial.leval (x:ℂ)
  | .inr (.inr (.inr j)) => (t*atomWeight z n j.val:ℂ) • Polynomial.leval (-(j.val:ℂ))

theorem sourceJet_lattice {F : Frame} (g : FrameGeometry F) (z : ℝ) (n : ℕ) (t : ℝ)
    (x : LatticeIdx F n) (T : ℂ[X]) :
    sourceJet g z n t (.inl x) T=latticeA z n x.val*T.eval (x.val:ℂ)+
      latticeB z n x.val*T.derivative.eval (x.val:ℂ) := by
  simp [sourceJet,Polynomial.leval,LinearMap.comp_apply,smul_eq_mul]
end CatalanCore.Li2.Decay.HeineSource
#print axioms CatalanCore.Li2.Decay.HeineSource.sourceMeasure_sigmaFinite
#print axioms CatalanCore.Li2.Decay.HeineSource.sourceJet_lattice

namespace CatalanCore.Li2.Decay.HeineSource
open CatalanCore.Li2.Uniform ContourGeometry

theorem sourceJet_lattice_deriv {F : Frame} (g : FrameGeometry F) (z : ℝ) (n : ℕ) (t : ℝ)
    (x : LatticeIdx F n) (T : ℂ[X]) :
    sourceJet g z n t (.inl x) T=(z:ℂ)^x.val*deriv (rationalCore n T) (x.val:ℂ) := by
  let U : ℂ → ℂ := fun u => u*weight n u
  have hUeq : rationalCore n (1:ℂ[X])=U := by funext u; simp [rationalCore,U]
  have hU := rationalCore_differentiableAt_right n (1:ℂ[X]) (x.val:ℂ) (by
    change -(1/4:ℝ)<(x.val:ℂ).re
    simp only [Complex.natCast_re]
    have hh := Nat.cast_nonneg x.val (α := ℝ)
    linarith)
  rw [hUeq] at hU
  have hd := hU.hasDerivAt.mul (T.hasDerivAt (x.val:ℂ))
  have hR : rationalCore n T=(fun u => U u*T.eval u) := funext fun _ => rfl
  have hder : deriv (fun u => U u*T.eval u) (x.val:ℂ)=
      deriv U (x.val:ℂ)*T.eval (x.val:ℂ)+U (x.val:ℂ)*T.derivative.eval (x.val:ℂ) := hd.deriv
  rw [sourceJet_lattice,hR,hder]
  unfold latticeA latticeB
  dsimp only [U]
  ring

theorem lattice_term_summable (z : ℝ) (hz : ValidZ z) (n : ℕ) (T : ℂ[X]) :
    Summable (fun x : ℕ => (z:ℂ)^x*deriv (rationalCore n T) (x:ℂ)) := by
  have hs := correctedLine_summable z hz n T
  have hb : Summable (fun x : ℕ => correctedLine z n T (x+1)) := (summable_nat_add_iff 1).mpr hs
  have hdiff := hs.sub hb
  have he (x : ℕ) : correctedLine z n T x-correctedLine z n T (x+1)=
      (z:ℂ)^(x+1)*deriv (rationalCore n T) ((x+1:ℕ):ℂ) := correctedLine_sub z hz n x T
  have hshift : Summable (fun x : ℕ => (z:ℂ)^(x+1)*deriv (rationalCore n T) ((x+1:ℕ):ℂ)) := by
    simpa only [Pi.sub_apply,he] using hdiff
  exact (summable_nat_add_iff 1).mp hshift

theorem lattice_source_summable {F : Frame} (g : FrameGeometry F) (z : ℝ) (hz : ValidZ z)
    (n : ℕ) (t : ℝ) (T : ℂ[X]) :
    Summable (fun x : LatticeIdx F n => sourceJet g z n t (.inl x) T) := by
  simp_rw [sourceJet_lattice_deriv]
  exact (lattice_term_summable z hz n T).comp_injective Subtype.val_injective
end CatalanCore.Li2.Decay.HeineSource
#print axioms CatalanCore.Li2.Decay.HeineSource.sourceJet_lattice_deriv
#print axioms CatalanCore.Li2.Decay.HeineSource.lattice_source_summable


namespace CatalanCore.Li2.Decay.HeineSource
open CatalanCore.Li2.Uniform ContourGeometry

theorem lattice_source_integrable {F : Frame} (g : FrameGeometry F) (z : ℝ) (hz : ValidZ z)
    (n : ℕ) (t : ℝ) (T : ℂ[X]) :
    Integrable (fun x : LatticeIdx F n => sourceJet g z n t (.inl x) T) Measure.count := by
  apply integrable_count_iff.mpr
  exact (lattice_source_summable g z hz n t T).norm

theorem atom_source_integrable {F : Frame} (g : FrameGeometry F) (z : ℝ)
    (n : ℕ) (t : ℝ) (T : ℂ[X]) :
    Integrable (fun j : AtomIdx n => sourceJet g z n t (.inr (.inr (.inr j))) T) Measure.count := by
  exact Integrable.of_finite

theorem lattice_idx_polygon_iff (p : PolygonFrame) (n : ℕ) (hn : 0 < n) (x : ℕ) :
    (1 ≤ x ∧ (x:ℝ)/(n:ℝ) ∈ Icc 0 p.cut) ↔ x ∈ Finset.Icc 1 (Nat.floor (p.cut*n)) := by
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  have hcut : 0 ≤ p.cut*(n:ℝ) := mul_nonneg p.nonneg hnR.le
  simp only [mem_Icc,Finset.mem_Icc]
  constructor
  · rintro ⟨hx,h0,h1⟩
    refine ⟨hx,(Nat.le_floor_iff hcut).mpr ?_⟩
    exact (div_le_iff₀ hnR).mp h1
  · rintro ⟨hx,h1⟩
    exact ⟨hx,div_nonneg (Nat.cast_nonneg _) hnR.le,
      (div_le_iff₀ hnR).mpr ((Nat.le_floor_iff hcut).mp h1)⟩

theorem functional_head_tail (z : ℝ) (hz : ValidZ z) (n N : ℕ) (t : ℝ) (T : ℂ[X]) :
    functional z n t T=(∑ x ∈ Finset.Icc 1 N, (z:ℂ)^x*deriv (rationalCore n T) (x:ℂ))+
      latticeTail z n N T+(t:ℂ)*∑ j ∈ Finset.Icc (n+1) (4*n), (atomWeight z n j:ℂ)*T.eval (-(j:ℂ)) := by
  let f : ℕ → ℂ := fun x => (z:ℂ)^(x+1)*deriv (rationalCore n T) ((x+1:ℕ):ℂ)
  have hs : Summable f := (summable_nat_add_iff 1).mpr (lattice_term_summable z hz n T)
  have hh := hs.sum_add_tsum_nat_add N
  have hhead : (∑ x ∈ Finset.range N, f x)=∑ x ∈ Finset.Icc 1 N, (z:ℂ)^x*deriv (rationalCore n T) (x:ℂ) := by
    apply Finset.sum_bij (fun x hx => x+1)
    · intro x hx
      simp only [Finset.mem_Icc,Finset.mem_range] at hx ⊢
      omega
    · intro x hx y hy he
      omega
    · intro y hy
      refine ⟨y-1,?_,?_⟩
      · simp only [Finset.mem_Icc] at hy
        simp only [Finset.mem_range]
        omega
      · have h1 := (Finset.mem_Icc.mp hy).1
        omega
    · intro x hx
      rfl
  have htail : (∑' x : ℕ, f (x+N))=latticeTail z n N T := by
    apply tsum_congr
    intro x
    dsimp only [f,latticeTail]
    have he : x+N+1=N+1+x := by omega
    rw [he]
    rfl
  rw [hhead,htail] at hh
  have hfun : rationalCore n T=(fun u : ℂ => u*weight n u*T.eval u) := funext fun _ => rfl
  unfold functional
  rw [← hfun]
  change (∑' x : ℕ, f x)+_= _
  rw [← hh]
end CatalanCore.Li2.Decay.HeineSource
#print axioms CatalanCore.Li2.Decay.HeineSource.functional_head_tail


namespace CatalanCore.Li2.Decay.HeineSource
open CatalanCore.Li2.Uniform CatalanCore.Decay.CurveFamily ContourGeometry

theorem piece_ae_in_set (q : Piece) : ∀ᵐ y : ℝ ∂q.nu, q.zeta y ∈ pieceSet q := by
  cases hq : q.ray
  · change ∀ᵐ y : ℝ ∂(if q.ray then volume.restrict (Ioi 0) else volume.restrict (Ioc 0 1)), _
    rw [if_neg (by simp [hq])]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
    exact ⟨y,by simpa [hq] using ⟨hy.1.le,hy.2⟩,rfl⟩
  · change ∀ᵐ y : ℝ ∂(if q.ray then volume.restrict (Ioi 0) else volume.restrict (Ioc 0 1)), _
    rw [if_pos (by simp [hq])]
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact ⟨y,by simpa [hq] using hy.le,rfl⟩

theorem contourDensity_measurable (z : ℝ) (n : ℕ) (T : ℂ[X]) : Measurable (contourDensity z n T) := by
  rw [contourDensity_eq]
  exact (densityCore_measurable z n T).const_mul _

theorem piece_density_integrable (z : ℝ) (hz : ValidZ z) (n : ℕ) (T : ℂ[X]) (q : Piece)
    (hdom : ∀ u ∈ pieceSet q, 0 ≤ u.re ∧ ((∃ N : ℕ, u.re=(N:ℝ)+1/2) ∨ 1 ≤ |u.im|))
    (hgap : q.ray=true → ∀ y : ℝ, 0 ≤ y → y ≤ ‖q.zeta y‖) :
    Integrable (fun y : ℝ => contourDensity z n T (q.zeta y)) q.nu := by
  obtain ⟨M,a,hM,ha,hbound⟩ := densityCore_radial_bound z hz n T
  let B := ‖((2*Real.pi:ℂ)*Complex.I)⁻¹‖*M
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hm : Measurable (fun y : ℝ => contourDensity z n T (q.zeta y)) :=
    (contourDensity_measurable z n T).comp (by unfold Piece.zeta; fun_prop)
  have hh : ∀ᵐ y : ℝ ∂q.nu, ‖contourDensity z n T (q.zeta y)‖ ≤ B*Real.exp (-a*‖q.zeta y‖) := by
    filter_upwards [piece_ae_in_set q] with y hy
    have hd := hdom _ hy
    have hb := hbound (q.zeta y) (by linarith [hd.1]) hd.2
    rw [contourDensity_eq]
    change ‖((2*Real.pi:ℂ)*Complex.I)⁻¹*densityCore z n T (q.zeta y)‖ ≤ _
    rw [norm_mul]
    simpa only [B,mul_assoc] using mul_le_mul_of_nonneg_left hb (norm_nonneg (((2*Real.pi:ℂ)*Complex.I)⁻¹))
  cases hr : q.ray
  · have hnu : q.nu=volume.restrict (Ioc (0:ℝ) 1) := by simp [Piece.nu,hr]
    rw [hnu] at hh ⊢
    apply (integrable_const B).mono' hm.aestronglyMeasurable
    filter_upwards [hh] with y hy
    have he : Real.exp (-a*‖q.zeta y‖) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [norm_nonneg (q.zeta y)])
    exact hy.trans ((mul_le_mul_of_nonneg_left he hB).trans_eq (mul_one B))
  · have hnu : q.nu=volume.restrict (Ioi (0:ℝ)) := by simp [Piece.nu,hr]
    rw [hnu] at hh ⊢
    apply ((integrableOn_exp_mul_Ioi (by linarith : -a<0) 0).const_mul B).mono' hm.aestronglyMeasurable
    filter_upwards [hh,ae_restrict_mem measurableSet_Ioi] with y hy hy0
    have hg := hgap hr y hy0.le
    exact hy.trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hg (by linarith))) hB)

theorem sourceJet_curve_apply {F : Frame} (g : FrameGeometry F) (z : ℝ) (n : ℕ) (t : ℝ)
    (i : Fin (orientedPieces g n).length) (y : ℝ) (T : ℂ[X]) :
    sourceJet g z n t (.inr (.inl (i,y))) T=
      (((orientedPieces g n).get i).2*((((orientedPieces g n).get i).1.D)/
        (‖((orientedPieces g n).get i).1.D‖:ℂ)))*
        contourDensity z n T (((orientedPieces g n).get i).1.zeta y) := by
  simp only [sourceJet,LinearMap.smul_apply,Polynomial.leval_apply,smul_eq_mul]
  unfold contourDensity
  simp only [Polynomial.eval_one]
  ring

theorem ray_source_integrable {F : Frame} (g : FrameGeometry F) (z : ℝ) (hz : ValidZ z)
    (n : ℕ) (t : ℝ) (T : ℂ[X]) :
    Integrable (fun x : ℝ => sourceJet g z n t (.inr (.inr (.inl x))) T) (rayMeasure g z n) := by
  cases g with
  | pure hp hl hf => simp [rayMeasure]
  | polygon p hp hl hf =>
    by_cases hpos : 0 < z
    · obtain ⟨C,q,hC,hq,hq1,hh⟩ := realTail_geometric_bound z hz n T
      have hi := (hh (Nat.floor (p.cut*n))).1.const_mul (-(Real.log |z|:ℂ))
      have he : (fun x : ℝ => sourceJet (FrameGeometry.polygon p hp hl hf) z n t (.inr (.inr (.inl x))) T)=
          (fun x : ℝ => -(Real.log |z|:ℂ)*realDensity z n T x) := by
        funext x
        simp only [sourceJet,LinearMap.smul_apply,Polynomial.leval_apply,smul_eq_mul]
        unfold rayDensity realDensity rationalCore
        ring
      rw [he]
      simpa only [rayMeasure,if_pos hpos] using hi
    · simp [rayMeasure,hpos]
end CatalanCore.Li2.Decay.HeineSource
#print axioms CatalanCore.Li2.Decay.HeineSource.piece_density_integrable
#print axioms CatalanCore.Li2.Decay.HeineSource.ray_source_integrable


namespace CatalanCore.Li2.Decay.HeineSource
open CatalanCore.Li2.Uniform CatalanCore.Decay.CurveFamily ContourGeometry
open CatalanLambda.Decay (integrable_sumM_iff)

theorem chainPiece_ray_false (vs : List ℂ) (q : Piece) (hq : q ∈ chainPieces vs) : q.ray=false := by
  induction vs with
  | nil => simp [chainPieces] at hq
  | cons a rest ih =>
    cases rest with
    | nil => simp [chainPieces] at hq
    | cons b rest =>
      change q ∈ ⟨a,b-a,false⟩::chainPieces (b::rest) at hq
      rcases List.mem_cons.mp hq with rfl|hq
      · rfl
      · exact ih hq

theorem oriented_piece_in_gamma {F : Frame} (g : FrameGeometry F) (n : ℕ) (r : Piece × ℂ)
    (hr : r ∈ orientedPieces g n) (u : ℂ) (hu : u ∈ pieceSet r.1) : u ∈ gammaN g n := by
  cases g with
  | pure hp hl hf => simp [orientedPieces] at hr
  | polygon p hp hl hf =>
    simp only [orientedPieces,List.mem_append,List.mem_map] at hr
    change u ∈ piecesSet (upperModified p n) ∪ piecesSet ((upperModified p n).map Piece.conj)
    rcases hr with ⟨q,hq,rfl⟩|⟨q,hq,rfl⟩
    · apply Or.inl
      simp only [piecesSet,mem_iUnion]
      exact ⟨q,hq,hu⟩
    · apply Or.inr
      simp only [piecesSet,mem_iUnion]
      exact ⟨q,List.mem_map.mpr hq,hu⟩

theorem upper_ray_gap (p : PolygonFrame) (n : ℕ) (hn : 0 < n) (q : Piece)
    (hq : q ∈ upperModified p n) (hray : q.ray=true) (y : ℝ) (hy : 0 ≤ y) : y ≤ ‖q.zeta y‖ := by
  simp only [upperModified,List.mem_append,List.mem_singleton] at hq
  rcases hq with hq|rfl
  · have hh := chainPiece_ray_false _ q hq
    rw [hh] at hray
    contradiction
  · have hv : 0 < (p.vertex p.edges).im := by
      have hh := p.imag_strict 0 p.edges p.edges_pos (le_refl _)
      simpa only [p.initial,Complex.ofReal_im] using hh
    have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
    have him : (Piece.zeta ⟨(n:ℂ)*p.vertex p.edges,Complex.I,true⟩ y).im=
        (n:ℝ)*(p.vertex p.edges).im+y := by simp [Piece.zeta]
    have hi : y ≤ (Piece.zeta ⟨(n:ℂ)*p.vertex p.edges,Complex.I,true⟩ y).im := by rw [him]; nlinarith [mul_pos hnR hv]
    exact hi.trans ((le_abs_self _).trans (Complex.abs_im_le_norm _))

theorem oriented_ray_gap {F : Frame} (g : FrameGeometry F) (n : ℕ) (hn : 0 < n) (r : Piece × ℂ)
    (hr : r ∈ orientedPieces g n) (hray : r.1.ray=true) (y : ℝ) (hy : 0 ≤ y) : y ≤ ‖r.1.zeta y‖ := by
  cases g with
  | pure hp hl hf => simp [orientedPieces] at hr
  | polygon p hp hl hf =>
    simp only [orientedPieces,List.mem_append,List.mem_map] at hr
    rcases hr with ⟨q,hq,rfl⟩|⟨q,hq,rfl⟩
    · exact upper_ray_gap p n hn q hq hray y hy
    · obtain ⟨q,hq,rfl⟩ := hq
      rw [Piece.zeta_conj,Complex.norm_conj]
      exact upper_ray_gap p n hn q hq hray y hy

theorem curve_source_integrable {F : Frame} (g : FrameGeometry F) (z : ℝ) (hz : ValidZ z)
    (n : ℕ) (hn : 0 < n) (t : ℝ) (T : ℂ[X])
    (hΓ : ∀ u ∈ gammaN g n, 0 ≤ u.re ∧ 1/2 ≤ ‖u‖ ∧
      ((∃ N : ℕ, u.re=(N:ℝ)+1/2) ∨ 1 ≤ |u.im|)) :
    Integrable (fun r : Fin (orientedPieces g n).length × ℝ =>
      sourceJet g z n t (.inr (.inl r)) T) (famMeasure (curveMeasure g n)) := by
  rw [integrable_fam_iff]
  intro i
  let r := (orientedPieces g n).get i
  have hr : r ∈ orientedPieces g n := List.get_mem _ _
  have hi := piece_density_integrable z hz n T r.1 (fun u hu =>
    let h := hΓ u (oriented_piece_in_gamma g n r hr u hu)
    ⟨h.1,h.2.2⟩) (fun hh y hy => oriented_ray_gap g n hn r hr hh y hy)
  have hm := (hi.const_mul (r.2*(r.1.D/(‖r.1.D‖:ℂ)))).smul_measure_nnreal
    (c := NNReal.mk ‖r.1.D‖ (norm_nonneg _))
  simpa only [curveMeasure,r,sourceJet_curve_apply] using hm

theorem source_integrable {F : Frame} (g : FrameGeometry F) (z : ℝ) (hz : ValidZ z)
    (n : ℕ) (hn : 0 < n) (t : ℝ) (T : ℂ[X])
    (hΓ : ∀ u ∈ gammaN g n, 0 ≤ u.re ∧ 1/2 ≤ ‖u‖ ∧
      ((∃ N : ℕ, u.re=(N:ℝ)+1/2) ∨ 1 ≤ |u.im|)) :
    Integrable (fun r : SourceSpace g n => sourceJet g z n t r T) (sourceMeasure g z n) := by
  unfold sourceMeasure
  rw [integrable_sumM_iff,integrable_sumM_iff,integrable_sumM_iff]
  exact ⟨lattice_source_integrable g z hz n t T,curve_source_integrable g z hz n hn t T hΓ,
    ray_source_integrable g z hz n t T,atom_source_integrable g z n t T⟩
end CatalanCore.Li2.Decay.HeineSource
#print axioms CatalanCore.Li2.Decay.HeineSource.source_integrable


namespace CatalanCore.Li2.Decay.HeineSource
open CatalanCore.Li2.Uniform CatalanCore.Decay.CurveFamily ContourGeometry

theorem curve_integral_index {F : Frame} (g : FrameGeometry F) (z : ℝ) (n : ℕ) (t : ℝ)
    (i : Fin (orientedPieces g n).length) (T : ℂ[X]) :
    (∫ y : ℝ, sourceJet g z n t (.inr (.inl (i,y))) T ∂curveMeasure g n i)=
      ((orientedPieces g n).get i).2*pieceIntegral ((orientedPieces g n).get i).1 (contourDensity z n T) := by
  simp_rw [sourceJet_curve_apply]
  dsimp only [curveMeasure]
  rw [integral_smul_nnreal_measure,integral_const_mul]
  simp only [NNReal.smul_def,NNReal.coe_mk,Complex.real_smul]
  unfold pieceIntegral
  rw [integral_mul_const]
  by_cases hD : ((orientedPieces g n).get i).1.D=0
  · simp only [hD,norm_zero,Complex.ofReal_zero,zero_mul,mul_zero,zero_div]
  · have hnorm : (‖((orientedPieces g n).get i).1.D‖:ℂ) ≠ 0 := by
      exact_mod_cast (norm_ne_zero_iff.mpr hD)
    field_simp
    <;> ring

theorem sum_fin_get {α : Type*} (ps : List α) (f : α → ℂ) :
    (∑ i : Fin ps.length, f (ps.get i))=(ps.map f).sum := by
  rw [← List.sum_ofFn]
  have he : List.ofFn (fun i : Fin ps.length => f (ps.get i))=(List.ofFn (fun i : Fin ps.length => ps.get i)).map f := by
    rw [List.map_ofFn]
    rfl
  rw [he,List.ofFn_get]

theorem curve_source_integral {F : Frame} (g : FrameGeometry F) (z : ℝ) (hz : ValidZ z)
    (n : ℕ) (hn : 0 < n) (t : ℝ) (T : ℂ[X])
    (hΓ : ∀ u ∈ gammaN g n, 0 ≤ u.re ∧ 1/2 ≤ ‖u‖ ∧
      ((∃ N : ℕ, u.re=(N:ℝ)+1/2) ∨ 1 ≤ |u.im|)) :
    (∫ r : Fin (orientedPieces g n).length × ℝ, sourceJet g z n t (.inr (.inl r)) T
      ∂famMeasure (curveMeasure g n))=lineIntegral g n (contourDensity z n T) := by
  rw [integral_fam (curveMeasure g n) (curve_source_integrable g z hz n hn t T hΓ)]
  simp_rw [curve_integral_index]
  rw [sum_fin_get (orientedPieces g n) (fun r => r.2*pieceIntegral r.1 (contourDensity z n T))]
  have hneg (ps : List Piece) :
      (ps.map (fun q => (-1:ℂ)*pieceIntegral q (contourDensity z n T))).sum=
        -(ps.map (fun q => pieceIntegral q (contourDensity z n T))).sum := by
    induction ps with
    | nil => simp
    | cons q ps ih =>
      simp only [List.map_cons,List.sum_cons]
      rw [ih]
      ring
  cases g with
  | pure hp hl hf => simp [orientedPieces,lineIntegral]
  | polygon p hp hl hf =>
    simp only [orientedPieces,List.map_append,List.sum_append,List.map_map,Function.comp_def]
    simp only [mul_one,one_mul]
    rw [hneg]
    simp only [lineIntegral,List.map_map,Function.comp_def]
end CatalanCore.Li2.Decay.HeineSource
#print axioms CatalanCore.Li2.Decay.HeineSource.curve_source_integral


namespace CatalanCore.Li2.Decay.HeineSource
open CatalanCore.Li2.Uniform ContourGeometry

theorem lattice_source_integral {F : Frame} (g : FrameGeometry F) (z : ℝ) (hz : ValidZ z)
    (n : ℕ) (t : ℝ) (T : ℂ[X]) :
    (∫ x : LatticeIdx F n, sourceJet g z n t (.inl x) T ∂Measure.count)=
      ∑' x : LatticeIdx F n, (z:ℂ)^x.val*deriv (rationalCore n T) (x.val:ℂ) := by
  have hh := integral_countable (lattice_source_integrable g z hz n t T)
  simpa only [count_real_singleton,one_smul,sourceJet_lattice_deriv] using hh

theorem lattice_source_polygon {F : Frame} (g : FrameGeometry F) (p : PolygonFrame)
    (hl : F.lattice=Icc 0 p.cut) (z : ℝ) (hz : ValidZ z)
    (n : ℕ) (hn : 0 < n) (t : ℝ) (T : ℂ[X]) :
    (∫ x : LatticeIdx F n, sourceJet g z n t (.inl x) T ∂Measure.count)=
      ∑ x ∈ Finset.Icc 1 (Nat.floor (p.cut*n)), (z:ℂ)^x*deriv (rationalCore n T) (x:ℂ) := by
  let e : LatticeIdx F n ≃ {x : ℕ // x ∈ Finset.Icc 1 (Nat.floor (p.cut*n))} :=
    Equiv.subtypeEquivRight (fun x => by
      change (1 ≤ x ∧ (x:ℝ)/(n:ℝ) ∈ F.lattice) ↔ _
      rw [hl]
      exact lattice_idx_polygon_iff p n hn x)
  have he : (∑' x : LatticeIdx F n, (z:ℂ)^x.val*deriv (rationalCore n T) (x.val:ℂ))=
      ∑' x : {x : ℕ // x ∈ Finset.Icc 1 (Nat.floor (p.cut*n))},
        (z:ℂ)^x.val*deriv (rationalCore n T) (x.val:ℂ) := e.tsum_eq (fun x : {x : ℕ // x ∈ Finset.Icc 1 (Nat.floor (p.cut*n))} =>
          (z:ℂ)^x.val*deriv (rationalCore n T) (x.val:ℂ))
  rw [lattice_source_integral g z hz n t T,he]
  exact Finset.tsum_subtype (Finset.Icc 1 (Nat.floor (p.cut*n)))
    (fun x : ℕ => (z:ℂ)^x*deriv (rationalCore n T) (x:ℂ))

theorem lattice_source_pure {F : Frame} (g : FrameGeometry F) (hl : F.lattice=Ici 0)
    (z : ℝ) (hz : ValidZ z) (n : ℕ) (t : ℝ) (T : ℂ[X]) :
    (∫ x : LatticeIdx F n, sourceJet g z n t (.inl x) T ∂Measure.count)=
      ∑' k : ℕ, (z:ℂ)^(k+1)*deriv (rationalCore n T) ((k+1:ℕ):ℂ) := by
  let e : ℕ ≃ LatticeIdx F n :=
    { toFun := fun k => ⟨k+1,by
        refine ⟨by omega,?_⟩
        rw [hl]
        exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)⟩
      invFun := fun x => x.val-1
      left_inv := fun k => by simp
      right_inv := fun x => by apply Subtype.ext; have hh := x.property.1; dsimp; omega }
  have he := e.tsum_eq (fun x : LatticeIdx F n => (z:ℂ)^x.val*deriv (rationalCore n T) (x.val:ℂ))
  rw [lattice_source_integral g z hz n t T]
  exact he.symm

theorem atom_source_integral {F : Frame} (g : FrameGeometry F) (z : ℝ)
    (n : ℕ) (t : ℝ) (T : ℂ[X]) :
    (∫ j : AtomIdx n, sourceJet g z n t (.inr (.inr (.inr j))) T ∂Measure.count)=
      (t:ℂ)*∑ j ∈ Finset.Icc (n+1) (4*n), (atomWeight z n j:ℂ)*T.eval (-(j:ℂ)) := by
  rw [integral_count]
  simp only [sourceJet,LinearMap.smul_apply,Polynomial.leval_apply,smul_eq_mul,mul_assoc]
  rw [← Finset.mul_sum]
  congr 1
  have hh := Finset.tsum_subtype (Finset.Icc (n+1) (4*n))
    (fun j : ℕ => (atomWeight z n j:ℂ)*T.eval (-(j:ℂ)))
  rw [tsum_fintype] at hh
  exact hh

theorem sourceJet_ray_apply {F : Frame} (g : FrameGeometry F) (z : ℝ)
    (n : ℕ) (t x : ℝ) (T : ℂ[X]) :
    sourceJet g z n t (.inr (.inr (.inl x))) T=-(Real.log |z|:ℂ)*realDensity z n T x := by
  simp only [sourceJet,LinearMap.smul_apply,Polynomial.leval_apply,smul_eq_mul]
  unfold rayDensity realDensity rationalCore
  ring
end CatalanCore.Li2.Decay.HeineSource
#print axioms CatalanCore.Li2.Decay.HeineSource.lattice_source_polygon
#print axioms CatalanCore.Li2.Decay.HeineSource.lattice_source_pure
#print axioms CatalanCore.Li2.Decay.HeineSource.atom_source_integral


namespace CatalanCore.Li2.Decay.HeineSource
open CatalanCore.Li2.Uniform CatalanCore.Decay.CurveFamily ContourGeometry
open CatalanLambda.Decay (sumM integrable_sumM_iff integral_sumM)

def SourceHeight {F : Frame} (g : FrameGeometry F) (n : ℕ) : Prop :=
  match g with
  | .pure _ _ _ => True
  | .polygon p _ _ _ => 1 ≤ (n:ℝ)*(p.vertex 1).im

theorem source_integral_parts {F : Frame} (g : FrameGeometry F) (z : ℝ) (hz : ValidZ z)
    (n : ℕ) (hn : 0 < n) (t : ℝ) (T : ℂ[X])
    (hΓ : ∀ u ∈ gammaN g n, 0 ≤ u.re ∧ 1/2 ≤ ‖u‖ ∧
      ((∃ N : ℕ, u.re=(N:ℝ)+1/2) ∨ 1 ≤ |u.im|)) :
    (∫ r : SourceSpace g n, sourceJet g z n t r T ∂sourceMeasure g z n)=
      (∫ x : LatticeIdx F n, sourceJet g z n t (.inl x) T ∂Measure.count)+
      (lineIntegral g n (contourDensity z n T)+
      ((∫ x : ℝ, sourceJet g z n t (.inr (.inr (.inl x))) T ∂rayMeasure g z n)+
        (t:ℂ)*∑ j ∈ Finset.Icc (n+1) (4*n), (atomWeight z n j:ℂ)*T.eval (-(j:ℂ)))) := by
  have hR := ray_source_integrable g z hz n t T
  have hA := atom_source_integrable g z n t T
  have hC := curve_source_integrable g z hz n hn t T hΓ
  have hRA : Integrable (fun r : ℝ ⊕ AtomIdx n => sourceJet g z n t (.inr (.inr r)) T)
      (sumM (rayMeasure g z n) (Measure.count : Measure (AtomIdx n))) :=
    (integrable_sumM_iff _ _ _).mpr ⟨hR,hA⟩
  have hCA : Integrable (fun r : (Fin (orientedPieces g n).length × ℝ) ⊕ (ℝ ⊕ AtomIdx n) =>
      sourceJet g z n t (.inr r) T)
      (sumM (famMeasure (curveMeasure g n)) (sumM (rayMeasure g z n) (Measure.count : Measure (AtomIdx n)))) :=
    (integrable_sumM_iff _ _ _).mpr ⟨hC,hRA⟩
  have hAll := source_integrable g z hz n hn t T hΓ
  unfold sourceMeasure
  rw [integral_sumM _ _ _ hAll,integral_sumM _ _ _ hCA,integral_sumM _ _ _ hRA,
    curve_source_integral g z hz n hn t T hΓ,atom_source_integral g z n t T]

theorem source_integral_functional {F : Frame} (g : FrameGeometry F) (z : ℝ) (hz : ValidZ z)
    (n : ℕ) (hn : 0 < n) (t : ℝ) (T : ℂ[X]) (hH : SourceHeight g n)
    (hΓ : ∀ u ∈ gammaN g n, 0 ≤ u.re ∧ 1/2 ≤ ‖u‖ ∧
      ((∃ N : ℕ, u.re=(N:ℝ)+1/2) ∨ 1 ≤ |u.im|)) :
    (∫ r : SourceSpace g n, sourceJet g z n t r T ∂sourceMeasure g z n)=functional z n t T := by
  rw [source_integral_parts g z hz n hn t T hΓ]
  cases g with
  | pure hp hl hf =>
    rw [lattice_source_pure (FrameGeometry.pure hp hl hf) hl z hz n t T]
    simp only [lineIntegral,rayMeasure,integral_zero_measure,zero_add,add_zero]
    have hfun : rationalCore n T=(fun u : ℂ => u*weight n u*T.eval u) := funext fun _ => rfl
    unfold functional
    rw [hfun]
  | polygon p hp hl hf =>
    rw [lattice_source_polygon (FrameGeometry.polygon p hp hl hf) p hl z hz n hn t T]
    have hRay : (∫ x : ℝ, sourceJet (FrameGeometry.polygon p hp hl hf) z n t (.inr (.inr (.inl x))) T
        ∂rayMeasure (FrameGeometry.polygon p hp hl hf) z n)=
        if 0 < z then -(Real.log |z|:ℂ)*realTail z n T (Nat.floor (p.cut*n)) else 0 := by
      simp_rw [sourceJet_ray_apply]
      unfold rayMeasure
      split_ifs with hpos
      · rw [integral_const_mul]
        rfl
      · simp
    rw [hRay,functional_head_tail z hz n (Nat.floor (p.cut*n)) t T]
    have hcomb : lineIntegral (FrameGeometry.polygon p hp hl hf) n (contourDensity z n T)+
        (if 0 < z then -(Real.log |z|:ℂ)*realTail z n T (Nat.floor (p.cut*n)) else 0)=
        latticeTail z n (Nat.floor (p.cut*n)) T := by
      rw [contourDensity_eq,lineIntegral_const_mul,latticeTail_eq_correctedLine z hz]
      change ((2*Real.pi:ℂ)*Complex.I)⁻¹*
        (-((upperModified p n).map (fun q => pieceIntegral q (densityCore z n T))).sum+
          (((upperModified p n).map Piece.conj).map (fun q => pieceIntegral q (densityCore z n T))).sum)+
          (if 0 < z then -(Real.log |z|:ℂ)*realTail z n T (Nat.floor (p.cut*n)) else 0)=_
      rw [polygon_line_straight z hz p n T hn hH]
      simp only [correctedLine]
      ring
    rw [← hcomb]
    ring
end CatalanCore.Li2.Decay.HeineSource
#print axioms CatalanCore.Li2.Decay.HeineSource.source_integral_functional


namespace CatalanCore.Li2.Decay.HeineSource
open CatalanCore.Li2.Uniform ContourGeometry

noncomputable def sourceFunctional {F : Frame} (g : FrameGeometry F) (z : ℝ) (hz : ValidZ z)
    (n : ℕ) (hn : 0 < n) (t : ℝ)
    (hΓ : ∀ u ∈ gammaN g n, 0 ≤ u.re ∧ 1/2 ≤ ‖u‖ ∧
      ((∃ N : ℕ, u.re=(N:ℝ)+1/2) ∨ 1 ≤ |u.im|)) : ℂ[X] →ₗ[ℂ] ℂ where
  toFun T := ∫ r : SourceSpace g n, sourceJet g z n t r T ∂sourceMeasure g z n
  map_add' P Q := by
    have he : (fun r : SourceSpace g n => sourceJet g z n t r (P+Q))=
        fun r => sourceJet g z n t r P+sourceJet g z n t r Q :=
      funext fun r => (sourceJet g z n t r).map_add P Q
    rw [he,integral_add (source_integrable g z hz n hn t P hΓ) (source_integrable g z hz n hn t Q hΓ)]
  map_smul' c P := by
    have he : (fun r : SourceSpace g n => sourceJet g z n t r (c • P))=
        fun r => c*sourceJet g z n t r P := by
      funext r
      rw [map_smul,smul_eq_mul]
    rw [he,integral_const_mul] <;> rfl

theorem sourceFunctional_eq {F : Frame} (g : FrameGeometry F) (z : ℝ) (hz : ValidZ z)
    (n : ℕ) (hn : 0 < n) (t : ℝ) (hH : SourceHeight g n)
    (hΓ : ∀ u ∈ gammaN g n, 0 ≤ u.re ∧ 1/2 ≤ ‖u‖ ∧
      ((∃ N : ℕ, u.re=(N:ℝ)+1/2) ∨ 1 ≤ |u.im|)) (T : ℂ[X]) :
    sourceFunctional g z hz n hn t hΓ T=functional z n t T :=
  source_integral_functional g z hz n hn t T hH hΓ

theorem source_eventually {F : Frame} (g : FrameGeometry F) :
    ∀ᶠ n : ℕ in atTop, 0 < n ∧ SourceHeight g n ∧
      ∀ u ∈ gammaN g n, 0 ≤ u.re ∧ 1/2 ≤ ‖u‖ ∧
        ((∃ N : ℕ, u.re=(N:ℝ)+1/2) ∨ 1 ≤ |u.im|) := by
  cases g with
  | pure hp hl hf =>
    filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
    refine ⟨by omega,trivial,?_⟩
    simp [gammaN]
  | polygon p hp hl hf =>
    filter_upwards [eventually_ge_atTop (1:ℕ),eventual_height p,
      gammaN_kernel_domain F (FrameGeometry.polygon p hp hl hf)] with n hn hh hΓ
    exact ⟨by omega,hh,hΓ⟩

theorem heine_source {F : Frame} (g : FrameGeometry F) (z : ℝ) (hz : ValidZ z)
    (n : ℕ) (hn : 0 < n) (t : ℝ) (hH : SourceHeight g n)
    (hΓ : ∀ u ∈ gammaN g n, 0 ≤ u.re ∧ 1/2 ≤ ‖u‖ ∧
      ((∃ N : ℕ, u.re=(N:ℝ)+1/2) ∨ 1 ≤ |u.im|)) :
    Matrix.det (fun i j : Fin (2*n) => functional z n t (Polynomial.X^(i.val+j.val)))=
      ((2*n).factorial:ℂ)⁻¹*∫ r : Fin (2*n) → SourceSpace g n,
        CatalanCore.Tools.IntegratedJets.tensorIntegrand (2*n) (sourceJet g z n t)
          (CatalanCore.Tools.Jets.vandSq (2*n)) r
        ∂Measure.pi (fun _ : Fin (2*n) => sourceMeasure g z n) := by
  have hh := CatalanCore.Tools.IntegratedJets.heine_integral (sourceMeasure g z n) (2*n)
    (sourceFunctional g z hz n hn t hΓ) (sourceJet g z n t)
    (fun k => source_integrable g z hz n hn t (Polynomial.X^k) hΓ) (fun k => rfl)
  simpa only [sourceFunctional_eq g z hz n hn t hH hΓ] using hh
end CatalanCore.Li2.Decay.HeineSource
#print axioms CatalanCore.Li2.Decay.HeineSource.heine_source


namespace CatalanCore.Li2.Decay.HeineSource
open CatalanCore.Li2.Uniform CatalanCore.Tools.Jets

noncomputable def sourceA {F : Frame} (g : FrameGeometry F) (z : ℝ) (n : ℕ) (r : SourceSpace g n) : ℂ :=
  match sourceParticle g n r with | .lattice x => latticeA z n x | _ => 0
noncomputable def sourceB {F : Frame} (g : FrameGeometry F) (z : ℝ) (n : ℕ) (r : SourceSpace g n) : ℂ :=
  match sourceParticle g n r with | .lattice x => latticeB z n x | _ => 0
noncomputable def sourceAmp {F : Frame} (g : FrameGeometry F) (z : ℝ) (n : ℕ) (t : ℝ) : SourceSpace g n → ℂ
  | .inl _ => 1
  | .inr (.inl r) =>
      let q := ((orientedPieces g n).get r.1).1
      let s := ((orientedPieces g n).get r.1).2
      s*(q.D/(‖q.D‖:ℂ))*contourDensity z n 1 (q.zeta r.2)
  | .inr (.inr (.inl x)) => rayDensity z n (x:ℂ)
  | .inr (.inr (.inr j)) => (t*atomWeight z n j.val:ℂ)

noncomputable def sourcePhase {F : Frame} (g : FrameGeometry F) (n : ℕ) : SourceSpace g n → ℂ
  | .inr (.inl r) =>
      let q := ((orientedPieces g n).get r.1).1
      let s := ((orientedPieces g n).get r.1).2
      s*(q.D/(‖q.D‖:ℂ))
  | _ => 1

theorem sourceJet_monomial {F : Frame} (g : FrameGeometry F) (z : ℝ) (n : ℕ) (t : ℝ)
    (r : SourceSpace g n) (k : ℕ) :
    sourceJet g z n t r (Polynomial.X^k)=sourceAmp g z n t r*
      (if isLattice (sourceParticle g n r) then
        sourceA g z n r*(sourceParticle g n r).point^k+
          sourceB g z n r*(k:ℂ)*(sourceParticle g n r).point^(k-1)
       else (sourceParticle g n r).point^k) := by
  rcases r with x|r
  · simp [sourceJet,sourceAmp,sourceParticle,sourceA,sourceB,isLattice,Particle.point,
      Polynomial.leval,Polynomial.derivative_X_pow,smul_eq_mul,mul_assoc]
  · rcases r with r|r
    · simp [sourceJet,sourceAmp,sourceParticle,isLattice,Particle.point,Polynomial.leval,smul_eq_mul]
    · rcases r with x|j <;>
        simp [sourceJet,sourceAmp,sourceParticle,isLattice,Particle.point,Polynomial.leval,smul_eq_mul]

theorem tensorIntegrand_mixedJet {F : Frame} (g : FrameGeometry F) (z : ℝ) (n M : ℕ) (t : ℝ)
    (r : Fin M → SourceSpace g n) (P : MvPolynomial (Fin M) ℂ) :
    CatalanCore.Tools.IntegratedJets.tensorIntegrand M (sourceJet g z n t) P r=
      mixedJet (Finset.univ.filter (fun i => isLattice (sourceParticle g n (r i))))
        (fun i => sourceA g z n (r i)) (fun i => sourceB g z n (r i))
        (fun i => (sourceParticle g n (r i)).point) P * ∏ i : Fin M, sourceAmp g z n t (r i) := by
  classical
  rw [CatalanCore.Tools.IntegratedJets.mixedJet_expansion,Finset.sum_mul]
  unfold CatalanCore.Tools.IntegratedJets.tensorIntegrand
  apply Finset.sum_congr rfl
  intro d hd
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  simp_rw [sourceJet_monomial,Finset.prod_mul_distrib]
  ring
end CatalanCore.Li2.Decay.HeineSource
#print axioms CatalanCore.Li2.Decay.HeineSource.tensorIntegrand_mixedJet


namespace CatalanCore.Li2.Decay.HeineSource
open CatalanCore.Li2.Uniform CatalanCore.Decay.CurveFamily CatalanCore.Tools.Jets

theorem oriented_sign_norm {F : Frame} (g : FrameGeometry F) (n : ℕ) (r : Piece × ℂ)
    (hr : r ∈ orientedPieces g n) : ‖r.2‖=1 := by
  cases g with
  | pure hp hl hf => simp [orientedPieces] at hr
  | polygon p hp hl hf =>
    simp only [orientedPieces,List.mem_append,List.mem_map] at hr
    rcases hr with ⟨q,hq,rfl⟩|⟨q,hq,rfl⟩ <;> norm_num

theorem sourcePhase_norm_le {F : Frame} (g : FrameGeometry F) (n : ℕ) (r : SourceSpace g n) :
    ‖sourcePhase g n r‖ ≤ 1 := by
  rcases r with x|r
  · simp [sourcePhase]
  · rcases r with r|r
    · have hh := oriented_sign_norm g n ((orientedPieces g n).get r.1) (List.get_mem _ _)
      simp only [sourcePhase,norm_mul,norm_div,Complex.norm_real,Real.norm_eq_abs,
        abs_of_nonneg (norm_nonneg _),hh,one_mul]
      by_cases hn : ‖((orientedPieces g n).get r.1).1.D‖=0
      · rw [hn,zero_div]
        norm_num
      · rw [div_self hn]
    · rcases r with x|j <;> simp [sourcePhase]

noncomputable def particleAmp (z : ℝ) (n : ℕ) (t : ℝ) : Particle → ℂ
  | .lattice _ => 1
  | .contour u => contourDensity z n 1 u
  | .ray x => rayDensity z n (x:ℂ)
  | .atom j => (t*atomWeight z n j:ℂ)

theorem sourceAmp_factor {F : Frame} (g : FrameGeometry F) (z : ℝ) (n : ℕ) (t : ℝ) (r : SourceSpace g n) :
    sourceAmp g z n t r=sourcePhase g n r*particleAmp z n t (sourceParticle g n r) := by
  rcases r with x|r
  · simp [sourceAmp,sourcePhase,particleAmp,sourceParticle]
  · rcases r with r|r
    · rfl
    · rcases r with x|j <;> simp [sourceAmp,sourcePhase,particleAmp,sourceParticle]

theorem tensorIntegrand_config {F : Frame} (g : FrameGeometry F) (z : ℝ) (n : ℕ) (t : ℝ)
    (r : Fin (2*n) → SourceSpace g n) (c : AdmissibleConfig F g z n)
    (hc : ∀ i, c.particle i=sourceParticle g n (r i)) :
    CatalanCore.Tools.IntegratedJets.tensorIntegrand (2*n) (sourceJet g z n t)
      (vandSq (2*n)) r=(∏ i : Fin (2*n), sourcePhase g n (r i))*configWeight z n t c := by
  have hCW : configWeight z n t c=
      mixedJet (Finset.univ.filter (fun i => isLattice (sourceParticle g n (r i))))
        (fun i => sourceA g z n (r i)) (fun i => sourceB g z n (r i))
        (fun i => (sourceParticle g n (r i)).point) (vandSq (2*n))*
          ∏ i : Fin (2*n), particleAmp z n t (sourceParticle g n (r i)) := by
    unfold configWeight AdmissibleConfig.Jlat
    simp_rw [hc]
    refine congrArg₂ (fun A B : ℂ => A*B) ?_ ?_
    · rfl
    · apply Finset.prod_congr rfl
      intro i hi
      cases hp : sourceParticle g n (r i) <;> rfl
  have hprod : (∏ i : Fin (2*n), sourceAmp g z n t (r i))=
      (∏ i : Fin (2*n), sourcePhase g n (r i))*(∏ i : Fin (2*n), particleAmp z n t (sourceParticle g n (r i))) := by
    simp_rw [sourceAmp_factor]
    rw [Finset.prod_mul_distrib]
  rw [hCW,tensorIntegrand_mixedJet,hprod]
  generalize mixedJet (Finset.univ.filter (fun i => isLattice (sourceParticle g n (r i))))
    (fun i => sourceA g z n (r i)) (fun i => sourceB g z n (r i))
    (fun i => (sourceParticle g n (r i)).point) (vandSq (2*n))=V
  generalize (∏ i : Fin (2*n), sourcePhase g n (r i))=B
  generalize (∏ i : Fin (2*n), particleAmp z n t (sourceParticle g n (r i)))=A
  ring

theorem tensorIntegrand_config_norm {F : Frame} (g : FrameGeometry F) (z : ℝ) (n : ℕ) (t : ℝ)
    (r : Fin (2*n) → SourceSpace g n) (c : AdmissibleConfig F g z n)
    (hc : ∀ i, c.particle i=sourceParticle g n (r i)) :
    ‖CatalanCore.Tools.IntegratedJets.tensorIntegrand (2*n) (sourceJet g z n t)
      (vandSq (2*n)) r‖ ≤ ‖configWeight z n t c‖ := by
  rw [tensorIntegrand_config g z n t r c hc,norm_mul]
  have hp : ‖∏ i : Fin (2*n), sourcePhase g n (r i)‖ ≤ 1 := by
    rw [norm_prod]
    exact Finset.prod_le_one₀ (fun i hi => norm_nonneg _) (fun i hi => sourcePhase_norm_le g n (r i))
  exact (mul_le_mul_of_nonneg_right hp (norm_nonneg _)).trans_eq (one_mul _)
end CatalanCore.Li2.Decay.HeineSource
#print axioms CatalanCore.Li2.Decay.HeineSource.tensorIntegrand_config_norm


namespace CatalanCore.Li2.Decay.HeineSource
open CatalanCore.Li2.Uniform CatalanCore.Decay.CurveFamily
open CatalanLambda.Decay (sumM meInl meInr)

def ParticleAllowed (F : Frame) (g : FrameGeometry F) (z : ℝ) (n : ℕ) : Particle → Prop
  | .lattice x => 1 ≤ x ∧ (x:ℝ)/(n:ℝ) ∈ F.lattice
  | .contour u => u ∈ gammaN g n
  | .ray x => 0 < z ∧ ∃ c : ℝ, frameCut g=some c ∧ (Nat.floor (c*n):ℝ)+1/2 ≤ x
  | .atom j => j ∈ Finset.Icc (n+1) (4*n)

theorem source_ae_iff {F : Frame} (g : FrameGeometry F) (z : ℝ) (n : ℕ) (P : SourceSpace g n → Prop) :
    (∀ᵐ r ∂sourceMeasure g z n, P r) ↔
      (∀ᵐ x ∂(Measure.count : Measure (LatticeIdx F n)), P (.inl x)) ∧
      (∀ᵐ r ∂famMeasure (curveMeasure g n), P (.inr (.inl r))) ∧
      (∀ᵐ x ∂rayMeasure g z n, P (.inr (.inr (.inl x)))) ∧
      (∀ᵐ j ∂(Measure.count : Measure (AtomIdx n)), P (.inr (.inr (.inr j)))) := by
  unfold sourceMeasure
  rw [sumM,ae_add_measure_iff,
    (meInl (LatticeIdx F n) ((Fin (orientedPieces g n).length × ℝ) ⊕ (ℝ ⊕ AtomIdx n))).ae_map_iff,
    (meInr (LatticeIdx F n) ((Fin (orientedPieces g n).length × ℝ) ⊕ (ℝ ⊕ AtomIdx n))).ae_map_iff]
  rw [sumM,ae_add_measure_iff,
    (meInl (Fin (orientedPieces g n).length × ℝ) (ℝ ⊕ AtomIdx n)).ae_map_iff,
    (meInr (Fin (orientedPieces g n).length × ℝ) (ℝ ⊕ AtomIdx n)).ae_map_iff]
  rw [sumM,ae_add_measure_iff,(meInl ℝ (AtomIdx n)).ae_map_iff,(meInr ℝ (AtomIdx n)).ae_map_iff]

theorem source_allowed_ae {F : Frame} (g : FrameGeometry F) (z : ℝ) (n : ℕ) :
    ∀ᵐ r ∂sourceMeasure g z n, ParticleAllowed F g z n (sourceParticle g n r) := by
  rw [source_ae_iff]
  refine ⟨Filter.Eventually.of_forall (fun x => x.property),?_,?_,
    Filter.Eventually.of_forall (fun j => j.property)⟩
  · unfold famMeasure
    rw [Measure.ae_sum_iff]
    intro i
    apply (measurableEmbedding_prodMk_left i).ae_map_iff.mpr
    dsimp only [curveMeasure]
    apply Measure.ae_smul_measure
    filter_upwards [piece_ae_in_set ((orientedPieces g n).get i).1] with y hy
    exact oriented_piece_in_gamma g n ((orientedPieces g n).get i) (List.get_mem _ _) _ hy
  · cases g with
    | pure hp hl hf => simp [rayMeasure]
    | polygon p hp hl hf =>
      by_cases hpos : 0 < z
      · simp only [rayMeasure,if_pos hpos]
        filter_upwards [ae_restrict_mem measurableSet_Ici] with x hx
        exact ⟨hpos,p.cut,rfl,hx⟩
      · simp [rayMeasure,hpos]

theorem source_allowed_pi_ae {F : Frame} (g : FrameGeometry F) (z : ℝ) (n M : ℕ) :
    ∀ᵐ r : Fin M → SourceSpace g n ∂Measure.pi (fun _ : Fin M => sourceMeasure g z n),
      ∀ i : Fin M, ParticleAllowed F g z n (sourceParticle g n (r i)) := by
  rw [ae_all_iff]
  intro i
  exact (Measure.quasiMeasurePreserving_eval (fun _ : Fin M => sourceMeasure g z n) i).ae
    (source_allowed_ae g z n)
end CatalanCore.Li2.Decay.HeineSource
#print axioms CatalanCore.Li2.Decay.HeineSource.source_allowed_pi_ae


namespace CatalanCore.Li2.Decay.HeineSource
open CatalanCore.Li2.Uniform CatalanCore.Tools.Jets CatalanCore.Tools.JetConfigurations

theorem lattice_pair_of_point_eq (p q : Particle) (hp : isLattice p=true) (hq : isLattice q=true)
    (he : p.point=q.point) : ∃ x : ℕ, p=.lattice x ∧ q=.lattice x := by
  cases p <;> cases q <;> simp_all [isLattice,Particle.point]

theorem admissible_of_mixedJet_ne_zero {F : Frame} (g : FrameGeometry F) (z : ℝ) (n : ℕ) (hn : 0 < n)
    (p : Fin (2*n) → Particle) (a b : Fin (2*n) → ℂ)
    (hallow : ∀ i, ParticleAllowed F g z n (p i))
    (hjet : mixedJet (Finset.univ.filter (fun i => isLattice (p i))) a b (fun i => (p i).point) (vandSq (2*n)) ≠ 0) :
    ∃ c : AdmissibleConfig F g z n, ∀ i, c.particle i=p i := by
  classical
  let J : Finset (Fin (2*n)) := Finset.univ.filter (fun i => isLattice (p i))
  have hnC : (n:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hn)
  have hphysical (i j : Fin (2*n)) (he : (p i).point/(n:ℂ)=(p j).point/(n:ℂ)) :
      (p i).point=(p j).point := by
    have hh := congrArg (fun u : ℂ => u*(n:ℂ)) he
    simpa only [div_mul_cancel₀ _ hnC] using hh
  have hpair (i j : Fin (2*n)) (hij : i≠j) (he : (p i).point=(p j).point) : i∈J ∧ j∈J := by
    by_contra hh
    have hnJ : i∉J ∨ j∉J := not_and_or.mp hh
    exact hjet (mixedJet_pair_zero (2*n) J a b (fun i => (p i).point) i j hij he hnJ)
  have hcap : ∀ u : ℂ, (Finset.univ.filter (fun i : Fin (2*n) => (p i).point/(n:ℂ)=u)).card≤2 := by
    intro u
    by_contra hc
    obtain ⟨i,j,k,hi,hj,hk,hij,hik,hjk⟩ := Finset.two_lt_card_iff.mp (lt_of_not_ge hc)
    have hijx := hphysical i j ((Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm)
    have hikx := hphysical i k ((Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hk).2.symm)
    exact hjet (mixedJet_triple_zero (2*n) J a b (fun i => (p i).point) i j k hij hik hjk hijx hikx)
  obtain ⟨cf,hcf⟩ := exists_confluent (2*n) (fun i => (p i).point/(n:ℂ)) hcap
  have hAtom : ∀ j : ℕ, (Finset.univ.filter (fun i => p i=.atom j)).card≤1 := by
    intro j
    apply Finset.card_le_one.mpr
    intro i hi k hk
    by_contra hik
    have hpi := (Finset.mem_filter.mp hi).2
    have hpk := (Finset.mem_filter.mp hk).2
    have he : (p i).point=(p k).point := by rw [hpi,hpk]
    have h := (hpair i k hik he).1
    change i ∈ Finset.univ.filter (fun i => isLattice (p i)) at h
    have hiLat := (Finset.mem_filter.mp h).2
    simpa only [hpi,isLattice,Bool.false_eq_true] using hiLat
  have hpaired : ∀ i j, cf.paired i j → ∃ x, p i=.lattice x ∧ p j=.lattice x := by
    intro i j hij
    have hne : i≠j := by
      rcases hij with hh|hh
      · exact ne_of_lt (cf.ordered (i,j) hh)
      · exact (ne_of_lt (cf.ordered (j,i) hh)).symm
    have he := (cf.diagonal i j hne).mpr hij
    rw [hcf] at he
    have hphys := hphysical i j he
    have h := hpair i j hne hphys
    have hiLat : isLattice (p i)=true := (Finset.mem_filter.mp h.1).2
    have hjLat : isLattice (p j)=true := (Finset.mem_filter.mp h.2).2
    exact lattice_pair_of_point_eq (p i) (p j) hiLat hjLat hphys
  refine ⟨{ particle := p
            lattice_sites := ?_
            contour_points := ?_
            ray_points := ?_
            atom_sites := ?_
            atom_cap := hAtom
            confluence := cf
            positions := ?_
            paired_lattice := hpaired },fun i => rfl⟩
  · intro i x he
    have hh := hallow i
    simpa only [he,ParticleAllowed] using hh
  · intro i u he
    have hh := hallow i
    simpa only [he,ParticleAllowed] using hh
  · intro i x he
    have hh := hallow i
    simpa only [he,ParticleAllowed] using hh
  · intro i j he
    have hh := hallow i
    simpa only [he,ParticleAllowed] using hh
  · intro i
    exact congrArg (fun f : Fin (2*n) → ℂ => f i) hcf

theorem source_config_or_zero {F : Frame} (g : FrameGeometry F) (z : ℝ) (n : ℕ) (hn : 0 < n) (t : ℝ)
    (r : Fin (2*n) → SourceSpace g n)
    (hallow : ∀ i, ParticleAllowed F g z n (sourceParticle g n (r i))) :
    CatalanCore.Tools.IntegratedJets.tensorIntegrand (2*n) (sourceJet g z n t) (vandSq (2*n)) r=0 ∨
      ∃ c : AdmissibleConfig F g z n, ∀ i, c.particle i=sourceParticle g n (r i) := by
  classical
  by_cases hj : mixedJet (Finset.univ.filter (fun i => isLattice (sourceParticle g n (r i))))
      (fun i => sourceA g z n (r i)) (fun i => sourceB g z n (r i))
      (fun i => (sourceParticle g n (r i)).point) (vandSq (2*n))=0
  · left
    rw [tensorIntegrand_mixedJet,hj,zero_mul]
  · right
    exact admissible_of_mixedJet_ne_zero g z n hn (fun i => sourceParticle g n (r i))
      (fun i => sourceA g z n (r i)) (fun i => sourceB g z n (r i)) hallow hj
end CatalanCore.Li2.Decay.HeineSource
#print axioms CatalanCore.Li2.Decay.HeineSource.source_config_or_zero


namespace CatalanCore.Li2.Decay.HeineSource
open CatalanCore.Li2.Uniform

noncomputable def tailProfile (z : ℝ) (d : DualDatum) (θ : ℝ) (K : ℕ) (u : ℂ) : ℝ :=
  Real.exp (W z d.σ u-θ)*(1+‖u‖)^K

noncomputable def sourceTail {F : Frame} (g : FrameGeometry F) (z : ℝ) (n : ℕ)
    (d : DualDatum) (θ : ℝ) (K : ℕ) (r : SourceSpace g n) : ℝ :=
  if isAtom (sourceParticle g n r) then 1 else tailProfile z d θ K ((sourceParticle g n r).point/(n:ℂ))

theorem tailProfile_nonneg (z : ℝ) (d : DualDatum) (θ : ℝ) (K : ℕ) (u : ℂ) :
    0 ≤ tailProfile z d θ K u := by unfold tailProfile; positivity

theorem tailProfile_measurable (z : ℝ) (d : DualDatum) (θ : ℝ) (K : ℕ) : Measurable (tailProfile z d θ K) := by
  have hW := measurable_W z d
  unfold tailProfile
  fun_prop

theorem sourceTail_nonneg {F : Frame} (g : FrameGeometry F) (z : ℝ) (n : ℕ)
    (d : DualDatum) (θ : ℝ) (K : ℕ) (r : SourceSpace g n) :
    0 ≤ sourceTail g z n d θ K r := by
  unfold sourceTail
  split_ifs
  · norm_num
  · exact tailProfile_nonneg z d θ K _

theorem lattice_tail_mass (z : ℝ) (hz : ValidZ z) (d : DualDatum) (θ : ℝ) (K : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : Frame) (n : ℕ), 0 < n →
      Integrable (fun x : LatticeIdx F n => tailProfile z d θ K ((x.val:ℂ)/(n:ℂ))) Measure.count ∧
      (∫ x : LatticeIdx F n, tailProfile z d θ K ((x.val:ℂ)/(n:ℂ)) ∂Measure.count) ≤ C*(n:ℝ) := by
  obtain ⟨C,hC,hall⟩ := tail_lattice_sum z hz d θ K
  obtain ⟨M,a,hM,ha,hbound⟩ := field_envelope z hz d θ K
  refine ⟨C,hC,?_⟩
  intro F n hn
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  let f : ℕ → ℝ := fun x => tailProfile z d θ K (((x+1:ℕ):ℂ)/(n:ℂ))
  have hnorm (x : ℕ) : ‖((x+1:ℕ):ℂ)/(n:ℂ)‖=((x+1:ℕ):ℝ)/(n:ℝ) := by
    rw [norm_div,Complex.norm_natCast,Complex.norm_natCast]
  have hle (x : ℕ) : f x ≤ M*Real.exp (-a*(((x+1:ℕ):ℝ)/(n:ℝ))) := by
    have hh := hbound (((x+1:ℕ):ℂ)/(n:ℂ)) (by
      simp only [← Complex.ofReal_natCast,Complex.div_ofReal_re,Complex.ofReal_re]
      positivity)
    simpa only [f,tailProfile,hnorm] using hh
  have hsMaj := (geometric_sample M a hM.le ha n hn).1
  have hs : Summable f := Summable.of_nonneg_of_le (fun x => tailProfile_nonneg z d θ K _) hle hsMaj
  have hmass : (∑' x : ℕ, f x) ≤ C*(n:ℝ) := by
    simpa only [f,tailProfile,hnorm] using hall n hn
  let ι : LatticeIdx F n → ℕ := fun x => x.val-1
  have hinj : Function.Injective ι := by
    intro x y he
    apply Subtype.ext
    have hx := x.property.1
    have hy := y.property.1
    dsimp only [ι] at he
    omega
  have hsub : Summable (fun x : LatticeIdx F n => f (ι x)) := hs.comp_injective hinj
  have hfn : (fun x : LatticeIdx F n => tailProfile z d θ K ((x.val:ℂ)/(n:ℂ)))=
      fun x => f (ι x) := by
    funext x
    dsimp only [f,ι]
    rw [Nat.sub_add_cancel x.property.1]
  have hi : Integrable (fun x : LatticeIdx F n => f (ι x)) Measure.count :=
    integrable_count_iff.mpr hsub.norm
  refine ⟨by rw [hfn]; exact hi,?_⟩
  rw [hfn]
  have hh := integral_countable hi
  simp only [count_real_singleton,one_smul] at hh
  rw [hh]
  have hnonneg (x : ℕ) : 0 ≤ f x := tailProfile_nonneg z d θ K (((x+1:ℕ):ℂ)/(n:ℂ))
  have hb : (∑' x : LatticeIdx F n, f (ι x)) ≤ ∑' x : ℕ, f x :=
    Summable.tsum_le_tsum_of_inj (f := fun x : LatticeIdx F n => f (ι x)) (g := f)
      ι hinj (fun x hx => hnonneg x) (fun x => le_rfl) hsub hs
  exact hb.trans hmass
end CatalanCore.Li2.Decay.HeineSource
#print axioms CatalanCore.Li2.Decay.HeineSource.lattice_tail_mass


namespace CatalanCore.Li2.Decay.HeineSource
open CatalanCore.Li2.Uniform CatalanCore.Decay.CurveFamily

theorem chainPieces_length (v : ℂ) (pts : List ℂ) :
    ((chainPieces (v::pts)).map (fun q => ‖q.D‖)).sum ≤ ‖v‖+2*(pts.map (fun u => ‖u‖)).sum := by
  induction pts generalizing v with
  | nil => simp [chainPieces]
  | cons w rest ih =>
    simp only [chainPieces,List.map_cons,List.sum_cons]
    have hh := ih w
    have hd := norm_sub_le w v
    linarith

theorem upperModified_length_bound (p : PolygonFrame) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      ((upperModified p n).map (fun q => ‖q.D‖)).sum ≤ C*(n:ℝ) := by
  let k := ((p.vertex 1).re-p.cut)/(p.vertex 1).im
  let V := ((List.range p.edges).map (fun j => ‖p.vertex (j+1)‖)).sum
  let C := 10+5*p.cut+2*V+2*|k|
  have hV : 0 ≤ V := by
    dsimp only [V]
    apply List.sum_nonneg
    intro x hx
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hx
    exact norm_nonneg _
  refine ⟨C,by dsimp only [C]; nlinarith [p.nonneg,abs_nonneg k],?_⟩
  intro n hn
  have hnR : 1 ≤ (n:ℝ) := by exact_mod_cast hn
  have hnc : 0 ≤ (n:ℝ)*p.cut := mul_nonneg (by positivity) p.nonneg
  have hc0 : 0 ≤ crossing p n := by unfold crossing; positivity
  have hc : ‖(crossing p n:ℂ)‖ ≤ (n:ℝ)*p.cut+1/2 := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hc0]
    unfold crossing
    have hh := Nat.floor_le (mul_nonneg p.nonneg (Nat.cast_nonneg n : (0:ℝ)≤n))
    nlinarith
  have hv : ‖(crossing p n:ℂ)+Complex.I‖ ≤ (n:ℝ)*p.cut+3/2 := by
    have hh := norm_add_le (crossing p n:ℂ) Complex.I
    rw [Complex.norm_I] at hh
    linarith
  have hfirst : firstAtOne p n=((((n:ℝ)*p.cut+k:ℝ):ℂ))+Complex.I := by
    simp only [firstAtOne,k,← Complex.ofReal_mul,← Complex.ofReal_sub,
      ← Complex.ofReal_div,← Complex.ofReal_add]
  have hf : ‖firstAtOne p n‖ ≤ (n:ℝ)*p.cut+|k|+1 := by
    rw [hfirst]
    have hh := norm_add_le ((((n:ℝ)*p.cut+k:ℝ):ℂ)) Complex.I
    simp only [Complex.norm_real,Real.norm_eq_abs,Complex.norm_I] at hh
    have ha := abs_add_le ((n:ℝ)*p.cut) k
    rw [abs_of_nonneg hnc] at ha
    linarith
  have hverts : (((List.range p.edges).map (fun j => (n:ℂ)*p.vertex (j+1))).map (fun u => ‖u‖)).sum=
      (n:ℝ)*V := by
    have he (xs : List ℕ) : ((xs.map (fun j => (n:ℂ)*p.vertex (j+1))).map (fun u => ‖u‖)).sum=
        (n:ℝ)*(xs.map (fun j => ‖p.vertex (j+1)‖)).sum := by
      induction xs with
      | nil => simp
      | cons j xs ih =>
        simp only [List.map_cons,List.sum_cons,norm_mul,Complex.norm_natCast,ih]
        ring
    exact he _
  have hchain := chainPieces_length (crossing p n:ℂ)
    (((crossing p n:ℂ)+Complex.I)::firstAtOne p n::(List.range p.edges).map (fun j => (n:ℂ)*p.vertex (j+1)))
  simp only [List.map_cons,List.sum_cons,hverts] at hchain
  have hupper : ((upperModified p n).map (fun q => ‖q.D‖)).sum=
      ((chainPieces (((crossing p n:ℂ))::((crossing p n:ℂ)+Complex.I)::firstAtOne p n::
        (List.range p.edges).map (fun j => (n:ℂ)*p.vertex (j+1)))).map (fun q => ‖q.D‖)).sum+1 := by
    simp only [upperModified,List.map_append,List.sum_append,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,Complex.norm_I,add_zero,List.cons_append,List.nil_append]
  rw [hupper]
  have hk := mul_nonneg (sub_nonneg.mpr hnR) (abs_nonneg k)
  dsimp only [C]
  nlinarith

theorem oriented_length_bound {F : Frame} (g : FrameGeometry F) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      ((orientedPieces g n).map (fun r => ‖r.1.D‖)).sum ≤ C*(n:ℝ) := by
  cases g with
  | pure hp hl hf => refine ⟨1,by norm_num,?_⟩; intro n hn; simp [orientedPieces]
  | polygon p hp hl hf =>
    obtain ⟨C,hC,hbound⟩ := upperModified_length_bound p
    refine ⟨2*C,by positivity,?_⟩
    intro n hn
    have hh := hbound n hn
    simp only [orientedPieces,List.map_append,List.sum_append,List.map_map,Function.comp_def,
      Piece.conj,Complex.norm_conj]
    linarith
end CatalanCore.Li2.Decay.HeineSource
#print axioms CatalanCore.Li2.Decay.HeineSource.oriented_length_bound


namespace CatalanCore.Li2.Decay.HeineSource
open CatalanCore.Li2.Uniform CatalanCore.Decay.CurveFamily

theorem tail_piece_mass (z : ℝ) (hz : ValidZ z) (d : DualDatum) (θ : ℝ) (K : ℕ) :
    ∃ M a : ℝ, 0 < M ∧ 0 < a ∧ ∀ (n : ℕ), 0 < n → ∀ q : Piece,
      (∀ u ∈ pieceSet q, 0 ≤ u.re) →
      (q.ray=true → ∀ y : ℝ, 0 ≤ y → y ≤ ‖q.zeta y‖) →
      Integrable (fun y : ℝ => tailProfile z d θ K (q.zeta y/(n:ℂ))) q.nu ∧
        (∫ y : ℝ, tailProfile z d θ K (q.zeta y/(n:ℂ)) ∂q.nu) ≤ M*(1+(n:ℝ)/a) := by
  obtain ⟨M,a,hM,ha,hbound⟩ := field_envelope z hz d θ K
  refine ⟨M,a,hM,ha,?_⟩
  intro n hn q hre hgap
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  let b := a/(n:ℝ)
  have hb : 0 < b := div_pos ha hnR
  let f : ℝ → ℝ := fun y => tailProfile z d θ K (q.zeta y/(n:ℂ))
  have hm : Measurable f := (tailProfile_measurable z d θ K).comp (by dsimp only [f,Piece.zeta]; fun_prop)
  have hf0 (y : ℝ) : 0 ≤ f y := tailProfile_nonneg z d θ K _
  have hh : ∀ᵐ y : ℝ ∂q.nu, f y ≤ M*Real.exp (-b*‖q.zeta y‖) := by
    filter_upwards [piece_ae_in_set q] with y hy
    have hRe : 0 ≤ (q.zeta y/(n:ℂ)).re := by
      simp only [← Complex.ofReal_natCast,Complex.div_ofReal_re]
      exact div_nonneg (hre _ hy) hnR.le
    have hnorm : ‖q.zeta y/(n:ℂ)‖=‖q.zeta y‖/(n:ℝ) := by rw [norm_div,Complex.norm_natCast]
    have hbnd := hbound (q.zeta y/(n:ℂ)) hRe
    have he : -a*(‖q.zeta y‖/(n:ℝ)) = -b*‖q.zeta y‖ := by dsimp only [b]; ring
    simpa only [f,tailProfile,hnorm,he] using hbnd
  cases hr : q.ray
  · have hnu : q.nu=volume.restrict (Ioc (0:ℝ) 1) := by simp [Piece.nu,hr]
    rw [hnu] at hh ⊢
    have hle : ∀ᵐ y : ℝ ∂volume.restrict (Ioc (0:ℝ) 1), f y ≤ M := hh.mono fun y hy =>
      hy.trans ((mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr (by nlinarith [norm_nonneg (q.zeta y)])) hM.le).trans_eq (mul_one M))
    have hi : Integrable f (volume.restrict (Ioc (0:ℝ) 1)) := by
      apply (integrable_const M).mono' hm.aestronglyMeasurable
      filter_upwards [hle] with y hy
      simpa only [Real.norm_eq_abs,abs_of_nonneg (hf0 y)] using hy
    refine ⟨hi,?_⟩
    have hv := integral_mono_ae hi (integrable_const M) hle
    have hc : (∫ y in Ioc (0:ℝ) 1, M)=M := by simp
    rw [hc] at hv
    exact hv.trans (by nlinarith [div_nonneg hnR.le ha.le])
  · have hnu : q.nu=volume.restrict (Ioi (0:ℝ)) := by simp [Piece.nu,hr]
    rw [hnu] at hh ⊢
    have hle : ∀ᵐ y : ℝ ∂volume.restrict (Ioi (0:ℝ)), f y ≤ M*Real.exp (-b*y) := by
      filter_upwards [hh,ae_restrict_mem measurableSet_Ioi] with y hy hy0
      exact hy.trans (mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left (hgap hr y hy0.le) (by linarith))) hM.le)
    have hmaj : Integrable (fun y : ℝ => M*Real.exp (-b*y)) (volume.restrict (Ioi (0:ℝ))) :=
      (integrableOn_exp_mul_Ioi (by linarith : -b<0) 0).const_mul M
    have hi : Integrable f (volume.restrict (Ioi (0:ℝ))) := by
      apply hmaj.mono' hm.aestronglyMeasurable
      filter_upwards [hle] with y hy
      simpa only [Real.norm_eq_abs,abs_of_nonneg (hf0 y)] using hy
    refine ⟨hi,?_⟩
    have hv := integral_mono_ae hi hmaj hle
    rw [integral_const_mul,integral_exp_mul_Ioi (by linarith : -b<0) 0] at hv
    have he : M*(-Real.exp (-b*0)/(-b))=M*(n:ℝ)/a := by
      simp only [mul_zero,Real.exp_zero,neg_div_neg_eq]
      dsimp only [b]
      field_simp
    rw [he] at hv
    exact hv.trans (by
      have he : M*(1+(n:ℝ)/a)=M+M*(n:ℝ)/a := by ring
      rw [he]
      exact le_add_of_nonneg_left hM.le)
end CatalanCore.Li2.Decay.HeineSource
#print axioms CatalanCore.Li2.Decay.HeineSource.tail_piece_mass


namespace CatalanCore.Li2.Decay.HeineSource
open CatalanCore.Li2.Uniform CatalanCore.Tools.Jets

theorem tailEnvelope_source {F : Frame} (g : FrameGeometry F) (z : ℝ) (n : ℕ)
    (d : DualDatum) (θ : ℝ) (K : ℕ) (r : Fin (2*n) → SourceSpace g n)
    (c : AdmissibleConfig F g z n) (hc : ∀ i, c.particle i=sourceParticle g n (r i)) :
    tailEnvelope z d θ K n c=∏ i : Fin (2*n), sourceTail g z n d θ K (r i) := by
  unfold tailEnvelope
  apply Finset.prod_congr rfl
  intro i hi
  rw [hc]
  unfold sourceTail tailProfile
  split_ifs <;> ring

theorem source_integrand_capped (z : ℝ) (hz : ValidZ z) (F : Frame) (g : FrameGeometry F)
    (d : DualDatum) (θ ρ : ℝ) (hρ : 0 < ρ) (hF : FreeBound z F d θ) :
    ∃ K : ℕ, ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ t : ℝ,
      |t| ≤ Real.exp (-ρ*(n:ℝ)) →
      ∀ᵐ r : Fin (2*n) → SourceSpace g n ∂Measure.pi (fun _ : Fin (2*n) => sourceMeasure g z n),
        ‖CatalanCore.Tools.IntegratedJets.tensorIntegrand (2*n) (sourceJet g z n t) (vandSq (2*n)) r‖ ≤
          Real.exp ((n:ℝ)^2*(I d.σ+2*θ+2*latPenalty z F d.σ θ+atomPenalty z ρ d.σ θ+ε)+
            2*(n:ℝ)^2*Real.log n)*(∏ i : Fin (2*n), sourceTail g z n d θ K (r i)) := by
  obtain ⟨K,hcap⟩ := capped_configuration_bound z hz F g d θ ρ hρ hF
  refine ⟨K,?_⟩
  intro ε hε
  filter_upwards [hcap ε hε,eventually_ge_atTop (1:ℕ)] with n hncap hn
  intro t ht
  filter_upwards [source_allowed_pi_ae g z n (2*n)] with r hr
  rcases source_config_or_zero g z n (by omega) t r hr with hzero|⟨c,hc⟩
  · rw [hzero,norm_zero]
    exact mul_nonneg (Real.exp_pos _).le (Finset.prod_nonneg (fun i hi => sourceTail_nonneg g z n d θ K (r i)))
  · have hb := hncap t ht c
    rw [tailEnvelope_source g z n d θ K r c hc] at hb
    exact (tensorIntegrand_config_norm g z n t r c hc).trans hb

theorem source_det_bound {F : Frame} (g : FrameGeometry F) (z : ℝ) (hz : ValidZ z)
    (n : ℕ) (hn : 0 < n) (t : ℝ) (hH : SourceHeight g n)
    (hΓ : ∀ u ∈ gammaN g n, 0 ≤ u.re ∧ 1/2 ≤ ‖u‖ ∧
      ((∃ N : ℕ, u.re=(N:ℝ)+1/2) ∨ 1 ≤ |u.im|))
    (d : DualDatum) (θ : ℝ) (K : ℕ) (B : ℝ)
    (hMass : Integrable (sourceTail g z n d θ K) (sourceMeasure g z n))
    (hBound : ∀ᵐ r : Fin (2*n) → SourceSpace g n ∂Measure.pi (fun _ : Fin (2*n) => sourceMeasure g z n),
      ‖CatalanCore.Tools.IntegratedJets.tensorIntegrand (2*n) (sourceJet g z n t) (vandSq (2*n)) r‖ ≤
        B*(∏ i : Fin (2*n), sourceTail g z n d θ K (r i))) :
    ‖Matrix.det (fun i j : Fin (2*n) => functional z n t (Polynomial.X^(i.val+j.val)))‖ ≤
      B*(∫ r : SourceSpace g n, sourceTail g z n d θ K r ∂sourceMeasure g z n)^(2*n) := by
  have hmaj : Integrable (fun r : Fin (2*n) → SourceSpace g n =>
      B*(∏ i : Fin (2*n), sourceTail g z n d θ K (r i)))
      (Measure.pi (fun _ : Fin (2*n) => sourceMeasure g z n)) :=
    (Integrable.fintype_prod (fun i : Fin (2*n) => hMass)).const_mul B
  have hInt := norm_integral_le_of_norm_le hmaj hBound
  rw [integral_const_mul,integral_fintype_prod_eq_pow] at hInt
  simp only [Fintype.card_fin] at hInt
  have hfact : ‖((2*n).factorial:ℂ)⁻¹‖ ≤ 1 := by
    rw [norm_inv,Complex.norm_natCast]
    have hh : (1:ℝ) ≤ ((2*n).factorial:ℝ) := by
      exact_mod_cast (Nat.succ_le_iff.mpr (Nat.factorial_pos (2*n)))
    have hi := one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1) hh
    simpa only [one_div,inv_one] using hi
  rw [heine_source g z hz n hn t hH hΓ,norm_mul]
  exact (mul_le_mul hfact hInt (norm_nonneg _) (by norm_num : (0:ℝ)≤1)).trans_eq (one_mul _)
end CatalanCore.Li2.Decay.HeineSource
#print axioms CatalanCore.Li2.Decay.HeineSource.source_integrand_capped
#print axioms CatalanCore.Li2.Decay.HeineSource.source_det_bound


namespace CatalanCore.Li2.Decay.HeineSource
open CatalanCore.Li2.Uniform CatalanCore.Decay.CurveFamily
open CatalanLambda.Decay (sumM integrable_sumM_iff integral_sumM)

theorem source_real_parts {F : Frame} (g : FrameGeometry F) (z : ℝ) (n : ℕ)
    (f : SourceSpace g n → ℝ)
    (hL : Integrable (fun x : LatticeIdx F n => f (.inl x)) Measure.count)
    (hC : Integrable (fun r : Fin (orientedPieces g n).length × ℝ => f (.inr (.inl r))) (famMeasure (curveMeasure g n)))
    (hR : Integrable (fun x : ℝ => f (.inr (.inr (.inl x)))) (rayMeasure g z n))
    (hA : Integrable (fun j : AtomIdx n => f (.inr (.inr (.inr j)))) Measure.count) :
    Integrable f (sourceMeasure g z n) ∧
    (∫ r : SourceSpace g n, f r ∂sourceMeasure g z n)=
      (∫ x : LatticeIdx F n, f (.inl x) ∂Measure.count)+
      ((∫ r : Fin (orientedPieces g n).length × ℝ, f (.inr (.inl r)) ∂famMeasure (curveMeasure g n))+
      ((∫ x : ℝ, f (.inr (.inr (.inl x))) ∂rayMeasure g z n)+
        (∫ j : AtomIdx n, f (.inr (.inr (.inr j))) ∂Measure.count))) := by
  have hRA : Integrable (fun r : ℝ ⊕ AtomIdx n => (f (.inr (.inr r)):ℂ))
      (sumM (rayMeasure g z n) (Measure.count : Measure (AtomIdx n))) :=
    (integrable_sumM_iff _ _ _).mpr ⟨hR.ofReal,hA.ofReal⟩
  have hCA : Integrable (fun r : (Fin (orientedPieces g n).length × ℝ) ⊕ (ℝ ⊕ AtomIdx n) => (f (.inr r):ℂ))
      (sumM (famMeasure (curveMeasure g n)) (sumM (rayMeasure g z n) (Measure.count : Measure (AtomIdx n)))) :=
    (integrable_sumM_iff _ _ _).mpr ⟨hC.ofReal,hRA⟩
  have hAll : Integrable (fun r : SourceSpace g n => (f r:ℂ)) (sourceMeasure g z n) :=
    (integrable_sumM_iff _ _ _).mpr ⟨hL.ofReal,hCA⟩
  refine ⟨by simpa only [RCLike.re_to_complex,Complex.ofReal_re] using hAll.re,?_⟩
  have hh : (∫ r : SourceSpace g n, (f r:ℂ) ∂sourceMeasure g z n)=
      (∫ x : LatticeIdx F n, (f (.inl x):ℂ) ∂Measure.count)+
      ((∫ r : Fin (orientedPieces g n).length × ℝ, (f (.inr (.inl r)):ℂ) ∂famMeasure (curveMeasure g n))+
      ((∫ x : ℝ, (f (.inr (.inr (.inl x))):ℂ) ∂rayMeasure g z n)+
        (∫ j : AtomIdx n, (f (.inr (.inr (.inr j))):ℂ) ∂Measure.count))) := by
    unfold sourceMeasure
    rw [integral_sumM _ _ _ hAll,integral_sumM _ _ _ hCA,integral_sumM _ _ _ hRA]
  have hr := congrArg Complex.re hh
  simpa only [integral_complex_ofReal,Complex.add_re,Complex.ofReal_re] using hr

theorem curve_tail_mass {F : Frame} (g : FrameGeometry F) (z : ℝ) (hz : ValidZ z)
    (d : DualDatum) (θ : ℝ) (K : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      Integrable (fun r : Fin (orientedPieces g n).length × ℝ =>
        tailProfile z d θ K (((orientedPieces g n).get r.1).1.zeta r.2/(n:ℂ))) (famMeasure (curveMeasure g n)) ∧
      (∫ r : Fin (orientedPieces g n).length × ℝ,
        tailProfile z d θ K (((orientedPieces g n).get r.1).1.zeta r.2/(n:ℂ))
        ∂famMeasure (curveMeasure g n)) ≤ C*(n:ℝ)^2 := by
  obtain ⟨M,a,hM,ha,hpiece⟩ := tail_piece_mass z hz d θ K
  obtain ⟨L,hL,hlen⟩ := oriented_length_bound g
  let C := M*L*(1+1/a)
  refine ⟨C,by dsimp only [C]; positivity,?_⟩
  filter_upwards [source_eventually g] with n hn
  have hn0 := hn.1
  have hn1 : 1 ≤ n := by omega
  have hnR : 1 ≤ (n:ℝ) := by exact_mod_cast hn1
  have hΓ := hn.2.2
  have hi (i : Fin (orientedPieces g n).length) :
      Integrable (fun y : ℝ => tailProfile z d θ K (((orientedPieces g n).get i).1.zeta y/(n:ℂ)))
          ((orientedPieces g n).get i).1.nu ∧
      (∫ y : ℝ, tailProfile z d θ K (((orientedPieces g n).get i).1.zeta y/(n:ℂ))
        ∂((orientedPieces g n).get i).1.nu) ≤ M*(1+(n:ℝ)/a) := by
    apply hpiece n hn0
    · intro u hu
      exact (hΓ u (oriented_piece_in_gamma g n _ (List.get_mem _ _) u hu)).1
    · intro hh y hy
      exact oriented_ray_gap g n hn0 _ (List.get_mem _ _) hh y hy
  have hiC : Integrable (fun r : Fin (orientedPieces g n).length × ℝ =>
      tailProfile z d θ K (((orientedPieces g n).get r.1).1.zeta r.2/(n:ℂ)))
      (famMeasure (curveMeasure g n)) := by
    rw [integrable_fam_iff]
    intro i
    exact (hi i).1.smul_measure_nnreal
  refine ⟨hiC,?_⟩
  rw [integral_fam (curveMeasure g n) hiC]
  have hb (i : Fin (orientedPieces g n).length) :
      (∫ y : ℝ, tailProfile z d θ K (((orientedPieces g n).get i).1.zeta y/(n:ℂ)) ∂curveMeasure g n i) ≤
        ‖((orientedPieces g n).get i).1.D‖*(M*(1+(n:ℝ)/a)) := by
    dsimp only [curveMeasure]
    rw [integral_smul_nnreal_measure]
    simp only [NNReal.smul_def,NNReal.coe_mk,smul_eq_mul]
    exact mul_le_mul_of_nonneg_left (hi i).2 (norm_nonneg _)
  apply (Finset.sum_le_sum (fun i hi => hb i)).trans
  rw [← Finset.sum_mul]
  have hget : (∑ i : Fin (orientedPieces g n).length, ‖((orientedPieces g n).get i).1.D‖)=
      ((orientedPieces g n).map (fun r => ‖r.1.D‖)).sum := by
    rw [← List.sum_ofFn]
    have he : List.ofFn (fun i : Fin (orientedPieces g n).length => ‖((orientedPieces g n).get i).1.D‖)=
        (List.ofFn (fun i : Fin (orientedPieces g n).length => (orientedPieces g n).get i)).map (fun r => ‖r.1.D‖) := by
      rw [List.map_ofFn]
      rfl
    rw [he,List.ofFn_get]
  rw [hget]
  have hlenN := hlen n hn1
  have hfac : 1+(n:ℝ)/a ≤ (n:ℝ)*(1+1/a) := by
    have he : (n:ℝ)*(1+1/a)=(n:ℝ)+(n:ℝ)/a := by ring
    rw [he]
    linarith
  calc
    _ ≤ (L*(n:ℝ))*(M*((n:ℝ)*(1+1/a))) :=
      mul_le_mul hlenN (mul_le_mul_of_nonneg_left hfac hM.le)
        (by positivity) (by positivity)
    _ = C*(n:ℝ)^2 := by dsimp only [C]; ring
end CatalanCore.Li2.Decay.HeineSource
#print axioms CatalanCore.Li2.Decay.HeineSource.curve_tail_mass


namespace CatalanCore.Li2.Decay.HeineSource
open CatalanCore.Li2.Uniform

theorem ray_tail_mass (z : ℝ) (hz : ValidZ z) (d : DualDatum) (θ : ℝ) (K : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : Frame) (g : FrameGeometry F) (n : ℕ), 0 < n →
      Integrable (fun x : ℝ => tailProfile z d θ K ((x:ℂ)/(n:ℂ))) (rayMeasure g z n) ∧
      (∫ x : ℝ, tailProfile z d θ K ((x:ℂ)/(n:ℂ)) ∂rayMeasure g z n) ≤ C*(n:ℝ) := by
  obtain ⟨M,a,hM,ha,hbound⟩ := field_envelope z hz d θ K
  let C := M/a
  refine ⟨C,by dsimp only [C]; positivity,?_⟩
  intro F g n hn
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  cases g with
  | pure hp hl hf =>
    simp only [rayMeasure,integrable_zero_measure,integral_zero_measure,true_and]
    dsimp only [C]
    positivity
  | polygon p hp hl hf =>
    by_cases hpos : 0 < z
    · let v : ℝ := (Nat.floor (p.cut*n):ℝ)+1/2
      have hv : 0 ≤ v := by dsimp only [v]; positivity
      let b := a/(n:ℝ)
      have hb : 0 < b := div_pos ha hnR
      let f : ℝ → ℝ := fun x => tailProfile z d θ K ((x:ℂ)/(n:ℂ))
      have hm : Measurable f := (tailProfile_measurable z d θ K).comp (by fun_prop)
      have hf0 (x : ℝ) : 0 ≤ f x := tailProfile_nonneg z d θ K ((x:ℂ)/(n:ℂ))
      have hle (x : ℝ) (hx : 0 ≤ x) : f x ≤ M*Real.exp (-b*x) := by
        have hre : 0 ≤ ((x:ℂ)/(n:ℂ)).re := by
          simp only [← Complex.ofReal_natCast,Complex.div_ofReal_re,Complex.ofReal_re]
          positivity
        have hh := hbound ((x:ℂ)/(n:ℂ)) hre
        have hnorm : ‖(x:ℂ)/(n:ℂ)‖=x/(n:ℝ) := by
          rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hx,Complex.norm_natCast]
        have he : -a*(x/(n:ℝ)) = -b*x := by dsimp only [b]; ring
        simpa only [f,tailProfile,hnorm,he] using hh
      have hmaj : IntegrableOn (fun x : ℝ => M*Real.exp (-b*x)) (Ioi v) :=
        (integrableOn_exp_mul_Ioi (by linarith : -b<0) v).const_mul M
      have hAE : ∀ᵐ x : ℝ ∂volume.restrict (Ioi v), f x ≤ M*Real.exp (-b*x) := by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
        exact hle x (hv.trans hx.le)
      have hi : IntegrableOn f (Ioi v) := by
        apply hmaj.mono' hm.aestronglyMeasurable
        filter_upwards [hAE] with x hx
        simpa only [Real.norm_eq_abs,abs_of_nonneg (hf0 x)] using hx
      have hiC : IntegrableOn f (Ici v) := Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi hi
      simp only [rayMeasure,if_pos hpos]
      refine ⟨hiC,?_⟩
      change (∫ x in Ici v, f x) ≤ _
      rw [integral_Ici_eq_integral_Ioi]
      have hh := integral_mono_ae hi hmaj hAE
      rw [integral_const_mul,integral_exp_mul_Ioi (by linarith : -b<0) v] at hh
      have he : M*(-Real.exp (-b*v)/(-b))=(M/b)*Real.exp (-b*v) := by ring
      rw [he] at hh
      calc
        _ ≤ (M/b)*Real.exp (-b*v) := hh
        _ ≤ (M/b)*1 := mul_le_mul_of_nonneg_left
          (Real.exp_le_one_iff.mpr (by nlinarith)) (by positivity)
        _ = C*(n:ℝ) := by dsimp only [b,C]; field_simp <;> ring
    · simp only [rayMeasure,if_neg hpos,integrable_zero_measure,integral_zero_measure,true_and]
      dsimp only [C]
      positivity

theorem atom_tail_mass (n : ℕ) :
    Integrable (fun j : AtomIdx n => (1:ℝ)) Measure.count ∧
      (∫ j : AtomIdx n, (1:ℝ) ∂Measure.count) ≤ 4*(n:ℝ) := by
  refine ⟨Integrable.of_finite,?_⟩
  rw [integral_count]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]
  have hcard : Fintype.card (AtomIdx n) ≤ 4*n := by
    change Fintype.card ↥(Finset.Icc (n+1) (4*n)) ≤ 4*n
    rw [Fintype.card_coe,Nat.card_Icc]
    omega
  exact_mod_cast hcard
end CatalanCore.Li2.Decay.HeineSource
#print axioms CatalanCore.Li2.Decay.HeineSource.ray_tail_mass
#print axioms CatalanCore.Li2.Decay.HeineSource.atom_tail_mass


namespace CatalanCore.Li2.Decay.HeineSource
open CatalanCore.Li2.Uniform

theorem source_tail_mass {F : Frame} (g : FrameGeometry F) (z : ℝ) (hz : ValidZ z)
    (d : DualDatum) (θ : ℝ) (K : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      Integrable (sourceTail g z n d θ K) (sourceMeasure g z n) ∧
      (∫ r : SourceSpace g n, sourceTail g z n d θ K r ∂sourceMeasure g z n) ≤ C*(n:ℝ)^2 := by
  obtain ⟨CL,hCL,hLat⟩ := lattice_tail_mass z hz d θ K
  obtain ⟨CC,hCC,hCurve⟩ := curve_tail_mass g z hz d θ K
  obtain ⟨CR,hCR,hRay⟩ := ray_tail_mass z hz d θ K
  let C := CL+CC+CR+4
  refine ⟨C,by dsimp only [C]; positivity,?_⟩
  filter_upwards [hCurve,eventually_ge_atTop (1:ℕ)] with n hC hn
  have hn0 : 0 < n := by omega
  have hnR : 1 ≤ (n:ℝ) := by exact_mod_cast hn
  have hL : Integrable (fun x : LatticeIdx F n => sourceTail g z n d θ K (.inl x)) Measure.count ∧
      (∫ x : LatticeIdx F n, sourceTail g z n d θ K (.inl x) ∂Measure.count) ≤ CL*(n:ℝ) := by
    simpa only [sourceTail,sourceParticle,isAtom,Particle.point,Bool.false_eq_true,↓reduceIte] using hLat F n hn0
  have hC' : Integrable (fun r : Fin (orientedPieces g n).length × ℝ => sourceTail g z n d θ K (.inr (.inl r)))
        (CatalanCore.Decay.CurveFamily.famMeasure (curveMeasure g n)) ∧
      (∫ r : Fin (orientedPieces g n).length × ℝ, sourceTail g z n d θ K (.inr (.inl r))
        ∂CatalanCore.Decay.CurveFamily.famMeasure (curveMeasure g n)) ≤ CC*(n:ℝ)^2 := by
    simpa only [sourceTail,sourceParticle,isAtom,Particle.point,Bool.false_eq_true,↓reduceIte] using hC
  have hR : Integrable (fun x : ℝ => sourceTail g z n d θ K (.inr (.inr (.inl x)))) (rayMeasure g z n) ∧
      (∫ x : ℝ, sourceTail g z n d θ K (.inr (.inr (.inl x))) ∂rayMeasure g z n) ≤ CR*(n:ℝ) := by
    simpa only [sourceTail,sourceParticle,isAtom,Particle.point,Bool.false_eq_true,↓reduceIte] using hRay F g n hn0
  have hA : Integrable (fun j : AtomIdx n => sourceTail g z n d θ K (.inr (.inr (.inr j)))) Measure.count ∧
      (∫ j : AtomIdx n, sourceTail g z n d θ K (.inr (.inr (.inr j))) ∂Measure.count) ≤ 4*(n:ℝ) := by
    simpa only [sourceTail,sourceParticle,isAtom,↓reduceIte] using atom_tail_mass n
  have hp := source_real_parts g z n (sourceTail g z n d θ K) hL.1 hC'.1 hR.1 hA.1
  refine ⟨hp.1,?_⟩
  rw [hp.2]
  have hsum := add_le_add hL.2 (add_le_add hC'.2 (add_le_add hR.2 hA.2))
  apply hsum.trans
  have hnn : (n:ℝ) ≤ (n:ℝ)^2 := by nlinarith
  have h1 := mul_le_mul_of_nonneg_left hnn hCL.le
  have h2 := mul_le_mul_of_nonneg_left hnn hCR.le
  have h3 := mul_le_mul_of_nonneg_left hnn (by norm_num : (0:ℝ)≤4)
  dsimp only [C]
  nlinarith
end CatalanCore.Li2.Decay.HeineSource
#print axioms CatalanCore.Li2.Decay.HeineSource.source_tail_mass


namespace CatalanCore.Li2.Decay.HeineSource
open CatalanCore.Li2.Uniform

theorem source_det_growth (z : ℝ) (hz : ValidZ z) (F : Frame) (g : FrameGeometry F)
    (d : DualDatum) (θ ρ : ℝ) (hρ : 0 < ρ) (hF : FreeBound z F d θ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ t : ℝ,
      |t| ≤ Real.exp (-ρ*(n:ℝ)) →
      ‖Matrix.det (fun i j : Fin (2*n) => functional z n t (Polynomial.X^(i.val+j.val)))‖ ≤
        Real.exp ((n:ℝ)^2*(I d.σ+2*θ+2*latPenalty z F d.σ θ+atomPenalty z ρ d.σ θ+ε)+
          2*(n:ℝ)^2*Real.log n)*(C*(n:ℝ)^2)^(2*n) := by
  obtain ⟨K,hcap⟩ := source_integrand_capped z hz F g d θ ρ hρ hF
  obtain ⟨C,hC,hmass⟩ := source_tail_mass g z hz d θ K
  refine ⟨C,hC,?_⟩
  intro ε hε
  filter_upwards [hcap ε hε,hmass,source_eventually g] with n hcapN hmassN hsource
  intro t ht
  have hb := source_det_bound g z hz n hsource.1 t hsource.2.1 hsource.2.2 d θ K _ hmassN.1 (hcapN t ht)
  have h0 : 0 ≤ ∫ r : SourceSpace g n, sourceTail g z n d θ K r ∂sourceMeasure g z n :=
    integral_nonneg (fun r => sourceTail_nonneg g z n d θ K r)
  exact hb.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 hmassN.2 (2*n)) (Real.exp_pos _).le)
end CatalanCore.Li2.Decay.HeineSource
#print axioms CatalanCore.Li2.Decay.HeineSource.source_det_growth

namespace CatalanCore.Li2.Decay

theorem li2_summable (z : ℝ) (hz : ValidZ z) :
    Summable (fun m : ℕ => z^(m+1)/((m:ℝ)+1)^2) := by
  have hg : Summable (fun m : ℕ => |z|^(m+1)) :=
    (summable_nat_add_iff 1).mpr (summable_geometric_of_abs_lt_one (by simpa only [abs_abs] using hz.2))
  apply hg.of_norm_bounded
  intro m
  rw [Real.norm_eq_abs,abs_div,abs_pow,abs_pow,abs_of_nonneg (by positivity : 0 ≤ (m:ℝ)+1)]
  exact div_le_self (by positivity) (by have hm := Nat.cast_nonneg m (α := ℝ); nlinarith)

theorem shifted_li2_sum (z : ℝ) (hz : ValidZ z) (j : ℕ) :
    (∑' m : ℕ, z^(m+1)/((m:ℝ)+j+1)^2)=
      z⁻¹^j*(li2 z-∑ b ∈ Finset.range j, z^(b+1)/((b:ℝ)+1)^2) := by
  have hz0 : z ≠ 0 := by intro he; simpa only [he,abs_zero,lt_self_iff_false] using hz.1
  let f : ℕ → ℝ := fun m => z^(m+1)/((m:ℝ)+1)^2
  have hs : Summable f := li2_summable z hz
  have hh := hs.sum_add_tsum_nat_add j
  have htail : (∑' m : ℕ, f (m+j))=li2 z-∑ b ∈ Finset.range j, f b := by
    change (∑ b ∈ Finset.range j, f b)+(∑' m : ℕ, f (m+j))=li2 z at hh
    linarith
  rw [← htail,← tsum_mul_left]
  apply tsum_congr
  intro m
  dsimp only [f]
  rw [show m+j+1=(m+1)+j by omega,pow_add,inv_pow]
  push_cast
  field_simp
  <;> ring
end CatalanCore.Li2.Decay
#print axioms CatalanCore.Li2.Decay.li2_summable
#print axioms CatalanCore.Li2.Decay.shifted_li2_sum


namespace CatalanCore.Li2.Decay
open Polynomial
namespace P0
noncomputable abbrev D := CatalanCore.Li2.Port.Li2.D
noncomputable abbrev numerator := CatalanCore.Li2.Port.Li2.numerator
noncomputable abbrev polynomialPart := CatalanCore.Li2.Port.Li2.polynomialPart
noncomputable abbrev residue := CatalanCore.Li2.Port.Li2.residue
end P0

theorem port_D_aeval (m : ℕ) (u : ℂ) : (P0.D m).aeval u=Dprod m u := by
  simp [P0.D,CatalanCore.Li2.Port.Li2.D,Dprod]

theorem right_add_nat_ne_zero (u : ℂ) (hu : 0 ≤ u.re) (j : ℕ) (hj : 1 ≤ j) :
    u+(j:ℂ) ≠ 0 := by
  intro he
  have hh := congrArg Complex.re he
  simp only [Complex.add_re,Complex.natCast_re,Complex.zero_re] at hh
  have hjR : 0 < (j:ℝ) := by exact_mod_cast (show 0 < j by omega)
  linarith

theorem weight_partial_fractions (n k : ℕ) (u : ℂ) (hu : 0 ≤ u.re) :
    u^k*weight n u=(P0.polynomialPart n k).aeval u+
      ∑ j ∈ Finset.Icc 1 (4*n), (P0.residue n k j:ℂ)/(u+(j:ℂ)) := by
  have hne (j) (hj : j ∈ Finset.Icc 1 (4*n)) : u+(j:ℂ) ≠ 0 :=
    right_add_nat_ne_zero u hu j (Finset.mem_Icc.mp hj).1
  have hD : Dprod (4*n) u ≠ 0 := Finset.prod_ne_zero_iff.mpr hne
  have hE (j) (hj : j ∈ Finset.Icc 1 (4*n)) :
      (∏ l ∈ (Finset.Icc 1 (4*n)).erase j, (u+(l:ℂ)))=
        Dprod (4*n) u/(u+(j:ℂ)) :=
    (eq_div_iff (hne j hj)).mpr
      (Finset.prod_erase_mul (Finset.Icc 1 (4*n)) (fun l => u+(l:ℂ)) hj)
  have h : u^k*Dprod n u^3=(P0.polynomialPart n k).aeval u*Dprod (4*n) u+
      ∑ j ∈ Finset.Icc 1 (4*n), (P0.residue n k j:ℂ)*
        (∏ l ∈ (Finset.Icc 1 (4*n)).erase j, (u+(l:ℂ))) := by
    have hh := congrArg (fun P : ℚ[X] => P.aeval u)
      (CatalanCore.Li2.Port.Li2.numerator_partial_fractions n k)
    have hcast (q : ℚ) : (algebraMap ℚ ℂ) q=(q:ℂ) :=
      congrArg (fun f : ℚ →+* ℂ => f q) (show algebraMap ℚ ℂ=Rat.castHom ℂ from Subsingleton.elim _ _)
    simpa only [P0.polynomialPart,P0.residue,hcast,CatalanCore.Li2.Port.Li2.numerator,map_mul,map_pow,aeval_X,map_add,map_sum,
      map_prod,aeval_C,map_natCast,port_D_aeval] using hh
  have hsplit : (∑ j ∈ Finset.Icc 1 (4*n), (P0.residue n k j:ℂ)*
      (∏ l ∈ (Finset.Icc 1 (4*n)).erase j, (u+(l:ℂ))))=
      ∑ j ∈ Finset.Icc 1 (4*n), (P0.residue n k j:ℂ)*(Dprod (4*n) u/(u+(j:ℂ))) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [hE j hj]
  rw [hsplit] at h
  have hs : (∑ j ∈ Finset.Icc 1 (4*n), (P0.residue n k j:ℂ)/(u+(j:ℂ)))*Dprod (4*n) u=
      ∑ j ∈ Finset.Icc 1 (4*n), (P0.residue n k j:ℂ)*(Dprod (4*n) u/(u+(j:ℂ))) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  unfold weight
  rw [← mul_div_assoc]
  apply (div_eq_iff hD).mpr
  rw [add_mul,hs]
  exact h
end CatalanCore.Li2.Decay
#print axioms CatalanCore.Li2.Decay.weight_partial_fractions



namespace CatalanCore.Li2.Decay
open Polynomial

theorem weighted_monomial_deriv (n k : ℕ) (x : ℂ) (hx : 0 < x.re) :
    deriv (fun u : ℂ => u*weight n u*(Polynomial.X^k).eval u) x=
      ((Polynomial.X*P0.polynomialPart n k).derivative).aeval x+
        ∑ j ∈ Finset.Icc 1 (4*n), (P0.residue n k j:ℂ)*(j:ℂ)/(x+(j:ℂ))^2 := by
  have hne (j) (hj : j ∈ Finset.Icc 1 (4*n)) : x+(j:ℂ) ≠ 0 :=
    right_add_nat_ne_zero x hx.le j (Finset.mem_Icc.mp hj).1
  have hpole (j) (hj : j ∈ Finset.Icc 1 (4*n)) :
      HasDerivAt (fun u : ℂ => (P0.residue n k j:ℂ)*u/(u+(j:ℂ)))
        ((P0.residue n k j:ℂ)*(j:ℂ)/(x+(j:ℂ))^2) x := by
    convert (((hasDerivAt_id x).const_mul (P0.residue n k j:ℂ)).div
      ((hasDerivAt_id x).add_const (j:ℂ)) (hne j hj)) using 1
    · funext u
      simp only [Pi.div_apply,id_eq] <;> ring
    · simp only [id_eq]
      field_simp
      <;> ring
  have hd := ((Polynomial.X*P0.polynomialPart n k).hasDerivAt_aeval x).add
    (HasDerivAt.fun_sum hpole)
  have hmem : ∀ᶠ u : ℂ in nhds x, 0 < u.re :=
    Complex.continuous_re.continuousAt.eventually (eventually_gt_nhds hx)
  have heq : (fun u : ℂ => u*weight n u*(Polynomial.X^k).eval u) =ᶠ[nhds x]
      (fun u : ℂ => (Polynomial.X*P0.polynomialPart n k).aeval u+
        ∑ j ∈ Finset.Icc 1 (4*n), (P0.residue n k j:ℂ)*u/(u+(j:ℂ))) := by
    filter_upwards [hmem] with u hu
    rw [Polynomial.eval_pow,Polynomial.eval_X,map_mul,aeval_X]
    calc
      _ = u*(u^k*weight n u) := by ring
      _ = u*((P0.polynomialPart n k).aeval u+
          ∑ j ∈ Finset.Icc 1 (4*n), (P0.residue n k j:ℂ)/(u+(j:ℂ))) := by
            rw [weight_partial_fractions n k u hu.le]
      _ = _ := by
        rw [mul_add,Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro j hj
        ring
  exact (hd.congr_of_eventuallyEq heq).deriv
end CatalanCore.Li2.Decay
#print axioms CatalanCore.Li2.Decay.weighted_monomial_deriv


namespace CatalanCore.Li2.Decay
open Polynomial

theorem parameterU_complex_series (z : ℚ) (hz : ‖(z:ℝ)‖ < 1) (P : ℚ[X]) :
    Summable (fun m : ℕ => (z:ℂ)^(m+1)*((Polynomial.X*P).derivative).aeval (((m+1:ℕ):ℂ))) ∧
      (∑' m : ℕ, (z:ℂ)^(m+1)*((Polynomial.X*P).derivative).aeval (((m+1:ℕ):ℂ)))=
        (CatalanCore.Li2.Port.Li2.parameterU z P:ℂ) := by
  let Q := (Polynomial.X*P).derivative
  have hc (q : ℚ) : ((q:ℝ):ℂ)=(q:ℂ) := map_ratCast Complex.ofRealHom q
  have hcast (q : ℚ) : (algebraMap ℚ ℂ) q=(q:ℂ) :=
    congrArg (fun f : ℚ →+* ℂ => f q) (show algebraMap ℚ ℂ=Rat.castHom ℂ from Subsingleton.elim _ _)
  have heval (q : ℚ) : Q.aeval (q:ℂ)=((Q.eval q:ℚ):ℂ) := by
    simpa only [hcast] using (Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval (A := ℂ) q Q)
  have hterm (m : ℕ) : ((((z^(m+1)*Q.eval ((m:ℚ)+1):ℚ):ℝ):ℂ))=
      (z:ℂ)^(m+1)*Q.aeval (((m+1:ℕ):ℂ)) := by
    rw [hc]
    push_cast
    rw [← heval]
    push_cast <;> rfl
  have hsum := CatalanCore.Li2.Port.Li2.summable_parameterPolynomial z hz Q
  have hsC := Complex.summable_ofReal.mpr hsum
  have hs : Summable (fun m : ℕ => (z:ℂ)^(m+1)*Q.aeval (((m+1:ℕ):ℂ))) :=
    hsC.congr (fun m => hterm m)
  refine ⟨hs,?_⟩
  change (∑' m : ℕ, (z:ℂ)^(m+1)*Q.aeval (((m+1:ℕ):ℂ)))= _
  calc
    _ = ∑' m : ℕ, ((((z^(m+1)*Q.eval ((m:ℚ)+1):ℚ):ℝ):ℂ)) := tsum_congr (fun m => (hterm m).symm)
    _ = (((∑' m : ℕ, ((z^(m+1)*Q.eval ((m:ℚ)+1):ℚ):ℝ)):ℝ):ℂ) := (Complex.ofReal_tsum _).symm
    _ = _ := by
      rw [← CatalanCore.Li2.Port.Li2.parameterG_cast_eq_series z hz Q,hc]
      rfl
end CatalanCore.Li2.Decay
#print axioms CatalanCore.Li2.Decay.parameterU_complex_series



namespace CatalanCore.Li2.Decay

theorem rational_pole_series (z : ℚ) (hz : ValidZ (z:ℝ)) (j : ℕ) :
    Summable (fun m : ℕ => (z:ℂ)^(m+1)/(((m+j+1:ℕ):ℂ))^2) ∧
      (∑' m : ℕ, (z:ℂ)^(m+1)/(((m+j+1:ℕ):ℂ))^2)=
        (z:ℂ)⁻¹^j*((li2 (z:ℝ):ℂ)-(CatalanCore.Li2.Port.Li2.parameterTau z j:ℂ)) := by
  have hc (q : ℚ) : ((q:ℝ):ℂ)=(q:ℂ) := map_ratCast Complex.ofRealHom q
  let f : ℕ → ℝ := fun m => (z:ℝ)^(m+1)/((m:ℝ)+j+1)^2
  have hg : Summable (fun m : ℕ => |(z:ℝ)|^(m+1)) :=
    (summable_nat_add_iff 1).mpr (summable_geometric_of_abs_lt_one (by simpa only [abs_abs] using hz.2))
  have hs : Summable f := by
    apply hg.of_norm_bounded
    intro m
    rw [Real.norm_eq_abs]
    dsimp only [f]
    rw [abs_div,abs_pow,abs_pow,abs_of_nonneg (by positivity : 0 ≤ (m:ℝ)+j+1)]
    exact div_le_self (by positivity) (by
      have hm := Nat.cast_nonneg m (α := ℝ)
      have hj := Nat.cast_nonneg j (α := ℝ)
      nlinarith)
  have hterm (m : ℕ) : ((f m:ℝ):ℂ)=(z:ℂ)^(m+1)/(((m+j+1:ℕ):ℂ))^2 := by
    dsimp only [f]
    push_cast <;> rfl
  have hsC : Summable (fun m : ℕ => (z:ℂ)^(m+1)/(((m+j+1:ℕ):ℂ))^2) :=
    (Complex.summable_ofReal.mpr hs).congr hterm
  have htau : (CatalanCore.Li2.Port.Li2.parameterTau z j:ℝ)=
      ∑ b ∈ Finset.range j, (z:ℝ)^(b+1)/((b:ℝ)+1)^2 := by
    rw [CatalanCore.Li2.Port.Li2.parameterTau_eq_range]
    push_cast <;> rfl
  refine ⟨hsC,?_⟩
  calc
    _ = ∑' m : ℕ, ((f m:ℝ):ℂ) := tsum_congr (fun m => (hterm m).symm)
    _ = ((∑' m : ℕ, f m:ℝ):ℂ) := (Complex.ofReal_tsum _).symm
    _ = _ := by
      change ((∑' m : ℕ, (z:ℝ)^(m+1)/((m:ℝ)+j+1)^2 : ℝ):ℂ)= _
      rw [shifted_li2_sum (z:ℝ) hz j,← htau]
      push_cast <;> rfl
end CatalanCore.Li2.Decay
#print axioms CatalanCore.Li2.Decay.rational_pole_series


namespace CatalanCore.Li2.Decay
open Polynomial

theorem monomial_lattice_sum (z : ℚ) (hz : ValidZ (z:ℝ)) (n k : ℕ) :
    Summable (fun m : ℕ => (z:ℂ)^(m+1)*
      deriv (fun u : ℂ => u*weight n u*(Polynomial.X^k).eval u) (((m+1:ℕ):ℂ))) ∧
    (∑' m : ℕ, (z:ℂ)^(m+1)*
      deriv (fun u : ℂ => u*weight n u*(Polynomial.X^k).eval u) (((m+1:ℕ):ℂ)))=
      (CatalanCore.Li2.Port.Li2.parameterU z (P0.polynomialPart n k):ℂ)+
        ∑ j ∈ Finset.Icc 1 (4*n), (P0.residue n k j:ℂ)*(j:ℂ)*(z:ℂ)⁻¹^j*
          ((li2 (z:ℝ):ℂ)-(CatalanCore.Li2.Port.Li2.parameterTau z j:ℂ)) := by
  let Q := (Polynomial.X*P0.polynomialPart n k).derivative
  let a : ℕ → ℂ := fun j => (P0.residue n k j:ℂ)*(j:ℂ)
  let p : ℕ → ℕ → ℂ := fun j m => a j*((z:ℂ)^(m+1)/(((m+j+1:ℕ):ℂ))^2)
  have hpoly := parameterU_complex_series z (by simpa only [Real.norm_eq_abs] using hz.2) (P0.polynomialPart n k)
  have hp : ∀ j ∈ Finset.Icc 1 (4*n), Summable (p j) := by
    intro j hj
    exact (rational_pole_series z hz j).1.mul_left (a j)
  have hpsum := summable_sum hp
  have hterm (m : ℕ) : (z:ℂ)^(m+1)*
      deriv (fun u : ℂ => u*weight n u*(Polynomial.X^k).eval u) (((m+1:ℕ):ℂ))=
      (z:ℂ)^(m+1)*Q.aeval (((m+1:ℕ):ℂ))+
        ∑ j ∈ Finset.Icc 1 (4*n), p j m := by
    rw [weighted_monomial_deriv n k _ (by simp only [Complex.natCast_re]; positivity),mul_add,Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    dsimp only [p,a]
    push_cast
    ring
  have hs := (hpoly.1.add hpsum).congr (fun m => (hterm m).symm)
  refine ⟨hs,?_⟩
  calc
    _ = ∑' m : ℕ, ((z:ℂ)^(m+1)*Q.aeval (((m+1:ℕ):ℂ))+
        ∑ j ∈ Finset.Icc 1 (4*n), p j m) := tsum_congr hterm
    _ = (∑' m : ℕ, (z:ℂ)^(m+1)*Q.aeval (((m+1:ℕ):ℂ)))+
        ∑ j ∈ Finset.Icc 1 (4*n), ∑' m : ℕ, p j m := by
      rw [Summable.tsum_add hpoly.1 hpsum, Summable.tsum_finsetSum hp]
    _ = _ := by
      rw [hpoly.2]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      dsimp only [p]
      rw [tsum_mul_left,(rational_pole_series z hz j).2]
      dsimp only [a]
      ring
end CatalanCore.Li2.Decay
#print axioms CatalanCore.Li2.Decay.monomial_lattice_sum


namespace CatalanCore.Li2.Decay
open Polynomial

theorem port_residue_complex (n k j : ℕ) :
    (P0.residue n k j:ℂ)=(-(j:ℂ))^k*Dprod n (-(j:ℂ))^3/
      (∏ l ∈ (Finset.Icc 1 (4*n)).erase j, (-(j:ℂ)+(l:ℂ))) := by
  have hD (m : ℕ) : (((P0.D m).eval (-(j:ℚ)):ℚ):ℂ)=Dprod m (-(j:ℂ)) := by
    rw [CatalanCore.Li2.Port.Li2.D_eval_eq_prod]
    push_cast
    apply Finset.prod_congr rfl
    intro l hl
    ring
  unfold P0.residue CatalanCore.Li2.Port.Li2.residue CatalanCore.Li2.Port.Li2.numerator
  simp only [eval_mul,eval_pow,eval_X]
  push_cast
  rw [hD]
  congr 1
  apply Finset.prod_congr rfl
  intro l hl
  ring

theorem port_residue_atom (n k j : ℕ) (hj : j ∈ Finset.Icc (n+1) (4*n)) :
    (P0.residue n k j:ℂ)=(-(j:ℂ))^k*(residue n j:ℂ) := by
  rw [port_residue_complex,mul_div_assoc,residue_value n j hj]

theorem port_residue_zero (n k j : ℕ) (hj1 : 1 ≤ j) (hjN : j ≤ n) :
    (P0.residue n k j:ℂ)=0 := by
  have hh : Dprod n (-(j:ℂ))=0 := by
    apply Finset.prod_eq_zero (Finset.mem_Icc.mpr ⟨hj1,hjN⟩)
    simp only [neg_add_cancel]
  rw [port_residue_complex,hh]
  simp only [zero_pow (by decide : (3:ℕ) ≠ 0),mul_zero,zero_div]

theorem atom_monomial_sum (z : ℚ) (hz : z ≠ 0) (n k : ℕ) :
    (∑ j ∈ Finset.Icc (n+1) (4*n), (atomWeight (z:ℝ) n j:ℂ)*(Polynomial.X^k).eval (-(j:ℂ)))=
      ∑ j ∈ Finset.Icc 1 (4*n), (P0.residue n k j:ℂ)*(j:ℂ)*(z:ℂ)⁻¹^j := by
  classical
  have hsub : Finset.Icc (n+1) (4*n) ⊆ Finset.Icc 1 (4*n) := by
    intro j hj
    have hh := Finset.mem_Icc.mp hj
    exact Finset.mem_Icc.mpr ⟨by omega,hh.2⟩
  symm
  calc
    _ = ∑ j ∈ Finset.Icc (n+1) (4*n), (P0.residue n k j:ℂ)*(j:ℂ)*(z:ℂ)⁻¹^j := by
      symm
      apply Finset.sum_subset hsub
      intro j hj hnot
      have hh := Finset.mem_Icc.mp hj
      have hjN : j ≤ n := by
        have ht : ¬(n+1 ≤ j ∧ j ≤ 4*n) := by simpa only [Finset.mem_Icc] using hnot
        omega
      rw [port_residue_zero n k j hh.1 hjN,zero_mul,zero_mul]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [port_residue_atom n k j hj]
      simp only [atomWeight,eval_pow,eval_X]
      push_cast
      rw [zpow_neg,zpow_natCast,inv_pow]
      ring
end CatalanCore.Li2.Decay
#print axioms CatalanCore.Li2.Decay.atom_monomial_sum


namespace CatalanCore.Li2.Decay
open Polynomial

theorem functional_monomial_eq (z : ℚ) (hz : ValidZ (z:ℝ)) (n k : ℕ) (t : ℝ) :
    functional (z:ℝ) n t (Polynomial.X^k)=
      (CatalanCore.Li2.Port.Unified.ParameterFamily.intercept z n k:ℂ)+
        ((li2 (z:ℝ):ℂ)+(t:ℂ))*(CatalanCore.Li2.Port.Unified.ParameterFamily.slope z n k:ℂ) := by
  have hz0 : z ≠ 0 := by
    intro he
    have hh := hz.1
    simp only [he,Rat.cast_zero,abs_zero,lt_self_iff_false] at hh
  have hc : (((z:ℝ):ℂ))=(z:ℂ) := map_ratCast Complex.ofRealHom z
  let r : ℕ → ℂ := fun j => (P0.residue n k j:ℂ)*(j:ℂ)*(z:ℂ)⁻¹^j
  have hS : (CatalanCore.Li2.Port.Unified.ParameterFamily.slope z n k:ℂ)=
      ∑ j ∈ Finset.Icc 1 (4*n), r j := by
    unfold CatalanCore.Li2.Port.Unified.ParameterFamily.slope
    dsimp only [r,P0.residue]
    push_cast <;> rfl
  have hI : (CatalanCore.Li2.Port.Unified.ParameterFamily.intercept z n k:ℂ)=
      (CatalanCore.Li2.Port.Li2.parameterU z (P0.polynomialPart n k):ℂ)-
        ∑ j ∈ Finset.Icc 1 (4*n), r j*(CatalanCore.Li2.Port.Li2.parameterTau z j:ℂ) := by
    unfold CatalanCore.Li2.Port.Unified.ParameterFamily.intercept
    dsimp only [r,P0.residue,P0.polynomialPart]
    push_cast <;> rfl
  rw [functional]
  simp only [hc]
  rw [(monomial_lattice_sum z hz n k).2,atom_monomial_sum z hz0 n k,hI,hS]
  change (CatalanCore.Li2.Port.Li2.parameterU z (P0.polynomialPart n k):ℂ)+
    (∑ j ∈ Finset.Icc 1 (4*n), r j*((li2 (z:ℝ):ℂ)-(CatalanCore.Li2.Port.Li2.parameterTau z j:ℂ)))+
      (t:ℂ)*(∑ j ∈ Finset.Icc 1 (4*n), r j)= _
  have he : (∑ j ∈ Finset.Icc 1 (4*n), r j*((li2 (z:ℝ):ℂ)-(CatalanCore.Li2.Port.Li2.parameterTau z j:ℂ)))=
      (li2 (z:ℝ):ℂ)*(∑ j ∈ Finset.Icc 1 (4*n), r j)-
        ∑ j ∈ Finset.Icc 1 (4*n), r j*(CatalanCore.Li2.Port.Li2.parameterTau z j:ℂ) := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib,Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [he]
  ring
end CatalanCore.Li2.Decay
#print axioms CatalanCore.Li2.Decay.functional_monomial_eq


namespace CatalanCore.Li2.Decay
open Polynomial
open CatalanCore.Li2.Port.Unified.ParameterFamily
noncomputable def normFactor (n : ℕ) : ℝ :=
  ((((4*n).factorial:ℝ)/(n.factorial:ℝ)^3)^(2*n))/
    ∏ i ∈ Finset.range (2*n), (i.factorial:ℝ)^2
noncomputable def rawQ (z : ℝ) (n : ℕ) (X : ℝ) : ℝ :=
  (Matrix.det (fun i j : Fin (2*n) =>
    functional z n (X-li2 z) (Polynomial.X^(i.val+j.val)))).re
noncomputable def normalizedQ (z : ℝ) (n : ℕ) (X : ℝ) : ℝ := normFactor n*rawQ z n X

theorem family_eval_matrix (z : ℚ) (n : ℕ) (x : ℝ) :
    (CatalanCore.Li2.li2Family z).evalR n x=normFactor n*
      ((CatalanCore.Li2.Port.Unified.ParameterFamily.A z n).map (Rat.castHom ℝ)+x • (CatalanCore.Li2.Port.Unified.ParameterFamily.B z n).map (Rat.castHom ℝ)).det := by
  have heval : (Q z n).aeval x=
      ((CatalanCore.Li2.Port.Unified.ParameterFamily.A z n).map (Rat.castHom ℝ)+x • (CatalanCore.Li2.Port.Unified.ParameterFamily.B z n).map (Rat.castHom ℝ)).det := by
    change (aeval x : ℚ[X] →ₐ[ℚ] ℝ).toRingHom
      (((Polynomial.X : ℚ[X]) • (CatalanCore.Li2.Port.Unified.ParameterFamily.B z n).map C+(CatalanCore.Li2.Port.Unified.ParameterFamily.A z n).map C).det)= _
    rw [RingHom.map_det]
    congr 1
    apply Matrix.ext
    intro i j
    simp only [AlgHom.mapMatrix_apply,RingHom.mapMatrix_apply,Matrix.map_apply,
      Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,map_add,map_mul,aeval_C,aeval_X]
    change (Polynomial.X : ℚ[X]).aeval x*(C (CatalanCore.Li2.Port.Unified.ParameterFamily.B z n i j)).aeval x+
      (C (CatalanCore.Li2.Port.Unified.ParameterFamily.A z n i j)).aeval x=
        (CatalanCore.Li2.Port.Unified.ParameterFamily.A z n i j:ℝ)+x*(CatalanCore.Li2.Port.Unified.ParameterFamily.B z n i j:ℝ)
    simp only [aeval_X,aeval_C]
    change x*(CatalanCore.Li2.Port.Unified.ParameterFamily.B z n i j:ℝ)+(CatalanCore.Li2.Port.Unified.ParameterFamily.A z n i j:ℝ)=(CatalanCore.Li2.Port.Unified.ParameterFamily.A z n i j:ℝ)+x*(CatalanCore.Li2.Port.Unified.ParameterFamily.B z n i j:ℝ)
    ring
  have hn : (((CatalanCore.Li2.Port.Li2.Sn n)^(2*n)/CatalanCore.Li2.Port.Li2.Fn n:ℚ):ℝ)=normFactor n := by
    unfold CatalanCore.Li2.Port.Li2.Sn CatalanCore.Li2.Port.Li2.Fn normFactor
    push_cast <;> rfl
  change (Qtilde z n).aeval x= _
  rw [Qtilde,map_mul,aeval_C,heval]
  rw [show (algebraMap ℚ ℝ) (CatalanCore.Li2.Port.Li2.Sn n^(2*n)/CatalanCore.Li2.Port.Li2.Fn n)=
    (((CatalanCore.Li2.Port.Li2.Sn n)^(2*n)/CatalanCore.Li2.Port.Li2.Fn n:ℚ):ℝ) from rfl,hn]

theorem normalizedQ_eq_family (z : ℚ) (hz : ValidZ (z:ℝ)) (n : ℕ) (hn : 1 ≤ n) (X : ℝ) :
    normalizedQ (z:ℝ) n X=(CatalanCore.Li2.li2Family z).evalR n X := by
  let M : Matrix (Fin (2*n)) (Fin (2*n)) ℝ :=
    (CatalanCore.Li2.Port.Unified.ParameterFamily.A z n).map (Rat.castHom ℝ)+X • (CatalanCore.Li2.Port.Unified.ParameterFamily.B z n).map (Rat.castHom ℝ)
  have hm : (fun i j : Fin (2*n) => functional (z:ℝ) n (X-li2 (z:ℝ))
      (Polynomial.X^(i.val+j.val)))=M.map Complex.ofRealHom := by
    apply Matrix.ext
    intro i j
    rw [functional_monomial_eq z hz]
    simp only [M,Matrix.map_apply,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,Rat.coe_castHom,map_add,map_mul,map_ratCast,Complex.ofRealHom_eq_coe,
      CatalanCore.Li2.Port.Unified.ParameterFamily.A,CatalanCore.Li2.Port.Unified.ParameterFamily.B]
    push_cast
    ring
  have hdet : (M.map Complex.ofRealHom).det=(M.det:ℂ) := (RingHom.map_det Complex.ofRealHom M).symm
  rw [normalizedQ,rawQ,hm,hdet,Complex.ofReal_re,family_eval_matrix]
end CatalanCore.Li2.Decay
#print axioms CatalanCore.Li2.Decay.normalizedQ_eq_family


namespace CatalanCore.Li2.Decay

theorem rational_sign_eq (z : ℚ) (hz : z ≠ 0) :
    CatalanCore.Li2.Uniform.signOf (z:ℝ)=Int.sign z.num := by
  have hzR : (z:ℝ) ≠ 0 := by exact_mod_cast hz
  unfold CatalanCore.Li2.Uniform.signOf
  by_cases hp : 0 < (z:ℝ)
  · have hpQ : 0 < z := by exact_mod_cast hp
    rw [if_pos hp,Int.sign_eq_one_of_pos (Rat.num_pos.mpr hpQ)]
  · have hnR : (z:ℝ) < 0 := by
      rcases lt_or_gt_of_ne hzR with hh | hh
      · exact hh
      · exact (hp hh).elim
    have hnQ : z < 0 := by exact_mod_cast hnR
    have hh := Rat.num_pos.mpr (neg_pos.mpr hnQ)
    rw [Rat.num_neg_eq_neg_num] at hh
    rw [if_neg hp,Int.sign_eq_neg_one_of_neg (by omega : z.num < 0)]

theorem window_decay_to_scaled (Fam : CatalanCore.PolyFamily)
    (scale : Fam.ι → ℕ) (Q : ℕ → ℝ → ℝ) (D ρ : ℝ)
    (hQ : WindowDecay Q Fam.const D ρ)
    (heval : ∀ i, Fam.Adm i → ∀ x : ℝ, Fam.evalR i x=Q (scale i) x) :
    CatalanCore.Uniform.HasScaledDecay Fam scale D ρ := by
  intro ε hε
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hQ ε hε)
  refine ⟨N,?_⟩
  intro i hi hNi t ht
  rw [heval i hi]
  apply hN (scale i) hNi t
  apply ht.trans
  apply Real.exp_le_exp.mpr
  nlinarith [Nat.cast_nonneg (scale i) (α := ℝ)]

theorem family_window_bound (z : ℚ) (hz : ValidZ (z:ℝ)) (D ρ : ℝ)
    (hQ : WindowDecay (normalizedQ (z:ℝ)) (li2 (z:ℝ)) D ρ) :
    CatalanCore.Li2.Uniform.WindowBound z ρ D := by
  apply window_decay_to_scaled (CatalanCore.Li2.li2Family z) CatalanCore.Li2.scale
    (normalizedQ (z:ℝ)) D ρ hQ
  intro n hn x
  exact (normalizedQ_eq_family z hz n hn x).symm

theorem family_decay_of_window (z : ℚ) (hz0 : z ≠ 0) (hz1 : |(z:ℝ)| < 1)
    (F : Frame) (d : DualDatum) (ρ θ D : ℝ)
    (hQ : WindowDecay (normalizedQ (z:ℝ)) (li2 (z:ℝ)) (dualValue (z:ℝ) ρ F d.σ θ) ρ)
    (hD : D ≤ CatalanCore.Li2.Uniform.dual F (Int.sign z.num)
      (Real.log (1/|(z:ℝ)|)) ρ d θ) :
    CatalanCore.Li2.Uniform.WindowBound z ρ D := by
  have hzR : (z:ℝ) ≠ 0 := by exact_mod_cast hz0
  have hz : ValidZ (z:ℝ) := ⟨abs_pos.mpr hzR,hz1⟩
  have hD' : D ≤ dualValue (z:ℝ) ρ F d.σ θ := by
    rw [CatalanCore.Li2.Uniform.decay_dual_eq (z:ℝ) ρ hz F d θ,rational_sign_eq z hz0]
    exact hD
  exact family_window_bound z hz D ρ (hQ.mono hD')
end CatalanCore.Li2.Decay
#print axioms CatalanCore.Li2.Decay.rational_sign_eq
#print axioms CatalanCore.Li2.Decay.family_window_bound
#print axioms CatalanCore.Li2.Decay.family_decay_of_window



namespace CatalanCore.Li2.Decay
theorem normFactor_log (n : ℕ) : Real.log (normFactor n)=
    2*(n:ℝ)*(Real.log ((4*n).factorial)-3*Real.log (n.factorial))-
      2*∑ i ∈ Finset.range (2*n), Real.log (i.factorial) := by
  have hp : 0 < ∏ i ∈ Finset.range (2*n), (i.factorial:ℝ)^2 :=
    Finset.prod_pos fun i hi => by positivity
  unfold normFactor
  rw [Real.log_div (by positivity) hp.ne',Real.log_pow,
    Real.log_div (by positivity) (by positivity),Real.log_pow,
    Real.log_prod (fun i hi => by positivity)]
  simp only [Real.log_pow,← Finset.mul_sum]
  push_cast
  ring

theorem normalization_asymptotic :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      |Real.log (normFactor n)-(-2*(n:ℝ)^2*Real.log n+(12*Real.log 2+4)*(n:ℝ)^2)| ≤
        C*(n:ℝ)*Real.log ((n:ℝ)+1) := by
  refine ⟨100,by norm_num,?_⟩
  intro n hn
  have hnR : 1 ≤ (n:ℝ) := by exact_mod_cast hn
  have hn0 : 0 < (n:ℝ) := by linarith
  have hlog2 : 1/2 ≤ Real.log 2 := by
    have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at hh ⊢
    exact hh
  have hlogn : 0 ≤ Real.log (n:ℝ) := Real.log_nonneg hnR
  have hlognL : Real.log (n:ℝ) ≤ Real.log ((n:ℝ)+1) := Real.log_le_log hn0 (by linarith)
  have hlog2L : Real.log 2 ≤ Real.log ((n:ℝ)+1) := Real.log_le_log (by norm_num) (by linarith)
  have hL : 1/2 ≤ Real.log ((n:ℝ)+1) := hlog2.trans hlog2L
  have hlog4 : Real.log (4:ℝ)=2*Real.log 2 := by
    rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow]
    norm_num
  have hlog4n : Real.log (((4*n:ℕ):ℝ))=2*Real.log 2+Real.log n := by
    simp only [Nat.cast_mul,Nat.cast_ofNat]
    rw [Real.log_mul (by norm_num) hn0.ne',hlog4]
  have hlog2n : Real.log (((2*n:ℕ):ℝ))=Real.log 2+Real.log n := by
    rw [Nat.cast_mul,Real.log_mul (by norm_num) hn0.ne']
    norm_num
  have hnlo := CatalanCore.Zeta5.Energy.log_factorial_ge n
  have hnup := CatalanCore.Zeta5.Energy.log_factorial_le hn
  have h4lo := CatalanCore.Zeta5.Energy.log_factorial_ge (4*n)
  have h4up := CatalanCore.Zeta5.Energy.log_factorial_le (show 1 ≤ 4*n by omega)
  have hS := CatalanCore.Tools.FactorialProducts.sum_log_factorial_error (2*n) (by omega)
  rw [hlog4n] at h4lo h4up
  rw [hlog2n,abs_le] at hS
  norm_num only [Nat.cast_mul,Nat.cast_ofNat] at h4lo h4up hS
  have h4lo' := mul_le_mul_of_nonneg_left h4lo (by positivity : 0 ≤ 2*(n:ℝ))
  have h4up' := mul_le_mul_of_nonneg_left h4up (by positivity : 0 ≤ 2*(n:ℝ))
  have hnlo' := mul_le_mul_of_nonneg_left hnlo (by positivity : 0 ≤ 6*(n:ℝ))
  have hnup' := mul_le_mul_of_nonneg_left hnup (by positivity : 0 ≤ 6*(n:ℝ))
  have hlogn' := mul_le_mul_of_nonneg_left hlognL (by positivity : 0 ≤ (n:ℝ))
  have hlog2' := mul_le_mul_of_nonneg_left hlog2L (by positivity : 0 ≤ (n:ℝ))
  have hL' := mul_le_mul_of_nonneg_left hL (by positivity : 0 ≤ (n:ℝ))
  rw [normFactor_log,abs_le]
  constructor <;> nlinarith [hS.1,hS.2]
end CatalanCore.Li2.Decay
#print axioms CatalanCore.Li2.Decay.normalization_asymptotic



namespace CatalanCore.Li2.Decay
open Polynomial

theorem li2_window_decay (z : ℝ) (hz : ValidZ z) (F : Frame) (g : CatalanCore.Li2.Uniform.FrameGeometry F)
    (d : DualDatum) (θ ρ : ℝ) (hρ : 0 < ρ) (hF : FreeBound z F d θ) :
    WindowDecay (normalizedQ z) (li2 z) (dualValue z ρ F d.σ θ) ρ := by
  obtain ⟨A,hA,hgrowth⟩ := HeineSource.source_det_growth z hz F g d θ ρ hρ hF
  obtain ⟨H,hH,hnormal⟩ := normalization_asymptotic
  intro ε hε
  let B := H+2*|Real.log A| +5
  have hB : 0 < B := by dsimp only [B]; positivity
  have hε2 : 0 < ε/2 := by positivity
  have hη : 0 < (ε/2)/B := div_pos hε2 hB
  filter_upwards [hgrowth (ε/2) hε2,analyticError_small 1 d ((ε/2)/B) hη,
    eventually_ge_atTop (1:ℕ)] with n hdet hsmall hn
  intro t ht
  have hnR1 : 1 ≤ (n:ℝ) := by exact_mod_cast hn
  have hnR : 0 < (n:ℝ) := by linarith
  have hlogn : 0 ≤ Real.log (n:ℝ) := Real.log_nonneg hnR1
  have hnlog : 0 ≤ (n:ℝ)*Real.log n := mul_nonneg hnR.le hlogn
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog51 : 1/2 ≤ Real.log 51 := by
    have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<51)
    norm_num at hh
    linarith
  have hlogadd : Real.log ((n:ℝ)+1) ≤ 1+Real.log n := by
    have hh := Real.log_le_log (by positivity : (0:ℝ)<(n:ℝ)+1)
      (show (n:ℝ)+1 ≤ 2*(n:ℝ) by linarith)
    rw [Real.log_mul (by norm_num : (2:ℝ)≠0) hnR.ne'] at hh
    have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    linarith
  have hAE : (n:ℝ)+(n:ℝ)*Real.log n ≤ analyticError 1 d n := by
    have h1 := mul_le_mul_of_nonneg_right
      (show (1:ℝ) ≤ 2*Real.log 51+Real.log 2 by linarith) hnR.le
    have h2 : (n:ℝ)*Real.log n ≤ (12+2*(1:ℝ))*(n:ℝ)*Real.log n := by nlinarith
    have hhold : 0 ≤ 4*(d.holderConstant:ℝ)*(n:ℝ)^(2-2*d.holderExponent) := by positivity
    unfold analyticError
    simp only [Real.log_one,mul_zero,add_zero]
    nlinarith
  have hError : H*(n:ℝ)*Real.log ((n:ℝ)+1)+2*(n:ℝ)*Real.log A+4*(n:ℝ)*Real.log n ≤
      (ε/2)*(n:ℝ)^2 := by
    have hN := mul_le_mul_of_nonneg_left hlogadd (mul_nonneg hH.le hnR.le)
    have hA' := mul_le_mul_of_nonneg_left (le_abs_self (Real.log A)) (by positivity : (0:ℝ)≤2*(n:ℝ))
    have hlinear : H*(n:ℝ)*Real.log ((n:ℝ)+1)+2*(n:ℝ)*Real.log A+4*(n:ℝ)*Real.log n ≤
        (H+2*|Real.log A|)*(n:ℝ)+(H+4)*((n:ℝ)*Real.log n) := by nlinarith
    have h1 := mul_le_mul_of_nonneg_right (show H+2*|Real.log A| ≤ B by dsimp only [B]; linarith) hnR.le
    have h2 := mul_le_mul_of_nonneg_right (show H+4 ≤ B by dsimp only [B]; linarith [abs_nonneg (Real.log A)]) hnlog
    have hE : H*(n:ℝ)*Real.log ((n:ℝ)+1)+2*(n:ℝ)*Real.log A+4*(n:ℝ)*Real.log n ≤
        B*((n:ℝ)+(n:ℝ)*Real.log n) := by nlinarith
    have hE2 := mul_le_mul_of_nonneg_left hAE hB.le
    have hSB := mul_le_mul_of_nonneg_left hsmall hB.le
    have he : B*(((ε/2)/B)*(n:ℝ)^2)=(ε/2)*(n:ℝ)^2 := by field_simp
    rw [he] at hSB
    exact hE.trans (hE2.trans hSB)
  have hDen : 0 < ∏ i ∈ Finset.range (2*n), (i.factorial:ℝ)^2 :=
    Finset.prod_pos (fun i hi => by positivity)
  have hNormPos : 0 < normFactor n := by unfold normFactor; positivity
  have hNormLog : Real.log (normFactor n) ≤
      -2*(n:ℝ)^2*Real.log n+(12*Real.log 2+4)*(n:ℝ)^2+H*(n:ℝ)*Real.log ((n:ℝ)+1) := by
    have hh := (abs_le.mp (hnormal n hn)).2
    linarith
  have hNormExp := Real.exp_le_exp.mpr hNormLog
  rw [Real.exp_log hNormPos] at hNormExp
  have hcast : 2*(n:ℝ)=((2*n:ℕ):ℝ) := by push_cast; ring
  have hPow : (A*(n:ℝ)^2)^(2*n)=Real.exp (2*(n:ℝ)*Real.log A+4*(n:ℝ)*Real.log n) := by
    calc
      _=Real.exp ((2*(n:ℝ))*(Real.log A+2*Real.log n)) := by
        rw [hcast,Real.exp_nat_mul,Real.exp_add,Real.exp_log hA,
          show (2:ℝ)*Real.log (n:ℝ)=Real.log (n:ℝ)*2 by ring,
          ← Real.rpow_def_of_pos hnR,Real.rpow_two]
      _=_ := by congr 1; ring
  have hRaw : |normalizedQ z n (li2 z+t)| ≤ normFactor n*
      ‖Matrix.det (fun i j : Fin (2*n) => functional z n t (Polynomial.X^(i.val+j.val)))‖ := by
    unfold normalizedQ rawQ
    rw [show li2 z+t-li2 z=t by ring,abs_mul,abs_of_pos hNormPos]
    exact mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) hNormPos.le
  calc
    _ ≤ normFactor n*‖Matrix.det (fun i j : Fin (2*n) => functional z n t (Polynomial.X^(i.val+j.val)))‖ := hRaw
    _ ≤ Real.exp (-2*(n:ℝ)^2*Real.log n+(12*Real.log 2+4)*(n:ℝ)^2+H*(n:ℝ)*Real.log ((n:ℝ)+1))*
        (Real.exp ((n:ℝ)^2*(I d.σ+2*θ+2*latPenalty z F d.σ θ+atomPenalty z ρ d.σ θ+ε/2)+
          2*(n:ℝ)^2*Real.log n)*(A*(n:ℝ)^2)^(2*n)) :=
      mul_le_mul hNormExp (hdet t ht) (norm_nonneg _) (Real.exp_pos _).le
    _ = Real.exp ((-dualValue z ρ F d.σ θ+ε/2)*(n:ℝ)^2+
        H*(n:ℝ)*Real.log ((n:ℝ)+1)+2*(n:ℝ)*Real.log A+4*(n:ℝ)*Real.log n) := by
      rw [hPow,← Real.exp_add,← Real.exp_add]
      congr 1
      unfold dualValue
      ring
    _ ≤ Real.exp (-(dualValue z ρ F d.σ θ-ε)*(n:ℝ)^2) := by
      apply Real.exp_le_exp.mpr
      nlinarith

theorem li2_family_decay (z : ℚ) (hz0 : z ≠ 0) (hz1 : |(z:ℝ)| < 1)
    (F : CatalanCore.Li2.Uniform.DualFrame) (g : CatalanCore.Li2.Uniform.FrameGeometry F)
    (d : CatalanCore.Li2.Uniform.DualDatum) (ρ θ D : ℝ) (hρ : 0 < ρ)
    (hadm : CatalanCore.Li2.Uniform.Admissible F (Int.sign z.num) (Real.log (1/|(z:ℝ)|)) d θ)
    (hcap : CatalanCore.Li2.Uniform.CapIntegrable F (Int.sign z.num) (Real.log (1/|(z:ℝ)|)) ρ d θ)
    (hD : D ≤ CatalanCore.Li2.Uniform.dual F (Int.sign z.num) (Real.log (1/|(z:ℝ)|)) ρ d θ) :
    CatalanCore.Li2.Uniform.WindowBound z ρ D := by
  have hzR : (z:ℝ) ≠ 0 := by exact_mod_cast hz0
  have hz : ValidZ (z:ℝ) := ⟨abs_pos.mpr hzR,hz1⟩
  have hA : CatalanCore.Li2.Uniform.Admissible F (CatalanCore.Li2.Uniform.signOf (z:ℝ))
      (Real.log (1/|(z:ℝ)|)) d θ := by
    rw [rational_sign_eq z hz0]
    exact hadm
  have hF := (CatalanCore.Li2.Uniform.decay_freeBound_iff (z:ℝ) hz F d θ).mpr hA
  exact family_decay_of_window z hz0 hz1 F d ρ θ D (li2_window_decay (z:ℝ) hz F g d θ ρ hρ hF) hD
end CatalanCore.Li2.Decay
#print axioms CatalanCore.Li2.Decay.li2_window_decay
#print axioms CatalanCore.Li2.Decay.li2_family_decay
