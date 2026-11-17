module
public import CatalanCore.Li2.Uniform.Spec
@[expose] public section
/-! Geometric bridges for the canonical polygonal frame and its modified oriented contour. Exact W1 rows. -/
set_option Elab.async false
open MeasureTheory Set Filter Complex
open scoped Topology
namespace CatalanCore.Li2.Uniform

private theorem pieceSet_re_nonneg (p : CatalanCore.Decay.CurveFamily.Piece)
    (ha : 0 ≤ p.a.re) (hb : if p.ray then 0 ≤ p.D.re else 0 ≤ (p.a+p.D).re)
    (u : ℂ) (hu : u ∈ pieceSet p) : 0 ≤ u.re := by
  rcases hu with ⟨t,ht,rfl⟩
  change 0 ≤ (p.a + (t:ℂ)*p.D).re
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  by_cases hp : p.ray = true
  · simp only [pieceSet, hp, ↓reduceIte] at ht
    simp only [hp, ↓reduceIte] at hb
    exact add_nonneg ha (mul_nonneg ht hb)
  · have hf : p.ray = false := Bool.eq_false_iff.mpr hp
    simp only [hf, Bool.false_eq_true, ↓reduceIte, mem_Icc] at ht hb
    have h1 := mul_nonneg (sub_nonneg.mpr ht.2) ha
    have h2 := mul_nonneg ht.1 hb
    simp only [Complex.add_re] at h2
    nlinarith

private theorem polygon_vertex_re_nonneg (p : PolygonFrame) (j : ℕ) (hj : j ≤ p.edges) :
    0 ≤ (p.vertex j).re := by
  by_cases hz : j = 0
  · subst j
    rw [p.initial, Complex.ofReal_re]
    exact p.nonneg
  · exact (p.real_pos j (by omega) hj).le

private theorem polygon_pieces_re_nonneg (p : PolygonFrame) (u : ℂ)
    (hu : u ∈ piecesSet (polygonPieces p)) : 0 ≤ u.re := by
  simp only [piecesSet, mem_iUnion] at hu
  rcases hu with ⟨q,hq,hu⟩
  simp only [polygonPieces, List.mem_append, List.mem_map, List.mem_singleton] at hq
  rcases hq with ⟨j,hj,rfl⟩ | rfl
  · have hj' : j < p.edges := List.mem_range.mp hj
    apply pieceSet_re_nonneg _ (polygon_vertex_re_nonneg p j (by omega)) _ u hu
    simp only [Bool.false_eq_true, ↓reduceIte]
    convert polygon_vertex_re_nonneg p (j+1) (by omega) using 1 <;> simp
  · apply pieceSet_re_nonneg _ (polygon_vertex_re_nonneg p p.edges le_rfl) _ u hu
    simp

theorem goodFrame_halfplane (F : DualFrame) (g : FrameGeometry F) (s : ℤ) :
    (∀ u ∈ F.free s, 0 ≤ u.re) ∧ (∀ x ∈ F.lattice, 0 ≤ x) := by
  refine ⟨?_,F.lattice_mem⟩
  cases g with
  | pure hp hl hf => simp [hf]
  | polygon p hp hl hf =>
    rw [hf]
    intro u hu
    rcases hu with hu | hu
    · rcases hu with hu | ⟨v,hv,rfl⟩
      · exact polygon_pieces_re_nonneg p u hu
      · simpa using polygon_pieces_re_nonneg p v hv
    · by_cases hs : s=1
      · simp only [hs, ↓reduceIte] at hu
        rcases hu with ⟨x,hx,rfl⟩
        simpa only [Complex.ofReal_re] using p.nonneg.trans hx
      · simp only [hs, ↓reduceIte, mem_empty_iff_false] at hu


private theorem piece_zeta_embedding (p : CatalanCore.Decay.CurveFamily.Piece) (hD : p.D ≠ 0) :
    MeasurableEmbedding p.zeta := by
  have hh := (Homeomorph.addLeft p.a).isClosedEmbedding.comp
    ((Homeomorph.mulRight₀ p.D hD).isClosedEmbedding.comp
      Complex.isUniformEmbedding_ofReal.isClosedEmbedding)
  exact hh.measurableEmbedding

private theorem piece_ae_mem (p : CatalanCore.Decay.CurveFamily.Piece) :
    ∀ᵐ t ∂p.nu, p.zeta t ∈ pieceSet p := by
  by_cases h : p.ray = true
  · change ∀ᵐ t ∂(if p.ray then volume.restrict (Ioi (0:ℝ)) else volume.restrict (Ioc (0:ℝ) 1)), _
    rw [if_pos h]
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact ⟨t, by simpa only [h, ↓reduceIte, mem_Ici] using ht.le, rfl⟩
  · have hf : p.ray = false := Bool.eq_false_iff.mpr h
    change ∀ᵐ t ∂(if p.ray then volume.restrict (Ioi (0:ℝ)) else volume.restrict (Ioc (0:ℝ) 1)), _
    rw [if_neg h]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact ⟨t, by simpa only [hf, Bool.false_eq_true, ↓reduceIte] using ⟨ht.1.le,ht.2⟩, rfl⟩

private theorem pieceArc_supported (p : CatalanCore.Decay.CurveFamily.Piece) :
    pieceArc p (pieceSet p)ᶜ = 0 := by
  by_cases hD : p.D = 0
  · simp only [pieceArc, hD, norm_zero, ENNReal.ofReal_zero, zero_smul, Measure.coe_zero, Pi.zero_apply]
  · rw [pieceArc, Measure.smul_apply, (piece_zeta_embedding p hD).map_apply]
    have hh : p.nu (p.zeta ⁻¹' (pieceSet p)ᶜ) = 0 := by
      exact ae_iff.mp (piece_ae_mem p)
    rw [hh, smul_zero]

private theorem piecesArc_supported (ps : List CatalanCore.Decay.CurveFamily.Piece) (S : Set ℂ)
    (hS : ∀ p ∈ ps, pieceSet p ⊆ S) : piecesArc ps Sᶜ = 0 := by
  induction ps with
  | nil => simp [piecesArc]
  | cons p ps ih =>
    have hp : pieceArc p Sᶜ = 0 := measure_mono_null (compl_subset_compl.mpr (hS p (by simp))) (pieceArc_supported p)
    have ht := ih (fun q hq => hS q (by simp [hq]))
    simpa only [piecesArc, List.map_cons, List.sum_cons, Measure.add_apply, hp, ht, add_zero] using
      congrArg (fun x : ENNReal => pieceArc p Sᶜ + x) ht

private theorem pieceSet_conj_subset (p : CatalanCore.Decay.CurveFamily.Piece) :
    pieceSet p.conj ⊆ starRingEnd ℂ '' pieceSet p := by
  intro u hu
  rcases hu with ⟨t,ht,rfl⟩
  refine ⟨p.zeta t, ?_, (CatalanCore.Decay.CurveFamily.Piece.zeta_conj p t).symm⟩
  exact ⟨t,ht,rfl⟩

theorem frame_arc_supported (F : DualFrame) (g : FrameGeometry F) (s : ℤ) :
    arcLength g s (F.free s)ᶜ = 0 := by
  cases g with
  | pure hp hl hf => simp [arcLength]
  | polygon p hp hl hf =>
    rw [hf]
    have hu : piecesArc (polygonPieces p) (polygonFree p s)ᶜ = 0 := by
      apply piecesArc_supported
      intro q hq u hu
      exact Or.inl (Or.inl (by simp only [piecesSet, mem_iUnion]; exact ⟨q,hq,hu⟩))
    have hd : piecesArc ((polygonPieces p).map CatalanCore.Decay.CurveFamily.Piece.conj) (polygonFree p s)ᶜ = 0 := by
      apply piecesArc_supported
      intro q hq u hqu
      rcases List.mem_map.mp hq with ⟨q',hq',rfl⟩
      rcases pieceSet_conj_subset q' hqu with ⟨v,hv,rfl⟩
      exact Or.inl (Or.inr ⟨v,by simp only [piecesSet,mem_iUnion]; exact ⟨q',hq',hv⟩,rfl⟩)
    have hr : (if s=1 then (volume.restrict (Ici p.cut)).map Complex.ofReal else 0) (polygonFree p s)ᶜ = 0 := by
      by_cases hs : s=1
      · rw [if_pos hs, Complex.isUniformEmbedding_ofReal.isClosedEmbedding.measurableEmbedding.map_apply]
        apply ae_iff.mp
        filter_upwards [ae_restrict_mem measurableSet_Ici] with x hx
        exact Or.inr (by simp only [hs, ↓reduceIte]; exact ⟨x,hx,rfl⟩)
      · simp only [hs, ↓reduceIte, Measure.coe_zero, Pi.zero_apply]
    change (piecesArc (polygonPieces p) +
      piecesArc ((polygonPieces p).map CatalanCore.Decay.CurveFamily.Piece.conj) +
      (if s=1 then (volume.restrict (Ici p.cut)).map Complex.ofReal else 0)) (polygonFree p s)ᶜ = 0
    rw [Measure.add_apply, Measure.add_apply, hu, hd, hr, add_zero, add_zero]


private theorem pieceIntegral_norm_le (p : CatalanCore.Decay.CurveFamily.Piece) (f : ℂ → ℂ) :
    ‖pieceIntegral p f‖ ≤ ∫ z, ‖f z‖ ∂pieceArc p := by
  by_cases hD : p.D = 0
  · simp [pieceIntegral,pieceArc,hD]
  · have he : (∫ z, ‖f z‖ ∂pieceArc p) = ‖p.D‖ * (∫ t, ‖f (p.zeta t)‖ ∂p.nu) := by
      rw [pieceArc, integral_smul_measure, (piece_zeta_embedding p hD).integral_map]
      simp only [ENNReal.toReal_ofReal (norm_nonneg _), smul_eq_mul]
    rw [he]
    calc
      ‖pieceIntegral p f‖ ≤ ∫ t, ‖f (p.zeta t)*p.D‖ ∂p.nu := norm_integral_le_integral_norm _
      _ = ‖p.D‖ * (∫ t, ‖f (p.zeta t)‖ ∂p.nu) := by
        simp only [norm_mul]
        rw [integral_mul_const]
        ring

private theorem piecesIntegral_norm_le (ps : List CatalanCore.Decay.CurveFamily.Piece)
    (f : ℂ → ℂ) (hf : Integrable (fun z => ‖f z‖) (piecesArc ps)) :
    ‖(ps.map (fun p => pieceIntegral p f)).sum‖ ≤ ∫ z, ‖f z‖ ∂piecesArc ps := by
  induction ps with
  | nil => simp [piecesArc]
  | cons p ps ih =>
    change Integrable (fun z => ‖f z‖) (pieceArc p + piecesArc ps) at hf
    obtain ⟨hp,ht⟩ := integrable_add_measure.mp hf
    change ‖pieceIntegral p f+(ps.map (fun q => pieceIntegral q f)).sum‖ ≤
      ∫ z, ‖f z‖ ∂(pieceArc p+piecesArc ps)
    rw [integral_add_measure hp ht]
    exact (norm_add_le _ _).trans (add_le_add (pieceIntegral_norm_le p f) (ih ht))

theorem lineIntegral_norm_le (F : DualFrame) (g : FrameGeometry F)
    (n : ℕ) (f : ℂ → ℂ) (hf : Integrable (fun z => ‖f z‖) (contourArcN g n)) :
    ‖lineIntegral g n f‖ ≤ ∫ z, ‖f z‖ ∂contourArcN g n := by
  cases g with
  | pure hp hl hfree => simp [lineIntegral,contourArcN]
  | polygon p hp hl hfree =>
    change Integrable (fun z => ‖f z‖)
      (piecesArc (upperModified p n)+piecesArc ((upperModified p n).map CatalanCore.Decay.CurveFamily.Piece.conj)) at hf
    obtain ⟨hu,hd⟩ := integrable_add_measure.mp hf
    change ‖-((upperModified p n).map (fun q => pieceIntegral q f)).sum +
      (((upperModified p n).map CatalanCore.Decay.CurveFamily.Piece.conj).map (fun q => pieceIntegral q f)).sum‖ ≤
      ∫ z, ‖f z‖ ∂(piecesArc (upperModified p n)+piecesArc ((upperModified p n).map CatalanCore.Decay.CurveFamily.Piece.conj))
    rw [integral_add_measure hu hd]
    apply (norm_add_le _ _).trans
    rw [norm_neg]
    exact add_le_add (piecesIntegral_norm_le _ f hu) (piecesIntegral_norm_le _ f hd)


private theorem segment_norm_le (a b u : ℂ)
    (hu : u ∈ pieceSet ⟨a,b-a,false⟩) : ‖u‖ ≤ ‖a‖+‖b‖ := by
  rcases hu with ⟨t,ht,rfl⟩
  have ht' : 0 ≤ t ∧ t ≤ 1 := by simpa only [Bool.false_eq_true, ↓reduceIte, mem_Icc] using ht
  have he : (⟨a,b-a,false⟩ : CatalanCore.Decay.CurveFamily.Piece).zeta t =
      ((1-t:ℝ):ℂ)*a+(t:ℂ)*b := by
    simp only [CatalanCore.Decay.CurveFamily.Piece.zeta, Complex.ofReal_sub, Complex.ofReal_one]
    ring
  rw [he]
  have hh := norm_add_le (((1-t:ℝ):ℂ)*a) ((t:ℂ)*b)
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg ht'.1, abs_of_nonneg (sub_nonneg.mpr ht'.2)] at hh
  have h0 := mul_nonneg ht'.1 (norm_nonneg a)
  have h1 := mul_nonneg (sub_nonneg.mpr ht'.2) (norm_nonneg b)
  nlinarith

private theorem piecesSet_conj (ps : List CatalanCore.Decay.CurveFamily.Piece) :
    piecesSet (ps.map CatalanCore.Decay.CurveFamily.Piece.conj) = starRingEnd ℂ '' piecesSet ps := by
  ext u
  constructor
  · intro hu
    simp only [piecesSet,mem_iUnion] at hu
    rcases hu with ⟨q,hq,hu⟩
    rcases List.mem_map.mp hq with ⟨q',hq',rfl⟩
    rcases pieceSet_conj_subset q' hu with ⟨v,hv,rfl⟩
    exact ⟨v,by simp only [piecesSet,mem_iUnion]; exact ⟨q',hq',hv⟩,rfl⟩
  · rintro ⟨v,hv,rfl⟩
    simp only [piecesSet,mem_iUnion] at hv ⊢
    rcases hv with ⟨q,hq,t,ht,rfl⟩
    refine ⟨q.conj,List.mem_map.mpr ⟨q,hq,rfl⟩,t,ht,?_⟩
    exact CatalanCore.Decay.CurveFamily.Piece.zeta_conj q t

theorem gammaN_bent_replacement (F : DualFrame) (g : FrameGeometry F)
    (hc : frameCut g = some 0) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n : ℕ in atTop,
      replacementLength g n ≤ K ∧
      ∀ u ∈ replacement g n, ‖u/(n:ℂ)‖ ≤ K/n := by
  cases g with
  | pure hp hl hf => simp [frameCut] at hc
  | polygon p hp hl hf =>
    have hc0 : p.cut = 0 := by simpa only [frameCut,Option.some.injEq] using hc
    let a : ℂ := (1/2:ℝ)
    let b : ℂ := a+Complex.I
    let c : ℂ := ((p.vertex 1).re/(p.vertex 1).im:ℝ)+Complex.I
    let L : ℝ := 2*(‖b-a‖+‖c-b‖)
    let K : ℝ := L+‖a‖+2*‖b‖+‖c‖+1
    have hL : 0 ≤ L := by dsimp [L]; positivity
    have hK : 0 < K := by dsimp [K]; positivity
    have hrep (n : ℕ) : replacementUpper p n = [⟨a,b-a,false⟩,⟨b,c-b,false⟩] := by
      simp only [replacementUpper, crossing, firstAtOne, hc0, zero_mul, mul_zero,
        Nat.floor_zero, Nat.cast_zero, zero_add, sub_zero,
        CatalanCore.Decay.CurveFamily.chainPieces]
      simp only [a,b,c,Complex.ofReal_zero,mul_zero,sub_zero,zero_add,Complex.ofReal_div]
    refine ⟨K,hK,?_⟩
    filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
    have hn0 : 0 ≤ (n:ℝ) := Nat.cast_nonneg n
    constructor
    · change 2*((replacementUpper p n).map (fun q => ‖q.D‖)).sum ≤ K
      rw [hrep]
      simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
      dsimp only [K,L]
      linarith [norm_nonneg a,norm_nonneg b,norm_nonneg c]
    · intro u hu
      have hbound : ∀ v ∈ piecesSet (replacementUpper p n), ‖v‖ ≤ K := by
        intro v hv
        rw [hrep] at hv
        simp only [piecesSet,mem_iUnion,List.mem_cons,List.not_mem_nil,or_false] at hv
        rcases hv with ⟨q,hq,hv⟩
        rcases hq with rfl | rfl
        · have hh := segment_norm_le a b v hv
          dsimp only [K]
          linarith [norm_nonneg b,norm_nonneg c]
        · have hh := segment_norm_le b c v hv
          dsimp only [K]
          linarith [norm_nonneg a,norm_nonneg b]
      have hu' : ‖u‖ ≤ K := by
        change u ∈ piecesSet (replacementUpper p n) ∪ piecesSet ((replacementUpper p n).map CatalanCore.Decay.CurveFamily.Piece.conj) at hu
        rcases hu with hu | hu
        · exact hbound u hu
        · rw [piecesSet_conj] at hu
          rcases hu with ⟨v,hv,rfl⟩
          simpa only [Complex.norm_conj] using hbound v hv
      rw [norm_div, Complex.norm_natCast]
      exact div_le_div_of_nonneg_right hu' hn0


private theorem pieceSet_region (p : CatalanCore.Decay.CurveFamily.Piece)
    (ha : 0 ≤ p.a.re ∧ 1 ≤ p.a.im)
    (hb : if p.ray then 0 ≤ p.D.re ∧ 0 ≤ p.D.im else
      0 ≤ (p.a+p.D).re ∧ 1 ≤ (p.a+p.D).im) (u : ℂ) (hu : u ∈ pieceSet p) :
    0 ≤ u.re ∧ 1 ≤ u.im := by
  have hre := pieceSet_re_nonneg p ha.1 (by split_ifs at hb ⊢ <;> exact hb.1) u hu
  refine ⟨hre,?_⟩
  rcases hu with ⟨t,ht,rfl⟩
  change 1 ≤ (p.a+(t:ℂ)*p.D).im
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, add_zero]
  by_cases h : p.ray = true
  · simp only [h,↓reduceIte] at ht hb
    have hh := mul_nonneg ht hb.2
    linarith [ha.2]
  · have hf : p.ray = false := Bool.eq_false_iff.mpr h
    simp only [hf,Bool.false_eq_true,↓reduceIte,mem_Icc] at ht hb
    have h1 := mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr ha.2)
    have h2 := mul_nonneg ht.1 (sub_nonneg.mpr hb.2)
    simp only [Complex.add_im] at h2
    nlinarith

private theorem chainPieces_endpoints (vs : List ℂ) (q : CatalanCore.Decay.CurveFamily.Piece)
    (hq : q ∈ CatalanCore.Decay.CurveFamily.chainPieces vs) :
    ∃ a ∈ vs, ∃ b ∈ vs, q = ⟨a,b-a,false⟩ := by
  induction vs with
  | nil => simp [CatalanCore.Decay.CurveFamily.chainPieces] at hq
  | cons a vs ih =>
    cases vs with
    | nil => simp [CatalanCore.Decay.CurveFamily.chainPieces] at hq
    | cons b vs =>
      change q ∈ ⟨a,b-a,false⟩ :: CatalanCore.Decay.CurveFamily.chainPieces (b::vs) at hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact ⟨a,by simp,b,by simp,rfl⟩
      · obtain ⟨c,hc,d,hd,he⟩ := ih hq
        exact ⟨c,by simp [hc],d,by simp [hd],he⟩

private theorem polygon_first_im_pos (p : PolygonFrame) : 0 < (p.vertex 1).im := by
  have hh := p.imag_strict 0 1 (by omega) p.edges_pos
  simpa only [p.initial,Complex.ofReal_im] using hh

private theorem scaled_vertex_region (p : PolygonFrame) (n : ℕ)
    (hn : 1 ≤ (n:ℝ)*(p.vertex 1).im) (j : ℕ) (hj0 : 1 ≤ j) (hj : j ≤ p.edges) :
    0 ≤ ((n:ℂ)*p.vertex j).re ∧ 1 ≤ ((n:ℂ)*p.vertex j).im := by
  have him : (p.vertex 1).im ≤ (p.vertex j).im := by
    by_cases he : j=1
    · simp [he]
    · exact (p.imag_strict 1 j (by omega) hj).le
  have hh := mul_le_mul_of_nonneg_left him (Nat.cast_nonneg n : (0:ℝ) ≤ n)
  simp only [Complex.mul_re,Complex.mul_im,Complex.natCast_re,Complex.natCast_im,
    zero_mul,sub_zero,add_zero]
  exact ⟨mul_nonneg (Nat.cast_nonneg n) (p.real_pos j hj0 hj).le,hn.trans hh⟩

private theorem firstAtOne_region (p : PolygonFrame) (n : ℕ)
    (hn : 1 ≤ (n:ℝ)*(p.vertex 1).im) :
    0 ≤ (firstAtOne p n).re ∧ 1 ≤ (firstAtOne p n).im := by
  have hi := polygon_first_im_pos p
  have hn' : 1/(p.vertex 1).im ≤ (n:ℝ) := (div_le_iff₀ hi).mpr (by nlinarith)
  have h0 := mul_nonneg (sub_nonneg.mpr hn') p.nonneg
  have h1 := div_nonneg (p.real_pos 1 le_rfl p.edges_pos).le hi.le
  have he : (n:ℝ)*p.cut+((p.vertex 1).re-p.cut)/(p.vertex 1).im =
      ((n:ℝ)-1/(p.vertex 1).im)*p.cut+(p.vertex 1).re/(p.vertex 1).im := by ring
  simp only [firstAtOne,← Complex.ofReal_mul,← Complex.ofReal_sub,← Complex.ofReal_div,← Complex.ofReal_add,Complex.add_re,Complex.ofReal_re,Complex.I_re,add_zero,
    Complex.add_im,Complex.ofReal_im,Complex.I_im,zero_add]
  exact ⟨by rw [he]; exact add_nonneg h0 h1,le_rfl⟩

private theorem upperModified_domain (p : PolygonFrame) (n : ℕ)
    (hn : 1 ≤ (n:ℝ)*(p.vertex 1).im) (u : ℂ) (hu : u ∈ piecesSet (upperModified p n)) :
    u ∈ pieceSet ⟨(crossing p n:ℂ),(crossing p n:ℂ)+Complex.I-(crossing p n:ℂ),false⟩ ∨
      (0 ≤ u.re ∧ 1 ≤ u.im) := by
  have hc : 0 ≤ crossing p n := by unfold crossing; positivity
  have hf := firstAtOne_region p n hn
  have hv : ∀ v ∈ (firstAtOne p n :: (List.range p.edges).map (fun j => (n:ℂ)*p.vertex (j+1))),
      0 ≤ v.re ∧ 1 ≤ v.im := by
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact hf
    · rcases List.mem_map.mp hv with ⟨j,hj,rfl⟩
      exact scaled_vertex_region p n hn (j+1) (by omega) (by have := List.mem_range.mp hj; omega)
  simp only [piecesSet,mem_iUnion] at hu
  rcases hu with ⟨q,hq,hu⟩
  change q ∈ ⟨(crossing p n:ℂ),(crossing p n:ℂ)+Complex.I-(crossing p n:ℂ),false⟩ ::
    ⟨(crossing p n:ℂ)+Complex.I,firstAtOne p n-((crossing p n:ℂ)+Complex.I),false⟩ ::
    (CatalanCore.Decay.CurveFamily.chainPieces
      (firstAtOne p n :: (List.range p.edges).map (fun j => (n:ℂ)*p.vertex (j+1))) ++
        [⟨(n:ℂ)*p.vertex p.edges,Complex.I,true⟩]) at hq
  simp only [List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at hq
  rcases hq with rfl | rfl | hq | rfl
  · exact Or.inl hu
  · apply Or.inr
    apply pieceSet_region _ (by simpa using And.intro hc (le_refl (1:ℝ))) _ u hu
    simpa using hf
  · obtain ⟨a,ha,b,hb,rfl⟩ := chainPieces_endpoints _ q hq
    apply Or.inr
    apply pieceSet_region _ (hv a ha) _ u hu
    simpa using hv b hb
  · apply Or.inr
    apply pieceSet_region _ (scaled_vertex_region p n hn p.edges p.edges_pos le_rfl) _ u hu
    simp


private theorem polygon_eventually_height (p : PolygonFrame) :
    ∀ᶠ n : ℕ in atTop, 1 ≤ (n:ℝ)*(p.vertex 1).im := by
  have hi := polygon_first_im_pos p
  have hh : ∀ᶠ n : ℕ in atTop, 1/(p.vertex 1).im ≤ (n:ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop _)
  filter_upwards [hh] with n hn
  exact (div_le_iff₀ hi).mp hn

private theorem upperModified_kernel (p : PolygonFrame) (n : ℕ)
    (hn : 1 ≤ (n:ℝ)*(p.vertex 1).im) (u : ℂ) (hu : u ∈ piecesSet (upperModified p n)) :
    0 ≤ u.re ∧ 1/2 ≤ ‖u‖ ∧ ((∃ k : ℕ, u.re=(k:ℝ)+1/2) ∨ 1 ≤ |u.im|) := by
  rcases upperModified_domain p n hn u hu with hv | hv
  · have hre : u.re = crossing p n := by
      rcases hv with ⟨t,ht,rfl⟩
      simp [CatalanCore.Decay.CurveFamily.Piece.zeta]
    have hc : (1:ℝ)/2 ≤ crossing p n := by
      unfold crossing
      linarith [Nat.cast_nonneg (Nat.floor (p.cut*(n:ℝ))) (α := ℝ)]
    have hnorm : (1:ℝ)/2 ≤ ‖u‖ :=
      hc.trans (by rw [← hre]; exact (le_abs_self _).trans (Complex.abs_re_le_norm u))
    refine ⟨by linarith [hre],hnorm,Or.inl ?_⟩
    exact ⟨Nat.floor (p.cut*(n:ℝ)), by simpa only [crossing] using hre⟩
  · have him : 1 ≤ |u.im| := hv.2.trans (le_abs_self _)
    have hn' : 1 ≤ ‖u‖ := him.trans (Complex.abs_im_le_norm u)
    exact ⟨hv.1,by linarith,Or.inr him⟩

theorem gammaN_kernel_domain (F : DualFrame) (g : FrameGeometry F) :
    ∀ᶠ n : ℕ in atTop, ∀ u ∈ gammaN g n,
      0 ≤ u.re ∧ 1/2 ≤ ‖u‖ ∧ ((∃ k : ℕ, u.re=(k:ℝ)+1/2) ∨ 1 ≤ |u.im|) := by
  cases g with
  | pure hp hl hf => exact Eventually.of_forall (by simp [gammaN])
  | polygon p hp hl hf =>
    filter_upwards [polygon_eventually_height p] with n hn
    intro u hu
    change u ∈ piecesSet (upperModified p n) ∪ piecesSet ((upperModified p n).map CatalanCore.Decay.CurveFamily.Piece.conj) at hu
    rcases hu with hu | hu
    · exact upperModified_kernel p n hn u hu
    · rw [piecesSet_conj] at hu
      rcases hu with ⟨v,hv,rfl⟩
      simpa using upperModified_kernel p n hn v hv

private theorem crossing_mem_upper (p : PolygonFrame) (n : ℕ) :
    (crossing p n:ℂ) ∈ piecesSet (upperModified p n) := by
  simp only [piecesSet,mem_iUnion]
  refine ⟨⟨(crossing p n:ℂ),(crossing p n:ℂ)+Complex.I-(crossing p n:ℂ),false⟩,?_,0,?_,?_⟩
  · change _ ∈ _ :: _
    exact List.mem_cons_self
  · simp only [Bool.false_eq_true,↓reduceIte,mem_Icc]
    norm_num
  · simp [CatalanCore.Decay.CurveFamily.Piece.zeta]

private theorem upperModified_real_eq (p : PolygonFrame) (n : ℕ)
    (hn : 1 ≤ (n:ℝ)*(p.vertex 1).im) (u : ℂ)
    (hu : u ∈ piecesSet (upperModified p n)) (him : u.im=0) :
    u=(crossing p n:ℂ) := by
  rcases upperModified_domain p n hn u hu with hv | hv
  · rcases hv with ⟨t,ht,rfl⟩
    have ht0 : t=0 := by simpa [CatalanCore.Decay.CurveFamily.Piece.zeta] using him
    simp [ht0,CatalanCore.Decay.CurveFamily.Piece.zeta]
  · linarith [hv.2]

theorem gammaN_crossing (F : DualFrame) (g : FrameGeometry F) (c : ℝ)
    (hc : frameCut g = some c) :
    ∀ᶠ n : ℕ in atTop,
      {u | u ∈ gammaN g n ∧ u.im=0} = {((⌊c*n⌋₊:ℝ)+1/2:ℂ)} := by
  cases g with
  | pure hp hl hf => simp [frameCut] at hc
  | polygon p hp hl hf =>
    have hcut : p.cut=c := by simpa only [frameCut,Option.some.injEq] using hc
    filter_upwards [polygon_eventually_height p] with n hn
    have heq : ((⌊c*n⌋₊:ℝ)+1/2:ℂ)=(crossing p n:ℂ) := by
      simp only [crossing,hcut,Complex.ofReal_add,Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat]
    rw [heq]
    ext u
    constructor
    · rintro ⟨hu,him⟩
      change u=(crossing p n:ℂ)
      change u ∈ piecesSet (upperModified p n) ∪ piecesSet ((upperModified p n).map CatalanCore.Decay.CurveFamily.Piece.conj) at hu
      rcases hu with hu | hu
      · exact upperModified_real_eq p n hn u hu him
      · rw [piecesSet_conj] at hu
        rcases hu with ⟨v,hv,rfl⟩
        have hvim : v.im=0 := by simpa using him
        rw [upperModified_real_eq p n hn v hv hvim]
        simp
    · intro hu
      rw [Set.mem_singleton_iff] at hu
      subst u
      exact ⟨Or.inl (crossing_mem_upper p n),by simp⟩


private theorem chainPieces_range (k : ℕ) : ∀ f : ℕ → ℂ,
    CatalanCore.Decay.CurveFamily.chainPieces ((List.range (k+1)).map f) =
      (List.range k).map (fun j => (⟨f j,f (j+1)-f j,false⟩ : CatalanCore.Decay.CurveFamily.Piece)) := by
  induction k with
  | zero => intro f; simp [CatalanCore.Decay.CurveFamily.chainPieces]
  | succ k ih =>
    intro f
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    change CatalanCore.Decay.CurveFamily.chainPieces (f 0 ::
      ((List.range (k+1)).map (fun j => f (j+1)))) = _
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    have hi := ih (fun j => f (j+1))
    rw [List.range_succ_eq_map,List.map_cons,List.map_map] at hi
    simpa only [CatalanCore.Decay.CurveFamily.chainPieces,List.map_cons,List.map_map,
      Function.comp_def,Nat.succ_eq_add_one,Nat.zero_add,Nat.add_assoc] using
      congrArg (fun ps => (⟨f 0,f 1-f 0,false⟩ : CatalanCore.Decay.CurveFamily.Piece) :: ps) hi

private theorem polygonPieces_chain (p : PolygonFrame) :
    polygonPieces p = CatalanCore.Decay.CurveFamily.chainPieces
      ((p.cut:ℂ) :: (List.range p.edges).map (fun j => p.vertex (j+1))) ++
      [⟨p.vertex p.edges,Complex.I,true⟩] := by
  have he := chainPieces_range p.edges p.vertex
  rw [List.range_succ_eq_map,List.map_cons,List.map_map] at he
  simpa only [polygonPieces,p.initial,Function.comp_def,Nat.succ_eq_add_one] using congrArg
    (fun ps => ps ++ [⟨p.vertex p.edges,Complex.I,true⟩]) he.symm

private theorem chainPieces_scale (vs : List ℂ) (c : ℂ) :
    CatalanCore.Decay.CurveFamily.chainPieces (vs.map (fun z => c*z)) =
      (CatalanCore.Decay.CurveFamily.chainPieces vs).map (fun p => ⟨c*p.a,c*p.D,p.ray⟩) := by
  induction vs with
  | nil => simp [CatalanCore.Decay.CurveFamily.chainPieces]
  | cons a vs ih =>
    cases vs with
    | nil => simp [CatalanCore.Decay.CurveFamily.chainPieces]
    | cons b vs =>
      simp only [List.map_cons,CatalanCore.Decay.CurveFamily.chainPieces]
      simp only [List.map_cons] at ih
      rw [ih]
      congr 2
      ring


private theorem segment_cut_at_one (a b u : ℂ) (ha : a.im=0) (hb : 1 < b.im) (hu : 1 < u.im) :
    u ∈ pieceSet ⟨a,b-a,false⟩ ↔
      u ∈ pieceSet ⟨a+((1/b.im:ℝ):ℂ)*(b-a),b-(a+((1/b.im:ℝ):ℂ)*(b-a)),false⟩ := by
  have hH : b.im ≠ 0 := by linarith
  have hH1 : b.im-1 ≠ 0 := by linarith
  have hHc : (b.im:ℂ) ≠ 0 := by exact_mod_cast hH
  have hH1c : ((b.im:ℂ)-1) ≠ 0 := by exact_mod_cast hH1
  constructor
  · rintro ⟨t,ht,hz⟩
    have ht' : 0 ≤ t ∧ t ≤ 1 := by simpa only [Bool.false_eq_true,↓reduceIte,mem_Icc] using ht
    have him : t*b.im=u.im := by
      have hh := congrArg Complex.im hz
      simpa [CatalanCore.Decay.CurveFamily.Piece.zeta,ha] using hh
    let q := (t*b.im-1)/(b.im-1)
    have hq0 : 0 ≤ q := div_nonneg (by linarith) (by linarith)
    have hq1 : q ≤ 1 := by
      apply (div_le_one (by linarith : 0 < b.im-1)).mpr
      nlinarith
    refine ⟨q,by simpa only [Bool.false_eq_true,↓reduceIte,mem_Icc] using And.intro hq0 hq1,?_⟩
    rw [← hz]
    simp only [CatalanCore.Decay.CurveFamily.Piece.zeta]
    dsimp only [q]
    push_cast
    field_simp
    <;> ring
  · rintro ⟨q,hq,hz⟩
    have hq' : 0 ≤ q ∧ q ≤ 1 := by simpa only [Bool.false_eq_true,↓reduceIte,mem_Icc] using hq
    let t := (1+q*(b.im-1))/b.im
    have ht0 : 0 ≤ t := div_nonneg (by nlinarith [mul_nonneg hq'.1 (show 0 ≤ b.im-1 by linarith)]) (by linarith)
    have ht1 : t ≤ 1 := by
      apply (div_le_one (by linarith : 0 < b.im)).mpr
      nlinarith
    refine ⟨t,by simpa only [Bool.false_eq_true,↓reduceIte,mem_Icc] using And.intro ht0 ht1,?_⟩
    rw [← hz]
    simp only [CatalanCore.Decay.CurveFamily.Piece.zeta]
    dsimp only [t]
    push_cast
    field_simp
    <;> ring


private theorem piecesSet_cons (p : CatalanCore.Decay.CurveFamily.Piece)
    (ps : List CatalanCore.Decay.CurveFamily.Piece) :
    piecesSet (p::ps) = pieceSet p ∪ piecesSet ps := by
  ext u
  simp [piecesSet]
private theorem piecesSet_append (ps qs : List CatalanCore.Decay.CurveFamily.Piece) :
    piecesSet (ps++qs) = piecesSet ps ∪ piecesSet qs := by
  ext u
  simp [piecesSet,or_and_right,exists_or]
private theorem pieceSet_scale (p : CatalanCore.Decay.CurveFamily.Piece) (c : ℂ) :
    pieceSet ⟨c*p.a,c*p.D,p.ray⟩ = (fun z => c*z) '' pieceSet p := by
  ext u
  constructor
  · rintro ⟨t,ht,rfl⟩
    refine ⟨p.zeta t,⟨t,ht,rfl⟩,?_⟩
    simp only [CatalanCore.Decay.CurveFamily.Piece.zeta]
    ring
  · rintro ⟨v,⟨t,ht,rfl⟩,rfl⟩
    refine ⟨t,ht,?_⟩
    simp only [CatalanCore.Decay.CurveFamily.Piece.zeta]
    ring
private theorem piecesSet_scale (ps : List CatalanCore.Decay.CurveFamily.Piece) (c : ℂ) :
    piecesSet (ps.map (fun p => ⟨c*p.a,c*p.D,p.ray⟩)) = (fun z => c*z) '' piecesSet ps := by
  induction ps with
  | nil => simp [piecesSet]
  | cons p ps ih =>
    rw [List.map_cons,piecesSet_cons,pieceSet_scale,ih,piecesSet_cons,Set.image_union]
private theorem raySet_scale_direction (a D : ℂ) (c : ℝ) (hc : 0 < c) :
    pieceSet ⟨a,D,true⟩ = pieceSet ⟨a,(c:ℂ)*D,true⟩ := by
  have hcc : (c:ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  ext u
  constructor
  · rintro ⟨t,ht,rfl⟩
    have ht0 : 0 ≤ t := by simpa only [Bool.true_eq,↓reduceIte,mem_Ici] using ht
    refine ⟨t/c,by simpa only [Bool.true_eq,↓reduceIte,mem_Ici] using div_nonneg ht0 hc.le,?_⟩
    simp only [CatalanCore.Decay.CurveFamily.Piece.zeta,Complex.ofReal_div]
    field_simp
  · rintro ⟨t,ht,rfl⟩
    have ht0 : 0 ≤ t := by simpa only [Bool.true_eq,↓reduceIte,mem_Ici] using ht
    refine ⟨t*c,by simpa only [Bool.true_eq,↓reduceIte,mem_Ici] using mul_nonneg ht0 hc.le,?_⟩
    simp only [CatalanCore.Decay.CurveFamily.Piece.zeta,Complex.ofReal_mul]
    ring


private noncomputable def scaledOriginalPieces (p : PolygonFrame) (n : ℕ) :
    List CatalanCore.Decay.CurveFamily.Piece :=
  CatalanCore.Decay.CurveFamily.chainPieces
    ((n:ℂ)*(p.cut:ℂ) :: (List.range p.edges).map (fun j => (n:ℂ)*p.vertex (j+1))) ++
    [⟨(n:ℂ)*p.vertex p.edges,Complex.I,true⟩]
private theorem scaledOriginalPieces_set (p : PolygonFrame) (n : ℕ) (hn : 0 < n) :
    piecesSet (scaledOriginalPieces p n) = (fun z => (n:ℂ)*z) '' piecesSet (polygonPieces p) := by
  have hv : (n:ℂ)*(p.cut:ℂ) :: (List.range p.edges).map (fun j => (n:ℂ)*p.vertex (j+1)) =
      ((p.cut:ℂ) :: (List.range p.edges).map (fun j => p.vertex (j+1))).map (fun z => (n:ℂ)*z) := by
    simp only [List.map_cons,List.map_map,Function.comp_def]
  rw [scaledOriginalPieces,polygonPieces_chain,piecesSet_append,piecesSet_append,Set.image_union,hv,
    chainPieces_scale,piecesSet_scale]
  congr 1
  simp only [piecesSet_cons]
  have hnil : piecesSet ([] : List CatalanCore.Decay.CurveFamily.Piece) = ∅ := by simp [piecesSet]
  rw [hnil,Set.union_empty,Set.union_empty,← pieceSet_scale]
  simpa only [Complex.ofReal_natCast] using raySet_scale_direction
    ((n:ℂ)*p.vertex p.edges) Complex.I (n:ℝ) (by exact_mod_cast hn)
private theorem firstAtOne_affine (p : PolygonFrame) (n : ℕ) (hn : 0 < n) :
    firstAtOne p n = (n:ℂ)*(p.cut:ℂ) +
      ((1/(((n:ℂ)*p.vertex 1).im):ℝ):ℂ)*((n:ℂ)*p.vertex 1-(n:ℂ)*(p.cut:ℂ)) := by
  have hi := polygon_first_im_pos p
  have hnR : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hiR : (p.vertex 1).im ≠ 0 := hi.ne'
  simp only [firstAtOne,← Complex.ofReal_mul,← Complex.ofReal_sub,← Complex.ofReal_div,← Complex.ofReal_add]
  apply Complex.ext <;>
    simp only [Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im,
      Complex.sub_re,Complex.sub_im,Complex.ofReal_re,Complex.ofReal_im,
      Complex.natCast_re,Complex.natCast_im,Complex.I_re,Complex.I_im,
      zero_mul,mul_zero,add_zero,zero_add,sub_zero]
  all_goals field_simp <;> ring


private theorem segment_im_le_one (a b u : ℂ) (ha : a.im ≤ 1) (hb : b.im ≤ 1)
    (hu : u ∈ pieceSet ⟨a,b-a,false⟩) : u.im ≤ 1 := by
  rcases hu with ⟨t,ht,rfl⟩
  have ht' : 0 ≤ t ∧ t ≤ 1 := by simpa only [Bool.false_eq_true,↓reduceIte,mem_Icc] using ht
  have h1 := mul_nonneg (sub_nonneg.mpr ht'.2) (sub_nonneg.mpr ha)
  have h2 := mul_nonneg ht'.1 (sub_nonneg.mpr hb)
  simp only [CatalanCore.Decay.CurveFamily.Piece.zeta,Complex.add_im,Complex.mul_im,
    Complex.sub_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero]
  nlinarith

private theorem upper_above_one_iff (p : PolygonFrame) (n : ℕ) (hn : 0 < n)
    (hheight : 1 < (n:ℝ)*(p.vertex 1).im) (u : ℂ) (hu : 1 < u.im) :
    u ∈ piecesSet (upperModified p n) ↔ u ∈ piecesSet (scaledOriginalPieces p n) := by
  obtain ⟨k,hk⟩ : ∃ k : ℕ, p.edges=k+1 := Nat.exists_eq_succ_of_ne_zero p.edges_pos.ne'
  have hvs : (List.range p.edges).map (fun j => (n:ℂ)*p.vertex (j+1)) =
      (n:ℂ)*p.vertex 1 :: (List.range k).map (fun j => (n:ℂ)*p.vertex (j+2)) := by
    rw [hk,List.range_succ_eq_map,List.map_cons,List.map_map]
    simp only [Function.comp_def,Nat.succ_eq_add_one,Nat.zero_add,Nat.add_assoc]
  have hfim : (firstAtOne p n).im=1 := by
    simp only [firstAtOne,← Complex.ofReal_mul,← Complex.ofReal_sub,← Complex.ofReal_div,
      ← Complex.ofReal_add,Complex.add_im,Complex.ofReal_im,Complex.I_im,zero_add]
  have hfirst : u ∉ pieceSet ⟨(crossing p n:ℂ),(crossing p n:ℂ)+Complex.I-(crossing p n:ℂ),false⟩ := by
    intro hh
    have ht := segment_im_le_one (crossing p n:ℂ) ((crossing p n:ℂ)+Complex.I) u (by simp) (by simp) hh
    linarith
  have hsecond : u ∉ pieceSet ⟨(crossing p n:ℂ)+Complex.I,
      firstAtOne p n-((crossing p n:ℂ)+Complex.I),false⟩ := by
    intro hh
    have ht := segment_im_le_one ((crossing p n:ℂ)+Complex.I) (firstAtOne p n) u (by simp) hfim.le hh
    linarith
  have hcut := segment_cut_at_one ((n:ℂ)*(p.cut:ℂ)) ((n:ℂ)*p.vertex 1) u
    (by simp) (by simpa using hheight) hu
  rw [← firstAtOne_affine p n hn] at hcut
  unfold upperModified scaledOriginalPieces
  rw [hvs]
  simp only [List.cons_append,List.nil_append,CatalanCore.Decay.CurveFamily.chainPieces,
    piecesSet_cons,piecesSet_append,Set.mem_union]
  simp only [hfirst,hsecond,false_or]
  tauto


private theorem pieceSet_im_nonneg (p : CatalanCore.Decay.CurveFamily.Piece)
    (ha : 0 ≤ p.a.im) (hb : if p.ray then 0 ≤ p.D.im else 0 ≤ (p.a+p.D).im)
    (u : ℂ) (hu : u ∈ pieceSet p) : 0 ≤ u.im := by
  rcases hu with ⟨t,ht,rfl⟩
  change 0 ≤ (p.a+(t:ℂ)*p.D).im
  simp only [Complex.add_im,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,add_zero]
  by_cases h : p.ray=true
  · simp only [h,↓reduceIte,mem_Ici] at ht hb
    exact add_nonneg ha (mul_nonneg ht hb)
  · have hf : p.ray=false := Bool.eq_false_iff.mpr h
    simp only [hf,Bool.false_eq_true,↓reduceIte,mem_Icc] at ht hb
    have h1 := mul_nonneg (sub_nonneg.mpr ht.2) ha
    have h2 := mul_nonneg ht.1 hb
    simp only [Complex.add_im] at h2
    nlinarith
private theorem upperModified_im_nonneg (p : PolygonFrame) (n : ℕ)
    (hn : 1 ≤ (n:ℝ)*(p.vertex 1).im) (u : ℂ) (hu : u ∈ piecesSet (upperModified p n)) :
    0 ≤ u.im := by
  rcases upperModified_domain p n hn u hu with hv | hv
  · apply pieceSet_im_nonneg _ (by simp) _ u hv
    simp
  · linarith [hv.2]
private theorem scaledOriginal_im_nonneg (p : PolygonFrame) (n : ℕ)
    (hn : 1 ≤ (n:ℝ)*(p.vertex 1).im) (u : ℂ) (hu : u ∈ piecesSet (scaledOriginalPieces p n)) :
    0 ≤ u.im := by
  have hv : ∀ v ∈ ((n:ℂ)*(p.cut:ℂ) :: (List.range p.edges).map (fun j => (n:ℂ)*p.vertex (j+1))), 0 ≤ v.im := by
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · simp
    · rcases List.mem_map.mp hv with ⟨j,hj,rfl⟩
      have hh := (scaled_vertex_region p n hn (j+1) (by omega) (by have := List.mem_range.mp hj; omega)).2
      linarith
  simp only [scaledOriginalPieces,piecesSet_append,Set.mem_union] at hu
  rcases hu with hu | hu
  · simp only [piecesSet,mem_iUnion] at hu
    rcases hu with ⟨q,hq,hu⟩
    obtain ⟨a,ha,b,hb,rfl⟩ := chainPieces_endpoints _ q hq
    apply pieceSet_im_nonneg _ (hv a ha) _ u hu
    simpa using hv b hb
  · simp only [piecesSet,mem_iUnion,List.mem_singleton] at hu
    rcases hu with ⟨q,rfl,hu⟩
    apply pieceSet_im_nonneg _ _ _ u hu
    · have hh := (scaled_vertex_region p n hn p.edges p.edges_pos le_rfl).2
      linarith
    · simp
private theorem conj_image_mem (S : Set ℂ) (u : ℂ) :
    u ∈ starRingEnd ℂ '' S ↔ starRingEnd ℂ u ∈ S := by
  constructor
  · rintro ⟨v,hv,rfl⟩
    simpa using hv
  · intro hu
    exact ⟨starRingEnd ℂ u,hu,by simp⟩
private theorem symmetric_sets_agree (A B : Set ℂ)
    (hA : ∀ u ∈ A, 0 ≤ u.im) (hB : ∀ u ∈ B, 0 ≤ u.im)
    (hAB : ∀ u : ℂ, 1 < u.im → (u ∈ A ↔ u ∈ B))
    (u : ℂ) (hu : 1 < |u.im|) :
    u ∈ A ∪ starRingEnd ℂ '' A ↔ u ∈ B ∪ starRingEnd ℂ '' B := by
  simp only [Set.mem_union,conj_image_mem]
  rcases lt_abs.mp hu with hp | hn
  · have ha : starRingEnd ℂ u ∉ A := by
      intro hh
      have ht := hA _ hh
      simp only [Complex.conj_im] at ht
      linarith
    have hb : starRingEnd ℂ u ∉ B := by
      intro hh
      have ht := hB _ hh
      simp only [Complex.conj_im] at ht
      linarith
    simp only [ha,hb,or_false]
    exact hAB u hp
  · have ha : u ∉ A := by intro hh; have ht := hA _ hh; linarith
    have hb : u ∉ B := by intro hh; have ht := hB _ hh; linarith
    simp only [ha,hb,false_or]
    exact hAB _ (by simpa only [Complex.conj_im] using hn)
private theorem scaled_polygon_symmetry (p : PolygonFrame) (n : ℕ) (hn : 0 < n) :
    (fun z => (n:ℂ)*z) '' polygonSet p = piecesSet (scaledOriginalPieces p n) ∪
      starRingEnd ℂ '' piecesSet (scaledOriginalPieces p n) := by
  rw [polygonSet,Set.image_union,scaledOriginalPieces_set p n hn,Set.image_image,Set.image_image]
  congr 1
  apply congrArg (fun f : ℂ → ℂ => f '' piecesSet (polygonPieces p))
  funext z
  simp

theorem gammaN_scaled_agrees (F : DualFrame) (g : FrameGeometry F) :
    ∀ᶠ n : ℕ in atTop,
      {u | u ∈ gammaN g n ∧ 1 < |u.im|} =
        {u | (∃ v ∈ contourSet g, u=(n:ℂ)*v) ∧ 1 < |u.im|} := by
  cases g with
  | pure hp hl hf => exact Eventually.of_forall (by simp [gammaN,contourSet])
  | polygon p hp hl hf =>
    have hi := polygon_first_im_pos p
    have hev : ∀ᶠ n : ℕ in atTop, 2/(p.vertex 1).im ≤ (n:ℝ) :=
      tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop _)
    filter_upwards [hev,eventually_ge_atTop (1:ℕ)] with n hn hn1
    have hn0 : 0 < n := by omega
    have hheight : 1 < (n:ℝ)*(p.vertex 1).im := by
      have hh := (div_le_iff₀ hi).mp hn
      linarith
    have hs := scaled_polygon_symmetry p n hn0
    ext u
    change (u ∈ piecesSet (upperModified p n) ∪
      piecesSet ((upperModified p n).map CatalanCore.Decay.CurveFamily.Piece.conj) ∧ 1 < |u.im|) ↔
      ((∃ v ∈ polygonSet p, u=(n:ℂ)*v) ∧ 1 < |u.im|)
    rw [piecesSet_conj]
    have himage : (∃ v ∈ polygonSet p, u=(n:ℂ)*v) ↔
        u ∈ piecesSet (scaledOriginalPieces p n) ∪ starRingEnd ℂ '' piecesSet (scaledOriginalPieces p n) := by
      rw [← hs]
      simp only [Set.mem_image]
      constructor <;> rintro ⟨v,hv,he⟩ <;> exact ⟨v,hv,he.symm⟩
    rw [himage]
    apply and_congr_left
    intro hu
    exact symmetric_sets_agree _ _ (upperModified_im_nonneg p n hheight.le)
      (scaledOriginal_im_nonneg p n hheight.le) (upper_above_one_iff p n hn0 hheight) u hu

end CatalanCore.Li2.Uniform
#print axioms CatalanCore.Li2.Uniform.goodFrame_halfplane

#print axioms CatalanCore.Li2.Uniform.frame_arc_supported

#print axioms CatalanCore.Li2.Uniform.lineIntegral_norm_le

#print axioms CatalanCore.Li2.Uniform.gammaN_bent_replacement

#print axioms CatalanCore.Li2.Uniform.upperModified_domain

#print axioms CatalanCore.Li2.Uniform.gammaN_kernel_domain
#print axioms CatalanCore.Li2.Uniform.gammaN_crossing

#print axioms CatalanCore.Li2.Uniform.polygonPieces_chain

#print axioms CatalanCore.Li2.Uniform.segment_cut_at_one

#print axioms CatalanCore.Li2.Uniform.raySet_scale_direction

#print axioms CatalanCore.Li2.Uniform.scaledOriginalPieces_set
#print axioms CatalanCore.Li2.Uniform.firstAtOne_affine

#print axioms CatalanCore.Li2.Uniform.upper_above_one_iff

#print axioms CatalanCore.Li2.Uniform.gammaN_scaled_agrees
