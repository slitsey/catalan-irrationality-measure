module
public import CatalanCore.Li2.DecayCert.Simple.Sound
public import CatalanCore.Li2.DecayCert.Lattice.Primitive
public import CatalanCore.Li2.DecayCert.Lattice.MultipoleUniform
/-! Bridge from the fused TC check to the lattice field on the first segment. `W_field_eq` splits
`W - θ` into `latticeApproxField` and the multipole remainder of the second segment, `second_mp_err`
bounds that remainder uniformly, `approxField_eq_target` identifies `latticeApproxField` with the
W-type target `tcTargetR` under the source identifications, and `wCell_bound` turns a passed W cell
into lower and upper bounds for `W - θ` on its interval. -/
@[expose] public section
open MeasureTheory Set
namespace CatalanCore.Li2.DecayCert.Simple
open CatalanCore.Li2.DecayCert CatalanCore.Li2.Decay CatalanCore.Li2.DecayCert.LatticeSimple
noncomputable section

/-- On the first segment, `W - θ` is the lattice field with the exact second-segment potential replaced
by its multipole sum, up to twice the multipole error. -/
theorem W_field_eq (z θ Y : ℝ) (hY : 0<Y) (σ1 σ2 : Measure ℂ) [IsFiniteMeasure σ2]
    (d : LatticeMomentData σ1 σ2 Y) (K : ℕ) (s : ℝ) (hs : s ∈ Icc 0 Y) :
    W z (σ1+σ2) (s:ℂ)-θ=latticeApproxField z θ d K s-2*(U σ2 (s:ℂ)-d.mpValue K s) := by
  have ho := latticeOwn_source d hY s hs
  have hi2 := latticeSecond_log_integrable d s hs.1
  have hU : U (σ1+σ2) (s:ℂ)=U σ1 (s:ℂ)+U σ2 (s:ℂ) := by
    change -(∫ u,Real.log ‖(s:ℂ)-u‖ ∂(σ1+σ2))=
      -(∫ u,Real.log ‖(s:ℂ)-u‖ ∂σ1)+ -(∫ u,Real.log ‖(s:ℂ)-u‖ ∂σ2)
    rw [integral_add_measure ho.1 hi2]
    ring
  rw [W,hU,ho.2]
  dsimp only [latticeApproxField]
  ring

/-- The multipole error on the first segment, uniformly. -/
theorem second_mp_err (Y : ℝ) (σ1 σ2 : Measure ℂ) [IsFiniteMeasure σ2]
    (d : LatticeMomentData σ1 σ2 Y) (K : ℕ) (s : ℝ) (hs : 0 ≤ s) :
    |U σ2 (s:ℂ)-d.mpValue K s| ≤ mpErr (σ2.real univ) (d.supportRadius/(-d.y0)) K := by
  have hy := d.y0_neg
  have hsy : 0 < s-d.y0 := by linarith
  have hn : ‖(s:ℂ)-(d.y0:ℂ)‖=s-d.y0 := by
    rw [← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hsy]
  have hsep : d.supportRadius < ‖(s:ℂ)-(d.y0:ℂ)‖ := by rw [hn]; linarith [d.separated]
  have h := logPot_multipole σ2 (d.y0:ℂ) (s:ℂ) d.supportRadius d.supportRadius_nonneg d.second_support hsep K
  rw [hn] at h
  refine h.trans (mpErr_mono_ratio _ _ _ K measureReal_nonneg (div_nonneg d.supportRadius_nonneg hsy.le)
    (div_le_div_of_nonneg_left d.supportRadius_nonneg (by linarith) (by linarith)) ?_)
  rw [div_lt_one (by linarith)]; exact d.separated

/-- The lattice field equals the TC target of a W cell under the source identifications. -/
theorem approxField_eq_target (s : SourceF) (r : SourceR) (p : TCSpec) (hk : p.kind=.W)
    (z θ Y : ℝ) (σ1 σ2 : Measure ℂ) (d : LatticeMomentData σ1 σ2 Y) (K : ℕ)
    (hL : r.L=Real.log |z|) (hθ : (s.theta:ℝ)=θ) (hy0 : (s.y0:ℝ)=d.y0) (hYs : (s.Y:ℝ)=Y)
    (hM2 : r.M2=σ2.real univ) (hU1c : r.U1c=d.c 0*Real.log (4/Y))
    (hq1 : ∀ x : ℝ, hornerR (2*x/Y-1) r.q1=(ownUPoly d).eval x) (hK : s.MU.length=K)
    (hw : ∀ k, r.w k=(moment σ2 (d.y0:ℂ) (k+1)).re/((k+1:ℕ):ℝ))
    (hY : 0 < Y) (u : ℝ) (hpos : 0 ≤ (p.center:ℝ)+u) :
    latticeApproxField z θ d K ((p.center:ℝ)+u)=tcTargetR s r p u := by
  have hy := d.y0_neg
  have hd : 0 < (p.center:ℝ)+u-d.y0 := by linarith
  have hW : tcIsW p=true := by simp [tcIsW,hk]
  have hR : p.kind ≠ .Right := by rw [hk]; decide
  have hO : p.kind ≠ .WOrigin := by rw [hk]; decide
  simp only [tcTargetR,hW,if_true,wModelR,wConstR,hR,if_false,tcArgs,hk,xlogSumR]
  simp only [show (TCKind.W==TCKind.WOrigin)=false by decide,Bool.false_eq_true,if_false,
    List.nil_append,List.cons_append,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  rw [latticeApproxField,V_real_value,phi0_real_closed,LatticeMomentData.mpValue,mp_real,← hq1]
  have ht : (((p.center/(s.Y/2)-1:ℚ):ℝ)+((1/(s.Y/2):ℚ):ℝ)*u)=2*((p.center:ℝ)+u)/Y-1 := by
    have hY0 : Y ≠ 0 := hY.ne'
    push_cast; rw [hYs]; field_simp; ring
  rw [ht,abs_of_pos hd]
  have hcy : (((p.center-s.y0:ℚ):ℝ)+u)=(p.center:ℝ)+u-d.y0 := by push_cast; rw [hy0]; ring
  rw [hcy,hL,hθ,hM2,hU1c,hK]
  have hsum : ∑ k ∈ Finset.range K,r.w k*((p.center:ℝ)+u-d.y0)^(-((k+1:ℕ):ℤ))=
      ∑ k ∈ Finset.range K,(moment σ2 (d.y0:ℂ) (k+1)).re/(((k+1:ℕ):ℝ)*((p.center:ℝ)+u-d.y0)^(k+1)) := by
    apply Finset.sum_congr rfl; intro k _
    rw [hw,zpow_neg,zpow_natCast]; field_simp
  rw [hsum]
  simp only [xlog]; push_cast; ring

theorem tcCheck_geom (s : SourceF) (logs : List LogEntry) (p : TCSpec) (lower upper : ℤ)
    (pos : Option Bool) (hc : tcCheck s logs p lower upper pos=true) : tcGeometryCheck s p=true := by
  cases hgc : tcGeometryCheck s p
  · exfalso; unfold tcCheck at hc; simp [buildTCBox,hgc] at hc
  · rfl

/-- A passed W cell encloses `W - θ` on its interval, once the global W allowance covers twice the
multipole error of the second segment. -/
theorem wCell_bound (s : SourceF) (logs : List LogEntry) (p : TCSpec) (lower upper : ℤ)
    (pos : Option Bool) (hc : tcCheck s logs p lower upper pos=true) (r : SourceR)
    (hlogs : LogsOK logs) (henc : SourceEnc s r) (hk : p.kind=.W)
    (z θ Y : ℝ) (hY : 0<Y) (σ1 σ2 : Measure ℂ) [IsFiniteMeasure σ2]
    (d : LatticeMomentData σ1 σ2 Y) (K : ℕ)
    (hL : r.L=Real.log |z|) (hθ : (s.theta:ℝ)=θ) (hy0 : (s.y0:ℝ)=d.y0) (hYs : (s.Y:ℝ)=Y)
    (hM2 : r.M2=σ2.real univ) (hU1c : r.U1c=d.c 0*Real.log (4/Y))
    (hq1 : ∀ x : ℝ, hornerR (2*x/Y-1) r.q1=(ownUPoly d).eval x) (hK : s.MU.length=K)
    (hw : ∀ k, r.w k=(moment σ2 (d.y0:ℂ) (k+1)).re/((k+1:ℕ):ℝ))
    (hglob : 2*mpErr (σ2.real univ) (d.supportRadius/(-d.y0)) K ≤ dec S s.globalW)
    (x : ℝ) (hx : (p.left:ℝ) ≤ x ∧ x ≤ p.right) :
    dec S lower ≤ W z (σ1+σ2) (x:ℂ)-θ ∧ W z (σ1+σ2) (x:ℂ)-θ ≤ dec S upper := by
  have hg := tcCheck_geom s logs p lower upper pos hc
  simp only [tcGeometryCheck,hk,Bool.and_eq_true,decide_eq_true_eq] at hg
  simp at hg
  obtain ⟨⟨hr0,hlr,hcl,hrc,-⟩,hl0,hrY⟩ := hg
  have hr0' : (0:ℝ) ≤ p.radius := by exact_mod_cast hr0
  have hcl' : (p.center:ℝ) ≤ p.left+p.radius := by exact_mod_cast hcl
  have hrc' : (p.right:ℝ) ≤ p.center+p.radius := by exact_mod_cast hrc
  have hl0' : (0:ℝ) ≤ p.left := by exact_mod_cast hl0
  have hrY' : (p.right:ℝ) ≤ Y := by rw [← hYs]; exact_mod_cast hrY
  have hW : tcIsW p=true := by simp [tcIsW,hk]
  set u := x-(p.center:ℝ) with hu_def
  have hxu : x=(p.center:ℝ)+u := by rw [hu_def]; ring
  have hu : |u| ≤ (p.radius:ℝ) := abs_le.mpr ⟨by linarith,by linarith⟩
  let e : ℝ → ℝ := fun v => if 0 ≤ (p.center:ℝ)+v then
    -2*(U σ2 ((((p.center:ℝ)+v:ℝ)):ℂ)-d.mpValue K ((p.center:ℝ)+v)) else 0
  have he : ∀ v, |v| ≤ (p.radius:ℝ) → |e v| ≤ dec S (if tcIsW p then s.globalW else s.globalA) := by
    intro v _
    rw [if_pos hW]
    by_cases h0 : 0 ≤ (p.center:ℝ)+v
    · simp only [e,if_pos h0,abs_mul,abs_neg,abs_two]
      exact (mul_le_mul_of_nonneg_left (second_mp_err Y σ1 σ2 d K _ h0) (by norm_num)).trans hglob
    · simp only [e,if_neg h0,abs_zero]
      exact (mul_nonneg (by norm_num)
        ((abs_nonneg _).trans (second_mp_err Y σ1 σ2 d K 0 le_rfl))).trans hglob
  have hH : (0:ℝ) ≤ 0 ∧ (0:ℝ) ≤ hullBoundR p := by
    simp [hullBoundR,hW,originBoundR,hk]
  have key := tcCheck_sound s logs p lower upper pos hc r hlogs henc 0 hH e he u hu
  have hx0 : 0 ≤ (p.center:ℝ)+u := by rw [← hxu]; linarith
  have ht := approxField_eq_target s r p hk z θ Y σ1 σ2 d K hL hθ hy0 hYs hM2 hU1c hq1 hK hw hY u hx0
  have hf := W_field_eq z θ Y hY σ1 σ2 d K x ⟨by linarith,by linarith⟩
  have heq : tcTargetR s r p u+0+e u=W z (σ1+σ2) (x:ℂ)-θ := by
    rw [hf,← ht]; simp only [e,if_pos hx0]; rw [← hxu]; ring
  rw [heq] at key
  exact ⟨key.1,key.2.1⟩

end
end CatalanCore.Li2.DecayCert.Simple
