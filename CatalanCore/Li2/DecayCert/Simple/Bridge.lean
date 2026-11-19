module
public import CatalanCore.Li2.DecayCert.Simple.Sound
public import CatalanCore.Li2.DecayCert.Lattice.Primitive
public import CatalanCore.Li2.DecayCert.Lattice.MultipoleUniform
public import CatalanCore.Li2.DecayCert.Simple.Integrals
public import CatalanCore.Li2.DecayCert.Lattice.Stieltjes.Model
/-! Bridge from the fused TC check to the lattice field on the first segment. `W_field_eq` splits
`W - θ` into `latticeApproxField` and the multipole remainder of the second segment, `second_mp_err`
bounds that remainder uniformly, `approxField_eq_target` identifies `latticeApproxField` with the
W-type target `tcTargetR` under the source identifications, and `wCell_bound` turns a passed W cell
into lower and upper bounds for `W - θ` on its interval. On `[1, 4]`, `atomField_eq_target` and
`atomCell_bound` do the same for `A - θ`, with the first segment by its Stieltjes expansion about `y0`
and the second by its own-support formula. -/
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


/-- The potential of a sum of two measures at a point where both log integrals exist. -/
theorem U_add_of_integrable (σ1 σ2 : Measure ℂ) (w : ℂ)
    (h1 : Integrable (fun u => Real.log ‖w-u‖) σ1) (h2 : Integrable (fun u => Real.log ‖w-u‖) σ2) :
    U (σ1+σ2) w=U σ1 w+U σ2 w := by
  change -(∫ u,Real.log ‖w-u‖ ∂(σ1+σ2))=-(∫ u,Real.log ‖w-u‖ ∂σ1)+ -(∫ u,Real.log ‖w-u‖ ∂σ2)
  rw [integral_add_measure h1 h2]
  ring

/-- The singular x·log terms that an end cell leaves out of its Taylor model. -/
def atomHullTerm (p : TCSpec) (x : ℝ) : ℝ :=
  (if p.kind=.AtomLeft then -3*xlog (x-1) else 0)+(if p.kind=.AtomRight then -xlog (4-x) else 0)

/-- Exact identity on an atom cell: `A - θ` is the atom-type TC target plus the omitted end term,
minus twice the Stieltjes remainder of the first segment at `-x`. -/
theorem atomField_eq_target (s : SourceF) (r : SourceR) (p : TCSpec)
    (hk : p.kind=.Atom ∨ p.kind=.AtomLeft ∨ p.kind=.AtomRight)
    (z ρ θ : ℝ) (σ1 σ2 : Measure ℂ) (y0 : ℝ) (K : ℕ) (f2 : ℝ → ℝ)
    (hL : r.L=Real.log |z|) (hρθ : ((s.rho+s.theta:ℚ):ℝ)=ρ+θ) (hU1y0 : r.U1y0=U σ1 (y0:ℂ))
    (u : ℝ) (x : ℝ) (hx : x=(p.center:ℝ)+u)
    (hi1 : Integrable (fun v => Real.log ‖(-(x:ℂ))-v‖) σ1)
    (hi2 : Integrable (fun v => Real.log ‖(-(x:ℂ))-v‖) σ2)
    (hU2 : U σ2 (-(x:ℂ))=r.U2c+f2 x)
    (hqA : hornerR x r.qA=f2 x+∑ k ∈ Finset.range (K+1),
      inverseMoment σ1 y0 k*(-x-y0)^k/(k:ℝ)) :
    A z ρ (σ1+σ2) x-θ=tcTargetR s r p u+atomHullTerm p x-
      2*(U σ1 (((y0+(-x-y0):ℝ)):ℂ)-evalModel (stieltjesCoeffs σ1 y0 K) (-x-y0)) := by
  subst hx
  have hW : tcIsW p=false := by
    rcases hk with h|h|h <;> simp [tcIsW,h]
  have hyx : (((y0+(-((p.center:ℝ)+u)-y0):ℝ)):ℂ)=-((((p.center:ℝ)+u:ℝ)):ℂ) := by push_cast; ring
  have e0 : ((p.center:ℚ):ℝ)+((1:ℤ):ℝ)*u=(p.center:ℝ)+u := by push_cast; ring
  have e1 : ((p.center-1:ℚ):ℝ)+((1:ℤ):ℝ)*u=(p.center:ℝ)+u-1 := by push_cast; ring
  have e2 : ((4-p.center:ℚ):ℝ)+((-1:ℤ):ℝ)*u=4-((p.center:ℝ)+u) := by push_cast; ring
  rw [hyx,evalModel_stieltjesCoeffs,← hU1y0,A,U_add_of_integrable σ1 σ2 _ hi1 hi2,hU2,omega_closed]
  simp only [tcTargetR,hW,Bool.false_eq_true,if_false,aConstR,xlogSumR,tcArgs]
  rw [hqA,hρθ,hL]
  rcases hk with h|h|h
  · simp only [h,show (TCKind.Atom==TCKind.AtomLeft)=false by decide,
      show (TCKind.Atom==TCKind.AtomRight)=false by decide,Bool.false_eq_true,↓reduceIte,
      List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      atomHullTerm,reduceCtorEq,e0,e1,e2]
    simp only [xlog]; ring
  · simp only [h,show (TCKind.AtomLeft==TCKind.AtomLeft)=true by decide,
      show (TCKind.AtomLeft==TCKind.AtomRight)=false by decide,Bool.false_eq_true,↓reduceIte,
      List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      atomHullTerm,reduceCtorEq,e0,e1,e2]
    simp only [xlog]; ring
  · simp only [h,show (TCKind.AtomRight==TCKind.AtomLeft)=false by decide,
      show (TCKind.AtomRight==TCKind.AtomRight)=true by decide,Bool.false_eq_true,↓reduceIte,
      List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      atomHullTerm,reduceCtorEq,e0,e1,e2]
    simp only [xlog]; ring

/-- `t log t` decreases on `[0, h]` once `h ≤ 1/3 < 1/e`. -/
theorem xlog_ge_end (t h : ℝ) (ht : 0 ≤ t) (hth : t ≤ h) (hh : h ≤ 1/3) : xlog h ≤ xlog t := by
  unfold xlog
  rcases ht.eq_or_lt with h0|htp
  · subst h0; simp only [zero_mul]
    exact Real.mul_log_nonpos (ht.trans hth) (by linarith)
  have hhp : 0 < h := htp.trans_le hth
  have hl3 : 1 ≤ Real.log 3 := (Real.le_log_iff_exp_le (by norm_num)).mpr (by linarith [Real.exp_one_lt_d9])
  have hlh : Real.log h+1 ≤ 0 := by
    have := Real.log_le_log hhp hh
    rw [one_div,Real.log_inv] at this; linarith
  have hq : Real.log h-Real.log t ≤ h/t-1 := by
    rw [← Real.log_div hhp.ne' htp.ne']; exact Real.log_le_sub_one_of_pos (div_pos hhp htp)
  have hq' : t*(Real.log h-Real.log t) ≤ h-t := by
    have h1 := mul_le_mul_of_nonneg_left hq htp.le
    have e : t*(h/t-1)=h-t := by field_simp
    rw [e] at h1; exact h1
  nlinarith [mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hth) hlh]

theorem atomHull_bounds (p : TCSpec) (hk : p.kind=.Atom ∨ p.kind=.AtomLeft ∨ p.kind=.AtomRight)
    (hl : p.kind=.AtomLeft → p.left=1) (hr : p.kind=.AtomRight → p.right=4)
    (hw : p.kind ≠ .Atom → p.right-p.left ≤ 1/3) (x : ℝ) (hx : (p.left:ℝ) ≤ x ∧ x ≤ p.right) :
    0 ≤ atomHullTerm p x ∧ atomHullTerm p x ≤ atomBoundR p := by
  rcases hk with h|h|h
  · simp [atomHullTerm,atomBoundR,h]
  · have h1 := hl h
    have hw' : ((p.right-p.left:ℚ):ℝ) ≤ 1/3 := by
      rw [show (1/3:ℝ)=((1/3:ℚ):ℝ) by norm_num]; exact Rat.cast_le.mpr (hw (by rw [h]; decide))
    have h1' : (p.left:ℝ)=1 := by exact_mod_cast h1
    have ht0 : 0 ≤ x-1 := by linarith [hx.1]
    have hth : x-1 ≤ ((p.right-p.left:ℚ):ℝ) := by push_cast; linarith [hx.2]
    have hm := xlog_ge_end _ _ ht0 hth hw'
    have hn : xlog (x-1) ≤ 0 := Real.mul_log_nonpos ht0 (by linarith)
    simp only [atomHullTerm,atomBoundR,h,if_true,show TCKind.AtomLeft ≠ TCKind.AtomRight by decide,
      if_false,add_zero]
    unfold xlog at hm hn ⊢
    constructor <;> linarith
  · have h4 := hr h
    have hw' : ((p.right-p.left:ℚ):ℝ) ≤ 1/3 := by
      rw [show (1/3:ℝ)=((1/3:ℚ):ℝ) by norm_num]; exact Rat.cast_le.mpr (hw (by rw [h]; decide))
    have h4' : (p.right:ℝ)=4 := by exact_mod_cast h4
    have ht0 : 0 ≤ 4-x := by linarith [hx.2]
    have hth : 4-x ≤ ((p.right-p.left:ℚ):ℝ) := by push_cast; linarith [hx.1]
    have hm := xlog_ge_end _ _ ht0 hth hw'
    have hn : xlog (4-x) ≤ 0 := Real.mul_log_nonpos ht0 (by linarith)
    simp only [atomHullTerm,atomBoundR,h,if_true,show TCKind.AtomRight ≠ TCKind.AtomLeft by decide,
      if_false,zero_add]
    unfold xlog at hm hn ⊢
    constructor <;> linarith

/-- A passed atom cell encloses `A - θ` on its interval, once the global atom allowance covers twice
the Stieltjes remainder of the first segment on `[-4, -1]`. -/
theorem atomCell_bound (s : SourceF) (logs : List LogEntry) (p : TCSpec) (lower upper : ℤ)
    (pos : Option Bool) (hc : tcCheck s logs p lower upper pos=true) (r : SourceR)
    (hlogs : LogsOK logs) (henc : SourceEnc s r)
    (hk : p.kind=.Atom ∨ p.kind=.AtomLeft ∨ p.kind=.AtomRight)
    (hw : p.kind ≠ .Atom → p.right-p.left ≤ 1/3)
    (z ρ θ Y : ℝ) (hY : 0 ≤ Y) (σ1 σ2 : Measure ℂ) [IsFiniteMeasure σ1]
    (hs1 : σ1 {s | s.im ≠ 0 ∨ s.re<0 ∨ Y<s.re}=0)
    (y0 rr : ℝ) (hy : y0<0) (hsep : rr < -y0) (hrr : -1-y0 ≤ rr ∧ 4+y0 ≤ rr) (K : ℕ) (f2 : ℝ → ℝ)
    (hL : r.L=Real.log |z|) (hρθ : ((s.rho+s.theta:ℚ):ℝ)=ρ+θ) (hU1y0 : r.U1y0=U σ1 (y0:ℂ))
    (hi1 : ∀ x ∈ Icc (1:ℝ) 4, Integrable (fun v => Real.log ‖(-(x:ℂ))-v‖) σ1)
    (hi2 : ∀ x ∈ Icc (1:ℝ) 4, Integrable (fun v => Real.log ‖(-(x:ℂ))-v‖) σ2)
    (hU2 : ∀ x ∈ Icc (1:ℝ) 4, U σ2 (-(x:ℂ))=r.U2c+f2 x)
    (hqA : ∀ x ∈ Icc (1:ℝ) 4, hornerR x r.qA=f2 x+∑ k ∈ Finset.range (K+1),
      inverseMoment σ1 y0 k*(-x-y0)^k/(k:ℝ))
    (hglob : 2*mpErr (σ1.real univ) (rr/(-y0)) K ≤ dec S s.globalA)
    (x : ℝ) (hx : (p.left:ℝ) ≤ x ∧ x ≤ p.right) :
    dec S lower ≤ A z ρ (σ1+σ2) x-θ ∧ A z ρ (σ1+σ2) x-θ ≤ dec S upper := by
  have hg := tcCheck_geom s logs p lower upper pos hc
  have hW : tcIsW p=false := by rcases hk with h|h|h <;> simp [tcIsW,h]
  have hA : (p.kind==.Atom || p.kind==.AtomLeft || p.kind==.AtomRight)=true := by
    rcases hk with h|h|h <;> simp [h]
  have hnW : (p.kind==.W || p.kind==.WOrigin)=false := by
    rcases hk with h|h|h <;> simp [h]
  simp only [tcGeometryCheck,Bool.and_eq_true] at hg
  obtain ⟨⟨⟨⟨⟨h0,-⟩,h14b⟩,hlb⟩,hrb⟩,-⟩ := hg
  obtain ⟨hr0,hlr,hcl,hrc,-⟩ := of_decide_eq_true h0
  rw [hA,Bool.not_true,Bool.false_or] at h14b
  have h14 := of_decide_eq_true h14b
  have hl1 : (1:ℝ) ≤ p.left := by exact_mod_cast h14.1
  have hr4 : (p.right:ℝ) ≤ 4 := by exact_mod_cast h14.2
  have hcl' : (p.center:ℝ)-p.radius ≤ p.left := by exact_mod_cast hcl
  have hrc' : (p.right:ℝ) ≤ p.center+p.radius := by exact_mod_cast hrc
  have hlk : p.kind=.AtomLeft → p.left=1 := by
    intro h; rw [h,show (TCKind.AtomLeft != TCKind.AtomLeft)=false by decide,Bool.false_or] at hlb
    exact of_decide_eq_true hlb
  have hrk : p.kind=.AtomRight → p.right=4 := by
    intro h; rw [h,show (TCKind.AtomRight != TCKind.AtomRight)=false by decide,Bool.false_or] at hrb
    exact of_decide_eq_true hrb
  have hmod := logPot_stieltjes_model σ1 y0 rr Y hy (by linarith [hrr.1]) hY hsep hs1 K
  set u := x-(p.center:ℝ) with hu_def
  have hxu : x=(p.center:ℝ)+u := by rw [hu_def]; ring
  have hu : |u| ≤ (p.radius:ℝ) := abs_le.mpr ⟨by linarith,by linarith⟩
  have hx14 : x ∈ Icc (1:ℝ) 4 := ⟨by linarith [hx.1],by linarith [hx.2]⟩
  let e : ℝ → ℝ := fun v => if (p.center:ℝ)+v ∈ Icc (1:ℝ) 4 then
    -2*(U σ1 (((y0+(-((p.center:ℝ)+v)-y0):ℝ)):ℂ)-evalModel (stieltjesCoeffs σ1 y0 K) (-((p.center:ℝ)+v)-y0))
    else 0
  have herr0 : 0 ≤ mpErr (σ1.real univ) (rr/(-y0)) K := hmod.2.1
  have he : ∀ v, |v| ≤ (p.radius:ℝ) → |e v| ≤ dec S (if tcIsW p then s.globalW else s.globalA) := by
    intro v _
    rw [hW,if_neg (by decide)]
    by_cases h0 : (p.center:ℝ)+v ∈ Icc (1:ℝ) 4
    · simp only [e,if_pos h0,abs_mul,abs_neg,abs_two]
      have hb := hmod.2.2 (-((p.center:ℝ)+v)-y0) (abs_le.mpr ⟨by linarith [h0.2,hrr.2],by linarith [h0.1,hrr.1]⟩)
      linarith
    · simp only [e,if_neg h0,abs_zero]; linarith
  have hH := atomHull_bounds p hk hlk hrk hw x hx
  have hH' : 0 ≤ atomHullTerm p x ∧ atomHullTerm p x ≤ hullBoundR p :=
    ⟨hH.1,by simp only [hullBoundR,hW,Bool.false_eq_true,if_false]; exact hH.2⟩
  have key := tcCheck_sound s logs p lower upper pos hc r hlogs henc (atomHullTerm p x) hH' e he u hu
  have hid := atomField_eq_target s r p hk z ρ θ σ1 σ2 y0 K f2 hL hρθ hU1y0 u x hxu
    (hi1 x hx14) (hi2 x hx14) (hU2 x hx14) (hqA x hx14)
  have heq : tcTargetR s r p u+atomHullTerm p x+e u=A z ρ (σ1+σ2) x-θ := by
    rw [hid]; simp only [e]; rw [← hxu,if_pos hx14]; ring
  rw [heq] at key
  exact ⟨key.1,key.2.1⟩

end
end CatalanCore.Li2.DecayCert.Simple
