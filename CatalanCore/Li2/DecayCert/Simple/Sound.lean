module
public import CatalanCore.Li2.DecayCert.Simple.Defs
public import CatalanCore.Li2.DecayCert.Simple.Taylor.Builders
/-! Soundness of the fused lattice TC check. `buildTCBox_sound`: a built model encloses the explicit
W-type or atom-type function `tcTargetR` (x·log terms, log-affine and multipole far field, the `-2·P`
polynomial or the right-chain constant, and the affine part), up to a hull constant in
`[0, hullBoundR]` and a global truncation error bounded by `globalW`/`globalA`, given that the log table
and the source boxes enclose their real values (`LogsOK`, `SourceEnc`). `tcCheck_sound` turns a passed
`tcCheck` into the stated lower/upper bounds and sign on the whole cell. -/
@[expose] public section
set_option Elab.async false
namespace CatalanCore.Li2.DecayCert.Simple
open CatalanCore.Li2.DecayCert.LatticeSimple
noncomputable section

/-- Coefficientwise sum of real coefficient lists (the real side of `boxAddList`). -/
def addListR : List ℝ → List ℝ → List ℝ
  | [],ys => ys
  | xs,[] => xs
  | x::xs,y::ys => (x+y)::addListR xs ys

theorem evalModel_addListR (u : ℝ) : ∀ a b : List ℝ,
    evalModel (addListR a b) u=evalModel a u+evalModel b u
  | [],b => by simp [addListR,evalModel_nil']
  | x::a,[] => by simp [addListR,evalModel_nil']
  | x::a,y::b => by
    simp only [addListR,evalModel_cons,evalModel_addListR u a b]; ring

theorem forall₂_boxAddList : ∀ (ca cb : List FBox) (a b : List ℝ),
    List.Forall₂ Contains ca a → List.Forall₂ Contains cb b →
    List.Forall₂ Contains (boxAddList ca cb) (addListR a b)
  | [],cb,[],b,_,hb => by simpa [boxAddList,addListR] using hb
  | x::ca,[],y::a,[],ha,_ => by simpa [boxAddList,addListR] using ha
  | x::ca,z::cb,y::a,w::b,ha,hb => by
    simp only [boxAddList,addListR]
    rcases List.forall₂_cons.1 ha with ⟨h1,h2⟩
    rcases List.forall₂_cons.1 hb with ⟨h3,h4⟩
    exact List.Forall₂.cons (boxAddF_sound _ _ _ _ h1 h3) (forall₂_boxAddList ca cb a b h2 h4)
  | [],_,_::_,_,ha,_ => by cases ha
  | _::_,_,[],_,ha,_ => by cases ha
  | _,[],_,_::_,_,hb => by cases hb
  | _,_::_,_,[],_,hb => by cases hb

theorem dec_add' (a b : ℤ) : dec S (a+b)=dec S a+dec S b := by simp [dec,add_div]

theorem modelsF_add (a b : IntTaylorModel) (r : ℝ) (f g : ℝ → ℝ)
    (ha : ModelsF a r f) (hb : ModelsF b r g) :
    ModelsF (modelAddF a b) r (fun u => f u+g u) := by
  obtain ⟨x,hx,hf⟩ := ha; obtain ⟨y,hy,hg⟩ := hb
  refine ⟨addListR x y,forall₂_boxAddList _ _ _ _ hx hy,fun u hu => ?_⟩
  simp only [modelAddF]
  rw [evalModel_addListR,dec_add']
  calc |f u+g u-(evalModel x u+evalModel y u)|
      =|(f u-evalModel x u)+(g u-evalModel y u)| := by ring_nf
    _ ≤ |f u-evalModel x u|+|g u-evalModel y u| := abs_add_le _ _
    _ ≤ _ := add_le_add (hf u hu) (hg u hu)

theorem evalModel_map_mul (k u : ℝ) : ∀ a : List ℝ, evalModel (a.map (fun x => k*x)) u=k*evalModel a u
  | [] => by simp [evalModel_nil']
  | x::a => by simp only [List.map_cons,evalModel_cons,evalModel_map_mul k u a]; ring

theorem modelsF_scale (k : ℤ) (a : IntTaylorModel) (r : ℝ) (f : ℝ → ℝ) (ha : ModelsF a r f) :
    ModelsF (modelScaleF k a) r (fun u => (k:ℝ)*f u) := by
  obtain ⟨x,hx,hf⟩ := ha
  refine ⟨x.map (fun c => (k:ℝ)*c),?_,fun u hu => ?_⟩
  · simp only [modelScaleF]
    rw [List.forall₂_map_left_iff,List.forall₂_map_right_iff]
    exact hx.imp (fun c v h => boxScaleF_sound k c v h)
  · rw [evalModel_map_mul,← mul_sub,abs_mul]
    simp only [modelScaleF,absI_eq_abs]
    have : dec S (|k| * a.remainder)=|(k:ℝ)| * dec S a.remainder := by simp [dec,mul_div_assoc]
    rw [this]; exact mul_le_mul_of_nonneg_left (hf u hu) (abs_nonneg _)

theorem modelsF_widen (a : IntTaylorModel) (g : ℤ) (r : ℝ) (f e : ℝ → ℝ) (ha : ModelsF a r f)
    (he : ∀ u, |u| ≤ r → |e u| ≤ dec S g) :
    ModelsF ⟨a.coeff,a.remainder+g⟩ r (fun u => f u+e u) := by
  obtain ⟨x,hx,hf⟩ := ha
  refine ⟨x,hx,fun u hu => ?_⟩
  rw [dec_add']
  calc |f u+e u-evalModel x u|=|(f u-evalModel x u)+e u| := by ring_nf
    _ ≤ |f u-evalModel x u|+|e u| := abs_add_le _ _
    _ ≤ _ := add_le_add (hf u hu) (he u hu)

theorem modelsF_affine (m : IntTaylorModel) (c l : FBox) (r C L : ℝ) (f : ℝ → ℝ) (hm : ModelsF m r f)
    (hc : Contains c C) (hl : Contains l L) :
    ModelsF (addAffineF m c l) r (fun u => f u+(C+L*u)) := by
  have h0 : ModelsF ⟨[c,l],0⟩ r (fun u => C+L*u) :=
    ⟨[C,L],List.Forall₂.cons hc (List.Forall₂.cons hl List.Forall₂.nil),fun u _ => by
      simp [evalModel_cons,evalModel_nil',dec]; ring_nf⟩
  exact modelsF_add _ _ r _ _ hm h0

theorem modelsF_zero (n : ℕ) (r : ℝ) : ModelsF ⟨List.replicate n boxZero,0⟩ r (fun _ => 0) := by
  refine ⟨List.replicate n 0,?_,fun u _ => ?_⟩
  · induction n with
    | zero => exact List.Forall₂.nil
    | succ n ih => simpa [List.replicate_succ] using List.Forall₂.cons boxZero_sound ih
  · have : evalModel (List.replicate n (0:ℝ)) u=0 := by
      induction n with
      | zero => simp [evalModel_nil']
      | succ n ih => simp [List.replicate_succ,evalModel_cons,ih]
    simp [this,dec]

theorem modelsF_mono (m : IntTaylorModel) (r r' : ℝ) (f : ℝ → ℝ) (hm : ModelsF m r' f) (h : r ≤ r') :
    ModelsF m r f := by
  obtain ⟨x,hx,hf⟩ := hm; exact ⟨x,hx,fun u hu => hf u (hu.trans h)⟩

theorem modelsF_congr (m : IntTaylorModel) (r : ℝ) (f g : ℝ → ℝ) (hm : ModelsF m r f)
    (h : ∀ u, |u| ≤ r → f u=g u) : ModelsF m r g := by
  obtain ⟨x,hx,hf⟩ := hm; exact ⟨x,hx,fun u hu => by rw [← h u hu]; exact hf u hu⟩


/-! ### Real side -/

/-- Every log table entry encloses the logarithm of its argument. -/
def LogsOK (logs : List LogEntry) : Prop := ∀ e ∈ logs, Contains e.bounds (Real.log (e.arg:ℝ))

theorem lookupLogF_sound (logs : List LogEntry) (hl : LogsOK logs) (arg : ℚ) :
    ∀ (ids : List ℕ) (b : FBox), lookupLogF logs arg ids=some b → Contains b (Real.log (arg:ℝ))
  | [],b,h => by simp [lookupLogF] at h
  | i::is,b,h => by
    simp only [lookupLogF] at h
    cases he : logs[i]? with
    | none => rw [he] at h; exact lookupLogF_sound logs hl arg is b h
    | some e =>
      rw [he] at h
      by_cases ha : e.arg=arg
      · simp only [ha,if_true,Option.some.injEq] at h
        subst h; rw [← ha]; exact hl e (List.mem_of_getElem? he)
      · simp only [ha,if_false] at h; exact lookupLogF_sound logs hl arg is b h

def hornerR (x : ℝ) (q : List ℝ) : ℝ := q.foldl (fun acc b => x*acc+b) 0

def xlogSumR (args : List (ℤ×ℤ×ℚ)) (u : ℝ) : ℝ :=
  (args.map fun a => (a.1:ℝ)*xlog ((a.2.2:ℝ)+(a.2.1:ℝ)*u)).sum

theorem xlogFoldF_sound (lg : ℚ → Option FBox) (hlg : ∀ a b, lg a=some b → Contains b (Real.log (a:ℝ)))
    (R : ℤ) (J : ℕ) (r : ℝ) (hr : r ≤ dec S R) :
    ∀ (args : List (ℤ×ℤ×ℚ)) (m m' : IntTaylorModel) (g : ℝ → ℝ), ModelsF m r g →
      xlogFoldF lg R J args m=some m' → ModelsF m' r (fun u => g u+xlogSumR args u)
  | [],m,m',g,hm,h => by
    simp only [xlogFoldF,Option.some.injEq] at h; subst h
    simpa [xlogSumR] using hm
  | (sg,di,x)::t,m,m',g,hm,h => by
    simp only [xlogFoldF,Option.bind_eq_some_iff] at h
    obtain ⟨lx,hlx,a,ha,h⟩ := h
    have hA := modelsF_mono _ _ _ _ (xlogBoxF_sound sg di (boxOfQ x) R lx J x (boxOfQ_sound x) (hlg x lx hlx) a ha) hr
    have ih := xlogFoldF_sound lg hlg R J r hr t _ m' _ (modelsF_add _ _ _ _ _ hm hA) h
    refine modelsF_congr _ _ _ _ ih (fun u _ => ?_)
    simp only [xlogSumR,List.map_cons,List.sum_cons]; ring

/-- Real values that the numeric source fields enclose. -/
structure SourceR where
  M1 : ℝ
  M2 : ℝ
  L : ℝ
  U1c : ℝ
  U2c : ℝ
  U1y0 : ℝ
  q1 : List ℝ
  qA : List ℝ
  fk : List ℝ
  w : ℕ → ℝ

def SourceEnc (s : SourceF) (r : SourceR) : Prop :=
  Contains s.m1 r.M1 ∧ Contains s.m2 r.M2 ∧ Contains s.L r.L ∧ Contains s.U1c r.U1c ∧
  Contains s.U2c r.U2c ∧ Contains s.U1y0 r.U1y0 ∧
  List.Forall₂ (fun a x => |x-dec S a| ≤ dec S s.P1width) s.P1mid r.q1 ∧
  List.Forall₂ (fun a x => |x-dec S a| ≤ dec S s.PAwidth) s.PAmid r.qA ∧
  List.Forall₂ Contains s.MU ((List.range s.MU.length).map r.w) ∧
  (∀ k < s.MU.length, |r.w k| ≤ |r.M2| * ((max |s.y0+4| |-1-s.y0| : ℚ):ℝ)^(k+1)/((k+1:ℕ):ℝ)) ∧
  List.Forall₂ Contains s.firstOverK r.fk

/-- The far-field part of a W-type model (log-affine plus multipole, and `-2 P1` off the right chain). -/
def wModelR (s : SourceF) (r : SourceR) (p : TCSpec) (u : ℝ) : ℝ :=
  2*r.M2*Real.log (((p.center-s.y0:ℚ):ℝ)+u)
  - 2*∑ k ∈ Finset.range s.MU.length, r.w k*(((p.center-s.y0:ℚ):ℝ)+u)^(-((k+1:ℕ):ℤ))
  + (if p.kind=.Right then 0 else -2*hornerR (((p.center/(s.Y/2)-1:ℚ):ℝ)+((1/(s.Y/2):ℚ):ℝ)*u) r.q1)

/-- Its constant term. -/
def wConstR (s : SourceF) (r : SourceR) (p : TCSpec) : ℝ :=
  1+r.L*(p.center:ℝ)-(s.theta:ℝ)-
  (if p.kind=.Right then 2*(r.M1*(Real.log ((4/s.Y:ℚ):ℝ)+Real.log (p.rightR:ℝ))+
      hornerR (p.rightR:ℝ) (r.fk.reverse++[0]))
   else 2*r.U1c)

def originBoundR (p : TCSpec) : ℝ := if p.kind=.WOrigin then -2*((p.right:ℝ)*Real.log (p.right:ℝ)) else 0

theorem contains_hull (b : FBox) (v H : ℝ) (hb : Contains b v) (hH : 0 ≤ H ∧ H ≤ v) : Contains (0,b.2) H :=
  ⟨by simpa [dec] using hH.1,hH.2.trans hb.2⟩

theorem wPartF_sound (s : SourceF) (lg : ℚ → Option FBox) (hlg : ∀ a b, lg a=some b → Contains b (Real.log (a:ℝ)))
    (p : TCSpec) (R : ℤ) (r : SourceR) (henc : SourceEnc s r) (rr : ℝ) (hrR : rr ≤ dec S R)
    (hrp : rr ≤ (p.radius:ℝ)) (m : IntTaylorModel) (cn lin : FBox)
    (h : wPartF s lg p R=some (m,cn,lin)) (H : ℝ) (hH : 0 ≤ H ∧ H ≤ originBoundR p)
    (e : ℝ → ℝ) (he : ∀ u, |u| ≤ rr → |e u| ≤ dec S s.globalW) :
    ModelsF m rr (fun u => wModelR s r p u+e u) ∧ Contains cn (wConstR s r p+H) ∧ Contains lin r.L := by
  obtain ⟨hM1,hM2,hL,hU1c,-,-,hq1,-,hMU,hw,hfk⟩ := henc
  simp only [wPartF,Option.bind_eq_some_iff] at h
  obtain ⟨logd,hlogd,lm,hlm,mm,hmm,mc,hmc,cn',hcn',heq⟩ := h
  simp only [Option.some.injEq,Prod.mk.injEq] at heq
  obtain ⟨rfl,rfl,rfl⟩ := heq
  have hd := boxOfQ_sound (p.center-s.y0)
  have hLM := modelsF_mono _ _ _ _ (logAffineBoxF_sound _ _ R logd p.mpJetOrder _ _
    (boxScaleF_sound 2 s.m2 r.M2 hM2) hd (hlg _ _ hlogd) lm hlm) hrR
  have hMM := modelsF_mono _ _ _ _ (mpBoxKF_sound s.MU s.m2 _ _ R p.mpJetOrder p.mpCut r.M2 _ r.w hM2 hd hMU hw mm hmm) hrR
  have h0 := modelsF_add _ _ _ _ _ (modelsF_add _ _ _ _ _ (modelsF_zero (p.jetOrder+1) rr) hLM) hMM
  have h1 := modelsF_widen _ s.globalW rr _ e h0 he
  have hC0 : Contains (boxSubF (boxAddF boxOne (boxMulF s.L (boxOfQ p.center))) (boxOfQ s.theta))
      (1+r.L*(p.center:ℝ)-(s.theta:ℝ)) :=
    boxSubF_sound _ _ _ _ (boxAddF_sound _ _ _ _ boxOne_sound (boxMulF_sound _ _ _ _ hL (boxOfQ_sound _)))
      (boxOfQ_sound _)
  refine ⟨?_,?_,hL⟩
  · by_cases hk : p.kind=.Right
    · simp only [wTailF,hk,beq_self_eq_true,if_true] at hmc
      split_ifs at hmc with hc
      simp only [Option.bind_eq_some_iff,Option.some.injEq] at hmc
      obtain ⟨lr,-,ly,-,rfl⟩ := hmc
      refine modelsF_congr _ _ _ _ h1 (fun u _ => ?_)
      simp only [wModelR,hk,if_true]; ring
    · have hk' : (p.kind==TCKind.Right)=false := by simpa using hk
      simp only [wTailF,hk',Bool.false_eq_true,if_false,Option.bind_eq_some_iff,Option.some.injEq] at hmc
      obtain ⟨pm,hpm,rfl⟩ := hmc
      have hP := modelsF_mono _ _ _ _ (midPolyBoxF_sound _ _ _ _ _ _ _ hq1 pm hpm) hrp
      have h2 := modelsF_add _ _ _ _ _ h1 (modelsF_scale (-2) _ _ _ hP)
      refine modelsF_congr _ _ _ _ h2 (fun u _ => ?_)
      simp only [wModelR,hk,if_false,hornerR]; push_cast; ring
  · have hT : Contains mc.2 (wConstR s r p) := by
      by_cases hk : p.kind=.Right
      · simp only [wTailF,hk,beq_self_eq_true,if_true] at hmc
        split_ifs at hmc with hc
        simp only [Option.bind_eq_some_iff,Option.some.injEq] at hmc
        obtain ⟨lr,hlr,ly,hly,rfl⟩ := hmc
        have hr1 : |(p.rightR:ℝ)| ≤ 1 := by
          push_neg at hc
          have h0 : (0:ℝ) < p.rightR := by exact_mod_cast hc.1
          have h1 : (p.rightR:ℝ) < 1 := by exact_mod_cast hc.2.1
          rw [abs_le]; constructor <;> linarith
        have hv := boxAddF_sound _ _ _ _ (boxMulF_sound _ _ _ _ hM1 (boxAddF_sound _ _ _ _ (hlg _ _ hly) (hlg _ _ hlr)))
          (polyExactF_sound p.rightR hr1 _ (r.fk.reverse++[0])
            (List.rel_append (List.forall₂_reverse_iff.2 hfk) (List.Forall₂.cons boxZero_sound List.Forall₂.nil)))
        have := boxSubF_sound _ _ _ _ hC0 (boxScaleF_sound 2 _ _ hv)
        simpa only [wConstR,hk,if_true,hornerR,Int.cast_ofNat] using this
      · have hk' : (p.kind==TCKind.Right)=false := by simpa using hk
        simp only [wTailF,hk',Bool.false_eq_true,if_false,Option.bind_eq_some_iff,Option.some.injEq] at hmc
        obtain ⟨pm,-,rfl⟩ := hmc
        have := boxSubF_sound _ _ _ _ hC0 (boxScaleF_sound 2 _ _ hU1c)
        simpa only [wConstR,hk,if_false,Int.cast_ofNat] using this
    by_cases ho : p.kind=.WOrigin
    · simp only [originF,ho,beq_self_eq_true,if_true] at hcn'
      split_ifs at hcn' with hc
      simp only [Option.bind_eq_some_iff,Option.some.injEq] at hcn'
      obtain ⟨lh,hlh,rfl⟩ := hcn'
      have hb := boxScaleF_sound (-2) _ _ (boxMulF_sound _ _ _ _ (boxOfQ_sound p.right) (hlg _ _ hlh))
      refine boxAddF_sound _ _ _ _ hT (contains_hull _ _ H hb ?_)
      simpa only [originBoundR,ho,if_true,Int.cast_neg,Int.cast_ofNat] using hH
    · have ho' : (p.kind==TCKind.WOrigin)=false := by simpa using ho
      simp only [originF,ho',Bool.false_eq_true,if_false,Option.some.injEq] at hcn'
      subst hcn'
      have hH0 : H=0 := by simp only [originBoundR,ho,if_false] at hH; linarith [hH.1,hH.2]
      simpa [hH0] using hT

def aConstR (s : SourceF) (r : SourceR) (p : TCSpec) : ℝ :=
  1-r.L*(p.center:ℝ)-((s.rho+s.theta:ℚ):ℝ)-2*(r.U2c+r.U1y0)

def atomBoundR (p : TCSpec) : ℝ :=
  if p.kind=.AtomLeft then -3*(((p.right-p.left:ℚ):ℝ)*Real.log ((p.right-p.left:ℚ):ℝ))
  else if p.kind=.AtomRight then -1*(((p.right-p.left:ℚ):ℝ)*Real.log ((p.right-p.left:ℚ):ℝ)) else 0

theorem aPartF_sound (s : SourceF) (lg : ℚ → Option FBox) (hlg : ∀ a b, lg a=some b → Contains b (Real.log (a:ℝ)))
    (p : TCSpec) (r : SourceR) (henc : SourceEnc s r) (rr : ℝ) (hrp : rr ≤ (p.radius:ℝ))
    (m : IntTaylorModel) (cn lin : FBox) (h : aPartF s lg p=some (m,cn,lin))
    (H : ℝ) (hH : 0 ≤ H ∧ H ≤ atomBoundR p) (e : ℝ → ℝ) (he : ∀ u, |u| ≤ rr → |e u| ≤ dec S s.globalA) :
    ModelsF m rr (fun u => -2*hornerR ((p.center:ℝ)+u) r.qA+e u) ∧
      Contains cn (aConstR s r p+H) ∧ Contains lin (-r.L) := by
  obtain ⟨-,-,hL,-,hU2c,hU1y0,-,hqA,-,-,-⟩ := henc
  simp only [aPartF,Option.bind_eq_some_iff] at h
  obtain ⟨pm,hpm,cn',hcn',heq⟩ := h
  simp only [Option.some.injEq,Prod.mk.injEq] at heq
  obtain ⟨rfl,rfl,rfl⟩ := heq
  have hP := modelsF_mono _ _ _ _ (midPolyBoxF_sound _ _ _ _ _ _ _ hqA pm hpm) hrp
  have h0 := modelsF_add _ _ _ _ _ (modelsF_zero (p.jetOrder+1) rr) (modelsF_scale (-2) _ _ _ hP)
  have h1 := modelsF_widen _ s.globalA rr _ e h0 he
  refine ⟨modelsF_congr _ _ _ _ h1 (fun u _ => ?_),?_,boxNegF_sound _ _ hL⟩
  · simp only [hornerR]; push_cast; ring
  · have hC0 : Contains (boxSubF (boxSubF (boxSubF boxOne (boxMulF s.L (boxOfQ p.center))) (boxOfQ (s.rho+s.theta)))
        (boxScaleF 2 (boxAddF s.U2c s.U1y0))) (aConstR s r p) := by
      have h1 := boxMulF_sound _ _ _ _ hL (boxOfQ_sound p.center)
      have h2 := boxSubF_sound _ _ _ _ boxOne_sound h1
      have h3 := boxSubF_sound _ _ _ _ h2 (boxOfQ_sound (s.rho+s.theta))
      have h4 := boxSubF_sound _ _ _ _ h3 (boxScaleF_sound 2 _ _ (boxAddF_sound _ _ _ _ hU2c hU1y0))
      simpa only [aConstR,Int.cast_ofNat] using h4
    by_cases hk : p.kind=.AtomLeft ∨ p.kind=.AtomRight
    · have hk' : (p.kind==TCKind.AtomLeft || p.kind==TCKind.AtomRight)=true := by
        rcases hk with hk|hk <;> simp [hk]
      simp only [hullAF,hk',if_true] at hcn'
      by_cases hc : p.right-p.left≤0 ∨ 1/3<p.right-p.left
      · rw [if_pos hc] at hcn'; simp at hcn'
      rw [if_neg hc] at hcn'
      simp only [Option.bind_eq_some_iff,Option.some.injEq] at hcn'
      obtain ⟨lh,hlh,rfl⟩ := hcn'
      have hX := boxMulF_sound _ _ _ _ (boxOfQ_sound (p.right-p.left)) (hlg _ _ hlh)
      rcases hk with hk|hk
      · rw [if_pos (show (p.kind==TCKind.AtomLeft)=true by simp [hk])]
        exact boxAddF_sound _ _ _ _ hC0 (contains_hull _ _ H (boxScaleF_sound (-3) _ _ hX)
          ⟨hH.1,by simpa [atomBoundR,hk] using hH.2⟩)
      · have hl : p.kind ≠ .AtomLeft := by rw [hk]; decide
        rw [if_neg (show ¬(p.kind==TCKind.AtomLeft)=true by simp [hl])]
        exact boxAddF_sound _ _ _ _ hC0 (contains_hull _ _ H (boxScaleF_sound (-1) _ _ hX)
          ⟨hH.1,by simpa [atomBoundR,hk,hl] using hH.2⟩)
    · have hk' : (p.kind==TCKind.AtomLeft || p.kind==TCKind.AtomRight)=false := by
        push_neg at hk; simp [hk.1,hk.2]
      simp only [hullAF,hk',Bool.false_eq_true,if_false,Option.some.injEq] at hcn'
      subst hcn'
      push_neg at hk
      have hH0 : H=0 := by simp only [atomBoundR,hk.1,hk.2,if_false] at hH; linarith [hH.1,hH.2]
      simpa [hH0] using hC0

/-- The real function a TC cell encloses, up to the hull constant and the global truncation error. -/
def tcTargetR (s : SourceF) (r : SourceR) (p : TCSpec) (u : ℝ) : ℝ :=
  xlogSumR (tcArgs p) u+
  if tcIsW p then wModelR s r p u+wConstR s r p+r.L*u
  else -2*hornerR ((p.center:ℝ)+u) r.qA+aConstR s r p+(-r.L)*u

def hullBoundR (p : TCSpec) : ℝ := if tcIsW p then originBoundR p else atomBoundR p

theorem buildTCBox_sound (s : SourceF) (logs : List LogEntry) (p : TCSpec) (r : SourceR)
    (hlogs : LogsOK logs) (henc : SourceEnc s r) (m : IntTaylorModel) (h : buildTCBox s logs p=some m)
    (H : ℝ) (hH : 0 ≤ H ∧ H ≤ hullBoundR p) (e : ℝ → ℝ)
    (he : ∀ u, |u| ≤ (p.radius:ℝ) → |e u| ≤ dec S (if tcIsW p then s.globalW else s.globalA)) :
    ModelsF m (p.radius:ℝ) (fun u => tcTargetR s r p u+H+e u) := by
  have hlg : ∀ a b, (fun a => lookupLogF logs a p.logIds) a=some b → Contains b (Real.log (a:ℝ)) :=
    fun a b hb => lookupLogF_sound logs hlogs a p.logIds b hb
  have hrR : (p.radius:ℝ) ≤ dec S (boxOfQ p.radius).2 := (boxOfQ_sound p.radius).2
  simp only [buildTCBox] at h
  by_cases hg : (!tcGeometryCheck s p)=true
  · rw [if_pos hg] at h; simp at h
  rw [if_neg hg] at h
  simp only [Option.bind_eq_some_iff,Option.some.injEq] at h
  obtain ⟨⟨m0,cn,lin⟩,ht,m1,hm1,rfl⟩ := h
  by_cases hw : tcIsW p
  · simp only [hw,if_true] at ht he
    obtain ⟨hM,hC,hL⟩ := wPartF_sound s _ hlg p _ r henc _ hrR le_rfl m0 cn lin ht H
      (by simpa [hullBoundR,hw] using hH) e he
    have hX := xlogFoldF_sound _ hlg _ p.jetOrder _ hrR (tcArgs p) m0 m1 _ hM hm1
    refine modelsF_congr _ _ _ _ (modelsF_affine _ _ _ _ _ _ _ hX hC hL) (fun u _ => ?_)
    simp only [tcTargetR,hw,if_true]; ring
  · have hw' : tcIsW p=false := by simpa using hw
    simp only [hw',Bool.false_eq_true,if_false] at ht he
    obtain ⟨hM,hC,hL⟩ := aPartF_sound s _ hlg p r henc _ le_rfl m0 cn lin ht H
      (by simpa [hullBoundR,hw'] using hH) e he
    have hX := xlogFoldF_sound _ hlg _ p.jetOrder _ hrR (tcArgs p) m0 m1 _ hM hm1
    refine modelsF_congr _ _ _ _ (modelsF_affine _ _ _ _ _ _ _ hX hC hL) (fun u _ => ?_)
    simp only [tcTargetR,hw',Bool.false_eq_true,if_false]; ring

/-- A passed fused check bounds the cell's target function on the whole cell, with the claimed sign. -/
theorem tcCheck_sound (s : SourceF) (logs : List LogEntry) (p : TCSpec) (lower upper : ℤ)
    (pos : Option Bool) (hc : tcCheck s logs p lower upper pos=true) (r : SourceR)
    (hlogs : LogsOK logs) (henc : SourceEnc s r) (H : ℝ) (hH : 0 ≤ H ∧ H ≤ hullBoundR p) (e : ℝ → ℝ)
    (he : ∀ u, |u| ≤ (p.radius:ℝ) → |e u| ≤ dec S (if tcIsW p then s.globalW else s.globalA))
    (u : ℝ) (hu : |u| ≤ (p.radius:ℝ)) :
    dec S lower ≤ tcTargetR s r p u+H+e u ∧ tcTargetR s r p u+H+e u ≤ dec S upper ∧
      (pos=some true → 0 ≤ tcTargetR s r p u+H+e u) ∧ (pos=some false → tcTargetR s r p u+H+e u ≤ 0) := by
  unfold tcCheck at hc
  cases hb : buildTCBox s logs p with
  | none => rw [hb] at hc; simp at hc
  | some m =>
    rw [hb] at hc
    simp only [Bool.and_eq_true,decide_eq_true_eq] at hc
    obtain ⟨⟨-,hlo,hhi⟩,hs⟩ := hc
    have hm := buildTCBox_sound s logs p r hlogs henc m hb H hH e he
    obtain ⟨h1,h2⟩ := modelRangeF_sound p.radius m _ hm u hu
    have hL : dec S lower ≤ dec S (modelRangeF p.radius m).1 := by
      unfold dec; exact div_le_div_of_nonneg_right (by exact_mod_cast hlo) (le_of_lt S_real_pos)
    have hU : dec S (modelRangeF p.radius m).2 ≤ dec S upper := by
      unfold dec; exact div_le_div_of_nonneg_right (by exact_mod_cast hhi) (le_of_lt S_real_pos)
    refine ⟨hL.trans h1,h2.trans hU,fun hp => ?_,fun hp => ?_⟩
    · subst hp; simp only [decide_eq_true_eq] at hs
      exact le_trans (by unfold dec; exact div_nonneg (by exact_mod_cast hs) (le_of_lt S_real_pos)) (hL.trans h1)
    · subst hp; simp only [decide_eq_true_eq] at hs
      exact le_trans (h2.trans hU) (by unfold dec; exact div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast hs) (le_of_lt S_real_pos))

#print axioms modelsF_add
#print axioms modelsF_scale
#print axioms lookupLogF_sound
#print axioms xlogFoldF_sound
#print axioms wPartF_sound
#print axioms aPartF_sound
#print axioms buildTCBox_sound
#print axioms tcCheck_sound
end
end CatalanCore.Li2.DecayCert.Simple
