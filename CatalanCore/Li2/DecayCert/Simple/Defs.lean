module
public import CatalanCore.Li2.DecayCert.Simple.Taylor.Defs
public import CatalanCore.Li2.DecayCert.Lattice.Simple.Pattern
@[expose] public section
set_option Elab.async false
namespace CatalanCore.Li2.DecayCert.Simple
structure LogEntry where
  arg : ℚ
  bounds : FBox
  deriving DecidableEq
structure SourceF where
  z : ℚ
  Y : ℚ
  y0 : ℚ
  phi : ℚ
  theta : ℚ
  rho : ℚ
  m1 : FBox
  m2 : FBox
  L : FBox
  U1c : FBox
  U2c : FBox
  U1y0 : FBox
  P1d : List FBox
  PAd : List FBox
  MU : List FBox
  firstOverK : List FBox
  globalW : ℤ
  globalA : ℤ
  P1mid : List ℤ := P1d.map midF
  PAmid : List ℤ := PAd.map midF
  P1width : ℤ := (P1d.map widthF).foldl max 0
  PAwidth : ℤ := (PAd.map widthF).foldl max 0
  deriving DecidableEq
inductive TCKind where
  | W | WOrigin | Atom | AtomLeft | AtomRight | Right
  deriving DecidableEq
structure TCSpec where
  left : ℚ
  right : ℚ
  center : ℚ
  radius : ℚ
  kind : TCKind
  jetOrder : ℕ
  mpJetOrder : ℕ
  mpCut : ℕ
  logIds : List ℕ
  rightR : ℚ
  deriving DecidableEq
structure TCWitness where
  spec : TCSpec
  model : IntTaylorModel
  lower : ℤ
  upper : ℤ
  deriving DecidableEq
def sourcePolyCacheCheck (s : SourceF) : Bool :=
  decide (s.P1mid=s.P1d.map midF ∧ s.PAmid=s.PAd.map midF ∧
    (s.P1d.map widthF).foldl max 0≤s.P1width ∧ (s.PAd.map widthF).foldl max 0≤s.PAwidth)

def lookupLogF (logs : List LogEntry) (arg : ℚ) : List ℕ → Option FBox
  | [] => none
  | i::is => match logs[i]? with
    | none => lookupLogF logs arg is
    | some e => if e.arg=arg then some e.bounds else lookupLogF logs arg is
def addAffineF (m : IntTaylorModel) (c l : FBox) : IntTaylorModel := modelAddF m ⟨[c,l],0⟩
def polyEvalF (x : FBox) (p : List FBox) : FBox :=
  p.foldl (fun v a => boxAddF a (boxMulF x v)) boxZero
def tcGeometryCheck (s : SourceF) (p : TCSpec) : Bool :=
  let w:=p.kind==.W || p.kind==.WOrigin
  let a:=p.kind==.Atom || p.kind==.AtomLeft || p.kind==.AtomRight
  decide (0≤p.radius ∧ p.left≤p.right ∧ p.center-p.radius≤p.left ∧ p.right≤p.center+p.radius ∧ 2≤p.jetOrder) &&
    (!w || decide (0≤p.left ∧ p.right≤s.Y)) &&
    (!a || decide (1≤p.left ∧ p.right≤4)) &&
    (p.kind != .AtomLeft || decide (p.left=1)) &&
    (p.kind != .AtomRight || decide (p.right=4)) &&
    (p.kind != .Right || decide (s.Y≤p.left))
def buildTCBox (s : SourceF) (logs : List LogEntry) (p : TCSpec) : Option IntTaylorModel := do
  if !tcGeometryCheck s p then none else do
    let c:=p.center
    let R:=(boxOfQ p.radius).2
    let lg := fun arg => lookupLogF logs arg p.logIds
    let isW := p.kind==.W || p.kind==.WOrigin || p.kind==.Right
    let mut m : IntTaylorModel := ⟨List.replicate (p.jetOrder+1) boxZero,0⟩
    let mut cn := boxZero
    let mut lin := boxZero
    if isW then
      let logd ← lg (c-s.y0)
      let lm ← logAffineBoxF (boxScaleF 2 s.m2) (boxOfQ (c-s.y0)) R logd p.mpJetOrder
      let mm ← mpBoxKF s.MU s.m2 (max |s.y0+4| |-1-s.y0|) (boxOfQ (c-s.y0)) R p.mpJetOrder p.mpCut
      m := modelAddF (modelAddF m lm) mm
      m := ⟨m.coeff,m.remainder+s.globalW⟩
      cn := boxSubF (boxAddF boxOne (boxMulF s.L (boxOfQ c))) (boxOfQ s.theta)
      lin := s.L
      if p.kind==.Right then
        if p.rightR≤0 ∨ 1≤p.rightR ∨ s.Y*(1+p.rightR)^2/(4*p.rightR)<p.right then none else do
          let lr ← lg p.rightR
          let ly ← lg (4/s.Y)
          let v:=boxAddF (boxMulF s.m1 (boxAddF ly lr)) (polyExactF p.rightR (s.firstOverK.reverse++[boxZero]))
          cn := boxSubF cn (boxScaleF 2 v)
      else
        let yh:=s.Y/2
        let pm ← midPolyBoxF s.P1mid s.P1width (c/yh-1) (1/yh) p.radius p.jetOrder
        m := modelAddF m (modelScaleF (-2) pm)
        cn := boxSubF cn (boxScaleF 2 s.U1c)
      if p.kind==.WOrigin then
        if p.left≠0 ∨ p.right≤0 ∨ 1/3<p.right then none else do
          let lh ← lg p.right
          let h:=boxScaleF (-2) (boxMulF (boxOfQ p.right) lh)
          cn := boxAddF cn (0,h.2)
    else
      cn := boxSubF (boxSubF (boxSubF boxOne (boxMulF s.L (boxOfQ c))) (boxOfQ (s.rho+s.theta))) (boxScaleF 2 (boxAddF s.U2c s.U1y0))
      lin := boxNegF s.L
      let pm ← midPolyBoxF s.PAmid s.PAwidth c 1 p.radius p.jetOrder
      m := modelAddF m (modelScaleF (-2) pm)
      m := ⟨m.coeff,m.remainder+s.globalA⟩
      if p.kind==.AtomLeft || p.kind==.AtomRight then
        let h:=p.right-p.left
        if h≤0 ∨ 1/3<h then none else do
          let lh ← lg h
          let sg : ℤ := if p.kind==.AtomLeft then -3 else -1
          let hull:=boxScaleF sg (boxMulF (boxOfQ h) lh)
          cn := boxAddF cn (0,hull.2)
    let args : List (ℤ×ℤ×ℚ) :=
      if isW then [(3,1,c+1),(-1,1,c+4)]++(if p.kind==.WOrigin then [] else [(-2,1,c)])
      else [(2,1,c)]++(if p.kind==.AtomLeft then [] else [(-3,1,c-1)])++(if p.kind==.AtomRight then [] else [(-1,-1,4-c)])
    for (sg,di,x) in args do
      let lx ← lg x
      let a ← xlogBoxF sg di (boxOfQ x) R lx p.jetOrder
      m := modelAddF m a
    pure (addAffineF m cn lin)
def tcBuildCheck (s : SourceF) (logs : List LogEntry) (w : TCWitness) : Bool := decide (buildTCBox s logs w.spec=some w.model)
def tcRangeCheck (w : TCWitness) : Bool :=
  modelValidF w.spec.radius w.model &&
    let b:=modelRangeF w.spec.radius w.model
    decide (w.lower≤b.1 ∧ b.2≤w.upper)
def tcSignCheck (positive : Bool) (w : TCWitness) : Bool := if positive then decide (0≤w.lower) else decide (w.upper≤0)
def tcRootCostF (delta : ℚ) (w : TCWitness) : ℤ := ceilDiv ((2*max w.upper 0+max (-w.lower) 0)*delta.num) delta.den

/-- Fused check: the model is computed and consumed in this declaration. -/
def tcCheck (s : SourceF) (logs : List LogEntry) (p : TCSpec)
    (lower upper : ℤ) (positive : Option Bool) : Bool :=
  match buildTCBox s logs p with
  | none=>false
  | some m=>modelValidF p.radius m &&
      (let b:=modelRangeF p.radius m; decide (lower≤b.1 ∧ b.2≤upper)) &&
      (match positive with | none=>true | some true=>decide (0≤lower) | some false=>decide (upper≤0))

def tcRootCostBoundsF (delta : ℚ) (lower upper : ℤ) : ℤ :=
  ceilDiv ((2*max upper 0+max (-lower) 0)*delta.num) delta.den

theorem tcRootCostBoundsF_eq (delta : ℚ) (w : TCWitness) :
    tcRootCostBoundsF delta w.lower w.upper=tcRootCostF delta w := rfl

theorem sourcePolyCacheCheck_spec (s : SourceF) :
    sourcePolyCacheCheck s=true ↔ s.P1mid=s.P1d.map midF ∧ s.PAmid=s.PAd.map midF ∧
      (s.P1d.map widthF).foldl max 0≤s.P1width ∧ (s.PAd.map widthF).foldl max 0≤s.PAwidth := by
  simp only [sourcePolyCacheCheck,decide_eq_true_eq]

theorem tcBuildCheck_spec (s : SourceF) (logs : List LogEntry) (w : TCWitness) :
    tcBuildCheck s logs w=true ↔ buildTCBox s logs w.spec=some w.model := by
  simp only [tcBuildCheck,decide_eq_true_eq]
theorem tcRangeCheck_spec (w : TCWitness) :
    tcRangeCheck w=true ↔ modelValidF w.spec.radius w.model=true ∧
      w.lower≤(modelRangeF w.spec.radius w.model).1 ∧ (modelRangeF w.spec.radius w.model).2≤w.upper := by
  simp only [tcRangeCheck,Bool.and_eq_true,decide_eq_true_eq]
theorem tcCheck_some_spec (s : SourceF) (logs : List LogEntry) (p : TCSpec)
    (lower upper : ℤ) (positive : Bool) :
    tcCheck s logs p lower upper (some positive)=true ↔ ∃m,
      buildTCBox s logs p=some m ∧ tcRangeCheck ⟨p,m,lower,upper⟩=true ∧
      tcSignCheck positive ⟨p,m,lower,upper⟩=true := by
  cases h:buildTCBox s logs p with
  | none=>simp [tcCheck,h]
  | some m=>cases positive <;> simp [tcCheck,h,tcRangeCheck,tcSignCheck,Bool.and_eq_true,and_assoc]

theorem tcCheck_none_spec (s : SourceF) (logs : List LogEntry) (p : TCSpec) (lower upper : ℤ) :
    tcCheck s logs p lower upper none=true ↔ ∃m,
      buildTCBox s logs p=some m ∧ tcRangeCheck ⟨p,m,lower,upper⟩=true := by
  cases h:buildTCBox s logs p with
  | none=>simp [tcCheck,h]
  | some m=>simp [tcCheck,h,tcRangeCheck]
#print axioms sourcePolyCacheCheck_spec
#print axioms tcRootCostBoundsF_eq
#print axioms tcCheck_some_spec
#print axioms tcCheck_none_spec
#print axioms tcBuildCheck_spec
#print axioms tcRangeCheck_spec
end CatalanCore.Li2.DecayCert.Simple
