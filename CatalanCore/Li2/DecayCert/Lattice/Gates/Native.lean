module
public import CatalanCore.Li2.DecayCert.Lattice.Gates.Own
public import CatalanCore.Li2.DecayCert.Lattice.Gates.RightMacro
public import CatalanCore.Li2.DecayCert.Lattice.Gates.Lists.Stieltjes
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 800000
namespace CatalanCore.Li2.DecayCert.LatticeGate

def modelNoDisc : ModelWitness → Bool
  | .segDisc _ => false
  | .add a b => modelNoDisc a && modelNoDisc b
  | .scale a => modelNoDisc a
  | _ => true

def compileNoDisc (lo hi : ℚ) : CellExpr → ModelWitness → Option CompiledModel
  | .constant e, .simple => some ⟨[e],seRat 0⟩
  | .variable, .simple => some ⟨[seRat 0,seRat 1],seRat 0⟩
  | .linear a b, .simple => some ⟨[a,b],seRat 0⟩
  | .poly p, .order J =>
      let rt := max |lo| |hi|
      some ⟨(List.range (J+1)).map (fun j : ℕ => seRat (coeffQ p j)),
        seRat (((List.range p.length).map (fun j : ℕ => if J < j then |coeffQ p j| *rt^j else 0)).sum)⟩
  | .add a b, .add wa wb => do
      let ma ← compileNoDisc lo hi a wa
      let mb ← compileNoDisc lo hi b wb
      pure ⟨combineCoeffs ma.coeff mb.coeff,seAdd ma.error mb.error⟩
  | .scale c a, .scale wa => do
      let ma ← compileNoDisc lo hi a wa
      pure ⟨ma.coeff.map (seScale c),seScale |c| ma.error⟩
  | .segment d p e, .segOwn J n => ownCompileFast d p e lo hi J n
  | .segment _ _ _, .segDisc _ => none
  | .ulog, .regular w =>
      if lo=0 ∧ 0 < hi then some (ulogCompile hi w.terms) else none
  | .xlog a b, .seeds terms =>
      if a=0 ∧ 0 < b ∧ lo=0 ∧ 0 < hi then
        let m := ulogCompile hi terms
        some ⟨combineCoeffs (m.coeff.map (seScale b))
          [seRat 0,seScale b (.log terms b)],seScale b m.error⟩
      else none
  | .fre a b, .seeds terms =>
      if cqSq a=0 ∧ lo=0 ∧ hi=0 then some ⟨[seRat 0],seRat 0⟩
      else if cqSq a=0 ∧ cqSq b ≠ 0 ∧ lo=0 ∧ 0 < hi then
        let m := ulogCompile hi terms
        some ⟨combineCoeffs (m.coeff.map (seScale b.1))
          [seRat 0,seSub (seReMulLog terms b b) (seRat b.1)],seScale |b.1| m.error⟩
      else none
  | src, .regular w => regularCompile src lo hi w
  | _, _ => none

theorem compileNoDisc_eq (lo hi : ℚ) (e : CellExpr) (w : ModelWitness) (hn : modelNoDisc w=true) :
    compileNoDisc lo hi e w=compileModel lo hi e w := by
  induction e generalizing w <;> cases w <;>
    simp_all [compileNoDisc,compileModel,ownCompileFast_eq,modelNoDisc]

def farModelFastCheck (d : QSegment) (mu : List ℚ)
    (y0 L Y H p r : ℚ) (K : ℕ) : Bool :=
  realSupportCheck d L Y && ordinaryMomentFast d y0 K mu &&
    decide (0≤H ∧ 0≤r ∧ H<p-y0-r ∧ |L-y0|≤H ∧ |Y-y0|≤H)
theorem farModelFastCheck_eq (d : QSegment) (mu : List ℚ) (y0 L Y H p r : ℚ) (K : ℕ) :
    farModelFastCheck d mu y0 L Y H p r K=farModelCheck d mu y0 L Y H p r K := by
  simp only [farModelFastCheck,farModelCheck,ordinaryMomentFast_eq]

def stieltjesModelFastCheck (d : QSegment) (phi : ℚ) (sm : List ℚ)
    (Y r : ℚ) (K : ℕ) : Bool :=
  let y0 := d.mid.1-d.half.1*((phi+phi⁻¹)/2)
  realSupportCheck d 0 Y && stieltjesMomentFast d phi K sm &&
    decide (0≤Y ∧ y0<0 ∧ 0≤r ∧ r< -y0)
theorem stieltjesModelFastCheck_eq (d : QSegment) (phi : ℚ) (sm : List ℚ) (Y r : ℚ) (K : ℕ) :
    stieltjesModelFastCheck d phi sm Y r K=stieltjesModelCheck d phi sm Y r K := by
  simp only [stieltjesModelFastCheck,stieltjesModelCheck,stieltjesMomentFast_eq]

def WNativeModel (terms : ℕ) (z : ℚ) (first second : QSegment)
    (p r y0 H : ℚ) (mu : List ℚ) (K J : ℕ) (base : ModelWitness) : Option CompiledModel := do
  let b ← compileNoDisc (-1) 1 ((.add (fieldExpr terms z (p,0) (r,0)) (.scale 2 (.segment first (p,0) (r,0))))) base
  pure (addCompiled b (scaleCompiled (-2)
    (affineCompiled (farModel terms (second.c 0) mu y0 H p r K J) 0 r)))

def WNativeParentCheck (terms : ℕ) (z : ℚ) (first second : QSegment)
    (p r y0 L Y H : ℚ) (mu : List ℚ) (K J : ℕ) (base : ModelWitness)
    (S : ℤ) (w : CellWitness) (boxes : List (ℤ×ℤ)) : Bool :=
  decide (0≤p-|r|) && farModelFastCheck second mu y0 L Y H p r K &&
    (match WNativeModel terms z first second p r y0 H mu K J base with
     | none=>false | some m=>bernParentCheck S m w boxes)

def atomNativeModel (terms : ℕ) (z : ℚ) (first second : QSegment)
    (p r phi R : ℚ) (sm : List ℚ) (K : ℕ) (base : ModelWitness) : Option CompiledModel := do
  let b ← compileNoDisc (-1) 1 ((.add (atomExpr terms z [] p r) (.scale 2 (.segment second (-p,0) (-r,0))))) base
  pure (addCompiled b (scaleCompiled (-2)
    (affineCompiled (stieltjesModel terms first phi sm R K)
      (-p-stieltjesCenter first phi) (-r))))

def atomNativeParentCheck (terms : ℕ) (z : ℚ) (first second : QSegment)
    (p r phi Y R : ℚ) (sm : List ℚ) (K : ℕ) (base : ModelWitness)
    (S : ℤ) (w : CellWitness) (boxes : List (ℤ×ℤ)) : Bool :=
  decide (1≤p-|r| ∧ p+|r|≤4) && stieltjesModelFastCheck first phi sm Y R K &&
    affineDomainCheck (-p-stieltjesCenter first phi) (-r) R &&
    (match atomNativeModel terms z first second p r phi R sm K base with
     | none=>false | some m=>bernParentCheck S m w boxes)

def rightNativeModel (z : ℚ) (first second : QSegment) (c : RightCell)
    (y0 H : ℚ) (mu : List ℚ) (K J : ℕ) (base : ModelWitness) : Option CompiledModel := do
  let b ← compileNoDisc (-1) 1 ((.add (fieldExpr c.terms z (rightCenter c,0) (rightRadius c,0)) (.scale 2 (.constant (segConstant c.terms first (1/c.r,0)))))) base
  pure (addCompiled b (scaleCompiled (-2)
    (affineCompiled (farModel c.terms (second.c 0) mu y0 H
      (rightCenter c) (rightRadius c) K J) 0 (rightRadius c))))

def rightNativeParentCheck (z supportEnd : ℚ) (first second : QSegment) (c : RightCell)
    (y0 L Y H : ℚ) (mu : List ℚ) (K J : ℕ) (base : ModelWitness)
    (S : ℤ) (w : CellWitness) (boxes : List (ℤ×ℤ)) : Bool :=
  decide (supportEnd≤c.left ∧ c.left<c.right ∧ 0<c.r ∧ c.r<1 ∧ c.right=supportEnd*(1+c.r)^2/(4*c.r)) && farModelFastCheck second mu y0 L Y H (rightCenter c) (rightRadius c) K &&
    (match rightNativeModel z first second c y0 H mu K J base with
     | none=>false | some m=>bernParentCheck S m w boxes)

theorem WNativeModel_eq (terms : ℕ) (z : ℚ) (d : LatticeInput) (p r y0 H : ℚ)
    (mu : List ℚ) (K J : ℕ) (base : ModelWitness) (hn : modelNoDisc base=true) :
    WNativeModel terms z d.first d.second p r y0 H mu K J base=WMacroModel terms z d p r y0 H mu K J base := by
  unfold WNativeModel WMacroModel WBase
  rw [compileNoDisc_eq (-1) 1 _ base hn]

theorem WNativeParentCheck_eq (terms : ℕ) (z : ℚ) (d : LatticeInput)
    (p r y0 L Y H : ℚ) (mu : List ℚ) (K J : ℕ) (base : ModelWitness) (hn : modelNoDisc base=true)
    (S : ℤ) (w : CellWitness) (boxes : List (ℤ×ℤ)) :
    WNativeParentCheck terms z d.first d.second p r y0 L Y H mu K J base S w boxes=
      WMacroParentCheck terms z d p r y0 L Y H mu K J base S w boxes := by
  unfold WNativeParentCheck WMacroParentCheck
  rw [farModelFastCheck_eq,WNativeModel_eq terms z d p r y0 H mu K J base hn]
  rfl

theorem atomNativeModel_eq (terms : ℕ) (z : ℚ) (d : LatticeInput) (p r phi R : ℚ)
    (sm : List ℚ) (K : ℕ) (base : ModelWitness) (hn : modelNoDisc base=true) :
    atomNativeModel terms z d.first d.second p r phi R sm K base=atomMacroModel terms z d p r phi R sm K base := by
  unfold atomNativeModel atomMacroModel atomBase
  rw [compileNoDisc_eq (-1) 1 _ base hn]

theorem atomNativeParentCheck_eq (terms : ℕ) (z : ℚ) (d : LatticeInput)
    (p r phi Y R : ℚ) (sm : List ℚ) (K : ℕ) (base : ModelWitness) (hn : modelNoDisc base=true)
    (S : ℤ) (w : CellWitness) (boxes : List (ℤ×ℤ)) :
    atomNativeParentCheck terms z d.first d.second p r phi Y R sm K base S w boxes=
      atomMacroParentCheck terms z d p r phi Y R sm K base S w boxes := by
  unfold atomNativeParentCheck atomMacroParentCheck
  rw [stieltjesModelFastCheck_eq,atomNativeModel_eq terms z d p r phi R sm K base hn]
  rfl

theorem rightNativeModel_eq (z : ℚ) (d : LatticeInput) (c : RightCell) (y0 H : ℚ)
    (mu : List ℚ) (K J : ℕ) (base : ModelWitness) (hn : modelNoDisc base=true) :
    rightNativeModel z d.first d.second c y0 H mu K J base=rightMacroModel z d c y0 H mu K J base := by
  unfold rightNativeModel rightMacroModel rightBase
  rw [compileNoDisc_eq (-1) 1 _ base hn]

theorem rightNativeParentCheck_eq (z : ℚ) (d : LatticeInput) (c : RightCell)
    (y0 L Y H : ℚ) (mu : List ℚ) (K J : ℕ) (base : ModelWitness) (hn : modelNoDisc base=true)
    (S : ℤ) (w : CellWitness) (boxes : List (ℤ×ℤ)) :
    rightNativeParentCheck z d.Y d.first d.second c y0 L Y H mu K J base S w boxes=
      rightMacroParentCheck z d c y0 L Y H mu K J base S w boxes := by
  unfold rightNativeParentCheck rightMacroParentCheck rightGeometryCheck
  rw [farModelFastCheck_eq,rightNativeModel_eq z d c y0 H mu K J base hn]
  rfl
#print axioms compileNoDisc_eq
#print axioms WNativeParentCheck_eq
#print axioms atomNativeParentCheck_eq
#print axioms rightNativeParentCheck_eq
end CatalanCore.Li2.DecayCert.LatticeGate
