module
public import CatalanCore.Cert.SigmaQuarter.Macros
public meta import Lean.Elab.Term

/-! Flat literal construction for the existing exact Macro record. -/
declare_syntax_cat rawmacronum
syntax num : rawmacronum
syntax "-" num : rawmacronum
syntax (name := rawMacroNumsStx) "raw_macro% " "[" rawmacronum,* "]" : term

public meta section
namespace CatalanCore.Cert.QuarterContour.RawMacroNums
open Lean Elab Term

private def intExpr : Int → Expr
  | .ofNat n => mkApp (Lean.mkConst ``Int.ofNat) (mkRawNatLit n)
  | .negSucc n => mkApp (Lean.mkConst ``Int.negSucc) (mkRawNatLit n)

/-- Construct right-nested products with every type argument supplied explicitly. -/
private def intTuple : List Int → Expr × Expr
  | [] => (Lean.mkConst ``Unit, Lean.mkConst ``Unit.unit)
  | [z] => (Lean.mkConst ``Int, intExpr z)
  | z::zs =>
    let (tailTy,tail) := intTuple zs
    let intTy := Lean.mkConst ``Int
    (mkApp2 (Lean.mkConst ``Prod [Level.zero,Level.zero]) intTy tailTy,
      mkApp4 (Lean.mkConst ``Prod.mk [Level.zero,Level.zero]) intTy tailTy (intExpr z) tail)

private def boxList : List Int → TermElabM Expr
  | [] => pure (mkApp (Lean.mkConst ``List.nil [Level.zero]) (Lean.mkConst ``SigmaQuarter.QBox))
  | a::b::c::d::e::f::g::h::rest => do
    let (quadTy,q1) := intTuple [a,b,c,d]
    let (_,q2) := intTuple [e,f,g,h]
    let box := mkApp4 (Lean.mkConst ``Prod.mk [Level.zero,Level.zero]) quadTy quadTy q1 q2
    let tail ← boxList rest
    return mkApp3 (Lean.mkConst ``List.cons [Level.zero]) (Lean.mkConst ``SigmaQuarter.QBox) box tail
  | _ => throwError "raw_macro% requires eight integer literals per box"

@[term_elab rawMacroNumsStx] def elabRawMacro : TermElab := fun stx _ => do
  let mut zs : List Int := []
  for a in stx[2].getSepArgs do
    let z : Int ← match a with
      | `(rawmacronum| $n:num) => pure (n.getNat : Int)
      | `(rawmacronum| - $n:num) => pure (-(n.getNat : Int))
      | _ => throwUnsupportedSyntax
    zs := z::zs
  zs := zs.reverse
  match zs with
  | x0::y0::i0::i1::a::b::c::d::e::f::rest =>
    if i0 < 0 || i1 < 0 then
      throwError "raw_macro% i0 and i1 must be nonnegative Nat literals"
    let (_,fd) := intTuple [a,b,c,d,e,f]
    let boxes ← boxList rest
    return mkApp6 (Lean.mkConst ``SigmaQuarter.Macro.mk)
      (intExpr x0) (intExpr y0) (mkRawNatLit i0.toNat) (mkRawNatLit i1.toNat) fd boxes
  | _ => throwError "raw_macro% requires x0,y0,i0,i1 and six far-data integers before its boxes"

end CatalanCore.Cert.QuarterContour.RawMacroNums
end

@[expose] public section
namespace CatalanCore.Cert.QuarterContour.RawMacroNums
open CatalanCore.Cert.SigmaQuarter

example : (raw_macro% [-3,0,0,2,-1,0,1,-2,3,-4,-9,-8,-7,-6,5,4,3,2] : Macro) =
    ⟨-3,0,0,2,(-1,0,1,-2,3,-4),[((-9,-8,-7,-6),(5,4,3,2))]⟩ := by rfl

example : (raw_macro% [0,-0,4294967296,4294967297,0,0,0,0,0,0] : Macro) =
    ⟨0,0,4294967296,4294967297,(0,0,0,0,0,0),[]⟩ := by rfl

example : (raw_macro% [1,-2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,-1,-2,-3,-4,-5,-6,-7,-8] : Macro) =
    ⟨1,-2,3,4,(5,6,7,8,9,10),[((11,12,13,14),(15,16,17,18)),((-1,-2,-3,-4),(-5,-6,-7,-8))]⟩ := by rfl
end CatalanCore.Cert.QuarterContour.RawMacroNums