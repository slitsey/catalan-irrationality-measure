module
public import Init.Data.Int.Basic
public import Init.Data.List.Basic
public meta import Lean.Elab.Term

/-! Direct literal construction of pure QBox lists: eight Int coordinates per box. -/
declare_syntax_cat rawqboxnum
syntax num : rawqboxnum
syntax "-" num : rawqboxnum
syntax (name := rawQBoxNumsStx) "raw_qboxes% " "[" rawqboxnum,* "]" : term

public meta section
namespace CatalanCore.Cert.QuarterCompute.RawQBoxNums
open Lean Elab Term

private def intExpr : Int → Expr
  | .ofNat n => mkApp (Lean.mkConst ``Int.ofNat) (mkRawNatLit n)
  | .negSucc n => mkApp (Lean.mkConst ``Int.negSucc) (mkRawNatLit n)

private def prodType (a b : Expr) : Expr :=
  mkApp2 (Lean.mkConst ``Prod [Level.zero,Level.zero]) a b

private def intTuple : List Int → Expr × Expr
  | [] => (Lean.mkConst ``Unit,Lean.mkConst ``Unit.unit)
  | [z] => (Lean.mkConst ``Int,intExpr z)
  | z::zs =>
    let (tailTy,tail) := intTuple zs
    let intTy := Lean.mkConst ``Int
    (prodType intTy tailTy,
      mkApp4 (Lean.mkConst ``Prod.mk [Level.zero,Level.zero]) intTy tailTy (intExpr z) tail)

private def qboxType : Expr :=
  let intTy := Lean.mkConst ``Int
  let quadTy := prodType intTy (prodType intTy (prodType intTy intTy))
  prodType quadTy quadTy

private def boxList : List Int → TermElabM Expr
  | [] => pure (mkApp (Lean.mkConst ``List.nil [Level.zero]) qboxType)
  | a::b::c::d::e::f::g::h::rest => do
    let (quadTy,q1) := intTuple [a,b,c,d]
    let (_,q2) := intTuple [e,f,g,h]
    let box := mkApp4 (Lean.mkConst ``Prod.mk [Level.zero,Level.zero]) quadTy quadTy q1 q2
    let tail ← boxList rest
    return mkApp3 (Lean.mkConst ``List.cons [Level.zero]) qboxType box tail
  | _ => throwError "raw_qboxes% requires exactly eight integer literals per box"

@[term_elab rawQBoxNumsStx] def elabRawQBoxes : TermElab := fun stx _ => do
  let mut zs : List Int := []
  for a in stx[2].getSepArgs do
    let z : Int ← match a with
      | `(rawqboxnum| $n:num) => pure (n.getNat : Int)
      | `(rawqboxnum| - $n:num) => pure (-(n.getNat : Int))
      | _ => throwUnsupportedSyntax
    zs := z::zs
  boxList zs.reverse

end CatalanCore.Cert.QuarterCompute.RawQBoxNums
end

@[expose] public section
namespace CatalanCore.Cert.QuarterCompute.RawQBoxNums

example : (raw_qboxes% [-3,-2,-1,-0,1,2,3,4] :
    List ((Int × Int × Int × Int) × (Int × Int × Int × Int))) =
    [((-3,-2,-1,0),(1,2,3,4))] := by rfl

example : (raw_qboxes% [] : List ((Int × Int × Int × Int) × (Int × Int × Int × Int))) = [] := by rfl

example : (raw_qboxes% [1,2,3,4,5,6,7,8,-1,-2,-3,-4,-5,-6,-7,-8] :
    List ((Int × Int × Int × Int) × (Int × Int × Int × Int))) =
    [((1,2,3,4),(5,6,7,8)),((-1,-2,-3,-4),(-5,-6,-7,-8))] := by rfl
end CatalanCore.Cert.QuarterCompute.RawQBoxNums