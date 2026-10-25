module
public import Init.Data.Int.Basic
public import Init.Data.List.Basic
public meta import Lean.Elab.Term

/-! Direct construction of point literals: Int x, Int y, Nat mass, with no arithmetic evaluator. -/
declare_syntax_cat rawptnum
syntax num : rawptnum
syntax "-" num : rawptnum
syntax (name := rawPtNumsStx) "raw_pts% " "[" rawptnum,* "]" : term

public meta section
namespace CatalanCore.Cert.QuarterCompute.RawPtNums
open Lean Elab Term
private def intExpr : Int → Expr
  | .ofNat n => mkApp (Lean.mkConst ``Int.ofNat) (mkRawNatLit n)
  | .negSucc n => mkApp (Lean.mkConst ``Int.negSucc) (mkRawNatLit n)
private def prodType (a b : Expr) : Expr :=
  mkApp2 (Lean.mkConst ``Prod [Level.zero,Level.zero]) a b
private def ptType : Expr :=
  prodType (Lean.mkConst ``Int) (prodType (Lean.mkConst ``Int) (Lean.mkConst ``Nat))
private def pointList : List Int → TermElabM Expr
  | [] => pure (mkApp (Lean.mkConst ``List.nil [Level.zero]) ptType)
  | x::y::m::rest => do
    if m < 0 then throwError "raw_pts% mass must be nonnegative"
    let intTy := Lean.mkConst ``Int
    let natTy := Lean.mkConst ``Nat
    let tailTy := prodType intTy natTy
    let tail := mkApp4 (Lean.mkConst ``Prod.mk [Level.zero,Level.zero]) intTy natTy
      (intExpr y) (mkRawNatLit m.toNat)
    let point := mkApp4 (Lean.mkConst ``Prod.mk [Level.zero,Level.zero]) intTy tailTy (intExpr x) tail
    let rest ← pointList rest
    return mkApp3 (Lean.mkConst ``List.cons [Level.zero]) ptType point rest
  | _ => throwError "raw_pts% requires exactly three literals per point"
@[term_elab rawPtNumsStx] def elabRawPts : TermElab := fun stx _ => do
  let mut zs : List Int := []
  for a in stx[2].getSepArgs do
    let z : Int ← match a with
      | `(rawptnum| $n:num) => pure (n.getNat : Int)
      | `(rawptnum| - $n:num) => pure (-(n.getNat : Int))
      | _ => throwUnsupportedSyntax
    zs := z::zs
  pointList zs.reverse
end CatalanCore.Cert.QuarterCompute.RawPtNums
end

@[expose] public section
namespace CatalanCore.Cert.QuarterCompute.RawPtNums
example : (raw_pts% [-3,4,5,0,-2,0] : List (Int × Int × Nat)) =
    [(-3,4,5),(0,-2,0)] := by rfl
example : (raw_pts% [] : List (Int × Int × Nat)) = [] := by rfl
example : (raw_pts% [-0,-0,4294967296] : List (Int × Int × Nat)) =
    [(0,0,4294967296)] := by rfl
end CatalanCore.Cert.QuarterCompute.RawPtNums
