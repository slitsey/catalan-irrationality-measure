module
public import CatalanMeasure.Cert.DescartesBudget
@[expose] public meta section
namespace CatalanMeasure.Cert
open Lean Meta Elab Tactic

/-- Reuse the already-audited, separately kernel-checked integer recurrence
chain to prove one supplied coarse homogeneous substitution. -/
elab "certify_hom_substitution" : tactic => withMainContext do
  let goal ← getMainGoal
  let some (_,lhs,_) := (← goal.getType).eq? |
    throwError "expected an explicit homogeneous-substitution equality"
  unless lhs.getAppFn.isConstOf ``ipHom do throwError "expected ipHom"
  let args := lhs.getAppArgs
  unless args.size=4 do throwError "unexpected homogeneous-substitution arity"
  let aE := args[0]!
  let bE := args[1]!
  let dE := args[2]!
  let pE := args[3]!
  let p ← unsafe evalExpr (List Int) (mkApp (mkConst ``List [Level.zero]) (mkConst ``Int)) pE
  let a ← unsafe evalExpr Int (mkConst ``Int) aE
  let b ← unsafe evalExpr Int (mkConst ``Int) bE
  let d ← unsafe evalExpr Int (mkConst ``Int) dE
  let base ← mkAppM ``ipHom #[aE,bE,dE,toExpr ([]:List Int)]
  let proof ← buildHomWitness aE bE dE a b d p.reverse [] [1] [] (← mkEqRefl base)
  unless ← isDefEq (← inferType proof) (← goal.getType) do
    throwError "computed witness does not match the supplied substitution"
  goal.assign proof
  setGoals []

end CatalanMeasure.Cert
