module

public import CatalanArchive.CatalanFrames.Lambda.Final
public import CatalanArchive.ChallengeLambda

/-!
# Parity gate for λ (negative control A and D), deleted at cut-over

* A: the generic `measureExp` reproduces the legacy exponent `lambdaMeasureExp`.
* D: the new final theorems have literally the statements of `ChallengeLambda.lean`.
-/

@[expose] public section

open CatalanCore

namespace CatalanParity.Lambda

theorem controlA : (measureExp (68726 / 10000) (313 / 105) (31111 / 10000) (3 / 4) 1
    CatalanFrames.Lambda.lamRule.s) = CatalanLambda.lambdaMeasureExp := by
  rw [CatalanFrames.Lambda.lamRule_s, CatalanLambda.lambdaMeasureExp_eq]
  norm_num [measureExp]

theorem controlA' : measureExp (68726 / 10000) (313 / 105) (31111 / 10000) (3 / 4) 1 1
    = 31682445459 / 409965000 := by norm_num [measureExp]

example : (type_of% @CatalanLambdaChallenge.lambda_irrational) =
    (type_of% @CatalanFrames.Lambda.lambda_irrational_solution) := rfl

example : (type_of% @CatalanLambdaChallenge.lambda_irrationalityMeasure) =
    (type_of% @CatalanFrames.Lambda.lambda_irrationalityMeasure_solution) := rfl

example : (type_of% @CatalanLambdaChallenge.lambda_irrationalityMeasure_78) =
    (type_of% @CatalanFrames.Lambda.lambda_irrationalityMeasure_78_solution) := rfl

end CatalanParity.Lambda

#print axioms CatalanFrames.Lambda.lambda_irrational_solution
#print axioms CatalanFrames.Lambda.lambda_irrationalityMeasure_solution
#print axioms CatalanFrames.Lambda.lambda_irrationalityMeasure_78_solution
