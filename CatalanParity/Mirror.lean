module

public import CatalanFrames.LambdaMirror.Final
public import ChallengeLambda

/-!
# Parity gate for the mirror constant (WP8), deleted at cut-over

The new final theorems have literally the statements of the mirror block of `ChallengeLambda.lean`.
-/

@[expose] public section

namespace CatalanParity.Mirror

example : (type_of% @CatalanLambdaChallenge.lambdaMirror_irrational) =
    (type_of% @CatalanFrames.LambdaMirror.lambdaMirror_irrational_solution) := rfl

example : (type_of% @CatalanLambdaChallenge.lambdaMirror_irrationalityMeasure) =
    (type_of% @CatalanFrames.LambdaMirror.lambdaMirror_irrationalityMeasure_solution) := rfl

example : (type_of% @CatalanLambdaChallenge.lambdaMirror_irrationalityMeasure_78) =
    (type_of% @CatalanFrames.LambdaMirror.lambdaMirror_irrationalityMeasure_78_solution) := rfl

example : (type_of% @CatalanLambdaChallenge.catalan_add_irrational) =
    (type_of% @CatalanFrames.LambdaMirror.catalan_add_irrational_solution) := rfl

example : (type_of% @CatalanLambdaChallenge.catalan_add_irrationalityMeasure_79) =
    (type_of% @CatalanFrames.LambdaMirror.catalan_add_irrationalityMeasure_79_solution) := rfl

end CatalanParity.Mirror

#print axioms CatalanFrames.LambdaMirror.lambdaMirror_irrational_solution
#print axioms CatalanFrames.LambdaMirror.lambdaMirror_irrationalityMeasure_solution
#print axioms CatalanFrames.LambdaMirror.lambdaMirror_irrationalityMeasure_78_solution
#print axioms CatalanFrames.LambdaMirror.catalan_add_irrational_solution
#print axioms CatalanFrames.LambdaMirror.catalan_add_irrationalityMeasure_79_solution
