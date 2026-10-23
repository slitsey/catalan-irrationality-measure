module
public import CatalanMeasure.G728.Main
@[expose] public section

/-!
# Audit of the 728 scalar stack

Exact input/budget audit.  Every literal constant used by the 728 scalar stack is restated
below as a theorem, so it can be compared with `witness728_data.json` and `lean-status.md`:

* target `U = 141027507/62500000`
* second cost `c2 = 429033/100000`, weight cost `17913/1000`
* `rho = 20 c2 + 17913/1000 = 259299/2500`, `kappa = 1820000/259299`, `rho*kappa = 728`
* `eta = 5993/3125`, `chi = 649/1000 = 507/2000 + 3331/10000 + 624/10000`, `delta = 1/10^7`
* second-trial caps: `MX = -97745957/10^8`, `MY = -156655368/10^8`,
  fieldCap `= MX + MY = -10176053/4000000`, residual `MR = -5247033/10^8`,
  normCap `= 24149189/31250000`, nearCap `-3/4`, residual domain `401/2500 <= |x|`
* first trial: old `FirstStrongTrial` (normCap 67761/10^5, fieldCap -247913/10^5, lambda 168493357/10^8,
  first cost 421/100) with the budget re-proved at `U`
* Chebyshev exponent `3 rho max(18/(eta+chi),4) < 2183`
-/

namespace CatalanMeasure.G728
open CatalanMeasure.Parametric

theorem audit_constants :
    target728 = 141027507/62500000 ∧ secondCost728 = 429033/100000 ∧
    gapWeightCost = 17913/1000 ∧ rho728 = 20*secondCost728 + gapWeightCost ∧
    rho728 = 259299/2500 ∧ kappa728 = 728/rho728 ∧ kappa728 = 1820000/259299 ∧
    eta728 = 5993/3125 ∧ chi728 = 649/1000 ∧ delta728 = 1/10^7 ∧
    normCap728 = 24149189/31250000 ∧ fieldCap728 = (-97745957/10^8) + (-156655368/10^8) ∧
    fieldCap728 = -10176053/4000000 ∧ residual728 = -5247033/10^8 ∧ nearCap728 = -(3/4) ∧
    strongFirstCost = 421/100 ∧ strongNormFirst = 67761/100000 ∧
    strongFieldsFirst = -247913/100000 ∧ strongLambda = 168493357/100000000 ∧
    physicalAtomGap = 401/2500 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [target728, secondCost728, gapWeightCost, rho728, kappa728, eta728, chi728, delta728,
      normCap728, fieldCap728, residual728, nearCap728, strongFirstCost, strongNormFirst,
      strongFieldsFirst, strongLambda, physicalAtomGap]

#print axioms objective_margin728
#print axioms first_budget728
#print axioms second_budget728
#print axioms eta_lt728
#print axioms payments728
#print axioms audit_constants
#print axioms measure_728_of_bounds
#print axioms measure_2183_of_bounds

end CatalanMeasure.G728
