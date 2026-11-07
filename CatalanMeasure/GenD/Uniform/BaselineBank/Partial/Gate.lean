module

public import CatalanMeasure.GenD.Uniform.BaselineBank.Partial.Instance
public import CatalanMeasure.GenD.DesignInstance.PositiveBudget
public import CatalanMeasure.GenD.PayW

@[expose] public section
set_option Elab.async false

/-!
# The B = 540 gate, symbolic in the ledger gain (lane G5c)

`Decay.Budget540` fixes `gain = 21.68168`.  Here the gain is a parameter `g`:

* `gDg g = 24733/4 + (2673/8) log 2 - g` is the exponent produced by `Ledger.ledger_growth`
  (and by `partial_growth` for `g = partialGain`);
* `gate_ineq`  : `g >= 21.6083` implies `eta = 29.596 < tDelta - gDg g`;
* `gate_pay`   : the payment hypotheses `PayW` hold at `eta = 29.596` (independent of `g`);
* `gate`       : both, as an existential over `eta`;
* `gate_of_remaining` : with the partial ledger, any further families of total area
  `>= 1.5565` complete the gate.

The final instance only plugs in the total area of all windows (partial + MT, M, A-envelope,
Theorem Z); nothing else changes.  The hard floor is `g > 21.608143` (pay threshold
`eta > 29.595908`).
-/

namespace CatalanMeasure.GenD.Uniform.Bank540.Ledger
open CatalanMeasure.GenD D58
noncomputable section

/-- The exponent of the denominator growth for a ledger of total gain `g`. -/
def gDg (g : ℝ) : ℝ := 24733 / 4 + (2673 / 8) * Real.log 2 - g

/-- The chosen decay rate. -/
def etaG : ℝ := 29596 / 1000

end
end CatalanMeasure.GenD.Uniform.Bank540.Ledger
