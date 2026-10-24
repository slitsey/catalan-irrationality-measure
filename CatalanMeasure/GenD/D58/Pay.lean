module

public import CatalanMeasure.GenD.D58.Budget
public import CatalanMeasure.GenD.PayW

@[expose] public section

/-!
# D58: the payments for the window criterion with `w = 3/4`

`pay_w` replaces `Budget.pay_own` (which needed the window `(p, 2.1 p]`): the recycling window is
`(p, 2p]` again and the lower window end is `(κ - 3/4) L`.  The total decay rate is `η + χ`.
-/

namespace CatalanMeasure.GenD
namespace D58
open Real
noncomputable section

theorem K160.pay_w : PayW (3 / 4) d0 K160.rho (K160.eta + chi) K160.kappa delta K160.B := by
  unfold PayW K160.kappa
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [K160.B, d0, K160.rho, K160.eta, chi, delta, t, K160.etaRef, chiRef, deltaRef,
      K160.secondCost, wcap]

theorem K640.pay_w : PayW (3 / 4) d0 K640.rho (K640.eta + chi) K640.kappa delta K640.B := by
  unfold PayW K640.kappa
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [K640.B, d0, K640.rho, K640.eta, chi, delta, t, K640.etaRef, chiRef, deltaRef,
      K640.secondCost, wcap]

end
end D58
end CatalanMeasure.GenD
