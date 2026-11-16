module

public import CatalanCore.Zeta5.Energy.Instance

/-!
# Z5-ENERGY (top module)

Theorem side of the decay inequality chain for Fauzan's Proposition 6.3 with the hard-edge
comparison measure `ν = f ω_{[0,b]}`:

* ZD01/ZD02 : `energy_log_nonpos` (`ZeroMass`), `gaussian_conv`, `tendsto_Ltr` (`Gauss`, `Kernel`);
* ZD03 : `integral_log_circ` (`Circle`);
* ZD05 : `integral_regTerm_le` (`LayerCake`);
* ZD06/ZD07 : `energy_raw` (`Config`), `config_ineq` (`Field`);
* ZD08/ZD09 : `pointwise_bound`, `Vfield`, `integral_log_add_sq` (`Field`);
* ZD24/ZD25/ZD27 : `w_le_8192`, `integral_le_sum_log`, `sum_log_le_integral`,
  `integral_one_add_pow_mul_exp` (`Weights`);
* ZD29 : `log_S_le` (`Stirling`);
* ZD26/ZD28/ZD30/ZD31 : `integrand_le`, `log_Δ_le'`, `real_bound` (`Bound`);
* the instance `real_bound_nu` at `nu c N b` (`Instance`), with the cell hypothesis `CellHyp`.
-/
