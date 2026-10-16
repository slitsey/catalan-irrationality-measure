# Exact 878 / 2632 witness records

The authoritative proof certificates are literal rational data in
`CatalanMeasure/FirstStrongTrial`, `StrongTrial` and `GapCircle`, checked by
ordinary Lean. These JSON records preserve the supplied inputs and exact
research contract; their numerical results are not imported as axioms.

- `first40.json`: SHA256 `2dfc1d5cb3177b20a7b4449a116a4c3e8c849fc34ae7c27ae0cfb41a95830587`.
- `second160.json`: SHA256 `00a9ab03f74d768cfe082421ddc7365e5f1f196a206098735634c1d876686aef`.
- `exact878-contract.json`: the exact physical-gap, marked-budget and circle ledger.

The first physical sequence is `p=2P`, with norm price `4||P||^2+||V||^2/2`;
the second uses `2||P||^2+||V||^2/2`. The common target is `22563367/10000000`.
Physical/interpolation gaps are `401/2500` and `2005000/6410801`. The second
residual cap is `-131/2500`, and the near cap is `-3/4`. Population costs are
`421/100` and `13421/3125`; the actual circle weight is `17913/1000`.
Thus `rho=519037/5000`, `eta=425979/200000`, and the degree coefficient is18.

`Parametric/GapMain.lean` assembles the unconditional endpoints. Its internal
and public axiom audits use only `propext`, `Classical.choice`, `Quot.sound`.
The original 955/2864 proof checkpoints remain available. This publication
does not assert independent-kernel or comparator acceptance.
