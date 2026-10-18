module

public import CatalanCore.Frame.Spec

/-!
# Template for a parity file (copy to `CatalanParity/<Name>.lean`; deleted at cut-over, design 4)

A parity file imports BOTH the legacy development and the new instance and proves, with `rfl`,
`exact` or `norm_num`, that
* the new final theorems have the same statements as the legacy ones (negative control D: the
  new Solution must compile against the UNCHANGED Challenge file);
* `measureExp c Λ D g₁ g₂ s` reproduces the legacy exponent (negative control A, for lambda
  `measureExp (68726/10000) (313/105) (31111/10000) (3/4) 1 1 = 31682445459/409965000`);
* `#print axioms` shows only `propext`, `Classical.choice`, `Quot.sound`.
-/

@[expose] public section

namespace CatalanParity.Template

open CatalanCore

/-- Negative control A for lambda, as a statement (proved by `norm_num [measureExp]`). -/
def controlA : Prop :=
  measureExp (68726 / 10000) (313 / 105) (31111 / 10000) (3 / 4) 1 1 = 31682445459 / 409965000

theorem controlA_holds : controlA := by
  unfold controlA measureExp
  norm_num

end CatalanParity.Template
