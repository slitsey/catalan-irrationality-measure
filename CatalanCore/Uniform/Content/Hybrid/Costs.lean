module

public import CatalanCore.Uniform.Content.Hybrid.LoadKernel
public import Mathlib.LinearAlgebra.Dimension.Constructions

@[expose] public section

/-!
# Elementary cost bounds for the pair conditions

The rank-two branches of `A_pair = max(0, 2c - W, max_t(c - W + w_t))` use three cost bounds on
`rank(B_c|V)` for the quotient condition maps of `LoadKernel`:

* `condMap_rank_le` : at most `dim V` (any condition, any `V`);
* `condMap_rank_eq_zero` : `0` when `V` lies in the condition space (a kernel line of the type);
* `condMap_rank_le_quot` : at most `2 - dim U_c` (the full space `V = K²`).
-/

open Module

namespace CatalanCore.Uniform.Content.Hybrid

variable {K : Type*} [Field K] [DecidableEq K] {R S : Type*} [Fintype R] [Fintype S]
  [DecidableEq R] [DecidableEq S]
  (α : R → K) (x : R → K × K) (β : S → K) (y : S → K × K) (Vs : Submodule K (K × K))

theorem condMap_rank_le (c : Cond α β) :
    finrank K (LinearMap.range (condMap α x β y Vs c)) ≤ finrank K Vs :=
  LinearMap.finrank_range_le _

theorem condMap_rank_eq_zero (c : Cond α β) (h : Vs ≤ condSpace α x β y c) :
    finrank K (LinearMap.range (condMap α x β y Vs c)) = 0 := by
  have : LinearMap.range (condMap α x β y Vs c) = ⊥ := by
    rw [LinearMap.range_eq_bot]
    ext v
    simp only [condMap, LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype,
      Submodule.mkQ_apply, LinearMap.zero_apply, Submodule.Quotient.mk_eq_zero]
    exact h v.2
  rw [this, finrank_bot]

theorem condMap_rank_le_quot (c : Cond α β) :
    finrank K (LinearMap.range (condMap α x β y Vs c)) + finrank K (condSpace α x β y c) ≤ 2 := by
  have h1 := Submodule.finrank_le (LinearMap.range (condMap α x β y Vs c))
  have h2 := Submodule.finrank_quotient_add_finrank (condSpace α x β y c)
  have h3 : finrank K (K × K) = 2 := by simp
  omega

end CatalanCore.Uniform.Content.Hybrid
