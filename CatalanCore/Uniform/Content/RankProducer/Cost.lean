module

public import CatalanCore.Uniform.Content.Hybrid.Costs

@[expose] public section

/-!
# Rank of a pair condition against a lower bound on `V ∩ U` (lane H15)

`finrank range (condMap c) + finrank (V ⊓ U_c) ≤ finrank V`: the restricted rank of a condition is
`dim V - dim (V ∩ U_c)`.
-/

open Module CatalanCore.Uniform.Content.Hybrid

namespace CatalanCore.Uniform.Content.RankProducer

variable {K : Type*} [Field K] [DecidableEq K] {R S : Type*} [Fintype R] [Fintype S]
  [DecidableEq R] [DecidableEq S]
  (α : R → K) (x : R → K × K) (β : S → K) (y : S → K × K) (Vs : Submodule K (K × K))

theorem finrank_range_condMap_add_le (c : Cond α β) :
    finrank K (LinearMap.range (condMap α x β y Vs c)) +
      finrank K (↥(Vs ⊓ condSpace α x β y c)) ≤ finrank K Vs := by
  have hk := (condMap α x β y Vs c).finrank_range_add_finrank_ker
  let f : ↥(Vs ⊓ condSpace α x β y c) →ₗ[K] LinearMap.ker (condMap α x β y Vs c) :=
    { toFun := fun v => ⟨⟨v.1, v.2.1⟩, by
        simp only [LinearMap.mem_ker, condMap, LinearMap.coe_comp, Function.comp_apply,
          Submodule.coe_subtype, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact v.2.2⟩
      map_add' := fun u v => rfl
      map_smul' := fun r v => rfl }
  have hf : Function.Injective f := by
    intro u v h
    apply Subtype.ext
    have := congrArg (fun w : LinearMap.ker (condMap α x β y Vs c) => ((w : Vs) : K × K)) h
    exact this
  have := LinearMap.finrank_le_finrank_of_injective hf
  omega

theorem finrank_range_condMap_le_of_lb (c : Cond α β) {m : ℕ}
    (hm : m ≤ finrank K (↥(Vs ⊓ condSpace α x β y c))) :
    finrank K (LinearMap.range (condMap α x β y Vs c)) ≤ finrank K Vs - m := by
  have := finrank_range_condMap_add_le α x β y Vs c
  omega

end CatalanCore.Uniform.Content.RankProducer
