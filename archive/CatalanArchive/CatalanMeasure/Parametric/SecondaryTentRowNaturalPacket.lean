module
public import CatalanArchive.CatalanMeasure.Parametric.SecondaryTentRowSourceJunction
public import CatalanArchive.CatalanMeasure.Parametric.SecondaryTentRowReflection
@[expose] public section

namespace CatalanMeasure.Parametric
open Polynomial
open scoped BigOperators
noncomputable section

theorem secondaryTent_row_interleave_cubic_degree {K : Type*} [Field K]
    {p : ℕ} (hp : 0<p) (A : Fin p → K[X]) (hA : ∀ e, (A e).natDegree ≤ 3) :
    (secondaryTentInterleave p A).natDegree ≤ 4*p-1 := by
  unfold secondaryTentInterleave
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro e he
  have ht := natDegree_mul_le (p := Polynomial.expand K p (A e)) (q := X^e.val)
  rw [natDegree_expand, natDegree_X_pow] at ht
  have ha := Nat.mul_le_mul_right p (hA e)
  have he := e.isLt
  omega

def secondaryTentRowFixedNaturalPacket {K : Type*} [Field K]
    (p : ℕ) (c : Fin p → (Fin 5 → K)) : K[X] :=
  secondaryTentRowNaturalNumerator p (4*p-1)
    (secondaryTentInterleave p (fun e => (secondaryTentRowFixedSeedPair (c e)).1))
    (secondaryTentInterleave p (fun e => (secondaryTentRowFixedSeedPair (c e)).2))

/-- The actual five fixed differential seeds, inverse coefficient
reconstruction, and combined ordinary natural numerator form an injective
packet map. Every part is a concrete polynomial construction. -/
theorem secondaryTent_row_fixed_natural_packet_injective {K : Type*} [Field K]
    (h2 : (2:K) ≠ 0) (hunit : (3445975817256960:K) ≠ 0)
    {p : ℕ} (hp : 0<p) (hodd : Odd p) :
    Function.Injective (secondaryTentRowFixedNaturalPacket (K := K) p) := by
  intro c d h
  let U (a : Fin p → (Fin 5 → K)) :=
    secondaryTentInterleave p (fun e => (secondaryTentRowFixedSeedPair (a e)).1)
  let V (a : Fin p → (Fin 5 → K)) :=
    secondaryTentInterleave p (fun e => (secondaryTentRowFixedSeedPair (a e)).2)
  have hU (a : Fin p → (Fin 5 → K)) : (U a).natDegree ≤ 4*p-1 := by
    apply secondaryTent_row_interleave_cubic_degree hp
    intro e
    exact secondaryTent_row_natural_P_degree _
  have hV (a : Fin p → (Fin 5 → K)) : (V a).natDegree ≤ 4*p-1 := by
    apply secondaryTent_row_interleave_cubic_degree hp
    intro e
    exact secondaryTent_row_natural_Q_degree _
  have hzero : secondaryTentRowNaturalNumerator p (4*p-1) (U c-U d) (V c-V d)=0 := by
    change secondaryTentRowNaturalNumerator p (4*p-1) (U c) (V c) =
      secondaryTentRowNaturalNumerator p (4*p-1) (U d) (V d) at h
    unfold secondaryTentRowNaturalNumerator at h ⊢
    rw [show secondaryTentRowInput (4*p-1) (U c-U d) =
        secondaryTentRowInput (4*p-1) (U c)-secondaryTentRowInput (4*p-1) (U d)
          from (secondaryTentRowInputLinear (K := K) (4*p-1)).map_sub (U c) (U d),
      show secondaryTentRowInput (4*p-1) (V c-V d) =
        secondaryTentRowInput (4*p-1) (V c)-secondaryTentRowInput (4*p-1) (V d)
          from (secondaryTentRowInputLinear (K := K) (4*p-1)).map_sub (V c) (V d)]
    linear_combination h
  have hz := (secondaryTent_row_natural_numerator_zero_iff h2 p (4*p-1) hodd
    (U c-U d) (V c-V d)
    ((natDegree_sub_le _ _).trans (max_le (hU c) (hU d)))
    ((natDegree_sub_le _ _).trans (max_le (hV c) (hV d)))).mp hzero
  apply secondaryTent_row_fixed_reconstruction_injective h2 hunit hp
  exact Prod.ext (sub_eq_zero.mp hz.1) (sub_eq_zero.mp hz.2)

end
end CatalanMeasure.Parametric
