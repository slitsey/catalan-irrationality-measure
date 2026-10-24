module
public import CatalanArchive.CatalanMeasure.Parametric.SecondaryTentFixedSeeds
public import CatalanArchive.CatalanMeasure.Parametric.SecondaryTentRowPolynomial
@[expose] public section

namespace CatalanMeasure.Parametric
open Polynomial Matrix
noncomputable section

/-- Literal natural U numerator `2x U` of the seven differential channels,
including the boundary `dz/z²` channel in coordinate 6. -/
def secondaryTentRowNaturalP {K : Type*} [CommRing K] (c : Fin 7 → K) : K[X] :=
  C (c 4) * X^0 + C (2*c 0-2*c 2+c 3+c 5) * X^1 +
    C (2*c 1+2*c 6) * X^2 + C (4*c 2) * X^3

/-- Literal natural V numerator `2x(x-1)V` in the same seven channels. -/
def secondaryTentRowNaturalQ {K : Type*} [CommRing K] (c : Fin 7 → K) : K[X] :=
  C (-c 5) * X^0 + C (-2*c 1+c 3+c 5+2*c 6) * X^1 +
    C (2*c 1-4*c 2-2*c 6) * X^2 + C (4*c 2) * X^3

def secondaryTentRowNaturalPair {K : Type*} [CommRing K] (c : Fin 7 → K) :
    K[X] × K[X] := (secondaryTentRowNaturalP c, secondaryTentRowNaturalQ c)

/-- The literal ordinary numerator of the seven-channel function t=eta/(dz/z),
with common denominator `z(z-1)(z²+1)`. This includes `boundary/z`. -/
def secondaryTentRowTNumerator {K : Type*} [CommRing K] (c : Fin 7 → K) : K[X] :=
  X * (X^2+1) * (X-1) * (C (c 0) + C (c 1)*X + C (c 2)*X^2) +
    C (c 3)*X^2*(X^2+1) + C (c 4)*X^2*(X-1) +
    C (c 5)*X^3*(X-1) + C (c 6)*(X^2+1)*(X-1)

/-- Exact polynomial source junction between the natural `(P,Q)` pair and
the actual seven-channel rational t seed, after clearing its denominator.
This fixed-degree identity is valid over every commutative ring. -/
theorem secondaryTent_row_natural_t_junction {K : Type*} [CommRing K]
    (c : Fin 7 → K) :
    (X-1) * secondaryTentRowInput 3 (secondaryTentRowNaturalP c) +
      (X+1) * secondaryTentRowInput 3 (secondaryTentRowNaturalQ c) =
      8 * X * secondaryTentRowTNumerator c := by
  unfold secondaryTentRowInput secondaryTentRowHom
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, add_zero]
  simp only [secondaryTentRowNaturalP, secondaryTentRowNaturalQ, coeff_add,
    coeff_C_mul_X_pow]
  norm_num
  simp only [secondaryTentRowTNumerator, map_add, map_sub, map_mul, map_ofNat]
  ring

def secondaryTentRowNaturalPairLinear {K : Type*} [CommRing K] :
    (Fin 7 → K) →ₗ[K] (K[X] × K[X]) where
  toFun := secondaryTentRowNaturalPair
  map_add' c d := by
    apply Prod.ext <;>
      simp [secondaryTentRowNaturalPair, secondaryTentRowNaturalP,
        secondaryTentRowNaturalQ, sub_eq_add_neg, add_mul] <;> ring
  map_smul' a c := by
    apply Prod.ext <;>
      simp [secondaryTentRowNaturalPair, secondaryTentRowNaturalP,
        secondaryTentRowNaturalQ, sub_eq_add_neg, ← C_mul', mul_add, mul_neg,
        mul_assoc] <;> ring

/-- An explicit coefficient inverse proves all seven differential channels
remain independent after passing to natural polynomial numerator pairs.
In particular, the boundary channel has not disappeared in reconstruction. -/
theorem secondaryTent_row_natural_pair_injective {K : Type*} [Field K]
    (h2 : (2:K) ≠ 0) : Function.Injective (secondaryTentRowNaturalPair (K := K)) := by
  intro c d h
  have hp₀ := congrArg (fun P : K[X] × K[X] => P.1.coeff 0) h
  have hp₁ := congrArg (fun P : K[X] × K[X] => P.1.coeff 1) h
  have hp₂ := congrArg (fun P : K[X] × K[X] => P.1.coeff 2) h
  have hp₃ := congrArg (fun P : K[X] × K[X] => P.1.coeff 3) h
  have hq₀ := congrArg (fun P : K[X] × K[X] => P.2.coeff 0) h
  have hq₁ := congrArg (fun P : K[X] × K[X] => P.2.coeff 1) h
  have hq₂ := congrArg (fun P : K[X] × K[X] => P.2.coeff 2) h
  simp only [secondaryTentRowNaturalPair, secondaryTentRowNaturalP,
    secondaryTentRowNaturalQ, coeff_add, coeff_C_mul_X_pow] at hp₀ hp₁ hp₂ hp₃ hq₀ hq₁ hq₂
  norm_num at hp₀ hp₁ hp₂ hp₃ hq₀ hq₁ hq₂
  have h4 : (4:K) ≠ 0 := by
    convert mul_ne_zero h2 h2 using 1 <;> norm_num
  have hc₂ : c 2=d 2 := hp₃.resolve_right h4
  have hc₁ : c 1=d 1 := by
    apply mul_left_cancel₀ h4
    linear_combination hp₂+hq₂+4*hc₂
  have hc₆ : c 6=d 6 := by
    apply mul_left_cancel₀ h4
    linear_combination hp₂-hq₂-4*hc₂
  have hc₅ : c 5=d 5 := by first | exact hq₀ | exact neg_injective hq₀
  have hc₃ : c 3=d 3 := by linear_combination hq₁+2*hc₁-hc₅-2*hc₆
  have hc₀ : c 0=d 0 := by
    apply mul_left_cancel₀ h2
    linear_combination hp₁+2*hc₂-hc₃-hc₅
  funext i
  fin_cases i <;> assumption

/-- The actual five fixed seed columns followed by their actual natural
polynomial pairs. The common integer normalization is that of FixedSeeds. -/
def secondaryTentRowFixedSeedPair {K : Type*} [Field K] :
    (Fin 5 → K) →ₗ[K] (K[X] × K[X]) :=
  secondaryTentRowNaturalPairLinear.comp
    (secondaryTentSeedCoefficients.map (Int.castRingHom K)).mulVecLin

theorem secondaryTent_row_fixed_seed_pair_injective {K : Type*} [Field K]
    (h2 : (2:K) ≠ 0) (hunit : (3445975817256960:K) ≠ 0) :
    Function.Injective (secondaryTentRowFixedSeedPair (K := K)) := by
  exact (secondaryTent_row_natural_pair_injective h2).comp
    (secondaryTent_seed_coefficients_injective hunit)

/-- Concrete fixed-seed reconstruction has injective natural numerator
pairs, using elementary coefficient extraction rather than a Cartier
normality or raw-rank assumption. -/
theorem secondaryTent_row_fixed_reconstruction_injective {K : Type*} [Field K]
    (h2 : (2:K) ≠ 0) (hunit : (3445975817256960:K) ≠ 0)
    {p : ℕ} (hp : 0<p) :
    Function.Injective (fun c : Fin p → (Fin 5 → K) =>
      (secondaryTentInterleave p (fun e => (secondaryTentRowFixedSeedPair (c e)).1),
       secondaryTentInterleave p (fun e => (secondaryTentRowFixedSeedPair (c e)).2))) := by
  exact secondaryTent_seed_reconstruction_injective (K := K) (V := Fin 5 → K) hp
    (secondaryTentRowFixedSeedPair (K := K))
    (secondaryTent_row_fixed_seed_pair_injective h2 hunit)

end
end CatalanMeasure.Parametric
