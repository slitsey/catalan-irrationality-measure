module
public import CatalanArchive.CatalanMeasure.Parametric.SecondaryTentSourceNaturalResponse
public import CatalanArchive.CatalanMeasure.Parametric.SecondaryTentSourceRawSectors

/-! The ordinary reduced macro polynomials evaluate to the literal actual
finite source sums used by the signed row-sector identity. -/
@[expose] public section
namespace CatalanMeasure.Parametric
open Polynomial OAI.InternalCatalan
open scoped BigOperators
noncomputable section

theorem secondaryTent_source_moment_macro_eval (p J : ℕ) [Fact p.Prime] :
    (secondaryTentSourceMomentForward p J).eval₂
      (algebraMap (ZMod p) (RatFunc (ZMod p))) (palindromicRatT p)⁻¹ =
      secondaryTentSourceMacroM p J := by
  simp only [secondaryTentSourceMomentForward, secondaryTentSourceMacroM,
    eval₂_finsetSum, eval₂_mul, eval₂_C, eval₂_X_pow]

theorem secondaryTent_source_zeta_macro_eval (p J : ℕ) [Fact p.Prime] :
    (secondaryTentSourceZetaForward p J).eval₂
      (algebraMap (ZMod p) (RatFunc (ZMod p))) (palindromicRatT p)⁻¹ =
      (3/2:RatFunc (ZMod p))*secondaryTentSourceMacroZ p J := by
  simp only [secondaryTentSourceZetaForward, secondaryTentSourceMacroZ,
    eval₂_finsetSum, eval₂_mul, eval₂_C, eval₂_X_pow,
    map_div₀, _root_.map_ofNat]

theorem secondaryTent_source_natural_symbol_eval {p J : ℕ} [Fact p.Prime]
    (HU HV : (ZMod p)[X]) (x : RatFunc (ZMod p)) :
    (secondaryTentSourceNaturalSymbol p J HU HV).eval₂
      (algebraMap (ZMod p) (RatFunc (ZMod p))) x =
      ((x*(secondaryTentSourceZetaForward p J).eval₂
          (algebraMap (ZMod p) (RatFunc (ZMod p))) x -
        (x-1)*(secondaryTentSourceMomentForward p J).eval₂
          (algebraMap (ZMod p) (RatFunc (ZMod p))) x)^p *
        HU.eval₂ (algebraMap (ZMod p) (RatFunc (ZMod p))) x +
       (x*(secondaryTentSourceZetaForward p J).eval₂
          (algebraMap (ZMod p) (RatFunc (ZMod p))) x -
        (x+1)*(secondaryTentSourceMomentForward p J).eval₂
          (algebraMap (ZMod p) (RatFunc (ZMod p))) x)^p *
        HV.eval₂ (algebraMap (ZMod p) (RatFunc (ZMod p))) x)/16 := by
  simp only [secondaryTentSourceNaturalSymbol, eval₂_mul, eval₂_add,
    eval₂_sub, eval₂_pow, eval₂_C, eval₂_X, eval₂_one,
    map_div₀, map_one, _root_.map_ofNat]
  ring

end
end CatalanMeasure.Parametric
