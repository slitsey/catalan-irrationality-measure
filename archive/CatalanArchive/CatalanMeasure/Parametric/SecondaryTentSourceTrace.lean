module
public import CatalanArchive.CatalanMeasure.Parametric.SecondaryTentSourceSymbol
public import CatalanArchive.CatalanMeasure.Parametric.SecondaryTentRowSeedPair

/-! Elementary mirror trace and its ordinary numerator. -/
@[expose] public section
namespace CatalanMeasure.Parametric
open Polynomial OAI.InternalCatalan
open scoped BigOperators
noncomputable section

def secondaryTentSourceTraceTerm {K : Type*} [Field K]
    (x s A B U V : K) : K :=
  ((x-1+s)/(16*x^4))*(B-s*A/x)*(U+s*V)/s

theorem secondaryTent_source_mirror_trace {K : Type*} [Field K]
    (x s A B U V : K) (h2 : (2:K)≠0) (hx : x≠0) (hs : s≠0) :
    secondaryTentSourceTraceTerm x s A B U V +
        secondaryTentSourceTraceTerm x (-s) A B U V =
      ((B-(x-1)*A/x)*U+((x-1)*B-s^2*A/x)*V)/(8*x^4) := by
  have h8 : (8:K)≠0 := by convert pow_ne_zero 3 h2 using 1 <;> norm_num
  have h16 : (16:K)≠0 := by convert pow_ne_zero 4 h2 using 1 <;> norm_num
  unfold secondaryTentSourceTraceTerm
  field_simp [h8, h16, hx, hs]
  <;> ring

def secondaryTentSourceTraceNumerator {K : Type*} [Field K]
    (A B P Q : K[X]) : K[X] :=
  C (1/16) * ((X*B-(X-1)*A)*P+(X*B-(X+1)*A)*Q)

/-- In the natural P,Q coordinates the full mirror trace has the single
ordinary denominator x^6. The apparent x-1 denominator cancels exactly. -/
theorem secondaryTent_source_natural_trace {K : Type*} [Field K]
    (x s A B P Q : K) (h2 : (2:K)≠0) (hx : x≠0) (hs : s≠0)
    (hw : x-1≠0) (hcurve : s^2=x^2-1) :
    x^6 *
      (secondaryTentSourceTraceTerm x s A B (P/(2*x)) (Q/(2*x*(x-1))) +
       secondaryTentSourceTraceTerm x (-s) A B (P/(2*x)) (Q/(2*x*(x-1)))) =
      ((x*B-(x-1)*A)*P+(x*B-(x+1)*A)*Q)/16 := by
  rw [secondaryTent_source_mirror_trace x s A B _ _ h2 hx hs, hcurve]
  have h8 : (8:K)≠0 := by convert pow_ne_zero 3 h2 using 1 <;> norm_num
  have h16 : (16:K)≠0 := by convert pow_ne_zero 4 h2 using 1 <;> norm_num
  field_simp [h2, h8, h16, hx, hw]
  <;> ring

def secondaryTentSourceMomentForwardRat (J : ℕ) : ℚ[X] :=
  ∑ v∈Finset.range 6, C (momentRatSigned ((v:ℤ)-1) J)*X^v

def secondaryTentSourceZetaForwardRat (J : ℕ) : ℚ[X] :=
  C (3/2) * ∑ v∈Finset.range 5, C (zetaRat v J)*X^v

/-- Ordinary polynomial symbol of an actual source macro and the seven
literal differential channels. -/
def secondaryTentSourceMacroTraceRat (J : ℕ) (c : Fin 7 → ℚ) : ℚ[X] :=
  secondaryTentSourceTraceNumerator (secondaryTentSourceMomentForwardRat J)
    (secondaryTentSourceZetaForwardRat J)
    (secondaryTentRowNaturalP c) (secondaryTentRowNaturalQ c)

def secondaryTentSourceMacroTable : Matrix (Fin 5) (Fin 7) ℚ :=
  !![61/288, 1/72, 145/144, -1/96, 25/4608, 551/4608, 5/288;
     -41/192, 157/192, -139/192, -11/64, 191/1152, -133/1152, 71/192;
     23/48, -35/96, -133/96, 5/16, -59/768, 89/256, -17/48;
     -251/576, -221/576, 263/576, -25/192, 299/1152, -257/1152, -43/576;
     -55/192, 1/16, 1/288, -23/192, -935/4608, -1025/4608, 73/192]

set_option maxRecDepth 5000
set_option maxHeartbeats 1500000
/-- All 35 fixed macro entries are computed from actual source moments.
The statement is linear in arbitrary seven-channel coefficients. -/
theorem secondaryTent_source_macro_trace_coefficient (J : Fin 5) (c : Fin 7 → ℚ) :
    (secondaryTentSourceMacroTraceRat J.val c).coeff 5 =
      ∑ i : Fin 7, secondaryTentSourceMacroTable J i*c i := by
  fin_cases J <;>
    norm_num [secondaryTentSourceMacroTraceRat, secondaryTentSourceTraceNumerator,
      secondaryTentSourceMomentForwardRat, secondaryTentSourceZetaForwardRat,
      secondaryTentRowNaturalP, secondaryTentRowNaturalQ,
      secondaryTentSourceMacroTable, momentRatSigned, momentRatNegOne, momentRat,
      boundaryPlus, boundaryMinus, momentScalar, centralCoeff, zetaRat, harmonicRat,
      mul_add, add_mul, mul_sub, sub_mul, ← mul_assoc,
      coeff_add, coeff_sub, coeff_C_mul, coeff_mul_C, coeff_mul_X_pow',
      coeff_X_mul, coeff_C_mul_X_pow,
      Finset.sum_range_succ, Fin.sum_univ_succ] <;> ring

/-- The four actual bulk macro responses of the five fixed integer-scaled
seeds. D=747824613120 is the common seed normalization from FixedSeeds. -/
def secondaryTentSourceFixedResponses : Matrix (Fin 4) (Fin 5) ℚ :=
  !![747824613120, 0, 0, 747824613120, 0;
     747824613120, 0, 0, 0, 0;
     747824613120, 0, 0, 0, 0;
     747824613120, 0, 0, 0, 747824613120*(-22627/732472)]

theorem secondaryTent_source_fixed_macro_response (J : Fin 4) (i : Fin 5) :
    (secondaryTentSourceMacroTraceRat J.val
      (fun k => (secondaryTentSeedCoefficients k i : ℚ))).coeff 5 =
      secondaryTentSourceFixedResponses J i := by
  rw [secondaryTent_source_macro_trace_coefficient ⟨J.val, by omega⟩]
  fin_cases J <;> fin_cases i <;>
    norm_num [secondaryTentSourceMacroTable, secondaryTentSeedCoefficients,
      secondaryTentSourceFixedResponses, Fin.sum_univ_succ]

end
end CatalanMeasure.Parametric
