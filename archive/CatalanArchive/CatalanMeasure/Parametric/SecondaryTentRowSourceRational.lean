module
public import CatalanArchive.CatalanMeasure.Parametric.SecondaryTentRowActualCoefficients
public import CatalanArchive.CatalanMeasure.Parametric.SecondaryTentSourceTrace
public import CatalanArchive.CatalanMeasure.Parametric.SecondaryTentSourceRawSectors
public import Mathlib.Algebra.CharP.Lemmas
@[expose] public section

namespace CatalanMeasure.Parametric
open Polynomial OAI.InternalCatalan
noncomputable section

def secondaryTentRowRationalX {L : Type*} [Field L] (z : L) : L := (z^2+1)/(2*z)
def secondaryTentRowRationalS {L : Type*} [Field L] (z : L) : L := (z^2-1)/(2*z)
def secondaryTentRowRationalB {L : Type*} [Field L] (z : L) : L := z^4*(z-1)/(z^2+1)^4

theorem secondaryTent_row_rational_curve {L : Type*} [Field L]
    (z : L) (h2 : (2:L)≠0) (hz : z≠0) :
    (secondaryTentRowRationalS z)^2=(secondaryTentRowRationalX z)^2-1 := by
  unfold secondaryTentRowRationalS secondaryTentRowRationalX
  field_simp [h2,hz]
  <;> ring

theorem secondaryTent_row_rational_mirror_x {L : Type*} [Field L]
    (z : L) (h2 : (2:L)≠0) (hz : z≠0) :
    secondaryTentRowRationalX z⁻¹=secondaryTentRowRationalX z := by
  unfold secondaryTentRowRationalX
  field_simp [h2,hz]
  <;> ring

theorem secondaryTent_row_rational_mirror_s {L : Type*} [Field L]
    (z : L) (h2 : (2:L)≠0) (hz : z≠0) :
    secondaryTentRowRationalS z⁻¹= -secondaryTentRowRationalS z := by
  unfold secondaryTentRowRationalS
  field_simp [h2,hz]
  <;> ring

theorem secondaryTent_row_rational_b_trace_form {L : Type*} [Field L]
    (z : L) (h2 : (2:L)≠0) (hz : z≠0) (hq : z^2+1≠0) :
    secondaryTentRowRationalB z =
      (secondaryTentRowRationalX z-1+secondaryTentRowRationalS z)/
        (16*(secondaryTentRowRationalX z)^4) := by
  have h16 : (16:L)≠0 := by convert pow_ne_zero 4 h2 using 1 <;> norm_num
  unfold secondaryTentRowRationalB secondaryTentRowRationalX secondaryTentRowRationalS
  field_simp [h2,h16,hz,hq]
  <;> ring

theorem secondaryTent_row_rational_b_over_xs {L : Type*} [Field L]
    (z : L) (h2 : (2:L)≠0) (hz : z≠0) (hq : z^2+1≠0)
    (hm : z-1≠0) (hp : z+1≠0) :
    secondaryTentRowRationalB z/(2*secondaryTentRowRationalX z*secondaryTentRowRationalS z) =
      2*z^6/((z^2+1)^5*(z+1)) := by
  have hD : z^2-1≠0 := by
    rw [show z^2-1=(z-1)*(z+1) by ring]
    exact mul_ne_zero hm hp
  unfold secondaryTentRowRationalB secondaryTentRowRationalX secondaryTentRowRationalS
  field_simp [h2,hz,hq,hD,hp]
  <;> ring

theorem secondaryTent_row_rational_b_over_x_minus {L : Type*} [Field L]
    (z : L) (h2 : (2:L)≠0) (hz : z≠0) (hq : z^2+1≠0) (hm : z-1≠0) :
    secondaryTentRowRationalB z/(2*secondaryTentRowRationalX z*(secondaryTentRowRationalX z-1)) =
      2*z^6/((z^2+1)^5*(z-1)) := by
  have hx : secondaryTentRowRationalX z-1=(z-1)^2/(2*z) := by
    unfold secondaryTentRowRationalX
    field_simp [h2,hz]
    <;> ring
  rw [hx]
  unfold secondaryTentRowRationalB secondaryTentRowRationalX
  field_simp [h2,hz,hq,hm]
  <;> ring

/-- The divisor relation already cancels every N-dependent factor of the
weighted row. Only the universal natural reconstruction denominator remains. -/
theorem secondaryTent_row_divisor_rational_ratio {L : Type*} [Field L]
    (N p a g : ℕ) (z K R : L) (hp : 0<p) (hpN : 2*p≤24*N)
    (hag : a+g=p) (hgp : g+4*p=27*N) (hq : z^2+1≠0)
    (hm : z-1≠0) (hplus : z+1≠0)
    (hK : K=z^(24*N-2*p)*(z^2+1)^a*(z-1)^(p+2*N-1)*(z+1)^(p-1)*R) :
    z^(24*N)*(z-1)^(2*N)*R/(z^2+1)^(27*N) =
      z^(2*p)*K/((z^2+1)^(5*p)*(z-1)^(p-1)*(z+1)^(p-1)) := by
  have hqpow : (z^2+1)^(5*p)=(z^2+1)^a*(z^2+1)^(27*N) := by
    rw [← pow_add]
    congr 1
    omega
  have hzpow : z^(24*N)=z^(2*p)*z^(24*N-2*p) := by
    rw [← pow_add,Nat.add_sub_of_le hpN]
  have hmpow : (z-1)^(p+2*N-1)=(z-1)^(2*N)*(z-1)^(p-1) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hK,hqpow,hzpow,hmpow]
  field_simp [hq,hm,hplus]
  <;> ring

/-- The universal ordinary K numerator is precisely the natural inverse
packet row, including its exact power-of-eight normalization. -/
theorem secondaryTent_row_natural_rational_ratio {L : Type*} [Field L]
    (p : ℕ) (z U V : L) (hp : 0<p) (h2 : (2:L)≠0) (hz : z≠0)
    (hq : z^2+1≠0) (hm : z-1≠0) (hplus : z+1≠0) :
    z^(2*p)*((z-1)^p*(2*z)^(4*p-1)*U+(z+1)^p*(2*z)^(4*p-1)*V)/
        ((z^2+1)^(5*p)*(z-1)^(p-1)*(z+1)^(p-1)) =
      (8:L)^p*secondaryTentRowRationalS z*
        ((secondaryTentRowRationalB z/(2*secondaryTentRowRationalX z*secondaryTentRowRationalS z))^p*U +
         (secondaryTentRowRationalB z/(2*secondaryTentRowRationalX z*(secondaryTentRowRationalX z-1)))^p*V) := by
  rw [secondaryTent_row_rational_b_over_xs z h2 hz hq hm hplus,
    secondaryTent_row_rational_b_over_x_minus z h2 hz hq hm]
  unfold secondaryTentRowRationalS
  have hmPow : (z-1)^p=(z-1)^(p-1)*(z-1) := by
    rw [← pow_succ, Nat.sub_add_cancel hp]
  have hpPow : (z+1)^p=(z+1)^(p-1)*(z+1) := by
    rw [← pow_succ, Nat.sub_add_cancel hp]
  have hFour : 4*p-1+1=4*p := by omega
  have hPow : (2:L)^(4*p)=(8:L)^p*2^p := by
    rw [show (8:L)=2^3 by norm_num,← pow_mul,← pow_add]
    congr 1
    omega
  have hzPow : z^(2*p)*z^(4*p)=z^(6*p) := by
    rw [← pow_add]
    congr 1
    omega
  have hcore : (8:L)^p*(2*z^6)^p=(z^(2*p)*(2*z)^(4*p-1))*(2*z) := by
    calc
      _ = ((8:L)^p*2^p)*z^(6*p) := by rw [mul_pow,← pow_mul]; ring
      _ = (2:L)^(4*p)*(z^(2*p)*z^(4*p)) := by rw [hPow,hzPow]
      _ = z^(2*p)*(2*z)^(4*p) := by rw [mul_pow]; ring
      _ = _ := by rw [mul_assoc,← pow_succ,hFour]
  have hc : (8:L)^p*(2*z^6)^p/(2*z)=z^(2*p)*(2*z)^(4*p-1) := by
    rw [hcore,mul_div_cancel_right₀ _ (mul_ne_zero h2 hz)]
  have hu : (2*z^6/((z^2+1)^5*(z+1)))^p = (2*z^6)^p/((z^2+1)^(5*p)*(z+1)^p) := by
    simp only [div_pow,mul_pow,← pow_mul]
  have hv : (2*z^6/((z^2+1)^5*(z-1)))^p = (2*z^6)^p/((z^2+1)^(5*p)*(z-1)^p) := by
    simp only [div_pow,mul_pow,← pow_mul]
  rw [hu,hv]
  have hfrac : ((z-1)^p*U+(z+1)^p*V)/
      ((z^2+1)^(5*p)*(z-1)^(p-1)*(z+1)^(p-1)) =
      (z^2-1)*(U/((z^2+1)^(5*p)*(z+1)^p)+V/((z^2+1)^(5*p)*(z-1)^p)) := by
    simp only [hmPow,hpPow]
    field_simp [hq,hm,hplus]
    <;> ring
  calc
    _ = (z^(2*p)*(2*z)^(4*p-1))*(((z-1)^p*U+(z+1)^p*V)/
        ((z^2+1)^(5*p)*(z-1)^(p-1)*(z+1)^(p-1))) := by ring
    _ = (z^(2*p)*(2*z)^(4*p-1))*(z^2-1)*
        (U/((z^2+1)^(5*p)*(z+1)^p)+V/((z^2+1)^(5*p)*(z-1)^p)) := by rw [hfrac]; ring
    _ = ((8:L)^p*(2*z^6)^p/(2*z))*(z^2-1)*
        (U/((z^2+1)^(5*p)*(z+1)^p)+V/((z^2+1)^(5*p)*(z-1)^p)) := by rw [hc]
    _ = _ := by ring

/-- The actual polynomial quotient row has the exact natural inverse
packet expression needed by the signed raw source. All denominators are
cleared from the proved polynomial divisor relation before evaluating. -/
theorem secondaryTent_row_quotient_natural_source {K L : Type*} [Field K] [Field L]
    (f : K →+* L) (N p a g : ℕ) (U V : K[X]) (hp : 0<p) (hpN : 2*p≤24*N)
    (hag : a+g=p) (hgp : g+4*p=27*N)
    (hU : U.natDegree≤4*p-1) (hV : V.natDegree≤4*p-1)
    (hd : secondaryTentRowTotalDivisor N p a ∣ secondaryTentRowNaturalNumerator p (4*p-1) U V)
    (z : L) (h2 : (2:L)≠0) (hz : z≠0) (hq : z^2+1≠0)
    (hm : z-1≠0) (hplus : z+1≠0) :
    z^(24*N)*(z-1)^(2*N)*
        (secondaryTentRowQuotientLinear N p a (secondaryTentRowNaturalNumerator p (4*p-1) U V)).eval₂ f z /
      (z^2+1)^(27*N) =
      (8:L)^p*secondaryTentRowRationalS z*
        ((secondaryTentRowRationalB z/(2*secondaryTentRowRationalX z*secondaryTentRowRationalS z))^p*
            U.eval₂ f (secondaryTentRowRationalX z) +
         (secondaryTentRowRationalB z/(2*secondaryTentRowRationalX z*(secondaryTentRowRationalX z-1)))^p*
            V.eval₂ f (secondaryTentRowRationalX z)) := by
  let F := secondaryTentRowNaturalNumerator p (4*p-1) U V
  let R := secondaryTentRowQuotientLinear N p a F
  have hmo : (secondaryTentRowTotalDivisor (K := K) N p a).Monic := secondaryTent_row_divisor_monic _ _ _ _
  have hrec : F=secondaryTentRowTotalDivisor N p a*R := by
    have h := modByMonic_add_div F (secondaryTentRowTotalDivisor N p a)
    rw [(modByMonic_eq_zero_iff_dvd hmo).mpr hd,zero_add] at h
    exact h.symm
  have hu := secondaryTent_rowHom_eval₂ f (4*p-1) U (X^2+1) (2*X) z hU
    (by simpa using mul_ne_zero h2 hz)
  have hv := secondaryTent_rowHom_eval₂ f (4*p-1) V (X^2+1) (2*X) z hV
    (by simpa using mul_ne_zero h2 hz)
  simp only [eval₂_add,eval₂_mul,eval₂_pow,eval₂_X,eval₂_one,eval₂_ofNat] at hu hv
  change (secondaryTentRowInput (4*p-1) U).eval₂ f z =
    U.eval₂ f (secondaryTentRowRationalX z)*(2*z)^(4*p-1) at hu
  change (secondaryTentRowInput (4*p-1) V).eval₂ f z =
    V.eval₂ f (secondaryTentRowRationalX z)*(2*z)^(4*p-1) at hv
  have he := congrArg (Polynomial.eval₂ f z) hrec
  change (secondaryTentRowNaturalNumerator p (4*p-1) U V).eval₂ f z =
    (secondaryTentRowTotalDivisor N p a*R).eval₂ f z at he
  simp only [secondaryTentRowNaturalNumerator,secondaryTentRowTotalDivisor,secondaryTentRowDivisor,
    eval₂_mul,eval₂_add,eval₂_sub,eval₂_pow,eval₂_X,eval₂_one] at he
  rw [hu,hv] at he
  have hk : (z-1)^p*(2*z)^(4*p-1)*U.eval₂ f (secondaryTentRowRationalX z)+
      (z+1)^p*(2*z)^(4*p-1)*V.eval₂ f (secondaryTentRowRationalX z) =
      z^(24*N-2*p)*(z^2+1)^a*(z-1)^(p+2*N-1)*(z+1)^(p-1)*R.eval₂ f z := by
    linear_combination he
  change z^(24*N)*(z-1)^(2*N)*R.eval₂ f z/(z^2+1)^(27*N) = _
  rw [secondaryTent_row_divisor_rational_ratio N p a g z _ (R.eval₂ f z) hp hpN hag hgp hq hm hplus hk]
  exact secondaryTent_row_natural_rational_ratio p z
    (U.eval₂ f (secondaryTentRowRationalX z)) (V.eval₂ f (secondaryTentRowRationalX z))
    hp h2 hz hq hm hplus

theorem secondaryTent_row_prime_power_eight {L : Type*} [Field L] {p : ℕ}
    [Fact p.Prime] [CharP L p] : (8:L)^p=8 := by
  change (frobenius L p) (8:L)=8
  exact _root_.map_ofNat (frobenius L p) 8

def secondaryTentRowRatX (p : ℕ) [Fact p.Prime] : RatFunc (ZMod p) := (palindromicRatT p)⁻¹
def secondaryTentRowRatS (p : ℕ) [Fact p.Prime] : RatFunc (ZMod p) :=
  -palindromicRatF p*secondaryTentRowRatX p
def secondaryTentRowRatB (p : ℕ) [Fact p.Prime] : RatFunc (ZMod p) :=
  (secondaryTentRowRatX p-1+secondaryTentRowRatS p)/(16*(secondaryTentRowRatX p)^4)
def secondaryTentRowRatH (p N : ℕ) [Fact p.Prime] : RatFunc (ZMod p) :=
  secondaryTentSourceRowBase twenty p N/2^(26*N)
def secondaryTentRowRatU (N p a : ℕ) [Fact p.Prime] (F : (ZMod p)[X]) : RatFunc (ZMod p) :=
  (secondaryTentRowQuotientLinear N p a F).eval₂ (algebraMap (ZMod p) (RatFunc (ZMod p)))
    (palindromicRatW p)/(palindromicRatW p)^(2*N)

theorem secondaryTent_row_rat_x_coordinate {p : ℕ} [Fact p.Prime] :
    secondaryTentRowRatX p=secondaryTentRowRationalX (palindromicRatW p) := by
  unfold secondaryTentRowRatX secondaryTentRowRationalX palindromicRatT
  rw [inv_div]
  congr 1
  ring

theorem secondaryTent_row_rat_s_coordinate {p : ℕ} [Fact p.Prime] (hp2 : p≠2) :
    secondaryTentRowRatS p=secondaryTentRowRationalS (palindromicRatW p) := by
  rw [secondaryTentRowRatS,secondaryTent_row_rat_x_coordinate]
  unfold secondaryTentRowRationalX secondaryTentRowRationalS palindromicRatF
  field_simp [palindromicRat_two_ne_zero hp2,palindromicRatW_ne_zero (p := p),
    palindromicRat_denominator_ne_zero (p := p)]
  <;> ring

theorem secondaryTent_row_rat_b_coordinate {p : ℕ} [Fact p.Prime] (hp2 : p≠2) :
    secondaryTentRowRatB p=secondaryTentRowRationalB (palindromicRatW p) := by
  unfold secondaryTentRowRatB
  rw [secondaryTent_row_rat_x_coordinate,secondaryTent_row_rat_s_coordinate hp2]
  exact (secondaryTent_row_rational_b_trace_form _ (palindromicRat_two_ne_zero hp2)
    palindromicRatW_ne_zero (by simpa [add_comm] using palindromicRat_denominator_ne_zero (p := p))).symm

theorem secondaryTent_row_rat_h_coordinate {p : ℕ} [Fact p.Prime] (hp2 : p≠2) (N : ℕ) :
    secondaryTentRowRatH p N=(palindromicRatW p)^(26*N)*(palindromicRatW p-1)^(2*N)/
      (1+palindromicRatW p^2)^(27*N) := by
  rw [secondaryTentRowRatH,secondaryTent_source_twenty_base]
  field_simp [palindromicRat_two_ne_zero hp2]

@[simp] theorem secondaryTent_row_rat_star_x {p : ℕ} [Fact p.Prime] :
    palindromicRatStar p (secondaryTentRowRatX p)=secondaryTentRowRatX p := by
  simp only [secondaryTentRowRatX,map_inv₀,palindromicRatStar_T]

@[simp] theorem secondaryTent_row_rat_star_s {p : ℕ} [Fact p.Prime] :
    palindromicRatStar p (secondaryTentRowRatS p)= -secondaryTentRowRatS p := by
  simp [secondaryTentRowRatS,map_neg,map_mul]

@[simp] theorem secondaryTent_row_rat_star_h {p : ℕ} [Fact p.Prime] (N : ℕ) :
    palindromicRatStar p (secondaryTentRowRatH p N)=secondaryTentRowRatH p N := by
  simp only [secondaryTentRowRatH,secondaryTentSourceRowBase,map_div₀,map_mul,map_pow,map_sub,
    map_one,palindromicRatStar_T,map_ofNat]

theorem secondaryTent_row_rat_star_b {p : ℕ} [Fact p.Prime] :
    palindromicRatStar p (secondaryTentRowRatB p)=
      (secondaryTentRowRatX p-1-secondaryTentRowRatS p)/(16*(secondaryTentRowRatX p)^4) := by
  simp only [secondaryTentRowRatB,map_div₀,map_add,map_sub,map_neg,map_one,map_pow,map_mul,map_ofNat,
    secondaryTent_row_rat_star_x,secondaryTent_row_rat_star_s,sub_eq_add_neg]

@[simp] theorem secondaryTent_row_rat_star_eval_x {p : ℕ} [Fact p.Prime] (U : (ZMod p)[X]) :
    palindromicRatStar p (U.eval₂ (algebraMap (ZMod p) (RatFunc (ZMod p))) (secondaryTentRowRatX p)) =
      U.eval₂ (algebraMap (ZMod p) (RatFunc (ZMod p))) (secondaryTentRowRatX p) := by
  simp only [eval₂_eq_sum,sum_def,map_sum,map_mul,map_pow,palindromicRatStar_scalar,
    secondaryTent_row_rat_star_x]

/-- The quotient row's actual rational function specializes to the
natural source packet with the correct common factor8. -/
theorem secondaryTent_row_ratfunc_natural_source {p : ℕ} [Fact p.Prime]
    (hp2 : p≠2) (N a g : ℕ) (U V : (ZMod p)[X]) (hpN : 2*p≤24*N)
    (hag : a+g=p) (hgp : g+4*p=27*N)
    (hU : U.natDegree≤4*p-1) (hV : V.natDegree≤4*p-1)
    (hd : secondaryTentRowTotalDivisor N p a ∣ secondaryTentRowNaturalNumerator p (4*p-1) U V) :
    secondaryTentRowRatU N p a (secondaryTentRowNaturalNumerator p (4*p-1) U V)*secondaryTentRowRatH p N =
      8*secondaryTentRowRatS p*
        ((secondaryTentRowRatB p/(2*secondaryTentRowRatX p*secondaryTentRowRatS p))^p*
          U.eval₂ (algebraMap (ZMod p) (RatFunc (ZMod p))) (secondaryTentRowRatX p) +
         (secondaryTentRowRatB p/(2*secondaryTentRowRatX p*(secondaryTentRowRatX p-1)))^p*
          V.eval₂ (algebraMap (ZMod p) (RatFunc (ZMod p))) (secondaryTentRowRatX p)) := by
  have hq : palindromicRatW p^2+1≠0 := by simpa [add_comm] using palindromicRat_denominator_ne_zero (p := p)
  have hm : palindromicRatW p-1≠0 := by
    have h := RatFunc.algebraMap_ne_zero (by simpa using (X_sub_C_ne_zero (1:ZMod p)))
    simpa [palindromicRatW] using h
  have hplus : palindromicRatW p+1≠0 := by
    have h := RatFunc.algebraMap_ne_zero (X_sub_C_ne_zero (-1:ZMod p))
    simpa [palindromicRatW] using h
  have h := secondaryTent_row_quotient_natural_source (algebraMap (ZMod p) (RatFunc (ZMod p)))
    N p a g U V (Fact.out : p.Prime).pos hpN hag hgp hU hV hd (palindromicRatW p)
    (palindromicRat_two_ne_zero hp2) palindromicRatW_ne_zero hq hm hplus
  rw [secondaryTent_row_prime_power_eight,← secondaryTent_row_rat_x_coordinate,
    ← secondaryTent_row_rat_s_coordinate hp2,← secondaryTent_row_rat_b_coordinate hp2] at h
  have hzP : (palindromicRatW p)^(26*N)=(palindromicRatW p)^(24*N)*(palindromicRatW p)^(2*N) := by
    rw [← pow_add]
    congr 1
    omega
  rw [← h,secondaryTent_row_rat_h_coordinate hp2]
  unfold secondaryTentRowRatU
  rw [hzP]
  field_simp [palindromicRatW_ne_zero (p := p),hq,show 1+palindromicRatW p^2≠0 by simpa [add_comm] using hq]
  <;> ring

/-- The mirror quotient row follows by the existing involution, with all
natural inputs fixed and the signed coordinate negated. -/
theorem secondaryTent_row_ratfunc_mirror_source {p : ℕ} [Fact p.Prime]
    (hp2 : p≠2) (N a g : ℕ) (U V : (ZMod p)[X]) (hpN : 2*p≤24*N)
    (hag : a+g=p) (hgp : g+4*p=27*N)
    (hU : U.natDegree≤4*p-1) (hV : V.natDegree≤4*p-1)
    (hd : secondaryTentRowTotalDivisor N p a ∣ secondaryTentRowNaturalNumerator p (4*p-1) U V) :
    palindromicRatStar p (secondaryTentRowRatU N p a (secondaryTentRowNaturalNumerator p (4*p-1) U V))*
        secondaryTentRowRatH p N =
      8*(-secondaryTentRowRatS p)*
        ((palindromicRatStar p (secondaryTentRowRatB p)/(2*secondaryTentRowRatX p*(-secondaryTentRowRatS p)))^p*
          U.eval₂ (algebraMap (ZMod p) (RatFunc (ZMod p))) (secondaryTentRowRatX p) +
         (palindromicRatStar p (secondaryTentRowRatB p)/(2*secondaryTentRowRatX p*(secondaryTentRowRatX p-1)))^p*
          V.eval₂ (algebraMap (ZMod p) (RatFunc (ZMod p))) (secondaryTentRowRatX p)) := by
  have h := congrArg (palindromicRatStar p)
    (secondaryTent_row_ratfunc_natural_source hp2 N a g U V hpN hag hgp hU hV hd)
  simpa only [map_mul,map_add,map_div₀,map_pow,map_sub,map_one,map_ofNat,
    secondaryTent_row_rat_star_x,secondaryTent_row_rat_star_s,secondaryTent_row_rat_star_h,
    secondaryTent_row_rat_star_eval_x] using h

end
end CatalanMeasure.Parametric
