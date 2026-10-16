module
public import CatalanMeasure.Parametric.SecondaryTentParametersResponseSupport
public import CatalanMeasure.Parametric.SecondaryTentParametersExtraResponse
public import CatalanMeasure.Parametric.SecondaryTentSourceCompatibility
@[expose] public section
namespace CatalanMeasure.Parametric
open Polynomial OAI.InternalCatalan
open scoped BigOperators
noncomputable section

theorem secondaryTent_parameter_actual_bulk_response {p N g boundary a b j : ℕ} [Fact p.Prime]
    (hp2 : p≠2) (hN : 0<N) (hg : 0<g) (hwindow : 52*N<9*p)
    (hB : ¬p ∣ 6310886697782126553600) (hj : j<24*N) (hJ : j/p<4)
    (hpN : 2*p≤24*N) (ha : a+g=p) (hb : b+3*N=p)
    (hgp : g+4*p=27*N) (hboundary : boundary≤p)
    (v : SecondaryTentParameters (ZMod p) N g boundary)
    (hd : secondaryTentRowTotalDivisor N p a ∣ secondaryTentParameterPacketLinear p N g boundary a b v)
    (hdegree : (secondaryTentParameterPacketLinear p N g boundary a b v).natDegree+8*N+3≤10*p) :
    (∑ r : Fin (20*N), palindromicRatResidue p ((p:ℚ)^2*rawEntryRat twenty 0 N r.val j)*
      secondaryTentParameterActualRowLinear p N g boundary a b v r) =
      (-8*2^(26*N-1):ZMod p)*∑ i : Fin 5,
        (secondaryTentSourceFixedResponseInteger ⟨j/p,hJ⟩ i:ZMod p)*
          (secondaryTentParameterInputs p N g boundary a b v i).coeff (p-1-j%p) := by
  let I := secondaryTentParameterInputs p N g boundary a b v
  let U := secondaryTentParameterNaturalULinear p N g boundary a b v
  let V := secondaryTentParameterNaturalVLinear p N g boundary a b v
  have hI := secondaryTent_parameter_inputs_degree hN hg ha hb hboundary v
  have hdeg := secondaryTent_parameter_natural_degree hN hg ha hb hboundary v
  have hpacket := secondaryTent_parameter_natural_packet_expansion hN hg ha hb hboundary v
  have hd' : secondaryTentRowTotalDivisor N p a ∣ secondaryTentRowNaturalNumerator p (4*p-1) U V := by
    rw [← hpacket]
    exact hd
  have hR := secondaryTent_row_quotient_degree N p a g
    (secondaryTentParameterPacketLinear p N g boundary a b v) hN
    (Fact.out : p.Prime).pos hpN ha hgp hdegree
  rw [hpacket] at hR
  have hr := secondaryTent_source_quotient_actual_response hp2 hN hwindow hj hpN ha hgp
    U V hdeg.1 hdeg.2 hd' hR 0 (by norm_num)
  have hseed (i : Fin 5) : secondaryTentRowActualSeedColumn (K := ZMod p) i =
      (fun k => (secondaryTentSeedCoefficients k i:ZMod p)) := by
    funext k
    simp [secondaryTentRowActualSeedColumn, Matrix.mulVec_single_one]
  have hcoeff : (secondaryTentSourceNaturalSymbol p (j/p) U V).coeff (6*p-1-j%p) =
      ∑ i : Fin 5, (secondaryTentSourceFixedResponseInteger ⟨j/p,hJ⟩ i:ZMod p)*
        (I i).coeff (p-1-j%p) := by
    change (secondaryTentSourceNaturalSymbol p (j/p)
      (∑ i : Fin 5, (secondaryTentRowNaturalP (secondaryTentRowActualSeedColumn i))^p*I i)
      (∑ i : Fin 5, (secondaryTentRowNaturalQ (secondaryTentRowActualSeedColumn i))^p*I i)).coeff
        (6*p-1-j%p) = _
    simp_rw [hseed]
    exact secondaryTent_source_fixed_natural_response hB ⟨j/p,hJ⟩ I hI
      (Nat.mod_lt j (Fact.out : p.Prime).pos)
  rw [hcoeff] at hr
  calc
    _ = ∑ r : Fin (20*N), (secondaryTentRowQuotientLinear N p a
        (secondaryTentRowNaturalNumerator p (4*p-1) U V)).coeff r.val *
          palindromicRatResidue p ((p:ℚ)^2*rawEntryRat twenty 0 N r.val j) := by
      apply Finset.sum_congr rfl
      intro r hr
      change _ * (secondaryTentRowQuotientLinear N p a
        (secondaryTentParameterPacketLinear p N g boundary a b v)).coeff r.val = _
      rw [hpacket]
      exact mul_comm _ _
    _ = _ := hr

theorem secondaryTent_positive_actual_raw_response {p N half δ g a b : ℕ} [Fact p.Prime]
    (hp2 : p≠2) (h2 : (2:ZMod p)≠0) (hN : 0<N) (hδ : 0<δ) (hg : 0<g)
    (hwindow : 52*N<9*p) (hB : ¬p ∣ 6310886697782126553600)
    (hp : p=6*N+δ) (hodd : p=2*half+1) (hgp : g+4*p=27*N)
    (ha : a+g=p) (hb : b+3*N=p) (hhi : p≤8*N) (hpN : 2*p≤24*N)
    (v : LinearMap.ker (secondaryTentConstraintMap (secondaryTentPositiveCosts N p half)
      (secondaryTentPositiveParameterConstraints p N half δ g a b)))
    (j : ℕ) (hjlo : 3*N≤j) (hjhi : j<24*N) :
    (∑ r : Fin (20*N), palindromicRatResidue p ((p:ℚ)^2*rawEntryRat twenty 0 N r.val j)*
      secondaryTentPositiveActualRowLinear p N half δ g a b v r) =
      (secondaryTentParameterResponsePolynomialLinear p N g (4*δ) v.val).eval (j:ZMod p) := by
  have hJ : j/p<4 := (Nat.div_lt_iff_lt_mul (Fact.out : p.Prime).pos).mpr (by omega)
  have hgeo := secondaryTent_positive_parameter_geometry h2 hN hδ hg hp hodd hgp ha hb hhi hpN v
  have hr := secondaryTent_parameter_actual_bulk_response hp2 hN hg hwindow hB hjhi hJ
    hpN ha hb hgp (by omega) v.val hgeo.1 hgeo.2
  have hidx : (j/p)*p+j%p=j := Nat.div_add_mod' j p
  have hs := secondaryTent_parameter_positive_macro_response (a := a) (by omega : N≤p) hδ hp hb
    (Nat.mod_lt j (Fact.out : p.Prime).pos) (⟨j/p,hJ⟩ : Fin 4)
    (by simpa only [hidx] using hjlo) (by simpa only [hidx] using hjhi) v.val
  rw [hs] at hr
  have hc : ((j%p:ℕ):ZMod p)=(j:ZMod p) := by simp
  rw [hc] at hr
  change _ = (C (secondaryTentParameterResponseScalar p N)*
    secondaryTentResponsePolynomial p N v.val.1).eval (j:ZMod p)
  rw [eval_mul, eval_C]
  simpa only [secondaryTentPositiveActualRowLinear, LinearMap.comp_apply,
    Submodule.subtype_apply, secondaryTentParameterResponseScalar, mul_assoc] using hr

theorem secondaryTent_negative_actual_raw_response {p N half g d a b : ℕ} [Fact p.Prime]
    (hp2 : p≠2) (h2 : (2:ZMod p)≠0) (hN : 0<N) (hg : 0<g)
    (hwindow : 52*N<9*p) (hB : ¬p ∣ 6310886697782126553600)
    (hp : p+d=6*N) (hodd : p=2*half+1) (hgp : g+4*p=27*N)
    (ha : a+g=p) (hb : b+3*N=p) (hlo : 8*N+2≤2*p) (hhi : p≤8*N)
    (v : LinearMap.ker (secondaryTentConstraintMap (secondaryTentNegativeCosts N p half g d)
      (secondaryTentNegativeParameterConstraints p N half g d a b)))
    (j : ℕ) (hjlo : 3*N≤j) (hjhi : j<24*N) :
    (∑ r : Fin (20*N), palindromicRatResidue p ((p:ℚ)^2*rawEntryRat twenty 0 N r.val j)*
      secondaryTentNegativeActualRowLinear p N half g d a b v r) =
      (secondaryTentParameterResponsePolynomialLinear p N g 0 v.val).eval (j:ZMod p) := by
  have hidx : (j/p)*p+j%p=j := Nat.div_add_mod' j p
  have hJ5 : j/p<5 := (Nat.div_lt_iff_lt_mul (Fact.out : p.Prime).pos).mpr (by omega)
  by_cases hJ : j/p<4
  · have hgeo := secondaryTent_negative_parameter_geometry h2 hN hg hp hodd hgp ha hb hlo hhi v
    have hr := secondaryTent_parameter_actual_bulk_response hp2 hN hg hwindow hB hjhi hJ
      (by omega) ha hb hgp (by omega) v.val hgeo.1 hgeo.2
    have hs := secondaryTent_parameter_negative_macro_response (a := a) (by omega : N≤p) hb
      (Nat.mod_lt j (Fact.out : p.Prime).pos) (⟨j/p,hJ⟩ : Fin 4)
      (by simpa only [hidx] using hjlo) v.val
    rw [hs] at hr
    have hc : ((j%p:ℕ):ZMod p)=(j:ZMod p) := by simp
    rw [hc] at hr
    change _ = (C (secondaryTentParameterResponseScalar p N)*
      secondaryTentResponsePolynomial p N v.val.1).eval (j:ZMod p)
    rw [eval_mul, eval_C]
    simpa only [secondaryTentNegativeActualRowLinear, LinearMap.comp_apply,
      Submodule.subtype_apply, secondaryTentParameterResponseScalar, mul_assoc] using hr
  · have hJ4 : j/p=4 := by omega
    rw [hJ4] at hidx
    have he : j%p<4*d := by omega
    have hr := secondaryTent_negative_extra_raw_response (p := p) (N := N) (half := half)
      (g := g) (d := d) (a := a) (b := b) he v
    simpa only [hidx] using hr

end
end CatalanMeasure.Parametric
