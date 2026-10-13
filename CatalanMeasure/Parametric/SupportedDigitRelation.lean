module
public import CatalanMeasure.Parametric.PrimeDigitSampling
@[expose] public section
namespace CatalanMeasure.Parametric
open Polynomial OAI.InternalCatalan
noncomputable section

theorem digitCore_low_support {p : ℕ} (hp : 0<p) (Q Qlo : (ZMod p)[X])
    (hshift : Q=X^p*Qlo)
    (hs : ∀ i,Q.coeff i≠0 → 2*p ≤ i ∧ i<3*p) :
    ∀ i,Qlo.coeff i≠0 → p ≤ i ∧ i<2*p :=by
  intro i hi
  have he : Q.coeff (p+i)=Qlo.coeff i :=by
    rw [hshift,coeff_X_pow_mul',ite_eq_left (by omega),show p+i-p=i by omega]
  have hq :=hs (p+i) (by rwa [he])
  constructor <;> omega

theorem digitCore_coeff_shift {p ell : ℕ} (Q Qlo : (ZMod p)[X]) (hshift : Q=X^p*Qlo) :
    Q.coeff (2*p+ell)=Qlo.coeff (p+ell) :=by
  rw [hshift,coeff_X_pow_mul',ite_eq_left (by omega),show 2*p+ell-p=p+ell by omega]

theorem supportedDigitPair_zero {p H j : ℕ} [hp : Fact p.Prime]
    (F G Q : (ZMod p)[X]) (hF : X*oddPrimeWeight p*F=0) (hG : G=X^p*Q)
    (hs : ∀ i,Q.coeff i≠0 → 2*p ≤ i ∧ i<3*p) (hH : 4<H) :
    primeDigitPair H p j F G=Q.coeff (2*p+j%p)*sparseDigitZeroResidue p (j/p) :=by
  unfold primeDigitPair
  rw [hF,hG]
  have hz : primeDigitSample (H+1) p (j%p)
      (fun v =>palindromicRatResidue p (momentRatSigned ((v:ℤ)-1) (j/p))) 0=0 :=by
    simp [primeDigitSample]
  rw [hz,zero_sub]
  have hsample :=primeDigitSample_shift_single (a:=2) (t:=1) hp.out.pos (Nat.mod_lt j hp.out.pos)
    (show 2+1<H by omega) (fun v =>palindromicRatResidue p (zetaRat v (j/p))) Q hs
  simp only [one_mul] at hsample
  rw [hsample]
  unfold sparseDigitZeroResidue
  ring

theorem supportedDigitPair_one {p H j : ℕ} [hp : Fact p.Prime]
    (F G Q : (ZMod p)[X]) (hF : X*oddPrimeWeight p*F=(1-X^(2*p))*Q) (hG : G=Q)
    (hs : ∀ i,Q.coeff i≠0 → 2*p ≤ i ∧ i<3*p) (hH : 4<H) :
    primeDigitPair H p j F G=Q.coeff (2*p+j%p)*sparseDigitOneResidue p (j/p) :=by
  unfold primeDigitPair
  rw [hF,hG,show (1-X^(2*p))*Q=Q-X^(2*p)*Q by ring,primeDigitSample_sub,
    primeDigitSample_single (a:=2) hp.out.pos (Nat.mod_lt j hp.out.pos) (by omega) _ Q hs,
    primeDigitSample_shift_single (a:=2) (t:=2) hp.out.pos (Nat.mod_lt j hp.out.pos) (by omega) _ Q hs,
    primeDigitSample_single (a:=2) hp.out.pos (Nat.mod_lt j hp.out.pos) (by omega) _ Q hs]
  norm_num only
  unfold sparseDigitOneResidue
  ring

theorem supportedDigitPair_two {p H j : ℕ} [hp : Fact p.Prime] (hp2 : p≠2)
    (F G Q Qlo : (ZMod p)[X])
    (hF : X*oddPrimeWeight p*F=2*(1-X^(2*p))*Qlo) (hG : G=2*Qlo-X^p*Q)
    (hshift : Q=X^p*Qlo) (hs : ∀ i,Q.coeff i≠0 → 2*p ≤ i ∧ i<3*p) (hH : 4<H) :
    primeDigitPair H p j F G=Q.coeff (2*p+j%p)*sparseDigitTwoResidue p (j/p) :=by
  have hlo :=digitCore_low_support hp.out.pos Q Qlo hshift hs
  have hslow : ∀ i,Qlo.coeff i≠0 → 1*p ≤ i ∧ i<(1+1)*p :=by simpa only [one_mul] using hlo
  unfold primeDigitPair
  rw [hF,hG,show 2*(1-X^(2*p))*Qlo=2*(Qlo-X^(2*p)*Qlo) by ring,
    show 2*Qlo-X^p*Q=2*Qlo-X^(1*p)*Q by simp,
    primeDigitSample_two_mul,primeDigitSample_sub,primeDigitSample_sub,primeDigitSample_two_mul,
    primeDigitSample_single (a:=1) hp.out.pos (Nat.mod_lt j hp.out.pos) (by omega) _ Qlo hslow,
    primeDigitSample_shift_single (a:=1) (t:=2) hp.out.pos (Nat.mod_lt j hp.out.pos) (by omega) _ Qlo hslow,
    primeDigitSample_single (a:=1) hp.out.pos (Nat.mod_lt j hp.out.pos) (by omega) _ Qlo hslow,
    primeDigitSample_shift_single (a:=2) (t:=1) hp.out.pos (Nat.mod_lt j hp.out.pos) (by omega) _ Q hs]
  have hc : Q.coeff (2*p+j%p)=Qlo.coeff (1*p+j%p) :=by
    simpa only [one_mul] using digitCore_coeff_shift Q Qlo hshift (ell:=j%p)
  rw [← hc]
  norm_num only
  unfold sparseDigitTwoResidue
  have htwo : (2:ZMod p)≠0 :=by
    intro hz
    have hpgt : 2<p :=by have :=hp.out.two_le; omega
    exact (Nat.not_dvd_of_pos_of_lt (by decide : 0<2) hpgt)
      ((ZMod.natCast_eq_zero_iff 2 p).mp hz)
  field_simp
  ring

theorem supportedDigitPair_relation {p H j : ℕ} [hp : Fact p.Prime] (hlarge : 1000000 ≤ p)
    (F0 G0 F1 G1 F2 G2 Q Qlo : (ZMod p)[X])
    (hF0 : X*oddPrimeWeight p*F0=0) (hG0 : G0=X^p*Q)
    (hF1 : X*oddPrimeWeight p*F1=(1-X^(2*p))*Q) (hG1 : G1=Q)
    (hF2 : X*oddPrimeWeight p*F2=2*(1-X^(2*p))*Qlo) (hG2 : G2=2*Qlo-X^p*Q)
    (hshift : Q=X^p*Qlo) (hs : ∀ i,Q.coeff i≠0 → 2*p ≤ i ∧ i<3*p)
    (hH : 4<H) (hpos : Q.coeff (2*p+j%p)≠0 → j/p=1 ∨ j/p=2) :
    primeDigitPair H p j F2 G2=(292/59:ZMod p)*primeDigitPair H p j F1 G1-
      (3281/177:ZMod p)*primeDigitPair H p j F0 G0 :=by
  rw [supportedDigitPair_two (by omega : p≠2) F2 G2 Q Qlo hF2 hG2 hshift hs hH,
    supportedDigitPair_one F1 G1 Q hF1 hG1 hs hH,supportedDigitPair_zero F0 G0 Q hF0 hG0 hs hH]
  by_cases hc : Q.coeff (2*p+j%p)=0
  · simp [hc]
  have hrel : sparseDigitTwoResidue p (j/p)=
      (292/59:ZMod p)*sparseDigitOneResidue p (j/p)-(3281/177:ZMod p)*sparseDigitZeroResidue p (j/p) :=by
    rcases hpos hc with h1 | h2
    · simpa [h1] using sparseDigit_identity_residue hlarge (0:Fin 2)
    · simpa [h2] using sparseDigit_identity_residue hlarge (1:Fin 2)
  rw [hrel]
  ring

end
end CatalanMeasure.Parametric
