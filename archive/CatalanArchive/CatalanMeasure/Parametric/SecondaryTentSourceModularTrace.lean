module
public import CatalanArchive.CatalanMeasure.Parametric.SecondaryTentSourceTrace

/-! Fixed trace responses of the actual reduced source arrays. -/
@[expose] public section
namespace CatalanMeasure.Parametric
open Polynomial OAI.InternalCatalan
open scoped BigOperators
noncomputable section

def secondaryTentSourceMomentForward (p J : ℕ) [Fact p.Prime] : (ZMod p)[X] :=
  ∑ v∈Finset.range 6, C (palindromicRatResidue p
    (momentRatSigned ((v:ℤ)-1) J))*X^v

def secondaryTentSourceZetaForward (p J : ℕ) [Fact p.Prime] : (ZMod p)[X] :=
  C (3/2) * ∑ v∈Finset.range 5,
    C (palindromicRatResidue p (zetaRat v J))*X^v

def secondaryTentSourceMacroTrace (p J : ℕ) [Fact p.Prime]
    (c : Fin 7 → ZMod p) : (ZMod p)[X] :=
  secondaryTentSourceTraceNumerator (secondaryTentSourceMomentForward p J)
    (secondaryTentSourceZetaForward p J)
    (secondaryTentRowNaturalP c) (secondaryTentRowNaturalQ c)

def secondaryTentSourceMacroIntegerTable : Matrix (Fin 5) (Fin 7) ℤ :=
  !![976, 64, 4640, -48, 25, 551, 80;
     -984, 3768, -3336, -792, 764, -532, 1704;
     2208, -1680, -6384, 1440, -354, 1602, -1632;
     -2008, -1768, 2104, -600, 1196, -1028, -344;
     -1320, 288, 16, -552, -935, -1025, 1752]

theorem secondaryTent_source_fixed_denominator_unit {p : ℕ} [Fact p.Prime]
    (hp : ¬p ∣ 6310886697782126553600) (d : ℕ)
    (hd : d ∣ 6310886697782126553600) : (d:ZMod p)≠0 := by
  intro hz
  exact hp (((ZMod.natCast_eq_zero_iff d p).mp hz).trans hd)

set_option maxRecDepth 5000
set_option maxHeartbeats 1500000
/-- Direct characteristic-p verification of the actual 35 macro entries.
This statement uses actual moment residues, so no rational-cast theorem
is left as an implicit source obligation. -/
theorem secondaryTent_source_macro_trace_modular {p : ℕ} [Fact p.Prime]
    (hp : ¬p ∣ 6310886697782126553600) (J : Fin 5) (c : Fin 7 → ZMod p) :
    (4608:ZMod p)*(secondaryTentSourceMacroTrace p J.val c).coeff 5 =
      ∑ i : Fin 7, (secondaryTentSourceMacroIntegerTable J i:ZMod p)*c i := by
  have hnat := secondaryTent_source_fixed_denominator_unit hp
  have h2 : (2:ZMod p)≠0 := by
    simpa only [Nat.cast_ofNat] using hnat 2 (by norm_num)
  have h3 : (3:ZMod p)≠0 := by
    simpa only [Nat.cast_ofNat] using hnat 3 (by norm_num)
  have h4 : (4:ZMod p)≠0 := by
    simpa only [Nat.cast_ofNat] using hnat 4 (by norm_num)
  have h6 : (6:ZMod p)≠0 := by
    simpa only [Nat.cast_ofNat] using hnat 6 (by norm_num)
  have h8 : (8:ZMod p)≠0 := by
    simpa only [Nat.cast_ofNat] using hnat 8 (by norm_num)
  have h9 : (9:ZMod p)≠0 := by
    simpa only [Nat.cast_ofNat] using hnat 9 (by norm_num)
  have h12 : (12:ZMod p)≠0 := by
    simpa only [Nat.cast_ofNat] using hnat 12 (by norm_num)
  have h16 : (16:ZMod p)≠0 := by
    simpa only [Nat.cast_ofNat] using hnat 16 (by norm_num)
  have h18 : (18:ZMod p)≠0 := by
    simpa only [Nat.cast_ofNat] using hnat 18 (by norm_num)
  have h24 : (24:ZMod p)≠0 := by
    simpa only [Nat.cast_ofNat] using hnat 24 (by norm_num)
  have h32 : (32:ZMod p)≠0 := by
    simpa only [Nat.cast_ofNat] using hnat 32 (by norm_num)
  have h36 : (36:ZMod p)≠0 := by
    simpa only [Nat.cast_ofNat] using hnat 36 (by norm_num)
  have h48 : (48:ZMod p)≠0 := by
    simpa only [Nat.cast_ofNat] using hnat 48 (by norm_num)
  have h64 : (64:ZMod p)≠0 := by
    simpa only [Nat.cast_ofNat] using hnat 64 (by norm_num)
  have h72 : (72:ZMod p)≠0 := by
    simpa only [Nat.cast_ofNat] using hnat 72 (by norm_num)
  have h96 : (96:ZMod p)≠0 := by
    simpa only [Nat.cast_ofNat] using hnat 96 (by norm_num)
  have h128 : (128:ZMod p)≠0 := by
    simpa only [Nat.cast_ofNat] using hnat 128 (by norm_num)
  have h144 : (144:ZMod p)≠0 := by
    simpa only [Nat.cast_ofNat] using hnat 144 (by norm_num)
  have h192 : (192:ZMod p)≠0 := by
    simpa only [Nat.cast_ofNat] using hnat 192 (by norm_num)
  have h256 : (256:ZMod p)≠0 := by
    simpa only [Nat.cast_ofNat] using hnat 256 (by norm_num)
  have h288 : (288:ZMod p)≠0 := by
    simpa only [Nat.cast_ofNat] using hnat 288 (by norm_num)
  have h384 : (384:ZMod p)≠0 := by
    simpa only [Nat.cast_ofNat] using hnat 384 (by norm_num)
  have h512 : (512:ZMod p)≠0 := by
    simpa only [Nat.cast_ofNat] using hnat 512 (by norm_num)
  have h576 : (576:ZMod p)≠0 := by
    simpa only [Nat.cast_ofNat] using hnat 576 (by norm_num)
  have h768 : (768:ZMod p)≠0 := by
    simpa only [Nat.cast_ofNat] using hnat 768 (by norm_num)
  have h1152 : (1152:ZMod p)≠0 := by
    simpa only [Nat.cast_ofNat] using hnat 1152 (by norm_num)
  have h1536 : (1536:ZMod p)≠0 := by
    simpa only [Nat.cast_ofNat] using hnat 1536 (by norm_num)
  have h2304 : (2304:ZMod p)≠0 := by
    simpa only [Nat.cast_ofNat] using hnat 2304 (by norm_num)
  have h4608 : (4608:ZMod p)≠0 := by
    simpa only [Nat.cast_ofNat] using hnat 4608 (by norm_num)
  fin_cases J <;>
    norm_num [secondaryTentSourceMacroTrace, secondaryTentSourceTraceNumerator,
      secondaryTentSourceMomentForward, secondaryTentSourceZetaForward,
      secondaryTentRowNaturalP, secondaryTentRowNaturalQ,
      secondaryTentSourceMacroIntegerTable, palindromicRatResidue,
      momentRatSigned, momentRatNegOne, momentRat, boundaryPlus, boundaryMinus,
      momentScalar, centralCoeff, zetaRat, harmonicRat,
      mul_add, add_mul, mul_sub, sub_mul, ← mul_assoc,
      coeff_add, coeff_sub, coeff_C_mul, coeff_mul_C, coeff_mul_X_pow',
      coeff_X_mul, coeff_C_mul_X_pow,
      Finset.sum_range_succ, Fin.sum_univ_succ] <;>
    field_simp [h2, h3, h4, h6, h8, h9, h12, h16, h18, h24, h32, h36, h48, h64, h72, h96, h128, h144, h192, h256, h288, h384, h512, h576, h768, h1152, h1536, h2304, h4608] <;> ring

def secondaryTentSourceFixedResponseInteger : Matrix (Fin 4) (Fin 5) ℤ :=
  !![747824613120, 0, 0, 747824613120, 0;
     747824613120, 0, 0, 0, 0;
     747824613120, 0, 0, 0, 0;
     747824613120, 0, 0, 0, -23101261920]

/-- Literal actual-source responses of the five integer-scaled seeds over
the prime field, with exactly the human proof's fixed exceptional set. -/
theorem secondaryTent_source_fixed_macro_modular {p : ℕ} [Fact p.Prime]
    (hp : ¬p ∣ 6310886697782126553600) (J : Fin 4) (i : Fin 5) :
    (secondaryTentSourceMacroTrace p J.val
      (fun k => (secondaryTentSeedCoefficients k i:ZMod p))).coeff 5 =
      (secondaryTentSourceFixedResponseInteger J i:ZMod p) := by
  have hh := secondaryTent_source_macro_trace_modular hp
    (⟨J.val,by omega⟩:Fin 5) (fun k => (secondaryTentSeedCoefficients k i:ZMod p))
  have htable :
      (∑ k : Fin 7,
        (secondaryTentSourceMacroIntegerTable ⟨J.val,by omega⟩ k:ZMod p)*
        (secondaryTentSeedCoefficients k i:ZMod p)) =
      (4608:ZMod p)*(secondaryTentSourceFixedResponseInteger J i:ZMod p) := by
    fin_cases J <;> fin_cases i <;>
      norm_num [secondaryTentSourceMacroIntegerTable, secondaryTentSeedCoefficients,
        secondaryTentSourceFixedResponseInteger, Fin.sum_univ_succ] <;> ring
  rw [htable] at hh
  exact mul_left_cancel₀ (secondaryTent_source_fixed_denominator_unit hp 4608
    secondaryTent_source_denominator_dvd_exceptional) hh

end
end CatalanMeasure.Parametric
