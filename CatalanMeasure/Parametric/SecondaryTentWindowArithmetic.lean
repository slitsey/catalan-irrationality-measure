module
public import CatalanMeasure.Parametric.SecondaryTentParametersFilteredRank
@[expose] public section
namespace CatalanMeasure.Parametric
open Polynomial
noncomputable section

/-- All eventual arithmetic side conditions for the literal tent, with
the fixed exceptional primes removed by an explicit index threshold. -/
structure SecondaryTentWindowData (N p : ℕ) [Fact p.Prime] : Prop where
  index_pos : 0<N
  five_index_lt : 5*N<p
  g_pos : 0<27*N-4*p
  a_add_g : (p-(27*N-4*p))+(27*N-4*p)=p
  b_add_three : (p-3*N)+3*N=p
  g_add_four : (27*N-4*p)+4*p=27*N
  prime_odd : p=2*(p/2)+1
  prime_ne_two : p≠2
  prime_ne_center : p≠6*N
  shared_cap_lower : 8*N+2≤2*p
  shared_cap_upper : p≤8*N
  lower_endpoint : 2*p≤24*N
  branch_bound : N+p/2≤p-N
  source_width : 27*N≤5*p
  source_square : 44*N<p^2
  exceptional : ¬p ∣ 6310886697782126553600
  two_unit : (2:ZMod p)≠0
  seed_unit : (3445975817256960:ZMod p)≠0

theorem secondaryTent_window_data {N p : ℕ} [Fact p.Prime]
    (hN : 6310886697782126553600≤N) (hlo : 52*N<9*p) (hhi : 7*p<44*N) :
    SecondaryTentWindowData N p := by
  have hN0 : 0<N := by omega
  have h5 : 5*N<p := by omega
  have hp2 : p≠2 := by omega
  have hoddmod := (Fact.out : p.Prime).eq_two_or_odd.resolve_left hp2
  have hdiv := Nat.div_add_mod p 2
  have hodd : p=2*(p/2)+1 := by omega
  have hsq : 44*N<p^2 := by
    have hprod := Nat.mul_lt_mul_of_pos_right h5 (Fact.out : p.Prime).pos
    have hbig := Nat.mul_le_mul_left (5*N) (by omega : 10≤p)
    nlinarith
  refine {
    index_pos := hN0
    five_index_lt := h5
    g_pos := by omega
    a_add_g := by omega
    b_add_three := by omega
    g_add_four := by omega
    prime_odd := hodd
    prime_ne_two := hp2
    prime_ne_center := by omega
    shared_cap_lower := by omega
    shared_cap_upper := by omega
    lower_endpoint := by omega
    branch_bound := by omega
    source_width := by omega
    source_square := hsq
    exceptional := ?_
    two_unit := ?_
    seed_unit := ?_
  }
  · intro hd
    have hh := Nat.le_of_dvd (by norm_num : 0<6310886697782126553600) hd
    omega
  · intro hz
    have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp hz
    have hh := Nat.le_of_dvd (by norm_num : 0<2) hd
    omega
  · intro hz
    have hd : p ∣ 3445975817256960 := (ZMod.natCast_eq_zero_iff 3445975817256960 p).mp hz
    have hh := Nat.le_of_dvd (by norm_num : 0<3445975817256960) hd
    omega

end
end CatalanMeasure.Parametric
