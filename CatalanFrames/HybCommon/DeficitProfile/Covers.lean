module
public import CatalanFrames.HybCommon.DeficitProfile.Rounding
public import CatalanCore.Arith.Hybrid.WitnessScaling
@[expose] public section
open Finset Filter Topology CatalanCore.Arith.Hybrid
namespace CatalanFrames.HybCommon
lemma profileRowDeficit_real_cover {o r p : ℕ} (ho : o=1 ∨ o=3) (hr : 0<r)
    (P : DeficitRow) (hP : P∈newProfile) (ha : profileRowActive o r p P) :
    (P.a : ℝ)*r+(P.b : ℝ)*p-8≤(profileRowDeficit o r p P : ℝ) := by
  have hc:=newProfile_cert P hP
  have hrR : (0 : ℝ)<r := by exact_mod_cast hr
  have hs : (0 : ℝ)<P.lo := by exact_mod_cast hc.2.1
  have ht : (0 : ℝ)≤P.hi := by
    have hh : (P.lo : ℝ)<P.hi := by exact_mod_cast hc.2.2.1
    linarith
  have hpL : (P.lo : ℝ)*r<p := (Nat.floor_lt (mul_nonneg hs.le hrR.le)).mp ha.2.1
  have hpH : (p : ℝ)≤(P.hi : ℝ)*r := (Nat.le_floor_iff (mul_nonneg ht hrR.le)).mp ha.2.2
  have huL : (P.lo : ℝ)≤(p : ℝ)/r := (le_div_iff₀ hrR).2 hpL.le
  have huH : (p : ℝ)/r≤(P.hi : ℝ) := (div_le_iff₀ hrR).2 hpH
  have hp : p≤r := by
    have hhi : (P.hi : ℝ)≤1 := by exact_mod_cast newProfile_hi_le_one P hP
    have hx := hpH.trans (mul_le_mul_of_nonneg_right hhi hrR.le)
    norm_num only [one_mul] at hx
    exact_mod_cast hx
  have ho3 : o≤3 := by rcases ho with rfl|rfl <;> omega
  have hev : (r : ℝ)*((P.a : ℝ)+(P.b : ℝ)*((p : ℝ)/r))=(P.a : ℝ)*r+(P.b : ℝ)*p := by
    field_simp <;> ring
  by_cases hk : P.kind=0
  · have hw:=mul_le_mul_of_nonneg_left (row_lowWitness hc hk huL huH) hrR.le
    rw [hev,lowWitness_mul _ _ _ _ hrR] at hw
    simp only [div_mul_eq_mul_div] at hw
    have hround:=profileRowDeficit_low_rounding o r p P ho3 hp hk
    linarith
  · have hw:=mul_le_mul_of_nonneg_left (row_ncWitness hc hk huL huH) hrR.le
    rw [hev,ncWitness_mul _ _ _ _ hrR] at hw
    simp only [div_mul_eq_mul_div] at hw
    have hround:=profileRowDeficit_nc_rounding o r p P ho3 hk
    linarith

/-- **Generic cover step.**  For any row list: the affine lower bound on each active row's
deficit (the arithmetic input `hcov`, proved for the banked rows by `profileRowDeficit_real_cover`)
and eventual validity of the explicit good-prime guard give the real cover input. -/
theorem profileCoverL_of_good {L : List DeficitRow} {o : ℕ}
    (hcov : ∀ r : ℕ, 0<r → ∀P∈L, ∀p : ℕ, profileRowActive o r p P →
      (P.a : ℝ)*r+(P.b : ℝ)*p-8≤(profileRowDeficit o r p P : ℝ))
    (hgood : ∀ᶠr : ℕ in atTop,∀P∈L,∀p : ℕ,p.Prime →
      profileRowActive o r p P → profilePrimeGood o r p) :
    ProfileCoverL L o (profileDeficitL L o) 8 := by
  filter_upwards [hgood,eventually_ge_atTop 1] with r hr hr1
  intro P hP p hpL hpH hp hc
  have ha : profileRowActive o r p P := ⟨hc,hpL,hpH⟩
  have hh:=hcov r (by omega) P hP p ha
  have hle : (profileRowDeficit o r p P : ℝ)≤profileDeficitL L o r p := by
    exact_mod_cast profileDeficit_ge_row o r p P hP (hr P hP p hp ha) ha
  exact hh.trans hle

/-- Integer rounding and all rational profile witnesses discharge the real cover input for the
banked rows; only eventual validity of the explicit good-prime guard remains geometric. -/
theorem profileCover_of_good {o : ℕ} (ho : o=1 ∨ o=3)
    (hgood : ∀ᶠr : ℕ in atTop,∀P∈newProfile,∀p : ℕ,p.Prime →
      profileRowActive o r p P → profilePrimeGood o r p) :
    ProfileCover o (profileDeficit o) 8 :=
  profileCoverL_of_good (fun r hr P hP p ha => profileRowDeficit_real_cover ho hr P hP ha) hgood
#print axioms profileCover_of_good
end CatalanFrames.HybCommon
