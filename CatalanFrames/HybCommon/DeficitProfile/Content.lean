module
public import CatalanFrames.HybCommon.DeficitProfile.Log
public import CatalanFrames.HybCommon.DeficitProfile.SumFinal
public import CatalanFrames.HybCommon.DeficitProfile.OldDisjoint
public import CatalanFrames.HybCommon.Final
public import CatalanFrames.HybCommon.DeficitProfile.Arithmetic
@[expose] public section
open Finset Filter Classical CatalanCore CatalanCore.Arith CatalanCore.Arith.Hybrid
namespace CatalanFrames.HybCommon
variable {Fr : Frame}

/-- Add the uniform interval savings of an arbitrary row list to the banked seven windows.
Only the new local arithmetic family (`hnew`) is an input; summation and numerics are closed. -/
theorem profile_both_eps_of_defBothL (I : HybInst Fr) [∀r, I.DiagOK r (r/8)]
    {o Lc cm : ℕ} (hL : LamData Fr o) (ho : o=1 ∨ o=3)
    (T : TropFacts I o) (B : BadInfo I Lc cm) {L : List DeficitRow} (hD : RowData L)
    (hcover : ProfileCoverL L o (profileDeficitL L o) 8) {c : ℝ}
    (hc : 24729491161 / 6665218560 - 1 / 448 - 1 / 576 - 1 / 352 - (profileIntegralL L : ℝ) ≤ c)
    (hnew : ∀ᶠr : ℕ in atTop, DefBothG I r (profileTL L o I r) (profileDeficitL L o r)) :
    ∀ε>0, ∀ᶠr : ℕ in atTop, ∃T δ : ℕ→ℕ, DefBothG I r T δ ∧
      Real.log (DhybT I r (r/8) T δ)≤(c+ε)*(r : ℝ)^2 := by
  apply both_eps_G7_extra I ho (profileTL L o I) (profileDeficitL L o) (profileIntegralL L : ℝ)
  · filter_upwards [hnew,eventually_ge_atTop 16] with r hn hr
    have hold := (defBoth_all7 hL ho hr).mono_T (fun p hp hb => profileT_ge L o I r p)
    exact hold.add hn (fun p hp hb => profileDeficit_disjoint_all7 L ho hr p)
  · intro ε hε
    have hh := profile_deficit_sum_lowerL I hD ho hcover hε
    filter_upwards [hh] with r hr
    nlinarith [hr]
  · exact fun ε hε => profile_logDhybT_le hD T B hε
  · exact hc

/-- **Interface for the final assembly.**  For an arbitrary row list `L` with
* `hD : RowData L` (row data, disjointness, nodup, lift support),
* `hrow : ProfileRowLocal I o L` (per-row local GLE bounds for both family members),
* `hcover : ProfileCoverL L o (profileDeficitL L o) 8` (from `profileCoverL_of_good`),
* `hc` (the exact content constant of the list),
the merged deficit family gives the two-member content bound `(c + ε) r²`.  No measure theorem is
used.  The banked list is the instance `L = newProfile`, `c = 184137/50000`. -/
theorem profile_both_eps_of_rows (I : HybInst Fr) [∀r, I.DiagOK r (r/8)]
    {o Lc cm : ℕ} (hL : LamData Fr o) (ho : o=1 ∨ o=3)
    (T : TropFacts I o) (B : BadInfo I Lc cm) {L : List DeficitRow} (hD : RowData L)
    (hrow : ProfileRowLocal I o L)
    (hcover : ProfileCoverL L o (profileDeficitL L o) 8) {c : ℝ}
    (hc : 24729491161 / 6665218560 - 1 / 448 - 1 / 576 - 1 / 352 - (profileIntegralL L : ℝ) ≤ c) :
    ∀ε>0, ∀ᶠr : ℕ in atTop, ∃T δ : ℕ→ℕ, DefBothG I r T δ ∧
      Real.log (DhybT I r (r/8) T δ)≤(c+ε)*(r : ℝ)^2 :=
  profile_both_eps_of_defBothL I hL ho T B hD hcover hc (profile_defBothL I hD hrow ho)

theorem profile_content_round_real :
    24729491161 / 6665218560 - 1 / 448 - 1 / 576 - 1 / 352 - (profileIntegral : ℝ) ≤ 184137/50000 := by
  have hh := (Rat.cast_le (K := ℝ)).2 profile_content_round
  unfold baseLambda at hh
  push_cast at hh
  exact hh

/-- Add the new uniform interval savings to the banked seven windows (banked rows). -/
theorem profile_both_eps_of_defBoth (I : HybInst Fr) [∀r, I.DiagOK r (r/8)]
    {o Lc cm : ℕ} (hL : LamData Fr o) (ho : o=1 ∨ o=3)
    (T : TropFacts I o) (B : BadInfo I Lc cm)
    (hnew : ∀ᶠr : ℕ in atTop, DefBothG I r (profileT o I r) (profileDeficit o r)) :
    ∀ε>0, ∀ᶠr : ℕ in atTop, ∃T δ : ℕ→ℕ, DefBothG I r T δ ∧
      Real.log (DhybT I r (r/8) T δ)≤((184137/50000 : ℝ)+ε)*(r : ℝ)^2 :=
  profile_both_eps_of_defBothL I hL ho T B newProfile_rowData (profileCover ho)
    profile_content_round_real hnew

/-- Unconditional two-member content with the full certified interval profile. -/
theorem profile_both_eps (I : HybInst Fr) [∀r, I.DiagOK r (r/8)]
    {o Lc cm : ℕ} (hL : LamData Fr o) (ho : o=1 ∨ o=3)
    (T : TropFacts I o) (B : BadInfo I Lc cm) :
    ∀ε>0, ∀ᶠr : ℕ in atTop, ∃T δ : ℕ→ℕ, DefBothG I r T δ ∧
      Real.log (DhybT I r (r/8) T δ)≤((184137/50000 : ℝ)+ε)*(r : ℝ)^2 :=
  profile_both_eps_of_rows I hL ho T B newProfile_rowData (profileRowLocal_new I hL ho)
    (profileCover ho) profile_content_round_real

#print axioms profile_both_eps
#print axioms profile_both_eps_of_rows

end CatalanFrames.HybCommon
