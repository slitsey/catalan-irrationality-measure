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

/-- Add the new uniform interval savings to the banked seven windows.  Only
the new local arithmetic family is an input; summation and numerics are closed. -/
theorem profile_both_eps_of_defBoth (I : HybInst Fr) [∀r, I.DiagOK r (r/8)]
    {o Lc cm : ℕ} (hL : LamData Fr o) (ho : o=1 ∨ o=3)
    (T : TropFacts I o) (B : BadInfo I Lc cm)
    (hnew : ∀ᶠr : ℕ in atTop, DefBothG I r (profileT o I r) (profileDeficit o r)) :
    ∀ε>0, ∀ᶠr : ℕ in atTop, ∃T δ : ℕ→ℕ, DefBothG I r T δ ∧
      Real.log (DhybT I r (r/8) T δ)≤((184137/50000 : ℝ)+ε)*(r : ℝ)^2 := by
  apply both_eps_G7_extra I ho (profileT o I) (profileDeficit o) (profileIntegral : ℝ)
  · filter_upwards [hnew,eventually_ge_atTop 16] with r hn hr
    have hold := (defBoth_all7 hL ho hr).mono_T (fun p hp hb => profileT_ge o I r p)
    exact hold.add hn (fun p hp hb => profileDeficit_disjoint_all7 ho hr p)
  · intro ε hε
    have hh := profile_deficit_sum_lower I ho hε
    filter_upwards [hh] with r hr
    nlinarith [hr]
  · exact fun ε hε => profile_logDhybT_le T B hε
  · have hh := (Rat.cast_le (K := ℝ)).2 profile_content_round
    unfold baseLambda at hh
    push_cast at hh
    exact hh

/-- Unconditional two-member content with the full certified interval profile. -/
theorem profile_both_eps (I : HybInst Fr) [∀r, I.DiagOK r (r/8)]
    {o Lc cm : ℕ} (hL : LamData Fr o) (ho : o=1 ∨ o=3)
    (T : TropFacts I o) (B : BadInfo I Lc cm) :
    ∀ε>0, ∀ᶠr : ℕ in atTop, ∃T δ : ℕ→ℕ, DefBothG I r T δ ∧
      Real.log (DhybT I r (r/8) T δ)≤((184137/50000 : ℝ)+ε)*(r : ℝ)^2 :=
  profile_both_eps_of_defBoth I hL ho T B (profile_defBoth I hL ho)

#print axioms profile_both_eps

end CatalanFrames.HybCommon
