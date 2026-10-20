module
public import CatalanFrames.HybCommon.DeficitProfile.Guard
@[expose] public section
open Finset Filter CatalanCore CatalanCore.Arith.Hybrid
namespace CatalanFrames.HybCommon
/-- Unconditional new-profile prime mass, with the same denominator range as the old content bound. -/
theorem profile_deficit_sum_lower {Fr : Frame} (I : HybInst Fr) {o : ℕ}
    (ho : o=1 ∨ o=3) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠr : ℕ in atTop,
      (r : ℝ)^2*((profileIntegral : ℝ)-ε)≤
        ∑p∈(range (Bnd I r (r/8))).filter Nat.Prime,
          (profileDeficit o r p : ℝ)*Real.log p := by
  apply profile_sum_lower ho (profileDeficit o) (by norm_num : (0 : ℝ)≤8)
    (profileCover ho) (fun r => Bnd I r (r/8)) ?_ hε
  intro r P hP
  have hh : (P.hi : ℝ)≤1 := by exact_mod_cast newProfile_hi_le_one P hP
  have hm:=Nat.floor_le_floor (mul_le_mul_of_nonneg_right hh (Nat.cast_nonneg r : (0 : ℝ)≤r))
  simp only [one_mul,Nat.floor_natCast] at hm
  have hb:=Bnd_ge I r (r/8)
  omega
#print axioms profile_deficit_sum_lower
end CatalanFrames.HybCommon
