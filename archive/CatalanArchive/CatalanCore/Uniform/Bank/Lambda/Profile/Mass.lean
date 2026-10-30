import CatalanCore.Uniform.Bank.Lambda.Profile.C1
import CatalanCore.Uniform.Bank.Lambda.Profile.C3
import CatalanCore.Uniform.Bank.Lambda.NoUF
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Lambda
open CatalanCore.Arith.Hybrid
/-- The infinite sawtooth prefix (0,1/10) plus the two finite class envelopes.
This identifies the mass; physical price coverage is a separate obligation. -/
theorem noUF_profile_mass (C0 : ℝ) :
    41 / 200 + (1 / 50) * Real.log 2 +
      (listInt (profile1 C0) + listInt (profile3 C0)) / 2 = LamNoUF := by
  rw [profile1_mass, profile3_mass]
  unfold profile1Mass profile3Mass LamNoUF
  push_cast
  ring
#print axioms noUF_profile_mass
end CatalanCore.Uniform.Bank.Lambda
