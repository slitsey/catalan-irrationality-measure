module
public import CatalanCore.Arith.Hybrid.Extra
@[expose] public section
open Filter CatalanCore.Arith.Hybrid
namespace CatalanFrames.HybGen
/-- Transport the existing negligible bound to a larger fixed numerology by scaling. -/
theorem extra_small_of_double_domination (f : ℕ → ℕ → ℝ)
    (hdom : ∀ r m, m ≤ r → f r m ≤ 5*extraBound (2*r) (2*m))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop, ∀ m ≤ r, f r m ≤ ε*(r : ℝ)^2 := by
  obtain ⟨R,hR⟩ := eventually_atTop.mp (extra_small (ε/20) (by positivity))
  filter_upwards [eventually_ge_atTop R] with r hr
  intro m hm
  have hh := hR (2*r) (by omega) (2*m) (by omega)
  have hd := hdom r m hm
  push_cast at hh
  nlinarith only [hh,hd]
end CatalanFrames.HybGen
#print axioms CatalanFrames.HybGen.extra_small_of_double_domination
