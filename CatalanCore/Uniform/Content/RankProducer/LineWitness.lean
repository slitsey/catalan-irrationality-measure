import CatalanCore.Uniform.Content.RankProducer.RationalLoads
set_option Elab.async false
namespace CatalanCore.Uniform.Content.RankProducer
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.Hybrid
open Module
open scoped Classical
variable (p : ℕ) [Fact p.Prime]

/-- An exact rational direction supplies a column intersection after reduction. -/
theorem col_line_lower_of_omega (c : FibreCert) (d : ℕ) (v : ℚ × ℚ)
    (hd : d ∈ c.kc) (hv : castV p v ≠ 0)
    (hc : castV p (c.cload d) ≠ 0)
    (hv1 : v.1 ∈ S p) (hv2 : v.2 ∈ S p)
    (hc1 : (c.cload d).1 ∈ S p) (hc2 : (c.cload d).2 ∈ S p)
    (horth : v.1 * (c.cload d).2 - v.2 * (c.cload d).1 = 0) :
    1 ≤ finrank (RatFunc (ZMod p))
      ↥(Submodule.span (RatFunc (ZMod p)) {castV p v} ⊓ Ucol p c) := by
  apply one_le_col_intersection p c _ d hd hc
  exact mem_span_of_omega_eq_zero (castV p v) (castV p (c.cload d)) hv
    (castV_omega_eq_zero p v (c.cload d) hv1 hv2 hc1 hc2 horth)

/-- Exact annihilation of all killed row loads supplies the row intersection. -/
theorem row_line_lower_of_omega (c : FibreCert) (v : ℚ × ℚ)
    (hv : castV p v ≠ 0) (hv1 : v.1 ∈ S p) (hv2 : v.2 ∈ S p)
    (hc : ∀ d ∈ c.kr, (c.rload d).1 ∈ S p ∧ (c.rload d).2 ∈ S p)
    (horth : ∀ d ∈ c.kr, (c.rload d).1 * v.2 - (c.rload d).2 * v.1 = 0) :
    1 ≤ finrank (RatFunc (ZMod p))
      ↥(Submodule.span (RatFunc (ZMod p)) {castV p v} ⊓ Urow p c) := by
  apply one_le_row_intersection p c _ (castV p v) hv
  · exact Submodule.subset_span (by simp)
  · intro d hd
    exact castV_omega_eq_zero p (c.rload d) v (hc d hd).1 (hc d hd).2 hv1 hv2 (horth d hd)

#print axioms col_line_lower_of_omega
#print axioms row_line_lower_of_omega
end CatalanCore.Uniform.Content.RankProducer
