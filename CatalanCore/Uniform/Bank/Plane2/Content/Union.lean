module

public import CatalanCore.Uniform.Bank.Plane2.Content.Tail

@[expose] public section
set_option Elab.async false

open Polynomial Finset Matrix CatalanCore.Basic CatalanCore.Arith.Hybrid

/-!
# Plane 2 content: the union of the rows `P₅` and `P₆` across `N = p` (lane H, wave P210-L; ledger P210)

The rows `P₅` (`r ≤ p ≤ N`) and `P₆` (`N ≤ p ≤ 2r`) meet at `θ = 1 + 2 α`, where their prices cross.  Each has a closed
condition on `N - p = r + 2m - p` that is inexact at its end (`m` is rounded), so a piece of the head cannot end at the
boundary.  `brU56` (price `max(τ₅, τ₆)`, conditions `r ≤ p ≤ 2r`) holds on both sides and is the branch of the short gap
piece around the boundary; `real_U56` is the case split on `p ≤ N`.
-/

namespace CatalanCore.Uniform.Bank.Plane2.Content

open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Support CatalanCore.Uniform.Content.Sweep
  CatalanCore.Uniform.Content.Shape CatalanCore.Uniform.Content.Wire
  CatalanCore.Uniform.Content.BankShared CatalanCore.Uniform.Content.BankShared.Check
  CatalanCore.Uniform.Content.BankShared.KTerm KExpr

/-- Rows `P₅` and `P₆` across `p = N`: `max(τ₅, τ₆)` for `r ≤ p ≤ 2r`. -/
def brU56 : KBranch :=
  ⟨.mx brP5.τ brP6.τ, [⟨-1, 1, 0, [], 0, false⟩, ⟨2, -1, 0, [], 0, false⟩, gGuard], 0⟩

theorem ns_holds {r p m : ℕ} {kv : ℕ → ℕ} {cr cp cm c1 : ℤ} (h : 0 ≤ cr * r + cp * p + cm * m + c1) :
    KCond.Holds ⟨cr, cp, cm, [], c1, false⟩ r p m kv := by
  simpa [KCond.Holds, KCond.L, dot] using h

theorem real_U56 (v u : ℤ) : Real v u brU56 := by
  intro r p _ S kv hr hr0 hPb hN0 hN hk hcond
  have hc1 := holds_ns (hcond ⟨-1, 1, 0, [], 0, false⟩ (by simp [brU56]))
  have hc2 := holds_ns (hcond ⟨2, -1, 0, [], 0, false⟩ (by simp [brU56]))
  have hg := hcond gGuard (by simp [brU56])
  by_cases hcase : p ≤ r + 2 * p2G.borderSize r
  · obtain ⟨n, hn, hb⟩ := real_P5 v u r p S kv hr hr0 hPb hN0 hN hk (by
      intro cd hcd
      simp only [brP5, List.mem_cons, List.not_mem_nil, or_false] at hcd
      rcases hcd with rfl | rfl | rfl
      · exact ns_holds (by omega)
      · exact ns_holds (by omega)
      · exact hg)
    exact ⟨n, hn, le_trans hb (le_max_left _ _)⟩
  · obtain ⟨n, hn, hb⟩ := real_P6 v u r p S kv hr hr0 hPb hN0 hN hk (by
      intro cd hcd
      simp only [brP6, List.mem_cons, List.not_mem_nil, or_false] at hcd
      rcases hcd with rfl | rfl | rfl
      · exact ns_holds (by omega)
      · exact ns_holds (by omega)
      · exact hg)
    exact ⟨n, hn, le_trans hb (le_max_right _ _)⟩

end CatalanCore.Uniform.Bank.Plane2.Content
#print axioms CatalanCore.Uniform.Bank.Plane2.Content.real_U56
