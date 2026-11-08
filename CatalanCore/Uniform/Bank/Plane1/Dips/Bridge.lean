module

public import CatalanCore.Uniform.Bank.Plane1.Dips.Line

@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 1600000

/-! # Max-bridges (wave R1; ledger R01-R03)

`max_bridge_valid`: a branch whose price is `max (τ_A, τ_B)` (same debit), valid whenever `A` and `B` are, provided its
conditions (with the facts every plane member provides) imply all the conditions of `A` or all those of `B`.  A bridge at
a type boundary of the dip lines is an instance: window and class conditions imply the conditions of the line on the
side that the rounding selects.  The bridge is the strip branch at the boundary (value `max = ` the common value). -/

namespace CatalanCore.Uniform.Bank.Plane1.Dips
open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Content.Shape CatalanCore.Uniform.Content.BankShared
  CatalanCore.Uniform.Content.BankShared.KTerm CatalanCore.Uniform.Bank.Plane1

theorem max_bridge_valid (σ : Support) (a b c : ℤ) (h0 : a + b + c = 0) (depth Q0 Pbad N0 : ℕ) (hQ0 : 3 ≤ Q0)
    (hP : 6 ≤ Pbad) (A B br : KBranch) (hτ : br.τ = KExpr.mx A.τ B.τ) (hdA : br.debit = A.debit)
    (hdB : br.debit = B.debit)
    (hAB : ∀ (r p m : ℕ) (kv : ℕ → ℕ), r % 2 = 0 → 0 < r → 6 < p → (r ≤ 12 * m + 6 ∧ 12 * m < r + 6) →
      2 * m ≤ r →
      (∃ jA, 3 * kv 0 = jA * p + σ.rho ∧ 0 < jA ∧ jA < 3 ∧ 0 < kv 0 ∧ kv 0 < p) →
      (∃ jB, 2 * kv 1 = jB * p + 1 ∧ 0 < jB ∧ jB < 2 ∧ 0 < kv 1 ∧ kv 1 < p) →
      (∀ cd ∈ br.conds, cd.Holds r p m kv) →
      (∀ cd ∈ A.conds, cd.Holds r p m kv) ∨ (∀ cd ∈ B.conds, cd.Holds r p m kv))
    (hA : KCatValid planeC planeC_pos (planeFrame σ a b c h0) depth (planeBundle σ a b c h0).shifts Q0 Pbad N0 [A])
    (hB : KCatValid planeC planeC_pos (planeFrame σ a b c h0) depth (planeBundle σ a b c h0).shifts Q0 Pbad N0 [B]) :
    KCatValid planeC planeC_pos (planeFrame σ a b c h0) depth (planeBundle σ a b c h0).shifts Q0 Pbad N0 [br] := by
  intro b' hb' i hi hr0 p hpf hPb hN hqN kv hroots hcond
  rw [List.mem_singleton] at hb'
  subst hb'
  obtain ⟨⟨jA, eA, hjA0, hjA3, hkA0, hkAp⟩, ⟨jB, eB, hjB0, hjB2, hkB0, hkBp⟩⟩ :=
    (planeBundle σ a b c h0).roots_facts hroots
  have hr : i.1 % 2 = 0 := hi.2
  have hbd := plane_border (r := i.1) hr
  have hm2 := border_two_m_le planeC planeC_pos planeC_le_one hr hr0
  rcases hAB i.1 p ((altGeom planeC planeC_pos).borderSize i.1) kv hr hr0 (by omega) hbd hm2
    ⟨jA, eA, hjA0, hjA3, hkA0, hkAp⟩ ⟨jB, eB, hjB0, hjB2, hkB0, hkBp⟩ hcond with h | h
  · obtain ⟨n, hn, hle⟩ := hA A (List.mem_singleton_self _) i hi hr0 p hPb hN hqN kv hroots h
    refine ⟨n, hn, le_trans hle ?_⟩
    rw [hτ, ← hdA]
    simp only [KExpr.evalN]
    omega
  · obtain ⟨n, hn, hle⟩ := hB B (List.mem_singleton_self _) i hi hr0 p hPb hN hqN kv hroots h
    refine ⟨n, hn, le_trans hle ?_⟩
    rw [hτ, ← hdB]
    simp only [KExpr.evalN]
    omega

end CatalanCore.Uniform.Bank.Plane1.Dips

#print axioms CatalanCore.Uniform.Bank.Plane1.Dips.max_bridge_valid
