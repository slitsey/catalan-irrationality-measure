module

public import CatalanCore.Uniform.Bank.Plane1.Dips.Line

@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 1600000

/-! # Max-bridges (wave R1; ledger R01-R03)

`max_bridge_valid`: a branch whose price is the maximum of the prices of a list of valid branches (same debit) is valid
whenever its conditions (with the facts every plane member provides) imply all the conditions of SOME listed branch.
A **bridge** at a type boundary of the dip lines is an instance (`DipBridge`): the window `x (1 - ε) ≤ p / r ≤ x (1 + ε)`
and the class condition imply the conditions of one of the lines of the configurations that occur in the window.  The
bridge is the strip branch at the boundary (value `max` = the common value of the adjacent lines). -/

namespace CatalanCore.Uniform.Bank.Plane1.Dips
open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Content.Shape CatalanCore.Uniform.Content.BankShared
  CatalanCore.Uniform.Content.BankShared.KTerm CatalanCore.Uniform.Bank.Plane1

/-- The maximum of a list of expressions (`0` for the empty list). -/
def mxl : List KExpr → KExpr
  | [] => KExpr.cst 0
  | [e] => e
  | e :: f :: es => KExpr.mx e (mxl (f :: es))

theorem evalN_le_mxl (r p m : ℕ) (kv : ℕ → ℕ) : ∀ (es : List KExpr) (e : KExpr), e ∈ es →
    e.evalN r p m kv ≤ (mxl es).evalN r p m kv
  | [], e, h => absurd h List.not_mem_nil
  | [f], e, h => by
    rw [List.mem_singleton] at h
    subst h
    exact le_rfl
  | f :: g :: es, e, h => by
    simp only [mxl, KExpr.evalN]
    rcases List.mem_cons.1 h with rfl | h
    · exact le_max_left _ _
    · exact le_trans (evalN_le_mxl r p m kv (g :: es) e h) (le_max_right _ _)

/-- The facts that every border member of the plane family provides about `(r, p, m, k_A, k_B)`. -/
def PlaneFacts (ρ : ℕ) (r p m : ℕ) (kv : ℕ → ℕ) : Prop :=
  r % 2 = 0 ∧ 0 < r ∧ 6 < p ∧ (r ≤ 12 * m + 6 ∧ 12 * m < r + 6) ∧ 2 * m ≤ r ∧
    (∃ jA, 3 * kv 0 = jA * p + ρ ∧ 0 < jA ∧ jA < 3 ∧ 0 < kv 0 ∧ kv 0 < p) ∧
    (∃ jB, 2 * kv 1 = jB * p + 1 ∧ 0 < jB ∧ jB < 2 ∧ 0 < kv 1 ∧ kv 1 < p)

theorem max_bridge_valid (σ : Support) (a b c : ℤ) (h0 : a + b + c = 0) (depth Q0 Pbad N0 : ℕ) (hQ0 : 3 ≤ Q0)
    (hP : 6 ≤ Pbad) (Ls : List KBranch) (br : KBranch) (hτ : br.τ = mxl (Ls.map (fun A => A.τ)))
    (hd : ∀ A ∈ Ls, br.debit = A.debit)
    (hAB : ∀ (r p m : ℕ) (kv : ℕ → ℕ), PlaneFacts σ.rho r p m kv →
      (∀ cd ∈ br.conds, cd.Holds r p m kv) → ∃ A ∈ Ls, ∀ cd ∈ A.conds, cd.Holds r p m kv)
    (hL : ∀ A ∈ Ls, KCatValid planeC planeC_pos (planeFrame σ a b c h0) depth (planeBundle σ a b c h0).shifts Q0
      Pbad N0 [A]) :
    KCatValid planeC planeC_pos (planeFrame σ a b c h0) depth (planeBundle σ a b c h0).shifts Q0 Pbad N0 [br] := by
  intro b' hb' i hi hr0 p hpf hPb hN hqN kv hroots hcond
  rw [List.mem_singleton] at hb'
  subst hb'
  obtain ⟨⟨jA, eA, hjA0, hjA3, hkA0, hkAp⟩, ⟨jB, eB, hjB0, hjB2, hkB0, hkBp⟩⟩ :=
    (planeBundle σ a b c h0).roots_facts hroots
  have hr : i.1 % 2 = 0 := hi.2
  have hbd := plane_border (r := i.1) hr
  have hm2 := border_two_m_le planeC planeC_pos planeC_le_one hr hr0
  obtain ⟨A, hA, hAc⟩ := hAB i.1 p ((altGeom planeC planeC_pos).borderSize i.1) kv
    ⟨hr, hr0, by omega, hbd, hm2, ⟨jA, eA, hjA0, hjA3, hkA0, hkAp⟩, ⟨jB, eB, hjB0, hjB2, hkB0, hkBp⟩⟩ hcond
  obtain ⟨n, hn, hle⟩ := hL A hA A (List.mem_singleton_self _) i hi hr0 p hPb hN hqN kv hroots hAc
  refine ⟨n, hn, le_trans hle ?_⟩
  have h1 := evalN_le_mxl i.1 p ((altGeom planeC planeC_pos).borderSize i.1) kv _ A.τ
    (List.mem_map.2 ⟨A, hA, rfl⟩)
  rw [hτ, hd A hA]
  exact Nat.add_le_add_right h1 _

/-! ### Bridges of dip lines -/

/-- A bridge at a type boundary: the window `ln / ld ≤ p / r ≤ hn / hd` of the ratio `p / r`, the class `n`, and the
lines of the configurations that occur in the window. -/
structure DipBridge where
  n : ℕ
  ln : ℤ
  ld : ℤ
  hn : ℤ
  hd : ℤ
  lines : List DipLine

namespace DipBridge
variable (B : DipBridge)

/-- The catalogue branch: price the maximum of the prices of the lines, debit 2. -/
def toBranch : KBranch :=
  ⟨mxl (B.lines.map DipLine.tau),
    [⟨-B.ln, B.ld, 0, [0, 0], 0, false⟩, ⟨B.hn, -B.hd, 0, [0, 0], 0, false⟩, DipLine.classCond B.n], 2⟩

/-- **Membership**: under the window, the class condition and the plane facts, the conditions of one of the lines hold. -/
def Member (ρ : ℕ) : Prop :=
  1 ≤ ρ → ρ ≤ 2 → ∀ (r p m : ℕ) (kv : ℕ → ℕ), PlaneFacts ρ r p m kv → (∀ cd ∈ B.toBranch.conds, cd.Holds r p m kv) →
    ∃ L ∈ B.lines, ∀ cd ∈ L.conds ρ, cd.Holds r p m kv

/-- A bridge whose lines are valid and which satisfies the membership property is a valid catalogue branch. -/
theorem valid (σ : Support) (a b c : ℤ) (h0 : a + b + c = 0) (depth Q0 Pbad N0 : ℕ) (hQ0 : 3 ≤ Q0)
    (hP : 6 ≤ Pbad) (hok : ∀ L ∈ B.lines, L.ok σ.rho a b c = true) (hm : B.Member σ.rho) :
    KCatValid planeC planeC_pos (planeFrame σ a b c h0) depth (planeBundle σ a b c h0).shifts Q0 Pbad N0
      [B.toBranch] := by
  refine max_bridge_valid σ a b c h0 depth Q0 Pbad N0 hQ0 hP (B.lines.map (fun L => L.toBranch σ.rho)) B.toBranch
    ?_ ?_ ?_ ?_
  · simp only [toBranch, List.map_map]
    rfl
  · intro A hA
    obtain ⟨L, _, rfl⟩ := List.mem_map.1 hA
    rfl
  · intro r p m kv hf hc
    obtain ⟨L, hL, hLc⟩ := hm (rho_pos σ) (rho_le σ) r p m kv hf hc
    exact ⟨L.toBranch σ.rho, List.mem_map.2 ⟨L, hL, rfl⟩, hLc⟩
  · intro A hA
    obtain ⟨L, hL, rfl⟩ := List.mem_map.1 hA
    exact DipLine.line_valid σ a b c h0 depth Q0 Pbad N0 hQ0 hP L (hok L hL)

end DipBridge

end CatalanCore.Uniform.Bank.Plane1.Dips

#print axioms CatalanCore.Uniform.Bank.Plane1.Dips.max_bridge_valid
#print axioms CatalanCore.Uniform.Bank.Plane1.Dips.DipBridge.valid
