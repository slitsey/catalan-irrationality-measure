module

public import CatalanCore.Uniform.Bank.Plane2.Content.Union
public import CatalanCore.Uniform.Bank.Plane2.Content.RowsBand
public import CatalanCore.Uniform.Content.BankShared.KTerm.Periodic

@[expose] public section
set_option Elab.async false

open Polynomial Finset Matrix CatalanCore.Basic CatalanCore.Arith.Hybrid

/-!
# Plane 2 content: the translation of the band rows along the lattice shift (lane H, wave P210-L; ledger P210)

The instance of `KTerm.Transl` for plane 2 (`b = 41`, `a = 3`, `K_c = 132`, ambient range `r ≤ 400 p`) on the base catalogue
`bandList 0 6` (plain row and bands `1 .. 6`): `p2rho n` is the pullback of the conditions by the lattice shift of order `n`
(the guard `400 p ≥ r` is kept: it is supplied by the range of the strip).  (T1) is `brBand_cov`/`brPlain_cov` iterated;
(T2): the translate of the band `k` is the band `k + 6 n`, the translate of the plain row is implied by the plain row
(`2m ≥ (6n+1) p` implies `2m ≥ p`).
-/

namespace CatalanCore.Uniform.Bank.Plane2.Content

open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Support CatalanCore.Uniform.Content.Sweep
  CatalanCore.Uniform.Content.Shape CatalanCore.Uniform.Content.Wire
  CatalanCore.Uniform.Content.BankShared CatalanCore.Uniform.Content.BankShared.Check
  CatalanCore.Uniform.Content.BankShared.KTerm KExpr

theorem s_holds {r p m : ℕ} {kv : ℕ → ℕ} {cr cp cm c1 : ℤ} (h : 0 < cr * r + cp * p + cm * m + c1) :
    KCond.Holds ⟨cr, cp, cm, [], c1, true⟩ r p m kv := by
  simpa [KCond.Holds, KCond.L, dot] using h

/-- The members of the base catalogue. -/
theorem mem_base {br : KBranch} (h : br ∈ bandList 0 6) :
    br = brPlain ∨ ∃ k W, 1 ≤ k ∧ k ≤ 6 ∧ W ∈ vecs ∧ br = brBand k W k := by
  simp only [bandList, List.mem_cons, List.mem_flatMap, List.mem_range, List.mem_map] at h
  rcases h with rfl | ⟨i, hi, W, hW, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨0 + 1 + i, W, by omega, by omega, hW, rfl⟩

/-- The translation of a branch: conditions pulled back by the lattice shift of order `n`, except the guard. -/
def p2rho (n : ℕ) (br : KBranch) : KBranch :=
  ⟨br.τ, br.conds.map (fun cd => if cd.cr = 0 then cd.shift 41 3 n else cd), br.debit⟩

/-- **(T1) iterated**: `n` periods add `132 n p`. -/
theorem cov_n {br : KBranch} (h : br ∈ bandList 0 6) (n r p m : ℕ) (kv : ℕ → ℕ) :
    br.τ.evalN (r + n * 41 * p) p (m + n * 3 * p) kv = br.τ.evalN r p m kv + n * 132 * p := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e1 : r + (n + 1) * 41 * p = (r + n * 41 * p) + 41 * p := by ring
    have e2 : m + (n + 1) * 3 * p = (m + n * 3 * p) + 3 * p := by ring
    rw [e1, e2]
    rcases mem_base h with rfl | ⟨k, W, -, -, -, rfl⟩
    · rw [brPlain_cov, ih]; ring
    · rw [brBand_cov, ih]; ring

theorem guard_of_cr {br : KBranch} (h : br ∈ bandList 0 6) {cd : KCond} (hcd : cd ∈ br.conds) (h0 : ¬ cd.cr = 0) :
    cd = gGuard := by
  rcases mem_base h with rfl | ⟨k, W, -, -, -, rfl⟩
  · simp only [brPlain, List.mem_cons, List.not_mem_nil, or_false] at hcd
    rcases hcd with rfl | rfl
    · exact absurd rfl h0
    · rfl
  · simp only [brBand, List.mem_cons, List.not_mem_nil, or_false] at hcd
    rcases hcd with rfl | rfl | rfl
    · exact absurd rfl h0
    · exact absurd rfl h0
    · rfl

/-- **The translation of the plane 2 base catalogue.** -/
def p2Tr : Transl 41 3 132 400 (bandList 0 6) where
  ρ := p2rho
  debit _ _ := rfl
  price n br hbr r p m kv := cov_n hbr n r p m kv
  cond n br hbr r p m kv hΩ hc cd hcd := by
    simp only [p2rho, List.mem_map] at hcd
    obtain ⟨cd', hcd', rfl⟩ := hcd
    by_cases h0 : cd'.cr = 0
    · rw [if_pos h0]
      exact (KCond.holds_shift 41 3 n cd' r p m kv).2 (hc cd' hcd')
    · rw [if_neg h0]
      have hg := guard_of_cr hbr hcd' h0
      subst hg
      have h2 : ((r + n * 41 * p : ℕ) : ℤ) ≤ 400 * (p : ℤ) := by exact_mod_cast hΩ
      exact ns_holds (cr := -1) (cp := 400) (cm := 0) (c1 := 0) (by linarith)

theorem p2rho_mem {n : ℕ} {br : KBranch} {cd : KCond} (hcd : cd ∈ br.conds) (h0 : cd.cr = 0) :
    cd.shift 41 3 n ∈ (p2rho n br).conds :=
  List.mem_map.2 ⟨cd, hcd, by simp [h0]⟩

theorem p2rho_guard {n : ℕ} {br : KBranch} (hcd : gGuard ∈ br.conds) : gGuard ∈ (p2rho n br).conds :=
  List.mem_map.2 ⟨gGuard, hcd, by simp [gGuard]⟩

/-- **(T2)**: the translates of the base catalogue are realised on the family. -/
theorem real_rho (v u : ℤ) (hv : v ≠ 0) (n : ℕ) {br : KBranch} (hbr : br ∈ bandList 0 6) :
    Real v u (p2rho n br) := by
  rcases mem_base hbr with rfl | ⟨k, W, hk1, hk6, hW, rfl⟩
  · intro r p inst S kv hr hr0 hPb hN hqN hk hc
    refine real_brPlain v u hv r p S kv hr hr0 hPb hN hqN hk ?_
    intro cd hcd
    simp only [brPlain, List.mem_cons, List.not_mem_nil, or_false] at hcd
    rcases hcd with rfl | rfl
    · have h1 := holds_ns (hc _ (p2rho_mem (n := n) (br := brPlain) (cd := ⟨0, -1, 2, [], 0, false⟩)
        (by simp [brPlain]) rfl))
      simp only [KCond.shift] at h1
      have h3 : (0 : ℤ) ≤ (n : ℤ) * 6 * p := by positivity
      refine ns_holds ?_
      push_cast at h1 ⊢
      nlinarith [h1, h3]
    · exact hc gGuard (p2rho_guard (n := n) (br := brPlain) (by simp [brPlain]))
  · intro r p inst S kv hr hr0 hPb hN hqN hk hc
    have hmem1 := hc _ (p2rho_mem (n := n) (br := brBand k W k) (cd := ⟨0, -(k : ℤ), 2, [], 0, false⟩)
      (by simp [brBand]) rfl)
    have hmem2 := hc _ (p2rho_mem (n := n) (br := brBand k W k) (cd := ⟨0, (k : ℤ) + 1, -2, [], 0, true⟩)
      (by simp [brBand]) rfl)
    have hg := hc gGuard (p2rho_guard (n := n) (br := brBand k W k) (by simp [brBand]))
    have h1 := holds_ns hmem1
    have h2 := holds_s hmem2
    simp only [KCond.shift] at h1 h2
    refine real_brBand v u hv k hW (k + 6 * n) (by omega) (by omega) r p S kv hr hr0 hPb hN hqN hk ?_
    intro cd hcd
    simp only [brBand, List.mem_cons, List.not_mem_nil, or_false] at hcd
    rcases hcd with rfl | rfl | rfl
    · refine ns_holds ?_
      push_cast at h1 ⊢
      nlinarith [h1]
    · refine s_holds ?_
      push_cast at h2 ⊢
      nlinarith [h2]
    · exact hg

theorem real_kb (v u : ℤ) (hv : v ≠ 0) : ∀ b ∈ bandList 0 6, Real v u b := by
  intro b hb
  rcases mem_base hb with rfl | ⟨k, W, hk1, -, hW, rfl⟩
  · exact real_brPlain v u hv
  · exact real_brBand v u hv k hW k hk1 rfl

/-- The full catalogue of the bank (head, union row, base) is realised. -/
theorem real_kcat (v u : ℤ) (hv : v ≠ 0) : ∀ b ∈ headList ++ brU56 :: bandList 0 6, Real v u b := by
  intro b hb
  simp only [List.mem_append, List.mem_cons] at hb
  rcases hb with hb | rfl | hb
  · exact real_headList v u hv b hb
  · exact real_U56 v u
  · exact real_kb v u hv b hb

theorem kcat_debit : ∀ b ∈ headList ++ brU56 :: bandList 0 6, b.debit = 0 := by
  intro b hb
  simp only [List.mem_append, List.mem_cons] at hb
  rcases hb with hb | rfl | hb
  · exact headList_debit b hb
  · rfl
  · rcases mem_base hb with rfl | ⟨k, W, -, -, -, rfl⟩ <;> rfl

theorem rho_debit (n : ℕ) : ∀ b ∈ (bandList 0 6).map (p2rho n), b.debit = 0 := by
  intro b hb
  obtain ⟨b', hb', rfl⟩ := List.mem_map.1 hb
  rcases mem_base hb' with rfl | ⟨k, W, -, -, -, rfl⟩ <;> rfl

end CatalanCore.Uniform.Bank.Plane2.Content
#print axioms CatalanCore.Uniform.Bank.Plane2.Content.real_rho
#print axioms CatalanCore.Uniform.Bank.Plane2.Content.real_kcat
#print axioms CatalanCore.Uniform.Bank.Plane2.Content.p2Tr
