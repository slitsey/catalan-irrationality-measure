module

public import CatalanCore.Uniform.Bank.Plane2.Content.RowsP
public import CatalanCore.Uniform.Support.Producer
public import CatalanCore.Uniform.Content.BankShared.BudgetAdd
public import CatalanCore.Uniform.Content.BankShared.Check.Content

@[expose] public section
set_option Elab.async false

open Polynomial Finset Matrix CatalanCore.Basic CatalanCore.Arith.Hybrid

/-!
# Plane 2 content: the tail, `AltQ` and the small-prime prefix (lane H, wave P210-B; ledger P210)

* `real_Tail`: the branch `p > 2N` (price `0`) from the row `P₇`;
* `p2_altQ`: `AltQ (6/41) (fS v u, eS v u)` with `c_F = 18` (the entry constant `3 Dc`, `Dc = 6` for the datum of
  `plane2`, `Dc = 3` for the one-term datum of `u = 0`), for every `v ≠ 0` and every `u`;
* `p2Budget L C = sqrtLog L C + 2 · unit`: the small-prime budget of the prefix.  The absolute slack `3/2` of
  `3 (r + m) ≤ (3 + 3α) r + 3/2` is paid by the two units (`X r p ≥ 2` on `p ≤ r`); it cannot go into `α₀'`;
* `p2_preValid`: `PreValidFam` at `α₀' ≥ 132/41 = 3 + 3α`, every `t₀ ≤ 1`, every modulus `M`, with
  budget `p2Budget 16 C`, `C ≥ 66 = 30 + 2 c_F`.  The primes `p² ≤ 16 r` are cleared by the crude exponent
  (`AltQ`) against the `sqrtLog` part; the others by the row `B₁` (`Sweep.row_B1u`, `3 (r + m) ∸ ‖m‖_p`), which holds
  for every `(v, u)` and every prime `p ≥ 5` with `2 (r + 2m) < p²`, in particular also at the primes dividing `v`.
-/

namespace CatalanCore.Uniform.Bank.Plane2.Content

open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Support CatalanCore.Uniform.Content.Sweep
  CatalanCore.Uniform.Content.Shape CatalanCore.Uniform.Content.Wire
  CatalanCore.Uniform.Content.BankShared CatalanCore.Uniform.Content.BankShared.Check
  CatalanCore.Uniform.Content.BankShared.KTerm KExpr CatalanCore.Uniform.Content.BankShared.TwoTerm
  CatalanCore.Uniform.Content.SmallPrimes

/-! ### The tail -/

/-- **`Real` for the tail `p > 2N`** (price `0`), from the row `P₇` (`p ≥ 2r`, `(p-1)/2 ≥ N`). -/
theorem real_Tail (v u : ℤ) : Real v u brTail := by
  intro r p _ S kv hr hr0 hPb hN0 hN hk hcond
  have hp5 := p2_hp5 hPb
  have hm := p2_two_m_le hr hr0
  have hc1 := holds_s (hcond ⟨-2, 1, -4, [], 0, true⟩ (by simp [brTail]))
  refine ⟨r + 2 * p2G.borderSize r - (p - 1) / 2, ?_, ?_⟩
  · exact p2_rowP_setup v u r p S hr _ (rowP7_all v u _ (p2Q_inj r S) (p2Q_lt r hr S) hN hm hp5
      (by simp at hc1; omega))
  · simp only [brTail, KExpr.evalN]
    simp at hc1
    omega

/-! ### `AltQ` -/

/-- The one-term datum of `u = 0`: `S = {1}`, `a = 0`, `b = v`. -/
@[reducible] def p2z (v : ℤ) (hv : v ≠ 0) : Datum where
  n := 1
  hn := by norm_num
  s := ![1]
  a := ![0]
  b := ![v]
  hs := by intro i; fin_cases i; norm_num
  hinj := by intro i j _; exact Subsingleton.elim i j
  hab := by intro i; fin_cases i; exact Or.inr (by simpa using hv)
  hbal := by simp

theorem p2z_f (v : ℤ) (hv : v ≠ 0) : (p2z v hv).f = fS v 0 := by
  funext t
  unfold Datum.f fS
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [Datum.delta, CatalanCore.Uniform.Content.Sweep.T1, CatalanCore.Uniform.Content.Sweep.T2]

theorem p2z_e (v : ℤ) (hv : v ≠ 0) : (p2z v hv).e = eS v 0 := by
  funext t
  unfold Datum.e eS
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [Datum.delta1, CatalanCore.Uniform.Content.Sweep.U1, CatalanCore.Uniform.Content.Sweep.U2]

theorem p2z_Dc (v : ℤ) (hv : v ≠ 0) : (p2z v hv).Dc = 3 := by
  unfold Datum.Dc
  simp [Dm, p2z]

theorem plane2_Dc (v u : ℤ) (hv : v ≠ 0) (hu : u ≠ 0) : (Datum.plane2 v u hv hu).Dc = 6 := by
  unfold Datum.Dc
  simp [Fin.sum_univ_two, Dm, Datum.plane2]
  decide

/-- **`AltQ` of the plane 2 family** (`c_F = 18`), for every `v ≠ 0` and every `u`. -/
theorem p2_altQ (v u : ℤ) (hv : v ≠ 0) :
    AltQ (6 / 41) plane2_pos 18 (SeqFamily.poly (fS v u) (eS v u) p2G.geometry) := by
  by_cases hu : u = 0
  · subst hu
    have h := datum_altQ (p2z v hv) (6 / 41) plane2_pos (by norm_num)
    rw [p2z_f, p2z_e, p2z_Dc] at h
    exact h.mono (by norm_num)
  · have h := datum_altQ (Datum.plane2 v u hv hu) (6 / 41) plane2_pos (by norm_num)
    rw [plane2_f v u hv hu, plane2_e v u hv hu, plane2_Dc v u hv hu] at h
    exact h.mono (by norm_num)

/-! ### The small-prime prefix -/

/-- The small-prime budget: `sqrtLog L C` plus two units on `p ≤ r`. -/
noncomputable def p2Budget (L C : ℕ) : SmallBudget :=
  SmallBudget.add (SmallBudget.sqrtLog L C) (SmallBudget.add SmallBudget.unit SmallBudget.unit)

theorem p2Budget_X (L C r p : ℕ) :
    (p2Budget L C).X r p = (SmallBudget.sqrtLog L C).X r p + (SmallBudget.unit.X r p + SmallBudget.unit.X r p) :=
  rfl

theorem unit_X_of (r p : ℕ) (h : p ≤ r) : SmallBudget.unit.X r p = 1 := by
  simp [SmallBudget.unit, SmallBudget.ofCutoff, h]

/-- **`PreValidFam` of the plane 2 family** at `α₀' ≥ 132/41`, every `t₀ ≤ 1`, every modulus `M`, with the
budget `sqrtLog 16 C + 2 · unit` (`C ≥ 66`). -/
theorem p2_preValid (v u : ℤ) (hv : v ≠ 0) (const : ℝ) (depth M C : ℕ) (hC : 66 ≤ C) (t0 α0b : ℚ)
    (ht0 : t0 ≤ 1) (hα : (132 / 41 : ℚ) ≤ α0b) :
    PreValidFam (6 / 41) plane2_pos const depth (SeqFamily.poly (fS v u) (eS v u) p2G.geometry) M
      (p2Budget 16 C) t0 α0b := by
  intro i hi p _ _ hpt
  obtain ⟨r, S⟩ := i
  have hr : r % 2 = 0 := hi.2
  have hQ := p2_altQ v u hv
  have hpr : p ≤ r := by
    refine hpt.trans ?_
    have h0 : (0 : ℝ) ≤ r := Nat.cast_nonneg _
    have : (t0 : ℝ) * r ≤ r := by
      have : (t0 : ℝ) ≤ 1 := by exact_mod_cast ht0
      nlinarith
    exact Nat.floor_le_of_le this
  have hp2 := (Fact.out : p.Prime).two_le
  have hr1 : 1 ≤ r := by omega
  have hα0 : (0 : ℝ) ≤ (α0b : ℝ) := by
    have : (0 : ℚ) ≤ α0b := by linarith [(by norm_num : (0 : ℚ) ≤ 132 / 41)]
    exact_mod_cast this
  have hr0R : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  have hXu : (0 : ℝ) ≤ SmallBudget.unit.X r p := SmallBudget.unit.nonneg r p
  have hXs := (SmallBudget.sqrtLog 16 C).nonneg r p
  by_cases hsq : p * p ≤ 16 * r
  · refine ⟨Ecrude 18 r p, hQ.crude ⟨r, S⟩ hr p, ?_⟩
    have h1 := Ecrude_le_budget 18 C r p (by omega) hr1 hp2
    have h2 : (Ecrude 18 r p : ℝ) ≤ (C : ℝ) * r * ((Nat.log 2 r : ℝ) + 1) := by
      exact_mod_cast (by simpa [mul_assoc] using h1 : Ecrude 18 r p ≤ C * r * (Nat.log 2 r + 1))
    have h3 := SmallBudget.sqrtLog_X_of 16 C r p hsq
    show (Ecrude 18 r p : ℝ) ≤ (α0b : ℝ) * r + (p2Budget 16 C).X r p
    rw [p2Budget_X]
    have h4 : (0 : ℝ) ≤ (α0b : ℝ) * r := mul_nonneg hα0 hr0R
    linarith
  · push Not at hsq
    have hp5 : 5 ≤ p := by
      by_contra hc
      push Not at hc
      have : p * p ≤ 16 := by nlinarith
      omega
    have hm := p2_two_m_le hr (by omega)
    obtain ⟨hb1, hb2⟩ := p2_border hr
    have hN : 2 * (r + 2 * p2G.borderSize r) < p * p := by omega
    refine ⟨3 * (r + p2G.borderSize r) - min (p2G.borderSize r % p) (p - p2G.borderSize r % p), ?_, ?_⟩
    · have e := p2Q_eq_m v u r hr S (p2_k_eq r)
      show GLE p _ (p2Q v u r S)
      rw [e]
      exact row_B1u v u _ (p2Q_inj r S) (p2Q_lt r hr S) hN hp5
    · have hn : 41 * (3 * (r + p2G.borderSize r) - min (p2G.borderSize r % p) (p - p2G.borderSize r % p)) ≤
          132 * r + 60 := by omega
      have hnR : (41 : ℝ) * ((3 * (r + p2G.borderSize r) - min (p2G.borderSize r % p)
          (p - p2G.borderSize r % p) : ℕ) : ℝ) ≤ 132 * r + 60 := by exact_mod_cast hn
      show ((3 * (r + p2G.borderSize r) - min (p2G.borderSize r % p) (p - p2G.borderSize r % p) : ℕ) : ℝ) ≤
        (α0b : ℝ) * r + (p2Budget 16 C).X r p
      rw [p2Budget_X, unit_X_of r p hpr]
      have hαR : (132 / 41 : ℝ) ≤ (α0b : ℝ) := by
        have : (((132 / 41 : ℚ)) : ℝ) ≤ (α0b : ℝ) := by exact_mod_cast hα
        simpa using this
      have h5 : (132 / 41 : ℝ) * r ≤ (α0b : ℝ) * r := mul_le_mul_of_nonneg_right hαR hr0R
      linarith

/-! ### The head catalogue -/

/-- **Every branch of the head catalogue is realised** (`headList`: `P₄ .. P₇`, the tail, `E₁ W`, `E₂ W`). -/
theorem real_headList (v u : ℤ) (hv : v ≠ 0) : ∀ b ∈ headList, Real v u b := by
  intro b hb
  simp only [headList, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map] at hb
  rcases hb with ((rfl | rfl | rfl | rfl | rfl) | ⟨W, hW, rfl⟩) | ⟨W, hW, rfl⟩
  · exact real_P4 v u
  · exact real_P5 v u
  · exact real_P6 v u
  · exact real_P7 v u
  · exact real_Tail v u
  · exact real_E1 v u hv hW
  · exact real_E2 v u hv hW

theorem headList_debit : ∀ b ∈ headList, b.debit = 0 := by
  intro b hb
  simp only [headList, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map] at hb
  rcases hb with ((rfl | rfl | rfl | rfl | rfl) | ⟨W, hW, rfl⟩) | ⟨W, hW, rfl⟩ <;> rfl

end CatalanCore.Uniform.Bank.Plane2.Content

#print axioms CatalanCore.Uniform.Bank.Plane2.Content.real_headList
#print axioms CatalanCore.Uniform.Bank.Plane2.Content.real_Tail
#print axioms CatalanCore.Uniform.Bank.Plane2.Content.p2_altQ
#print axioms CatalanCore.Uniform.Bank.Plane2.Content.p2_preValid
