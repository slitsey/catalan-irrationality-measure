module

public import CatalanCore.Uniform.Content.BankShared.KTerm.Win
public import CatalanCore.Arith.Hybrid.PieceTools

@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 1600000

/-! # The prefix rule over a pole bundle (wave H1)

`KBundle.pre_gle` is `TwoTerm.pre_gle` for the instance `B.inst r m` of the scale: its diagonal set depends on
`(r, m)`, so the generic lemma (`[∀ r m, I.DiagOK r m]`) does not apply; the body is the same (the tropical bridge,
`D1`, and the counting of the levels).  `KBundle.prefix_valid` is the prefix branch `kbrPre n j0 [j1, j2]` of the
`k`-shift catalogue (Theorem 1 of the prefix rule through `KBundle.pre_gap`), valid for every alternating geometry
`altGeom c`.  The numerical prefix bounds (`PreValid`) are instances of `pre_gle` with the constants of the bank. -/

namespace CatalanCore.Uniform.Content.BankShared.KTerm
open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Content.Shape CatalanCore.Uniform.Content.BankShared
  CatalanCore.Uniform.Content.BankShared.TwoTerm CatalanCore.Uniform.Content.BankShared.TwoTerm.Pre
  CatalanCore.Uniform.Content.BankShared.Check
  CatalanCore.Uniform.Content.SmallPrimes CatalanCore.Arith CatalanCore.Arith.Hybrid CatalanFrames.HybCommon
  CatalanFrames.HybGen CatalanCore.Rect

namespace KBundle

/-- **`pre_gle` over the bundle**: the tropical bridge, `D1`, and the counting of the levels. -/
theorem pre_gle (B : KBundle) (c : ℚ) (hc : 0 < c) (depth : ℕ) (i : ((altGeom c hc).family B.Fr depth).ι)
    (hr : i.1 % 2 = 0) (hr1 : 1 ≤ i.1) (p : ℕ) [hp : Fact p.Prime] (h5 : 5 ≤ p)
    (A C e : ℕ) (α0 : ℝ)
    (hA : 3 * (i.1 + 2 * (altGeom c hc).borderSize i.1) ≤ A * i.1)
    (he : 3 * (i.1 + 2 * (altGeom c hc).borderSize i.1) ≤ i.1 * 2 ^ e)
    (hC1 : 2 * (i.1 + (altGeom c hc).borderSize i.1) * e ≤ C * i.1)
    (hC2 : 2 * (i.1 + (altGeom c hc).borderSize i.1) ≤ C * i.1)
    (h0 : 2 * ((i.1 : ℝ) + (altGeom c hc).borderSize i.1) ≤ α0 * i.1 + 1) (hpr : p ≤ i.1) :
    ∃ n : ℕ, GLE p n (((altGeom c hc).family B.Fr depth).Q i) ∧
      (n : ℝ) ≤ α0 * i.1 + (SmallBudget.add (SmallBudget.sqrtLog A C) SmallBudget.unit).X i.1 p := by
  have hG0 := B.gle_tropExp c hc depth i hr p
  set r := i.1 with hrdef
  set m := (altGeom c hc).borderSize r with hmdef
  have hG : GLE p (tropExp (B.inst r m) r m p) (((altGeom c hc).family B.Fr depth).Q i) := hG0
  refine ⟨_, hG, ?_⟩
  have hL : (B.inst r m).cd.L = 3 := (B.badInfo r m).L_eq
  have hnb : p ∉ (B.inst r m).cd.bad := by
    intro hb
    have := (B.badInfo r m).bad_le p hb
    omega
  have hX : (SmallBudget.add (SmallBudget.sqrtLog A C) SmallBudget.unit).X r p =
      (SmallBudget.sqrtLog A C).X r p + 1 := by
    show (SmallBudget.sqrtLog A C).X r p + SmallBudget.unit.X r p = _
    congr 1
    simp [SmallBudget.unit, SmallBudget.ofCutoff, hpr]
  have hX0 := (SmallBudget.sqrtLog A C).nonneg r p
  have hle := tropExp_le_good (B.inst r m) r m p hr1 hp.out hnb
  have hD1 : XGm (B.inst r m) r m p ≤ 2 * (r + m) := XGm_D1 _ _ _ _
  have hXG : (tropVal (HW (B.inst r m).lev p r m) : ℝ) ≤ 2 * ((r : ℝ) + m) := by
    have : tropVal (HW (B.inst r m).lev p r m) ≤ 2 * (r + m) := hD1
    exact_mod_cast this
  rw [hX]
  by_cases hsq : p * p ≤ A * r
  · rw [SmallBudget.sqrtLog_X_of A C r p hsq]
    have hcnt := cntG_le (B.inst r m) r m p hp.out
    rw [hL] at hcnt
    have hlog : Nat.log 2 (3 * (r + 2 * m)) ≤ Nat.log 2 r + e := by
      rw [← log2_mul_pow r e (by omega)]
      exact Nat.log_mono_right he
    have hcn : 2 * (r + m) * cntG (B.inst r m) r m p ≤ C * r * (Nat.log 2 r + 1) := by
      have h1 : 2 * (r + m) * cntG (B.inst r m) r m p ≤ 2 * (r + m) * (Nat.log 2 r + e) :=
        Nat.mul_le_mul_left _ (hcnt.trans hlog)
      have h2 : 2 * (r + m) * Nat.log 2 r ≤ C * r * Nat.log 2 r := Nat.mul_le_mul_right _ hC2
      calc 2 * (r + m) * cntG (B.inst r m) r m p ≤ 2 * (r + m) * (Nat.log 2 r + e) := h1
        _ = 2 * (r + m) * Nat.log 2 r + 2 * (r + m) * e := by ring
        _ ≤ C * r * Nat.log 2 r + C * r := Nat.add_le_add h2 hC1
        _ = C * r * (Nat.log 2 r + 1) := by ring
    have hcn' : ((2 * (r + m) * cntG (B.inst r m) r m p : ℕ) : ℝ) ≤ (C : ℝ) * r * ((Nat.log 2 r : ℝ) + 1) := by
      have h := (Nat.cast_le (α := ℝ)).2 hcn
      have e : ((C * r * (Nat.log 2 r + 1) : ℕ) : ℝ) = (C : ℝ) * r * ((Nat.log 2 r : ℝ) + 1) := by
        push_cast; ring
      rw [e] at h
      exact h
    linarith
  · push Not at hsq
    have hz : cntG (B.inst r m) r m p = 0 := by
      apply cntG_zero _ _ _ _ hp.out
      rw [hL, pow_two]
      omega
    rw [hz] at hle
    simp only [mul_zero, Nat.cast_zero, zero_add] at hle
    linarith

/-- **The prefix branch over the bundle** (Theorem 1 of the prefix rule), for any alternating geometry. -/
theorem prefix_valid (B : KBundle) (c : ℚ) (hc : 0 < c) (depth Q0 Pbad N0 n j0 j1 j2 : ℕ)
    (hQ0 : 3 ≤ Q0) (hP : 6 ≤ Pbad) :
    KCatValid c hc B.Fr depth B.shifts Q0 Pbad N0 [kbrPre n j0 [j1, j2]] := by
  intro b hb i hi hr0 p _ hPb _ hqN kv hroots hcond
  simp only [List.mem_singleton] at hb
  subst hb
  have hr := hi.2
  have h7 : 7 ≤ p := by omega
  set r := i.1 with hrdef
  set m := (altGeom c hc).borderSize r with hmdef
  have hp2 := odd_of_ge_seven (Fact.out : p.Prime) h7
  obtain ⟨⟨jA, eA, -, -, -, hkAp⟩, ⟨jB, eB, -, -, -, hkBp⟩⟩ := B.roots_facts hroots
  have hsq : 3 * (r + 2 * m) < p * p :=
    lt_of_le_of_lt (Nat.mul_le_mul_right _ hQ0) hqN
  have hG : GLE p (tropVal (HW (B.inst r m).lev p r m)) ((AltEven c hc B.Fr depth).Q i) :=
    B.gle_trop c hc depth i hr hr0 p (by omega) hsq
  have hlo := kMx_ge r p m kv (.vr :: .add .ap (.smul j0 .vp) :: kPoleLos 0 [j1, j2]) (.tsub (kNn n) .vp)
  have hhi := kMn_le r p m kv (.add .vr .vp :: .add .ap (.smul (j0 + 1) .vp) :: kPoleHis 0 [j1, j2]) (kNn n)
  obtain ⟨hlo1, hlo2⟩ := hlo
  obtain ⟨hhi1, hhi2⟩ := hhi
  have hev : (kbrPre n j0 [j1, j2]).τ.evalN r p m kv =
      2 * r + (2 * m - ((kPreHi n j0 [j1, j2]).evalN r p m kv - (kPreLo n j0 [j1, j2]).evalN r p m kv)) := rfl
  have hd0 : (kbrPre n j0 [j1, j2]).debit = 0 := rfl
  generalize haa : (kPreLo n j0 [j1, j2]).evalN r p m kv = aa at hev
  generalize hbb : (kPreHi n j0 [j1, j2]).evalN r p m kv = bb at hev
  have hlN : r + 2 * (m - n * p) - p ≤ aa := by rw [← haa]; exact hlo1
  have hlr : r ≤ aa := by rw [← haa]; exact hlo2 .vr (by simp)
  have hl0 : p * (r / p) + j0 * p ≤ aa := by
    rw [← haa]; exact hlo2 (.add .ap (.smul j0 .vp)) (by simp)
  have hl1 : j1 ≠ 0 → p * (r / p) + (kv 0 + (j1 - 1) * p) ≤ aa := fun h => by
    rw [← haa]; exact hlo2 (.add .ap (.add (.vk 0) (.smul (j1 - 1) .vp))) (by simp [kPoleLos, h])
  have hl2 : j2 ≠ 0 → p * (r / p) + (kv 1 + (j2 - 1) * p) ≤ aa := fun h => by
    rw [← haa]; exact hlo2 (.add .ap (.add (.vk 1) (.smul (j2 - 1) .vp))) (by simp [kPoleLos, h])
  have hhN : bb ≤ r + 2 * (m - n * p) := by rw [← hbb]; exact hhi1
  have hhp : bb ≤ r + p := by rw [← hbb]; exact hhi2 (.add .vr .vp) (by simp)
  have hh0 : bb ≤ p * (r / p) + (j0 + 1) * p := by
    rw [← hbb]; exact hhi2 (.add .ap (.smul (j0 + 1) .vp)) (by simp)
  have hh1 : bb ≤ p * (r / p) + (kv 0 + j1 * p) := by
    rw [← hbb]; exact hhi2 (.add .ap (.add (.vk 0) (.smul j1 .vp))) (by simp [kPoleHis])
  have hh2 : bb ≤ p * (r / p) + (kv 1 + j2 * p) := by
    rw [← hbb]; exact hhi2 (.add .ap (.add (.vk 1) (.smul j2 .vp))) (by simp [kPoleHis])
  by_cases hab : aa < bb
  swap
  · refine ⟨_, hG.mono (XGm_D1 _ _ _ _), ?_⟩
    rw [hev, hd0]
    simp only [zero_mul, add_zero]
    omega
  have hnp : n * p ≤ m := by
    by_contra h
    have : m - n * p = 0 := by omega
    omega
  have hApr : p * (r / p) ≤ r := Nat.mul_div_le r p
  have hW : Win p r m n (m - n * p) aa bb := ⟨by omega, hp2, hlr, hab.le, hhp, hhN, by omega⟩
  have hgap := B.cutfree (A' := r / p) (n0 := j0 + 1) (n1 := j1) (n2 := j2) (a := aa) (b := bb)
    (Fact.out : p.Prime) (by omega) (by omega) ⟨jA, eA⟩ hkAp ⟨jB, eB⟩ hkBp
    (fun _ => by simpa using hl0) (by simpa using hh0)
    (fun h => by have := hl1 (by omega); omega) (by omega)
    (fun h => by have := hl2 (by omega); omega) (by omega)
  have hgp : GLE p (2 * r + 2 * m - (bb - aa)) ((AltEven c hc B.Fr depth).Q i) :=
    B.pre_gap c hc depth i hi.1 hr p (by omega) hsq n aa bb hW hgap
  refine ⟨_, hgp, ?_⟩
  rw [hev, hd0]
  simp only [zero_mul, add_zero]
  omega


end KBundle

end CatalanCore.Uniform.Content.BankShared.KTerm
