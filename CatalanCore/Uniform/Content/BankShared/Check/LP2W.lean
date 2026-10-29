import CatalanCore.Uniform.Content.BankShared.Check.UF
import CatalanCore.Uniform.Content.BankShared.Check.Rank
import CatalanCore.Uniform.Content.BankShared.TwoTerm.LP2W
set_option Elab.async false

/-! # The widened LP2 branch `brLP2w` (paper `lp2-strip-2026-10-29`)

`brLP2w` is `brLP2` with the condition `N ≤ p + k` (`cNlepk`) replaced by `N ≤ 2p` (`cNle2p`): same expression
`tLP2`, same debit 1.  Its soundness is `lp2w_gle_tt`.  A bank opts in by writing `brLP2w` in place of `brLP2` in
its catalogue (same index) and citing `catValid_bankW` / `catValid_bankUFw` in place of `catValid_bank` /
`catValid_bankUF`. -/

namespace CatalanCore.Uniform.Content.BankShared.Check
open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Content.Shape CatalanCore.Uniform.Content.BankShared
  CatalanCore.Uniform.Content.Member CatalanCore.Uniform.Content.RankProducer
  CatalanCore.Uniform.Content.UFSimple CatalanCore.Uniform.Content.Smith CatalanCore.Basic CatalanCore.Arith
  CatalanCore.Arith.Hybrid TwoTerm Cat

/-- The widened LP2 branch: `r < p`, `k ≤ r`, `N ≤ 2p`, `p < r + m`; price `tLP2`, debit 1. -/
def brLP2w : Branch := ⟨tLP2, [cRltp, cKler, cNle2p, cPltrm], 1⟩

theorem catValid_LP2w (c : ℚ) (hc : 0 < c) {Fr : Frame} {q o : ℕ} (T : TwoTermData Fr q o) {nm : ℕ}
    (hnorm : Fr.norm = (nm : ℚ)) (depth Pbad N0 : ℕ)
    (hP : ∀ p : ℕ, p.Prime → Pbad < p → ¬ p ∣ nm ∧ 5 ≤ p ∧ 2 * q ≤ p) :
    CatValid c hc Fr depth q o Pbad N0 [brLP2w] := by
  intro b hb i hi hr0 p _ hPb _ hqN j k hk hj0 hjq hk0 hkp hcond
  obtain ⟨hpn, hp5, hpq⟩ := hP p Fact.out hPb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  subst hb
  have h1 := holds_Rltp (hcond cRltp (by simp [brLP2w]))
  have h2 := holds_Kler (hcond cKler (by simp [brLP2w]))
  have h3 := holds_Nle2p (hcond cNle2p (by simp [brLP2w]))
  have h4 := holds_Pltrm (hcond cPltrm (by simp [brLP2w]))
  have hg := lp2w_gle_tt c hc T hnorm depth i hi.1 hi.2 p k j hpn hp5 hpq hk hk0 hkp hj0 h3 h1 h2 h4
  exact ⟨_, hg, by simp only [brLP2w, one_mul]; exact le_refl _⟩

/-- `catValid_twoTerm` with `brLP2w` in place of `brLP2`. -/
theorem catValid_twoTermW {Fr : Frame} (I : HybInst Fr) [∀ r m, I.DiagOK r m] {Lc : ℕ}
    (hL : I.cd.L = Lc) {Gd : ℕ → Prop}
    (Lv : CatalanFrames.HybCommon.LevelFacts I Gd (fun q c => c < I.cd.kq q))
    (c : ℚ) (hc : 0 < c) (hc1 : c ≤ 1) {q o : ℕ} (T : TwoTermData Fr q o) {nm : ℕ}
    (hnorm : Fr.norm = (nm : ℚ)) (depth Pbad N0 : ℕ) (hq : 0 < q) (hLq : Lc ≤ q)
    (hP : ∀ p : ℕ, p.Prime → Pbad < p →
      ¬ p ∣ nm ∧ 5 ≤ p ∧ 2 * q ≤ p ∧ p ∉ I.cd.bad ∧ Gd p ∧ p ≠ 2)
    (hkq : ∀ p : ℕ, p.Prime → Pbad < p → ∀ j k : ℕ, q * k = j * p + o → 0 < j → j < q → 0 < k →
      k < p → I.cd.kq p = k)
    (hrank : CatValid c hc Fr depth q o Pbad N0 [brRank]) (wins : List (ℕ × ℕ)) :
    CatValid c hc Fr depth q o Pbad N0
      (tableT ++ ([brLP1, brLP2w, brRank] ++ wins.map (fun w => brWin w.1 w.2))) := by
  refine catValid_append (catValid_tableT I hL Lv c hc hc1 depth q o Pbad N0 hLq
    (fun p hp h => ⟨(hP p hp h).2.2.2.1, (hP p hp h).2.2.2.2.1, (hP p hp h).2.2.2.2.2⟩) hkq) ?_
  have hP3 : ∀ p : ℕ, p.Prime → Pbad < p → ¬ p ∣ nm ∧ 5 ≤ p ∧ 2 * q ≤ p :=
    fun p hp h => ⟨(hP p hp h).1, (hP p hp h).2.1, (hP p hp h).2.2.1⟩
  have hLP := catValid_LP c hc T hnorm depth Pbad N0 hP3
  have hLPw := catValid_LP2w c hc T hnorm depth Pbad N0 hP3
  have hW : CatValid c hc Fr depth q o Pbad N0 (wins.map (fun w => brWin w.1 w.2)) := by
    intro b hb
    obtain ⟨w, -, rfl⟩ := List.mem_map.1 hb
    exact catValid_win c hc T hnorm depth Pbad N0 hq
      (fun p hp h => ⟨(hP p hp h).1, by have := (hP p hp h).2.2.1; omega⟩) w.1 w.2 _ (by simp)
  intro b hb
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with (rfl | rfl | rfl) | hb
  · exact hLP _ (by simp)
  · exact hLPw _ (by simp)
  · exact hrank _ (by simp)
  · exact hW b hb

/-- **`catValid_bank` with the widened LP2 branch**: catalogue `tableT ++ [LP1, LP2w, R] ++ windows`. -/
theorem catValid_bankW {Fr : Frame} (I : HybInst Fr) [∀ r m, I.DiagOK r m] {Lc : ℕ}
    (hL : I.cd.L = Lc) {Gd : ℕ → Prop}
    (Lv : CatalanFrames.HybCommon.LevelFacts I Gd (fun q c => c < I.cd.kq q))
    (c : ℚ) (hc : 0 < c) (hc1 : c ≤ 1) {q o : ℕ} (T : TwoTermData Fr q o) {nm : ℕ}
    (hnorm : Fr.norm = (nm : ℚ)) (depth Pbad K : ℕ) (hK : 2 ≤ c * K) (hq : 0 < q) (hLq : Lc ≤ q)
    (hP : ∀ p : ℕ, p.Prime → Pbad < p →
      ¬ p ∣ nm ∧ 5 ≤ p ∧ 2 * q ≤ p ∧ p ∉ I.cd.bad ∧ Gd p ∧ p ≠ 2)
    (hkq : ∀ p : ℕ, p.Prime → Pbad < p → ∀ j k : ℕ, q * k = j * p + o → 0 < j → j < q → 0 < k →
      k < p → I.cd.kq p = k) (wins : List (ℕ × ℕ)) :
    CatValid c hc Fr depth q o Pbad (NFr (1 / Fr.norm) (-1 / Fr.norm) q K)
      (tableT ++ ([brLP1, brLP2w, brRank] ++ wins.map (fun w => brWin w.1 w.2))) :=
  catValid_twoTermW I hL Lv c hc hc1 T hnorm depth Pbad _ hq hLq hP hkq
    (catValid_rank c hc T depth Pbad K hK (fun p hp h => by have := (hP p hp h).2.2.1; omega)) wins

/-- **`catValid_bankUF` with the widened LP2 branch**: catalogue `tableT ++ [LP1, LP2w, R, S] ++ windows`. -/
theorem catValid_bankUFw {Fr : Frame} (I : HybInst Fr) [∀ r m, I.DiagOK r m] {Lc : ℕ}
    (hL : I.cd.L = Lc) {Gd : ℕ → Prop}
    (Lv : CatalanFrames.HybCommon.LevelFacts I Gd (fun q c => c < I.cd.kq q))
    (c : ℚ) (hc : 0 < c) (hc1 : c ≤ 1) {q o : ℕ} (T : TwoTermData Fr q o) {nm : ℕ}
    (hnorm : Fr.norm = (nm : ℚ)) (depth Pbad K N1 : ℕ) (hK : 2 ≤ c * K) (hN1 : (q : ℚ) * (2 + c) ≤ c * N1)
    (hq : 0 < q) (hLq : Lc ≤ q)
    (hP : ∀ p : ℕ, p.Prime → Pbad < p →
      ¬ p ∣ nm ∧ 5 ≤ p ∧ 2 * q ≤ p ∧ p ∉ I.cd.bad ∧ Gd p ∧ p ≠ 2)
    (hkq : ∀ p : ℕ, p.Prime → Pbad < p → ∀ j k : ℕ, q * k = j * p + o → 0 < j → j < q → 0 < k →
      k < p → I.cd.kq p = k) (wins : List (ℕ × ℕ)) :
    CatValid c hc Fr depth q o Pbad (max (NFr (1 / Fr.norm) (-1 / Fr.norm) q K) N1)
      (tableT ++ ([brLP1, brLP2w, brRank, brS] ++ wins.map (fun w => brWin w.1 w.2))) := by
  have hUF := catValid_bankUF I hL Lv c hc hc1 T hnorm depth Pbad K N1 hK hN1 hq hLq hP hkq wins
  have hLPw := catValid_LP2w c hc T hnorm depth Pbad (max (NFr (1 / Fr.norm) (-1 / Fr.norm) q K) N1)
    (fun p hp h => ⟨(hP p hp h).1, (hP p hp h).2.1, (hP p hp h).2.2.1⟩)
  refine catValid_append (fun b hb => hUF b (List.mem_append_left _ hb)) ?_
  intro b hb
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with (rfl | rfl | rfl | rfl) | hb
  · exact hUF _ (by simp)
  · exact hLPw _ (by simp)
  · exact hUF _ (by simp)
  · exact hUF _ (by simp)
  · exact hUF b (List.mem_append_right _ (List.mem_append_right _ hb))

end CatalanCore.Uniform.Content.BankShared.Check

#print axioms CatalanCore.Uniform.Content.BankShared.Check.catValid_LP2w
#print axioms CatalanCore.Uniform.Content.BankShared.Check.catValid_bankW
#print axioms CatalanCore.Uniform.Content.BankShared.Check.catValid_bankUFw
