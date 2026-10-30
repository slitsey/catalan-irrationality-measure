import CatalanCore.Uniform.Bank.Sevenths.RankCount.C1S00
import CatalanCore.Uniform.Bank.Sevenths.RankFacts.C1S00
import CatalanCore.Uniform.Bank.Sevenths.RankFinish
import CatalanCore.Uniform.Bank.Sevenths.RankUnits
import CatalanCore.Uniform.Bank.Sevenths.Roots
import CatalanCore.Uniform.Content.RankProducer.LineBound
import CatalanCore.Uniform.Bank.Sevenths.RankMatch.C1S00
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace CatalanCore.Uniform.Bank.Sevenths.RankPrice
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.Hybrid
open CatalanCore.Uniform.Content.RankProducer CatalanCore.Uniform.Content.RankProducer.Geometry
open RankFibre RankData RankCount RankFacts
open scoped Classical
open RankMatch

theorem C1S00_member0 (a : Fin 6) (p r m : ℕ) [Fact p.Prime] (s : Finset (Fin r))
    (hp : rankPrimeCutoff < p) (hr : r % 2 = 0) (hodd : p % 2 = 1)
    (hrp : r ≤ 6 * p) (hm1 : 12 * m ≤ r + 6) (hm2 : r ≤ 12 * m + 6)
    (hleft : 1 * r ≤ 6 * p)
    (hright : 258 * p ≤ 49 * r)
    (hroot : 7 * (seventhRho a p - 1) + seventhNumerator a = 1 * p) :
    ∃ M : RankMember (pipelineFrame a) (u7 a) q7 (fun c : Fin r => (c : ℕ))
      (fun j : Fin m => r + 2 * (j : ℕ)) (fun j : Fin m => r + 2 * (j : ℕ) + 1) s p,
      (M.price : ℚ) ≤ ((1 / 1 : ℚ) * (r : ℚ) + (43 / 7 : ℚ) * (p : ℚ)) + 1000 * (((r - s.card : ℕ) : ℚ) + 1) := by
  have hp64 : 64 ≤ p := rankPrimeCutoff_ge_sixtyFour.trans hp.le
  have ha : 1 ≤ seventhNumerator a ∧ seventhNumerator a ≤ 6 := by
    dsimp [seventhNumerator]
    have := a.isLt
    omega
  have hp7 : ¬ p ∣ 7 := by
    intro hd
    have := Nat.le_of_dvd (by norm_num : 0 < 7) hd
    omega
  let PS := seventhsPoleSplit (seventhNumerator a) p r m ha hp64 hp7 hrp hm1
  let cert := C1S00_assignment (seventhNumerator a) p r m s ha hp64 hp7 hrp hm1
  have hden : ∀ N ∈ ([C1T00_den, C1T01_den, C1T02_den, C1T03_den, C1T04_den, C1T05_den, C1T06_den] : List ℕ), ¬ p ∣ N := by
    intro N hN hd
    have hb : ∀ N ∈ ([C1T00_den, C1T01_den, C1T02_den, C1T03_den, C1T04_den, C1T05_den, C1T06_den] : List ℕ), 0 < N ∧ N ≤ rankPrimeCutoff := by decide +kernel
    have hle := Nat.le_of_dvd (hb N hN).1 hd
    have hbound := (hb N hN).2
    omega
  have hb := seventhRho_bounds a p (by omega)
  have hdata (x : ZMod p) := C1S00_assignment_valid (seventhNumerator a) p r m s ha hp64 hp7 hrp hm1
    hr hodd hm2 hleft hright (seventhRho a p - 1) (by omega) hroot hden x
  have hOk : ∀ x, (cert x).Ok := fun x => (hdata x).1
  have hInt : ∀ x, (cert x).Integral p := fun x => (hdata x).2.1
  have hReal : ∀ x, Realizes PS (rowsOf r m s) (colsOf r m s) x (cert x) := fun x => (hdata x).2.2
  have hOR := killRows_card_eq_sum PS (rowsOf r m s) (colsOf r m s) (rows_inj r m s) cert hOk hReal
  have hOC := killCols_card_eq_sum PS (rowsOf r m s) (colsOf r m s) (cols_inj r m s) cert hOk hReal
  have hR : ((1 / 12 : ℚ) * (r : ℚ) + (0 / 1 : ℚ) * (p : ℚ)) - (48 + 8 * ((r - s.card : ℕ) : ℚ)) ≤
      ((killRows (p := p) (rowsOf r m s) cert).card : ℚ) ∧
      ((killRows (p := p) (rowsOf r m s) cert).card : ℚ) ≤ ((1 / 12 : ℚ) * (r : ℚ) + (0 / 1 : ℚ) * (p : ℚ)) + 48 := by
    rw [hOR]
    exact C1S00_row_bounds (seventhNumerator a) p r m s ha hp64 hp7 hrp hm1 hleft hright
  have hC : ((1 / 12 : ℚ) * (r : ℚ) + (0 / 1 : ℚ) * (p : ℚ)) - (48 + 8 * ((r - s.card : ℕ) : ℚ)) ≤
      ((killCols (p := p) (colsOf r m s) cert).card : ℚ) ∧
      ((killCols (p := p) (colsOf r m s) cert).card : ℚ) ≤ ((1 / 12 : ℚ) * (r : ℚ) + (0 / 1 : ℚ) * (p : ℚ)) + 48 := by
    rw [hOC]
    exact C1S00_col_bounds (seventhNumerator a) p r m s ha hp64 hp7 hrp hm1 hleft hright
  have hFacts (x : ZMod p) := C1S00_load_facts (seventhNumerator a) p r m s ha hp64 hp7 hrp hm1 hp x
  let V : ℚ × ℚ := C1S00_V0
  have hV1 : V.1 ∈ S p := rank_rational_mem p V.1 hp (by decide +kernel)
  have hV2 : V.2 ∈ S p := rank_rational_mem p V.2 hp (by decide +kernel)
  have hV : castV p V ≠ 0 := rank_castV_ne_zero_of_fst p V hp
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  obtain ⟨M, hK, hcost, htrim⟩ := balanced_rank_line a p r m s hp64 hp7 hrp hm1
    cert hOk hInt hReal (fun x => (hFacts x).1.1) (fun x => (hFacts x).1.2)
    V hV1 hV2 hV (fun x => (hFacts x).2.1)
    (fun x d hd => ⟨((hFacts x).2.2 d hd).1, ((hFacts x).2.2 d hd).2.1⟩)
    (fun x d hd => ((hFacts x).2.2 d hd).2.2)
  have hs : (s.card : ℚ) ≤ r := by exact_mod_cast (show s.card ≤ r by simpa using Finset.card_le_univ s)
  have hm : (12 : ℚ) * m ≤ r + 6 := by exact_mod_cast hm1
  have hdepth : (0 : ℚ) ≤ ((r - s.card : ℕ) : ℚ) := Nat.cast_nonneg _
  have hW := C1S00_V0_matched_lower (seventhNumerator a) p r m s ha hp64 hp7 hrp hm1 hleft hright
  have htrim' : (∑ x : ZMod p, rationalRowMatches (cert x) V) +
      (∑ x : ZMod p, rationalColMatches (cert x) V) ≤ M.colScore + M.rowScore +
      ((killRows (p := p) (rowsOf r m s) cert).card - M.killCount) +
      ((killCols (p := p) (colsOf r m s) cert).card - M.killCount) := by omega
  have hP := price_le_line_of_counts M.price M.killCount
    (killRows (p := p) (rowsOf r m s) cert).card
    (killCols (p := p) (colsOf r m s) cert).card M.colScore M.rowScore
    ((∑ x : ZMod p, rationalRowMatches (cert x) V) + (∑ x : ZMod p, rationalColMatches (cert x) V))
    (s.card + m) ((1 / 12 : ℚ) * (r : ℚ) + (0 / 1 : ℚ) * (p : ℚ)) (48 + 8 * ((r - s.card : ℕ) : ℚ)) 48
    ((7 / 6 : ℚ) * (r : ℚ) + (-43 / 7 : ℚ) * (p : ℚ)) (96 + 16 * ((r - s.card : ℕ) : ℚ)) hK hcost htrim' hR hC hW
  exact ⟨M, by push_cast at hP; linarith⟩

#print axioms C1S00_member0

theorem C1S00_member1 (a : Fin 6) (p r m : ℕ) [Fact p.Prime] (s : Finset (Fin r))
    (hp : rankPrimeCutoff < p) (hr : r % 2 = 0) (hodd : p % 2 = 1)
    (hrp : r ≤ 6 * p) (hm1 : 12 * m ≤ r + 6) (hm2 : r ≤ 12 * m + 6)
    (hleft : 1 * r ≤ 6 * p)
    (hright : 258 * p ≤ 49 * r)
    (hroot : 7 * (seventhRho a p - 1) + seventhNumerator a = 1 * p) :
    ∃ M : RankMember (pipelineFrame a) (u7 a) q7 (fun c : Fin r => (c : ℕ))
      (fun j : Fin m => r + 2 * (j : ℕ)) (fun j : Fin m => r + 2 * (j : ℕ) + 1) s p,
      (M.price : ℚ) ≤ ((25 / 12 : ℚ) * (r : ℚ) + (0 / 1 : ℚ) * (p : ℚ)) + 1000 * (((r - s.card : ℕ) : ℚ) + 1) := by
  have hp64 : 64 ≤ p := rankPrimeCutoff_ge_sixtyFour.trans hp.le
  have ha : 1 ≤ seventhNumerator a ∧ seventhNumerator a ≤ 6 := by
    dsimp [seventhNumerator]
    have := a.isLt
    omega
  have hp7 : ¬ p ∣ 7 := by
    intro hd
    have := Nat.le_of_dvd (by norm_num : 0 < 7) hd
    omega
  let PS := seventhsPoleSplit (seventhNumerator a) p r m ha hp64 hp7 hrp hm1
  let cert := C1S00_assignment (seventhNumerator a) p r m s ha hp64 hp7 hrp hm1
  have hden : ∀ N ∈ ([C1T00_den, C1T01_den, C1T02_den, C1T03_den, C1T04_den, C1T05_den, C1T06_den] : List ℕ), ¬ p ∣ N := by
    intro N hN hd
    have hb : ∀ N ∈ ([C1T00_den, C1T01_den, C1T02_den, C1T03_den, C1T04_den, C1T05_den, C1T06_den] : List ℕ), 0 < N ∧ N ≤ rankPrimeCutoff := by decide +kernel
    have hle := Nat.le_of_dvd (hb N hN).1 hd
    have hbound := (hb N hN).2
    omega
  have hb := seventhRho_bounds a p (by omega)
  have hdata (x : ZMod p) := C1S00_assignment_valid (seventhNumerator a) p r m s ha hp64 hp7 hrp hm1
    hr hodd hm2 hleft hright (seventhRho a p - 1) (by omega) hroot hden x
  have hOk : ∀ x, (cert x).Ok := fun x => (hdata x).1
  have hInt : ∀ x, (cert x).Integral p := fun x => (hdata x).2.1
  have hReal : ∀ x, Realizes PS (rowsOf r m s) (colsOf r m s) x (cert x) := fun x => (hdata x).2.2
  have hOR := killRows_card_eq_sum PS (rowsOf r m s) (colsOf r m s) (rows_inj r m s) cert hOk hReal
  have hOC := killCols_card_eq_sum PS (rowsOf r m s) (colsOf r m s) (cols_inj r m s) cert hOk hReal
  have hR : ((1 / 12 : ℚ) * (r : ℚ) + (0 / 1 : ℚ) * (p : ℚ)) - (48 + 8 * ((r - s.card : ℕ) : ℚ)) ≤
      ((killRows (p := p) (rowsOf r m s) cert).card : ℚ) ∧
      ((killRows (p := p) (rowsOf r m s) cert).card : ℚ) ≤ ((1 / 12 : ℚ) * (r : ℚ) + (0 / 1 : ℚ) * (p : ℚ)) + 48 := by
    rw [hOR]
    exact C1S00_row_bounds (seventhNumerator a) p r m s ha hp64 hp7 hrp hm1 hleft hright
  have hC : ((1 / 12 : ℚ) * (r : ℚ) + (0 / 1 : ℚ) * (p : ℚ)) - (48 + 8 * ((r - s.card : ℕ) : ℚ)) ≤
      ((killCols (p := p) (colsOf r m s) cert).card : ℚ) ∧
      ((killCols (p := p) (colsOf r m s) cert).card : ℚ) ≤ ((1 / 12 : ℚ) * (r : ℚ) + (0 / 1 : ℚ) * (p : ℚ)) + 48 := by
    rw [hOC]
    exact C1S00_col_bounds (seventhNumerator a) p r m s ha hp64 hp7 hrp hm1 hleft hright
  have hFacts (x : ZMod p) := C1S00_load_facts (seventhNumerator a) p r m s ha hp64 hp7 hrp hm1 hp x
  let V : ℚ × ℚ := ((1, 0) : ℚ × ℚ)
  have hV1 : V.1 ∈ S p := rank_rational_mem p V.1 hp (by decide +kernel)
  have hV2 : V.2 ∈ S p := rank_rational_mem p V.2 hp (by decide +kernel)
  have hV : castV p V ≠ 0 := rank_castV_ne_zero_of_fst p V hp
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  obtain ⟨M, hK, hcost, htrim⟩ := balanced_rank_line a p r m s hp64 hp7 hrp hm1
    cert hOk hInt hReal (fun x => (hFacts x).1.1) (fun x => (hFacts x).1.2)
    V hV1 hV2 hV (fun x => (hFacts x).2.1)
    (fun x d hd => ⟨((hFacts x).2.2 d hd).1, ((hFacts x).2.2 d hd).2.1⟩)
    (fun x d hd => ((hFacts x).2.2 d hd).2.2)
  have hs : (s.card : ℚ) ≤ r := by exact_mod_cast (show s.card ≤ r by simpa using Finset.card_le_univ s)
  have hm : (12 : ℚ) * m ≤ r + 6 := by exact_mod_cast hm1
  have hdepth : (0 : ℚ) ≤ ((r - s.card : ℕ) : ℚ) := Nat.cast_nonneg _
  have hmin : ((1 / 12 : ℚ) * (r : ℚ) + (0 / 1 : ℚ) * (p : ℚ)) - (48 + 8 * ((r - s.card : ℕ) : ℚ)) ≤ (M.killCount : ℚ) := by
    rw [hK]
    rcases le_total (killRows (p := p) (rowsOf r m s) cert).card
        (killCols (p := p) (colsOf r m s) cert).card with h | h
    · rw [min_eq_left h]; exact hR.1
    · rw [min_eq_right h]; exact hC.1
  have hraw : M.price + M.killCount ≤ 2 * (s.card + m) := by omega
  have hrawQ : (M.price : ℚ) + (M.killCount : ℚ) ≤ 2 * ((s.card : ℚ) + m) := by exact_mod_cast hraw
  exact ⟨M, by linarith⟩

#print axioms C1S00_member1

theorem C1S00_member2 (a : Fin 6) (p r m : ℕ) [Fact p.Prime] (s : Finset (Fin r))
    (hp : rankPrimeCutoff < p) (hr : r % 2 = 0) (hodd : p % 2 = 1)
    (hrp : r ≤ 6 * p) (hm1 : 12 * m ≤ r + 6) (hm2 : r ≤ 12 * m + 6)
    (hleft : 1 * r ≤ 6 * p)
    (hright : 258 * p ≤ 49 * r)
    (hroot : 7 * (seventhRho a p - 1) + seventhNumerator a = 1 * p) :
    ∃ M : RankMember (pipelineFrame a) (u7 a) q7 (fun c : Fin r => (c : ℕ))
      (fun j : Fin m => r + 2 * (j : ℕ)) (fun j : Fin m => r + 2 * (j : ℕ) + 1) s p,
      (M.price : ℚ) ≤ ((19 / 6 : ℚ) * (r : ℚ) + (-6 / 1 : ℚ) * (p : ℚ)) + 1000 * (((r - s.card : ℕ) : ℚ) + 1) := by
  have hp64 : 64 ≤ p := rankPrimeCutoff_ge_sixtyFour.trans hp.le
  have ha : 1 ≤ seventhNumerator a ∧ seventhNumerator a ≤ 6 := by
    dsimp [seventhNumerator]
    have := a.isLt
    omega
  have hp7 : ¬ p ∣ 7 := by
    intro hd
    have := Nat.le_of_dvd (by norm_num : 0 < 7) hd
    omega
  let PS := seventhsPoleSplit (seventhNumerator a) p r m ha hp64 hp7 hrp hm1
  let cert := C1S00_assignment (seventhNumerator a) p r m s ha hp64 hp7 hrp hm1
  have hden : ∀ N ∈ ([C1T00_den, C1T01_den, C1T02_den, C1T03_den, C1T04_den, C1T05_den, C1T06_den] : List ℕ), ¬ p ∣ N := by
    intro N hN hd
    have hb : ∀ N ∈ ([C1T00_den, C1T01_den, C1T02_den, C1T03_den, C1T04_den, C1T05_den, C1T06_den] : List ℕ), 0 < N ∧ N ≤ rankPrimeCutoff := by decide +kernel
    have hle := Nat.le_of_dvd (hb N hN).1 hd
    have hbound := (hb N hN).2
    omega
  have hb := seventhRho_bounds a p (by omega)
  have hdata (x : ZMod p) := C1S00_assignment_valid (seventhNumerator a) p r m s ha hp64 hp7 hrp hm1
    hr hodd hm2 hleft hright (seventhRho a p - 1) (by omega) hroot hden x
  have hOk : ∀ x, (cert x).Ok := fun x => (hdata x).1
  have hInt : ∀ x, (cert x).Integral p := fun x => (hdata x).2.1
  have hReal : ∀ x, Realizes PS (rowsOf r m s) (colsOf r m s) x (cert x) := fun x => (hdata x).2.2
  have hOR := killRows_card_eq_sum PS (rowsOf r m s) (colsOf r m s) (rows_inj r m s) cert hOk hReal
  have hOC := killCols_card_eq_sum PS (rowsOf r m s) (colsOf r m s) (cols_inj r m s) cert hOk hReal
  have hR : ((1 / 12 : ℚ) * (r : ℚ) + (0 / 1 : ℚ) * (p : ℚ)) - (48 + 8 * ((r - s.card : ℕ) : ℚ)) ≤
      ((killRows (p := p) (rowsOf r m s) cert).card : ℚ) ∧
      ((killRows (p := p) (rowsOf r m s) cert).card : ℚ) ≤ ((1 / 12 : ℚ) * (r : ℚ) + (0 / 1 : ℚ) * (p : ℚ)) + 48 := by
    rw [hOR]
    exact C1S00_row_bounds (seventhNumerator a) p r m s ha hp64 hp7 hrp hm1 hleft hright
  have hC : ((1 / 12 : ℚ) * (r : ℚ) + (0 / 1 : ℚ) * (p : ℚ)) - (48 + 8 * ((r - s.card : ℕ) : ℚ)) ≤
      ((killCols (p := p) (colsOf r m s) cert).card : ℚ) ∧
      ((killCols (p := p) (colsOf r m s) cert).card : ℚ) ≤ ((1 / 12 : ℚ) * (r : ℚ) + (0 / 1 : ℚ) * (p : ℚ)) + 48 := by
    rw [hOC]
    exact C1S00_col_bounds (seventhNumerator a) p r m s ha hp64 hp7 hrp hm1 hleft hright
  have hFacts (x : ZMod p) := C1S00_load_facts (seventhNumerator a) p r m s ha hp64 hp7 hrp hm1 hp x
  let V : ℚ × ℚ := C1S00_V1
  have hV1 : V.1 ∈ S p := rank_rational_mem p V.1 hp (by decide +kernel)
  have hV2 : V.2 ∈ S p := rank_rational_mem p V.2 hp (by decide +kernel)
  have hV : castV p V ≠ 0 := rank_castV_ne_zero_of_fst p V hp
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  obtain ⟨M, hK, hcost, htrim⟩ := balanced_rank_line a p r m s hp64 hp7 hrp hm1
    cert hOk hInt hReal (fun x => (hFacts x).1.1) (fun x => (hFacts x).1.2)
    V hV1 hV2 hV (fun x => (hFacts x).2.1)
    (fun x d hd => ⟨((hFacts x).2.2 d hd).1, ((hFacts x).2.2 d hd).2.1⟩)
    (fun x d hd => ((hFacts x).2.2 d hd).2.2)
  have hs : (s.card : ℚ) ≤ r := by exact_mod_cast (show s.card ≤ r by simpa using Finset.card_le_univ s)
  have hm : (12 : ℚ) * m ≤ r + 6 := by exact_mod_cast hm1
  have hdepth : (0 : ℚ) ≤ ((r - s.card : ℕ) : ℚ) := Nat.cast_nonneg _
  have hW := C1S00_V1_matched_lower (seventhNumerator a) p r m s ha hp64 hp7 hrp hm1 hleft hright
  have htrim' : (∑ x : ZMod p, rationalRowMatches (cert x) V) +
      (∑ x : ZMod p, rationalColMatches (cert x) V) ≤ M.colScore + M.rowScore +
      ((killRows (p := p) (rowsOf r m s) cert).card - M.killCount) +
      ((killCols (p := p) (colsOf r m s) cert).card - M.killCount) := by omega
  have hP := price_le_line_of_counts M.price M.killCount
    (killRows (p := p) (rowsOf r m s) cert).card
    (killCols (p := p) (colsOf r m s) cert).card M.colScore M.rowScore
    ((∑ x : ZMod p, rationalRowMatches (cert x) V) + (∑ x : ZMod p, rationalColMatches (cert x) V))
    (s.card + m) ((1 / 12 : ℚ) * (r : ℚ) + (0 / 1 : ℚ) * (p : ℚ)) (48 + 8 * ((r - s.card : ℕ) : ℚ)) 48
    ((-1 / 1 : ℚ) * (r : ℚ) + (6 / 1 : ℚ) * (p : ℚ)) (96 + 16 * ((r - s.card : ℕ) : ℚ)) hK hcost htrim' hR hC hW
  exact ⟨M, by push_cast at hP; linarith⟩

#print axioms C1S00_member2
end CatalanCore.Uniform.Bank.Sevenths.RankPrice
