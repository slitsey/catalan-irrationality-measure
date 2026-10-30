import CatalanCore.Uniform.Bank.Lambda.RankCount.C1S00
import CatalanCore.Uniform.Bank.Lambda.RankMatch.C1S00
import CatalanCore.Uniform.Bank.Lambda.RankFacts.C1S00
import CatalanCore.Uniform.Bank.Lambda.RankAffine
import CatalanCore.Uniform.Bank.Lambda.RankUnits
import CatalanCore.Uniform.Bank.Lambda.RankCount.C1S00
import CatalanCore.Uniform.Bank.Lambda.RankSetup
import CatalanCore.Uniform.Bank.Lambda.PrimeBound
import CatalanCore.Uniform.Content.RankProducer.LineCost
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Lambda.RankPrice
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.Hybrid
open CatalanCore.Uniform.Content.RankProducer
open CatalanCore.Uniform.Bank.Chi3Rank
open RankFibre RankData RankCount
open scoped Classical

theorem C1S00_raw_member (a p r m : ℕ) [Fact p.Prime] (s : Finset (Fin r))
    (ha : a = 1 ∨ a = 3) (hp : rankPrimeCutoff < p) (hr : r % 2 = 0)
    (hodd : p % 2 = 1) (hrp : r ≤ 5 * p) (hm1 : 10 * m ≤ r + 5)
    (hm2 : r ≤ 10 * m + 5) (hright : 35 * p ≤ 8 * r) (hclass : root4 a p = 1) :
    ∃ M : RankMember (pipelineFrame a ha) (u4 a) q4 (fun c : Fin r => (c : ℕ))
      (fun j : Fin m => r + 2 * (j : ℕ)) (fun j : Fin m => r + 2 * (j : ℕ) + 1) s p,
      (M.price : ℚ) ≤ (21 / 10 : ℚ) * r + 49 + 8 * ((r - s.card : ℕ) : ℚ) := by
  have hp29 : 29 ≤ p := rankPrimeCutoff_ge_twentyNine.trans hp.le
  have hp4 : ¬ p ∣ 4 := by
    intro hd
    have h := Nat.le_of_dvd (by norm_num : 0 < 4) hd
    omega
  let PS := lambdaPoleSplit a p r m ha hp29 hp4 hrp hm1
  let cert := C1S00_assignment a p r m s ha hp29 hp4 hrp hm1
  have hleft : 1 * r ≤ 5 * p := by omega
  have hroot : 4 * pole4 a p + a = 1 * p := by
    have h := (root4_spec a p ha hodd).2.1
    rw [hclass] at h
    simpa only [Nat.mul_one, Nat.one_mul] using h
  have hden : ∀ N ∈ ([C1T00_den, C1T01_den, C1T02_den, C1T03_den,
      C1T04_den, C1T05_den, C1T06_den] : List ℕ), ¬ p ∣ N := by
    intro N hN hd
    have hb : ∀ N ∈ ([C1T00_den, C1T01_den, C1T02_den, C1T03_den,
        C1T04_den, C1T05_den, C1T06_den] : List ℕ), 0 < N ∧ N ≤ rankPrimeCutoff := by decide +kernel
    have hle := Nat.le_of_dvd (hb N hN).1 hd
    have hbound := (hb N hN).2
    omega
  have hdata (x : ZMod p) := C1S00_assignment_valid a p r m s ha hp29 hp4 hrp hm1
    hr hodd hm2 hleft hright (pole4 a p) (root4_spec a p ha hodd).2.2 hroot hden x
  have hOk : ∀ x, (cert x).Ok := fun x => (hdata x).1
  have hInt : ∀ x, (cert x).Integral p := fun x => (hdata x).2.1
  have hReal : ∀ x, Realizes PS (rowsOf r m s) (colsOf r m s) x (cert x) := fun x => (hdata x).2.2
  have hOR := killRows_card_eq_sum PS (rowsOf r m s) (colsOf r m s) (rows_inj r m s) cert hOk hReal
  have hOC := killCols_card_eq_sum PS (rowsOf r m s) (colsOf r m s) (cols_inj r m s) cert hOk hReal
  obtain ⟨bal, hBO, hBI, hBR, hK, hKC⟩ :=
    RankTools.exists_balanced_realization PS r m s cert hOk hInt hReal
  have hBC : (killRows (p := p) (rowsOf r m s) bal).card =
      (killCols (p := p) (colsOf r m s) bal).card := hK.trans hKC.symm
  have hw : ((1, 0) : RatFunc (ZMod p) × RatFunc (ZMod p)) ≠ 0 := by
    intro h
    have hf := congrArg Prod.fst h
    exact one_ne_zero hf
  let M := rankMemberOfAssignment a p r m s ha hp29 hp4 hrp hm1 bal hBO hBI hBR hBC (1, 0) hw
  have hMK : M.killCount = min (killRows (p := p) (rowsOf r m s) cert).card
      (killCols (p := p) (colsOf r m s) cert).card := hK
  have hKR : M.killCount ≤ s.card + m := by
    change (killRows (p := p) (rowsOf r m s) bal).card ≤ s.card + m
    simpa only [Fintype.card_sum, Fintype.card_coe, Fintype.card_fin] using
      (Finset.card_le_univ (killRows (p := p) (rowsOf r m s) bal))
  have hraw : M.price ≤ (s.card + m) + (s.card + m - M.killCount) := by
    simpa only [Fintype.card_sum, Fintype.card_coe, Fintype.card_fin] using M.price_le_raw
  have hN : M.price + M.killCount ≤ 2 * (s.card + m) := by omega
  have hQ : (M.price : ℚ) + (M.killCount : ℚ) ≤ 2 * ((s.card : ℚ) + (m : ℚ)) := by exact_mod_cast hN
  have hR : (1 / 10 : ℚ) * r - (48 + 8 * ((r - s.card : ℕ) : ℚ)) ≤
      ((killRows (p := p) (rowsOf r m s) cert).card : ℚ) := by
    rw [hOR]
    simpa using (C1S00_row_bounds a p r m s ha hp29 hp4 hrp hm1 hleft hright).1
  have hC : (1 / 10 : ℚ) * r - (48 + 8 * ((r - s.card : ℕ) : ℚ)) ≤
      ((killCols (p := p) (colsOf r m s) cert).card : ℚ) := by
    rw [hOC]
    simpa using (C1S00_col_bounds a p r m s ha hp29 hp4 hrp hm1 hleft hright).1
  have hmin : (1 / 10 : ℚ) * r - (48 + 8 * ((r - s.card : ℕ) : ℚ)) ≤ (M.killCount : ℚ) := by
    rw [hMK]
    rcases le_total (killRows (p := p) (rowsOf r m s) cert).card
        (killCols (p := p) (colsOf r m s) cert).card with h | h
    · rw [min_eq_left h]; exact hR
    · rw [min_eq_right h]; exact hC
  have hs : s.card ≤ r := by simpa using Finset.card_le_univ s
  have hsQ : (s.card : ℚ) ≤ r := by exact_mod_cast hs
  have hmQ : (10 : ℚ) * m ≤ r + 5 := by exact_mod_cast hm1
  exact ⟨M, by linarith⟩

#print axioms C1S00_raw_member
open RankFacts RankMatch

theorem C1S00_physical_valid (a p r m : ℕ) [Fact p.Prime] (s : Finset (Fin r))
    (ha : a = 1 ∨ a = 3) (hp : rankPrimeCutoff < p) (hr : r % 2 = 0)
    (hodd : p % 2 = 1) (hrp : r ≤ 5 * p) (hm1 : 10 * m ≤ r + 5)
    (hm2 : r ≤ 10 * m + 5) (hleft : 1 * r ≤ 5 * p)
    (hright : 35 * p ≤ 8 * r) (hclass : root4 a p = 1)
    (hp29 : 29 ≤ p) (hp4 : ¬ p ∣ 4) (x : ZMod p) :
    (C1S00_assignment a p r m s ha hp29 hp4 hrp hm1 x).Ok ∧ (C1S00_assignment a p r m s ha hp29 hp4 hrp hm1 x).Integral p ∧
      Realizes (lambdaPoleSplit a p r m ha hp29 hp4 hrp hm1)
        (rowsOf r m s) (colsOf r m s) x (C1S00_assignment a p r m s ha hp29 hp4 hrp hm1 x) := by
  have hroot : 4 * pole4 a p + a = 1 * p := by
    have h := (root4_spec a p ha hodd).2.1
    rw [hclass] at h
    simpa only [Nat.mul_one, Nat.one_mul, Nat.mul_comm] using h
  have hden : ∀ N ∈ ([C1T00_den, C1T01_den, C1T02_den, C1T03_den, C1T04_den, C1T05_den, C1T06_den] : List ℕ), ¬ p ∣ N := by
    intro N hN hd
    have hb : ∀ N ∈ ([C1T00_den, C1T01_den, C1T02_den, C1T03_den, C1T04_den, C1T05_den, C1T06_den] : List ℕ), 0 < N ∧ N ≤ rankPrimeCutoff := by decide +kernel
    have hle := Nat.le_of_dvd (hb N hN).1 hd
    have hbound := (hb N hN).2
    omega
  exact C1S00_assignment_valid a p r m s ha hp29 hp4 hrp hm1 hr hodd hm2 hleft hright
    (pole4 a p) (root4_spec a p ha hodd).2.2 hroot hden x

theorem C1S00_V0_member (a p r m : ℕ) [Fact p.Prime] (s : Finset (Fin r))
    (ha : a = 1 ∨ a = 3) (hp : rankPrimeCutoff < p) (hr : r % 2 = 0)
    (hodd : p % 2 = 1) (hrp : r ≤ 5 * p) (hm1 : 10 * m ≤ r + 5)
    (hm2 : r ≤ 10 * m + 5) (hleft : 1 * r ≤ 5 * p)
    (hright : 35 * p ≤ 8 * r) (hclass : root4 a p = 1) :
    ∃ M : RankMember (pipelineFrame a ha) (u4 a) q4 (fun c : Fin r => (c : ℕ))
      (fun j : Fin m => r + 2 * (j : ℕ)) (fun j : Fin m => r + 2 * (j : ℕ) + 1) s p,
      (M.price : ℚ) ≤ ((1 / 1 : ℚ) * (r : ℚ) + (21 / 4 : ℚ) * (p : ℚ)) + 289 + 48 * ((r - s.card : ℕ) : ℚ) := by
  have hp29 : 29 ≤ p := rankPrimeCutoff_ge_twentyNine.trans hp.le
  have hp4 : ¬ p ∣ 4 := by
    intro hd
    have hle := Nat.le_of_dvd (by norm_num : 0 < 4) hd
    omega
  let cert := C1S00_assignment a p r m s ha hp29 hp4 hrp hm1
  have hdata := C1S00_physical_valid a p r m s ha hp hr hodd hrp hm1 hm2 hleft hright hclass hp29 hp4
  have hOk : ∀ x, (cert x).Ok := fun x => (hdata x).1
  have hInt : ∀ x, (cert x).Integral p := fun x => (hdata x).2.1
  have hReal : ∀ x, Realizes (lambdaPoleSplit a p r m ha hp29 hp4 hrp hm1)
      (rowsOf r m s) (colsOf r m s) x (cert x) := fun x => (hdata x).2.2
  have hR0 := C1S00_row_bounds a p r m s ha hp29 hp4 hrp hm1 hleft hright
  have hC0 := C1S00_col_bounds a p r m s ha hp29 hp4 hrp hm1 hleft hright
  have hdepth : (0 : ℚ) ≤ ((r - s.card : ℕ) : ℚ) := Nat.cast_nonneg _
  have hR : ((1 / 10 : ℚ) * (r : ℚ) + (0 / 1 : ℚ) * (p : ℚ)) - (48 + 8 * ((r - s.card : ℕ) : ℚ)) ≤ ((∑ x : ZMod p, (cert x).kr.card : ℕ) : ℚ) ∧
      ((∑ x : ZMod p, (cert x).kr.card : ℕ) : ℚ) ≤ ((1 / 10 : ℚ) * (r : ℚ) + (0 / 1 : ℚ) * (p : ℚ)) + (48 + 8 * ((r - s.card : ℕ) : ℚ)) := by
    constructor <;> linarith [hR0.1, hR0.2]
  have hC : ((1 / 10 : ℚ) * (r : ℚ) + (0 / 1 : ℚ) * (p : ℚ)) - (48 + 8 * ((r - s.card : ℕ) : ℚ)) ≤ ((∑ x : ZMod p, (cert x).kc.card : ℕ) : ℚ) ∧
      ((∑ x : ZMod p, (cert x).kc.card : ℕ) : ℚ) ≤ ((1 / 10 : ℚ) * (r : ℚ) + (0 / 1 : ℚ) * (p : ℚ)) + (48 + 8 * ((r - s.card : ℕ) : ℚ)) := by
    constructor <;> linarith [hC0.1, hC0.2]
  have hf := C1S00_load_facts a p r m s ha hp29 hp4 hrp hm1 hp
  have hv1 : C1S00_V0.1 ∈ S p := rank_rational_mem p C1S00_V0.1 hp (by decide +kernel)
  have hv2 : C1S00_V0.2 ∈ S p := rank_rational_mem p C1S00_V0.2 hp (by decide +kernel)
  have hv : castV p C1S00_V0 ≠ 0 := rank_castV_ne_zero_of_fst p C1S00_V0 hp
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have hm0 := C1S00_V0_matched_lower a p r m s ha hp29 hp4 hrp hm1 hleft hright
  have hMatch : ((6 / 5 : ℚ) * (r : ℚ) + (-21 / 4 : ℚ) * (p : ℚ)) - 2 * (48 + 8 * ((r - s.card : ℕ) : ℚ)) ≤
      (((∑ x : ZMod p, rationalRowMatches (cert x) C1S00_V0) +
        (∑ x : ZMod p, rationalColMatches (cert x) C1S00_V0) : ℕ) : ℚ) := by linarith
  obtain ⟨M, hM⟩ := rank_affine_member a p r m s ha hp29 hp4 hrp hm1 cert hOk hInt hReal
    (fun x => (hf x).1.1) (fun x => (hf x).1.2) C1S00_V0 hv1 hv2 hv
    (fun x => (hf x).2.1) (fun x d hd => ⟨((hf x).2.2 d hd).1, ((hf x).2.2 d hd).2.1⟩)
    (fun x d hd => ((hf x).2.2 d hd).2.2) ((1 / 10 : ℚ) * (r : ℚ) + (0 / 1 : ℚ) * (p : ℚ)) ((6 / 5 : ℚ) * (r : ℚ) + (-21 / 4 : ℚ) * (p : ℚ)) (48 + 8 * ((r - s.card : ℕ) : ℚ)) hR hC hMatch
  exact ⟨M, by linarith⟩
#print axioms C1S00_V0_member

theorem C1S00_V1_member (a p r m : ℕ) [Fact p.Prime] (s : Finset (Fin r))
    (ha : a = 1 ∨ a = 3) (hp : rankPrimeCutoff < p) (hr : r % 2 = 0)
    (hodd : p % 2 = 1) (hrp : r ≤ 5 * p) (hm1 : 10 * m ≤ r + 5)
    (hm2 : r ≤ 10 * m + 5) (hleft : 1 * r ≤ 5 * p)
    (hright : 35 * p ≤ 8 * r) (hclass : root4 a p = 1) :
    ∃ M : RankMember (pipelineFrame a ha) (u4 a) q4 (fun c : Fin r => (c : ℕ))
      (fun j : Fin m => r + 2 * (j : ℕ)) (fun j : Fin m => r + 2 * (j : ℕ) + 1) s p,
      (M.price : ℚ) ≤ ((16 / 5 : ℚ) * (r : ℚ) + (-5 / 1 : ℚ) * (p : ℚ)) + 289 + 48 * ((r - s.card : ℕ) : ℚ) := by
  have hp29 : 29 ≤ p := rankPrimeCutoff_ge_twentyNine.trans hp.le
  have hp4 : ¬ p ∣ 4 := by
    intro hd
    have hle := Nat.le_of_dvd (by norm_num : 0 < 4) hd
    omega
  let cert := C1S00_assignment a p r m s ha hp29 hp4 hrp hm1
  have hdata := C1S00_physical_valid a p r m s ha hp hr hodd hrp hm1 hm2 hleft hright hclass hp29 hp4
  have hOk : ∀ x, (cert x).Ok := fun x => (hdata x).1
  have hInt : ∀ x, (cert x).Integral p := fun x => (hdata x).2.1
  have hReal : ∀ x, Realizes (lambdaPoleSplit a p r m ha hp29 hp4 hrp hm1)
      (rowsOf r m s) (colsOf r m s) x (cert x) := fun x => (hdata x).2.2
  have hR0 := C1S00_row_bounds a p r m s ha hp29 hp4 hrp hm1 hleft hright
  have hC0 := C1S00_col_bounds a p r m s ha hp29 hp4 hrp hm1 hleft hright
  have hdepth : (0 : ℚ) ≤ ((r - s.card : ℕ) : ℚ) := Nat.cast_nonneg _
  have hR : ((1 / 10 : ℚ) * (r : ℚ) + (0 / 1 : ℚ) * (p : ℚ)) - (48 + 8 * ((r - s.card : ℕ) : ℚ)) ≤ ((∑ x : ZMod p, (cert x).kr.card : ℕ) : ℚ) ∧
      ((∑ x : ZMod p, (cert x).kr.card : ℕ) : ℚ) ≤ ((1 / 10 : ℚ) * (r : ℚ) + (0 / 1 : ℚ) * (p : ℚ)) + (48 + 8 * ((r - s.card : ℕ) : ℚ)) := by
    constructor <;> linarith [hR0.1, hR0.2]
  have hC : ((1 / 10 : ℚ) * (r : ℚ) + (0 / 1 : ℚ) * (p : ℚ)) - (48 + 8 * ((r - s.card : ℕ) : ℚ)) ≤ ((∑ x : ZMod p, (cert x).kc.card : ℕ) : ℚ) ∧
      ((∑ x : ZMod p, (cert x).kc.card : ℕ) : ℚ) ≤ ((1 / 10 : ℚ) * (r : ℚ) + (0 / 1 : ℚ) * (p : ℚ)) + (48 + 8 * ((r - s.card : ℕ) : ℚ)) := by
    constructor <;> linarith [hC0.1, hC0.2]
  have hf := C1S00_load_facts a p r m s ha hp29 hp4 hrp hm1 hp
  have hv1 : C1S00_V1.1 ∈ S p := rank_rational_mem p C1S00_V1.1 hp (by decide +kernel)
  have hv2 : C1S00_V1.2 ∈ S p := rank_rational_mem p C1S00_V1.2 hp (by decide +kernel)
  have hv : castV p C1S00_V1 ≠ 0 := rank_castV_ne_zero_of_fst p C1S00_V1 hp
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have hm0 := C1S00_V1_matched_lower a p r m s ha hp29 hp4 hrp hm1 hleft hright
  have hMatch : ((-1 / 1 : ℚ) * (r : ℚ) + (5 / 1 : ℚ) * (p : ℚ)) - 2 * (48 + 8 * ((r - s.card : ℕ) : ℚ)) ≤
      (((∑ x : ZMod p, rationalRowMatches (cert x) C1S00_V1) +
        (∑ x : ZMod p, rationalColMatches (cert x) C1S00_V1) : ℕ) : ℚ) := by linarith
  obtain ⟨M, hM⟩ := rank_affine_member a p r m s ha hp29 hp4 hrp hm1 cert hOk hInt hReal
    (fun x => (hf x).1.1) (fun x => (hf x).1.2) C1S00_V1 hv1 hv2 hv
    (fun x => (hf x).2.1) (fun x d hd => ⟨((hf x).2.2 d hd).1, ((hf x).2.2 d hd).2.1⟩)
    (fun x d hd => ((hf x).2.2 d hd).2.2) ((1 / 10 : ℚ) * (r : ℚ) + (0 / 1 : ℚ) * (p : ℚ)) ((-1 / 1 : ℚ) * (r : ℚ) + (5 / 1 : ℚ) * (p : ℚ)) (48 + 8 * ((r - s.card : ℕ) : ℚ)) hR hC hMatch
  exact ⟨M, by linarith⟩
#print axioms C1S00_V1_member
end CatalanCore.Uniform.Bank.Lambda.RankPrice
