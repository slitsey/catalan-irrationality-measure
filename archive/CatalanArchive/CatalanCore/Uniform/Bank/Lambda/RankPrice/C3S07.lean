import CatalanCore.Uniform.Bank.Lambda.RankCount.C3S07
import CatalanCore.Uniform.Bank.Lambda.RankMatch.C3S07
import CatalanCore.Uniform.Bank.Lambda.RankFacts.C3S07
import CatalanCore.Uniform.Bank.Lambda.RankAffine
import CatalanCore.Uniform.Bank.Lambda.RankUnits
set_option Elab.async false
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Lambda.RankPrice
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.Hybrid
open CatalanCore.Uniform.Content.RankProducer
open CatalanCore.Uniform.Bank.Chi3Rank
open RankFibre RankData RankCount RankFacts RankMatch
open scoped Classical

theorem C3S07_physical_valid (a p r m : ℕ) [Fact p.Prime] (s : Finset (Fin r))
    (ha : a = 1 ∨ a = 3) (hp : rankPrimeCutoff < p) (hr : r % 2 = 0)
    (hodd : p % 2 = 1) (hrp : r ≤ 5 * p) (hm1 : 10 * m ≤ r + 5)
    (hm2 : r ≤ 10 * m + 5) (hleft : 3 * r ≤ 10 * p)
    (hright : 25 * p ≤ 8 * r) (hclass : root4 a p = 3)
    (hp29 : 29 ≤ p) (hp4 : ¬ p ∣ 4) (x : ZMod p) :
    (C3S07_assignment a p r m s ha hp29 hp4 hrp hm1 x).Ok ∧ (C3S07_assignment a p r m s ha hp29 hp4 hrp hm1 x).Integral p ∧
      Realizes (lambdaPoleSplit a p r m ha hp29 hp4 hrp hm1)
        (rowsOf r m s) (colsOf r m s) x (C3S07_assignment a p r m s ha hp29 hp4 hrp hm1 x) := by
  have hroot : 4 * pole4 a p + a = 3 * p := by
    have h := (root4_spec a p ha hodd).2.1
    rw [hclass] at h
    simpa only [Nat.mul_one, Nat.one_mul, Nat.mul_comm] using h
  have hden : ∀ N ∈ ([C3T11_den, C3T12_den, C3T13_den, C3T14_den, C3T15_den, C3T16_den] : List ℕ), ¬ p ∣ N := by
    intro N hN hd
    have hb : ∀ N ∈ ([C3T11_den, C3T12_den, C3T13_den, C3T14_den, C3T15_den, C3T16_den] : List ℕ), 0 < N ∧ N ≤ rankPrimeCutoff := by decide +kernel
    have hle := Nat.le_of_dvd (hb N hN).1 hd
    have hbound := (hb N hN).2
    omega
  exact C3S07_assignment_valid a p r m s ha hp29 hp4 hrp hm1 hr hodd hm2 hleft hright
    (pole4 a p) (root4_spec a p ha hodd).2.2 hroot hden x

theorem C3S07_raw_member (a p r m : ℕ) [Fact p.Prime] (s : Finset (Fin r))
    (ha : a = 1 ∨ a = 3) (hp : rankPrimeCutoff < p) (hr : r % 2 = 0)
    (hodd : p % 2 = 1) (hrp : r ≤ 5 * p) (hm1 : 10 * m ≤ r + 5)
    (hm2 : r ≤ 10 * m + 5) (hleft : 3 * r ≤ 10 * p)
    (hright : 25 * p ≤ 8 * r) (hclass : root4 a p = 3) :
    ∃ M : RankMember (pipelineFrame a ha) (u4 a) q4 (fun c : Fin r => (c : ℕ))
      (fun j : Fin m => r + 2 * (j : ℕ)) (fun j : Fin m => r + 2 * (j : ℕ) + 1) s p,
      (M.price : ℚ) ≤ ((21 / 10 : ℚ) * (r : ℚ) + (0 / 1 : ℚ) * (p : ℚ)) + 49 + 8 * ((r - s.card : ℕ) : ℚ) := by
  have hp29 : 29 ≤ p := rankPrimeCutoff_ge_twentyNine.trans hp.le
  have hp4 : ¬ p ∣ 4 := by
    intro hd
    have hle := Nat.le_of_dvd (by norm_num : 0 < 4) hd
    omega
  let cert := C3S07_assignment a p r m s ha hp29 hp4 hrp hm1
  have hdata := C3S07_physical_valid a p r m s ha hp hr hodd hrp hm1 hm2 hleft hright hclass hp29 hp4
  have hOk : ∀ x, (cert x).Ok := fun x => (hdata x).1
  have hInt : ∀ x, (cert x).Integral p := fun x => (hdata x).2.1
  have hReal : ∀ x, Realizes (lambdaPoleSplit a p r m ha hp29 hp4 hrp hm1)
      (rowsOf r m s) (colsOf r m s) x (cert x) := fun x => (hdata x).2.2
  have hR0 := C3S07_row_bounds a p r m s ha hp29 hp4 hrp hm1 hleft hright
  have hC0 := C3S07_col_bounds a p r m s ha hp29 hp4 hrp hm1 hleft hright
  obtain ⟨M, hM⟩ := rank_raw_member a p r m s ha hp29 hp4 hrp hm1 cert hOk hInt hReal ((1 / 10 : ℚ) * (r : ℚ) + (0 / 1 : ℚ) * (p : ℚ)) (48 + 8 * ((r - s.card : ℕ) : ℚ)) hR0.1 hC0.1
  exact ⟨M, by linarith⟩
#print axioms C3S07_raw_member

theorem C3S07_V0_member (a p r m : ℕ) [Fact p.Prime] (s : Finset (Fin r))
    (ha : a = 1 ∨ a = 3) (hp : rankPrimeCutoff < p) (hr : r % 2 = 0)
    (hodd : p % 2 = 1) (hrp : r ≤ 5 * p) (hm1 : 10 * m ≤ r + 5)
    (hm2 : r ≤ 10 * m + 5) (hleft : 3 * r ≤ 10 * p)
    (hright : 25 * p ≤ 8 * r) (hclass : root4 a p = 3) :
    ∃ M : RankMember (pipelineFrame a ha) (u4 a) q4 (fun c : Fin r => (c : ℕ))
      (fun j : Fin m => r + 2 * (j : ℕ)) (fun j : Fin m => r + 2 * (j : ℕ) + 1) s p,
      (M.price : ℚ) ≤ ((16 / 5 : ℚ) * (r : ℚ) + (-15 / 4 : ℚ) * (p : ℚ)) + 289 + 48 * ((r - s.card : ℕ) : ℚ) := by
  have hp29 : 29 ≤ p := rankPrimeCutoff_ge_twentyNine.trans hp.le
  have hp4 : ¬ p ∣ 4 := by
    intro hd
    have hle := Nat.le_of_dvd (by norm_num : 0 < 4) hd
    omega
  let cert := C3S07_assignment a p r m s ha hp29 hp4 hrp hm1
  have hdata := C3S07_physical_valid a p r m s ha hp hr hodd hrp hm1 hm2 hleft hright hclass hp29 hp4
  have hOk : ∀ x, (cert x).Ok := fun x => (hdata x).1
  have hInt : ∀ x, (cert x).Integral p := fun x => (hdata x).2.1
  have hReal : ∀ x, Realizes (lambdaPoleSplit a p r m ha hp29 hp4 hrp hm1)
      (rowsOf r m s) (colsOf r m s) x (cert x) := fun x => (hdata x).2.2
  have hR0 := C3S07_row_bounds a p r m s ha hp29 hp4 hrp hm1 hleft hright
  have hC0 := C3S07_col_bounds a p r m s ha hp29 hp4 hrp hm1 hleft hright
  have hdepth : (0 : ℚ) ≤ ((r - s.card : ℕ) : ℚ) := Nat.cast_nonneg _
  have hR : ((1 / 10 : ℚ) * (r : ℚ) + (0 / 1 : ℚ) * (p : ℚ)) - (48 + 8 * ((r - s.card : ℕ) : ℚ)) ≤ ((∑ x : ZMod p, (cert x).kr.card : ℕ) : ℚ) ∧
      ((∑ x : ZMod p, (cert x).kr.card : ℕ) : ℚ) ≤ ((1 / 10 : ℚ) * (r : ℚ) + (0 / 1 : ℚ) * (p : ℚ)) + (48 + 8 * ((r - s.card : ℕ) : ℚ)) := by
    constructor <;> linarith [hR0.1, hR0.2]
  have hC : ((1 / 10 : ℚ) * (r : ℚ) + (0 / 1 : ℚ) * (p : ℚ)) - (48 + 8 * ((r - s.card : ℕ) : ℚ)) ≤ ((∑ x : ZMod p, (cert x).kc.card : ℕ) : ℚ) ∧
      ((∑ x : ZMod p, (cert x).kc.card : ℕ) : ℚ) ≤ ((1 / 10 : ℚ) * (r : ℚ) + (0 / 1 : ℚ) * (p : ℚ)) + (48 + 8 * ((r - s.card : ℕ) : ℚ)) := by
    constructor <;> linarith [hC0.1, hC0.2]
  have hf := C3S07_load_facts a p r m s ha hp29 hp4 hrp hm1 hp
  have hv1 : C3S07_V0.1 ∈ S p := rank_rational_mem p C3S07_V0.1 hp (by decide +kernel)
  have hv2 : C3S07_V0.2 ∈ S p := rank_rational_mem p C3S07_V0.2 hp (by decide +kernel)
  have hv : castV p C3S07_V0 ≠ 0 := rank_castV_ne_zero_of_fst p C3S07_V0 hp
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have hm0 := C3S07_V0_matched_lower a p r m s ha hp29 hp4 hrp hm1 hleft hright
  have hMatch : ((-1 / 1 : ℚ) * (r : ℚ) + (15 / 4 : ℚ) * (p : ℚ)) - 2 * (48 + 8 * ((r - s.card : ℕ) : ℚ)) ≤
      (((∑ x : ZMod p, rationalRowMatches (cert x) C3S07_V0) +
        (∑ x : ZMod p, rationalColMatches (cert x) C3S07_V0) : ℕ) : ℚ) := by linarith
  obtain ⟨M, hM⟩ := rank_affine_member a p r m s ha hp29 hp4 hrp hm1 cert hOk hInt hReal
    (fun x => (hf x).1.1) (fun x => (hf x).1.2) C3S07_V0 hv1 hv2 hv
    (fun x => (hf x).2.1) (fun x d hd => ⟨((hf x).2.2 d hd).1, ((hf x).2.2 d hd).2.1⟩)
    (fun x d hd => ((hf x).2.2 d hd).2.2) ((1 / 10 : ℚ) * (r : ℚ) + (0 / 1 : ℚ) * (p : ℚ)) ((-1 / 1 : ℚ) * (r : ℚ) + (15 / 4 : ℚ) * (p : ℚ)) (48 + 8 * ((r - s.card : ℕ) : ℚ)) hR hC hMatch
  exact ⟨M, by linarith⟩
#print axioms C3S07_V0_member
end CatalanCore.Uniform.Bank.Lambda.RankPrice
