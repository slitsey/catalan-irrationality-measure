import CatalanCore.Uniform.Bank.Lambda.RankCount.C3S05
import CatalanCore.Uniform.Content.RankProducer.RationalMatches
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Lambda.RankMatch
open CatalanCore.Uniform.Content.RankProducer RankFibre RankData RankCount
open scoped Classical

def C3S05_V0 : ℚ × ℚ := ((1 / 1 : ℚ), (6619969800313 / 629367000320 : ℚ))

theorem C3S05_V0_row_pointwise (a p r m : ℕ) [Fact p.Prime] (s : Finset (Fin r))
    (ha : a = 1 ∨ a = 3) (hp29 : 29 ≤ p) (hp4 : ¬ p ∣ 4)
    (hrp : r ≤ 5 * p) (hm1 : 10 * m ≤ r + 5) (hleft : 24 * r ≤ 95 * p)
    (hright : 15 * p ≤ 4 * r) (x : ZMod p) :
    rationalRowMatches (C3S05_assignment a p r m s ha hp29 hp4 hrp hm1 x) C3S05_V0 = (if C3S05_test0 r p s x then 1 else 0) := by
  by_cases h0 : C3S05_test0 r p s x
  · rw [C3S05_assignment_on_run0 a p r m s ha hp29 hp4 hrp hm1 hleft hright x h0]
    have hn1 : ¬ C3S05_test1 r p s x := by
      intro hj
      rcases h0 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn2 : ¬ C3S05_test2 r p s x := by
      intro hj
      rcases h0 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn3 : ¬ C3S05_test3 r p s x := by
      intro hj
      rcases h0 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn4 : ¬ C3S05_test4 r p s x := by
      intro hj
      rcases h0 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn5 : ¬ C3S05_test5 r p s x := by
      intro hj
      rcases h0 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn6 : ¬ C3S05_test6 r p s x := by
      intro hj
      rcases h0 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn7 : ¬ C3S05_test7 r p s x := by
      intro hj
      rcases h0 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    simp only [if_pos h0, if_neg hn1, if_neg hn2, if_neg hn3, if_neg hn4, if_neg hn5, if_neg hn6, if_neg hn7]
    decide +kernel
  by_cases h1 : C3S05_test1 r p s x
  · rw [C3S05_assignment_on_run1 a p r m s ha hp29 hp4 hrp hm1 hleft hright x h1]
    have hn2 : ¬ C3S05_test2 r p s x := by
      intro hj
      rcases h1 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn3 : ¬ C3S05_test3 r p s x := by
      intro hj
      rcases h1 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn4 : ¬ C3S05_test4 r p s x := by
      intro hj
      rcases h1 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn5 : ¬ C3S05_test5 r p s x := by
      intro hj
      rcases h1 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn6 : ¬ C3S05_test6 r p s x := by
      intro hj
      rcases h1 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn7 : ¬ C3S05_test7 r p s x := by
      intro hj
      rcases h1 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    simp only [if_neg h0, if_pos h1, if_neg hn2, if_neg hn3, if_neg hn4, if_neg hn5, if_neg hn6, if_neg hn7]
    decide +kernel
  by_cases h2 : C3S05_test2 r p s x
  · rw [C3S05_assignment_on_run2 a p r m s ha hp29 hp4 hrp hm1 hleft hright x h2]
    have hn3 : ¬ C3S05_test3 r p s x := by
      intro hj
      rcases h2 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn4 : ¬ C3S05_test4 r p s x := by
      intro hj
      rcases h2 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn5 : ¬ C3S05_test5 r p s x := by
      intro hj
      rcases h2 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn6 : ¬ C3S05_test6 r p s x := by
      intro hj
      rcases h2 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn7 : ¬ C3S05_test7 r p s x := by
      intro hj
      rcases h2 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    simp only [if_neg h0, if_neg h1, if_pos h2, if_neg hn3, if_neg hn4, if_neg hn5, if_neg hn6, if_neg hn7]
    decide +kernel
  by_cases h3 : C3S05_test3 r p s x
  · rw [C3S05_assignment_on_run3 a p r m s ha hp29 hp4 hrp hm1 hleft hright x h3]
    have hn4 : ¬ C3S05_test4 r p s x := by
      intro hj
      rcases h3 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn5 : ¬ C3S05_test5 r p s x := by
      intro hj
      rcases h3 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn6 : ¬ C3S05_test6 r p s x := by
      intro hj
      rcases h3 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn7 : ¬ C3S05_test7 r p s x := by
      intro hj
      rcases h3 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    simp only [if_neg h0, if_neg h1, if_neg h2, if_pos h3, if_neg hn4, if_neg hn5, if_neg hn6, if_neg hn7]
    decide +kernel
  by_cases h4 : C3S05_test4 r p s x
  · rw [C3S05_assignment_on_run4 a p r m s ha hp29 hp4 hrp hm1 hleft hright x h4]
    have hn5 : ¬ C3S05_test5 r p s x := by
      intro hj
      rcases h4 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn6 : ¬ C3S05_test6 r p s x := by
      intro hj
      rcases h4 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn7 : ¬ C3S05_test7 r p s x := by
      intro hj
      rcases h4 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    simp only [if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_pos h4, if_neg hn5, if_neg hn6, if_neg hn7]
    decide +kernel
  by_cases h5 : C3S05_test5 r p s x
  · rw [C3S05_assignment_on_run5 a p r m s ha hp29 hp4 hrp hm1 hleft hright x h5]
    have hn6 : ¬ C3S05_test6 r p s x := by
      intro hj
      rcases h5 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn7 : ¬ C3S05_test7 r p s x := by
      intro hj
      rcases h5 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    simp only [if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_pos h5, if_neg hn6, if_neg hn7]
    decide +kernel
  by_cases h6 : C3S05_test6 r p s x
  · rw [C3S05_assignment_on_run6 a p r m s ha hp29 hp4 hrp hm1 hleft hright x h6]
    have hn7 : ¬ C3S05_test7 r p s x := by
      intro hj
      rcases h6 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    simp only [if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_pos h6, if_neg hn7]
    decide +kernel
  by_cases h7 : C3S05_test7 r p s x
  · rw [C3S05_assignment_on_run7 a p r m s ha hp29 hp4 hrp hm1 hleft hright x h7]
    simp only [if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6, if_pos h7]
    decide +kernel
  simp only [C3S05_assignment, if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6, if_neg h7]
  rfl

theorem C3S05_V0_row_sum (a p r m : ℕ) [Fact p.Prime] (s : Finset (Fin r))
    (ha : a = 1 ∨ a = 3) (hp29 : 29 ≤ p) (hp4 : ¬ p ∣ 4)
    (hrp : r ≤ 5 * p) (hm1 : 10 * m ≤ r + 5) (hleft : 24 * r ≤ 95 * p)
    (hright : 15 * p ≤ 4 * r) :
    (∑ x : ZMod p, rationalRowMatches (C3S05_assignment a p r m s ha hp29 hp4 hrp hm1 x) C3S05_V0) = C3S05_count0 r p s := by
  calc
    _ = ∑ x : ZMod p, ((if C3S05_test0 r p s x then 1 else 0)) := Finset.sum_congr rfl (fun x _ =>
      C3S05_V0_row_pointwise a p r m s ha hp29 hp4 hrp hm1 hleft hright x)
    _ = _ := by simp [Finset.sum_add_distrib, Finset.sum_boole, C3S05_count0]

theorem C3S05_V0_column_pointwise (a p r m : ℕ) [Fact p.Prime] (s : Finset (Fin r))
    (ha : a = 1 ∨ a = 3) (hp29 : 29 ≤ p) (hp4 : ¬ p ∣ 4)
    (hrp : r ≤ 5 * p) (hm1 : 10 * m ≤ r + 5) (hleft : 24 * r ≤ 95 * p)
    (hright : 15 * p ≤ 4 * r) (x : ZMod p) :
    rationalColMatches (C3S05_assignment a p r m s ha hp29 hp4 hrp hm1 x) C3S05_V0 = (if C3S05_test1 r p s x then 1 else 0) := by
  by_cases h0 : C3S05_test0 r p s x
  · rw [C3S05_assignment_on_run0 a p r m s ha hp29 hp4 hrp hm1 hleft hright x h0]
    have hn1 : ¬ C3S05_test1 r p s x := by
      intro hj
      rcases h0 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn2 : ¬ C3S05_test2 r p s x := by
      intro hj
      rcases h0 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn3 : ¬ C3S05_test3 r p s x := by
      intro hj
      rcases h0 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn4 : ¬ C3S05_test4 r p s x := by
      intro hj
      rcases h0 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn5 : ¬ C3S05_test5 r p s x := by
      intro hj
      rcases h0 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn6 : ¬ C3S05_test6 r p s x := by
      intro hj
      rcases h0 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn7 : ¬ C3S05_test7 r p s x := by
      intro hj
      rcases h0 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    simp only [if_pos h0, if_neg hn1, if_neg hn2, if_neg hn3, if_neg hn4, if_neg hn5, if_neg hn6, if_neg hn7]
    decide +kernel
  by_cases h1 : C3S05_test1 r p s x
  · rw [C3S05_assignment_on_run1 a p r m s ha hp29 hp4 hrp hm1 hleft hright x h1]
    have hn2 : ¬ C3S05_test2 r p s x := by
      intro hj
      rcases h1 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn3 : ¬ C3S05_test3 r p s x := by
      intro hj
      rcases h1 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn4 : ¬ C3S05_test4 r p s x := by
      intro hj
      rcases h1 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn5 : ¬ C3S05_test5 r p s x := by
      intro hj
      rcases h1 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn6 : ¬ C3S05_test6 r p s x := by
      intro hj
      rcases h1 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn7 : ¬ C3S05_test7 r p s x := by
      intro hj
      rcases h1 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    simp only [if_neg h0, if_pos h1, if_neg hn2, if_neg hn3, if_neg hn4, if_neg hn5, if_neg hn6, if_neg hn7]
    decide +kernel
  by_cases h2 : C3S05_test2 r p s x
  · rw [C3S05_assignment_on_run2 a p r m s ha hp29 hp4 hrp hm1 hleft hright x h2]
    have hn3 : ¬ C3S05_test3 r p s x := by
      intro hj
      rcases h2 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn4 : ¬ C3S05_test4 r p s x := by
      intro hj
      rcases h2 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn5 : ¬ C3S05_test5 r p s x := by
      intro hj
      rcases h2 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn6 : ¬ C3S05_test6 r p s x := by
      intro hj
      rcases h2 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn7 : ¬ C3S05_test7 r p s x := by
      intro hj
      rcases h2 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    simp only [if_neg h0, if_neg h1, if_pos h2, if_neg hn3, if_neg hn4, if_neg hn5, if_neg hn6, if_neg hn7]
    decide +kernel
  by_cases h3 : C3S05_test3 r p s x
  · rw [C3S05_assignment_on_run3 a p r m s ha hp29 hp4 hrp hm1 hleft hright x h3]
    have hn4 : ¬ C3S05_test4 r p s x := by
      intro hj
      rcases h3 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn5 : ¬ C3S05_test5 r p s x := by
      intro hj
      rcases h3 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn6 : ¬ C3S05_test6 r p s x := by
      intro hj
      rcases h3 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn7 : ¬ C3S05_test7 r p s x := by
      intro hj
      rcases h3 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    simp only [if_neg h0, if_neg h1, if_neg h2, if_pos h3, if_neg hn4, if_neg hn5, if_neg hn6, if_neg hn7]
    decide +kernel
  by_cases h4 : C3S05_test4 r p s x
  · rw [C3S05_assignment_on_run4 a p r m s ha hp29 hp4 hrp hm1 hleft hright x h4]
    have hn5 : ¬ C3S05_test5 r p s x := by
      intro hj
      rcases h4 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn6 : ¬ C3S05_test6 r p s x := by
      intro hj
      rcases h4 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn7 : ¬ C3S05_test7 r p s x := by
      intro hj
      rcases h4 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    simp only [if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_pos h4, if_neg hn5, if_neg hn6, if_neg hn7]
    decide +kernel
  by_cases h5 : C3S05_test5 r p s x
  · rw [C3S05_assignment_on_run5 a p r m s ha hp29 hp4 hrp hm1 hleft hright x h5]
    have hn6 : ¬ C3S05_test6 r p s x := by
      intro hj
      rcases h5 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn7 : ¬ C3S05_test7 r p s x := by
      intro hj
      rcases h5 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    simp only [if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_pos h5, if_neg hn6, if_neg hn7]
    decide +kernel
  by_cases h6 : C3S05_test6 r p s x
  · rw [C3S05_assignment_on_run6 a p r m s ha hp29 hp4 hrp hm1 hleft hright x h6]
    have hn7 : ¬ C3S05_test7 r p s x := by
      intro hj
      rcases h6 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    simp only [if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_pos h6, if_neg hn7]
    decide +kernel
  by_cases h7 : C3S05_test7 r p s x
  · rw [C3S05_assignment_on_run7 a p r m s ha hp29 hp4 hrp hm1 hleft hright x h7]
    simp only [if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6, if_pos h7]
    decide +kernel
  simp only [C3S05_assignment, if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6, if_neg h7]
  rfl

theorem C3S05_V0_column_sum (a p r m : ℕ) [Fact p.Prime] (s : Finset (Fin r))
    (ha : a = 1 ∨ a = 3) (hp29 : 29 ≤ p) (hp4 : ¬ p ∣ 4)
    (hrp : r ≤ 5 * p) (hm1 : 10 * m ≤ r + 5) (hleft : 24 * r ≤ 95 * p)
    (hright : 15 * p ≤ 4 * r) :
    (∑ x : ZMod p, rationalColMatches (C3S05_assignment a p r m s ha hp29 hp4 hrp hm1 x) C3S05_V0) = C3S05_count1 r p s := by
  calc
    _ = ∑ x : ZMod p, ((if C3S05_test1 r p s x then 1 else 0)) := Finset.sum_congr rfl (fun x _ =>
      C3S05_V0_column_pointwise a p r m s ha hp29 hp4 hrp hm1 hleft hright x)
    _ = _ := by simp [Finset.sum_add_distrib, Finset.sum_boole, C3S05_count1]

theorem C3S05_V0_matched_lower (a p r m : ℕ) [Fact p.Prime] (s : Finset (Fin r))
    (ha : a = 1 ∨ a = 3) (hp29 : 29 ≤ p) (hp4 : ¬ p ∣ 4)
    (hrp : r ≤ 5 * p) (hm1 : 10 * m ≤ r + 5) (hleft : 24 * r ≤ 95 * p)
    (hright : 15 * p ≤ 4 * r) :
    ((6 / 5 : ℚ) * (r : ℚ) + (-4 / 1 : ℚ) * (p : ℚ)) - (96 + 16 * ((r - s.card : ℕ) : ℚ)) ≤
      (((∑ x : ZMod p, rationalRowMatches (C3S05_assignment a p r m s ha hp29 hp4 hrp hm1 x) C3S05_V0) +
        (∑ x : ZMod p, rationalColMatches (C3S05_assignment a p r m s ha hp29 hp4 hrp hm1 x) C3S05_V0) : ℕ) : ℚ) := by
  rw [C3S05_V0_row_sum a p r m s ha hp29 hp4 hrp hm1 hleft hright,
    C3S05_V0_column_sum a p r m s ha hp29 hp4 hrp hm1 hleft hright]
  push_cast
  have hdepth : (0 : ℚ) ≤ ((r - s.card : ℕ) : ℚ) := Nat.cast_nonneg _
  have h0 := C3S05_count_bounds0 r p s hleft hright
  have h1 := C3S05_count_bounds1 r p s hleft hright
  linarith [h0.1, h0.2, h1.1, h1.2]

#print axioms C3S05_V0_matched_lower
end CatalanCore.Uniform.Bank.Lambda.RankMatch
