import CatalanCore.Uniform.Bank.Lambda.RankCount.C1S04
import CatalanCore.Uniform.Content.RankProducer.RationalMatches
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Lambda.RankMatch
open CatalanCore.Uniform.Content.RankProducer RankFibre RankData RankCount
open scoped Classical

def C1S04_V0 : ℚ × ℚ := ((1 / 1 : ℚ), (-2123218450145081683903413 / 573459436986500156900416 : ℚ))

theorem C1S04_V0_row_pointwise (a p r m : ℕ) [Fact p.Prime] (s : Finset (Fin r))
    (ha : a = 1 ∨ a = 3) (hp29 : 29 ≤ p) (hp4 : ¬ p ∣ 4)
    (hrp : r ≤ 5 * p) (hm1 : 10 * m ≤ r + 5) (hleft : 1 * r ≤ 4 * p)
    (hright : 85 * p ≤ 24 * r) (x : ZMod p) :
    rationalRowMatches (C1S04_assignment a p r m s ha hp29 hp4 hrp hm1 x) C1S04_V0 = (if C1S04_test2 r p s x then 1 else 0) := by
  by_cases h0 : C1S04_test0 r p s x
  · rw [C1S04_assignment_on_run0 a p r m s ha hp29 hp4 hrp hm1 hleft hright x h0]
    have hn1 : ¬ C1S04_test1 r p s x := by
      intro hj
      rcases h0 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn2 : ¬ C1S04_test2 r p s x := by
      intro hj
      rcases h0 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn3 : ¬ C1S04_test3 r p s x := by
      intro hj
      rcases h0 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn4 : ¬ C1S04_test4 r p s x := by
      intro hj
      rcases h0 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn5 : ¬ C1S04_test5 r p s x := by
      intro hj
      rcases h0 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn6 : ¬ C1S04_test6 r p s x := by
      intro hj
      rcases h0 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn7 : ¬ C1S04_test7 r p s x := by
      intro hj
      rcases h0 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    simp only [if_pos h0, if_neg hn1, if_neg hn2, if_neg hn3, if_neg hn4, if_neg hn5, if_neg hn6, if_neg hn7]
    decide +kernel
  by_cases h1 : C1S04_test1 r p s x
  · rw [C1S04_assignment_on_run1 a p r m s ha hp29 hp4 hrp hm1 hleft hright x h1]
    have hn2 : ¬ C1S04_test2 r p s x := by
      intro hj
      rcases h1 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn3 : ¬ C1S04_test3 r p s x := by
      intro hj
      rcases h1 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn4 : ¬ C1S04_test4 r p s x := by
      intro hj
      rcases h1 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn5 : ¬ C1S04_test5 r p s x := by
      intro hj
      rcases h1 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn6 : ¬ C1S04_test6 r p s x := by
      intro hj
      rcases h1 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn7 : ¬ C1S04_test7 r p s x := by
      intro hj
      rcases h1 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    simp only [if_neg h0, if_pos h1, if_neg hn2, if_neg hn3, if_neg hn4, if_neg hn5, if_neg hn6, if_neg hn7]
    decide +kernel
  by_cases h2 : C1S04_test2 r p s x
  · rw [C1S04_assignment_on_run2 a p r m s ha hp29 hp4 hrp hm1 hleft hright x h2]
    have hn3 : ¬ C1S04_test3 r p s x := by
      intro hj
      rcases h2 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn4 : ¬ C1S04_test4 r p s x := by
      intro hj
      rcases h2 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn5 : ¬ C1S04_test5 r p s x := by
      intro hj
      rcases h2 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn6 : ¬ C1S04_test6 r p s x := by
      intro hj
      rcases h2 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn7 : ¬ C1S04_test7 r p s x := by
      intro hj
      rcases h2 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    simp only [if_neg h0, if_neg h1, if_pos h2, if_neg hn3, if_neg hn4, if_neg hn5, if_neg hn6, if_neg hn7]
    decide +kernel
  by_cases h3 : C1S04_test3 r p s x
  · rw [C1S04_assignment_on_run3 a p r m s ha hp29 hp4 hrp hm1 hleft hright x h3]
    have hn4 : ¬ C1S04_test4 r p s x := by
      intro hj
      rcases h3 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn5 : ¬ C1S04_test5 r p s x := by
      intro hj
      rcases h3 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn6 : ¬ C1S04_test6 r p s x := by
      intro hj
      rcases h3 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn7 : ¬ C1S04_test7 r p s x := by
      intro hj
      rcases h3 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    simp only [if_neg h0, if_neg h1, if_neg h2, if_pos h3, if_neg hn4, if_neg hn5, if_neg hn6, if_neg hn7]
    decide +kernel
  by_cases h4 : C1S04_test4 r p s x
  · rw [C1S04_assignment_on_run4 a p r m s ha hp29 hp4 hrp hm1 hleft hright x h4]
    have hn5 : ¬ C1S04_test5 r p s x := by
      intro hj
      rcases h4 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn6 : ¬ C1S04_test6 r p s x := by
      intro hj
      rcases h4 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn7 : ¬ C1S04_test7 r p s x := by
      intro hj
      rcases h4 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    simp only [if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_pos h4, if_neg hn5, if_neg hn6, if_neg hn7]
    decide +kernel
  by_cases h5 : C1S04_test5 r p s x
  · rw [C1S04_assignment_on_run5 a p r m s ha hp29 hp4 hrp hm1 hleft hright x h5]
    have hn6 : ¬ C1S04_test6 r p s x := by
      intro hj
      rcases h5 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn7 : ¬ C1S04_test7 r p s x := by
      intro hj
      rcases h5 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    simp only [if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_pos h5, if_neg hn6, if_neg hn7]
    decide +kernel
  by_cases h6 : C1S04_test6 r p s x
  · rw [C1S04_assignment_on_run6 a p r m s ha hp29 hp4 hrp hm1 hleft hright x h6]
    have hn7 : ¬ C1S04_test7 r p s x := by
      intro hj
      rcases h6 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    simp only [if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_pos h6, if_neg hn7]
    decide +kernel
  by_cases h7 : C1S04_test7 r p s x
  · rw [C1S04_assignment_on_run7 a p r m s ha hp29 hp4 hrp hm1 hleft hright x h7]
    simp only [if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6, if_pos h7]
    decide +kernel
  simp only [C1S04_assignment, if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6, if_neg h7]
  rfl

theorem C1S04_V0_row_sum (a p r m : ℕ) [Fact p.Prime] (s : Finset (Fin r))
    (ha : a = 1 ∨ a = 3) (hp29 : 29 ≤ p) (hp4 : ¬ p ∣ 4)
    (hrp : r ≤ 5 * p) (hm1 : 10 * m ≤ r + 5) (hleft : 1 * r ≤ 4 * p)
    (hright : 85 * p ≤ 24 * r) :
    (∑ x : ZMod p, rationalRowMatches (C1S04_assignment a p r m s ha hp29 hp4 hrp hm1 x) C1S04_V0) = C1S04_count2 r p s := by
  calc
    _ = ∑ x : ZMod p, ((if C1S04_test2 r p s x then 1 else 0)) := Finset.sum_congr rfl (fun x _ =>
      C1S04_V0_row_pointwise a p r m s ha hp29 hp4 hrp hm1 hleft hright x)
    _ = _ := by simp [Finset.sum_add_distrib, Finset.sum_boole, C1S04_count2]

theorem C1S04_V0_column_pointwise (a p r m : ℕ) [Fact p.Prime] (s : Finset (Fin r))
    (ha : a = 1 ∨ a = 3) (hp29 : 29 ≤ p) (hp4 : ¬ p ∣ 4)
    (hrp : r ≤ 5 * p) (hm1 : 10 * m ≤ r + 5) (hleft : 1 * r ≤ 4 * p)
    (hright : 85 * p ≤ 24 * r) (x : ZMod p) :
    rationalColMatches (C1S04_assignment a p r m s ha hp29 hp4 hrp hm1 x) C1S04_V0 = (if C1S04_test3 r p s x then 1 else 0) := by
  by_cases h0 : C1S04_test0 r p s x
  · rw [C1S04_assignment_on_run0 a p r m s ha hp29 hp4 hrp hm1 hleft hright x h0]
    have hn1 : ¬ C1S04_test1 r p s x := by
      intro hj
      rcases h0 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn2 : ¬ C1S04_test2 r p s x := by
      intro hj
      rcases h0 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn3 : ¬ C1S04_test3 r p s x := by
      intro hj
      rcases h0 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn4 : ¬ C1S04_test4 r p s x := by
      intro hj
      rcases h0 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn5 : ¬ C1S04_test5 r p s x := by
      intro hj
      rcases h0 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn6 : ¬ C1S04_test6 r p s x := by
      intro hj
      rcases h0 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn7 : ¬ C1S04_test7 r p s x := by
      intro hj
      rcases h0 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    simp only [if_pos h0, if_neg hn1, if_neg hn2, if_neg hn3, if_neg hn4, if_neg hn5, if_neg hn6, if_neg hn7]
    decide +kernel
  by_cases h1 : C1S04_test1 r p s x
  · rw [C1S04_assignment_on_run1 a p r m s ha hp29 hp4 hrp hm1 hleft hright x h1]
    have hn2 : ¬ C1S04_test2 r p s x := by
      intro hj
      rcases h1 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn3 : ¬ C1S04_test3 r p s x := by
      intro hj
      rcases h1 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn4 : ¬ C1S04_test4 r p s x := by
      intro hj
      rcases h1 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn5 : ¬ C1S04_test5 r p s x := by
      intro hj
      rcases h1 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn6 : ¬ C1S04_test6 r p s x := by
      intro hj
      rcases h1 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn7 : ¬ C1S04_test7 r p s x := by
      intro hj
      rcases h1 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    simp only [if_neg h0, if_pos h1, if_neg hn2, if_neg hn3, if_neg hn4, if_neg hn5, if_neg hn6, if_neg hn7]
    decide +kernel
  by_cases h2 : C1S04_test2 r p s x
  · rw [C1S04_assignment_on_run2 a p r m s ha hp29 hp4 hrp hm1 hleft hright x h2]
    have hn3 : ¬ C1S04_test3 r p s x := by
      intro hj
      rcases h2 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn4 : ¬ C1S04_test4 r p s x := by
      intro hj
      rcases h2 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn5 : ¬ C1S04_test5 r p s x := by
      intro hj
      rcases h2 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn6 : ¬ C1S04_test6 r p s x := by
      intro hj
      rcases h2 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn7 : ¬ C1S04_test7 r p s x := by
      intro hj
      rcases h2 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    simp only [if_neg h0, if_neg h1, if_pos h2, if_neg hn3, if_neg hn4, if_neg hn5, if_neg hn6, if_neg hn7]
    decide +kernel
  by_cases h3 : C1S04_test3 r p s x
  · rw [C1S04_assignment_on_run3 a p r m s ha hp29 hp4 hrp hm1 hleft hright x h3]
    have hn4 : ¬ C1S04_test4 r p s x := by
      intro hj
      rcases h3 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn5 : ¬ C1S04_test5 r p s x := by
      intro hj
      rcases h3 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn6 : ¬ C1S04_test6 r p s x := by
      intro hj
      rcases h3 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn7 : ¬ C1S04_test7 r p s x := by
      intro hj
      rcases h3 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    simp only [if_neg h0, if_neg h1, if_neg h2, if_pos h3, if_neg hn4, if_neg hn5, if_neg hn6, if_neg hn7]
    decide +kernel
  by_cases h4 : C1S04_test4 r p s x
  · rw [C1S04_assignment_on_run4 a p r m s ha hp29 hp4 hrp hm1 hleft hright x h4]
    have hn5 : ¬ C1S04_test5 r p s x := by
      intro hj
      rcases h4 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn6 : ¬ C1S04_test6 r p s x := by
      intro hj
      rcases h4 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn7 : ¬ C1S04_test7 r p s x := by
      intro hj
      rcases h4 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    simp only [if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_pos h4, if_neg hn5, if_neg hn6, if_neg hn7]
    decide +kernel
  by_cases h5 : C1S04_test5 r p s x
  · rw [C1S04_assignment_on_run5 a p r m s ha hp29 hp4 hrp hm1 hleft hright x h5]
    have hn6 : ¬ C1S04_test6 r p s x := by
      intro hj
      rcases h5 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn7 : ¬ C1S04_test7 r p s x := by
      intro hj
      rcases h5 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    simp only [if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_pos h5, if_neg hn6, if_neg hn7]
    decide +kernel
  by_cases h6 : C1S04_test6 r p s x
  · rw [C1S04_assignment_on_run6 a p r m s ha hp29 hp4 hrp hm1 hleft hright x h6]
    have hn7 : ¬ C1S04_test7 r p s x := by
      intro hj
      rcases h6 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    simp only [if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_pos h6, if_neg hn7]
    decide +kernel
  by_cases h7 : C1S04_test7 r p s x
  · rw [C1S04_assignment_on_run7 a p r m s ha hp29 hp4 hrp hm1 hleft hright x h7]
    simp only [if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6, if_pos h7]
    decide +kernel
  simp only [C1S04_assignment, if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6, if_neg h7]
  rfl

theorem C1S04_V0_column_sum (a p r m : ℕ) [Fact p.Prime] (s : Finset (Fin r))
    (ha : a = 1 ∨ a = 3) (hp29 : 29 ≤ p) (hp4 : ¬ p ∣ 4)
    (hrp : r ≤ 5 * p) (hm1 : 10 * m ≤ r + 5) (hleft : 1 * r ≤ 4 * p)
    (hright : 85 * p ≤ 24 * r) :
    (∑ x : ZMod p, rationalColMatches (C1S04_assignment a p r m s ha hp29 hp4 hrp hm1 x) C1S04_V0) = C1S04_count3 r p s := by
  calc
    _ = ∑ x : ZMod p, ((if C1S04_test3 r p s x then 1 else 0)) := Finset.sum_congr rfl (fun x _ =>
      C1S04_V0_column_pointwise a p r m s ha hp29 hp4 hrp hm1 hleft hright x)
    _ = _ := by simp [Finset.sum_add_distrib, Finset.sum_boole, C1S04_count3]

theorem C1S04_V0_matched_lower (a p r m : ℕ) [Fact p.Prime] (s : Finset (Fin r))
    (ha : a = 1 ∨ a = 3) (hp29 : 29 ≤ p) (hp4 : ¬ p ∣ 4)
    (hrp : r ≤ 5 * p) (hm1 : 10 * m ≤ r + 5) (hleft : 1 * r ≤ 4 * p)
    (hright : 85 * p ≤ 24 * r) :
    ((6 / 5 : ℚ) * (r : ℚ) + (-17 / 4 : ℚ) * (p : ℚ)) - (96 + 16 * ((r - s.card : ℕ) : ℚ)) ≤
      (((∑ x : ZMod p, rationalRowMatches (C1S04_assignment a p r m s ha hp29 hp4 hrp hm1 x) C1S04_V0) +
        (∑ x : ZMod p, rationalColMatches (C1S04_assignment a p r m s ha hp29 hp4 hrp hm1 x) C1S04_V0) : ℕ) : ℚ) := by
  rw [C1S04_V0_row_sum a p r m s ha hp29 hp4 hrp hm1 hleft hright,
    C1S04_V0_column_sum a p r m s ha hp29 hp4 hrp hm1 hleft hright]
  push_cast
  have hdepth : (0 : ℚ) ≤ ((r - s.card : ℕ) : ℚ) := Nat.cast_nonneg _
  have h2 := C1S04_count_bounds2 r p s hleft hright
  have h3 := C1S04_count_bounds3 r p s hleft hright
  linarith [h2.1, h2.2, h3.1, h3.2]

#print axioms C1S04_V0_matched_lower

def C1S04_V1 : ℚ × ℚ := ((1 / 1 : ℚ), (-9066989195663 / 2439392450783 : ℚ))

theorem C1S04_V1_row_pointwise (a p r m : ℕ) [Fact p.Prime] (s : Finset (Fin r))
    (ha : a = 1 ∨ a = 3) (hp29 : 29 ≤ p) (hp4 : ¬ p ∣ 4)
    (hrp : r ≤ 5 * p) (hm1 : 10 * m ≤ r + 5) (hleft : 1 * r ≤ 4 * p)
    (hright : 85 * p ≤ 24 * r) (x : ZMod p) :
    rationalRowMatches (C1S04_assignment a p r m s ha hp29 hp4 hrp hm1 x) C1S04_V1 = (if C1S04_test7 r p s x then 1 else 0) := by
  by_cases h0 : C1S04_test0 r p s x
  · rw [C1S04_assignment_on_run0 a p r m s ha hp29 hp4 hrp hm1 hleft hright x h0]
    have hn1 : ¬ C1S04_test1 r p s x := by
      intro hj
      rcases h0 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn2 : ¬ C1S04_test2 r p s x := by
      intro hj
      rcases h0 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn3 : ¬ C1S04_test3 r p s x := by
      intro hj
      rcases h0 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn4 : ¬ C1S04_test4 r p s x := by
      intro hj
      rcases h0 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn5 : ¬ C1S04_test5 r p s x := by
      intro hj
      rcases h0 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn6 : ¬ C1S04_test6 r p s x := by
      intro hj
      rcases h0 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn7 : ¬ C1S04_test7 r p s x := by
      intro hj
      rcases h0 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    simp only [if_pos h0, if_neg hn1, if_neg hn2, if_neg hn3, if_neg hn4, if_neg hn5, if_neg hn6, if_neg hn7]
    decide +kernel
  by_cases h1 : C1S04_test1 r p s x
  · rw [C1S04_assignment_on_run1 a p r m s ha hp29 hp4 hrp hm1 hleft hright x h1]
    have hn2 : ¬ C1S04_test2 r p s x := by
      intro hj
      rcases h1 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn3 : ¬ C1S04_test3 r p s x := by
      intro hj
      rcases h1 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn4 : ¬ C1S04_test4 r p s x := by
      intro hj
      rcases h1 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn5 : ¬ C1S04_test5 r p s x := by
      intro hj
      rcases h1 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn6 : ¬ C1S04_test6 r p s x := by
      intro hj
      rcases h1 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn7 : ¬ C1S04_test7 r p s x := by
      intro hj
      rcases h1 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    simp only [if_neg h0, if_pos h1, if_neg hn2, if_neg hn3, if_neg hn4, if_neg hn5, if_neg hn6, if_neg hn7]
    decide +kernel
  by_cases h2 : C1S04_test2 r p s x
  · rw [C1S04_assignment_on_run2 a p r m s ha hp29 hp4 hrp hm1 hleft hright x h2]
    have hn3 : ¬ C1S04_test3 r p s x := by
      intro hj
      rcases h2 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn4 : ¬ C1S04_test4 r p s x := by
      intro hj
      rcases h2 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn5 : ¬ C1S04_test5 r p s x := by
      intro hj
      rcases h2 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn6 : ¬ C1S04_test6 r p s x := by
      intro hj
      rcases h2 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn7 : ¬ C1S04_test7 r p s x := by
      intro hj
      rcases h2 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    simp only [if_neg h0, if_neg h1, if_pos h2, if_neg hn3, if_neg hn4, if_neg hn5, if_neg hn6, if_neg hn7]
    decide +kernel
  by_cases h3 : C1S04_test3 r p s x
  · rw [C1S04_assignment_on_run3 a p r m s ha hp29 hp4 hrp hm1 hleft hright x h3]
    have hn4 : ¬ C1S04_test4 r p s x := by
      intro hj
      rcases h3 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn5 : ¬ C1S04_test5 r p s x := by
      intro hj
      rcases h3 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn6 : ¬ C1S04_test6 r p s x := by
      intro hj
      rcases h3 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn7 : ¬ C1S04_test7 r p s x := by
      intro hj
      rcases h3 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    simp only [if_neg h0, if_neg h1, if_neg h2, if_pos h3, if_neg hn4, if_neg hn5, if_neg hn6, if_neg hn7]
    decide +kernel
  by_cases h4 : C1S04_test4 r p s x
  · rw [C1S04_assignment_on_run4 a p r m s ha hp29 hp4 hrp hm1 hleft hright x h4]
    have hn5 : ¬ C1S04_test5 r p s x := by
      intro hj
      rcases h4 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn6 : ¬ C1S04_test6 r p s x := by
      intro hj
      rcases h4 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn7 : ¬ C1S04_test7 r p s x := by
      intro hj
      rcases h4 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    simp only [if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_pos h4, if_neg hn5, if_neg hn6, if_neg hn7]
    decide +kernel
  by_cases h5 : C1S04_test5 r p s x
  · rw [C1S04_assignment_on_run5 a p r m s ha hp29 hp4 hrp hm1 hleft hright x h5]
    have hn6 : ¬ C1S04_test6 r p s x := by
      intro hj
      rcases h5 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn7 : ¬ C1S04_test7 r p s x := by
      intro hj
      rcases h5 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    simp only [if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_pos h5, if_neg hn6, if_neg hn7]
    decide +kernel
  by_cases h6 : C1S04_test6 r p s x
  · rw [C1S04_assignment_on_run6 a p r m s ha hp29 hp4 hrp hm1 hleft hright x h6]
    have hn7 : ¬ C1S04_test7 r p s x := by
      intro hj
      rcases h6 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    simp only [if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_pos h6, if_neg hn7]
    decide +kernel
  by_cases h7 : C1S04_test7 r p s x
  · rw [C1S04_assignment_on_run7 a p r m s ha hp29 hp4 hrp hm1 hleft hright x h7]
    simp only [if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6, if_pos h7]
    decide +kernel
  simp only [C1S04_assignment, if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6, if_neg h7]
  rfl

theorem C1S04_V1_row_sum (a p r m : ℕ) [Fact p.Prime] (s : Finset (Fin r))
    (ha : a = 1 ∨ a = 3) (hp29 : 29 ≤ p) (hp4 : ¬ p ∣ 4)
    (hrp : r ≤ 5 * p) (hm1 : 10 * m ≤ r + 5) (hleft : 1 * r ≤ 4 * p)
    (hright : 85 * p ≤ 24 * r) :
    (∑ x : ZMod p, rationalRowMatches (C1S04_assignment a p r m s ha hp29 hp4 hrp hm1 x) C1S04_V1) = C1S04_count7 r p s := by
  calc
    _ = ∑ x : ZMod p, ((if C1S04_test7 r p s x then 1 else 0)) := Finset.sum_congr rfl (fun x _ =>
      C1S04_V1_row_pointwise a p r m s ha hp29 hp4 hrp hm1 hleft hright x)
    _ = _ := by simp [Finset.sum_add_distrib, Finset.sum_boole, C1S04_count7]

theorem C1S04_V1_column_pointwise (a p r m : ℕ) [Fact p.Prime] (s : Finset (Fin r))
    (ha : a = 1 ∨ a = 3) (hp29 : 29 ≤ p) (hp4 : ¬ p ∣ 4)
    (hrp : r ≤ 5 * p) (hm1 : 10 * m ≤ r + 5) (hleft : 1 * r ≤ 4 * p)
    (hright : 85 * p ≤ 24 * r) (x : ZMod p) :
    rationalColMatches (C1S04_assignment a p r m s ha hp29 hp4 hrp hm1 x) C1S04_V1 = (if C1S04_test6 r p s x then 1 else 0) := by
  by_cases h0 : C1S04_test0 r p s x
  · rw [C1S04_assignment_on_run0 a p r m s ha hp29 hp4 hrp hm1 hleft hright x h0]
    have hn1 : ¬ C1S04_test1 r p s x := by
      intro hj
      rcases h0 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn2 : ¬ C1S04_test2 r p s x := by
      intro hj
      rcases h0 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn3 : ¬ C1S04_test3 r p s x := by
      intro hj
      rcases h0 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn4 : ¬ C1S04_test4 r p s x := by
      intro hj
      rcases h0 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn5 : ¬ C1S04_test5 r p s x := by
      intro hj
      rcases h0 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn6 : ¬ C1S04_test6 r p s x := by
      intro hj
      rcases h0 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn7 : ¬ C1S04_test7 r p s x := by
      intro hj
      rcases h0 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    simp only [if_pos h0, if_neg hn1, if_neg hn2, if_neg hn3, if_neg hn4, if_neg hn5, if_neg hn6, if_neg hn7]
    decide +kernel
  by_cases h1 : C1S04_test1 r p s x
  · rw [C1S04_assignment_on_run1 a p r m s ha hp29 hp4 hrp hm1 hleft hright x h1]
    have hn2 : ¬ C1S04_test2 r p s x := by
      intro hj
      rcases h1 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn3 : ¬ C1S04_test3 r p s x := by
      intro hj
      rcases h1 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn4 : ¬ C1S04_test4 r p s x := by
      intro hj
      rcases h1 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn5 : ¬ C1S04_test5 r p s x := by
      intro hj
      rcases h1 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn6 : ¬ C1S04_test6 r p s x := by
      intro hj
      rcases h1 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn7 : ¬ C1S04_test7 r p s x := by
      intro hj
      rcases h1 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    simp only [if_neg h0, if_pos h1, if_neg hn2, if_neg hn3, if_neg hn4, if_neg hn5, if_neg hn6, if_neg hn7]
    decide +kernel
  by_cases h2 : C1S04_test2 r p s x
  · rw [C1S04_assignment_on_run2 a p r m s ha hp29 hp4 hrp hm1 hleft hright x h2]
    have hn3 : ¬ C1S04_test3 r p s x := by
      intro hj
      rcases h2 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn4 : ¬ C1S04_test4 r p s x := by
      intro hj
      rcases h2 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn5 : ¬ C1S04_test5 r p s x := by
      intro hj
      rcases h2 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn6 : ¬ C1S04_test6 r p s x := by
      intro hj
      rcases h2 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn7 : ¬ C1S04_test7 r p s x := by
      intro hj
      rcases h2 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    simp only [if_neg h0, if_neg h1, if_pos h2, if_neg hn3, if_neg hn4, if_neg hn5, if_neg hn6, if_neg hn7]
    decide +kernel
  by_cases h3 : C1S04_test3 r p s x
  · rw [C1S04_assignment_on_run3 a p r m s ha hp29 hp4 hrp hm1 hleft hright x h3]
    have hn4 : ¬ C1S04_test4 r p s x := by
      intro hj
      rcases h3 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn5 : ¬ C1S04_test5 r p s x := by
      intro hj
      rcases h3 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn6 : ¬ C1S04_test6 r p s x := by
      intro hj
      rcases h3 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn7 : ¬ C1S04_test7 r p s x := by
      intro hj
      rcases h3 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    simp only [if_neg h0, if_neg h1, if_neg h2, if_pos h3, if_neg hn4, if_neg hn5, if_neg hn6, if_neg hn7]
    decide +kernel
  by_cases h4 : C1S04_test4 r p s x
  · rw [C1S04_assignment_on_run4 a p r m s ha hp29 hp4 hrp hm1 hleft hright x h4]
    have hn5 : ¬ C1S04_test5 r p s x := by
      intro hj
      rcases h4 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn6 : ¬ C1S04_test6 r p s x := by
      intro hj
      rcases h4 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn7 : ¬ C1S04_test7 r p s x := by
      intro hj
      rcases h4 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    simp only [if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_pos h4, if_neg hn5, if_neg hn6, if_neg hn7]
    decide +kernel
  by_cases h5 : C1S04_test5 r p s x
  · rw [C1S04_assignment_on_run5 a p r m s ha hp29 hp4 hrp hm1 hleft hright x h5]
    have hn6 : ¬ C1S04_test6 r p s x := by
      intro hj
      rcases h5 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn7 : ¬ C1S04_test7 r p s x := by
      intro hj
      rcases h5 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    simp only [if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_pos h5, if_neg hn6, if_neg hn7]
    decide +kernel
  by_cases h6 : C1S04_test6 r p s x
  · rw [C1S04_assignment_on_run6 a p r m s ha hp29 hp4 hrp hm1 hleft hright x h6]
    have hn7 : ¬ C1S04_test7 r p s x := by
      intro hj
      rcases h6 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    simp only [if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_pos h6, if_neg hn7]
    decide +kernel
  by_cases h7 : C1S04_test7 r p s x
  · rw [C1S04_assignment_on_run7 a p r m s ha hp29 hp4 hrp hm1 hleft hright x h7]
    simp only [if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6, if_pos h7]
    decide +kernel
  simp only [C1S04_assignment, if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6, if_neg h7]
  rfl

theorem C1S04_V1_column_sum (a p r m : ℕ) [Fact p.Prime] (s : Finset (Fin r))
    (ha : a = 1 ∨ a = 3) (hp29 : 29 ≤ p) (hp4 : ¬ p ∣ 4)
    (hrp : r ≤ 5 * p) (hm1 : 10 * m ≤ r + 5) (hleft : 1 * r ≤ 4 * p)
    (hright : 85 * p ≤ 24 * r) :
    (∑ x : ZMod p, rationalColMatches (C1S04_assignment a p r m s ha hp29 hp4 hrp hm1 x) C1S04_V1) = C1S04_count6 r p s := by
  calc
    _ = ∑ x : ZMod p, ((if C1S04_test6 r p s x then 1 else 0)) := Finset.sum_congr rfl (fun x _ =>
      C1S04_V1_column_pointwise a p r m s ha hp29 hp4 hrp hm1 hleft hright x)
    _ = _ := by simp [Finset.sum_add_distrib, Finset.sum_boole, C1S04_count6]

theorem C1S04_V1_matched_lower (a p r m : ℕ) [Fact p.Prime] (s : Finset (Fin r))
    (ha : a = 1 ∨ a = 3) (hp29 : 29 ≤ p) (hp4 : ¬ p ∣ 4)
    (hrp : r ≤ 5 * p) (hm1 : 10 * m ≤ r + 5) (hleft : 1 * r ≤ 4 * p)
    (hright : 85 * p ≤ 24 * r) :
    ((-1 / 1 : ℚ) * (r : ℚ) + (4 / 1 : ℚ) * (p : ℚ)) - (96 + 16 * ((r - s.card : ℕ) : ℚ)) ≤
      (((∑ x : ZMod p, rationalRowMatches (C1S04_assignment a p r m s ha hp29 hp4 hrp hm1 x) C1S04_V1) +
        (∑ x : ZMod p, rationalColMatches (C1S04_assignment a p r m s ha hp29 hp4 hrp hm1 x) C1S04_V1) : ℕ) : ℚ) := by
  rw [C1S04_V1_row_sum a p r m s ha hp29 hp4 hrp hm1 hleft hright,
    C1S04_V1_column_sum a p r m s ha hp29 hp4 hrp hm1 hleft hright]
  push_cast
  have hdepth : (0 : ℚ) ≤ ((r - s.card : ℕ) : ℚ) := Nat.cast_nonneg _
  have h6 := C1S04_count_bounds6 r p s hleft hright
  have h7 := C1S04_count_bounds7 r p s hleft hright
  linarith [h6.1, h6.2, h7.1, h7.2]

#print axioms C1S04_V1_matched_lower
end CatalanCore.Uniform.Bank.Lambda.RankMatch
