import CatalanCore.Uniform.Content.RankProducer.Price
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Lambda

/-- The rank producer's natural-number accounting for a line witness. CM and RM
count column/row load fibres on that line. K is the balanced number of kills. -/
theorem rank_line_price_bound (H K F C D CM RM : ℕ)
    (hK : K ≤ H) (hCM : CM ≤ K) (hRM : RM ≤ K)
    (hC : CM ≤ C) (hD : D + RM ≤ K) :
    H + (H - K) - (F + (C - D)) + max K (CM + RM) ≤ 2 * H := by
  omega

/-- Kernel certificates with at most one kill per side have the recorded
zero/full/line envelope: a line contributes w-K, and the natural price is 2H-K. -/
theorem rank_line_gain_identity (K CM RM : ℕ) :
    K + ((CM + RM) - K) = max K (CM + RM) := by omega

#print axioms rank_line_price_bound
#print axioms rank_line_gain_identity
end CatalanCore.Uniform.Bank.Lambda
