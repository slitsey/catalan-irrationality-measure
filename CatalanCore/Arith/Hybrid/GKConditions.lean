module
public import CatalanCore.Arith.Hybrid.LamEntries
@[expose] public section
namespace CatalanCore.Arith.Hybrid
variable {o p : ℕ} [Fact p.Prime]
/-- Hypotheses of the class-3 GK setting. -/
structure GKS3 (o p r m k : ℕ) : Prop where
  p13 : 13 ≤ p
  hk : 4 * k = p + o ∧ 0 < o ∧ o ≤ 3
  hr : 2 * p + k < r
  hN : r + 2 * m ≤ 3 * p
  hm : 0 < m
  h139 : p ≠ 139
  h37 : p ≠ 37
  h73 : p ≠ 73
  hbig : p ≠ 350972849

lemma GKS3.kp {r m k : ℕ} (S : GKS3 o p r m k) : k < p := by have := S.p13; have := S.hk; omega
lemma GKS3.k0 {r m k : ℕ} (S : GKS3 o p r m k) : 0 < k := by have := S.hk; omega


namespace GK1
/-- Hypotheses of the class-1 GK setting. -/
structure GKS1 (o p r m k : ℕ) : Prop where
  p13 : 13 ≤ p
  hk : 4 * k = 3 * p + o ∧ 0 < o ∧ o ≤ 3
  hr : 2 * p < r
  hN : 4 * (r + 2 * m) ≤ 11 * p + o
  hm : 0 < m
  h1009 : p ≠ 1009
  h8663 : p ≠ 8663

lemma GKS1.kp {r m k : ℕ} (S : GKS1 o p r m k) : k < p := by have := S.p13; have := S.hk; omega
lemma GKS1.k0 {r m k : ℕ} (S : GKS1 o p r m k) : 0 < k := by have := S.hk; omega


end GK1
end CatalanCore.Arith.Hybrid
