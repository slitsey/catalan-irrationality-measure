module

public import CatalanFrames.LambdaMirrorHybrid.MirTrop
public import CatalanFrames.HybCommon.Numer

@[expose] public section

/-!
# Mirror: numerology (`BadInfo mirNInst 4 4`; bad primes `{2, 3}`)

The assembly is the generic `HybCommon.Numer` (`log_Dhyb_le_gen`).
-/

open Finset Filter CatalanCore CatalanCore.Arith CatalanCore.Arith.Hybrid CatalanFrames.LambdaMirror
  CatalanFrames.HybCommon

namespace CatalanFrames.LambdaMirrorHybrid

lemma mir_Bnd (r m : ℕ) : Bnd mirNInst r m = 4 * (r + 2 * m) + 6 := by
  show mirCD.L * (r + 2 * m) + 3 + mirCD.bad.sup id = _
  have : mirCD.bad.sup id = 3 := by
    show ({2, 3} : Finset ℕ).sup id = 3
    decide
  rw [this]
  show 4 * (r + 2 * m) + 3 + 3 = _
  ring

lemma mir_cOf2 : cOf mirNInst 2 = 4 := by
  show (16 : ℕ).factorization 2 = 4
  rw [show (16 : ℕ) = 2 ^ 4 by norm_num, Nat.Prime.factorization_pow Nat.prime_two]
  simp

lemma mir_cOf3 : cOf mirNInst 3 = 0 := by
  show (16 : ℕ).factorization 3 = 0
  rw [show (16 : ℕ) = 2 ^ 4 by norm_num, Nat.Prime.factorization_pow Nat.prime_two]
  simp

lemma mir_cOf_good {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) (h3 : p ≠ 3) : cOf mirNInst p = 0 :=
  cOf_eq_zero mirNInst hp (by simpa [mirNInst, mirInst, HybInst.neg, HybInst.ofSing,
    ContentData.neg, mirCD] using And.intro h2 h3)

lemma mir_cOf_le (p : ℕ) : cOf mirNInst p ≤ 4 := by
  show (16 : ℕ).factorization p ≤ 4
  rw [show (16 : ℕ) = 2 ^ 4 by norm_num, Nat.Prime.factorization_pow Nat.prime_two]
  by_cases h : p = 2
  · subst h; simp
  · simp [Finsupp.single_apply, Ne.symm h]

/-- **The bad-prime numerology of the mirror**: `BadInfo mirNInst 4 4`. -/
lemma mirBad : BadInfo mirNInst 4 4 where
  L_eq := rfl
  Lc_le := le_rfl
  cm_le := le_rfl
  Ebd_le := fun N => cubic_Ebd N
  two_mem := by simp [mirNInst, mirInst, HybInst.neg, HybInst.ofSing, ContentData.neg, mirCD]
  bad_le := fun b hb => by
    simp [mirNInst, mirInst, HybInst.neg, HybInst.ofSing, ContentData.neg, mirCD] at hb; omega
  cOf_le := mir_cOf_le

end CatalanFrames.LambdaMirrorHybrid
