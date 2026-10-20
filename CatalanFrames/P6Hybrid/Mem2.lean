module

public import CatalanFrames.P6Hybrid.Admissible
public import CatalanFrames.HybCommon.TopSum

@[expose] public section

/-!
# P6 hybrid: the second-member content `p6_mem2Content`

`Mem2ContentA p6Frame A (10339/3072)` for every relation `A` inside `P6Adm9` (`r ≤ 8 m ≤ r + 9`);
`P6Adm` (`r ≤ 8 m ≤ r + 8`) is a corollary.  The same `Λ` as member 1.
P6 has no deficit families, so this is the generic `mem2ContentA_of_member1` (`δ = 0`, bordering cost
`topC`, `O(r log r)`) applied to the P6 instance family `p6Inst` with the numerology `p6_badInfo`
and the member-1 content `p6_content`.  An admissible `m` is `⌈r/8⌉`, `r/8 + 1` or (only when
`r ≡ 7 (8)`) `r/8 + 2`, so the three choice functions cover the window.
-/

open Filter CatalanCore CatalanCore.Arith.Hybrid CatalanFrames.HybCommon CatalanFrames.P6

namespace CatalanFrames.P6Hybrid

/-- **P6 second-member content** at the member-1 constant, on any relation inside `P6Adm9`. -/
theorem p6_mem2ContentA {A : ℕ → ℕ → Prop} (hA : ∀ r m, A r m → P6Adm9 r m) :
    CatalanCore.Rect.Mem2ContentA p6Frame A (10339 / 3072) := by
  refine mem2ContentA_of_member1 p6Inst p6_badInfo A ?_ (p6_log_Dhyb_uniform hA)
  filter_upwards [eventually_ge_atTop 2] with r hr m hm
  have := hA r m hm; unfold P6Adm9 at this; omega

/-- **P6 second-member content** on `P6Adm` (corollary). -/
theorem p6_mem2Content :
    CatalanCore.Rect.Mem2ContentA p6Frame P6Adm (10339 / 3072) :=
  p6_mem2ContentA (fun _ _ h => h.toAdm9)

end CatalanFrames.P6Hybrid

#print axioms CatalanFrames.P6Hybrid.p6_mem2ContentA
#print axioms CatalanFrames.P6Hybrid.p6_mem2Content
