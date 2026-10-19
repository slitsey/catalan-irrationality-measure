module

public import CatalanFrames.P6Hybrid.Pieces
public import CatalanFrames.HybCommon.TopSum

@[expose] public section

/-!
# P6 hybrid: the second-member content `p6_mem2Content`

`Mem2ContentA p6Frame (fun r m => r ≤ 8 m ∧ 8 m ≤ r + 8) (10339/3072)`: the same `Λ` as member 1.
P6 has no deficit families, so this is the generic `mem2ContentA_of_member1` (`δ = 0`, bordering cost
`topC`, `O(r log r)`) applied to the P6 instance family `p6Inst` with the numerology `p6_badInfo`
and the member-1 content `p6_content`.  An admissible `m` is `⌈r/8⌉` or `r/8 + 1`, so the two
choice functions `p6mfA, p6mfB` cover the window.
-/

open Filter CatalanCore CatalanCore.Arith.Hybrid CatalanFrames.HybCommon CatalanFrames.P6

namespace CatalanFrames.P6Hybrid

/-- The admissible window of the P6 pair family. -/
def P6Adm (r m : ℕ) : Prop := r ≤ 8 * m ∧ 8 * m ≤ r + 8


/-- **P6 second-member content** at the member-1 constant. -/
theorem p6_mem2Content :
    CatalanCore.Rect.Mem2ContentA p6Frame P6Adm (10339 / 3072) := by
  have hA : P6ContentStmt (fun r => (r + 7) / 8) :=
    p6_content _ (fun r => ⟨by omega, by omega⟩)
  have hB : P6ContentStmt (fun r => r / 8 + 1) :=
    p6_content _ (fun r => ⟨by omega, by omega⟩)
  refine mem2ContentA_of_member1 p6Inst p6_badInfo P6Adm ?_ ?_
  · filter_upwards [eventually_ge_atTop 2] with r hr m ⟨ha, hb⟩
    omega
  · intro ε hε
    filter_upwards [hA ε hε, hB ε hε] with r h1 h2 m ⟨ha, hb⟩
    have : m = (r + 7) / 8 ∨ m = r / 8 + 1 := by omega
    rcases this with rfl | rfl
    · exact h1
    · exact h2

end CatalanFrames.P6Hybrid

#print axioms CatalanFrames.P6Hybrid.p6_mem2Content
