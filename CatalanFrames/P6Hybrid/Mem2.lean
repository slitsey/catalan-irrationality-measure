module

public import CatalanFrames.P6Hybrid.Pieces
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

/-- The admissible window of the P6 pair family: `r ≤ 8m ≤ r + 8`. -/
def P6Adm (r m : ℕ) : Prop := r ≤ 8 * m ∧ 8 * m ≤ r + 8

/-- The widened window `r ≤ 8m ≤ r + 9` (P6GAP): for `ℓ = 6t+1`, `r + 2m = 3t`, a member exists for
EVERY `t` (`pair_window_wide`), so the prime class need not avoid `ℓ ≡ 43 (60)`. -/
def P6Adm9 (r m : ℕ) : Prop := r ≤ 8 * m ∧ 8 * m ≤ r + 9

theorem P6Adm.toAdm9 {r m : ℕ} (h : P6Adm r m) : P6Adm9 r m := ⟨h.1, by have := h.2; omega⟩

/-- the third choice function covering the window `P6Adm9` -/
def p6mfC (r : ℕ) : ℕ := if r % 8 = 7 then r / 8 + 2 else r / 8 + 1

theorem P6Adm9.cases {r m : ℕ} (h : P6Adm9 r m) :
    m = (r + 7) / 8 ∨ m = r / 8 + 1 ∨ m = p6mfC r := by
  unfold p6mfC; obtain ⟨h1, h2⟩ := h; split_ifs <;> omega

/-- **P6 second-member content** at the member-1 constant, on any relation inside `P6Adm9`. -/
theorem p6_mem2ContentA {A : ℕ → ℕ → Prop} (hA : ∀ r m, A r m → P6Adm9 r m) :
    CatalanCore.Rect.Mem2ContentA p6Frame A (10339 / 3072) := by
  have h1 : P6ContentStmt (fun r => (r + 7) / 8) :=
    p6_content _ (fun r => ⟨by omega, by omega⟩)
  have h2 : P6ContentStmt (fun r => r / 8 + 1) :=
    p6_content _ (fun r => ⟨by omega, by omega⟩)
  have h3 : P6ContentStmt p6mfC :=
    p6_content _ (fun r => by unfold p6mfC; split_ifs <;> omega)
  refine mem2ContentA_of_member1 p6Inst p6_badInfo A ?_ ?_
  · filter_upwards [eventually_ge_atTop 2] with r hr m hm
    have := hA r m hm; unfold P6Adm9 at this; omega
  · intro ε hε
    filter_upwards [h1 ε hε, h2 ε hε, h3 ε hε] with r a b c m hm
    rcases (hA r m hm).cases with rfl | rfl | rfl
    · exact a
    · exact b
    · exact c

/-- **P6 second-member content** on `P6Adm` (corollary). -/
theorem p6_mem2Content :
    CatalanCore.Rect.Mem2ContentA p6Frame P6Adm (10339 / 3072) :=
  p6_mem2ContentA (fun _ _ h => h.toAdm9)

end CatalanFrames.P6Hybrid

#print axioms CatalanFrames.P6Hybrid.p6_mem2ContentA
#print axioms CatalanFrames.P6Hybrid.p6_mem2Content
