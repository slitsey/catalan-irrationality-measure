module

public import CatalanFrames.P6Hybrid.Pieces

@[expose] public section

open Filter CatalanCore CatalanCore.Arith.Hybrid CatalanFrames.P6

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

/-- Uniform base denominator growth on the widened admissible window. -/
theorem p6_log_Dhyb_uniform {A : ℕ → ℕ → Prop} (hA : ∀ r m, A r m → P6Adm9 r m) :
    ∀ ε > 0, ∀ᶠ r : ℕ in atTop, ∀ m, A r m →
      Real.log (Dhyb (p6Inst r m) r m) ≤ (10339 / 3072 + ε) * (r : ℝ) ^ 2 := by
  have h1 : P6ContentStmt (fun r => (r + 7) / 8) :=
    p6_content _ (fun r => ⟨by omega, by omega⟩)
  have h2 : P6ContentStmt (fun r => r / 8 + 1) :=
    p6_content _ (fun r => ⟨by omega, by omega⟩)
  have h3 : P6ContentStmt p6mfC :=
    p6_content _ (fun r => by unfold p6mfC; split_ifs <;> omega)
  intro ε hε
  filter_upwards [h1 ε hε, h2 ε hε, h3 ε hε] with r a b c m hm
  rcases (hA r m hm).cases with rfl | rfl | rfl
  · exact a
  · exact b
  · exact c


/-- The prime class `ℓ ≡ 1 (mod 6)`. -/
def P6Cls1 (l : ℕ) : Prop := (l : ZMod 6) ∈ ({1} : Finset (ZMod 6))

theorem P6Cls1.mod6 {l : ℕ} (h : P6Cls1 l) : l % 6 = 1 := by
  have h' : (l : ZMod 6) = 1 := by simpa [P6Cls1] using h
  exact cls_one h'


end CatalanFrames.P6Hybrid
