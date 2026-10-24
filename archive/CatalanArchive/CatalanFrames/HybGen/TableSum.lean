module

public import CatalanFrames.HybGen.D1Prefix

@[expose] public section
open CatalanFrames.HybGen
open CatalanFrames CatalanFrames.HybCommon

/-!
# From covers to a class sum

`class_sum_of_tables`: for a list `ll` of pieces chained from `1/68`, covered for every admissible
`(r, m)` (window `r ≤ 8m ≤ r + 9`), the class sum of `WGm` up to `⌊lastEnd * r⌋` is at most
`r² ((9/4 · (1/68) + listInt ll)/φ(M) + ε)` eventually, uniformly in `m`.  The prefix `p ≤ r/68`
uses the trivial `D1` bound `X ≤ 2(r+m)`.
-/

open Finset Filter CatalanCore CatalanCore.Arith CatalanCore.Arith.Hybrid CatalanFrames.HybCommon

namespace CatalanArchive.CatalanFrames.HybGen.TableSum

variable {Fr : Frame}

lemma XGm_D1 (I : HybInst Fr) (r m p : ℕ) : XGm I r m p ≤ 2 * (r + m) := by
  have h := trop_D1 (lev := I.lev) p r m
  have : (XGm I r m p : ℚ) ≤ ((2 * (r + m) : ℕ) : ℚ) := by push_cast; exact h
  exact_mod_cast this

theorem class_sum_of_tables {M : ℕ} [NeZero M] {c : ZMod M} (hc : IsUnit c) (I : HybInst Fr)
    (ll : List Piece) (hl : Chain (1 / 68) ll)
    (hcov : ∀ r m : ℕ, r ≤ 8 * m → 8 * m ≤ r + 9 → 400 ≤ r → ∀ P ∈ ll, Covers c (WGm I r m) r P)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop, ∀ m : ℕ, r ≤ 8 * m → 8 * m ≤ r + 9 →
      clsSum M c (WGm I r m) 0 ⌊lastEnd (1 / 68) ll * r⌋₊ ≤
        (r : ℝ) ^ 2 * ((9 / 4 * (1 / 68) + listInt ll) / (M.totient : ℝ) + ε) := by
  have h := class_total (M := M) hc (α0 := 9 / 4 + ε) (t1 := 1 / 68) (by positivity)
    (by norm_num) ll hl (ε := ε / 2) (by positivity)
  have hφ : (1 : ℝ) ≤ (M.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne M))
  filter_upwards [h, eventually_ge_atTop 400, eventually_ge_atTop ⌈3 / ε⌉₊] with r hr h400 hre
  intro m hm1 hm2
  have he : 3 ≤ ε * (r : ℝ) := by
    have h1 := Nat.le_ceil (3 / ε)
    have h2 : 3 / ε ≤ (r : ℝ) := h1.trans (by exact_mod_cast hre)
    rwa [div_le_iff₀ hε, mul_comm] at h2
  have hm2' : (8 * m : ℝ) ≤ r + 9 := by exact_mod_cast hm2
  have hh := hr (WGm I r m) (by
    intro p _ _ _
    have h1 : (XGm I r m p : ℝ) ≤ ((2 * (r + m) : ℕ) : ℝ) := by exact_mod_cast XGm_D1 I r m p
    push_cast at h1
    show (XGm I r m p : ℝ) ≤ _
    nlinarith) (hcov r m hm1 hm2 h400)
  refine hh.trans ?_
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  have e1 : (9 / 4 + ε) * (1 / 68) = 9 / 4 * (1 / 68) + ε / 68 := by ring
  rw [e1]
  have e2 : (9 / 4 * (1 / 68) + ε / 68 + listInt ll) / (M.totient : ℝ) =
      (9 / 4 * (1 / 68) + listInt ll) / (M.totient : ℝ) + ε / 68 / (M.totient : ℝ) := by
    field_simp; ring
  rw [e2]
  have e3 : ε / 68 / (M.totient : ℝ) ≤ ε / 68 := div_le_self (by positivity) hφ
  linarith

end CatalanArchive.CatalanFrames.HybGen.TableSum

#print axioms CatalanArchive.CatalanFrames.HybGen.TableSum.class_sum_of_tables
