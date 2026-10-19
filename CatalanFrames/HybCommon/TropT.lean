module

public import CatalanFrames.HybCommon.EN
public import CatalanFrames.HybCommon.Trop

@[expose] public section

/-!
# Extended-weight covers (generic in the offset)

`WTG I o r p = max (WG I r p) (eNG o r p)`: the weight of the deficit family `TfunG`.  All 27 class and
D1 piece covers of `Trop.lean` extend to `WTG` (the duals of all six windows are below the same piece
bounds), for both offsets.
-/

open Finset Filter Classical CatalanCore CatalanCore.Arith CatalanCore.Arith.Hybrid

namespace CatalanFrames.HybCommon

variable {Fr : Frame}

/-- The extended weight. -/
noncomputable def WTG (I : HybInst Fr) (o r p : ℕ) : ℝ := max (WG I r p) (eNG o r p : ℝ)

lemma WTG_nonneg (I : HybInst Fr) (o r p : ℕ) : 0 ≤ WTG I o r p :=
  (Nat.cast_nonneg _).trans (le_max_right _ _)

section Covers

variable {I : HybInst Fr} {o : ℕ}

theorem cwj1_1 (T : TropFacts I o) (r : ℕ) (hr : 400 ≤ r) :
    Covers (cJ1 o) (WTG I o r) r (mkPiece 1 4 9 10 17 (0) 64 8) := by
  intro p hlo hhi hp hc
  have hW := cj1_1 T r hr p hlo hhi hp hc
  rw [floor_mk_s] at hlo; rw [floor_mk_t] at hhi
  have hm := mod_j1 T hc
  have hE : (8 : ℤ) * (eNG o r p : ℤ) ≤ 17 * (r : ℤ) + (0) * (p : ℤ) + (64) := by
    rcases eNG_cases (o := o) (r := r) (p := p) T.ho (by omega) with h | ⟨⟨_, c2, c3, c4⟩, e⟩ |
        ⟨⟨_, c2, c3, c4, _⟩, e⟩ | ⟨⟨_, c2, c3⟩, e⟩ | ⟨⟨_, c2, c3, c4, c5⟩, e⟩ |
        ⟨⟨_, c2, c3, c4⟩, e⟩ | ⟨hLC, e⟩
    · rw [h]; omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rw [e, kBG_j1 T.ho hm]; rcases T.ho with rfl | rfl <;> omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rcases hLC with ⟨g1, g2, _, g3, g4⟩ | ⟨g1, g2, _, g3, g4⟩ <;> rw [e] <;>
        rcases T.ho with rfl | rfl <;> omega
  show max (WG I r p) (eNG o r p : ℝ) ≤ _
  exact max_le hW (real_of_int_bound (x := eNG o r p) (r := r) (p := p) 8 17 (0) 64 (by norm_num) hE)

theorem cwj1_2 (T : TropFacts I o) (r : ℕ) (hr : 400 ≤ r) :
    Covers (cJ1 o) (WTG I o r) r (mkPiece 9 10 1 1 13 (-5) 32 4) := by
  intro p hlo hhi hp hc
  have hW := cj1_2 T r hr p hlo hhi hp hc
  rw [floor_mk_s] at hlo; rw [floor_mk_t] at hhi
  have hm := mod_j1 T hc
  have hE : (4 : ℤ) * (eNG o r p : ℤ) ≤ 13 * (r : ℤ) + (-5) * (p : ℤ) + (32) := by
    rcases eNG_cases (o := o) (r := r) (p := p) T.ho (by omega) with h | ⟨⟨_, c2, c3, c4⟩, e⟩ |
        ⟨⟨_, c2, c3, c4, _⟩, e⟩ | ⟨⟨_, c2, c3⟩, e⟩ | ⟨⟨_, c2, c3, c4, c5⟩, e⟩ |
        ⟨⟨_, c2, c3, c4⟩, e⟩ | ⟨hLC, e⟩
    · rw [h]; omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rw [e, kBG_j1 T.ho hm]; rcases T.ho with rfl | rfl <;> omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rcases hLC with ⟨g1, g2, _, g3, g4⟩ | ⟨g1, g2, _, g3, g4⟩ <;> rw [e] <;>
        rcases T.ho with rfl | rfl <;> omega
  show max (WG I r p) (eNG o r p : ℝ) ≤ _
  exact max_le hW (real_of_int_bound (x := eNG o r p) (r := r) (p := p) 4 13 (-5) 32 (by norm_num) hE)

theorem cwj1_3 (T : TropFacts I o) (r : ℕ) (hr : 400 ≤ r) :
    Covers (cJ1 o) (WTG I o r) r (mkPiece 1 1 5 4 7 (-3) 32 2) := by
  intro p hlo hhi hp hc
  have hW := cj1_3 T r hr p hlo hhi hp hc
  rw [floor_mk_s] at hlo; rw [floor_mk_t] at hhi
  have hm := mod_j1 T hc
  have hE : (2 : ℤ) * (eNG o r p : ℤ) ≤ 7 * (r : ℤ) + (-3) * (p : ℤ) + (32) := by
    rcases eNG_cases (o := o) (r := r) (p := p) T.ho (by omega) with h | ⟨⟨_, c2, c3, c4⟩, e⟩ |
        ⟨⟨_, c2, c3, c4, _⟩, e⟩ | ⟨⟨_, c2, c3⟩, e⟩ | ⟨⟨_, c2, c3, c4, c5⟩, e⟩ |
        ⟨⟨_, c2, c3, c4⟩, e⟩ | ⟨hLC, e⟩
    · rw [h]; omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rw [e, kBG_j1 T.ho hm]; rcases T.ho with rfl | rfl <;> omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rcases hLC with ⟨g1, g2, _, g3, g4⟩ | ⟨g1, g2, _, g3, g4⟩ <;> rw [e] <;>
        rcases T.ho with rfl | rfl <;> omega
  show max (WG I r p) (eNG o r p : ℝ) ≤ _
  exact max_le hW (real_of_int_bound (x := eNG o r p) (r := r) (p := p) 2 7 (-3) 32 (by norm_num) hE)

theorem cwj1_4 (T : TropFacts I o) (r : ℕ) (hr : 400 ≤ r) :
    Covers (cJ1 o) (WTG I o r) r (mkPiece 5 4 4 1 9 (-2) 32 4) := by
  intro p hlo hhi hp hc
  have hW := cj1_4 T r hr p hlo hhi hp hc
  rw [floor_mk_s] at hlo; rw [floor_mk_t] at hhi
  have hm := mod_j1 T hc
  have hE : (4 : ℤ) * (eNG o r p : ℤ) ≤ 9 * (r : ℤ) + (-2) * (p : ℤ) + (32) := by
    rcases eNG_cases (o := o) (r := r) (p := p) T.ho (by omega) with h | ⟨⟨_, c2, c3, c4⟩, e⟩ |
        ⟨⟨_, c2, c3, c4, _⟩, e⟩ | ⟨⟨_, c2, c3⟩, e⟩ | ⟨⟨_, c2, c3, c4, c5⟩, e⟩ |
        ⟨⟨_, c2, c3, c4⟩, e⟩ | ⟨hLC, e⟩
    · rw [h]; omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rw [e, kBG_j1 T.ho hm]; rcases T.ho with rfl | rfl <;> omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rcases hLC with ⟨g1, g2, _, g3, g4⟩ | ⟨g1, g2, _, g3, g4⟩ <;> rw [e] <;>
        rcases T.ho with rfl | rfl <;> omega
  show max (WG I r p) (eNG o r p : ℝ) ≤ _
  exact max_le hW (real_of_int_bound (x := eNG o r p) (r := r) (p := p) 4 9 (-2) 32 (by norm_num) hE)

theorem cwj1_5 (T : TropFacts I o) (r : ℕ) (hr : 400 ≤ r) :
    Covers (cJ1 o) (WTG I o r) r (mkPiece 4 1 5 1 5 (-1) 32 4) := by
  intro p hlo hhi hp hc
  have hW := cj1_5 T r hr p hlo hhi hp hc
  rw [floor_mk_s] at hlo; rw [floor_mk_t] at hhi
  have hm := mod_j1 T hc
  have hE : (4 : ℤ) * (eNG o r p : ℤ) ≤ 5 * (r : ℤ) + (-1) * (p : ℤ) + (32) := by
    rcases eNG_cases (o := o) (r := r) (p := p) T.ho (by omega) with h | ⟨⟨_, c2, c3, c4⟩, e⟩ |
        ⟨⟨_, c2, c3, c4, _⟩, e⟩ | ⟨⟨_, c2, c3⟩, e⟩ | ⟨⟨_, c2, c3, c4, c5⟩, e⟩ |
        ⟨⟨_, c2, c3, c4⟩, e⟩ | ⟨hLC, e⟩
    · rw [h]; omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rw [e, kBG_j1 T.ho hm]; rcases T.ho with rfl | rfl <;> omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rcases hLC with ⟨g1, g2, _, g3, g4⟩ | ⟨g1, g2, _, g3, g4⟩ <;> rw [e] <;>
        rcases T.ho with rfl | rfl <;> omega
  show max (WG I r p) (eNG o r p : ℝ) ≤ _
  exact max_le hW (real_of_int_bound (x := eNG o r p) (r := r) (p := p) 4 5 (-1) 32 (by norm_num) hE)

theorem cwj3_1 (T : TropFacts I o) (r : ℕ) (hr : 400 ≤ r) :
    Covers (cJ3 o) (WTG I o r) r (mkPiece 1 4 9 14 17 (0) 64 8) := by
  intro p hlo hhi hp hc
  have hW := cj3_1 T r hr p hlo hhi hp hc
  rw [floor_mk_s] at hlo; rw [floor_mk_t] at hhi
  have hm := mod_j3 T hc
  have hE : (8 : ℤ) * (eNG o r p : ℤ) ≤ 17 * (r : ℤ) + (0) * (p : ℤ) + (64) := by
    rcases eNG_cases (o := o) (r := r) (p := p) T.ho (by omega) with h | ⟨⟨_, c2, c3, c4⟩, e⟩ |
        ⟨⟨_, c2, c3, c4, _⟩, e⟩ | ⟨⟨_, c2, c3⟩, e⟩ | ⟨⟨_, c2, c3, c4, c5⟩, e⟩ |
        ⟨⟨_, c2, c3, c4⟩, e⟩ | ⟨hLC, e⟩
    · rw [h]; omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rw [e, kBG_j3 hm]; rcases T.ho with rfl | rfl <;> omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rcases hLC with ⟨g1, g2, _, g3, g4⟩ | ⟨g1, g2, _, g3, g4⟩ <;> rw [e] <;>
        rcases T.ho with rfl | rfl <;> omega
  show max (WG I r p) (eNG o r p : ℝ) ≤ _
  exact max_le hW (real_of_int_bound (x := eNG o r p) (r := r) (p := p) 8 17 (0) 64 (by norm_num) hE)

theorem cwj3_2 (T : TropFacts I o) (r : ℕ) (hr : 400 ≤ r) :
    Covers (cJ3 o) (WTG I o r) r (mkPiece 9 14 5 7 13 (-7) 32 4) := by
  intro p hlo hhi hp hc
  have hW := cj3_2 T r hr p hlo hhi hp hc
  rw [floor_mk_s] at hlo; rw [floor_mk_t] at hhi
  have hm := mod_j3 T hc
  have hE : (4 : ℤ) * (eNG o r p : ℤ) ≤ 13 * (r : ℤ) + (-7) * (p : ℤ) + (32) := by
    rcases eNG_cases (o := o) (r := r) (p := p) T.ho (by omega) with h | ⟨⟨_, c2, c3, c4⟩, e⟩ |
        ⟨⟨_, c2, c3, c4, _⟩, e⟩ | ⟨⟨_, c2, c3⟩, e⟩ | ⟨⟨_, c2, c3, c4, c5⟩, e⟩ |
        ⟨⟨_, c2, c3, c4⟩, e⟩ | ⟨hLC, e⟩
    · rw [h]; omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rw [e, kBG_j3 hm]; rcases T.ho with rfl | rfl <;> omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rcases hLC with ⟨g1, g2, _, g3, g4⟩ | ⟨g1, g2, _, g3, g4⟩ <;> rw [e] <;>
        rcases T.ho with rfl | rfl <;> omega
  show max (WG I r p) (eNG o r p : ℝ) ≤ _
  exact max_le hW (real_of_int_bound (x := eNG o r p) (r := r) (p := p) 4 13 (-7) 32 (by norm_num) hE)

theorem cwj3_3 (T : TropFacts I o) (r : ℕ) (hr : 400 ≤ r) :
    Covers (cJ3 o) (WTG I o r) r (mkPiece 5 7 1 1 9 (-7) 16 2) := by
  intro p hlo hhi hp hc
  have hW := cj3_3 T r hr p hlo hhi hp hc
  rw [floor_mk_s] at hlo; rw [floor_mk_t] at hhi
  have hm := mod_j3 T hc
  have hE : (2 : ℤ) * (eNG o r p : ℤ) ≤ 9 * (r : ℤ) + (-7) * (p : ℤ) + (16) := by
    rcases eNG_cases (o := o) (r := r) (p := p) T.ho (by omega) with h | ⟨⟨_, c2, c3, c4⟩, e⟩ |
        ⟨⟨_, c2, c3, c4, _⟩, e⟩ | ⟨⟨_, c2, c3⟩, e⟩ | ⟨⟨_, c2, c3, c4, c5⟩, e⟩ |
        ⟨⟨_, c2, c3, c4⟩, e⟩ | ⟨hLC, e⟩
    · rw [h]; omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rw [e, kBG_j3 hm]; rcases T.ho with rfl | rfl <;> omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rcases hLC with ⟨g1, g2, _, g3, g4⟩ | ⟨g1, g2, _, g3, g4⟩ <;> rw [e] <;>
        rcases T.ho with rfl | rfl <;> omega
  show max (WG I r p) (eNG o r p : ℝ) ≤ _
  exact max_le hW (real_of_int_bound (x := eNG o r p) (r := r) (p := p) 2 9 (-7) 16 (by norm_num) hE)

theorem cwj3_4 (T : TropFacts I o) (r : ℕ) (hr : 400 ≤ r) :
    Covers (cJ3 o) (WTG I o r) r (mkPiece 1 1 5 4 7 (-5) 16 2) := by
  intro p hlo hhi hp hc
  have hW := cj3_4 T r hr p hlo hhi hp hc
  rw [floor_mk_s] at hlo; rw [floor_mk_t] at hhi
  have hm := mod_j3 T hc
  have hE : (2 : ℤ) * (eNG o r p : ℤ) ≤ 7 * (r : ℤ) + (-5) * (p : ℤ) + (16) := by
    rcases eNG_cases (o := o) (r := r) (p := p) T.ho (by omega) with h | ⟨⟨_, c2, c3, c4⟩, e⟩ |
        ⟨⟨_, c2, c3, c4, _⟩, e⟩ | ⟨⟨_, c2, c3⟩, e⟩ | ⟨⟨_, c2, c3, c4, c5⟩, e⟩ |
        ⟨⟨_, c2, c3, c4⟩, e⟩ | ⟨hLC, e⟩
    · rw [h]; omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rw [e, kBG_j3 hm]; rcases T.ho with rfl | rfl <;> omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rcases hLC with ⟨g1, g2, _, g3, g4⟩ | ⟨g1, g2, _, g3, g4⟩ <;> rw [e] <;>
        rcases T.ho with rfl | rfl <;> omega
  show max (WG I r p) (eNG o r p : ℝ) ≤ _
  exact max_le hW (real_of_int_bound (x := eNG o r p) (r := r) (p := p) 2 7 (-5) 16 (by norm_num) hE)

theorem cwj3_5 (T : TropFacts I o) (r : ℕ) (hr : 400 ≤ r) :
    Covers (cJ3 o) (WTG I o r) r (mkPiece 5 4 4 3 9 (-6) 32 4) := by
  intro p hlo hhi hp hc
  have hW := cj3_5 T r hr p hlo hhi hp hc
  rw [floor_mk_s] at hlo; rw [floor_mk_t] at hhi
  have hm := mod_j3 T hc
  have hE : (4 : ℤ) * (eNG o r p : ℤ) ≤ 9 * (r : ℤ) + (-6) * (p : ℤ) + (32) := by
    rcases eNG_cases (o := o) (r := r) (p := p) T.ho (by omega) with h | ⟨⟨_, c2, c3, c4⟩, e⟩ |
        ⟨⟨_, c2, c3, c4, _⟩, e⟩ | ⟨⟨_, c2, c3⟩, e⟩ | ⟨⟨_, c2, c3, c4, c5⟩, e⟩ |
        ⟨⟨_, c2, c3, c4⟩, e⟩ | ⟨hLC, e⟩
    · rw [h]; omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rw [e, kBG_j3 hm]; rcases T.ho with rfl | rfl <;> omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rcases hLC with ⟨g1, g2, _, g3, g4⟩ | ⟨g1, g2, _, g3, g4⟩ <;> rw [e] <;>
        rcases T.ho with rfl | rfl <;> omega
  show max (WG I r p) (eNG o r p : ℝ) ≤ _
  exact max_le hW (real_of_int_bound (x := eNG o r p) (r := r) (p := p) 4 9 (-6) 32 (by norm_num) hE)

theorem cwj3_6 (T : TropFacts I o) (r : ℕ) (hr : 400 ≤ r) :
    Covers (cJ3 o) (WTG I o r) r (mkPiece 4 3 5 3 5 (-3) 32 4) := by
  intro p hlo hhi hp hc
  have hW := cj3_6 T r hr p hlo hhi hp hc
  rw [floor_mk_s] at hlo; rw [floor_mk_t] at hhi
  have hm := mod_j3 T hc
  have hE : (4 : ℤ) * (eNG o r p : ℤ) ≤ 5 * (r : ℤ) + (-3) * (p : ℤ) + (32) := by
    rcases eNG_cases (o := o) (r := r) (p := p) T.ho (by omega) with h | ⟨⟨_, c2, c3, c4⟩, e⟩ |
        ⟨⟨_, c2, c3, c4, _⟩, e⟩ | ⟨⟨_, c2, c3⟩, e⟩ | ⟨⟨_, c2, c3, c4, c5⟩, e⟩ |
        ⟨⟨_, c2, c3, c4⟩, e⟩ | ⟨hLC, e⟩
    · rw [h]; omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rw [e, kBG_j3 hm]; rcases T.ho with rfl | rfl <;> omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rcases hLC with ⟨g1, g2, _, g3, g4⟩ | ⟨g1, g2, _, g3, g4⟩ <;> rw [e] <;>
        rcases T.ho with rfl | rfl <;> omega
  show max (WG I r p) (eNG o r p : ℝ) ≤ _
  exact max_le hW (real_of_int_bound (x := eNG o r p) (r := r) (p := p) 4 5 (-3) 32 (by norm_num) hE)

theorem cwd1_0 (T : TropFacts I o) (c : ZMod 4) (hc2 : (2 : ZMod 4) ≠ c) (r : ℕ) (hr : 400 ≤ r) :
    Covers c (WTG I o r) r (mkPiece 1 68 1 64 17 (64) 320 8) := by
  intro p hlo hhi hp hc
  have hW := d1g_0 T c hc2 r p hlo hhi hp hc
  rw [floor_mk_s] at hlo; rw [floor_mk_t] at hhi
  have hE : (8 : ℤ) * (eNG o r p : ℤ) ≤ 17 * (r : ℤ) + (64) * (p : ℤ) + (320) := by
    rcases eNG_cases (o := o) (r := r) (p := p) T.ho (by omega) with h | ⟨⟨_, c2, c3, c4⟩, e⟩ |
        ⟨⟨_, c2, c3, c4, _⟩, e⟩ | ⟨⟨_, c2, c3⟩, e⟩ | ⟨⟨_, c2, c3, c4, c5⟩, e⟩ |
        ⟨⟨_, c2, c3, c4⟩, e⟩ | ⟨hLC, e⟩
    · rw [h]; omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rcases hLC with ⟨g1, g2, _, g3, g4⟩ | ⟨g1, g2, _, g3, g4⟩ <;> rw [e] <;>
        rcases T.ho with rfl | rfl <;> omega
  show max (WG I r p) (eNG o r p : ℝ) ≤ _
  exact max_le hW (real_of_int_bound (x := eNG o r p) (r := r) (p := p) 8 17 (64) 320 (by norm_num) hE)

theorem cwd1_1 (T : TropFacts I o) (c : ZMod 4) (hc2 : (2 : ZMod 4) ≠ c) (r : ℕ) (hr : 400 ≤ r) :
    Covers c (WTG I o r) r (mkPiece 1 64 1 60 19 (-64) 320 8) := by
  intro p hlo hhi hp hc
  have hW := d1g_1 T c hc2 r p hlo hhi hp hc
  rw [floor_mk_s] at hlo; rw [floor_mk_t] at hhi
  have hE : (8 : ℤ) * (eNG o r p : ℤ) ≤ 19 * (r : ℤ) + (-64) * (p : ℤ) + (320) := by
    rcases eNG_cases (o := o) (r := r) (p := p) T.ho (by omega) with h | ⟨⟨_, c2, c3, c4⟩, e⟩ |
        ⟨⟨_, c2, c3, c4, _⟩, e⟩ | ⟨⟨_, c2, c3⟩, e⟩ | ⟨⟨_, c2, c3, c4, c5⟩, e⟩ |
        ⟨⟨_, c2, c3, c4⟩, e⟩ | ⟨hLC, e⟩
    · rw [h]; omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rcases hLC with ⟨g1, g2, _, g3, g4⟩ | ⟨g1, g2, _, g3, g4⟩ <;> rw [e] <;>
        rcases T.ho with rfl | rfl <;> omega
  show max (WG I r p) (eNG o r p : ℝ) ≤ _
  exact max_le hW (real_of_int_bound (x := eNG o r p) (r := r) (p := p) 8 19 (-64) 320 (by norm_num) hE)

theorem cwd1_2 (T : TropFacts I o) (c : ZMod 4) (hc2 : (2 : ZMod 4) ≠ c) (r : ℕ) (hr : 400 ≤ r) :
    Covers c (WTG I o r) r (mkPiece 1 60 1 56 17 (56) 320 8) := by
  intro p hlo hhi hp hc
  have hW := d1g_2 T c hc2 r p hlo hhi hp hc
  rw [floor_mk_s] at hlo; rw [floor_mk_t] at hhi
  have hE : (8 : ℤ) * (eNG o r p : ℤ) ≤ 17 * (r : ℤ) + (56) * (p : ℤ) + (320) := by
    rcases eNG_cases (o := o) (r := r) (p := p) T.ho (by omega) with h | ⟨⟨_, c2, c3, c4⟩, e⟩ |
        ⟨⟨_, c2, c3, c4, _⟩, e⟩ | ⟨⟨_, c2, c3⟩, e⟩ | ⟨⟨_, c2, c3, c4, c5⟩, e⟩ |
        ⟨⟨_, c2, c3, c4⟩, e⟩ | ⟨hLC, e⟩
    · rw [h]; omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rcases hLC with ⟨g1, g2, _, g3, g4⟩ | ⟨g1, g2, _, g3, g4⟩ <;> rw [e] <;>
        rcases T.ho with rfl | rfl <;> omega
  show max (WG I r p) (eNG o r p : ℝ) ≤ _
  exact max_le hW (real_of_int_bound (x := eNG o r p) (r := r) (p := p) 8 17 (56) 320 (by norm_num) hE)

theorem cwd1_3 (T : TropFacts I o) (c : ZMod 4) (hc2 : (2 : ZMod 4) ≠ c) (r : ℕ) (hr : 400 ≤ r) :
    Covers c (WTG I o r) r (mkPiece 1 56 1 52 19 (-56) 320 8) := by
  intro p hlo hhi hp hc
  have hW := d1g_3 T c hc2 r p hlo hhi hp hc
  rw [floor_mk_s] at hlo; rw [floor_mk_t] at hhi
  have hE : (8 : ℤ) * (eNG o r p : ℤ) ≤ 19 * (r : ℤ) + (-56) * (p : ℤ) + (320) := by
    rcases eNG_cases (o := o) (r := r) (p := p) T.ho (by omega) with h | ⟨⟨_, c2, c3, c4⟩, e⟩ |
        ⟨⟨_, c2, c3, c4, _⟩, e⟩ | ⟨⟨_, c2, c3⟩, e⟩ | ⟨⟨_, c2, c3, c4, c5⟩, e⟩ |
        ⟨⟨_, c2, c3, c4⟩, e⟩ | ⟨hLC, e⟩
    · rw [h]; omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rcases hLC with ⟨g1, g2, _, g3, g4⟩ | ⟨g1, g2, _, g3, g4⟩ <;> rw [e] <;>
        rcases T.ho with rfl | rfl <;> omega
  show max (WG I r p) (eNG o r p : ℝ) ≤ _
  exact max_le hW (real_of_int_bound (x := eNG o r p) (r := r) (p := p) 8 19 (-56) 320 (by norm_num) hE)

theorem cwd1_4 (T : TropFacts I o) (c : ZMod 4) (hc2 : (2 : ZMod 4) ≠ c) (r : ℕ) (hr : 400 ≤ r) :
    Covers c (WTG I o r) r (mkPiece 1 52 1 48 17 (48) 320 8) := by
  intro p hlo hhi hp hc
  have hW := d1g_4 T c hc2 r p hlo hhi hp hc
  rw [floor_mk_s] at hlo; rw [floor_mk_t] at hhi
  have hE : (8 : ℤ) * (eNG o r p : ℤ) ≤ 17 * (r : ℤ) + (48) * (p : ℤ) + (320) := by
    rcases eNG_cases (o := o) (r := r) (p := p) T.ho (by omega) with h | ⟨⟨_, c2, c3, c4⟩, e⟩ |
        ⟨⟨_, c2, c3, c4, _⟩, e⟩ | ⟨⟨_, c2, c3⟩, e⟩ | ⟨⟨_, c2, c3, c4, c5⟩, e⟩ |
        ⟨⟨_, c2, c3, c4⟩, e⟩ | ⟨hLC, e⟩
    · rw [h]; omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rcases hLC with ⟨g1, g2, _, g3, g4⟩ | ⟨g1, g2, _, g3, g4⟩ <;> rw [e] <;>
        rcases T.ho with rfl | rfl <;> omega
  show max (WG I r p) (eNG o r p : ℝ) ≤ _
  exact max_le hW (real_of_int_bound (x := eNG o r p) (r := r) (p := p) 8 17 (48) 320 (by norm_num) hE)

theorem cwd1_5 (T : TropFacts I o) (c : ZMod 4) (hc2 : (2 : ZMod 4) ≠ c) (r : ℕ) (hr : 400 ≤ r) :
    Covers c (WTG I o r) r (mkPiece 1 48 1 44 19 (-48) 320 8) := by
  intro p hlo hhi hp hc
  have hW := d1g_5 T c hc2 r p hlo hhi hp hc
  rw [floor_mk_s] at hlo; rw [floor_mk_t] at hhi
  have hE : (8 : ℤ) * (eNG o r p : ℤ) ≤ 19 * (r : ℤ) + (-48) * (p : ℤ) + (320) := by
    rcases eNG_cases (o := o) (r := r) (p := p) T.ho (by omega) with h | ⟨⟨_, c2, c3, c4⟩, e⟩ |
        ⟨⟨_, c2, c3, c4, _⟩, e⟩ | ⟨⟨_, c2, c3⟩, e⟩ | ⟨⟨_, c2, c3, c4, c5⟩, e⟩ |
        ⟨⟨_, c2, c3, c4⟩, e⟩ | ⟨hLC, e⟩
    · rw [h]; omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rcases hLC with ⟨g1, g2, _, g3, g4⟩ | ⟨g1, g2, _, g3, g4⟩ <;> rw [e] <;>
        rcases T.ho with rfl | rfl <;> omega
  show max (WG I r p) (eNG o r p : ℝ) ≤ _
  exact max_le hW (real_of_int_bound (x := eNG o r p) (r := r) (p := p) 8 19 (-48) 320 (by norm_num) hE)

theorem cwd1_6 (T : TropFacts I o) (c : ZMod 4) (hc2 : (2 : ZMod 4) ≠ c) (r : ℕ) (hr : 400 ≤ r) :
    Covers c (WTG I o r) r (mkPiece 1 44 1 40 17 (40) 320 8) := by
  intro p hlo hhi hp hc
  have hW := d1g_6 T c hc2 r p hlo hhi hp hc
  rw [floor_mk_s] at hlo; rw [floor_mk_t] at hhi
  have hE : (8 : ℤ) * (eNG o r p : ℤ) ≤ 17 * (r : ℤ) + (40) * (p : ℤ) + (320) := by
    rcases eNG_cases (o := o) (r := r) (p := p) T.ho (by omega) with h | ⟨⟨_, c2, c3, c4⟩, e⟩ |
        ⟨⟨_, c2, c3, c4, _⟩, e⟩ | ⟨⟨_, c2, c3⟩, e⟩ | ⟨⟨_, c2, c3, c4, c5⟩, e⟩ |
        ⟨⟨_, c2, c3, c4⟩, e⟩ | ⟨hLC, e⟩
    · rw [h]; omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rcases hLC with ⟨g1, g2, _, g3, g4⟩ | ⟨g1, g2, _, g3, g4⟩ <;> rw [e] <;>
        rcases T.ho with rfl | rfl <;> omega
  show max (WG I r p) (eNG o r p : ℝ) ≤ _
  exact max_le hW (real_of_int_bound (x := eNG o r p) (r := r) (p := p) 8 17 (40) 320 (by norm_num) hE)

theorem cwd1_7 (T : TropFacts I o) (c : ZMod 4) (hc2 : (2 : ZMod 4) ≠ c) (r : ℕ) (hr : 400 ≤ r) :
    Covers c (WTG I o r) r (mkPiece 1 40 1 36 19 (-40) 320 8) := by
  intro p hlo hhi hp hc
  have hW := d1g_7 T c hc2 r p hlo hhi hp hc
  rw [floor_mk_s] at hlo; rw [floor_mk_t] at hhi
  have hE : (8 : ℤ) * (eNG o r p : ℤ) ≤ 19 * (r : ℤ) + (-40) * (p : ℤ) + (320) := by
    rcases eNG_cases (o := o) (r := r) (p := p) T.ho (by omega) with h | ⟨⟨_, c2, c3, c4⟩, e⟩ |
        ⟨⟨_, c2, c3, c4, _⟩, e⟩ | ⟨⟨_, c2, c3⟩, e⟩ | ⟨⟨_, c2, c3, c4, c5⟩, e⟩ |
        ⟨⟨_, c2, c3, c4⟩, e⟩ | ⟨hLC, e⟩
    · rw [h]; omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rcases hLC with ⟨g1, g2, _, g3, g4⟩ | ⟨g1, g2, _, g3, g4⟩ <;> rw [e] <;>
        rcases T.ho with rfl | rfl <;> omega
  show max (WG I r p) (eNG o r p : ℝ) ≤ _
  exact max_le hW (real_of_int_bound (x := eNG o r p) (r := r) (p := p) 8 19 (-40) 320 (by norm_num) hE)

theorem cwd1_8 (T : TropFacts I o) (c : ZMod 4) (hc2 : (2 : ZMod 4) ≠ c) (r : ℕ) (hr : 400 ≤ r) :
    Covers c (WTG I o r) r (mkPiece 1 36 1 32 17 (32) 320 8) := by
  intro p hlo hhi hp hc
  have hW := d1g_8 T c hc2 r p hlo hhi hp hc
  rw [floor_mk_s] at hlo; rw [floor_mk_t] at hhi
  have hE : (8 : ℤ) * (eNG o r p : ℤ) ≤ 17 * (r : ℤ) + (32) * (p : ℤ) + (320) := by
    rcases eNG_cases (o := o) (r := r) (p := p) T.ho (by omega) with h | ⟨⟨_, c2, c3, c4⟩, e⟩ |
        ⟨⟨_, c2, c3, c4, _⟩, e⟩ | ⟨⟨_, c2, c3⟩, e⟩ | ⟨⟨_, c2, c3, c4, c5⟩, e⟩ |
        ⟨⟨_, c2, c3, c4⟩, e⟩ | ⟨hLC, e⟩
    · rw [h]; omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rcases hLC with ⟨g1, g2, _, g3, g4⟩ | ⟨g1, g2, _, g3, g4⟩ <;> rw [e] <;>
        rcases T.ho with rfl | rfl <;> omega
  show max (WG I r p) (eNG o r p : ℝ) ≤ _
  exact max_le hW (real_of_int_bound (x := eNG o r p) (r := r) (p := p) 8 17 (32) 320 (by norm_num) hE)

theorem cwd1_9 (T : TropFacts I o) (c : ZMod 4) (hc2 : (2 : ZMod 4) ≠ c) (r : ℕ) (hr : 400 ≤ r) :
    Covers c (WTG I o r) r (mkPiece 1 32 1 28 19 (-32) 320 8) := by
  intro p hlo hhi hp hc
  have hW := d1g_9 T c hc2 r p hlo hhi hp hc
  rw [floor_mk_s] at hlo; rw [floor_mk_t] at hhi
  have hE : (8 : ℤ) * (eNG o r p : ℤ) ≤ 19 * (r : ℤ) + (-32) * (p : ℤ) + (320) := by
    rcases eNG_cases (o := o) (r := r) (p := p) T.ho (by omega) with h | ⟨⟨_, c2, c3, c4⟩, e⟩ |
        ⟨⟨_, c2, c3, c4, _⟩, e⟩ | ⟨⟨_, c2, c3⟩, e⟩ | ⟨⟨_, c2, c3, c4, c5⟩, e⟩ |
        ⟨⟨_, c2, c3, c4⟩, e⟩ | ⟨hLC, e⟩
    · rw [h]; omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rcases hLC with ⟨g1, g2, _, g3, g4⟩ | ⟨g1, g2, _, g3, g4⟩ <;> rw [e] <;>
        rcases T.ho with rfl | rfl <;> omega
  show max (WG I r p) (eNG o r p : ℝ) ≤ _
  exact max_le hW (real_of_int_bound (x := eNG o r p) (r := r) (p := p) 8 19 (-32) 320 (by norm_num) hE)

theorem cwd1_10 (T : TropFacts I o) (c : ZMod 4) (hc2 : (2 : ZMod 4) ≠ c) (r : ℕ) (hr : 400 ≤ r) :
    Covers c (WTG I o r) r (mkPiece 1 28 1 24 17 (24) 320 8) := by
  intro p hlo hhi hp hc
  have hW := d1g_10 T c hc2 r p hlo hhi hp hc
  rw [floor_mk_s] at hlo; rw [floor_mk_t] at hhi
  have hE : (8 : ℤ) * (eNG o r p : ℤ) ≤ 17 * (r : ℤ) + (24) * (p : ℤ) + (320) := by
    rcases eNG_cases (o := o) (r := r) (p := p) T.ho (by omega) with h | ⟨⟨_, c2, c3, c4⟩, e⟩ |
        ⟨⟨_, c2, c3, c4, _⟩, e⟩ | ⟨⟨_, c2, c3⟩, e⟩ | ⟨⟨_, c2, c3, c4, c5⟩, e⟩ |
        ⟨⟨_, c2, c3, c4⟩, e⟩ | ⟨hLC, e⟩
    · rw [h]; omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rcases hLC with ⟨g1, g2, _, g3, g4⟩ | ⟨g1, g2, _, g3, g4⟩ <;> rw [e] <;>
        rcases T.ho with rfl | rfl <;> omega
  show max (WG I r p) (eNG o r p : ℝ) ≤ _
  exact max_le hW (real_of_int_bound (x := eNG o r p) (r := r) (p := p) 8 17 (24) 320 (by norm_num) hE)

theorem cwd1_11 (T : TropFacts I o) (c : ZMod 4) (hc2 : (2 : ZMod 4) ≠ c) (r : ℕ) (hr : 400 ≤ r) :
    Covers c (WTG I o r) r (mkPiece 1 24 1 20 19 (-24) 320 8) := by
  intro p hlo hhi hp hc
  have hW := d1g_11 T c hc2 r p hlo hhi hp hc
  rw [floor_mk_s] at hlo; rw [floor_mk_t] at hhi
  have hE : (8 : ℤ) * (eNG o r p : ℤ) ≤ 19 * (r : ℤ) + (-24) * (p : ℤ) + (320) := by
    rcases eNG_cases (o := o) (r := r) (p := p) T.ho (by omega) with h | ⟨⟨_, c2, c3, c4⟩, e⟩ |
        ⟨⟨_, c2, c3, c4, _⟩, e⟩ | ⟨⟨_, c2, c3⟩, e⟩ | ⟨⟨_, c2, c3, c4, c5⟩, e⟩ |
        ⟨⟨_, c2, c3, c4⟩, e⟩ | ⟨hLC, e⟩
    · rw [h]; omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rcases hLC with ⟨g1, g2, _, g3, g4⟩ | ⟨g1, g2, _, g3, g4⟩ <;> rw [e] <;>
        rcases T.ho with rfl | rfl <;> omega
  show max (WG I r p) (eNG o r p : ℝ) ≤ _
  exact max_le hW (real_of_int_bound (x := eNG o r p) (r := r) (p := p) 8 19 (-24) 320 (by norm_num) hE)

theorem cwd1_12 (T : TropFacts I o) (c : ZMod 4) (hc2 : (2 : ZMod 4) ≠ c) (r : ℕ) (hr : 400 ≤ r) :
    Covers c (WTG I o r) r (mkPiece 1 20 1 16 17 (16) 320 8) := by
  intro p hlo hhi hp hc
  have hW := d1g_12 T c hc2 r p hlo hhi hp hc
  rw [floor_mk_s] at hlo; rw [floor_mk_t] at hhi
  have hE : (8 : ℤ) * (eNG o r p : ℤ) ≤ 17 * (r : ℤ) + (16) * (p : ℤ) + (320) := by
    rcases eNG_cases (o := o) (r := r) (p := p) T.ho (by omega) with h | ⟨⟨_, c2, c3, c4⟩, e⟩ |
        ⟨⟨_, c2, c3, c4, _⟩, e⟩ | ⟨⟨_, c2, c3⟩, e⟩ | ⟨⟨_, c2, c3, c4, c5⟩, e⟩ |
        ⟨⟨_, c2, c3, c4⟩, e⟩ | ⟨hLC, e⟩
    · rw [h]; omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rcases hLC with ⟨g1, g2, _, g3, g4⟩ | ⟨g1, g2, _, g3, g4⟩ <;> rw [e] <;>
        rcases T.ho with rfl | rfl <;> omega
  show max (WG I r p) (eNG o r p : ℝ) ≤ _
  exact max_le hW (real_of_int_bound (x := eNG o r p) (r := r) (p := p) 8 17 (16) 320 (by norm_num) hE)

theorem cwd1_13 (T : TropFacts I o) (c : ZMod 4) (hc2 : (2 : ZMod 4) ≠ c) (r : ℕ) (hr : 400 ≤ r) :
    Covers c (WTG I o r) r (mkPiece 1 16 1 12 19 (-16) 320 8) := by
  intro p hlo hhi hp hc
  have hW := d1g_13 T c hc2 r p hlo hhi hp hc
  rw [floor_mk_s] at hlo; rw [floor_mk_t] at hhi
  have hE : (8 : ℤ) * (eNG o r p : ℤ) ≤ 19 * (r : ℤ) + (-16) * (p : ℤ) + (320) := by
    rcases eNG_cases (o := o) (r := r) (p := p) T.ho (by omega) with h | ⟨⟨_, c2, c3, c4⟩, e⟩ |
        ⟨⟨_, c2, c3, c4, _⟩, e⟩ | ⟨⟨_, c2, c3⟩, e⟩ | ⟨⟨_, c2, c3, c4, c5⟩, e⟩ |
        ⟨⟨_, c2, c3, c4⟩, e⟩ | ⟨hLC, e⟩
    · rw [h]; omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rcases hLC with ⟨g1, g2, _, g3, g4⟩ | ⟨g1, g2, _, g3, g4⟩ <;> rw [e] <;>
        rcases T.ho with rfl | rfl <;> omega
  show max (WG I r p) (eNG o r p : ℝ) ≤ _
  exact max_le hW (real_of_int_bound (x := eNG o r p) (r := r) (p := p) 8 19 (-16) 320 (by norm_num) hE)

theorem cwd1_14 (T : TropFacts I o) (c : ZMod 4) (hc2 : (2 : ZMod 4) ≠ c) (r : ℕ) (hr : 400 ≤ r) :
    Covers c (WTG I o r) r (mkPiece 1 12 1 8 17 (8) 320 8) := by
  intro p hlo hhi hp hc
  have hW := d1g_14 T c hc2 r p hlo hhi hp hc
  rw [floor_mk_s] at hlo; rw [floor_mk_t] at hhi
  have hE : (8 : ℤ) * (eNG o r p : ℤ) ≤ 17 * (r : ℤ) + (8) * (p : ℤ) + (320) := by
    rcases eNG_cases (o := o) (r := r) (p := p) T.ho (by omega) with h | ⟨⟨_, c2, c3, c4⟩, e⟩ |
        ⟨⟨_, c2, c3, c4, _⟩, e⟩ | ⟨⟨_, c2, c3⟩, e⟩ | ⟨⟨_, c2, c3, c4, c5⟩, e⟩ |
        ⟨⟨_, c2, c3, c4⟩, e⟩ | ⟨hLC, e⟩
    · rw [h]; omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rcases hLC with ⟨g1, g2, _, g3, g4⟩ | ⟨g1, g2, _, g3, g4⟩ <;> rw [e] <;>
        rcases T.ho with rfl | rfl <;> omega
  show max (WG I r p) (eNG o r p : ℝ) ≤ _
  exact max_le hW (real_of_int_bound (x := eNG o r p) (r := r) (p := p) 8 17 (8) 320 (by norm_num) hE)

theorem cwd1_15 (T : TropFacts I o) (c : ZMod 4) (hc2 : (2 : ZMod 4) ≠ c) (r : ℕ) (hr : 400 ≤ r) :
    Covers c (WTG I o r) r (mkPiece 1 8 1 4 19 (-8) 320 8) := by
  intro p hlo hhi hp hc
  have hW := d1g_15 T c hc2 r p hlo hhi hp hc
  rw [floor_mk_s] at hlo; rw [floor_mk_t] at hhi
  have hE : (8 : ℤ) * (eNG o r p : ℤ) ≤ 19 * (r : ℤ) + (-8) * (p : ℤ) + (320) := by
    rcases eNG_cases (o := o) (r := r) (p := p) T.ho (by omega) with h | ⟨⟨_, c2, c3, c4⟩, e⟩ |
        ⟨⟨_, c2, c3, c4, _⟩, e⟩ | ⟨⟨_, c2, c3⟩, e⟩ | ⟨⟨_, c2, c3, c4, c5⟩, e⟩ |
        ⟨⟨_, c2, c3, c4⟩, e⟩ | ⟨hLC, e⟩
    · rw [h]; omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rw [e]; rcases T.ho with rfl | rfl <;> omega
    · rcases hLC with ⟨g1, g2, _, g3, g4⟩ | ⟨g1, g2, _, g3, g4⟩ <;> rw [e] <;>
        rcases T.ho with rfl | rfl <;> omega
  show max (WG I r p) (eNG o r p : ℝ) ≤ _
  exact max_le hW (real_of_int_bound (x := eNG o r p) (r := r) (p := p) 8 19 (-8) 320 (by norm_num) hE)

end Covers

end CatalanFrames.HybCommon
