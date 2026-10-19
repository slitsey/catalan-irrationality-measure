module

public import CatalanFrames.Lambda.HybContentT

@[expose] public section

/-!
# λ: the content bound for `DhybT`, part 2: the piece covers for `lamWT = max (lamW) eN`

Every piece cover of `lamW` extends to `lamWT r p = max (lamW r p) (eN r p)`: the extra check is the
integer inequality `D · eN ≤ A r + B p + E`, an `omega` problem after `eN_arith`.
-/

open Finset Filter CatalanCore CatalanCore.Arith CatalanCore.Arith.Hybrid

namespace CatalanFrames.Lambda

/-- The weight including the dual excess. -/
noncomputable def lamWT (r p : ℕ) : ℝ := max (lamW r p) ((eN r p : ℕ) : ℝ)

lemma lamWT_nonneg (r p : ℕ) : 0 ≤ lamWT r p := (lamW_nonneg r p).trans (le_max_left _ _)

lemma covers_T_of {M : ℕ} (c : ZMod M) {r sn sd tn td : ℕ} {A B E D : ℤ} (hD : 0 < D)
    (hw : Covers c (lamW r) r (mkPiece sn sd tn td A B E D))
    (he : ∀ p, sn * r / sd < p → p ≤ tn * r / td → p.Prime → (p : ZMod M) = c →
      D * (eN r p : ℤ) ≤ A * r + B * p + E) :
    Covers c (lamWT r) r (mkPiece sn sd tn td A B E D) := by
  intro p hlo hhi hp hc
  have h1 := hw p hlo hhi hp hc
  rw [floor_mk_s] at hlo; rw [floor_mk_t] at hhi
  exact max_le h1 (real_of_int_bound D A B E hD (he p hlo hhi hp hc))

section Class3

variable {r : ℕ} (hr : 16 ≤ r)
include hr

lemma c3T_1 : Covers (3 : ZMod 4) (lamWT r) r (mkPiece 1 4 9 10 17 0 64 8) :=
  covers_T_of _ (by norm_num) (c3_1 r) fun p hlo hhi hp hc => by
    have h4 := cls4_mod3 hc
    rcases eN_arith r p hr hp with h | h | h | h <;> omega

lemma c3T_2 : Covers (3 : ZMod 4) (lamWT r) r (mkPiece 9 10 1 1 13 (-5) 32 4) :=
  covers_T_of _ (by norm_num) (c3_2 r) fun p hlo hhi hp hc => by
    have h4 := cls4_mod3 hc
    rcases eN_arith r p hr hp with h | h | h | h <;> omega

lemma c3T_3 : Covers (3 : ZMod 4) (lamWT r) r (mkPiece 1 1 5 4 7 (-3) 32 2) :=
  covers_T_of _ (by norm_num) (c3_3 r) fun p hlo hhi hp hc => by
    have h4 := cls4_mod3 hc
    rcases eN_arith r p hr hp with h | h | h | h <;> omega

lemma c3T_4 : Covers (3 : ZMod 4) (lamWT r) r (mkPiece 5 4 4 1 9 (-2) 32 4) :=
  covers_T_of _ (by norm_num) (c3_4 r) fun p hlo hhi hp hc => by
    have h4 := cls4_mod3 hc
    rcases eN_arith r p hr hp with h | h | h | h <;> omega

lemma c3T_5 : Covers (3 : ZMod 4) (lamWT r) r (mkPiece 4 1 5 1 5 (-1) 32 4) :=
  covers_T_of _ (by norm_num) (c3_5 r) fun p hlo hhi hp hc => by
    have h4 := cls4_mod3 hc
    rcases eN_arith r p hr hp with h | h | h | h <;> omega

end Class3

section Class1

variable {r : ℕ} (hr : 16 ≤ r)
include hr

lemma c1T_1 : Covers (1 : ZMod 4) (lamWT r) r (mkPiece 1 4 9 14 17 0 64 8) :=
  covers_T_of _ (by norm_num) (c1_1 r) fun p hlo hhi hp hc => by
    have h4 := cls4_mod1 hc
    rcases eN_arith r p hr hp with h | h | h | h <;> omega

lemma c1T_2 : Covers (1 : ZMod 4) (lamWT r) r (mkPiece 9 14 5 7 13 (-7) 32 4) :=
  covers_T_of _ (by norm_num) (c1_2 r) fun p hlo hhi hp hc => by
    have h4 := cls4_mod1 hc
    rcases eN_arith r p hr hp with h | h | h | h <;> omega

lemma c1T_3 : Covers (1 : ZMod 4) (lamWT r) r (mkPiece 5 7 1 1 9 (-7) 16 2) :=
  covers_T_of _ (by norm_num) (c1_3 r) fun p hlo hhi hp hc => by
    have h4 := cls4_mod1 hc
    rcases eN_arith r p hr hp with h | h | h | h <;> omega

lemma c1T_4 : Covers (1 : ZMod 4) (lamWT r) r (mkPiece 1 1 5 4 7 (-5) 16 2) :=
  covers_T_of _ (by norm_num) (c1_4 r) fun p hlo hhi hp hc => by
    have h4 := cls4_mod1 hc
    rcases eN_arith r p hr hp with h | h | h | h <;> omega

lemma c1T_5 : Covers (1 : ZMod 4) (lamWT r) r (mkPiece 5 4 4 3 9 (-6) 32 4) :=
  covers_T_of _ (by norm_num) (c1_5 r) fun p hlo hhi hp hc => by
    have h4 := cls4_mod1 hc
    rcases eN_arith r p hr hp with h | h | h | h <;> omega

lemma c1T_6 : Covers (1 : ZMod 4) (lamWT r) r (mkPiece 4 3 5 3 5 (-3) 32 4) :=
  covers_T_of _ (by norm_num) (c1_6 r) fun p hlo hhi hp hc => by
    have h4 := cls4_mod1 hc
    rcases eN_arith r p hr hp with h | h | h | h <;> omega

end Class1

end CatalanFrames.Lambda
