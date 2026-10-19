module

public import CatalanFrames.Lambda.HybBounds

@[expose] public section

/-!
# λ: the piece tables (simplified route: trivial D1 on `(0, 1/4]`)

Class `3 (mod 4)` (`k = (p+1)/4`, "j = 1") and class `1 (mod 4)` (`k = (3p+1)/4`, "j = 3").
Each piece is a linear bound `α r + β p + C` for `lamX r p`, proved by `omega` from the dual
bounds `lamX_D1/D2/D3/D45/D6`.  The integral of the tables is `1579/420` (checked in `HybTotal`).
-/

open Finset CatalanCore CatalanCore.Arith CatalanCore.Arith.Hybrid

namespace CatalanFrames.Lambda

/-- The weight function of the summation. -/
noncomputable def lamW (r p : ℕ) : ℝ := (lamX r p : ℝ)

/-! ### Class 3 (mod 4) -/

lemma c3_1 (r : ℕ) : Covers (3 : ZMod 4) (lamW r) r (mkPiece 1 4 9 10 17 0 64 8) := by
  intro p hlo hhi hp hc
  rw [floor_mk_s] at hlo; rw [floor_mk_t] at hhi
  have h3 := cls4_mod3 hc
  have h2 : p ≠ 2 := by omega
  have hb := lamX_D3 r p hp h2 (by omega) (by omega)
  show (lamX r p : ℝ) ≤ _
  exact real_of_int_bound 8 17 0 64 (by norm_num) (by omega)

lemma c3_2 (r : ℕ) : Covers (3 : ZMod 4) (lamW r) r (mkPiece 9 10 1 1 13 (-5) 32 4) := by
  intro p hlo hhi hp hc
  rw [floor_mk_s] at hlo; rw [floor_mk_t] at hhi
  have h3 := cls4_mod3 hc
  have h2 : p ≠ 2 := by omega
  obtain ⟨u, L, h1, h4, h5, h6, hb⟩ := lamX_D2 r p hp h2 (by omega) (by omega)
  have hk := lam_kq_eq h3
  show (lamX r p : ℝ) ≤ _
  exact real_of_int_bound 4 13 (-5) 32 (by norm_num) (by omega)

lemma c3_3 (r : ℕ) : Covers (3 : ZMod 4) (lamW r) r (mkPiece 1 1 5 4 7 (-3) 32 2) := by
  intro p hlo hhi hp hc
  rw [floor_mk_s] at hlo; rw [floor_mk_t] at hhi
  have h3 := cls4_mod3 hc
  have h2 : p ≠ 2 := by omega
  have hb := lamX_D45 r p hp h2 (by omega)
  have hk := lam_kq_eq h3
  show (lamX r p : ℝ) ≤ _
  exact real_of_int_bound 2 7 (-3) 32 (by norm_num) (by omega)

lemma c3_4 (r : ℕ) : Covers (3 : ZMod 4) (lamW r) r (mkPiece 5 4 4 1 9 (-2) 32 4) := by
  intro p hlo hhi hp hc
  rw [floor_mk_s] at hlo; rw [floor_mk_t] at hhi
  have h3 := cls4_mod3 hc
  have h2 : p ≠ 2 := by omega
  have hb := lamX_D45 r p hp h2 (by omega)
  have hk := lam_kq_eq h3
  show (lamX r p : ℝ) ≤ _
  exact real_of_int_bound 4 9 (-2) 32 (by norm_num) (by omega)

lemma c3_5 (r : ℕ) : Covers (3 : ZMod 4) (lamW r) r (mkPiece 4 1 5 1 5 (-1) 32 4) := by
  intro p hlo hhi hp hc
  rw [floor_mk_s] at hlo; rw [floor_mk_t] at hhi
  have h3 := cls4_mod3 hc
  have h2 : p ≠ 2 := by omega
  have hk := lam_kq_eq h3
  have hb := lamX_D6 r p hp h2 (by omega) (by omega)
  show (lamX r p : ℝ) ≤ _
  exact real_of_int_bound 4 5 (-1) 32 (by norm_num) (by omega)

/-! ### Class 1 (mod 4) -/

lemma c1_1 (r : ℕ) : Covers (1 : ZMod 4) (lamW r) r (mkPiece 1 4 9 14 17 0 64 8) := by
  intro p hlo hhi hp hc
  rw [floor_mk_s] at hlo; rw [floor_mk_t] at hhi
  have h1 := cls4_mod1 hc
  have h2 : p ≠ 2 := by omega
  have hb := lamX_D3 r p hp h2 (by omega) (by omega)
  show (lamX r p : ℝ) ≤ _
  exact real_of_int_bound 8 17 0 64 (by norm_num) (by omega)

lemma c1_2 (r : ℕ) : Covers (1 : ZMod 4) (lamW r) r (mkPiece 9 14 5 7 13 (-7) 32 4) := by
  intro p hlo hhi hp hc
  rw [floor_mk_s] at hlo; rw [floor_mk_t] at hhi
  have h1 := cls4_mod1 hc
  have h2 : p ≠ 2 := by omega
  obtain ⟨u, L, h1', h4, h5, h6, hb⟩ := lamX_D2 r p hp h2 (by omega) (by omega)
  have hk := lam_kq_eq1 h1
  show (lamX r p : ℝ) ≤ _
  exact real_of_int_bound 4 13 (-7) 32 (by norm_num) (by omega)

lemma c1_3 (r : ℕ) : Covers (1 : ZMod 4) (lamW r) r (mkPiece 5 7 1 1 9 (-7) 16 2) := by
  intro p hlo hhi hp hc
  rw [floor_mk_s] at hlo; rw [floor_mk_t] at hhi
  have h1 := cls4_mod1 hc
  have h2 : p ≠ 2 := by omega
  obtain ⟨u, L, h1', h4, h5, h6, hb⟩ := lamX_D2 r p hp h2 (by omega) (by omega)
  have hk := lam_kq_eq1 h1
  show (lamX r p : ℝ) ≤ _
  exact real_of_int_bound 2 9 (-7) 16 (by norm_num) (by omega)

lemma c1_4 (r : ℕ) : Covers (1 : ZMod 4) (lamW r) r (mkPiece 1 1 5 4 7 (-5) 16 2) := by
  intro p hlo hhi hp hc
  rw [floor_mk_s] at hlo; rw [floor_mk_t] at hhi
  have h1 := cls4_mod1 hc
  have h2 : p ≠ 2 := by omega
  have hb := lamX_D45 r p hp h2 (by omega)
  have hk := lam_kq_eq1 h1
  show (lamX r p : ℝ) ≤ _
  exact real_of_int_bound 2 7 (-5) 16 (by norm_num) (by omega)

lemma c1_5 (r : ℕ) : Covers (1 : ZMod 4) (lamW r) r (mkPiece 5 4 4 3 9 (-6) 32 4) := by
  intro p hlo hhi hp hc
  rw [floor_mk_s] at hlo; rw [floor_mk_t] at hhi
  have h1 := cls4_mod1 hc
  have h2 : p ≠ 2 := by omega
  have hb := lamX_D45 r p hp h2 (by omega)
  have hk := lam_kq_eq1 h1
  show (lamX r p : ℝ) ≤ _
  exact real_of_int_bound 4 9 (-6) 32 (by norm_num) (by omega)

lemma c1_6 (r : ℕ) : Covers (1 : ZMod 4) (lamW r) r (mkPiece 4 3 5 3 5 (-3) 32 4) := by
  intro p hlo hhi hp hc
  rw [floor_mk_s] at hlo; rw [floor_mk_t] at hhi
  have h1 := cls4_mod1 hc
  have h2 : p ≠ 2 := by omega
  have hk := lam_kq_eq1 h1
  have hb := lamX_D6 r p hp h2 (by omega) (by omega)
  show (lamX r p : ℝ) ≤ _
  exact real_of_int_bound 4 5 (-3) 32 (by norm_num) (by omega)

/-! ### Prefix and tails -/

lemma lam_prefix (r p : ℕ) : lamW r p ≤ 9 / 4 * r := by
  have hb := lamX_D1 r p
  have := real_of_int_bound (x := lamX r p) (r := r) (p := p) 4 9 0 0 (by norm_num) (by omega)
  show (lamX r p : ℝ) ≤ _
  norm_num at this
  linarith

lemma lam_tail3 (r p : ℕ) (hp : p.Prime) (h3 : p % 4 = 3) (ht : 5 * r < p) : lamX r p = 0 := by
  have h2 : p ≠ 2 := by omega
  have hk := lam_kq_eq h3
  have := lamX_D6 r p hp h2 (by omega) (by omega)
  omega

lemma lam_tail1 (r p : ℕ) (hp : p.Prime) (h1 : p % 4 = 1) (ht : 5 * r / 3 < p) : lamX r p = 0 := by
  have h2 : p ≠ 2 := by omega
  have hk := lam_kq_eq1 h1
  have := lamX_D6 r p hp h2 (by omega) (by omega)
  omega

end CatalanFrames.Lambda
