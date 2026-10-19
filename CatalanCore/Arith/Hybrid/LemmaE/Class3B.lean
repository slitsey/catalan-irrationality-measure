module

public import CatalanCore.Arith.Hybrid.LemmaE.Class3A
public import CatalanCore.Arith.Hybrid.DefBLam

@[expose] public section

/-!
# Lemma E, class 3: potentials, the residue table `TEw3`, the reduction `BE3` and its lifts

Potentials (DQ Prop. 2.3): rows `u`: `0` on the partners `c_x = r - p + 2x` and on the zone rows,
`1` on the rest of `C`; columns `v`: `2` on the `c_x`, `1` elsewhere.  `∑u + ∑v = 2r + m`.
-/

open Finset Polynomial CatalanCore CatalanCore.Basic

namespace CatalanCore.Arith.Hybrid

section

variable {o p : ℕ} [Fact p.Prime] {Fr : Frame} {r m k1 : ℕ}

/-- The partners `c_x = r - p + 2x` of the zone rows. -/
def isCz (p r m c : ℕ) : Prop := r - p ≤ c ∧ c < r - p + 2 * m ∧ (c - (r - p)) % 2 = 0

instance (p r m c : ℕ) : Decidable (isCz p r m c) := by unfold isCz; infer_instance

def wr (p r m c : ℕ) : ℕ := if c < r then (if isCz p r m c then 0 else 1) else 0

def wc (p r m c : ℕ) : ℕ := if c < r then (if isCz p r m c then 2 else 1) else 1

def rowLab (r m A : ℕ) : Prop := A < r ∨ (r ≤ A ∧ A < r + 2 * m ∧ (A - r) % 2 = 0)
def colLab (r m B : ℕ) : Prop := B < r ∨ (r ≤ B ∧ B < r + 2 * m ∧ (B - r) % 2 = 1)

noncomputable def TEw3 (p r m : ℕ) [Fact p.Prime] (D : SingData p (r + 2 * m) k1) (A B : ℕ) : ZMod p :=
  if A < B then TEoG D (wr p r m A + wc p r m B) A B
  else if B < A then TEoG D (wr p r m A + wc p r m B) B A
  else TEdG D (wr p r m A + wc p r m B) A

lemma feas3 (S : ESetup3 o p r m k1) {A B : ℕ} (hA : rowLab r m A) (hB : colLab r m B) :
    1 ≤ wr p r m A + wc p r m B ∧
    (A < B → B - A = p → 2 ≤ wr p r m A + wc p r m B) ∧
    (B < A → A - B = p → 2 ≤ wr p r m A + wc p r m B) ∧
    (A = B → wr p r m A + wc p r m B = 2) := by
  have := S.hpr; have := S.hk2r; have := S.hk1o; have := S.hN; have := S.p5
  unfold rowLab at hA
  unfold colLab at hB
  unfold wr wc isCz
  refine ⟨?_, ?_, ?_, ?_⟩
  · split_ifs <;> omega
  · intro h1 h2; split_ifs <;> omega
  · intro h1 h2; split_ifs <;> omega
  · intro h1; split_ifs <;> omega

theorem good_TEw3 {o : ℕ} (hL : LamData Fr o) (S : ESetup3 o p r m k1) {A B : ℕ} (hA : rowLab r m A)
    (hB : colLab r m B) :
    Good p ((p : ℚ) ^ (wr p r m A + wc p r m B) * Fr.Mn A B)
      (TEw3 p r m (sd3 S) A B) := by
  obtain ⟨f1, f2, f3, f4⟩ := feas3 S hA hB
  have hAN : A < r + 2 * m := by unfold rowLab at hA; omega
  have hBN : B < r + 2 * m := by unfold colLab at hB; omega
  have hSN := S.hN
  have hpr := S.hpr
  have hG := sd3_good hL S
  rcases lt_trichotomy A B with h | h | h
  · have e : TEw3 p r m (sd3 S) A B = TEoG (sd3 S) (wr p r m A + wc p r m B) A B := by
      unfold TEw3; rw [if_pos h]
    rw [e]
    exact good_TEoG hL S.p5 S.hk4 (sd3 S) hG h hBN f1 (by omega) (f2 h)
  · subst h
    have e : TEw3 p r m (sd3 S) A A = TEdG (sd3 S) (wr p r m A + wc p r m A) A := by
      unfold TEw3; rw [if_neg (lt_irrefl _), if_neg (lt_irrefl _)]
    rw [e]
    exact good_TEdG hL S.p5 S.hk4 (sd3 S) hG hAN (f4 rfl)
  · have e : TEw3 p r m (sd3 S) A B = TEoG (sd3 S) (wr p r m A + wc p r m B) B A := by
      unfold TEw3; rw [if_neg (by omega), if_pos h]
    rw [e, Mn_symm]
    exact good_TEoG hL S.p5 S.hk4 (sd3 S) hG h hAN f1 (by omega) (f3 h)

/-- The reduction matrix of Lemma E, class 3 (no `X`: every weight is `≥ 1`). -/
noncomputable def BE3 (p r m : ℕ) [Fact p.Prime] (D : SingData p (r + 2 * m) k1) :
    Matrix (Fin r ⊕ Fin m) (Fin r ⊕ Fin m) (RatFunc (ZMod p)) :=
  Matrix.of fun a b => rfC p (TEw3 p r m D (Frame.hybRow r m a) (Frame.hybCol r m b))

lemma rowLab_hyb (a : Fin r ⊕ Fin m) : rowLab r m (Frame.hybRow r m a) := by
  rcases a with c | i
  · have := c.2; show rowLab r m (c : ℕ); unfold rowLab; left; exact this
  · have := i.2; show rowLab r m (r + 2 * (i : ℕ)); unfold rowLab; right; omega

lemma colLab_hyb (b : Fin r ⊕ Fin m) : colLab r m (Frame.hybCol r m b) := by
  rcases b with c | i
  · have := c.2; show colLab r m (c : ℕ); unfold colLab; left; exact this
  · have := i.2; show colLab r m (r + 2 * (i : ℕ) + 1); unfold colLab; right; omega

theorem hred_E3 {o : ℕ} (hL : LamData Fr o) (S : ESetup3 o p r m k1) (a b : Fin r ⊕ Fin m) :
    ∃ g : (LocRing p)[X], toQ p g =
      C ((p : ℚ) ^ (wr p r m (Frame.hybRow r m a) + wc p r m (Frame.hybCol r m b))) *
        fullEntry Fr r m a b ∧ phiP p g = BE3 p r m (sd3 S) a b := by
  have hA := rowLab_hyb (r := r) (m := m) a
  have hB := colLab_hyb (r := r) (m := m) b
  have hAN : Frame.hybRow r m a < r + 2 * m := hybRow_lt a
  have hBN : Frame.hybCol r m b < r + 2 * m := hybCol_lt b
  rcases a with c | i <;> rcases b with c' | i'
  · by_cases hcc : c = c'
    · subst hcc
      have hA' : rowLab r m (c : ℕ) := hA
      have hB' : colLab r m (c : ℕ) := hB
      obtain ⟨f1, f2, f3, f4⟩ := feas3 S hA' hB'
      have hgood := good_TEw3 hL S hA' hB'
      obtain ⟨g, h1, h2⟩ := exists_lift_diag p (wr p r m c + wc p r m c) (Fr.Mn c c) hgood.1
      refine ⟨g, ?_, ?_⟩
      · rw [h1]; simp [fullEntry, Frame.hybRow, Frame.hybCol]
      · rw [h2]
        have e1 : redQ p ⟨_, hgood.1⟩ = TEw3 p r m (sd3 S) c c := hgood.2
        rw [e1, if_neg (by have := f4 rfl; omega), zero_add]
        simp [BE3, Frame.hybRow, Frame.hybCol]
    · obtain ⟨g, h1, h2⟩ := lift_good p (good_TEw3 hL S hA hB)
      refine ⟨g, ?_, ?_⟩
      · rw [h1]; simp [fullEntry, hcc, Frame.hybRow, Frame.hybCol]
      · rw [h2]; simp [BE3, Frame.hybRow, Frame.hybCol]
  · obtain ⟨g, h1, h2⟩ := lift_good p (good_TEw3 hL S hA hB)
    refine ⟨g, ?_, ?_⟩
    · rw [h1]; simp [fullEntry, Frame.hybRow, Frame.hybCol]
    · rw [h2]; simp [BE3, Frame.hybRow, Frame.hybCol]
  · obtain ⟨g, h1, h2⟩ := lift_good p (good_TEw3 hL S hA hB)
    refine ⟨g, ?_, ?_⟩
    · rw [h1]; simp [fullEntry, Frame.hybRow, Frame.hybCol]
    · rw [h2]; simp [BE3, Frame.hybRow, Frame.hybCol]
  · obtain ⟨g, h1, h2⟩ := lift_good p (good_TEw3 hL S hA hB)
    refine ⟨g, ?_, ?_⟩
    · rw [h1]; simp [fullEntry, Frame.hybRow, Frame.hybCol]
    · rw [h2]; simp [BE3, Frame.hybRow, Frame.hybCol]

end

end CatalanCore.Arith.Hybrid
