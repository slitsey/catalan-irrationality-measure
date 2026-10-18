module

public import CatalanCore.ThmA.KStep
public import Mathlib.Data.ZMod.Basic
public import Mathlib.FieldTheory.Finite.Basic

/-!
# Lemma CC over `𝔽_ℓ` via the recursion shortcut

Over any field in which `1, …, 3K` are nonzero, `u(K, K) ≠ 0` and `u(K, K+1) ≠ 0`, by induction on
`K` using the K-step and two s-steps.  For `ℓ ≡ 3 (mod 4)`, `K = (ℓ+1)/4` one has `3K < ℓ`.
-/

@[expose] public section

open Finset Matrix

namespace CatalanCore.ThmA

variable {F : Type*} [Field F] {N : ℕ}

lemma uK_one (s : ℕ) : uK F 1 s = 1 / ((s : F) + 1) := by
  simp [uK, kdet, krylov, Nmat, wvec, Matrix.det_unique]

/-- Base-to-top induction: `u(K,K) ≠ 0` and `u(K,K+1) ≠ 0` whenever `3K ≤ N`. -/
theorem uK_ne_zero_diag (h : CharGt F N) (K : ℕ) (hK : 1 ≤ K) (hN : 3 * K ≤ N) :
    uK F K K ≠ 0 ∧ uK F K (K + 1) ≠ 0 := by
  induction K, hK using Nat.le_induction with
  | base =>
    have h2 : ((1 : ℕ) : F) + 1 ≠ 0 := by
      have e : ((1 : ℕ) : F) + 1 = ((2 : ℕ) : F) := by norm_num
      rw [e]; exact h.ne (by omega) (by omega)
    have h3 : ((1 + 1 : ℕ) : F) + 1 ≠ 0 := by
      have e : ((1 + 1 : ℕ) : F) + 1 = ((3 : ℕ) : F) := by norm_num
      rw [e]; exact h.ne (by omega) (by omega)
    refine ⟨?_, ?_⟩
    · rw [uK_one]; exact one_div_ne_zero h2
    · rw [uK_one]; exact one_div_ne_zero h3
  | succ m hm ih =>
    obtain ⟨-, ih2⟩ := ih (by omega)
    have k1 : uK F (m + 1) m ≠ 0 := uK_pred_ne h m hm (by omega) ih2
    have k2 : uK F (m + 1) (m + 1) ≠ 0 := uK_succ_ne h (m + 1) m (by omega) (by omega) (by omega) k1
    exact ⟨k2, uK_succ_ne h (m + 1) (m + 1) (by omega) (by omega) (by omega) k2⟩

lemma charGt_zmod (l : ℕ) [Fact l.Prime] : CharGt (ZMod l) (l - 1) := by
  intro n hn hle
  rw [Ne, ZMod.natCast_eq_zero_iff]
  exact fun hd => absurd (Nat.le_of_dvd hn hd) (by omega)

/-- **Lemma CC, shortcut (i)**: over `𝔽_ℓ`, `ℓ ≡ 3 (mod 4)`, `K = (ℓ+1)/4`, `s ∈ {K, K+1}`. -/
theorem uK_ne_zero_CC (l : ℕ) [Fact l.Prime] (K s : ℕ) (hl : l % 4 = 3) (hl7 : 7 ≤ l)
    (hK : K = (l + 1) / 4) (hs : s = K ∨ s = K + 1) : uK (ZMod l) K s ≠ 0 := by
  have h := uK_ne_zero_diag (charGt_zmod l) K (by omega) (by omega)
  rcases hs with rfl | rfl
  · exact h.1
  · exact h.2

end CatalanCore.ThmA
