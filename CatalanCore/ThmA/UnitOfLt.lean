module

public import CatalanCore.ThmA.UnitStep
public import CatalanCore.ThmA.CC

/-!
# `unit_of_lt`: `u(K,s) ≠ 0` in `𝔽_ℓ` whenever `s + K < ℓ` and `s ≥ K - 1`

Proof: `u(K,s)` is an `ℓ`-adic unit of `ℚ` (induction along the path with the s-step and K-step
identities and the window ledger), and an `ℓ`-unit Krylov determinant with `ℓ`-integral entries
reduces to a nonzero element of `𝔽_ℓ`.
-/

@[expose] public section

open Finset Matrix

namespace CatalanCore.ThmA

variable {l : ℕ} [hl : Fact l.Prime]

/-- Units along the diagonal `s = K - 1`. -/
theorem LU_diag (K0 : ℕ) (h2 : 2 * K0 ≤ l) :
    ∀ m : ℕ, m + 1 ≤ K0 → LU l (uK ℚ (m + 1) m)
  | 0, _ => by rw [uK_one]; simpa using (LU.one : LU l 1)
  | m + 1, hm => by
    have ih := LU_diag K0 h2 m (by omega)
    have s1 := LU_uK_succ (l := l) (m + 1) m (by omega) (by omega) (by omega) ih
    have s2 := LU_uK_succ (l := l) (m + 1) (m + 1) (by omega) (by omega) (by omega) s1
    exact LU_uK_pred (l := l) (m + 1) (by omega) (by omega) s2

/-- Sweep in `s`. -/
theorem LU_sweep (m s0 : ℕ) (h : s0 + (m + 1) < l) (hbase : LU l (uK ℚ (m + 1) m)) :
    ∀ s, m ≤ s → s ≤ s0 → LU l (uK ℚ (m + 1) s) := by
  intro s hs
  induction s, hs using Nat.le_induction with
  | base => intro _; exact hbase
  | succ s hs ih =>
    intro hs0
    exact LU_uK_succ (l := l) (m + 1) s (by omega) (by omega) (by omega) (ih (by omega))

/-- `ℓ`-integral inverse of a natural number. -/
def invNat (n : ℕ) (hn : 0 < n) (hnl : n < l) : Rl l := ⟨(n : ℚ)⁻¹, (LU_natCast_lt hn hnl).2.2⟩

lemma phi_invNat (n : ℕ) (hn : 0 < n) (hnl : n < l) :
    phi l (invNat n hn hnl) = ((n : ZMod l))⁻¹ := by
  have h1 : invNat n hn hnl * (⟨(n : ℚ), (LU_natCast_lt hn hnl).2.1⟩ : Rl l) = 1 :=
    Subtype.ext (inv_mul_cancel₀ (LU_natCast_lt hn hnl).1)
  have := congrArg (phi l) h1
  rw [map_mul, map_one] at this
  have h2 : phi l (⟨(n : ℚ), (LU_natCast_lt hn hnl).2.1⟩ : Rl l) = (n : ZMod l) := by
    simp [phi_apply]
  rw [h2] at this
  exact eq_inv_of_mul_eq_one_left this

/-- Lifted Cauchy-type matrix over `Rl l`. -/
def CmR (K s : ℕ) (h : K + s ≤ l) : Matrix (Fin K) (Fin s) (Rl l) :=
  Matrix.of fun a j => invNat ((a : ℕ) + (j : ℕ) + 1) (by omega)
    (by have := a.2; have := j.2; omega)

/-- Lifted start vector. -/
def wvR (K s : ℕ) (h : K + s + 1 ≤ l) : Fin K → Rl l :=
  fun a => invNat ((a : ℕ) + s + 1) (by omega) (by have := a.2; omega)

lemma CmR_map_val (K s : ℕ) (h : K + s ≤ l) :
    (CmR (l := l) K s h).map (Rl l).subtype = Cmat ℚ K s := by
  ext a j
  simp [CmR, invNat, Cmat]

lemma CmR_map_phi (K s : ℕ) (h : K + s ≤ l) :
    (CmR (l := l) K s h).map (phi l) = Cmat (ZMod l) K s := by
  ext a j
  simp only [CmR, Matrix.map_apply, Matrix.of_apply, phi_invNat, Cmat]
  push_cast
  simp

lemma wvR_val (K s : ℕ) (h : K + s + 1 ≤ l) : (Rl l).subtype ∘ wvR (l := l) K s h = wvec ℚ K s := by
  ext a
  simp [wvR, invNat, wvec]

lemma wvR_phi (K s : ℕ) (h : K + s + 1 ≤ l) : phi l ∘ wvR (l := l) K s h = wvec (ZMod l) K s := by
  ext a
  simp only [Function.comp, wvR, phi_invNat, wvec]
  push_cast
  simp

/-- An `ℓ`-unit `u(K,s)` over `ℚ` reduces to a nonzero element of `𝔽_ℓ`. -/
theorem uK_zmod_ne_of_LU (K s : ℕ) (h : K + s + 1 ≤ l) (hu : LU l (uK ℚ K s)) :
    uK (ZMod l) K s ≠ 0 := by
  have hN : ((CmR (l := l) K s (by omega)) * (CmR (l := l) K s (by omega))ᵀ).map (Rl l).subtype =
      Nmat ℚ K s := by
    rw [Matrix.map_mul, Matrix.transpose_map, CmR_map_val]; rfl
  have hN' : ((CmR (l := l) K s (by omega)) * (CmR (l := l) K s (by omega))ᵀ).map (phi l) =
      Nmat (ZMod l) K s := by
    rw [Matrix.map_mul, Matrix.transpose_map, CmR_map_phi]; rfl
  have := kdet_phi_ne_zero (CmR (l := l) K s (by omega) * (CmR (l := l) K s (by omega))ᵀ)
    (wvR (l := l) K s h) (by rw [hN, wvR_val]; exact hu)
  rw [hN', wvR_phi] at this
  exact this

/-- **Unit-ratio lemma**: `u(K,s) ≠ 0` in `𝔽_ℓ` for `s ≥ K - 1`, `s + K < ℓ`. -/
theorem unit_of_lt_proof (K s : ℕ) (hK : 1 ≤ K) (hs : K - 1 ≤ s) (hlt : s + K < l) :
    uK (ZMod l) K s ≠ 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, K = m + 1 := ⟨K - 1, by omega⟩
  have hd := LU_diag (l := l) (m + 1) (by omega) m le_rfl
  have hsw := LU_sweep (l := l) m s (by omega) hd s (by omega) le_rfl
  exact uK_zmod_ne_of_LU (m + 1) s (by omega) hsw

end CatalanCore.ThmA
