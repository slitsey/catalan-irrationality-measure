import CatalanCore.Uniform.Bank.Chi3Rank.Assemble
set_option Elab.async false

/-! # Realisation of the class-1 fibre certificates `E1`, `O1` (lane H, H16) -/

namespace CatalanCore.Uniform.Bank.Chi3Rank
open Polynomial Finset Module Matrix CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Uniform.Content.Hybrid CatalanCore.Uniform.Content.Member
  CatalanCore.Uniform.Content.RankProducer CatalanFrames.P6

/-- A node `≡ x0` below `x0 + 2p` has digit `0` or `1`. -/
theorem node_two (p x0 n : ℕ) (hp0 : 0 < p) (hx0 : x0 < p) (hmod : n % p = x0)
    (hlt : n < x0 + 2 * p) : (n = x0 ∧ n / p = 0) ∨ (n = x0 + p ∧ n / p = 1) := by
  have e := Nat.mod_add_div n p
  obtain ⟨d, hd⟩ : ∃ d, d = n / p := ⟨_, rfl⟩
  rw [← hd] at e ⊢
  rcases Nat.lt_or_ge d 2 with h | h
  · interval_cases d
    · left; refine ⟨by omega, rfl⟩
    · right; refine ⟨by omega, rfl⟩
  · have := Nat.mul_le_mul_left p h
    omega

/-- A node `≡ x0` below `x0 + 3p` has digit `0`, `1` or `2`. -/
theorem node_three (p x0 n : ℕ) (hp0 : 0 < p) (hx0 : x0 < p) (hmod : n % p = x0)
    (hlt : n < x0 + 3 * p) :
    (n = x0 ∧ n / p = 0) ∨ (n = x0 + p ∧ n / p = 1) ∨ (n = x0 + 2 * p ∧ n / p = 2) := by
  have e := Nat.mod_add_div n p
  obtain ⟨d, hd⟩ : ∃ d, d = n / p := ⟨_, rfl⟩
  rw [← hd] at e ⊢
  rcases Nat.lt_or_ge d 3 with h | h
  · interval_cases d
    · left; refine ⟨by omega, rfl⟩
    · right; left; refine ⟨by omega, rfl⟩
    · right; right; refine ⟨by omega, rfl⟩
  · have := Nat.mul_le_mul_left p h
    omega

theorem keptN_lt {r : ℕ} {s : Finset (Fin r)} {n : ℕ} (h : keptN r s n) : n < r := h.1

section C1
variable {p : ℕ} [hp : Fact p.Prime] {B : ℕ} {f e : ℕ → ℚ}

theorem real_E1 (PS : PoleSplit p B f e) (r m : ℕ) (s : Finset (Fin r)) (x0 : ℕ)
    (hr : r = 4 * m) (hrp : r ≤ 2 * p) (hx0 : x0 < p) (hlow : r ≤ x0 + p)
    (hhigh : x0 + p < r + 2 * m) (hodd : x0 % 2 = 1) (hpodd : p % 2 = 1)
    (hk : keptN r s x0) (hL0 : PS.Lf x0 = 0) (hL1 : PS.Lf (x0 + p) = 1 / 72)
    (hE0 : PS.E x0 = 1 / 6) (hE1 : PS.E (x0 + p) = 163 / 864) :
    Realizes PS (rowsOf r m s) (colsOf r m s) (x0 : ZMod p) E1 := by
  have hp0 := hp.out.pos
  have hrow : ∀ i, rowsOf r m s i % p = x0 →
      (rowsOf r m s i = x0 ∧ rowsOf r m s i / p = 0) ∨
      (rowsOf r m s i = x0 + p ∧ rowsOf r m s i / p = 1) := by
    intro i hmod
    have hn := (rowN_iff r m s _).1 ⟨i, rfl⟩
    refine node_two p x0 _ hp0 hx0 hmod ?_
    rcases hn with ⟨h, _⟩ | ⟨h1, h2, h3⟩ <;> omega
  have hcol : ∀ j, colsOf r m s j % p = x0 →
      (colsOf r m s j = x0 ∧ colsOf r m s j / p = 0) := by
    intro j hmod
    have hn := (colN_iff r m s _).1 ⟨j, rfl⟩
    have hlt : colsOf r m s j < x0 + 2 * p := by
      rcases hn with ⟨h, _⟩ | ⟨h1, h2, h3⟩ <;> omega
    rcases node_two p x0 _ hp0 hx0 hmod hlt with h | ⟨h, hd⟩
    · exact h
    · exfalso
      rcases hn with ⟨h', _⟩ | ⟨h1, h2, h3⟩ <;> omega
  refine realizes_of PS _ _ x0 hx0 E1 ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro i hmod
    rcases hrow i hmod with ⟨_, hd⟩ | ⟨_, hd⟩ <;> rw [hd] <;> simp [E1]
  · intro d hd
    simp only [E1, Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl
    · exact (rowN_iff r m s _).2 (Or.inl (by simpa using hk))
    · exact (rowN_iff r m s _).2 (Or.inr ⟨by omega, by omega, by omega⟩)
  · intro j hmod
    rw [(hcol j hmod).2]; simp [E1]
  · intro d hd
    simp only [E1, Finset.mem_singleton] at hd
    subst hd
    exact (colN_iff r m s _).2 (Or.inl (by simpa using hk))
  · intro i hmod
    rcases hrow i hmod with ⟨hn, hd⟩ | ⟨hn, hd⟩
    · rw [hd, hn]; simpa [E1, vec3] using hL0
    · rw [hd, hn]; simpa [E1, vec3] using hL1
  · intro j hmod
    obtain ⟨hn, hd⟩ := hcol j hmod
    rw [hd, hn]; simpa [E1, vec3] using hL0
  · intro i hmod
    rcases hrow i hmod with ⟨hn, hd⟩ | ⟨hn, hd⟩
    · rw [hd, hn]; simpa [E1, vec3] using hE0
    · rw [hd, hn]; simpa [E1, vec3] using hE1

theorem real_O1 (PS : PoleSplit p B f e) (r m : ℕ) (s : Finset (Fin r)) (x0 : ℕ)
    (hr : r = 4 * m) (hrp : r ≤ 2 * p) (hx0 : x0 < p) (hlow : r ≤ x0 + p)
    (hhigh : x0 + p < r + 2 * m) (heven : x0 % 2 = 0) (hpodd : p % 2 = 1)
    (hk : keptN r s x0) (hL0 : PS.Lf x0 = 0) (hL1 : PS.Lf (x0 + p) = 1 / 72)
    (hE0 : PS.E x0 = 1 / 6) :
    Realizes PS (rowsOf r m s) (colsOf r m s) (x0 : ZMod p) O1 := by
  have hp0 := hp.out.pos
  have hcol : ∀ j, colsOf r m s j % p = x0 →
      (colsOf r m s j = x0 ∧ colsOf r m s j / p = 0) ∨
      (colsOf r m s j = x0 + p ∧ colsOf r m s j / p = 1) := by
    intro j hmod
    have hn := (colN_iff r m s _).1 ⟨j, rfl⟩
    refine node_two p x0 _ hp0 hx0 hmod ?_
    rcases hn with ⟨h, _⟩ | ⟨h1, h2, h3⟩ <;> omega
  have hrow : ∀ i, rowsOf r m s i % p = x0 →
      (rowsOf r m s i = x0 ∧ rowsOf r m s i / p = 0) := by
    intro i hmod
    have hn := (rowN_iff r m s _).1 ⟨i, rfl⟩
    have hlt : rowsOf r m s i < x0 + 2 * p := by
      rcases hn with ⟨h, _⟩ | ⟨h1, h2, h3⟩ <;> omega
    rcases node_two p x0 _ hp0 hx0 hmod hlt with h | ⟨h, hd⟩
    · exact h
    · exfalso
      rcases hn with ⟨h', _⟩ | ⟨h1, h2, h3⟩ <;> omega
  refine realizes_of PS _ _ x0 hx0 O1 ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro i hmod
    rw [(hrow i hmod).2]; simp [O1]
  · intro d hd
    simp only [O1, Finset.mem_singleton] at hd
    subst hd
    exact (rowN_iff r m s _).2 (Or.inl (by simpa using hk))
  · intro j hmod
    rcases hcol j hmod with ⟨_, hd⟩ | ⟨_, hd⟩ <;> rw [hd] <;> simp [O1]
  · intro d hd
    simp only [O1, Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl
    · exact (colN_iff r m s _).2 (Or.inl (by simpa using hk))
    · exact (colN_iff r m s _).2 (Or.inr ⟨by omega, by omega, by omega⟩)
  · intro i hmod
    obtain ⟨hn, hd⟩ := hrow i hmod
    rw [hd, hn]; simpa [O1, vec3] using hL0
  · intro j hmod
    rcases hcol j hmod with ⟨hn, hd⟩ | ⟨hn, hd⟩
    · rw [hd, hn]; simpa [O1, vec3] using hL0
    · rw [hd, hn]; simpa [O1, vec3] using hL1
  · intro i hmod
    obtain ⟨hn, hd⟩ := hrow i hmod
    rw [hd, hn]; simpa [O1, vec3] using hE0

end C1

end CatalanCore.Uniform.Bank.Chi3Rank
