import CatalanCore.Uniform.Bank.Chi3Rank.Layer1
set_option Elab.async false

/-! # The class `p ≡ 5 (mod 6)` rank member (lane H, H16)

Fibres `x < min ((p+1)/2) (6m - 2p)`: digits `0, 1` are common nodes, digit `2` is a border node
(a row for `x` even, a column for `x` odd). -/

namespace CatalanCore.Uniform.Bank.Chi3Rank
open Polynomial Finset Module Matrix CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Uniform.Content.Hybrid CatalanCore.Uniform.Content.Member
  CatalanCore.Uniform.Content.RankProducer CatalanFrames.P6

section C5
variable {p : ℕ} [hp : Fact p.Prime] {B : ℕ} {f e : ℕ → ℚ}

theorem real_E5 (PS : PoleSplit p B f e) (r m : ℕ) (s : Finset (Fin r)) (x0 : ℕ)
    (hr : r = 4 * m) (hrp : r ≤ 2 * p) (hx0 : x0 < p) (hhigh : x0 + 2 * p < r + 2 * m)
    (heven : x0 % 2 = 0) (hpodd : p % 2 = 1) (hk0 : keptN r s x0) (hk1 : keptN r s (x0 + p))
    (hL0 : PS.Lf x0 = 0) (hL1 : PS.Lf (x0 + p) = -1 / 18) (hL2 : PS.Lf (x0 + 2 * p) = -23 / 360)
    (hE0 : PS.E x0 = 0) (hE1 : PS.E (x0 + p) = -13 / 72)
    (hE2 : PS.E (x0 + 2 * p) = -2059 / 10800) :
    Realizes PS (rowsOf r m s) (colsOf r m s) (x0 : ZMod p) E5 := by
  have hp0 := hp.out.pos
  have hrow : ∀ i, rowsOf r m s i % p = x0 →
      (rowsOf r m s i = x0 ∧ rowsOf r m s i / p = 0) ∨
      (rowsOf r m s i = x0 + p ∧ rowsOf r m s i / p = 1) ∨
      (rowsOf r m s i = x0 + 2 * p ∧ rowsOf r m s i / p = 2) := by
    intro i hmod
    have hn := (rowN_iff r m s _).1 ⟨i, rfl⟩
    refine node_three p x0 _ hp0 hx0 hmod ?_
    rcases hn with ⟨h, _⟩ | ⟨h1, h2, h3⟩ <;> omega
  have hcol : ∀ j, colsOf r m s j % p = x0 →
      (colsOf r m s j = x0 ∧ colsOf r m s j / p = 0) ∨
      (colsOf r m s j = x0 + p ∧ colsOf r m s j / p = 1) := by
    intro j hmod
    have hn := (colN_iff r m s _).1 ⟨j, rfl⟩
    have hlt : colsOf r m s j < x0 + 3 * p := by
      rcases hn with ⟨h, _⟩ | ⟨h1, h2, h3⟩ <;> omega
    rcases node_three p x0 _ hp0 hx0 hmod hlt with h | h | ⟨h, hd⟩
    · exact Or.inl h
    · exact Or.inr h
    · exfalso
      rcases hn with ⟨h', _⟩ | ⟨h1, h2, h3⟩ <;> omega
  refine realizes_of PS _ _ x0 hx0 E5 ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro i hmod
    rcases hrow i hmod with ⟨_, hd⟩ | ⟨_, hd⟩ | ⟨_, hd⟩ <;> rw [hd] <;> simp [E5]
  · intro d hd
    simp only [E5, Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl | rfl
    · exact (rowN_iff r m s _).2 (Or.inl (by simpa using hk0))
    · exact (rowN_iff r m s _).2 (Or.inl (by simpa using hk1))
    · exact (rowN_iff r m s _).2 (Or.inr ⟨by omega, by omega, by omega⟩)
  · intro j hmod
    rcases hcol j hmod with ⟨_, hd⟩ | ⟨_, hd⟩ <;> rw [hd] <;> simp [E5]
  · intro d hd
    simp only [E5, Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl
    · exact (colN_iff r m s _).2 (Or.inl (by simpa using hk0))
    · exact (colN_iff r m s _).2 (Or.inl (by simpa using hk1))
  · intro i hmod
    rcases hrow i hmod with ⟨hn, hd⟩ | ⟨hn, hd⟩ | ⟨hn, hd⟩
    · rw [hd, hn]; simpa [E5, vec3] using hL0
    · rw [hd, hn]; simpa [E5, vec3] using hL1
    · rw [hd, hn]; simpa [E5, vec3] using hL2
  · intro j hmod
    rcases hcol j hmod with ⟨hn, hd⟩ | ⟨hn, hd⟩
    · rw [hd, hn]; simpa [E5, vec3] using hL0
    · rw [hd, hn]; simpa [E5, vec3] using hL1
  · intro i hmod
    rcases hrow i hmod with ⟨hn, hd⟩ | ⟨hn, hd⟩ | ⟨hn, hd⟩
    · rw [hd, hn]; simpa [E5, vec3] using hE0
    · rw [hd, hn]; simpa [E5, vec3] using hE1
    · rw [hd, hn]; simpa [E5, vec3] using hE2

theorem real_O5 (PS : PoleSplit p B f e) (r m : ℕ) (s : Finset (Fin r)) (x0 : ℕ)
    (hr : r = 4 * m) (hrp : r ≤ 2 * p) (hx0 : x0 < p) (hhigh : x0 + 2 * p < r + 2 * m)
    (hodd : x0 % 2 = 1) (hpodd : p % 2 = 1) (hk0 : keptN r s x0) (hk1 : keptN r s (x0 + p))
    (hL0 : PS.Lf x0 = 0) (hL1 : PS.Lf (x0 + p) = -1 / 18) (hL2 : PS.Lf (x0 + 2 * p) = -23 / 360)
    (hE0 : PS.E x0 = 0) (hE1 : PS.E (x0 + p) = -13 / 72) :
    Realizes PS (rowsOf r m s) (colsOf r m s) (x0 : ZMod p) O5 := by
  have hp0 := hp.out.pos
  have hcol : ∀ j, colsOf r m s j % p = x0 →
      (colsOf r m s j = x0 ∧ colsOf r m s j / p = 0) ∨
      (colsOf r m s j = x0 + p ∧ colsOf r m s j / p = 1) ∨
      (colsOf r m s j = x0 + 2 * p ∧ colsOf r m s j / p = 2) := by
    intro j hmod
    have hn := (colN_iff r m s _).1 ⟨j, rfl⟩
    refine node_three p x0 _ hp0 hx0 hmod ?_
    rcases hn with ⟨h, _⟩ | ⟨h1, h2, h3⟩ <;> omega
  have hrow : ∀ i, rowsOf r m s i % p = x0 →
      (rowsOf r m s i = x0 ∧ rowsOf r m s i / p = 0) ∨
      (rowsOf r m s i = x0 + p ∧ rowsOf r m s i / p = 1) := by
    intro i hmod
    have hn := (rowN_iff r m s _).1 ⟨i, rfl⟩
    have hlt : rowsOf r m s i < x0 + 3 * p := by
      rcases hn with ⟨h, _⟩ | ⟨h1, h2, h3⟩ <;> omega
    rcases node_three p x0 _ hp0 hx0 hmod hlt with h | h | ⟨h, hd⟩
    · exact Or.inl h
    · exact Or.inr h
    · exfalso
      rcases hn with ⟨h', _⟩ | ⟨h1, h2, h3⟩ <;> omega
  refine realizes_of PS _ _ x0 hx0 O5 ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro i hmod
    rcases hrow i hmod with ⟨_, hd⟩ | ⟨_, hd⟩ <;> rw [hd] <;> simp [O5]
  · intro d hd
    simp only [O5, Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl
    · exact (rowN_iff r m s _).2 (Or.inl (by simpa using hk0))
    · exact (rowN_iff r m s _).2 (Or.inl (by simpa using hk1))
  · intro j hmod
    rcases hcol j hmod with ⟨_, hd⟩ | ⟨_, hd⟩ | ⟨_, hd⟩ <;> rw [hd] <;> simp [O5]
  · intro d hd
    simp only [O5, Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl | rfl
    · exact (colN_iff r m s _).2 (Or.inl (by simpa using hk0))
    · exact (colN_iff r m s _).2 (Or.inl (by simpa using hk1))
    · exact (colN_iff r m s _).2 (Or.inr ⟨by omega, by omega, by omega⟩)
  · intro i hmod
    rcases hrow i hmod with ⟨hn, hd⟩ | ⟨hn, hd⟩
    · rw [hd, hn]; simpa [O5, vec3] using hL0
    · rw [hd, hn]; simpa [O5, vec3] using hL1
  · intro j hmod
    rcases hcol j hmod with ⟨hn, hd⟩ | ⟨hn, hd⟩ | ⟨hn, hd⟩
    · rw [hd, hn]; simpa [O5, vec3] using hL0
    · rw [hd, hn]; simpa [O5, vec3] using hL1
    · rw [hd, hn]; simpa [O5, vec3] using hL2
  · intro i hmod
    rcases hrow i hmod with ⟨hn, hd⟩ | ⟨hn, hd⟩
    · rw [hd, hn]; simpa [O5, vec3] using hE0
    · rw [hd, hn]; simpa [O5, vec3] using hE1

end C5

theorem nz5 (p : ℕ) [hp : Fact p.Prime] (hN : N0 < p) : castV p (O5.cload 0) ≠ 0 := by
  rw [load5_val]
  refine castV_ne_zero_snd p _ (cast_ne_zero_of p _ ?_ ?_)
  · have : (-23 / 720 : ℚ).num = -23 := by decide +kernel
    show ¬ (p : ℤ) ∣ (-23 / 720 : ℚ).num
    rw [this]; intro h
    have h' := Int.natCast_dvd.1 h
    have := Nat.le_of_dvd (by norm_num : 0 < 23) (by simpa using h')
    unfold N0 at hN; omega
  · have : (-23 / 720 : ℚ).den = 720 := by decide +kernel
    show ¬ p ∣ (-23 / 720 : ℚ).den
    rw [this]; intro h
    have := Nat.le_of_dvd (by norm_num) h
    unfold N0 at hN; omega

theorem rank_c5 (r m p : ℕ) [hp : Fact p.Prime] (hr : r = 4 * m) (h6 : p % 6 = 5)
    (hN : N0 < p) (hrp : r ≤ 2 * p) (s : Finset (Fin r)) :
    ∃ M : RankMember p6Frame u3 q3 (fun c : Fin r => (c : ℕ))
        (fun j : Fin m => r + 2 * (j : ℕ)) (fun j : Fin m => r + 2 * (j : ℕ) + 1) s p,
      M.price + (min ((p + 1) / 2) (6 * m - 2 * p) - 0) ≤ 2 * r + 2 * m + 1 := by
  have hpodd : p % 2 = 1 := by omega
  have hbig : 3 * (r + 2 * m) + 1 ≤ p ^ 2 := by
    have h1 : 9 * p + 1 ≤ p ^ 2 := by unfold N0 at hN; nlinarith
    omega
  refine assemble r m p s E5 O5 0 (min ((p + 1) / 2) (6 * m - 2 * p)) 0
    (fun x => keptN r s x ∧ keptN r s (x + p)) (by norm_num) (Or.inr h6) hN hbig
    (by omega) ?_ E5_ok O5_ok E5_den O5_den rfl rfl rfl rfl ?_ ?_ load5 (nz5 p hN)
  · intro x hlo hhi hnp
    have hxr : x + p < r := by omega
    by_cases h0 : keptN r s x
    · refine ⟨x + p, hxr, fun h => hnp ⟨h0, h⟩, ?_⟩
      simp only [Nat.add_mod_right]; exact Nat.mod_eq_of_lt (by omega)
    · exact ⟨x, by omega, h0, Nat.mod_eq_of_lt (by omega)⟩
  · intro x0 hlo hhi hpar hk PS hL hE
    have hx0 : x0 < p := by omega
    obtain ⟨hl0, hl1, hl2, he0, he1, he2⟩ := lfE_c5 p h6 x0 (by omega)
    exact real_E5 PS r m s x0 hr hrp hx0 (by omega) hpar hpodd hk.1 hk.2
      (by rw [hL]; exact hl0) (by rw [hL]; exact hl1)
      (by rw [hL, show x0 + 2 * p = x0 + p * 2 by ring]; exact hl2)
      (by rw [hE]; exact he0) (by rw [hE]; exact he1)
      (by rw [hE, show x0 + 2 * p = x0 + p * 2 by ring]; exact he2)
  · intro x0 hlo hhi hpar hk PS hL hE
    have hx0 : x0 < p := by omega
    obtain ⟨hl0, hl1, hl2, he0, he1, he2⟩ := lfE_c5 p h6 x0 (by omega)
    exact real_O5 PS r m s x0 hr hrp hx0 (by omega) (by omega) hpodd hk.1 hk.2
      (by rw [hL]; exact hl0) (by rw [hL]; exact hl1)
      (by rw [hL, show x0 + 2 * p = x0 + p * 2 by ring]; exact hl2)
      (by rw [hE]; exact he0) (by rw [hE]; exact he1)

end CatalanCore.Uniform.Bank.Chi3Rank
