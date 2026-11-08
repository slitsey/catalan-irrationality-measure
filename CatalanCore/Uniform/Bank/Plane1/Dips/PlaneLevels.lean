module

public import CatalanCore.Uniform.Bank.Plane1.Dips.Levels
public import CatalanCore.Uniform.Bank.Plane1.Inst

@[expose] public section
set_option Elab.async false
set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.unusedVariables false
set_option linter.unusedTactic false

/-! # The levels of the plane frames (wave R0; ledger R01-R03)

For `planeFrame σ a b c h0` and a prime `p ≥ 7`, the three atoms are `0 : 3k - ρ`, `1 : 2k - 1`, `2 : k` (`Plane1.Inst.pl`).
Their first polar indices and cofactors are

* `k - ` atom 2: `k₀ = p`, `m₀ = 1`; atom 1: `k₀ = (p + 1)/2`, `m₀ = 1`;
* atom 0: `k₀ = (n p + ρ)/3`, `m₀ = n`, where `n ∈ {1, 2}` is the class (`3 ∣ n p + ρ`).

So `Vp t` and `Up t` (`Levels.Vp_closed`, `Up_closed`) are explicit sums over the counts `Ucnt` of the three atoms:
`planeV`, `planeU`.  The counts depend on `t` only through `⌊t/p⌋` and the position of `t mod p` against `k₀`. -/

namespace CatalanCore.Uniform.Bank.Plane1.Dips
open Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid CatalanCore.Uniform.Bank.Plane1

section Plane

variable (σ : Support) (a b c : ℤ) (h0 : a + b + c = 0) {p : ℕ} [hp : Fact p.Prime]

theorem plane_den_le (i : Fin (planeFrame σ a b c h0).d) : ((planeFrame σ a b c h0).μ i).den ≤ 3 := by
  have hi : i.1 < 3 := i.2
  obtain ⟨j, hj⟩ := i
  interval_cases j
  · change (σ.shift).den ≤ 3
    rw [shift_den]
  · change ((1 / 2 : ℚ)).den ≤ 3
    rw [half_den]; norm_num
  · change ((1 : ℚ)).den ≤ 3
    rw [one_den]; norm_num

variable {σ a b c h0}

theorem plane_not_dvd_den (hp7 : 7 ≤ p) (i : Fin (planeFrame σ a b c h0).d) : ¬ p ∣ ((planeFrame σ a b c h0).μ i).den := fun h => by
  have := Nat.le_of_dvd ((planeFrame σ a b c h0).μ i).den_pos h
  have := plane_den_le σ a b c h0 i
  omega

/-- Atom 2 (`k`): `k₀ = p`, `m₀ = 1`. -/
theorem k0_C (hp7 : 7 ≤ p) : k0 p (planeFrame σ a b c h0) ⟨2, by show 2 < 3; norm_num⟩ = p := by
  refine k0_eq_of _ (plane_not_dvd_den hp7 _) hp.out.one_lt.le (le_refl _) ?_
  rw [lin_plane σ a b c h0 _ (by omega)]
  simp [pl]

theorem m0_C (hp7 : 7 ≤ p) : m0 p (planeFrame σ a b c h0) ⟨2, by show 2 < 3; norm_num⟩ = 1 := by
  unfold m0
  rw [k0_C hp7, lin_plane σ a b c h0 _ (by omega)]
  simp [pl, Nat.div_self hp.out.pos]

/-- Atom 1 (`2k - 1`): `k₀ = (p + 1)/2`, `m₀ = 1`. -/
theorem k0_B (hp7 : 7 ≤ p) : k0 p (planeFrame σ a b c h0) ⟨1, by show 1 < 3; norm_num⟩ = (p + 1) / 2 := by
  have hodd := (hp.out.eq_one_or_self_of_dvd 2)
  have h2 : p % 2 = 1 := by
    by_contra h
    have : 2 ∣ p := by omega
    rcases hodd this with h | h <;> omega
  refine k0_eq_of _ (plane_not_dvd_den hp7 _) (by omega) (by omega) ?_
  rw [lin_plane σ a b c h0 _ (by omega)]
  simp only [pl]
  exact ⟨1, by omega⟩

theorem m0_B (hp7 : 7 ≤ p) : m0 p (planeFrame σ a b c h0) ⟨1, by show 1 < 3; norm_num⟩ = 1 := by
  have hodd := (hp.out.eq_one_or_self_of_dvd 2)
  have h2 : p % 2 = 1 := by
    by_contra h
    have : 2 ∣ p := by omega
    rcases hodd this with h | h <;> omega
  unfold m0
  rw [k0_B hp7, lin_plane σ a b c h0 _ (by omega)]
  simp only [pl]
  have : 2 * ((p + 1) / 2) - 1 = p * 1 := by omega
  rw [this, Nat.mul_div_cancel_left _ hp.out.pos]

/-- Atom 0 (`3k - ρ`): `k₀ = (n p + ρ)/3`, `m₀ = n`, for the class `n ∈ {1, 2}` with `3 ∣ n p + ρ`. -/
theorem k0_A (hp7 : 7 ≤ p) {n : ℕ} (hn : n = 1 ∨ n = 2) (h3 : 3 ∣ n * p + σ.rho) :
    k0 p (planeFrame σ a b c h0) ⟨0, by show 0 < 3; norm_num⟩ = (n * p + σ.rho) / 3 ∧ m0 p (planeFrame σ a b c h0) ⟨0, by show 0 < 3; norm_num⟩ = n := by
  have hr1 : 1 ≤ σ.rho := by cases σ <;> simp [Support.rho]
  have hr2 : σ.rho ≤ 2 := by cases σ <;> simp [Support.rho]
  have hk1 : 1 ≤ (n * p + σ.rho) / 3 := by
    obtain ⟨t, ht⟩ := h3
    rcases hn with rfl | rfl <;> omega
  have hkp : (n * p + σ.rho) / 3 ≤ p := by
    rcases hn with rfl | rfl <;> omega
  have hlin : lin (planeFrame σ a b c h0) ⟨0, by show 0 < 3; norm_num⟩ ((n * p + σ.rho) / 3) = p * n := by
    rw [lin_plane σ a b c h0 _ hk1]
    simp only [pl]
    obtain ⟨t, ht⟩ := h3
    rcases hn with rfl | rfl <;> omega
  have hk0 : k0 p (planeFrame σ a b c h0) ⟨0, by show 0 < 3; norm_num⟩ = (n * p + σ.rho) / 3 :=
    k0_eq_of _ (plane_not_dvd_den hp7 _) hk1 hkp (hlin ▸ dvd_mul_right p n)
  refine ⟨hk0, ?_⟩
  unfold m0
  rw [hk0, hlin, Nat.mul_div_cancel_left _ hp.out.pos]

theorem exists_class (hp7 : 7 ≤ p) : ∃ n, (n = 1 ∨ n = 2) ∧ 3 ∣ n * p + σ.rho := by
  have h3 : p % 3 = 1 ∨ p % 3 = 2 := by
    have h3 : ¬ 3 ∣ p := fun h => by
      rcases hp.out.eq_one_or_self_of_dvd 3 h with h | h <;> omega
    omega
  cases σ <;> simp only [Support.rho]
  · rcases h3 with h | h
    · exact ⟨1, Or.inl rfl, by omega⟩
    · exact ⟨2, Or.inr rfl, by omega⟩
  · rcases h3 with h | h
    · exact ⟨2, Or.inr rfl, by omega⟩
    · exact ⟨1, Or.inl rfl, by omega⟩

end Plane

end CatalanCore.Uniform.Bank.Plane1.Dips

#print axioms CatalanCore.Uniform.Bank.Plane1.Dips.k0_C
#print axioms CatalanCore.Uniform.Bank.Plane1.Dips.k0_B
#print axioms CatalanCore.Uniform.Bank.Plane1.Dips.k0_A
#print axioms CatalanCore.Uniform.Bank.Plane1.Dips.exists_class
