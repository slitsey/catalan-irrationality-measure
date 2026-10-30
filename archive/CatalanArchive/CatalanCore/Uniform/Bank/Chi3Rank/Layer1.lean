import CatalanCore.Uniform.Bank.Chi3Rank.Real1
set_option Elab.async false

/-! # The class `p ≡ 1 (mod 6)` rank member (lane H, H16)

For `r = 4 m`, `r ≤ 2 p < 2 r`, the member `commonMinor r m s` has rank price at most
`2 r + 2 m + 1 - (min p (6m - p) - max (r - p) ((p+1)/2))`, for every retained set `s`. -/

namespace CatalanCore.Uniform.Bank.Chi3Rank
open Polynomial Finset Module Matrix CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Uniform.Content.Hybrid CatalanCore.Uniform.Content.Member
  CatalanCore.Uniform.Content.RankProducer CatalanFrames.P6

theorem cast_ne_zero_of (p : ℕ) [hp : Fact p.Prime] (q : ℚ) (hnum : ¬ (p : ℤ) ∣ q.num)
    (hden : ¬ p ∣ q.den) : (q : ZMod p) ≠ 0 := by
  rw [Rat.cast_def]
  have h1 : (q.num : ZMod p) ≠ 0 := by rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have h2 : (q.den : ZMod p) ≠ 0 := by rwa [Ne, ZMod.natCast_eq_zero_iff]
  exact div_ne_zero h1 h2

theorem castV_ne_zero_snd (p : ℕ) [hp : Fact p.Prime] (v : ℚ × ℚ) (h : (v.2 : ZMod p) ≠ 0) :
    castV p v ≠ 0 := by
  intro h0
  apply h
  have := congrArg Prod.snd h0
  exact rfH_injective (this.trans (map_zero _).symm)

theorem nz1 (p : ℕ) [hp : Fact p.Prime] (hN : N0 < p) : castV p (O1.cload 0) ≠ 0 := by
  rw [load1_val]
  refine castV_ne_zero_snd p _ (cast_ne_zero_of p _ ?_ ?_)
  · have : (1 / 72 : ℚ).num = 1 := by decide +kernel
    show ¬ (p : ℤ) ∣ (1 / 72 : ℚ).num
    rw [this]; exact_mod_cast hp.out.not_dvd_one
  · have : (1 / 72 : ℚ).den = 72 := by decide +kernel
    show ¬ p ∣ (1 / 72 : ℚ).den
    rw [this]; intro h
    have := Nat.le_of_dvd (by norm_num) h
    unfold N0 at hN; omega

theorem rank_c1 (r m p : ℕ) [hp : Fact p.Prime] (hr : r = 4 * m) (h6 : p % 6 = 1)
    (hN : N0 < p) (hrp : r ≤ 2 * p) (hpr : p < r) (s : Finset (Fin r)) :
    ∃ M : RankMember p6Frame u3 q3 (fun c : Fin r => (c : ℕ))
        (fun j : Fin m => r + 2 * (j : ℕ)) (fun j : Fin m => r + 2 * (j : ℕ) + 1) s p,
      M.price + (min p (6 * m - p) - max (r - p) ((p + 1) / 2)) ≤ 2 * r + 2 * m + 1 := by
  have hpodd : p % 2 = 1 := by omega
  have hbig : 3 * (r + 2 * m) + 1 ≤ p ^ 2 := by
    have h1 : 9 * p + 1 ≤ p ^ 2 := by unfold N0 at hN; nlinarith
    omega
  refine assemble r m p s E1 O1 (max (r - p) ((p + 1) / 2)) (min p (6 * m - p)) 1
    (keptN r s) (by norm_num) (Or.inl h6) hN hbig (min_le_left _ _) ?_ E1_ok O1_ok E1_den O1_den
    rfl rfl rfl rfl ?_ ?_ load1 (nz1 p hN)
  · intro x hlo hhi hnp
    exact ⟨x, by omega, hnp, Nat.mod_eq_of_lt (by omega)⟩
  · intro x0 hlo hhi hpar hk PS hL hE
    have hx0 : x0 < p := by omega
    obtain ⟨hl0, hl1, he0, he1⟩ := lfE_c1 p h6 x0 (by omega) hx0
    exact real_E1 PS r m s x0 hr hrp hx0 (by omega) (by omega) hpar hpodd hk
      (by rw [hL]; exact hl0) (by rw [hL]; exact hl1) (by rw [hE]; exact he0)
      (by rw [hE]; exact he1)
  · intro x0 hlo hhi hpar hk PS hL hE
    have hx0 : x0 < p := by omega
    obtain ⟨hl0, hl1, he0, he1⟩ := lfE_c1 p h6 x0 (by omega) hx0
    exact real_O1 PS r m s x0 hr hrp hx0 (by omega) (by omega) (by omega) hpodd hk
      (by rw [hL]; exact hl0) (by rw [hL]; exact hl1) (by rw [hE]; exact he0)

end CatalanCore.Uniform.Bank.Chi3Rank
