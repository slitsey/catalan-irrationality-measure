module

public import CatalanFrames.Lambda.HybInst
public import CatalanCore.Arith.Hybrid.PieceTools

@[expose] public section

/-!
# λ: per-prime level-1 bounds (`m = ⌊r/8⌋`)

`lamX r p = tropVal (HW lamInst.lev p r ⌊r/8⌋)`; for an odd prime `p`, with
`kq p = (p+1)/4` (`p ≡ 3`) or `(3p+1)/4` (`p ≡ 1`), the bounds of the duals D1, D2, D3, D45, D6.
-/

open Finset CatalanCore CatalanCore.Arith CatalanCore.Arith.Hybrid

namespace CatalanFrames.Lambda

/-- The level-1 tropical value of the hybrid at `(r, ⌊r/8⌋)` and the prime `p`. -/
noncomputable def lamX (r p : ℕ) : ℕ := tropVal (HW lamInst.lev p r (r / 8))

lemma lam_kq_eq {p : ℕ} (h3 : p % 4 = 3) : lamCD.kq p = (p + 1) / 4 := by
  show kq p = _
  unfold kq jq; rw [if_pos h3]; simp

lemma lam_kq_eq1 {p : ℕ} (h1 : p % 4 = 1) : lamCD.kq p = (3 * p + 1) / 4 := by
  show kq p = _
  unfold kq jq; rw [if_neg (by omega)]

lemma lam_odd_good {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) :
    IsPrimePow p ∧ (∀ q ∈ lamCD.bad, ¬ q ∣ p) := by
  refine ⟨hp.isPrimePow, ?_⟩
  intro q hq hd
  have : q = 2 := by simpa [lamCD] using hq
  subst this
  exact h2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp hd).symm

lemma lamX_D1 (r p : ℕ) : lamX r p ≤ 2 * (r + r / 8) := by
  have h := trop_D1 (lev := lamInst.lev) p r (r / 8)
  have : (lamX r p : ℚ) ≤ ((2 * (r + r / 8) : ℕ) : ℚ) := by push_cast; exact h
  exact_mod_cast this

lemma lamX_D3 (r p : ℕ) (hp : p.Prime) (h2 : p ≠ 2) (hl : r / 4 < p) (hu : p ≤ r) :
    lamX r p ≤ 2 * r + r / 8 := by
  have := val_D3 p r (r / 8) (lev := lamInst.lev) hp.one_lt.le
    (fun c hc => lam_lev_high p c hp.one_lt.le hc) (by omega) hu
  exact this

lemma lamX_D2 (r p : ℕ) (hp : p.Prime) (h2 : p ≠ 2) (hl : r / 4 < p) (hu : p ≤ r) :
    ∃ u L : ℕ, lamCD.kq p + p ≤ u + r ∧ u ≤ r ∧ L ≤ u ∧ L ≤ 2 * (r / 8) ∧
      lamX r p ≤ 2 * (r - u) + 2 * (r / 8) + L := by
  obtain ⟨hq, hb⟩ := lam_odd_good hp h2
  have hk : lamCD.kq p ≤ r := by
    have : lamCD.kq p ≤ p := by
      show kq p ≤ p
      unfold kq jq; split_ifs <;> omega
    omega
  exact val_D2 p r (r / 8) (lamCD.kq p) (lev := lamInst.lev) hp.one_lt.le
    (fun c hc => lam_lev_high p c hp.one_lt.le hc) (by omega) hu hk
    (fun c => lam_lev_zero_iff hq hb)

lemma lamX_D45 (r p : ℕ) (hp : p.Prime) (h2 : p ≠ 2) (hr : r < p) :
    lamX r p ≤ 2 * (r - lamCD.kq p) + 2 * (r / 8) + (2 * (r / 8) - (p - r)) := by
  obtain ⟨hq, hb⟩ := lam_odd_good hp h2
  exact val_D45 p r (r / 8) (lamCD.kq p) (lev := lamInst.lev) hr (by omega)
    (fun c => lam_lev_zero_iff hq hb)

lemma lamX_D6 (r p : ℕ) (hp : p.Prime) (h2 : p ≠ 2) (hN : r + 2 * (r / 8) ≤ p)
    (hk : r ≤ lamCD.kq p) : lamX r p ≤ 2 * (r / 8) - (lamCD.kq p - r) := by
  obtain ⟨hq, hb⟩ := lam_odd_good hp h2
  exact val_D6 p r (r / 8) (lamCD.kq p) (lev := lamInst.lev) hN hk
    (fun c => lam_lev_zero_iff hq hb)

end CatalanFrames.Lambda
