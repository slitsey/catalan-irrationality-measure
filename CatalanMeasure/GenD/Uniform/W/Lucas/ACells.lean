module
public import CatalanMeasure.GenD.Uniform.W.Lucas.ALB
public import CatalanMeasure.GenD.Uniform.W.LStar.Cells
public import CatalanMeasure.GenD.D58.OddProfile
@[expose] public section
set_option Elab.async false

/-!
# Theorem A window cells at the D58 design (ledger-ready)

The single cell `cellA` (`S = 35`, digits `[4, 31]`, blocks `-2 … 24`) gives, with explicit position
intervals `[lo, hi)` affine in `N`, `p`, three linear pieces of `kap` on `x = p/N`:

* `-67 + 31 x`   on `(67/31, 13/6]`   (`lo = 78N - 36p`, `hi = 8N - 3p`),
* `11 - 5 x`     on `(13/6, 24/11]`   (`lo = 0`,        `hi = 8N - 3p`),
* `-1/N + 59 - 27 x` on `(24/11, 59/27]` (`lo = 0`,      `hi = 56N - 1 - 25p`).

Each lemma: for `N ≥ cellA.modulus` and `p` prime in the window, the stated linear form is `≤ kap`.
Total area `0.002552` (own/N²).
-/

namespace CatalanMeasure.GenD.Uniform.W.Lucas
open CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W.LStar
noncomputable section

local notation "des" => D58.Odd.design

set_option hygiene false in
macro "acond_data" : tactic => `(tactic| (
  unfold aCond
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · (try simp only [cellA, hH, hL, hn, hb, hq, hg, hh]); ((try norm_num) <;> omega)
  · (try simp only [cellA, hH, hL, hn, hb, hq, hg, hh]); ((try norm_num) <;> omega)
  · (try simp only [cellA, hH, hL, hn, hb, hq, hg, hh]); ((try norm_num) <;> omega)
  · (try simp only [cellA, hH, hL, hn, hb, hq, hg, hh]); ((try norm_num) <;> omega)
  · (try simp only [cellA, hH, hL, hn, hb, hq, hg, hh]); ((try norm_num) <;> omega)
  · (try simp only [cellA, hH, hL, hn, hb, hq, hg, hh]); ((try norm_num) <;> omega)
  · (try simp only [cellA, hH, hL, hn, hb, hq, hg, hh]); ((try norm_num) <;> omega)
  · (try simp only [cellA, hH, hL, hn, hb, hq, hg, hh]); ((try norm_num) <;> omega)
  · (try simp only [cellA, hH, hL, hn, hb, hq, hg, hh]); ((try norm_num) <;> omega)
  · intro e l1 l2
    simp only [cellA, hH, hL, hn, hb, hq, hg, hh]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> (try norm_num) <;> omega))

/-- `K = -67 + 31 x` on `(67/31, 13/6]`. -/
theorem a1_cell {N p : ℕ} (hp : p.Prime) (h1 : 67 * N < 31 * p) (h2 : 6 * p ≤ 13 * N)
    (hN : cellA.modulus ≤ N) :
    (-67 : ℤ) * N + 31 * p ≤ ((aCellLB cellA cellA_affine des D58.Odd.design_admissible).kap N p : ℕ) := by
  obtain ⟨hH, hL, hn, hb, hq, hg, hh⟩ := design_facts N
  have hm := cellA.modulus_pos yA_ne
  have hcop := cellA.coprime_of_gt yA_ne hp (by omega)
  have key := aCellLB_kap_ge cellA cellA_affine des D58.Odd.design_admissible
    (lo := 78 * N - 36 * p) (hi := 8 * N - 3 * p) hcop (by rw [hq]; omega) (by acond_data)
  omega

/-- `K = 11 - 5 x` on `(13/6, 24/11]`. -/
theorem a2_cell {N p : ℕ} (hp : p.Prime) (h1 : 13 * N < 6 * p) (h2 : 11 * p ≤ 24 * N)
    (hN : cellA.modulus ≤ N) :
    (11 : ℤ) * N + (-5) * p ≤ ((aCellLB cellA cellA_affine des D58.Odd.design_admissible).kap N p : ℕ) := by
  obtain ⟨hH, hL, hn, hb, hq, hg, hh⟩ := design_facts N
  have hm := cellA.modulus_pos yA_ne
  have hne : 11 * p ≠ 24 * N := by
    intro h
    have h2 : 2 ∣ 11 * p := ⟨12 * N, by omega⟩
    have h3 : 2 ∣ p := ((Nat.Prime.dvd_mul Nat.prime_two).mp h2).resolve_left (by norm_num)
    have h4 : p = 2 := ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h3).symm
    omega
  have hcop := cellA.coprime_of_gt yA_ne hp (by omega)
  have key := aCellLB_kap_ge cellA cellA_affine des D58.Odd.design_admissible
    (lo := 0) (hi := 8 * N - 3 * p) hcop (by rw [hq]; omega) (by acond_data)
  omega

/-- `K = 59 - 27 x - 1/N` on `(24/11, 59/27]`. -/
theorem a3_cell {N p : ℕ} (hp : p.Prime) (h1 : 24 * N < 11 * p) (h2 : 27 * p ≤ 59 * N)
    (hN : cellA.modulus ≤ N) :
    (59 : ℤ) * N + (-27) * p - 1 ≤ ((aCellLB cellA cellA_affine des D58.Odd.design_admissible).kap N p : ℕ) := by
  obtain ⟨hH, hL, hn, hb, hq, hg, hh⟩ := design_facts N
  have hm := cellA.modulus_pos yA_ne
  have hcop := cellA.coprime_of_gt yA_ne hp (by omega)
  have key := aCellLB_kap_ge cellA cellA_affine des D58.Odd.design_admissible
    (lo := 0) (hi := 56 * N - 1 - 25 * p) hcop (by rw [hq]; omega) (by acond_data)
  omega

end
end CatalanMeasure.GenD.Uniform.W.Lucas
