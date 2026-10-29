import CatalanCore.Uniform.Bank.Chi3Rank.Closed
set_option Elab.async false

/-! # The fibre palette of a two-pole frame (C2/PAPER.md §1, lane C2L)

For a rational digamma frame with exactly two poles, `μ = 1` (`u = q = 1`, coefficient `c0`) and
`μ = (q-o)/q` (coefficient `c1`), at a prime `p ∤ q` with singular position `k0 < p`
(`q k0 + (q - o) = p j`), the pole parts at the node `x + p d` (`x < p`) are

  `Lf = ttL c0 c1 q j z d`,  `E = ttE c0 c1 q j z d`,  `z = [k0 < x]`,

functions of the digit `d`, the bit `z` and the class `j` only (`twoPole_LfE`).  This is the
two-pole case of `Chi3Rank.LfE_node`, by the generic `lf_term`, `e_term`.  Signs and normalisation
enter only through `c0, c1`.  The degenerate digit: `ttL _ _ _ _ false 0 = ttE _ _ _ _ false 0 = 0`.
-/

namespace CatalanCore.Uniform.Content.RankProducer
open Finset CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.Hybrid
  CatalanCore.Uniform.Bank.Chi3Rank

/-- The two-pole palette `L(d, z)` of class `j`. -/
noncomputable def ttL (c0 c1 : ℚ) (q j : ℕ) (z : Bool) (d : ℕ) : ℚ :=
  (∑ m ∈ range d, c0 * ((1 : ℕ) : ℚ) / ((1 + 1 * m : ℕ) : ℚ)) +
    ∑ m ∈ range (d + if z then 1 else 0), c1 * (q : ℚ) / ((j + q * m : ℕ) : ℚ)

/-- The two-pole diagonal palette `E(d, z)` of class `j`. -/
noncomputable def ttE (c0 c1 : ℚ) (q j : ℕ) (z : Bool) (d : ℕ) : ℚ :=
  (∑ m ∈ range d, c0 * ((1 : ℕ) : ℚ) ^ 2 / ((1 + 1 * m : ℕ) : ℚ) ^ 2) +
    ∑ m ∈ range (d + if z then 1 else 0), c1 * (q : ℚ) ^ 2 / ((j + q * m : ℕ) : ℚ) ^ 2

theorem ttL_zero (c0 c1 : ℚ) (q j : ℕ) : ttL c0 c1 q j false 0 = 0 := by simp [ttL]

theorem ttE_zero (c0 c1 : ℚ) (q j : ℕ) : ttE c0 c1 q j false 0 = 0 := by simp [ttE]

/-- **Palette lemma.** -/
theorem twoPole_LfE {J : Type*} [Fintype J] [DecidableEq J] (D : DigammaFrame J) (j1 j2 : J)
    (hne : j1 ≠ j2) (hall : ∀ j, j = j1 ∨ j = j2) {q o : ℕ} (hu1 : D.u j1 = 1)
    (hq1 : D.q j1 = 1) (hq2 : D.q j2 = q) (hu2 : D.u j2 = q - o) (hq0 : 0 < q)
    (p : ℕ) [Fact p.Prime] (hpq : ¬ p ∣ q) (k0 j : ℕ) (hk0 : k0 < p)
    (hw : q * k0 + (q - o) = p * j) (x d : ℕ) (hx : x < p) :
    D.Lf p (x + p * d) = ttL (D.c j1) (D.c j2) q j (decide (k0 < x)) d ∧
      D.E p (x + p * d) = ttE (D.c j1) (D.c j2) q j (decide (k0 < x)) d := by
  have huniv : (Finset.univ : Finset J) = {j1, j2} := by
    ext j
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    exact hall j
  have hp0 := (Fact.out : p.Prime).pos
  have hp1 : ¬ p ∣ 1 := (Fact.out : p.Prime).not_dvd_one
  have hpI : p - 1 < p := by omega
  have hI : 1 * (p - 1) + 1 = p * 1 := by omega
  have hI' : ¬ (p - 1 < x) := by omega
  have pa := lf_term p (D.c j1) 1 1 (p - 1) 1 x d (by norm_num) hp1 hpI hI hx
  have pb := lf_term p (D.c j2) q (q - o) k0 j x d hq0 hpq hk0 hw hx
  have ea := e_term p (D.c j1) 1 1 (p - 1) 1 x d (by norm_num) hp1 hpI hI hx
  have eb := e_term p (D.c j2) q (q - o) k0 j x d hq0 hpq hk0 hw hx
  rw [if_neg hI', add_zero] at pa ea
  constructor
  · unfold DigammaFrame.Lf
    rw [huniv, Finset.sum_pair hne]
    simp only [DigammaFrame.den, hu1, hq1, hu2, hq2]
    rw [pa, pb]
    unfold ttL
    simp only [decide_eq_true_eq]
  · unfold DigammaFrame.E
    rw [huniv, Finset.sum_pair hne]
    simp only [DigammaFrame.den, hu1, hq1, hu2, hq2]
    rw [ea, eb]
    unfold ttE
    simp only [decide_eq_true_eq]

#print axioms twoPole_LfE
end CatalanCore.Uniform.Content.RankProducer
