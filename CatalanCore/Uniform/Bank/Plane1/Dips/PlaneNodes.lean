module

public import CatalanCore.Uniform.Bank.Plane1.Dips.PlaneLevels

@[expose] public section
set_option Elab.async false
set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.unusedVariables false
set_option linter.unusedTactic false

/-! # The level tables of the plane frames (wave R0; ledger R01-R03; package R1a)

For a plane frame with weights `(a, b, c)` and a prime `p ≥ 7` of class `n` (`3 ∣ n p + ρ`) the levels at a node `t` depend
on `t` only through the triple `(q, eA, eB) = (t / p, 1[t mod p ≥ kA], 1[t mod p ≥ kB])`, `kA = (n p + ρ)/3`,
`kB = (p + 1)/2` (the cell of `t`):

* `Vtab a b c n q eA eB = FA (q + eA) + FB (q + eB) + FC q`, `FA j = Σ_{u<j} 3a/(n + 3u)`, `FB j = Σ_{u<j} 2b/(1 + 2u)`,
  `FC j = Σ_{u<j} c/(1 + u)`;
* `Utab` likewise with the squared forms and the sign of `Up`.

`planeV_eq`, `planeU_eq` are `Vp p Fr t = Vtab ..`, `Up p Fr t = Utab ..`: the p-independent table the dip lines use. -/

namespace CatalanCore.Uniform.Bank.Plane1.Dips
open Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid CatalanCore.Uniform.Bank.Plane1

section Tables

/-- The partial sums of the residues of the atom `3k - ρ` (cofactors `n, n + 3, …`). -/
def FA (a : ℤ) (n j : ℕ) : ℚ := ∑ u ∈ range j, (3 * (a : ℚ)) / ((n + 3 * u : ℕ) : ℚ)
/-- The partial sums of the residues of the atom `2k - 1` (cofactors `1, 3, …`). -/
def FB (b : ℤ) (j : ℕ) : ℚ := ∑ u ∈ range j, (2 * (b : ℚ)) / ((1 + 2 * u : ℕ) : ℚ)
/-- The partial sums of the residues of the atom `k` (cofactors `1, 2, …`). -/
def FC (c : ℤ) (j : ℕ) : ℚ := ∑ u ∈ range j, (c : ℚ) / ((1 + u : ℕ) : ℚ)

def GA (a : ℤ) (n j : ℕ) : ℚ := ∑ u ∈ range j, (9 * (a : ℚ)) / ((n + 3 * u : ℕ) : ℚ) ^ 2
def GB (b : ℤ) (j : ℕ) : ℚ := ∑ u ∈ range j, (4 * (b : ℚ)) / ((1 + 2 * u : ℕ) : ℚ) ^ 2
def GC (c : ℤ) (j : ℕ) : ℚ := ∑ u ∈ range j, (c : ℚ) / ((1 + u : ℕ) : ℚ) ^ 2

/-- The level at the cell `(q, eA, eB)`. -/
def Vtab (a b c : ℤ) (n q : ℕ) (eA eB : Bool) : ℚ :=
  FA a n (q + if eA then 1 else 0) + FB b (q + if eB then 1 else 0) + FC c q

/-- The diagonal level at the cell `(q, eA, eB)`. -/
def Utab (a b c : ℤ) (n q : ℕ) (eA eB : Bool) : ℚ :=
  -(GA a n (q + if eA then 1 else 0) + GB b (q + if eB then 1 else 0) + GC c q)

end Tables

section Nodes

variable (σ : Support) (a b c : ℤ) (h0 : a + b + c = 0) {p : ℕ} [hp : Fact p.Prime]

theorem plane_w0 : (planeFrame σ a b c h0).w ⟨0, by show 0 < 3; norm_num⟩ = a := rfl
theorem plane_w1 : (planeFrame σ a b c h0).w ⟨1, by show 1 < 3; norm_num⟩ = b := rfl
theorem plane_w2 : (planeFrame σ a b c h0).w ⟨2, by show 2 < 3; norm_num⟩ = c := rfl
theorem plane_d0 : ((planeFrame σ a b c h0).μ ⟨0, by show 0 < 3; norm_num⟩).den = 3 := shift_den σ
theorem plane_d1 : ((planeFrame σ a b c h0).μ ⟨1, by show 1 < 3; norm_num⟩).den = 2 := half_den
theorem plane_d2 : ((planeFrame σ a b c h0).μ ⟨2, by show 2 < 3; norm_num⟩).den = 1 := one_den

variable {σ a b c h0}

/-- **The level of a node, from the table.** -/
theorem planeV_eq (hp7 : 7 ≤ p) {n : ℕ} (hn : n = 1 ∨ n = 2) (h3 : 3 ∣ n * p + σ.rho) (t : ℕ) :
    Vp p (planeFrame σ a b c h0) t =
      Vtab a b c n (t / p) (decide ((n * p + σ.rho) / 3 ≤ t % p)) (decide ((p + 1) / 2 ≤ t % p)) := by
  have hsum : ∀ f : Fin (planeFrame σ a b c h0).d → ℚ, ∑ i, f i =
      f ⟨0, by show 0 < 3; norm_num⟩ + f ⟨1, by show 1 < 3; norm_num⟩ + f ⟨2, by show 2 < 3; norm_num⟩ :=
    fun f => Fin.sum_univ_three f
  rw [Vp_closed (plane_den_le σ a b c h0) (by omega), hsum]
  obtain ⟨hkA, hmA⟩ := k0_A hp7 hn h3
  have hd0 := plane_d0 σ a b c h0
  have hd1 := plane_d1 σ a b c h0
  have hd2 := plane_d2 σ a b c h0
  unfold Vtab FA FB FC
  rw [Ucnt_eq, Ucnt_eq, Ucnt_eq, hkA, k0_B hp7, k0_C hp7, hmA, m0_B hp7, m0_C hp7]
  have e2 : ¬ (p ≤ t % p) := by have := Nat.mod_lt t hp.out.pos; omega
  simp only [e2, if_false, add_zero]
  simp only [Fin.mk_zero, plane_w0, plane_w1, plane_w2, hd0, hd1, hd2]
  congr 1
  · congr 1
    · refine Finset.sum_congr (by simp [decide_eq_true_eq]) fun u _ => ?_
      push_cast; ring
    · refine Finset.sum_congr (by simp [decide_eq_true_eq]) fun u _ => ?_
      push_cast; ring
  · refine Finset.sum_congr rfl fun u _ => ?_
    push_cast; ring

/-- **The diagonal level of a node, from the table.** -/
theorem planeU_eq (hp7 : 7 ≤ p) {n : ℕ} (hn : n = 1 ∨ n = 2) (h3 : 3 ∣ n * p + σ.rho) (t : ℕ) :
    Up p (planeFrame σ a b c h0) t =
      Utab a b c n (t / p) (decide ((n * p + σ.rho) / 3 ≤ t % p)) (decide ((p + 1) / 2 ≤ t % p)) := by
  have hsum : ∀ f : Fin (planeFrame σ a b c h0).d → ℚ, ∑ i, f i =
      f ⟨0, by show 0 < 3; norm_num⟩ + f ⟨1, by show 1 < 3; norm_num⟩ + f ⟨2, by show 2 < 3; norm_num⟩ :=
    fun f => Fin.sum_univ_three f
  rw [Up_closed (plane_den_le σ a b c h0) (by omega), hsum]
  obtain ⟨hkA, hmA⟩ := k0_A hp7 hn h3
  have hd0 := plane_d0 σ a b c h0
  have hd1 := plane_d1 σ a b c h0
  have hd2 := plane_d2 σ a b c h0
  unfold Utab GA GB GC
  rw [Ucnt_eq, Ucnt_eq, Ucnt_eq, hkA, k0_B hp7, k0_C hp7, hmA, m0_B hp7, m0_C hp7]
  have e2 : ¬ (p ≤ t % p) := by have := Nat.mod_lt t hp.out.pos; omega
  simp only [e2, if_false, add_zero]
  simp only [plane_w0, plane_w1, plane_w2, hd0, hd1, hd2]
  congr 2
  · congr 1
    · refine Finset.sum_congr (by simp [decide_eq_true_eq]) fun u _ => ?_
      push_cast; ring
    · refine Finset.sum_congr (by simp [decide_eq_true_eq]) fun u _ => ?_
      push_cast; ring
  · refine Finset.sum_congr rfl fun u _ => ?_
    push_cast; ring

end Nodes

#print axioms CatalanCore.Uniform.Bank.Plane1.Dips.planeV_eq
#print axioms CatalanCore.Uniform.Bank.Plane1.Dips.planeU_eq

end CatalanCore.Uniform.Bank.Plane1.Dips
