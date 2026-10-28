module
public import CatalanMeasure.GenD.Uniform.W.HYPlus.HyLB
@[expose] public section
set_option Elab.async false

/-!
# Regression: `hyVal` against the Python count `under3/hy.py: N_HY` at D58 points

D58 = (58, 9, 3, 5, 3) N.  Python `Dsel = D`, Lean `Dn = D + 1`.
-/

open CatalanMeasure.GenD.Uniform.W.HYPlus CatalanMeasure.Parametric

def D58 : Parameters := ⟨58, 9, 3, 5, 3⟩

instance (P : Parameters) (N p s Dn : ℕ) : Decidable (HYNum P N p s Dn) := by
  unfold HYNum; infer_instance

theorem hyTermG_of {P : Parameters} {N p s K Z Dn : ℕ} (hp : p.Prime) (hf : Fact p.Prime)
    (hc : p ≠ 2 ∧ HYNum P N p s Dn ∧ s + 4 ≤ P.H N ∧ ¬ p ∣ Z) :
    hyTermG P N p s K Z Dn = hyVal P N p s K Dn (-1) := by
  classical
  unfold hyTermG
  rw [dif_pos hp]
  simp only [if_pos hc]
instance : Fact (Nat.Prime 211) := ⟨by decide +kernel⟩
instance : Fact (Nat.Prime 277) := ⟨by decide +kernel⟩
instance : Fact (Nat.Prime 229) := ⟨by decide +kernel⟩
instance : Fact (Nat.Prime 191) := ⟨by decide +kernel⟩
instance : Fact (Nat.Prime 239) := ⟨by decide +kernel⟩
instance : Fact (Nat.Prime 197) := ⟨by decide +kernel⟩

-- s = 10 (the M region, window s-1 present): N = 30 p = 211: Python 21
example : HYNum D58 30 211 10 45 := by decide +kernel
example : hyVal D58 30 211 10 9 45 (-1) = 21 := by decide +kernel
example : hyVal D58 27 191 10 9 40 (-1) = 9 := by decide +kernel
example : hyVal D58 34 239 10 9 51 (-1) = 25 := by decide +kernel
example : hyVal D58 28 197 10 9 42 (-1) = 19 := by decide +kernel
-- s = 9
example : HYNum D58 36 277 9 69 := by decide +kernel
example : hyVal D58 36 277 9 8 69 (-1) = 23 := by decide +kernel
example : hyVal D58 30 229 9 8 75 (-1) = 14 := by decide +kernel
-- the window value with the Lemma B coprimality
example : hyTermG D58 30 211 10 9 ZHY10 45 = 21 := by
  rw [hyTermG_of (Fact.out : Nat.Prime 211) inferInstance (by decide +kernel)]
  decide +kernel
example : hyTermG D58 36 277 9 8 ZHY9 69 = 23 := by
  rw [hyTermG_of (Fact.out : Nat.Prime 277) inferInstance (by decide +kernel)]
  decide +kernel
