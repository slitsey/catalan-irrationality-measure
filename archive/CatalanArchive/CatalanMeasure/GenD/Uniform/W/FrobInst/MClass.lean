module
public import CatalanMeasure.GenD.Uniform.W.FrobInst.MResp
@[expose] public section
set_option Elab.async false

/-!
# Window arithmetic of Theorem M: which source covectors are seen

With `H = 3p + eta` (`0 ≤ eta < p`), visible columns `j ∈ [b, L)`, `b ≥ eta`, `L ≤ 3p`,
`H = L + g + h`, and slot exponents `e < h + R0` with `h + R0 ≤ p`, `R0 ≤ g`: if
`p ∣ H - 1 - (j mod p) - e` with quotient `a`, then either

* `a = 3`, block `j/p ∈ {1,2}` and `e < eta` (the *mixed* classes `(1,4),(2,4)` in the `s = a + 1`
  convention of UNIFIED-COUNTING-THEOREM), or
* `a = 2`, block `j/p ∈ {0,1}` and `eta ≤ e` (the *C* classes `(0,3),(1,3)`).
-/

namespace CatalanMeasure.GenD.Uniform.W.FrobInst
noncomputable section

theorem class_split {p H b L g h R0 j e : ℕ} (a : ℤ) (hp : 0 < p) (h3 : 3 * p ≤ H) (h4 : H < 4 * p)
    (hb : H ≤ b + 3 * p) (hL : L ≤ 3 * p) (hHL : H = L + g + h) (hR : R0 ≤ g)
    (hhR : h + R0 ≤ p) (hj1 : b ≤ j) (hj2 : j < L) (he : e < h + R0)
    (heq : (H : ℤ) - 1 - ((j % p : ℕ) : ℤ) - e = a * p) :
    (a = 3 ∧ (j / p = 1 ∨ j / p = 2) ∧ e < H - 3 * p) ∨
      (a = 2 ∧ (j / p = 0 ∨ j / p = 1) ∧ H - 3 * p ≤ e) := by
  have hjd := Nat.div_add_mod j p
  have hlt : j % p < p := Nat.mod_lt _ hp
  have hp' : (0 : ℤ) < p := by exact_mod_cast hp
  have ha2 : 2 ≤ a := by
    by_contra hc
    have : a * p ≤ 1 * p := by nlinarith
    omega
  have ha3 : a ≤ 3 := by
    by_contra hc
    have : 4 * p ≤ a * p := by nlinarith
    omega
  have hjL : j < p * 3 := by omega
  have hJ3 : j / p < 3 := Nat.div_lt_of_lt_mul hjL
  have hac : a = 2 ∨ a = 3 := by omega
  generalize j / p = J at hjd hJ3 ⊢
  have hJ : J = 0 ∨ J = 1 ∨ J = 2 := by omega
  rcases hac with rfl | rfl
  · right
    refine ⟨rfl, ?_, by omega⟩
    rcases hJ with h0 | h0 | h0
    · left; exact h0
    · right; exact h0
    · exfalso
      rw [h0] at hjd
      omega
  · left
    refine ⟨rfl, ?_, by omega⟩
    rcases hJ with h0 | h0 | h0
    · exfalso
      rw [h0] at hjd
      omega
    · left; exact h0
    · right; exact h0

end
end CatalanMeasure.GenD.Uniform.W.FrobInst
