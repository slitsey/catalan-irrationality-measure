module

public import Mathlib.Tactic

@[expose] public section

/-!
# ZC19, integer part: `γ_p^ext` against the closed `p Γ(K/p)`

`extGamZ` is the closed class-count formula of the ordinary-class sum of `γ_p^ext` (`ExtSum`),
`GZ2 = 2 p Γ(K/p)` is the four-region closed form of the paper's `Γ` at `x = K/p`
(`Γ = ∫ (T-b)(T+b-ℓ-5) dz + u (2T-q-5) + (u-v)₊` with `T = ⌊92n/p⌋`, `q = ⌊80n/p⌋`).
`ext_int_close` : `-2 ≤ 2 extGamZ - GZ2 ≤ 38` for the parameters of `ExtHyp`.
-/

namespace CatalanCore.Zeta5.CostOut

/-- The class weight `(T - 3β)(T + 3β - 2q - α - 5)`. -/
def hwt (T q a b : ℤ) : ℤ := (T - 3 * b) * (T + 3 * b - 2 * q - a - 5)

/-- `2 p Γ(K/p)`: the four regions, then `u(2T - q' - 5)` and `(u - v)₊`, all times `2p`. -/
def GZ2 (n p v T0 q q2 : ℤ) : ℤ :=
  p * hwt T0 q 1 1
    + (p - 2 * min v (p - v)) * ((if 2 * v < p then hwt T0 q 0 1 else hwt T0 q 2 1) - hwt T0 q 1 1)
    + (p - 2 * (3 * n)) * (hwt T0 q 1 0 - hwt T0 q 1 1)
    + (p - 2 * max (min v (p - v)) (3 * n)) *
        ((if 2 * v < p then hwt T0 q 0 0 else hwt T0 q 2 0)
          - (if 2 * v < p then hwt T0 q 0 1 else hwt T0 q 2 1) - hwt T0 q 1 0 + hwt T0 q 1 1)
    + (92 * n - p * T0) * (2 * T0 - q2 - 5) + max 0 (12 * n + p * (q2 - T0))

/-- The closed ordinary-class sum. -/
def extGamZ (m N E nH nNH T q lo : ℤ) : ℤ :=
  m * (T * (T - 2 * q - lo - 5))
    + N * ((T - 3) * (T + 3 - 2 * q - lo - 5) - T * (T - 2 * q - lo - 5))
    + nH * (T * (T - 2 * q - lo - 6) - T * (T - 2 * q - lo - 5))
    + nNH * ((T - 3) * (T + 3 - 2 * q - lo - 6) - (T - 3) * (T + 3 - 2 * q - lo - 5)
      - T * (T - 2 * q - lo - 6) + T * (T - 2 * q - lo - 5))
    + E * (2 * T - 2 * q - lo - 4) - min E nH

set_option maxHeartbeats 8000000 in
lemma ext_int_close {n p v E m T T0 q q2 r0 r2 : ℕ}
    (hm : p = 2 * m + 1) (hp : 101 ≤ p) (hpK : p ≤ 40 * n) (hout : 40 * n < 3 * p)
    (hq : p * q + v = 40 * n) (hv : v < p) (hq12 : q = 1 ∨ q = 2)
    (hT : m * T + E = 46 * n - 8) (hE : E < m) (hT2 : 2 ≤ T) (hT6 : T ≤ 6)
    (hT0 : p * T0 + r0 = 92 * n) (hr0 : r0 < p) (hT0b : 2 ≤ T0 ∧ T0 ≤ 6)
    (hQ2 : p * q2 + r2 = 80 * n) (hr2 : r2 < p) (hQ2b : 2 ≤ q2 ∧ q2 ≤ 5) :
    ∀ nH nNH lo : ℕ,
      (lo = if v ≤ m then 0 else 1) →
      (nH = if v ≤ m then min v m else m + 1 - (p - v)) →
      (nNH = if v ≤ m then min (min (3 * n) v) m else min (3 * n) m + 1 - (p - v)) →
      -2 ≤ 2 * extGamZ m (3 * n) E nH nNH T q lo - GZ2 n p v T0 q q2 ∧
        2 * extGamZ m (3 * n) E nH nNH T q lo - GZ2 n p v T0 q q2 ≤ 38 := by
  intro nH nNH lo hlo hnH hnNH
  have hn3 : 3 * n ≤ m := by omega
  have h2N : 2 * (3 * n) < p := by omega
  unfold extGamZ GZ2 hwt
  rcases hq12 with rfl | rfl <;> rcases (by omega : T = 2 ∨ T = 3 ∨ T = 4 ∨ T = 5 ∨ T = 6) with
    rfl | rfl | rfl | rfl | rfl <;>
  rcases (by omega : T0 = 2 ∨ T0 = 3 ∨ T0 = 4 ∨ T0 = 5 ∨ T0 = 6) with
    rfl | rfl | rfl | rfl | rfl <;>
  rcases (by omega : q2 = 2 ∨ q2 = 3 ∨ q2 = 4 ∨ q2 = 5) with rfl | rfl | rfl | rfl <;>
  (try omega) <;>
  (by_cases hvm : v ≤ m <;> by_cases hvh : 2 * v < p <;>
    (have hvhZ : (2 * (v : ℤ) < (p : ℤ)) ↔ (2 * v < p) := by
        constructor <;> intro h <;> omega) <;>
    simp only [hvm, hvh, ite_true, ite_false, hvhZ] at hlo hnH hnNH ⊢ <;> subst hlo <;> subst hnH <;>
    subst hnNH <;> push_cast <;> omega)

end CatalanCore.Zeta5.CostOut
