module

public import CatalanCore.Zeta5.Profile.All

@[expose] public section

/-!
# The outer profile `T₀` in closed form (definitions)

CONTENT-THEOREM §2 defines, for `y > 1/3`, the outer rate
`T₀(y) = −G(y) + min(r(y), Z(y)) − 2λ⌊1/y⌋ + Σ_{j=1}^5 (2λ − j y)₊` with
`G(y) = 2y ∫₀^{1/2} Σ_i w_i(z) dz`, `Z(y) = y ∫₀^{1/2} #{i : w_i(z) = 0} dz` (for `y < 1`; `G = 0`,
`Z = λ` for `y ≥ 1`) and `r(y) = min(λ, (1 + 4α − 2y)₊)`.

Here `(s, κ, α, λ) = (5, 6, 3/40, 37/40)`, so the rows of the class with `ℓ = ℓ(x, z)` and
`δ = 1_{z < αx}` have the weights `w_i = min(0, i + 3δ − (ℓ + 4)/2)` for `i < ℓ − 2`, else `0`
(`wrowQ`), and there are `ℓ − δ` rows.

In the variable `x = 1/y` the integrand in `z` takes four values (two thresholds `te = min({x}, 1−{x})`
and `ν = αx`), so `x·T₀(1/x)` has a closed form `Ex` in floors, `min`, `max` only (generic over a
floor field `K`, like `Profile.Rg`). The integral bridge `T₀(y) = y·Ex(1/y)` is in `OuterBridge`.

* `wrowQ`, `Sq`, `Nq`: the row weights, their sum and the number of zero rows (over `ℚ`).
* `lA`, `lB`: the two values of `ℓ` (`z < te`, `z > te`).
* `Iint x = ∫₀^{1/2} Σ w_i dz`, `Zint x = ∫₀^{1/2} #{w_i = 0} dz` (closed form).
* `Ex x = x T₀(1/x)`, with the guards `gtG, g1G, g2G, g3G` of the cell test.
-/

open Set

set_option linter.deprecated false

namespace CatalanCore.Zeta5.Sum

open CatalanCore.Zeta5.Profile

/-- Row weight: `w_i = min(0, i + 3δ − (ℓ+4)/2)` for `i < ℓ − 2`, else `0`. -/
def wrowQ (l d i : ℕ) : ℚ := if i + 2 < l then min 0 ((i : ℚ) + 3 * d - ((l : ℚ) + 4) / 2) else 0

/-- `Σ_{i < ℓ − δ} w_i`. -/
def Sq (l d : ℕ) : ℚ := ((List.range (l - d)).map (wrowQ l d)).sum

/-- `#{i < ℓ − δ : w_i = 0}`. -/
def Nq (l d : ℕ) : ℚ := (((List.range (l - d)).filter (fun i => decide (wrowQ l d i = 0))).length : ℚ)

section Gen

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K]

/-- `ℓ` for `z < te`: `2⌊x⌋ + 1`. -/
def lA (x : K) : ℕ := (2 * ⌊x⌋ + 1).toNat

/-- `ℓ` for `z > te`: `2⌊x⌋` if `{x} < 1/2`, else `2⌊x⌋ + 2`. -/
def lB (x : K) : ℕ := if Int.fract x < 1 / 2 then (2 * ⌊x⌋).toNat else (2 * ⌊x⌋ + 2).toNat

/-- `∫₀^{1/2} Σ_i w_i(z) dz` in the closed four-region form. -/
def Iint (x : K) : K :=
  ((Sq (lA x) 1 : ℚ) : K) * min (tri x) (al * x)
    + ((Sq (lA x) 0 : ℚ) : K) * max 0 (tri x - al * x)
    + ((Sq (lB x) 1 : ℚ) : K) * max 0 (al * x - tri x)
    + ((Sq (lB x) 0 : ℚ) : K) * (1 / 2 - max (tri x) (al * x))

/-- `∫₀^{1/2} #{i : w_i(z) = 0} dz`. -/
def Zint (x : K) : K :=
  ((Nq (lA x) 1 : ℚ) : K) * min (tri x) (al * x)
    + ((Nq (lA x) 0 : ℚ) : K) * max 0 (tri x - al * x)
    + ((Nq (lB x) 1 : ℚ) : K) * max 0 (al * x - tri x)
    + ((Nq (lB x) 0 : ℚ) : K) * (1 / 2 - max (tri x) (al * x))

/-- `x · r(1/x)`: `min(λ x, ((1 + 4α) x − 2)₊)`. -/
def rx (x : K) : K := min (lam * x) (max 0 ((1 + 4 * al) * x - 2))

/-- `x · Z(1/x)`. -/
def Zx (x : K) : K := if 1 < x then Zint x else lam * x

/-- `x · G(1/x)` is `2 · Iint x` for `x > 1` (and `0` for `x ≤ 1`). -/
def Gx (x : K) : K := if 1 < x then 2 * Iint x else 0

/-- `x · T₀(1/x)`. -/
def Ex (x : K) : K :=
  -Gx x + min (rx x) (Zx x) - 2 * lam * x * ⌊x⌋
    + max 0 (2 * lam * x - 1) + max 0 (2 * lam * x - 2) + max 0 (2 * lam * x - 3)
    + max 0 (2 * lam * x - 4) + max 0 (2 * lam * x - 5)

/-- Guard: `te − ν`. -/
def gtG (x : K) : K := tri x - al * x
/-- Guard: `(1 + 4α) x − 2`. -/
def g1G (x : K) : K := (1 + 4 * al) * x - 2
/-- Guard: `λ x − (g1)₊`. -/
def g2G (x : K) : K := lam * x - max 0 (g1G x)
/-- Guard: `x r − x Z`. -/
def g3G (x : K) : K := min (lam * x) (max 0 (g1G x)) - Zx x

end Gen

/-! ### Casts `ℚ → ℝ` -/

lemma floor_cast_q (q : ℚ) : ⌊(q : ℝ)⌋ = ⌊q⌋ := by
  rw [← Rat.floor_cast (α := ℝ)]

lemma lA_cast (q : ℚ) : lA (q : ℝ) = lA q := by
  unfold lA; rw [floor_cast_q]

lemma lt_half_cast' (y : ℚ) : y < 1 / 2 ↔ (y : ℝ) < 1 / 2 := by
  have := (Rat.cast_lt (K := ℝ) (p := y) (q := 1 / 2))
  simpa using this.symm

lemma lB_cast (q : ℚ) : lB (q : ℝ) = lB q := by
  unfold lB
  have h : Int.fract (q : ℝ) < 1 / 2 ↔ Int.fract q < 1 / 2 := by
    rw [← fract_cast]; exact (lt_half_cast' _).symm
  rw [floor_cast_q]
  by_cases hq : Int.fract q < 1 / 2
  · rw [if_pos hq, if_pos (h.2 hq)]
  · rw [if_neg hq, if_neg (fun hh => hq (h.1 hh))]

lemma al_cast' : ((al : ℚ) : ℝ) = (al : ℝ) := by unfold al; norm_num
lemma lam_cast' : ((lam : ℚ) : ℝ) = (lam : ℝ) := by unfold lam; norm_num

lemma Iint_cast (q : ℚ) : ((Iint q : ℚ) : ℝ) = Iint (q : ℝ) := by
  unfold Iint
  simp only [lA_cast, lB_cast, Rat.cast_add, Rat.cast_mul, Rat.cast_min, Rat.cast_max,
    Rat.cast_sub, Rat.cast_div, Rat.cast_one, Rat.cast_zero, Rat.cast_ofNat, tri_cast,
    al_cast', Rat.cast_mul, Rat.cast_id]

lemma Zint_cast (q : ℚ) : ((Zint q : ℚ) : ℝ) = Zint (q : ℝ) := by
  unfold Zint
  simp only [lA_cast, lB_cast, Rat.cast_add, Rat.cast_mul, Rat.cast_min, Rat.cast_max,
    Rat.cast_sub, Rat.cast_div, Rat.cast_one, Rat.cast_zero, Rat.cast_ofNat, tri_cast,
    al_cast', Rat.cast_mul, Rat.cast_id]

lemma lt_one_cast (q : ℚ) : (1 : ℝ) < q ↔ (1 : ℚ) < q := by
  exact_mod_cast Iff.rfl

lemma rx_cast (q : ℚ) : ((rx q : ℚ) : ℝ) = rx (q : ℝ) := by
  unfold rx
  simp only [Rat.cast_min, Rat.cast_max, Rat.cast_sub, Rat.cast_mul, Rat.cast_add, Rat.cast_one,
    Rat.cast_zero, Rat.cast_ofNat, al_cast', lam_cast']

lemma Zx_cast (q : ℚ) : ((Zx q : ℚ) : ℝ) = Zx (q : ℝ) := by
  unfold Zx
  by_cases h : (1 : ℚ) < q
  · rw [if_pos h, if_pos ((lt_one_cast q).2 h), Zint_cast]
  · rw [if_neg h, if_neg (fun hh => h ((lt_one_cast q).1 hh))]
    simp only [Rat.cast_mul, lam_cast']

lemma Gx_cast (q : ℚ) : ((Gx q : ℚ) : ℝ) = Gx (q : ℝ) := by
  unfold Gx
  by_cases h : (1 : ℚ) < q
  · rw [if_pos h, if_pos ((lt_one_cast q).2 h)]
    simp only [Rat.cast_mul, Rat.cast_ofNat, Iint_cast]
  · rw [if_neg h, if_neg (fun hh => h ((lt_one_cast q).1 hh))]
    simp

lemma Ex_cast (q : ℚ) : ((Ex q : ℚ) : ℝ) = Ex (q : ℝ) := by
  unfold Ex
  simp only [Rat.cast_add, Rat.cast_sub, Rat.cast_neg, Rat.cast_mul, Rat.cast_min, Rat.cast_max,
    Rat.cast_ofNat, Rat.cast_zero, Rat.cast_one, Rat.cast_intCast, Gx_cast, rx_cast, Zx_cast,
    lam_cast', floor_cast_q]

lemma gtG_cast (q : ℚ) : ((gtG q : ℚ) : ℝ) = gtG (q : ℝ) := by
  unfold gtG; simp only [Rat.cast_sub, Rat.cast_mul, tri_cast, al_cast']

lemma g1G_cast (q : ℚ) : ((g1G q : ℚ) : ℝ) = g1G (q : ℝ) := by
  unfold g1G; simp only [Rat.cast_sub, Rat.cast_mul, Rat.cast_add, Rat.cast_one, Rat.cast_ofNat,
    al_cast']

lemma g2G_cast (q : ℚ) : ((g2G q : ℚ) : ℝ) = g2G (q : ℝ) := by
  unfold g2G; simp only [Rat.cast_sub, Rat.cast_mul, Rat.cast_max, Rat.cast_zero, g1G_cast,
    lam_cast']

lemma g3G_cast (q : ℚ) : ((g3G q : ℚ) : ℝ) = g3G (q : ℝ) := by
  unfold g3G; simp only [Rat.cast_sub, Rat.cast_mul, Rat.cast_max, Rat.cast_min, Rat.cast_zero,
    g1G_cast, Zx_cast, lam_cast']

end CatalanCore.Zeta5.Sum
