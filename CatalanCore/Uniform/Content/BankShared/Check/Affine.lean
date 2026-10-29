import CatalanCore.Uniform.Content.BankShared.Check.Expr
set_option Elab.async false

/-! # The line of a homogenised profile on an interval (lane C1L; C1/PAPER.md §9)

`affineOn α κ u v e` returns the line `(c0, c1)` of the profile `prof α κ θ e` on the half-open interval
`(u, v]`, when every `min`, `max` and truncated-subtraction node compares its two arguments consistently at
`u` and at `v`, every `δ` node has a fixed nearest lattice point and sign, and `⌊1/θ⌋` is constant on `(u, v]`.
`affineOn_sound`: the profile equals the returned line on `(u, v]` (`0 < u`).  The interval is half-open on
the left because `θ ⌊1/θ⌋` is left-continuous; every other node is continuous. -/

namespace CatalanCore.Uniform.Content.BankShared.Check

/-- The value of the line `l` at `x`. -/
def lval (l : ℚ × ℚ) (x : ℚ) : ℚ := l.1 + l.2 * x

/-- The line of the profile on `(u, v]`, when the comparisons are consistent. -/
def affineOn (α κ u v : ℚ) : Expr → Option (ℚ × ℚ)
  | .vr => some (1, 0)
  | .vp => some (0, 1)
  | .vm => some (α, 0)
  | .vk => some (0, κ)
  | .cst _ => some (0, 0)
  | .add a b =>
    match affineOn α κ u v a, affineOn α κ u v b with
    | some la, some lb => some (la.1 + lb.1, la.2 + lb.2)
    | _, _ => none
  | .smul c a =>
    match affineOn α κ u v a with
    | some la => some (c * la.1, c * la.2)
    | none => none
  | .tsub a b =>
    match affineOn α κ u v a, affineOn α κ u v b with
    | some la, some lb =>
      if 0 ≤ lval (la.1 - lb.1, la.2 - lb.2) u ∧ 0 ≤ lval (la.1 - lb.1, la.2 - lb.2) v then
        some (la.1 - lb.1, la.2 - lb.2)
      else if lval (la.1 - lb.1, la.2 - lb.2) u ≤ 0 ∧ lval (la.1 - lb.1, la.2 - lb.2) v ≤ 0 then
        some (0, 0)
      else none
    | _, _ => none
  | .mn a b =>
    match affineOn α κ u v a, affineOn α κ u v b with
    | some la, some lb =>
      if lval (la.1 - lb.1, la.2 - lb.2) u ≤ 0 ∧ lval (la.1 - lb.1, la.2 - lb.2) v ≤ 0 then some la
      else if 0 ≤ lval (la.1 - lb.1, la.2 - lb.2) u ∧ 0 ≤ lval (la.1 - lb.1, la.2 - lb.2) v then
        some lb
      else none
    | _, _ => none
  | .mx a b =>
    match affineOn α κ u v a, affineOn α κ u v b with
    | some la, some lb =>
      if 0 ≤ lval (la.1 - lb.1, la.2 - lb.2) u ∧ 0 ≤ lval (la.1 - lb.1, la.2 - lb.2) v then some la
      else if lval (la.1 - lb.1, la.2 - lb.2) u ≤ 0 ∧ lval (la.1 - lb.1, la.2 - lb.2) v ≤ 0 then
        some lb
      else none
    | _, _ => none
  | .dist a =>
    match affineOn α κ u v a with
    | some la =>
      let n : ℤ := Rat.floor (lval la ((u + v) / 2) / ((u + v) / 2) + 1 / 2)
      if 2 * lval (la.1, la.2 - n) u ≤ u ∧ -u ≤ 2 * lval (la.1, la.2 - n) u ∧
          2 * lval (la.1, la.2 - n) v ≤ v ∧ -v ≤ 2 * lval (la.1, la.2 - n) v then
        if 0 ≤ lval (la.1, la.2 - n) u ∧ 0 ≤ lval (la.1, la.2 - n) v then some (la.1, la.2 - n)
        else if lval (la.1, la.2 - n) u ≤ 0 ∧ lval (la.1, la.2 - n) v ≤ 0 then
          some (-la.1, -(la.2 - n))
        else none
      else none
    | none => none
  | .ap =>
    if 1 ≤ (((Rat.floor (1 / v)).toNat : ℚ) + 1) * u then some (0, ((Rat.floor (1 / v)).toNat : ℚ))
    else none
  | .sp =>
    if 1 ≤ (((Rat.floor (1 / v)).toNat : ℚ) + 1) * u then some (1, -((Rat.floor (1 / v)).toNat : ℚ))
    else none

/-! ### Soundness -/

/-- An affine function nonnegative at both ends of an interval is nonnegative on it. -/
theorem affine_nonneg {c0 c1 u v x : ℝ} (hux : u ≤ x) (hxv : x ≤ v) (hu : 0 ≤ c0 + c1 * u)
    (hv : 0 ≤ c0 + c1 * v) : 0 ≤ c0 + c1 * x := by
  rcases le_total 0 c1 with h | h
  · nlinarith
  · nlinarith

/-- The sign tests of `affineOn`, transported to the reals on `[u, v]`. -/
theorem lval_nonneg {d : ℚ × ℚ} {u v : ℚ} {θ : ℝ} (h1 : (u : ℝ) ≤ θ) (h2 : θ ≤ v)
    (hu : 0 ≤ lval d u) (hv : 0 ≤ lval d v) : 0 ≤ (d.1 : ℝ) + d.2 * θ := by
  have hu' : (0 : ℝ) ≤ (d.1 : ℝ) + d.2 * u := by
    have := (Rat.cast_le (K := ℝ)).2 hu; unfold lval at this; push_cast at this; exact this
  have hv' : (0 : ℝ) ≤ (d.1 : ℝ) + d.2 * v := by
    have := (Rat.cast_le (K := ℝ)).2 hv; unfold lval at this; push_cast at this; exact this
  exact affine_nonneg h1 h2 hu' hv'

theorem lval_nonpos {d : ℚ × ℚ} {u v : ℚ} {θ : ℝ} (h1 : (u : ℝ) ≤ θ) (h2 : θ ≤ v)
    (hu : lval d u ≤ 0) (hv : lval d v ≤ 0) : (d.1 : ℝ) + d.2 * θ ≤ 0 := by
  have := lval_nonneg (d := (-d.1, -d.2)) h1 h2 (by unfold lval at hu ⊢; simp only; linarith)
    (by unfold lval at hv ⊢; simp only; linarith)
  push_cast at this
  linarith

theorem prof_add (α κ : ℚ) (θ : ℝ) (a b : Expr) :
    prof α κ θ (.add a b) = prof α κ θ a + prof α κ θ b := rfl
theorem prof_smul (α κ : ℚ) (θ : ℝ) (c : ℕ) (a : Expr) :
    prof α κ θ (.smul c a) = c * prof α κ θ a := rfl
theorem prof_tsub (α κ : ℚ) (θ : ℝ) (a b : Expr) :
    prof α κ θ (.tsub a b) = max (prof α κ θ a - prof α κ θ b) 0 := rfl
theorem prof_mn (α κ : ℚ) (θ : ℝ) (a b : Expr) :
    prof α κ θ (.mn a b) = min (prof α κ θ a) (prof α κ θ b) := rfl
theorem prof_mx (α κ : ℚ) (θ : ℝ) (a b : Expr) :
    prof α κ θ (.mx a b) = max (prof α κ θ a) (prof α κ θ b) := rfl
theorem prof_dist (α κ : ℚ) (θ : ℝ) (a : Expr) :
    prof α κ θ (.dist a) = θ * latDist (prof α κ θ a / θ) := rfl
theorem prof_ap (α κ : ℚ) (θ : ℝ) : prof α κ θ .ap = θ * (⌊1 / θ⌋₊ : ℝ) := rfl
theorem prof_sp (α κ : ℚ) (θ : ℝ) : prof α κ θ .sp = 1 - θ * (⌊1 / θ⌋₊ : ℝ) := rfl

/-- `⌊1/θ⌋ = n` on `(u, v]` under the test of `affineOn`. -/
theorem floor_inv_eq {u v : ℚ} {θ : ℝ} (hu : 0 < u) (h1 : (u : ℝ) < θ) (h2 : θ ≤ v)
    (h : 1 ≤ (((Rat.floor (1 / v)).toNat : ℚ) + 1) * u) :
    ⌊1 / θ⌋₊ = (Rat.floor (1 / v)).toNat := by
  set n := (Rat.floor (1 / v)).toNat with hn
  have hu' : (0 : ℝ) < u := by exact_mod_cast hu
  have hθ : 0 < θ := lt_trans hu' h1
  have hv : (0 : ℚ) < v := by
    have : (u : ℝ) < v := lt_of_lt_of_le h1 h2
    exact lt_trans hu (by exact_mod_cast this)
  have hnq : (n : ℚ) ≤ 1 / v := by
    rcases le_or_gt 0 (Rat.floor (1 / v)) with h0 | h0
    · have e : ((n : ℤ)) = Rat.floor (1 / v) := by rw [hn]; exact Int.toNat_of_nonneg h0
      have e' : (n : ℚ) = ((Rat.floor (1 / v) : ℤ) : ℚ) := by rw [← e]; exact (Int.cast_natCast n).symm
      rw [e']; exact Rat.floor_le (1 / v)
    · have : n = 0 := by rw [hn]; exact Int.toNat_eq_zero.2 h0.le
      rw [this, Nat.cast_zero]; exact div_nonneg zero_le_one hv.le
  rw [Nat.floor_eq_iff (div_nonneg zero_le_one hθ.le)]
  constructor
  · have h3 : (n : ℝ) ≤ 1 / (v : ℝ) := by
      have := (Rat.cast_le (K := ℝ)).2 hnq; push_cast at this; exact this
    exact h3.trans (one_div_le_one_div_of_le hθ h2)
  · have h3 : (1 : ℝ) ≤ ((n : ℝ) + 1) * u := by
      have := (Rat.cast_le (K := ℝ)).2 h; push_cast at this; exact this
    have h4 : 1 / θ < 1 / (u : ℝ) := one_div_lt_one_div_of_lt hu' h1
    have h5 : 1 / (u : ℝ) ≤ (n : ℝ) + 1 := by
      rw [div_le_iff₀ hu']; linarith
    linarith

/-- `2 |c0 + c1 θ| ≤ θ` on `[u, v]` from the four endpoint tests of the `δ` node. -/
theorem two_abs_le {c0 c1 u v θ : ℝ} (hu : u ≤ θ) (hv : θ ≤ v) (h1 : 2 * (c0 + c1 * u) ≤ u)
    (h2 : -u ≤ 2 * (c0 + c1 * u)) (h3 : 2 * (c0 + c1 * v) ≤ v) (h4 : -v ≤ 2 * (c0 + c1 * v)) :
    |c0 + c1 * θ| * 2 ≤ θ := by
  have e1 := affine_nonneg (c0 := -2 * c0) (c1 := 1 - 2 * c1) hu hv (by linarith) (by linarith)
  have e2 := affine_nonneg (c0 := 2 * c0) (c1 := 1 + 2 * c1) hu hv (by linarith) (by linarith)
  have : |c0 + c1 * θ| ≤ θ / 2 := by rw [abs_le]; constructor <;> linarith
  linarith

theorem lq_le {la : ℚ × ℚ} {n : ℤ} {x : ℚ} (h : 2 * lval (la.1, la.2 - n) x ≤ x) :
    2 * ((la.1 : ℝ) + ((la.2 : ℝ) - n) * x) ≤ x := by
  have := (Rat.cast_le (K := ℝ)).2 h
  simp only [lval] at this
  push_cast at this
  exact this

theorem lq_ge {la : ℚ × ℚ} {n : ℤ} {x : ℚ} (h : -x ≤ 2 * lval (la.1, la.2 - n) x) :
    -(x : ℝ) ≤ 2 * ((la.1 : ℝ) + ((la.2 : ℝ) - n) * x) := by
  have := (Rat.cast_le (K := ℝ)).2 h
  simp only [lval] at this
  push_cast at this
  exact this

/-- **Soundness of `affineOn`.** -/
theorem affineOn_sound (α κ u v : ℚ) (hu : 0 < u) :
    ∀ (e : Expr) (l : ℚ × ℚ), affineOn α κ u v e = some l → ∀ θ : ℝ, (u : ℝ) < θ → θ ≤ v →
      prof α κ θ e = (l.1 : ℝ) + l.2 * θ := by
  intro e
  induction e with
  | vr => intro l h θ _ _; simp only [affineOn, Option.some.injEq] at h; subst h; simp [prof, Expr.evalR]
  | vp => intro l h θ _ _; simp only [affineOn, Option.some.injEq] at h; subst h; simp [prof, Expr.evalR]
  | vm => intro l h θ _ _; simp only [affineOn, Option.some.injEq] at h; subst h; simp [prof, Expr.evalR]
  | vk => intro l h θ _ _; simp only [affineOn, Option.some.injEq] at h; subst h; simp [prof, Expr.evalR]
  | cst n => intro l h θ _ _; simp only [affineOn, Option.some.injEq] at h; subst h; simp [prof, Expr.evalR]
  | add a b iha ihb =>
    intro l h θ h1 h2
    simp only [affineOn] at h
    rcases ha : affineOn α κ u v a with _ | la <;> rcases hb : affineOn α κ u v b with _ | lb <;>
      simp only [ha, hb, reduceCtorEq, Option.some.injEq] at h
    subst h
    rw [prof_add, iha la ha θ h1 h2, ihb lb hb θ h1 h2]; push_cast; ring
  | smul c a iha =>
    intro l h θ h1 h2
    simp only [affineOn] at h
    rcases ha : affineOn α κ u v a with _ | la <;> simp only [ha, reduceCtorEq, Option.some.injEq] at h
    subst h
    rw [prof_smul, iha la ha θ h1 h2]; push_cast; ring
  | tsub a b iha ihb =>
    intro l h θ h1 h2
    simp only [affineOn] at h
    rcases ha : affineOn α κ u v a with _ | la <;> rcases hb : affineOn α κ u v b with _ | lb <;>
      simp only [ha, hb, reduceCtorEq] at h
    rw [prof_tsub, iha la ha θ h1 h2, ihb lb hb θ h1 h2]
    split_ifs at h with c1 c2 <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h
    · have := lval_nonneg h1.le h2 c1.1 c1.2; push_cast at this ⊢
      rw [max_eq_left (by linarith)]; ring
    · have := lval_nonpos h1.le h2 c2.1 c2.2; push_cast at this ⊢
      rw [max_eq_right (by linarith)]; ring
  | mn a b iha ihb =>
    intro l h θ h1 h2
    simp only [affineOn] at h
    rcases ha : affineOn α κ u v a with _ | la <;> rcases hb : affineOn α κ u v b with _ | lb <;>
      simp only [ha, hb, reduceCtorEq] at h
    rw [prof_mn, iha la ha θ h1 h2, ihb lb hb θ h1 h2]
    split_ifs at h with c1 c2 <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h
    · have := lval_nonpos h1.le h2 c1.1 c1.2; push_cast at this
      rw [min_eq_left (by linarith)]
    · have := lval_nonneg h1.le h2 c2.1 c2.2; push_cast at this
      rw [min_eq_right (by linarith)]
  | mx a b iha ihb =>
    intro l h θ h1 h2
    simp only [affineOn] at h
    rcases ha : affineOn α κ u v a with _ | la <;> rcases hb : affineOn α κ u v b with _ | lb <;>
      simp only [ha, hb, reduceCtorEq] at h
    rw [prof_mx, iha la ha θ h1 h2, ihb lb hb θ h1 h2]
    split_ifs at h with c1 c2 <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h
    · have := lval_nonneg h1.le h2 c1.1 c1.2; push_cast at this
      rw [max_eq_left (by linarith)]
    · have := lval_nonpos h1.le h2 c2.1 c2.2; push_cast at this
      rw [max_eq_right (by linarith)]
  | dist a iha =>
    intro l h θ h1 h2
    simp only [affineOn] at h
    rcases ha : affineOn α κ u v a with _ | la <;> simp only [ha, reduceCtorEq] at h
    have hu' : (0 : ℝ) < u := by exact_mod_cast hu
    have hθ : 0 < θ := lt_trans hu' h1
    rw [prof_dist, iha la ha θ h1 h2]
    generalize Rat.floor (lval la ((u + v) / 2) / ((u + v) / 2) + 1 / 2) = n at h
    have hX : ((la.1 : ℝ) + la.2 * θ) / θ - n = ((la.1 : ℝ) + ((la.2 : ℝ) - n) * θ) / θ := by
      field_simp; ring
    split_ifs at h with c1 c2 c3 <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h
    · obtain ⟨a1, a2, a3, a4⟩ := c1
      have hb := two_abs_le h1.le h2 (lq_le a1) (lq_ge a2) (lq_le a3) (lq_ge a4)
      have s1 := lval_nonneg (d := (la.1, la.2 - n)) h1.le h2 c2.1 c2.2
      push_cast at s1 ⊢
      have hle : |((la.1 : ℝ) + la.2 * θ) / θ - n| ≤ 1 / 2 := by
        rw [hX, abs_div, abs_of_pos hθ, div_le_iff₀ hθ]; linarith
      rw [latDist_eq _ n hle, hX, abs_div, abs_of_pos hθ, abs_of_nonneg s1]
      field_simp
    · obtain ⟨a1, a2, a3, a4⟩ := c1
      have hb := two_abs_le h1.le h2 (lq_le a1) (lq_ge a2) (lq_le a3) (lq_ge a4)
      have s1 := lval_nonpos (d := (la.1, la.2 - n)) h1.le h2 c3.1 c3.2
      push_cast at s1 ⊢
      have hle : |((la.1 : ℝ) + la.2 * θ) / θ - n| ≤ 1 / 2 := by
        rw [hX, abs_div, abs_of_pos hθ, div_le_iff₀ hθ]; linarith
      rw [latDist_eq _ n hle, hX, abs_div, abs_of_pos hθ, abs_of_nonpos s1]
      field_simp
      ring
  | ap =>
    intro l h θ h1 h2
    simp only [affineOn] at h
    split_ifs at h with c1 <;> simp only [Option.some.injEq, reduceCtorEq] at h
    subst h
    rw [prof_ap, floor_inv_eq hu h1 h2 c1]; push_cast; ring
  | sp =>
    intro l h θ h1 h2
    simp only [affineOn] at h
    split_ifs at h with c1 <;> simp only [Option.some.injEq, reduceCtorEq] at h
    subst h
    rw [prof_sp, floor_inv_eq hu h1 h2 c1]; push_cast; ring

end CatalanCore.Uniform.Content.BankShared.Check
