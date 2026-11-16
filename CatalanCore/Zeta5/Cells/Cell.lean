module

public import CatalanCore.Zeta5.Cells.Compose
public import CatalanCore.Zeta5.Cells.Enclosures

@[expose] public section

/-!
# Z5-CELLS, part 4: the generic cell bound for `T − Vy ∘ Y` (ZD19, ZD20)

**ZD19** is `TaylorCell.taylor_cell_ub` / `taylor_cell_ub_rat` (audited, reused unchanged): for a
derivative tower `f` of order `M ≥ 3` on `[c-r, c+r]`,
`f 0 x ≤ A0 + max (qs l1 A2 r) (qs u1 A2 r) + Σ_{3 ≤ k < M} B_k r^k + B_M r^M` with `qs` the exact
quadratic maximum and `B_M ≥ sup |f^{(M)}| / M!` (Lagrange).  Here `M = 5`: coefficients up to
order 4 at the centre, the Lagrange remainder of order 5.

**ZD20** (this file): for the field `x ↦ T 0 x − Vy α (Y 0 x)` the tower is
`compT j = T j − fdb (Dv α · ∘ Y 0) Y j` (`isTower_compT`); its point values at the centre are
rational plus the two transcendental slots `Dv 0 = Vy`, `Dv 1 = V1`, and `fdb` is affine in the
slot `Dv 1` with coefficient `Y j`, so the enclosure of `compT j c` costs one multiplication
(`fdb_affine`).  The order-5 remainder is bounded by the Faà di Bruno majorant (`abs_fdb5_le`) with
`|Y i| ≤ Ym i` and the pole-distance bounds `|Dv k| ≤ Dmq k` (`abs_Dv_le`).  `cellUB` is the
rational bound; `cell_sound` is the generic soundness theorem; nothing here is specific to the
design (`α`, `T`, `Y` are parameters).
-/

namespace CatalanCore.Zeta5.Cells

open Set Nat CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.GenD.Signed.LogEval
open CatalanMeasure.Cert (qabs)

noncomputable section

/-- **ZD19**, the generic cell bound in the ledger form (`TaylorCell.taylor_cell_ub`, audited and
reused unchanged): `f 0 x ≤ A0 + max (qs l1 A2 r) (qs u1 A2 r) + Σ_{3 ≤ k < M} B_k r^k + B_M r^M`,
where `A0 ≥ f 0 c`, `l1 ≤ f 1 c ≤ u1`, `A2 ≥ f 2 c / 2`, `B_k ≥ |f k c| / k!` and
`B_M ≥ sup_{cell} |f M| / M!` (Lagrange remainder); `qs a A r` is the exact maximum of
`a y + A y²` over `|y| ≤ r` (`quadSupR`, vertex or endpoint). -/
theorem zd19_cell_bound {f : ℕ → ℝ → ℝ} {c r : ℝ} {M : ℕ} (hM : 3 ≤ M) (hf : IsTower f c r M)
    {A0 l1 u1 A2 BM : ℝ} {B : ℕ → ℝ}
    (h0 : f 0 c ≤ A0) (h1l : l1 ≤ f 1 c) (h1u : f 1 c ≤ u1) (h2 : f 2 c / 2 ≤ A2)
    (hB : ∀ k, 3 ≤ k → k < M → |f k c| / (k ! : ℝ) ≤ B k)
    (hBM : ∀ x ∈ Icc (c - r) (c + r), |f M x| / (M ! : ℝ) ≤ BM) :
    ∀ x ∈ Icc (c - r) (c + r), f 0 x ≤ tmUBR A0 l1 u1 A2 r B BM M :=
  taylor_cell_ub hM hf h0 h1l h1u h2 hB hBM

/-! ### the derivative chain of `Vy` -/

theorem hasDerivAt_Dv {α : ℝ} (hα : 0 < α) (k : ℕ) (hk : k < 5) (y : ℝ) :
    HasDerivAt (Dv α k) (Dv α (k + 1) y) y := by
  interval_cases k
  · exact hasDerivAt_Vy hα y
  · exact hasDerivAt_V1 hα y
  · exact (((hasDerivAt_Gd0 one_pos y).const_mul (-2)).fun_add
      ((hasDerivAt_Gd0 hα y).const_mul 12))
  · exact (((hasDerivAt_Gd1 one_pos y).const_mul (-2)).fun_add
      ((hasDerivAt_Gd1 hα y).const_mul 12))
  · exact (((hasDerivAt_Gd2 one_pos y).const_mul (-2)).fun_add
      ((hasDerivAt_Gd2 hα y).const_mul 12))

theorem continuous_Dv {α : ℝ} (hα : 0 < α) (k : ℕ) (hk : k ≤ 5) : Continuous (Dv α k) := by
  rcases Nat.lt_or_ge k 5 with h | h
  · exact continuous_iff_continuousAt.2 fun y => (hasDerivAt_Dv hα k h y).continuousAt
  · have hk5 : k = 5 := le_antisymm hk h
    subst hk5
    have hG : ∀ a : ℝ, 0 < a → Continuous (Gd 3 a) := by
      intro a ha
      have : Gd 3 a = fun y => 24 * a * y * (a ^ 2 - y ^ 2) / (y ^ 2 + a ^ 2) ^ 4 := by
        funext y; simp [Gd]
      rw [this]
      exact Continuous.div (by fun_prop) (by fun_prop) (fun y => by positivity)
    have : Dv α 5 = fun y => -2 * Gd 3 1 y + 12 * Gd 3 α y := rfl
    rw [this]
    exact (continuous_const.mul (hG 1 one_pos)).add (continuous_const.mul (hG α hα))

/-! ### the tower of the composite field -/

/-- the tower of `x ↦ T 0 x − Vy α (Y 0 x)`. -/
def compT (α : ℝ) (T Y : ℕ → ℝ → ℝ) (j : ℕ) (x : ℝ) : ℝ :=
  T j x - fdb (fun k => Dv α k (Y 0 x)) (fun i => Y i x) j

theorem isTower_compT {α : ℝ} (hα : 0 < α) {T Y : ℕ → ℝ → ℝ} {c r : ℝ}
    (hT : IsTower T c r 5) (hYd : ∀ i < 5, ∀ x, HasDerivAt (Y i) (Y (i + 1) x) x)
    (hYc : ∀ i ≤ 5, Continuous (Y i)) : IsTower (compT α T Y) c r 5 where
  cont j hj := by
    refine (hT.cont j hj).sub (Continuous.continuousOn ?_)
    have hD : ∀ k ≤ 5, Continuous fun x => Dv α k (Y 0 x) :=
      fun k hk => (continuous_Dv hα k hk).comp (hYc 0 (by norm_num))
    have h0 := hD 0 (by norm_num)
    have h1 := hD 1 (by norm_num)
    have h2 := hD 2 (by norm_num)
    have h3 := hD 3 (by norm_num)
    have h4 := hD 4 (by norm_num)
    have h5 := hD 5 (by norm_num)
    have y1 := hYc 1 (by norm_num)
    have y2 := hYc 2 (by norm_num)
    have y3 := hYc 3 (by norm_num)
    have y4 := hYc 4 (by norm_num)
    have y5 := hYc 5 (by norm_num)
    interval_cases j <;> simp only [fdb] <;> fun_prop
  der j hj x hx := by
    have hD : ∀ k < 5, HasDerivAt (fun z => Dv α k (Y 0 z)) (Dv α (k + 1) (Y 0 x) * Y 1 x) x :=
      fun k hk => (hasDerivAt_Dv hα k hk (Y 0 x)).comp x (hYd 0 (by norm_num) x)
    exact (hT.der j hj x hx).sub (hasDerivAt_fdb hD (fun i hi => hYd i hi x) j hj)

/-! ### rational values of the derivative tower at a rational point -/

/-- `Gd` on rationals. -/
def Gq : ℕ → ℚ → ℚ → ℚ
  | 0, a, y => a / (y ^ 2 + a ^ 2)
  | 1, a, y => -2 * a * y / (y ^ 2 + a ^ 2) ^ 2
  | 2, a, y => a * (6 * y ^ 2 - 2 * a ^ 2) / (y ^ 2 + a ^ 2) ^ 3
  | 3, a, y => 24 * a * y * (a ^ 2 - y ^ 2) / (y ^ 2 + a ^ 2) ^ 4
  | _, _, _ => 0

/-- `Dv α k y` for `2 ≤ k ≤ 5` on rationals. -/
def Dq (α y : ℚ) (k : ℕ) : ℚ := -2 * Gq (k - 2) 1 y + 12 * Gq (k - 2) α y

theorem Dq_cast (α y : ℚ) (k : ℕ) (hk2 : 2 ≤ k) (hk5 : k ≤ 5) :
    Dv (α : ℝ) k (y : ℝ) = ((Dq α y k : ℚ) : ℝ) := by
  interval_cases k <;> simp [Dv, Gd, Dq, Gq]

/-- the slots `D 0, D 1` get the centres `v0, v1` of their enclosures. -/
def Dvec (α y v0 v1 : ℚ) (k : ℕ) : ℚ :=
  if k = 0 then v0 else if k = 1 then v1 else Dq α y k

/-- the bound `|Dv k| ≤ Dmq k` (`k = 1..5`): `|V1| ≤ 10π ≤ 32`, then the pole-distance bound. -/
def Dmq (ρ1 ρa : ℚ) (k : ℕ) : ℚ :=
  if k = 1 then 32
  else if 2 ≤ k then 2 * (((k - 2).factorial : ℚ) / ρ1 ^ (k - 1))
    + 12 * (((k - 2).factorial : ℚ) / ρa ^ (k - 1))
  else 0

theorem abs_Dv_le_Dmq {α : ℝ} (hα : 0 < α) {y : ℝ} {ρ1 ρa : ℚ} (h1 : 0 < ρ1) (ha : 0 < ρa)
    (hs1 : (ρ1 : ℝ) ^ 2 ≤ y ^ 2 + 1) (hsa : (ρa : ℝ) ^ 2 ≤ y ^ 2 + α ^ 2) (k : ℕ)
    (hk1 : 1 ≤ k) (hk5 : k ≤ 5) : |Dv α k y| ≤ ((Dmq ρ1 ρa k : ℚ) : ℝ) := by
  rcases Nat.eq_or_lt_of_le hk1 with rfl | hk
  · simp only [Dmq, if_true]
    have := abs_V1_le α y
    have hpi := Real.pi_lt_d2
    show |V1 α y| ≤ ((32 : ℚ) : ℝ)
    push_cast
    linarith
  · obtain ⟨n, rfl⟩ : ∃ n, k = n + 2 := ⟨k - 2, by omega⟩
    have hb := abs_Dv_le hα (by exact_mod_cast h1) (by exact_mod_cast ha) hs1 hsa n (by omega)
    have e : Dmq ρ1 ρa (n + 2) = 2 * (((n).factorial : ℚ) / ρ1 ^ (n + 1))
        + 12 * (((n).factorial : ℚ) / ρa ^ (n + 1)) := by
      simp [Dmq]
    rw [e]
    push_cast
    exact hb

/-! ### the rational cell bound -/

/-- the data of one cell: point enclosures `tq ± te` of `T j c` (`j ≤ 4`), the rational values
`yq j` of `Y j c`, enclosures `v0 ± e0`, `v1 ± e1` of `Vy`, `V1` at `y_c = yq 0`, the remainder
bound `TR ≥ sup |T 5|`, bounds `Ym i ≥ |Y i|` on the cell, pole-distance bounds `ρ1, ρa`. -/
def cellUB (α : ℚ) (tq te yq : ℕ → ℚ) (v0 e0 v1 e1 TR : ℚ) (Ym : ℕ → ℚ) (ρ1 ρa r : ℚ) : ℚ :=
  tmUBQ
    (tq 0 - fdb (Dvec α (yq 0) v0 v1) yq 0 + (te 0 + e0))
    (tq 1 - fdb (Dvec α (yq 0) v0 v1) yq 1 - (te 1 + e1 * qabs (yq 1)))
    (tq 1 - fdb (Dvec α (yq 0) v0 v1) yq 1 + (te 1 + e1 * qabs (yq 1)))
    ((tq 2 - fdb (Dvec α (yq 0) v0 v1) yq 2 + (te 2 + e1 * qabs (yq 2))) / 2)
    r
    [(qabs (tq 3 - fdb (Dvec α (yq 0) v0 v1) yq 3) + (te 3 + e1 * qabs (yq 3))) / 6,
     (qabs (tq 4 - fdb (Dvec α (yq 0) v0 v1) yq 4) + (te 4 + e1 * qabs (yq 4))) / 24]
    ((TR + fdbBound (Dmq ρ1 ρa) Ym) / 120)

/-- **Generic soundness of the cell bound (ZD19 + ZD20).**  For the field
`x ↦ T 0 x − Vy α (Y 0 x)` on `[c-r, c+r]`: every `x` of the cell has value `≤ cellUB …`. -/
theorem cell_sound {α : ℚ} (hα : 0 < α) {T Y : ℕ → ℝ → ℝ} {c r : ℝ}
    (hT : IsTower T c r 5) (hYd : ∀ i < 5, ∀ x, HasDerivAt (Y i) (Y (i + 1) x) x)
    (hYc : ∀ i ≤ 5, Continuous (Y i))
    {tq te yq : ℕ → ℚ} {v0 e0 v1 e1 TR : ℚ} {Ym : ℕ → ℚ} {ρ1 ρa rq : ℚ}
    (hrq : (rq : ℝ) = r)
    (hTenc : ∀ j ≤ 4, Enc (T j c) (tq j, te j))
    (hyq : ∀ j ≤ 5, Y j c = (yq j : ℝ))
    (hD0 : Enc (Vy (α : ℝ) (Y 0 c)) (v0, e0)) (hD1 : Enc (V1 (α : ℝ) (Y 0 c)) (v1, e1))
    (hTR : ∀ x ∈ Icc (c - r) (c + r), |T 5 x| ≤ (TR : ℝ))
    (hYm : ∀ x ∈ Icc (c - r) (c + r), ∀ i, 1 ≤ i → i ≤ 5 → |Y i x| ≤ (Ym i : ℝ))
    (hρ1 : 0 < ρ1) (hρa : 0 < ρa)
    (hρ : ∀ x ∈ Icc (c - r) (c + r),
      (ρ1 : ℝ) ^ 2 ≤ Y 0 x ^ 2 + 1 ∧ (ρa : ℝ) ^ 2 ≤ Y 0 x ^ 2 + (α : ℝ) ^ 2) :
    ∀ x ∈ Icc (c - r) (c + r),
      T 0 x - Vy (α : ℝ) (Y 0 x) ≤
        ((cellUB α tq te yq v0 e0 v1 e1 TR Ym ρ1 ρa rq : ℚ) : ℝ) := by
  have hαR : (0 : ℝ) < (α : ℝ) := by exact_mod_cast hα
  have hF := isTower_compT hαR hT hYd hYc
  -- point values of the tower
  set Dr : ℕ → ℝ := fun k => Dv (α : ℝ) k (Y 0 c) with hDr
  set Dv' : ℕ → ℚ := Dvec α (yq 0) v0 v1 with hDv'
  have hY0 : Y 0 c = (yq 0 : ℝ) := hyq 0 (by norm_num)
  have hDk : ∀ k, 2 ≤ k → k ≤ 5 → Dr k = ((Dv' k : ℚ) : ℝ) := by
    intro k hk2 hk5
    simp only [hDr, hDv', Dvec]
    rw [if_neg (by omega), if_neg (by omega), hY0]
    exact Dq_cast α (yq 0) k hk2 hk5
  have hD0' : Enc (Dr 0) (v0, e0) := hD0
  have hD1' : Enc (Dr 1) (v1, e1) := hD1
  have hdelta : |Dr 1 - (v1 : ℝ)| ≤ (e1 : ℝ) := hD1
  have hYc' : ∀ i, 1 ≤ i → i ≤ 5 → Y i c = (yq i : ℝ) := fun i _ hi => hyq i hi
  have habs : ∀ q : ℚ, |(q : ℝ)| = ((qabs q : ℚ) : ℝ) := by
    intro q; rw [CatalanMeasure.Cert.qabs_eq]; push_cast; rfl
  -- enclosures of the tower values at the centre
  have hF0 : Enc (compT (α : ℝ) T Y 0 c) (tq 0 - fdb Dv' yq 0, te 0 + e0) := by
    have h0 : |T 0 c - (tq 0 : ℝ)| ≤ (te 0 : ℝ) := hTenc 0 (by norm_num)
    have hq : ((fdb Dv' yq 0 : ℚ) : ℝ) = (v0 : ℝ) := by
      simp [hDv', fdb, Dvec]
    have e : compT (α : ℝ) T Y 0 c = T 0 c - Dr 0 := by
      simp only [compT, fdb, hDr]
    unfold Enc
    rw [e]
    show |T 0 c - Dr 0 - (((tq 0 - fdb Dv' yq 0 : ℚ)) : ℝ)| ≤ ((te 0 + e0 : ℚ) : ℝ)
    rw [Rat.cast_sub, hq, Rat.cast_add]
    have h1 : |Dr 0 - (v0 : ℝ)| ≤ (e0 : ℝ) := hD0
    have : T 0 c - Dr 0 - ((tq 0 : ℝ) - (v0 : ℝ)) = (T 0 c - (tq 0 : ℝ)) - (Dr 0 - (v0 : ℝ)) := by
      ring
    rw [this]
    exact (abs_sub _ _).trans (add_le_add h0 h1)
  have hFj : ∀ j, 1 ≤ j → j ≤ 4 → Enc (compT (α : ℝ) T Y j c)
      (tq j - fdb Dv' yq j, te j + e1 * qabs (yq j)) := by
    intro j hj1 hj4
    have hj : |T j c - (tq j : ℝ)| ≤ (te j : ℝ) := hTenc j hj4
    have haff := fdb_affine Dr (fun k => (Dv' k : ℝ)) (fun i => (yq i : ℝ)) j hj1 (by omega)
      (fun k hk2 hk5 => hDk k hk2 hk5)
    have e : compT (α : ℝ) T Y j c = T j c - (fdb (fun k => (Dv' k : ℝ)) (fun i => (yq i : ℝ)) j
        + (Dr 1 - (Dv' 1 : ℝ)) * (yq j : ℝ)) := by
      simp only [compT]
      have : fdb (fun k => Dv (α : ℝ) k (Y 0 c)) (fun i => Y i c) j =
          fdb Dr (fun i => (yq i : ℝ)) j := by
        refine fdb_congr_Y _ _ _ j (by omega) fun i hi1 hi5 => hYc' i hi1 hi5
      rw [this, haff]
    have hv1 : Dv' 1 = v1 := by simp [hDv', Dvec]
    have hq : ((fdb Dv' yq j : ℚ) : ℝ) = fdb (fun k => (Dv' k : ℝ)) (fun i => (yq i : ℝ)) j :=
      fdb_cast Dv' yq j
    unfold Enc
    rw [e, hv1]
    show |T j c - (fdb (fun k => (Dv' k : ℝ)) (fun i => (yq i : ℝ)) j + (Dr 1 - (v1 : ℝ)) * (yq j : ℝ))
      - (((tq j - fdb Dv' yq j : ℚ)) : ℝ)| ≤ ((te j + e1 * qabs (yq j) : ℚ) : ℝ)
    rw [Rat.cast_sub, hq, Rat.cast_add, Rat.cast_mul, ← habs]
    have h1 : |(Dr 1 - (v1 : ℝ)) * (yq j : ℝ)| ≤ (e1 : ℝ) * |(yq j : ℝ)| := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_right hdelta (abs_nonneg _)
    have : T j c - (fdb (fun k => (Dv' k : ℝ)) (fun i => (yq i : ℝ)) j + (Dr 1 - (v1 : ℝ)) * (yq j : ℝ))
        - ((tq j : ℝ) - fdb (fun k => (Dv' k : ℝ)) (fun i => (yq i : ℝ)) j) =
        (T j c - (tq j : ℝ)) - (Dr 1 - (v1 : ℝ)) * (yq j : ℝ) := by ring
    rw [this]
    exact (abs_sub _ _).trans (add_le_add hj h1)
  -- the remainder
  have hBM : ∀ x ∈ Icc (c - r) (c + r),
      |compT (α : ℝ) T Y 5 x| / (120 : ℝ) ≤
        (((TR + fdbBound (Dmq ρ1 ρa) Ym) / 120 : ℚ) : ℝ) := by
    intro x hx
    have hDm : ∀ k, 1 ≤ k → k ≤ 5 → |Dv (α : ℝ) k (Y 0 x)| ≤ ((Dmq ρ1 ρa k : ℚ) : ℝ) :=
      fun k hk1 hk5 => abs_Dv_le_Dmq hαR hρ1 hρa (hρ x hx).1 (hρ x hx).2 k hk1 hk5
    have hfb := abs_fdb5_le (fun k => Dv (α : ℝ) k (Y 0 x)) (fun i => Y i x)
      (fun k => ((Dmq ρ1 ρa k : ℚ) : ℝ)) (fun i => ((Ym i : ℚ) : ℝ)) hDm
      (fun i hi1 hi5 => hYm x hx i hi1 hi5)
    have hT5 := hTR x hx
    have h1 : |compT (α : ℝ) T Y 5 x| ≤ (TR : ℝ) + fdbBound (fun k => ((Dmq ρ1 ρa k : ℚ) : ℝ))
        (fun i => ((Ym i : ℚ) : ℝ)) := by
      unfold compT
      exact (abs_sub _ _).trans (add_le_add hT5 hfb)
    rw [← fdbBound_cast] at h1
    push_cast
    rw [div_le_div_iff_of_pos_right (by norm_num)]
    push_cast at h1
    linarith
  intro x hx
  have key := taylor_cell_ub_rat (f := compT (α : ℝ) T Y) (c := c) (r := r)
    [(qabs (tq 3 - fdb Dv' yq 3) + (te 3 + e1 * qabs (yq 3))) / 6,
     (qabs (tq 4 - fdb Dv' yq 4) + (te 4 + e1 * qabs (yq 4))) / 24]
    hF (A0 := tq 0 - fdb Dv' yq 0 + (te 0 + e0))
    (l1 := tq 1 - fdb Dv' yq 1 - (te 1 + e1 * qabs (yq 1)))
    (u1 := tq 1 - fdb Dv' yq 1 + (te 1 + e1 * qabs (yq 1)))
    (A2 := (tq 2 - fdb Dv' yq 2 + (te 2 + e1 * qabs (yq 2))) / 2)
    (BM := (TR + fdbBound (Dmq ρ1 ρa) Ym) / 120)
    (hF0.le_upper) (by simpa using (hFj 1 le_rfl (by norm_num)).ge_lower)
    (by simpa using (hFj 1 le_rfl (by norm_num)).le_upper)
    (by
      have := (hFj 2 (by norm_num) (by norm_num)).le_upper
      push_cast at this ⊢
      linarith)
    (by
      intro i hi
      have hi2 : i < 2 := by simpa using hi
      have hb : ∀ j, 3 ≤ j → j ≤ 4 → |compT (α : ℝ) T Y j c| ≤
          (((qabs (tq j - fdb Dv' yq j) + (te j + e1 * qabs (yq j)) : ℚ)) : ℝ) := by
        intro j hj3 hj4
        have h := hFj j (by omega) hj4
        have h' : |compT (α : ℝ) T Y j c - ((tq j - fdb Dv' yq j : ℚ) : ℝ)| ≤
            ((te j + e1 * qabs (yq j) : ℚ) : ℝ) := h
        have := abs_sub_abs_le_abs_sub (compT (α : ℝ) T Y j c)
          (((tq j - fdb Dv' yq j : ℚ)) : ℝ)
        rw [habs] at this
        push_cast at h' ⊢
        push_cast at this
        linarith
      interval_cases i
      · have := hb 3 le_rfl (by norm_num)
        simp only [List.getD_cons_zero]
        push_cast at this ⊢
        norm_num [Nat.factorial]
        linarith
      · have := hb 4 (by norm_num) le_rfl
        simp only [List.getD_cons_succ, List.getD_cons_zero]
        push_cast at this ⊢
        norm_num [Nat.factorial]
        linarith)
    (fun y hy => by have := hBM y hy; simpa [Nat.factorial] using this) rq hrq x hx
  exact key

end

end CatalanCore.Zeta5.Cells
