module

public import CatalanMeasure.GenD.Signed.RouteI.ChordTableData

@[expose] public section
set_option Elab.async false

/-!
# Route I `ChordLine`: the frozen chord table below an affine line on a cell (ledger G16)

`pwl K k v` is the piecewise linear `δ̂` through the knots (`ChordTable`).  A cell `[ylo, yhi]` of the real
coordinate `y` is sent by `t = 2y/(1+y²)` (increasing on `[-1,1]`) to the interval `[p, q]` of knots
`i0 .. i1`.  Then `δ̂(t) ≤ A + B t` on the cell as soon as it holds at the knots strictly inside (`vq j ≤ A + B kq j`)
and at the two end points `p`, `q` (chord value of the segment containing it): `pwl_le_line`.
`yChk` is the decidable certificate (exact rationals, data `ChordCell`), `yChk_sound` its soundness
for `δ̂ = pwl 865 kt vt` of `ChordTableData`.
-/

namespace CatalanMeasure.GenD.Signed.RouteI.ChordLine

open CatalanMeasure.GenD.Signed.RouteI CatalanMeasure.GenD.Signed.RouteI.ChordTable
  CatalanMeasure.GenD.Signed.RouteI.ChordTableData Set

/-! ### Generic piecewise linear lemma -/

theorem chordAt_left {k v : ℕ → ℝ} {i : ℕ} (hk : k i < k (i + 1)) : chordAt k v i (k i) = v i := by
  unfold chordAt
  have : k (i + 1) - k i ≠ 0 := (sub_pos.mpr hk).ne'
  field_simp
  ring

theorem chordAt_right {k v : ℕ → ℝ} {i : ℕ} (hk : k i < k (i + 1)) :
    chordAt k v i (k (i + 1)) = v (i + 1) := by
  unfold chordAt
  have : k (i + 1) - k i ≠ 0 := (sub_pos.mpr hk).ne'
  field_simp
  ring

theorem chordAt_agree {K : ℕ} {k v : ℕ → ℝ} (hk : ∀ i, i < K → k i < k (i + 1)) {i j : ℕ}
    (hi : i < K) (hj : j < K) {t : ℝ} (hti : t ∈ Icc (k i) (k (i + 1))) (htj : t ∈ Icc (k j) (k (j + 1))) :
    chordAt k v j t = chordAt k v i t := by
  rcases lt_trichotomy i j with h | h | h
  · -- i < j : t = k (i+1) = k j
    have h1 : k (i + 1) ≤ k j := by
      rcases Nat.lt_or_ge (i + 1) j with h' | h'
      · exact (k_lt hk _ _ h' (by omega)).le
      · have : i + 1 = j := by omega
        rw [this]
    have h2 : t = k j := le_antisymm (by linarith [hti.2]) htj.1
    have h3 : i + 1 = j := by
      by_contra hne
      have : k (i + 1) < k j := k_lt hk _ _ (by omega) (by omega)
      linarith [hti.2]
    have e1 : t = k (i + 1) := by rw [h3]; exact h2
    have a1 : chordAt k v j t = v j := by rw [h2]; exact chordAt_left (hk j hj)
    have a2 : chordAt k v i t = v (i + 1) := by rw [e1]; exact chordAt_right (hk i hi)
    rw [a1, a2, h3]
  · subst h; rfl
  · have h1 : k (j + 1) ≤ k i := by
      rcases Nat.lt_or_ge (j + 1) i with h' | h'
      · exact (k_lt hk _ _ h' (by omega)).le
      · have : j + 1 = i := by omega
        rw [this]
    have h2 : t = k i := le_antisymm (by linarith [htj.2]) hti.1
    have h3 : j + 1 = i := by
      by_contra hne
      have : k (j + 1) < k i := k_lt hk _ _ (by omega) (by omega)
      linarith [htj.2]
    have e1 : t = k (j + 1) := by rw [h3]; exact h2
    have a1 : chordAt k v i t = v i := by rw [h2]; exact chordAt_left (hk i hi)
    have a2 : chordAt k v j t = v (j + 1) := by rw [e1]; exact chordAt_right (hk j hj)
    rw [a1, a2, h3]

theorem pwl_eq_chord {K : ℕ} {k v : ℕ → ℝ} (hk : ∀ i, i < K → k i < k (i + 1)) {i : ℕ} (hi : i < K)
    {t : ℝ} (ht : t ∈ Icc (k i) (k (i + 1))) : pwl K k v t = chordAt k v i t := by
  have hset : {r | ∃ j, j < K ∧ t ∈ Icc (k j) (k (j + 1)) ∧ r = chordAt k v j t} = {chordAt k v i t} := by
    ext r
    simp only [mem_setOf_eq, mem_singleton_iff]
    constructor
    · rintro ⟨j, hj, hjt, rfl⟩
      exact chordAt_agree hk hi hj ht hjt
    · rintro rfl
      exact ⟨i, hi, ht, rfl⟩
  unfold pwl
  rw [hset, csSup_singleton]

theorem exists_seg_between {K : ℕ} {k : ℕ → ℝ} (hk : ∀ i, i < K → k i < k (i + 1)) {i0 i1 : ℕ}
    (h01 : i0 ≤ i1) (h1K : i1 < K) {t : ℝ} (h0 : k i0 ≤ t) (h1 : t ≤ k (i1 + 1)) :
    ∃ i, i0 ≤ i ∧ i ≤ i1 ∧ t ∈ Icc (k i) (k (i + 1)) := by
  have hex := exists_seg (K := i1 + 1 - i0) (k := fun j => k (i0 + j)) (by omega)
    (t := t) (by simpa using h0) (by
      have : i0 + (i1 + 1 - i0) = i1 + 1 := by omega
      simpa [this] using h1)
  obtain ⟨j, hj, hjt⟩ := hex
  refine ⟨i0 + j, by omega, by omega, ?_⟩
  simpa [add_assoc] using hjt

/-- **A piecewise linear function below a line on `[p, q]`**: the line dominates at the knots strictly
inside `(i0, i1]` and the chord at `p` (segment `i0`) and at `q` (segment `i1`). -/
theorem pwl_le_line {K : ℕ} {k v : ℕ → ℝ} (hk : ∀ i, i < K → k i < k (i + 1)) {i0 i1 : ℕ}
    (h01 : i0 ≤ i1) (h1K : i1 < K) {p q A B : ℝ}
    (hp0 : k i0 ≤ p) (hp1 : p ≤ k (i0 + 1)) (hq0 : k i1 ≤ q) (hq1 : q ≤ k (i1 + 1))
    (hkn : ∀ j, i0 < j → j ≤ i1 → v j ≤ A + B * k j)
    (hP : chordAt k v i0 p ≤ A + B * p) (hQ : chordAt k v i1 q ≤ A + B * q)
    {t : ℝ} (ht1 : p ≤ t) (ht2 : t ≤ q) : pwl K k v t ≤ A + B * t := by
  obtain ⟨i, hi0, hi1, hseg⟩ := exists_seg_between hk h01 h1K (hp0.trans ht1) (ht2.trans hq1)
  have hiK : i < K := by omega
  rw [pwl_eq_chord hk hiK hseg]
  have hd : 0 < k (i + 1) - k i := sub_pos.mpr (hk i hiK)
  -- H s = (A + B s) d - ((k1 - s) v0 + (s - k0) v1)
  set k0 := k i with hk0
  set k1 := k (i + 1) with hk1
  set v0 := v i with hv0
  set v1 := v (i + 1) with hv1
  have hH : ∀ s : ℝ, chordAt k v i s ≤ A + B * s ↔
      0 ≤ (A + B * s) * (k1 - k0) - ((k1 - s) * v0 + (s - k0) * v1) := by
    intro s
    unfold chordAt
    rw [div_le_iff₀ hd]
    constructor <;> intro h <;> linarith
  rw [hH]
  -- left end
  obtain ⟨P, hPt, hHP⟩ : ∃ P : ℝ, P ≤ t ∧ 0 ≤ (A + B * P) * (k1 - k0) - ((k1 - P) * v0 + (P - k0) * v1) := by
    by_cases hi : i = i0
    · subst hi
      exact ⟨p, ht1, (hH p).mp hP⟩
    · have hgt : i0 < i := by omega
      refine ⟨k0, hseg.1, ?_⟩
      have := hkn i hgt hi1
      nlinarith [mul_nonneg (sub_nonneg.mpr this) hd.le]
  obtain ⟨Q, hQt, hHQ⟩ : ∃ Q : ℝ, t ≤ Q ∧ 0 ≤ (A + B * Q) * (k1 - k0) - ((k1 - Q) * v0 + (Q - k0) * v1) := by
    by_cases hi : i = i1
    · subst hi
      exact ⟨q, ht2, (hH q).mp hQ⟩
    · have hlt : i < i1 := by omega
      refine ⟨k1, hseg.2, ?_⟩
      have := hkn (i + 1) (by omega) (by omega)
      nlinarith [mul_nonneg (sub_nonneg.mpr this) hd.le]
  -- affine in s: slope β
  set β := B * (k1 - k0) + v0 - v1 with hβ
  have hexp : ∀ s : ℝ, (A + B * s) * (k1 - k0) - ((k1 - s) * v0 + (s - k0) * v1) =
      (A * (k1 - k0) - k1 * v0 + k0 * v1) + β * s := by
    intro s; rw [hβ]; ring
  rw [hexp] at hHP hHQ ⊢
  rcases le_total 0 β with hb | hb
  · nlinarith [mul_nonneg hb (sub_nonneg.mpr hPt)]
  · nlinarith [mul_nonneg (neg_nonneg.mpr hb) (sub_nonneg.mpr hQt)]

theorem pwl_zero_outside {K : ℕ} {k v : ℕ → ℝ} (hk : ∀ i, i < K → k i < k (i + 1)) {t : ℝ}
    (h : t < k 0 ∨ k K < t) : pwl K k v t = 0 := by
  unfold pwl
  have : {r | ∃ i, i < K ∧ t ∈ Icc (k i) (k (i + 1)) ∧ r = chordAt k v i t} = ∅ := by
    ext r
    simp only [mem_setOf_eq, mem_empty_iff_false, iff_false]
    rintro ⟨i, hi, hit, rfl⟩
    rcases h with h | h
    · have : k 0 ≤ k i := by
        rcases Nat.eq_zero_or_pos i with h0 | h0
        · rw [h0]
        · exact (k_lt hk _ _ h0 (by omega)).le
      linarith [hit.1]
    · have : k (i + 1) ≤ k K := by
        rcases Nat.lt_or_ge (i + 1) K with h0 | h0
        · exact (k_lt hk _ _ h0 (by omega)).le
        · have : i + 1 = K := by omega
          rw [this]
      linarith [hit.2]
  rw [this, Real.sSup_empty]


/-! ### The frozen table: exact rational certificate -/

/-- Knot `k_i` as a rational. -/
def kq (i : ℕ) : ℚ := (knotZ i : ℚ) / 2 ^ 40
/-- Knot value `v_i` as a rational. -/
def vq (i : ℕ) : ℚ := (vZ i : ℚ) / 10 ^ 9
/-- The chord of segment `i` at `t`. -/
def chordQ (i : ℕ) (t : ℚ) : ℚ := ((kq (i + 1) - t) * vq i + (t - kq i) * vq (i + 1)) / (kq (i + 1) - kq i)

/-- Data of one cell: the segment indices of its end points and the end points `pN/2^100`, `qN/2^100`. -/
structure ChordCell where
  i0 : ℕ
  i1 : ℕ
  pN : ℤ
  qN : ℤ

def cp (c : ChordCell) : ℚ := (c.pN : ℚ) / 2 ^ 100
def cq (c : ChordCell) : ℚ := (c.qN : ℚ) / 2 ^ 100

def lineChk (c : ChordCell) (A B : ℚ) : Bool :=
  decide (c.i0 ≤ c.i1) && decide (c.i1 < 865) && decide (kq c.i0 ≤ cp c) && decide (cp c ≤ kq (c.i0 + 1)) &&
    decide (kq c.i1 ≤ cq c) && decide (cq c ≤ kq (c.i1 + 1)) &&
    (List.range' (c.i0 + 1) (c.i1 - c.i0)).all (fun j => decide (vq j ≤ A + B * kq j)) &&
    decide (chordQ c.i0 (cp c) ≤ A + B * cp c) && decide (chordQ c.i1 (cq c) ≤ A + B * cq c)

theorem kt_eq (i : ℕ) : kt i = ((kq i : ℚ) : ℝ) := by
  unfold kt kq; push_cast; rfl

theorem vt_eq (i : ℕ) : vt i = ((vq i : ℚ) : ℝ) := by
  unfold vt vq; push_cast; rfl

theorem chordAt_eq (i : ℕ) (t : ℚ) : chordAt kt vt i (t : ℝ) = ((chordQ i t : ℚ) : ℝ) := by
  unfold chordAt chordQ
  push_cast
  simp only [kt_eq, vt_eq]

theorem lineChk_sound {c : ChordCell} {A B : ℚ} (h : lineChk c A B = true) {t : ℝ}
    (ht1 : (cp c : ℝ) ≤ t) (ht2 : t ≤ (cq c : ℝ)) : pwl 865 kt vt t ≤ (A : ℝ) + (B : ℝ) * t := by
  simp only [lineChk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h01, h1K⟩, hp0⟩, hp1⟩, hq0⟩, hq1⟩, hkn⟩, hP⟩, hQ⟩ := h
  have rc : ∀ {a b : ℚ}, a ≤ b → (a : ℝ) ≤ (b : ℝ) := fun h => Rat.cast_le.mpr h
  refine pwl_le_line (K := 865) (k := kt) (v := vt) (i0 := c.i0) (i1 := c.i1) kt_lt h01 h1K
    (p := (cp c : ℝ)) (q := (cq c : ℝ)) (A := (A : ℝ)) (B := (B : ℝ)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ht1 ht2
  · rw [kt_eq]; exact rc hp0
  · rw [kt_eq]; exact rc hp1
  · rw [kt_eq]; exact rc hq0
  · rw [kt_eq]; exact rc hq1
  · intro j hj1 hj2
    have hm : j ∈ List.range' (c.i0 + 1) (c.i1 - c.i0) := by
      rw [List.mem_range'_1]; omega
    have := hkn j hm
    rw [vt_eq, kt_eq]
    exact_mod_cast rc this
  · rw [chordAt_eq]; exact_mod_cast rc hP
  · rw [chordAt_eq]; exact_mod_cast rc hQ

/-! ### Cells in the real coordinate `y`, `t = 2y/(1+y²)` -/

def tauQ (y : ℚ) : ℚ := 2 * y / (1 + y ^ 2)

theorem tau_mono {v y : ℝ} (hv : -1 ≤ v) (hvy : v ≤ y) (hy : y ≤ 1) :
    2 * v / (1 + v ^ 2) ≤ 2 * y / (1 + y ^ 2) := by
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_nonneg (sub_nonneg.mpr hvy) (show 0 ≤ 1 - y * v by nlinarith)]

/-- The certificate of a cell `[ylo, yhi] ⊆ [-1, 1]` for the line `A + B t`: either its image lies outside the
hull of the knots, or `lineChk` holds on `[p, q] ⊇ image ∩ hull`. -/
def yChk (ylo yhi A B : ℚ) (c : ChordCell) : Bool :=
  decide (-1 ≤ ylo) && decide (ylo ≤ yhi) && decide (yhi ≤ 1) &&
    (decide (tauQ yhi < kq 0) || decide (kq 865 < tauQ ylo) ||
      ((decide (cp c ≤ tauQ ylo) || decide (cp c ≤ kq 0)) &&
        (decide (tauQ yhi ≤ cq c) || decide (kq 865 ≤ cq c)) && lineChk c A B))

theorem yChk_sound {ylo yhi A B : ℚ} {c : ChordCell} (h : yChk ylo yhi A B c = true) {y : ℝ}
    (hy1 : (ylo : ℝ) ≤ y) (hy2 : y ≤ (yhi : ℝ)) (h0 : kt 0 ≤ 2 * y / (1 + y ^ 2))
    (h865 : 2 * y / (1 + y ^ 2) ≤ kt 865) :
    pwl 865 kt vt (2 * y / (1 + y ^ 2)) ≤ (A : ℝ) + (B : ℝ) * (2 * y / (1 + y ^ 2)) := by
  simp only [yChk, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hlo, hle⟩, hhi⟩, hcase⟩ := h
  have rc : ∀ {a b : ℚ}, a ≤ b → (a : ℝ) ≤ (b : ℝ) := fun h => Rat.cast_le.mpr h
  have hlo' : (-1 : ℝ) ≤ ylo := by exact_mod_cast hlo
  have hhi' : (yhi : ℝ) ≤ 1 := by exact_mod_cast hhi
  have mlo : ((tauQ ylo : ℚ) : ℝ) ≤ 2 * y / (1 + y ^ 2) := by
    have := tau_mono hlo' hy1 (hy2.trans hhi')
    simpa [tauQ] using this
  have mhi : 2 * y / (1 + y ^ 2) ≤ ((tauQ yhi : ℚ) : ℝ) := by
    have := tau_mono (hlo'.trans hy1) hy2 hhi'
    simpa [tauQ] using this
  rcases hcase with (hc | hc) | ⟨⟨hp, hq⟩, hl⟩
  · exfalso
    have : ((tauQ yhi : ℚ) : ℝ) < ((kq 0 : ℚ) : ℝ) := Rat.cast_lt.mpr hc
    rw [← kt_eq] at this
    linarith
  · exfalso
    have : ((kq 865 : ℚ) : ℝ) < ((tauQ ylo : ℚ) : ℝ) := Rat.cast_lt.mpr hc
    rw [← kt_eq] at this
    linarith
  · apply lineChk_sound hl
    · rcases hp with hp | hp
      · exact (rc hp).trans mlo
      · have h0' : ((kq 0 : ℚ) : ℝ) ≤ 2 * y / (1 + y ^ 2) := by rw [← kt_eq]; exact h0
        exact (rc hp).trans h0'
    · rcases hq with hq | hq
      · exact mhi.trans (rc hq)
      · have h865' : 2 * y / (1 + y ^ 2) ≤ ((kq 865 : ℚ) : ℝ) := by rw [← kt_eq]; exact h865
        exact h865'.trans (rc hq)

end CatalanMeasure.GenD.Signed.RouteI.ChordLine
