module

public import CatalanMeasure.GenD.Signed.RouteI.IntervalNodes
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.SpecialFunctions.Arcosh

@[expose] public section
set_option Elab.async false

/-!
# Route I `ChordTable`: concavity of `L` and the through-table bound (GP §7.1, Lemma 7.1, Cor 7.2,
Lemma 7.3; ledger G13, G14)

Everything is generic: the interval list `lo hi : ι → ℝ`, the knot list `k₀ < … < k_K`, the knot
values `v_i`, the constant `C₀`, the case field and the cap `S(λ)` are parameters.  The frozen
table (866 knots, `C₀ = 33.052`) is data of `ChordTableData`.

* `concaveOn_arcosh`, `concaveOn_chordL` (Lemma 7.1): on a convex set `J` such that every interval
  `[lo_c, hi_c]` contains `J`, or `J` lies on one side of it, `t ↦ L(t) = ivlL lo hi t` is concave.
  A segment between consecutive knots is such a set when the knots include every `lo_c`, `hi_c`
  (`SegOK`, the exact check `knotOK`).
* `neg_L_le_pwl` (Corollary 7.2): `-L(t) ≤ C₀ + δ̂(t)` on the hull of the knots, for the piecewise
  linear `δ̂ = pwl K k v` through values `v_i ≥ -L(k_i) - C₀`.
* `caseField_le`, `first_case_cap`, `Sfun_convex` (Lemma 7.3): `λ c(x) + δ̂(t(x))/n₀ ≤ S(λ)` with
  `S` a maximum of affine functions of `λ`, hence convex in `λ`.
-/

namespace CatalanMeasure.GenD.Signed.RouteI.ChordTable

open CatalanMeasure.GenD.Signed.RouteI CatalanMeasure.GenD.Analytic CatalanMeasure.Parametric Set Finset
open OAI.InternalCatalan
open scoped BigOperators

noncomputable section

/-! ### `arcosh` is concave on `[1, ∞)` -/

theorem concaveOn_arcosh : ConcaveOn ℝ (Ici (1 : ℝ)) Real.arcosh := by
  refine AntitoneOn.concaveOn_of_deriv (convex_Ici 1) Real.continuousOn_arcosh ?_ ?_
  · rw [interior_Ici]
    exact Real.differentiableOn_arcosh
  · rw [interior_Ici]
    intro x hx y hy hxy
    have hx1 : (1 : ℝ) < x := hx
    have hxy' : x ≤ y := hxy
    rw [(Real.hasDerivAt_arcosh hx).deriv, (Real.hasDerivAt_arcosh hy).deriv]
    have h0 : 0 < Real.sqrt (x ^ 2 - 1) := Real.sqrt_pos.mpr (by nlinarith)
    exact inv_anti₀ h0 (Real.sqrt_le_sqrt (by nlinarith))

/-! ### The Green function of an interval at a real point -/

/-- The affine coordinate of `[a, b]` at a real `t`. -/
def lcoord (a b t : ℝ) : ℝ := (2 * t - a - b) / (b - a)

theorem lcoord_affine {a b : ℝ} (hab : a < b) {x y u v : ℝ} (huv : u + v = 1) :
    lcoord a b (u * x + v * y) = u * lcoord a b x + v * lcoord a b y := by
  have hne : b - a ≠ 0 := (sub_pos.mpr hab).ne'
  have hv : v = 1 - u := by linarith
  subst hv
  unfold lcoord
  field_simp
  ring

theorem ivlGreen_real {a b : ℝ} (hab : a < b) (t : ℝ) :
    ivlGreen a b (t : ℂ) = Real.arcosh (max 1 |lcoord a b t|) := by
  have hc : ivlCoord a b (t : ℂ) = ((lcoord a b t : ℝ) : ℂ) := by
    unfold ivlCoord lcoord
    push_cast
    ring
  unfold ivlGreen
  rw [hc]
  by_cases h : |lcoord a b t| ≤ 1
  · rw [ellipseLog_ofReal_of_abs_le_one h, max_eq_left h]
    exact Real.arcosh_zero.symm
  · push_neg at h
    unfold ellipseLog
    rw [ellipseH_ofReal_of_one_le_abs h.le, max_eq_right h.le]

/-- A set `J` is `SegOK` for the interval `[a, b]` if it lies inside, to the left or to the right. -/
def SegOK (a b : ℝ) (J : Set ℝ) : Prop := J ⊆ Iic a ∨ J ⊆ Ici b ∨ J ⊆ Icc a b

theorem concaveOn_green {a b : ℝ} (hab : a < b) {J : Set ℝ} (hJ : Convex ℝ J) (hS : SegOK a b J) :
    ConcaveOn ℝ J (fun t : ℝ => ivlGreen a b (t : ℂ)) := by
  have hne : 0 < b - a := sub_pos.mpr hab
  rcases hS with h | h | h
  · -- left of the interval: `lcoord ≤ -1`, `G = arcosh (-lcoord)`
    have hl : ∀ t ∈ J, lcoord a b t ≤ -1 := fun t ht => by
      have := h ht
      unfold lcoord
      rw [div_le_iff₀ hne]
      have : t ≤ a := this
      linarith
    refine ⟨hJ, fun x hx y hy u v hu hv huv => ?_⟩
    have hx1 : (1 : ℝ) ≤ -lcoord a b x := by linarith [hl x hx]
    have hy1 : (1 : ℝ) ≤ -lcoord a b y := by linarith [hl y hy]
    have hxy : u * x + v * y ∈ J := hJ hx hy hu hv huv
    have hxy1 : lcoord a b (u * x + v * y) ≤ -1 := hl _ hxy
    have key := concaveOn_arcosh.2 (show -lcoord a b x ∈ Ici (1 : ℝ) from hx1)
      (show -lcoord a b y ∈ Ici (1 : ℝ) from hy1) hu hv huv
    have ea : lcoord a b (u * x + v * y) = u * lcoord a b x + v * lcoord a b y :=
      lcoord_affine hab huv
    have e1 : ∀ z ∈ J, ivlGreen a b (z : ℂ) = Real.arcosh (-lcoord a b z) := fun z hz => by
      rw [ivlGreen_real hab, abs_of_nonpos (by linarith [hl z hz]),
        max_eq_right (by linarith [hl z hz])]
    show u • ivlGreen a b (x : ℂ) + v • ivlGreen a b (y : ℂ) ≤
      ivlGreen a b ((u * x + v * y : ℝ) : ℂ)
    rw [e1 x hx, e1 y hy]
    have := e1 (u * x + v * y) hxy
    simp only [smul_eq_mul] at key ⊢
    rw [show ((u * x + v * y : ℝ) : ℂ) = ((u * x + v * y : ℝ) : ℂ) from rfl, this, ea]
    calc u * Real.arcosh (-lcoord a b x) + v * Real.arcosh (-lcoord a b y)
        ≤ Real.arcosh (u * -lcoord a b x + v * -lcoord a b y) := key
      _ = _ := by congr 1; ring
  · -- right of the interval: `lcoord ≥ 1`, `G = arcosh (lcoord)`
    have hl : ∀ t ∈ J, 1 ≤ lcoord a b t := fun t ht => by
      have := h ht
      unfold lcoord
      rw [le_div_iff₀ hne]
      have : b ≤ t := this
      linarith
    refine ⟨hJ, fun x hx y hy u v hu hv huv => ?_⟩
    have hxy : u * x + v * y ∈ J := hJ hx hy hu hv huv
    have key := concaveOn_arcosh.2 (show lcoord a b x ∈ Ici (1 : ℝ) from hl x hx)
      (show lcoord a b y ∈ Ici (1 : ℝ) from hl y hy) hu hv huv
    have ea : lcoord a b (u * x + v * y) = u * lcoord a b x + v * lcoord a b y :=
      lcoord_affine hab huv
    have e1 : ∀ z ∈ J, ivlGreen a b (z : ℂ) = Real.arcosh (lcoord a b z) := fun z hz => by
      rw [ivlGreen_real hab, abs_of_nonneg (by linarith [hl z hz]),
        max_eq_right (by linarith [hl z hz])]
    show u • ivlGreen a b (x : ℂ) + v • ivlGreen a b (y : ℂ) ≤
      ivlGreen a b ((u * x + v * y : ℝ) : ℂ)
    rw [e1 x hx, e1 y hy, e1 _ hxy, ea]
    simp only [smul_eq_mul] at key ⊢
    exact key
  · -- inside: `G = 0`
    have hl : ∀ t ∈ J, ivlGreen a b (t : ℂ) = 0 := fun t ht => by
      have ht' := h ht
      have h1 : |lcoord a b t| ≤ 1 := by
        unfold lcoord
        rw [abs_div, abs_of_pos hne, div_le_one hne, abs_le]
        constructor <;> linarith [ht'.1, ht'.2]
      rw [ivlGreen_real hab, max_eq_left h1]
      exact Real.arcosh_zero
    refine ⟨hJ, fun x hx y hy u v hu hv huv => ?_⟩
    have hxy : u * x + v * y ∈ J := hJ hx hy hu hv huv
    show u • ivlGreen a b (x : ℂ) + v • ivlGreen a b (y : ℂ) ≤
      ivlGreen a b ((u * x + v * y : ℝ) : ℂ)
    rw [hl x hx, hl y hy, hl _ hxy]
    simp

/-! ### Lemma 7.1: concavity of `L` -/

/-- The real restriction of the interval potential. -/
def chordL {ι : Type*} [Fintype ι] (lo hi : ι → ℝ) (t : ℝ) : ℝ := ivlL lo hi (t : ℂ)

theorem concaveOn_finset_sum {J : Set ℝ} (hJ : Convex ℝ J) {ι : Type*} (s : Finset ι)
    (f : ι → ℝ → ℝ) (hf : ∀ c ∈ s, ConcaveOn ℝ J (f c)) :
    ConcaveOn ℝ J (fun t => ∑ c ∈ s, f c t) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using concaveOn_const (0 : ℝ) hJ
  | insert a s ha ih =>
    have h1 := hf a (Finset.mem_insert_self a s)
    have h2 := ih (fun c hc => hf c (Finset.mem_insert_of_mem hc))
    refine (h1.add h2).congr (fun t _ => ?_)
    simp [Finset.sum_insert ha]

/-- **GP Lemma 7.1.** `L` is concave on every convex set `J` that is `SegOK` for every interval. -/
theorem concaveOn_chordL {ι : Type*} [Fintype ι] (lo hi : ι → ℝ) (hlt : ∀ c, lo c < hi c)
    {J : Set ℝ} (hJ : Convex ℝ J) (hS : ∀ c, SegOK (lo c) (hi c) J) :
    ConcaveOn ℝ J (chordL lo hi) := by
  have hsum := concaveOn_finset_sum hJ (Finset.univ : Finset ι)
    (fun c t => ivlGreen (lo c) (hi c) (t : ℂ)) (fun c _ => concaveOn_green (hlt c) hJ (hS c))
  have hc : ConcaveOn ℝ J (fun t => ∑ c, (ivlGreen (lo c) (hi c) (t : ℂ) +
      Real.log ((hi c - lo c) / 4))) := by
    have := hsum.add (concaveOn_const (∑ c : ι, Real.log ((hi c - lo c) / 4)) hJ)
    refine this.congr (fun t _ => ?_)
    simp [Finset.sum_add_distrib]
  have := hc.smul (show (0 : ℝ) ≤ 1 / 2 by norm_num)
  refine this.congr (fun t _ => ?_)
  simp [chordL, ivlL]

/-- The window `G_W(x) := |x| ≤ 1 ∧ t(x) ∈ U` (audit repair R4: `G_W` needs `|x| ≤ 1`), `U` the
hull of the knots on the sides that carry nodes; it replaces `G58`. -/
def GW (U : Set ℝ) (x : ℝ) : Prop := |x| ≤ 1 ∧ realCoordinateInv x ∈ U

/-! ### The knot table and Corollary 7.2 -/

/-- The chord of the knot values `v_i, v_{i+1}` at `k_i, k_{i+1}`, evaluated at `t`. -/
def chordAt (k v : ℕ → ℝ) (i : ℕ) (t : ℝ) : ℝ :=
  ((k (i + 1) - t) * v i + (t - k i) * v (i + 1)) / (k (i + 1) - k i)

/-- The piecewise linear `δ̂` through `(k_i, v_i)`, `i ≤ K`, on the hull `[k₀, k_K]`: on each
segment it is the chord, at a knot all adjacent chords agree. -/
def pwl (K : ℕ) (k v : ℕ → ℝ) (t : ℝ) : ℝ :=
  sSup {r | ∃ i, i < K ∧ t ∈ Icc (k i) (k (i + 1)) ∧ r = chordAt k v i t}

theorem exists_seg {K : ℕ} (hK : 0 < K) {k : ℕ → ℝ} {t : ℝ} (h0 : k 0 ≤ t) (h1 : t ≤ k K) :
    ∃ i, i < K ∧ t ∈ Icc (k i) (k (i + 1)) := by
  classical
  have hex : ∃ j, j < K ∧ t ≤ k (j + 1) := ⟨K - 1, by omega, by
    have : K - 1 + 1 = K := by omega
    rw [this]; exact h1⟩
  refine ⟨Nat.find hex, (Nat.find_spec hex).1, ?_, (Nat.find_spec hex).2⟩
  by_cases hi : Nat.find hex = 0
  · rw [hi]; exact h0
  · obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hi
    have hmin := Nat.find_min hex (show j < Nat.find hex by omega)
    rw [hj]
    push_neg at hmin
    have := hmin (by have := (Nat.find_spec hex).1; omega)
    exact this.le

theorem chordAt_le {k v : ℕ → ℝ} {i : ℕ} (hk : k i < k (i + 1)) {t : ℝ}
    (ht : t ∈ Icc (k i) (k (i + 1))) : chordAt k v i t ≤ max (v i) (v (i + 1)) := by
  have hd : 0 < k (i + 1) - k i := sub_pos.mpr hk
  unfold chordAt
  rw [div_le_iff₀ hd]
  have h1 : 0 ≤ k (i + 1) - t := sub_nonneg.mpr ht.2
  have h2 : 0 ≤ t - k i := sub_nonneg.mpr ht.1
  have a1 := le_max_left (v i) (v (i + 1))
  have a2 := le_max_right (v i) (v (i + 1))
  nlinarith [mul_le_mul_of_nonneg_left a1 h1, mul_le_mul_of_nonneg_left a2 h2]

/-- Concavity gives the chord below `L`. -/
theorem chord_le_of_concave {L : ℝ → ℝ} {a b : ℝ} (hab : a < b) (hc : ConcaveOn ℝ (Icc a b) L)
    {t : ℝ} (ht : t ∈ Icc a b) :
    ((b - t) * L a + (t - a) * L b) / (b - a) ≤ L t := by
  have hd : 0 < b - a := sub_pos.mpr hab
  have hu : 0 ≤ (b - t) / (b - a) := div_nonneg (sub_nonneg.mpr ht.2) hd.le
  have hv : 0 ≤ (t - a) / (b - a) := div_nonneg (sub_nonneg.mpr ht.1) hd.le
  have huv : (b - t) / (b - a) + (t - a) / (b - a) = 1 := by field_simp; ring
  have key := hc.2 (show a ∈ Icc a b from ⟨le_rfl, hab.le⟩) (show b ∈ Icc a b from ⟨hab.le, le_rfl⟩)
    hu hv huv
  have e : (b - t) / (b - a) * a + (t - a) / (b - a) * b = t := by field_simp; ring
  simp only [smul_eq_mul, e] at key
  have e2 : ((b - t) * L a + (t - a) * L b) / (b - a) =
      (b - t) / (b - a) * L a + (t - a) / (b - a) * L b := by ring
  rw [e2]
  exact key

/-- **GP Corollary 7.2.**  `-L(t) ≤ C₀ + δ̂(t)` on the hull of the knots, for values
`v_i ≥ -L(k_i) - C₀` and `L` concave on every segment. -/
theorem neg_L_le_pwl {L : ℝ → ℝ} {C₀ : ℝ} {K : ℕ} (hK : 0 < K) {k v : ℕ → ℝ}
    (hk : ∀ i, i < K → k i < k (i + 1))
    (hconc : ∀ i, i < K → ConcaveOn ℝ (Icc (k i) (k (i + 1))) L)
    (hv : ∀ i, i ≤ K → -L (k i) - C₀ ≤ v i) {t : ℝ} (h0 : k 0 ≤ t) (h1 : t ≤ k K) :
    -L t ≤ C₀ + pwl K k v t := by
  obtain ⟨i, hi, ht⟩ := exists_seg hK h0 h1
  have hchord := chord_le_of_concave (hk i hi) (hconc i hi) ht
  have hd : 0 < k (i + 1) - k i := sub_pos.mpr (hk i hi)
  have h1' : 0 ≤ k (i + 1) - t := sub_nonneg.mpr ht.2
  have h2' : 0 ≤ t - k i := sub_nonneg.mpr ht.1
  have hva := hv i hi.le
  have hvb := hv (i + 1) (by omega)
  have hchv : -(((k (i + 1) - t) * L (k i) + (t - k i) * L (k (i + 1))) / (k (i + 1) - k i)) - C₀ ≤
      chordAt k v i t := by
    unfold chordAt
    rw [← sub_nonneg]
    have e : ((k (i + 1) - t) * v i + (t - k i) * v (i + 1)) / (k (i + 1) - k i) -
        (-(((k (i + 1) - t) * L (k i) + (t - k i) * L (k (i + 1))) / (k (i + 1) - k i)) - C₀) =
        ((k (i + 1) - t) * (v i + L (k i) + C₀) + (t - k i) * (v (i + 1) + L (k (i + 1)) + C₀)) /
          (k (i + 1) - k i) := by
      field_simp
      ring
    rw [e]
    apply div_nonneg _ hd.le
    have := mul_nonneg h1' (show 0 ≤ v i + L (k i) + C₀ by linarith)
    have := mul_nonneg h2' (show 0 ≤ v (i + 1) + L (k (i + 1)) + C₀ by linarith)
    linarith
  have hmem : chordAt k v i t ∈ {r | ∃ i, i < K ∧ t ∈ Icc (k i) (k (i + 1)) ∧
      r = chordAt k v i t} := ⟨i, hi, ht, rfl⟩
  have hbdd : BddAbove {r | ∃ i, i < K ∧ t ∈ Icc (k i) (k (i + 1)) ∧ r = chordAt k v i t} := by
    refine ⟨(Finset.range K).sup' ⟨0, Finset.mem_range.mpr hK⟩ (fun j => chordAt k v j t), ?_⟩
    rintro r ⟨j, hj, -, rfl⟩
    exact Finset.le_sup' (fun j => chordAt k v j t) (Finset.mem_range.mpr hj)
  have hle := le_csSup hbdd hmem
  unfold pwl
  have : -L t ≤ -(((k (i + 1) - t) * L (k i) + (t - k i) * L (k (i + 1))) / (k (i + 1) - k i)) := by
    linarith
  linarith

theorem k_lt {K : ℕ} {k : ℕ → ℝ} (hk : ∀ i, i < K → k i < k (i + 1)) :
    ∀ i j, i < j → j ≤ K → k i < k j := by
  intro i j hij
  induction j, hij using Nat.le_induction with
  | base => intro h; exact hk i (by omega)
  | succ j hij ih =>
    intro h
    exact (ih (by omega)).trans (hk j (by omega))

/-- On a segment `δ̂` is at most the larger knot value (strictly increasing knots). -/
theorem pwl_le_max {K : ℕ} {k v : ℕ → ℝ} (hk : ∀ i, i < K → k i < k (i + 1)) {i : ℕ} (hi : i < K)
    {t : ℝ} (ht : t ∈ Icc (k i) (k (i + 1))) : pwl K k v t ≤ max (v i) (v (i + 1)) := by
  unfold pwl
  refine csSup_le ⟨chordAt k v i t, i, hi, ht, rfl⟩ ?_
  rintro r ⟨j, hj, hjt, rfl⟩
  rcases lt_trichotomy j i with hji | hji | hji
  · -- `j < i`: `t = k i = k (j+1)`
    have h1 : k (j + 1) ≤ k i := by
      rcases Nat.lt_or_ge (j + 1) i with h | h
      · exact (k_lt hk _ _ h (by omega)).le
      · have : j + 1 = i := by omega
        rw [this]
    have h2 : t = k i := le_antisymm (by linarith [hjt.2]) ht.1
    have h3 : j + 1 = i := by
      by_contra hne
      have : k (j + 1) < k i := k_lt hk _ _ (by omega) (by omega)
      linarith [hjt.2]
    have : chordAt k v j t = v i := by
      unfold chordAt
      have hd : k (j + 1) - k j ≠ 0 := (sub_pos.mpr (hk j hj)).ne'
      rw [h2, ← h3]
      field_simp
      ring
    rw [this]
    exact le_max_left _ _
  · subst hji
    exact chordAt_le (hk _ hj) hjt
  · have h2 : t = k (i + 1) := le_antisymm ht.2 (by
      have : k (i + 1) ≤ k j := by
        rcases Nat.lt_or_ge (i + 1) j with h | h
        · exact (k_lt hk _ _ h (by omega)).le
        · have : j = i + 1 := by omega
          rw [this]
      linarith [hjt.1])
    have h3 : j = i + 1 := by
      by_contra hne
      have : k (i + 1) < k j := k_lt hk _ _ (by omega) (by omega)
      linarith [hjt.1]
    have : chordAt k v j t = v j := by
      unfold chordAt
      have hd : k (j + 1) - k j ≠ 0 := (sub_pos.mpr (hk j hj)).ne'
      rw [h2, ← h3]
      field_simp
      ring
    rw [this, h3]
    exact le_max_right _ _

/-! ### Lemma 7.3: the first-case cap through the table -/

/-- The first-case field `c(x) = 2 g₀/n₀ - 2x²/(1 + x²)` in terms of `t = 2x/(1 + x²)`. -/
theorem caseField_eq {g n x : ℝ} (hx : |x| ≤ 1) :
    g - 2 * x ^ 2 / (1 + x ^ 2) = g - 1 + Real.sqrt (1 - (2 * x / (1 + x ^ 2)) ^ 2) := by
  have h1 : 0 < 1 + x ^ 2 := by positivity
  have hsq : 1 - (2 * x / (1 + x ^ 2)) ^ 2 = ((1 - x ^ 2) / (1 + x ^ 2)) ^ 2 := by
    field_simp
    ring
  have hx2 : x ^ 2 ≤ 1 := by
    have := abs_le.mp hx
    nlinarith
  rw [hsq, Real.sqrt_sq (div_nonneg (by linarith) h1.le)]
  field_simp
  ring

/-- Monotonicity of the case field in `|t|`: `c(x) ≤ g - 1 + √(1 - t*²)` when `|t| ≥ t*`. -/
theorem caseField_le {g x ts : ℝ} (hx : |x| ≤ 1) (hts : 0 ≤ ts)
    (h : ts ≤ |2 * x / (1 + x ^ 2)|) :
    g - 2 * x ^ 2 / (1 + x ^ 2) ≤ g - 1 + Real.sqrt (1 - ts ^ 2) := by
  rw [caseField_eq (n := 0) hx]
  have : Real.sqrt (1 - (2 * x / (1 + x ^ 2)) ^ 2) ≤ Real.sqrt (1 - ts ^ 2) := by
    apply Real.sqrt_le_sqrt
    have : ts ^ 2 ≤ (2 * x / (1 + x ^ 2)) ^ 2 := by
      rw [← sq_abs (2 * x / (1 + x ^ 2))]
      exact pow_le_pow_left₀ hts h 2
    linarith
  linarith

/-- **GP Lemma 7.3 (segment form).**  On a segment with `t = 2x/(1+x²) ∈ [u, w]`, `u, w` of the
same sign (`0 ∉ (u, w)`), `λ ≥ 0`: `λ c(x) + δ̂(t)/n₀ ≤ λ (g - 1 + √(1 - t*²)) + m/n₀`
where `t* = min(|u|, |w|)` and `m ≥ δ̂(t)` on the segment. -/
theorem first_case_cap {g lam n₀ m ts u w x δt : ℝ} (hx : |x| ≤ 1) (hlam : 0 ≤ lam)
    (hn : 0 < n₀) (hts : 0 ≤ ts) (hu : ts ≤ |u|) (hw : ts ≤ |w|)
    (hsame : 0 ≤ u * w) (hxt : 2 * x / (1 + x ^ 2) ∈ Icc u w) (hδ : δt ≤ m) :
    lam * (g - 2 * x ^ 2 / (1 + x ^ 2)) + δt / n₀ ≤ lam * (g - 1 + Real.sqrt (1 - ts ^ 2)) + m / n₀ := by
  have hT : ts ≤ |2 * x / (1 + x ^ 2)| := by
    obtain ⟨h1, h2⟩ := hxt
    by_cases hu0 : 0 ≤ u
    · have h0 : 0 ≤ 2 * x / (1 + x ^ 2) := hu0.trans h1
      rw [abs_of_nonneg h0]
      rw [abs_of_nonneg hu0] at hu
      linarith
    · push_neg at hu0
      have hw0 : w ≤ 0 := by
        by_contra hw
        push_neg at hw
        nlinarith
      have h0 : 2 * x / (1 + x ^ 2) ≤ 0 := h2.trans hw0
      rw [abs_of_nonpos h0]
      rw [abs_of_nonpos hw0] at hw
      linarith
  have := caseField_le (g := g) hx hts hT
  have h3 : lam * (g - 2 * x ^ 2 / (1 + x ^ 2)) ≤ lam * (g - 1 + Real.sqrt (1 - ts ^ 2)) :=
    mul_le_mul_of_nonneg_left this hlam
  have h4 : δt / n₀ ≤ m / n₀ := div_le_div_of_nonneg_right hδ hn.le
  linarith

/-- The cap `S(λ) = max_i (A_i λ + B_i)` is convex in `λ`: along a chord of `λ` it lies below the
chord of its endpoint values. -/
theorem Sfun_convex {ι : Type*} (I : Finset ι) (hI : I.Nonempty) (A B : ι → ℝ) {l0 l1 τ : ℝ}
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) :
    I.sup' hI (fun i => A i * ((1 - τ) * l0 + τ * l1) + B i) ≤
      (1 - τ) * I.sup' hI (fun i => A i * l0 + B i) + τ * I.sup' hI (fun i => A i * l1 + B i) := by
  refine Finset.sup'_le _ _ (fun i hi => ?_)
  have h0 := Finset.le_sup' (fun i => A i * l0 + B i) hi
  have h1 := Finset.le_sup' (fun i => A i * l1 + B i) hi
  nlinarith [mul_nonneg hτ0 (sub_nonneg.mpr h1), mul_nonneg (sub_nonneg.mpr hτ1) (sub_nonneg.mpr h0)]

end

end CatalanMeasure.GenD.Signed.RouteI.ChordTable

#print axioms CatalanMeasure.GenD.Signed.RouteI.ChordTable.concaveOn_arcosh
#print axioms CatalanMeasure.GenD.Signed.RouteI.ChordTable.concaveOn_chordL
#print axioms CatalanMeasure.GenD.Signed.RouteI.ChordTable.neg_L_le_pwl
#print axioms CatalanMeasure.GenD.Signed.RouteI.ChordTable.pwl_le_max
#print axioms CatalanMeasure.GenD.Signed.RouteI.ChordTable.first_case_cap
#print axioms CatalanMeasure.GenD.Signed.RouteI.ChordTable.Sfun_convex
