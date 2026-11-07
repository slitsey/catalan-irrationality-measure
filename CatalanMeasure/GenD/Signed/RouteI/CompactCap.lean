module

public import CatalanMeasure.GenD.Signed.RouteI.CompactSource
public import CatalanMeasure.GenD.Signed.ChebSquare
public import CatalanMeasure.GenD.Signed.AnalyticZero

@[expose] public section
set_option Elab.async false

/-!
# Route I `CompactCap`: generic consumers of the C4 compact caps (data-free)

Plan row C4, theorem side. For an admissible `CapSource S` and truncation `t`:

* `ordCap_of_square`: `OrdCap t σ d G cap` on `ordDom σ` (`σ = pos`: `[98749/10^6, 1]`, the field
  carries `R900 + Eref900`; `σ = neg`: `[19501/10^5, 1]` at `x = -s`, field carries the radial
  mirror), from the source bound `hf : field <= chebSum p D (affine a s) + eps` and the exact
  integer `SquareIdentity` (built X1, `Signed/ChebSquare`).
* `nearCap_of_square`: `NearCap t (cap - m)` on `(0,1)` from the same on `[1/10,1]` and the zero
  geometry of `CompactSource` on `(0,1/10]` (fixed tail retained).
* quantitative margin `margin r D = (r_0 - l1 tail)/D` (the strict-cap conclusion of X1 is
  strengthened to `F <= cap - margin`), and the scalar finite-N corrections (`N >= 3` on
  `[1/10,1]`, every `N >= 1` on `(0,1/10]`) that keep the cap `-9783/10000` up to `log 2/(58N)`.
* exact-field caps from finite-surrogate caps via `Dominates` (`CompactSource`).

The source-to-polynomial bounds `hf`, the source-to-trial relation `H <= F` and the numerical
instance (`p q s r D cap eps`) are hypotheses supplied by later steps.
-/

namespace CatalanMeasure.GenD.Signed.RouteI.CompactCap

open CatalanMeasure.GenD.Signed.RouteI.CapFields
open CatalanMeasure.GenD.Signed.RouteI.CapFields.CapSource
open CatalanMeasure.GenD.Signed.RouteI.CompactSource
open CatalanMeasure.Signed.ChebSquare
open Real Set

noncomputable section

/-! ### Affine normalisation of `[a,1]` onto `[-1,1]` -/

def affine (a u : ℝ) : ℝ := (u - (a + 1) / 2) / ((1 - a) / 2)

theorem affine_mem {a u : ℝ} (ha : a < 1) (h1 : a ≤ u) (h2 : u ≤ 1) :
    affine a u ∈ Icc (-1 : ℝ) 1 := by
  have h : 0 < (1 - a) / 2 := by linarith
  unfold affine
  constructor
  · rw [le_div_iff₀ h]; linarith
  · rw [div_le_iff₀ h]; linarith

/-! ### Quantitative form of the weighted Chebyshev square -/

/-- The remainder margin `(r_0 - l1 tail)/D`. -/
def margin (r : List ℤ) (D : ℕ) : ℝ :=
  (((r.headD 0 : ℤ) : ℝ) - ((l1 r.tail : ℤ) : ℝ)) / D

theorem margin_pos {r : List ℤ} (D : ℕ) (hD : 0 < D) (hm : l1 r.tail < r.headD 0) :
    0 < margin r D := by
  unfold margin
  have : ((l1 r.tail : ℤ) : ℝ) < ((r.headD 0 : ℤ) : ℝ) := by exact_mod_cast hm
  exact div_pos (by linarith) (by exact_mod_cast hD)

theorem rawSum_ge (r : List ℤ) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    ((r.headD 0 : ℤ) : ℝ) - ((l1 r.tail : ℤ) : ℝ) ≤ rawSum r 0 x := by
  cases r with
  | nil => simp [l1]
  | cons a tail =>
    have ht := abs_rawSum_le tail 1 hx
    have hlo := (abs_le.mp ht).1
    simp only [rawSum_cons, basis_zero, mul_one, List.headD_cons, List.tail_cons]
    linarith

theorem square_margin (p q s r : List ℤ) (D : ℕ) (hD : 0 < D) (cap ε : ℚ)
    (hid : SquareIdentity p q s r D cap ε) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    chebSum p D x + ε ≤ cap - margin r D := by
  have hid' := hid.eval hD x
  have hd : (0 : ℝ) < D := by exact_mod_cast hD
  have h1 : margin r D ≤ chebSum r D x :=
    div_le_div_of_nonneg_right (rawSum_ge r hx) hd.le
  have hw : 0 ≤ 1 - x ^ 2 := by
    have := mul_nonneg (sub_nonneg.mpr hx.2) (sub_nonneg.mpr hx.1)
    nlinarith
  have hq := sq_nonneg (chebSum q D x)
  have hs := mul_nonneg hw (sq_nonneg (chebSum s D x))
  linarith

/-! ### Ordinary compact caps -/

/-- Left endpoint of the ordinary domain. -/
def ordLo : Sign → ℝ
  | Sign.neg => 19501 / 100000
  | Sign.pos => 98749 / 1000000

theorem ordDom_eq (σ : Sign) : ordDom σ = Icc (ordLo σ) 1 := by cases σ <;> rfl

theorem ordLo_lt_one (σ : Sign) : ordLo σ < 1 := by cases σ <;> norm_num [ordLo]

/-- Ordinary compact consumer with margin. -/
theorem ord_le_margin (S : CapSource) (t : Trunc) (σ : Sign) (p q s r : List ℤ) (D : ℕ)
    (hD : 0 < D) (cap ε : ℚ) (hid : SquareIdentity p q s r D cap ε)
    (hf : ∀ u ∈ ordDom σ, S.ordField t σ ((if σ = Sign.neg then -1 else 1) * u) ≤
      chebSum p D (affine (ordLo σ) u) + ε) :
    ∀ u ∈ ordDom σ, S.ordField t σ ((if σ = Sign.neg then -1 else 1) * u) ≤
      (cap : ℝ) - margin r D := by
  intro u hu
  rw [ordDom_eq] at hu
  exact (hf u (by rwa [ordDom_eq])).trans
    (square_margin p q s r D hD cap ε hid (affine_mem (ordLo_lt_one σ) hu.1 hu.2))

/-- `OrdCap t σ d G c` (any sign) from one square certificate at `cap` and a constant bound
`d ≤ c - cap` of the node correction on the window `G` (GP Lemma 7.5 with `d` bounded on the whole
band; the cell form is `ordCap_of_cells`). -/
theorem ordCap_of_square (S : CapSource) (t : Trunc) (σ : Sign) (p q s r : List ℤ) (D : ℕ)
    (hD : 0 < D) (cap ε : ℚ) (hid : SquareIdentity p q s r D cap ε)
    (hm : l1 r.tail < r.headD 0)
    (hf : ∀ u ∈ ordDom σ, S.ordField t σ ((if σ = Sign.neg then -1 else 1) * u) ≤
      chebSum p D (affine (ordLo σ) u) + ε)
    (d : ℝ → ℝ) (G : ℝ → Prop) (c : ℝ)
    (hd : ∀ u ∈ ordDom σ, G ((if σ = Sign.neg then -1 else 1) * u) →
      d ((if σ = Sign.neg then -1 else 1) * u) ≤ c - cap) :
    S.OrdCap t σ d G c := by
  intro u hu hG
  have := ord_le_margin S t σ p q s r D hD cap ε hid hf u hu
  have := margin_pos (r := r) D hD hm
  have := hd u hu hG
  linarith

/-- **GP Lemma 7.5, consumer.**  `OrdCap t σ d G c` from a finite cover of the band by cells on which
the node correction is bounded by a function `dseg i` (the affine chord of `δ̂/58`) with
`ordField + dseg i ≤ c`: the cell inequalities are the finite data. -/
theorem ordCap_of_cells (S : CapSource) (t : Trunc) (σ : Sign) (d : ℝ → ℝ) (G : ℝ → Prop) (c : ℝ)
    {ι : Type*} (cells : Finset ι) (lo hi : ι → ℝ) (dseg : ι → ℝ → ℝ)
    (hcov : ∀ u ∈ ordDom σ, G ((if σ = Sign.neg then -1 else 1) * u) →
      ∃ i ∈ cells, u ∈ Icc (lo i) (hi i))
    (hd : ∀ i ∈ cells, ∀ u ∈ Icc (lo i) (hi i), u ∈ ordDom σ →
      G ((if σ = Sign.neg then -1 else 1) * u) →
      d ((if σ = Sign.neg then -1 else 1) * u) ≤ dseg i ((if σ = Sign.neg then -1 else 1) * u))
    (hf : ∀ i ∈ cells, ∀ u ∈ Icc (lo i) (hi i), u ∈ ordDom σ →
      S.ordField t σ ((if σ = Sign.neg then -1 else 1) * u) +
        dseg i ((if σ = Sign.neg then -1 else 1) * u) ≤ c) :
    S.OrdCap t σ d G c := by
  intro u hu hG
  obtain ⟨i, hi, hui⟩ := hcov u hu hG
  have := hd i hi u hui hu hG
  have := hf i hi u hui hu
  linarith

/-- Positive ordinary cap on `[98749/10^6, 1]` (field with `R900 + Eref900`). -/
theorem ordCap_pos_of_square (S : CapSource) (t : Trunc) (p q s r : List ℤ) (D : ℕ)
    (hD : 0 < D) (cap ε : ℚ) (hid : SquareIdentity p q s r D cap ε)
    (hm : l1 r.tail < r.headD 0)
    (hf : ∀ u ∈ Icc (98749 / 1000000 : ℝ) 1, S.ordField t Sign.pos u ≤
      chebSum p D (affine (98749 / 1000000) u) + ε)
    (d : ℝ → ℝ) (G : ℝ → Prop) (c : ℝ)
    (hd : ∀ u ∈ Icc (98749 / 1000000 : ℝ) 1, G u → d u ≤ c - cap) :
    S.OrdCap t Sign.pos d G c :=
  ordCap_of_square S t Sign.pos p q s r D hD cap ε hid hm (by
    intro u hu
    simpa [ordLo] using hf u hu) d G c (by
    intro u hu hG
    simpa [ordDom] using hd u (by simpa [ordDom] using hu) (by simpa using hG))

/-- Negative ordinary cap on `[19501/10^5, 1]` at `x = -u` (radial mirror in the field). -/
theorem ordCap_neg_of_square (S : CapSource) (t : Trunc) (p q s r : List ℤ) (D : ℕ)
    (hD : 0 < D) (cap ε : ℚ) (hid : SquareIdentity p q s r D cap ε)
    (hm : l1 r.tail < r.headD 0)
    (hf : ∀ u ∈ Icc (19501 / 100000 : ℝ) 1, S.ordField t Sign.neg (-u) ≤
      chebSum p D (affine (19501 / 100000) u) + ε)
    (d : ℝ → ℝ) (G : ℝ → Prop) (c : ℝ)
    (hd : ∀ u ∈ Icc (19501 / 100000 : ℝ) 1, G (-u) → d (-u) ≤ c - cap) :
    S.OrdCap t Sign.neg d G c :=
  ordCap_of_square S t Sign.neg p q s r D hD cap ε hid hm (by
    intro u hu
    simpa [ordLo] using hf u hu) d G c (by
    intro u hu hG
    simpa [ordDom] using hd u (by simpa [ordDom] using hu) (by simpa using hG))

/-! ### Near cap -/

theorem NearCap.mono {S : CapSource} {t : Trunc} {d : ℝ → ℝ} {G : ℝ → Prop} {c c' : ℝ}
    (h : S.NearCap t d G c) (hc : c ≤ c') : S.NearCap t d G c' :=
  fun y hy hG => (h y hy hG).trans hc

/-- **GP Lemma 7.5 (near field), consumer:** cells with an affine bound `dseg i` of `d`. -/
theorem nearCap_of_cells (S : CapSource) (t : Trunc) (d : ℝ → ℝ) (G : ℝ → Prop) (c : ℝ)
    {ι : Type*} (cells : Finset ι) (lo hi : ι → ℝ) (dseg : ι → ℝ → ℝ)
    (hcov : ∀ y ∈ Ioo (0 : ℝ) 1, G y → ∃ i ∈ cells, y ∈ Icc (lo i) (hi i))
    (hd : ∀ i ∈ cells, ∀ y ∈ Icc (lo i) (hi i), y ∈ Ioo (0 : ℝ) 1 → G y → d y ≤ dseg i y)
    (hf : ∀ i ∈ cells, ∀ y ∈ Icc (lo i) (hi i), y ∈ Ioo (0 : ℝ) 1 →
      S.nearField t y + dseg i y ≤ c) :
    S.NearCap t d G c := by
  intro y hy hG
  obtain ⟨i, hi, hyi⟩ := hcov y hy hG
  have := hd i hi y hyi hy hG
  have := hf i hi y hyi hy
  linarith

/-- Zero region of the near field, generic in the angular constant `κ ≥ 1/10`. -/
theorem zero_near_gen {y κ : ℝ} (h0 : 0 < y) (h1 : y ≤ 1 / 10) (hκ : 1 / 10 ≤ κ) :
    (24 / 29) * Real.log y + Real.log (1 + y) - κ ≤ -19 / 10 := by
  have := AnalyticZero.zero_near_cap_sharp y h0 h1
  linarith

/-- Near consumer: `[1/10,1]` by the square, `(0,1/10]` by the zero geometry (fixed tail kept).
`m` is any real below the square margin and below `9/10`; `cap >= -9783/10000`. -/
theorem nearCap_of_square (S : CapSource) (hS : S.Admissible) (t : Trunc)
    (hs : S.strength ≤ 1 / 10) (hc : S.curvature ≤ 1 / 10)
    (hM : S.auxMass Sign.pos ≤ 37 / 100) (hE : S.auxTail t Sign.pos ≤ 1 / 100)
    (p q s r : List ℤ) (D : ℕ) (hD : 0 < D) (cap ε : ℚ)
    (hid : SquareIdentity p q s r D cap ε)
    (hf : ∀ y ∈ Icc (1 / 10 : ℝ) 1, S.nearField t y ≤ chebSum p D (affine (1 / 10) y) + ε)
    (m : ℝ) (hm1 : m ≤ margin r D) (hm2 : m ≤ 9 / 10) (hcap : (-9783 / 10000 : ℝ) ≤ cap)
    (hkap : (1 / 10 : ℝ) ≤ kappa Sign.pos)
    (d : ℝ → ℝ) (G : ℝ → Prop) (c : ℝ)
    (hd : ∀ y ∈ Ioo (0 : ℝ) 1, G y → d y ≤ c - ((cap : ℝ) - m)) :
    S.NearCap t d G c := by
  intro y hy hG
  have hdy := hd y hy hG
  by_cases h : y ≤ 1 / 10
  · have g := near_zero_geometry S hS t hs hc hM hy.1 h
    have z := zero_near_gen hy.1 h hkap
    linarith
  · push_neg at h
    have hy' : y ∈ Icc (1 / 10 : ℝ) 1 := ⟨h.le, hy.2.le⟩
    have := square_margin p q s r D hD cap ε hid
      (affine_mem (a := 1 / 10) (by norm_num) hy'.1 hy'.2)
    linarith [hf y hy']

/-! ### Exact fields from finite surrogates -/

theorem ordCap_exact (S : CapSource) (hS : S.Admissible) {K : ℕ} {σ : Sign} {d : ℝ → ℝ}
    {G : ℝ → Prop} {c : ℝ}
    (h : S.OrdCap (Trunc.finite K) σ d G c) : S.OrdCap Trunc.exact σ d G c :=
  fun s hs hG => (add_le_add_left (ord_dominates S hS K σ s hs) _).trans (h s hs hG)

theorem nearCap_exact (S : CapSource) (hS : S.Admissible) {K : ℕ} {d : ℝ → ℝ} {G : ℝ → Prop}
    {c : ℝ} (h : S.NearCap (Trunc.finite K) d G c) : S.NearCap Trunc.exact d G c :=
  fun y hy hG => (add_le_add_left (near_dominates S hS K y hy) _).trans (h y hy hG)

/-! ### Finite-N corrections (scalar, no trial assumed) -/

theorem log_ten_lt_three : Real.log 10 < 3 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num)]
  have h := Real.exp_one_gt_d9
  have e : Real.exp 3 = Real.exp 1 * Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add, ← Real.exp_add]; norm_num
  rw [e]
  nlinarith [Real.exp_pos 1]

theorem log_one_add_sq_le {y : ℝ} (hy : |y| ≤ 1) : Real.log (1 + y ^ 2) ≤ Real.log 2 := by
  apply Real.log_le_log (by positivity)
  have := abs_le.mp hy
  nlinarith

/-- Compact region, every `N >= 3`: `H <= F <= cap - m`, `m >= 1/58`
gives `H + (log(1+y^2) - log y)/(58N) <= cap + log 2/(58N)` on `[1/10,1]`. -/
theorem near_terminal_compact (N : ℕ) (hN : 3 ≤ N) {y H F cap m : ℝ}
    (hy : y ∈ Icc (1 / 10 : ℝ) 1) (hH : H ≤ F) (hF : F ≤ cap - m) (hm : 1 / 58 ≤ m) :
    H + (Real.log (1 + y ^ 2) - Real.log y) / (58 * N) ≤ cap + Real.log 2 / (58 * N) := by
  have hN' : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hpos : (0 : ℝ) < 58 * N := by positivity
  have hly : -Real.log y ≤ 3 := by
    have : Real.log (1 / 10) ≤ Real.log y := Real.log_le_log (by norm_num) hy.1
    rw [one_div, Real.log_inv] at this
    linarith [log_ten_lt_three]
  have hl2 := log_one_add_sq_le (y := y) (by rw [abs_le]; constructor <;> linarith [hy.1, hy.2])
  have h1 : (Real.log (1 + y ^ 2) - Real.log y) / (58 * N) ≤ (Real.log 2 + 3) / (58 * N) :=
    div_le_div_of_nonneg_right (by linarith) hpos.le
  have h2 : (3 : ℝ) / (58 * N) ≤ 1 / 58 := by
    rw [div_le_div_iff₀ hpos (by norm_num)]; nlinarith
  have e : (Real.log 2 + 3) / (58 * N) = Real.log 2 / (58 * N) + 3 / (58 * N) := add_div _ _ _
  linarith

/-- Zero region, every `N >= 1`: from the source geometry for `H`, with the fixed tail `E <= 1/100`. -/
theorem near_terminal_zero (N : ℕ) (hN : 1 ≤ N) {y H E cap κ : ℝ} (hy0 : 0 < y)
    (hy1 : y ≤ 1 / 10) (hκ : 1 / 10 ≤ κ) (hE : E ≤ 1 / 100)
    (hH : H ≤ (24 / 29) * Real.log y + Real.log (1 + y) - κ + E)
    (hcap : (-9783 / 10000 : ℝ) ≤ cap) :
    H + (Real.log (1 + y ^ 2) - Real.log y) / (58 * N) ≤ cap + Real.log 2 / (58 * N) := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hpos : (0 : ℝ) < 58 * N := by positivity
  set u : ℝ := 1 / (58 * N) with hu
  have hu0 : 0 < u := by positivity
  have hu1 : u ≤ 1 / 58 := by
    rw [hu, div_le_div_iff₀ hpos (by norm_num)]; nlinarith
  have e : ∀ a : ℝ, a / (58 * N) = a * u := fun a => by rw [hu]; ring
  rw [e, e]
  have hL : Real.log y ≤ -(23 / 10) := by
    have : Real.log y ≤ Real.log (1 / 10) := Real.log_le_log hy0 hy1
    rw [one_div, Real.log_inv] at this
    linarith [AnalyticZero.log_ten_gt]
  have hp : Real.log (1 + y) ≤ y := by
    have := Real.log_le_sub_one_of_pos (show 0 < 1 + y by linarith)
    linarith
  have hl2 := log_one_add_sq_le (y := y) (by rw [abs_le]; constructor <;> linarith)
  have h3 : Real.log (1 + y ^ 2) * u ≤ Real.log 2 * u := mul_le_mul_of_nonneg_right hl2 hu0.le
  have h4 : Real.log y * (24 / 29 - u) ≤ Real.log y * (47 / 58) := by
    apply mul_le_mul_of_nonpos_left _ (by linarith)
    linarith
  nlinarith

end

end CatalanMeasure.GenD.Signed.RouteI.CompactCap

#print axioms CatalanMeasure.GenD.Signed.RouteI.CompactCap.ordCap_pos_of_square
#print axioms CatalanMeasure.GenD.Signed.RouteI.CompactCap.ordCap_neg_of_square
#print axioms CatalanMeasure.GenD.Signed.RouteI.CompactCap.nearCap_of_square
#print axioms CatalanMeasure.GenD.Signed.RouteI.CompactCap.ordCap_exact
#print axioms CatalanMeasure.GenD.Signed.RouteI.CompactCap.nearCap_exact
#print axioms CatalanMeasure.GenD.Signed.RouteI.CompactCap.near_terminal_compact
#print axioms CatalanMeasure.GenD.Signed.RouteI.CompactCap.near_terminal_zero
