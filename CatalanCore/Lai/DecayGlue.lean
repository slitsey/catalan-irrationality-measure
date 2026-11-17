module

public import CatalanCore.Lai.DecayCert
public import CatalanCore.Zeta5.Potential.SOS
public import CatalanCore.Zeta5.Cells.Cover
public import CatalanMeasure.CellCert.Tower
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

@[expose] public section

/-!
# `CatalanCore.Lai.DecayGlue`: theorem-side glue of the Lai decay data (W2)

* **G-a** `laiC`, `laiC_hpos`, `laiC_zero`, `laiC_eq_q`: the SOS density `c_k = (3/2) a_k / a_0`,
  `a_k = sosCoef hI 8 k` for the nine integers `h_i = 2^24 h`, with `0 ≤ chebF laiC 8` and `c₀ = 3/2`.
* **G-b** `chainOK`, `chainOK_cover`, `cover_pred`, `laiCover_of_chains`, `cosh_lb`: a chain of cells
  (centre, radius) over the three arms and the ray gives `LaiCover`.  The per-cell input is the
  conclusion of `cellA/G/R_sound` (see `laiCover_of_chains` for the exact types).
* **G-d** `supB`, `tower_sup_le`, `Ftow_enc`, `mulTower_le_enc`, `crossCellBound_le`,
  `laiEnergyOK_of_cells`: sup bounds `U_{i,j}` of the cross tower from centre enclosures and the
  order-5 remainder, and the assembly of `LaiEnergyOK`.
-/

open Set Real Finset MeasureTheory
open CatalanCore.Zeta5.Potential CatalanCore.Zeta5.Cells CatalanMeasure.GenD.Signed.TaylorCell
  CatalanCore.Lai CatalanCore.Lai.DecayInstance CatalanCore.Lai.DecayEnergy CatalanCore.Lai.DecayCert
  CatalanCore.Tools.Joukowski CatalanCore.Decay.ComplexTaylor CatalanCore.Decay.WedgeBounds

namespace CatalanCore.Lai.DecayGlue

noncomputable section

/-! ### G-a: the SOS density -/

/-- `2^24 h_i`, the integer coefficients of the nine-term SOS factor of Theorem L′. -/
def hI : ℕ → ℤ
  | 0 => 107224
  | 1 => 76785
  | 2 => 240184
  | 3 => 539459
  | 4 => -565327
  | 5 => 3717555
  | 6 => -9212693
  | 7 => -6236781
  | 8 => 16850383
  | _ => 0

def hRr (j : ℕ) : ℝ := ((hI j : ℤ) : ℝ)

/-- `a_k` over `ℤ`. -/
def aI (k : ℕ) : ℤ :=
  if k = 0 then ∑ j ∈ range 9, hI j ^ 2 else 2 * ∑ j ∈ range (9 - k), hI j * hI (j + k)

theorem sum_hRr : ∑ j ∈ range (8 + 1), hRr j ^ 2 = ((aI 0 : ℤ) : ℝ) := by
  simp only [aI, ite_true, hRr]
  push_cast
  rfl

theorem aI_zero_pos : 0 < aI 0 := by
  simp only [aI, ite_true, Finset.sum_range_succ, Finset.sum_range_zero, hI]
  norm_num

theorem a0R_pos : (0 : ℝ) < ((aI 0 : ℤ) : ℝ) := by exact_mod_cast aI_zero_pos

theorem sosCoef_eq (k : ℕ) : sosCoef hRr 8 k = ((aI k : ℤ) : ℝ) := by
  unfold sosCoef aI
  split_ifs with hk
  · simp only [hRr]; push_cast; rfl
  · simp only [hRr]; push_cast; rfl

/-- The density `c_k = (3/2) a_k / a_0`. -/
def laiC (k : ℕ) : ℝ := (3 / 2 : ℝ) / (∑ j ∈ range (8 + 1), hRr j ^ 2) * sosCoef hRr 8 k

theorem laiC_hpos : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ chebF laiC 8 x := by
  intro x hx
  have hs : (0 : ℝ) ≤ (3 / 2 : ℝ) / (∑ j ∈ range (8 + 1), hRr j ^ 2) := by
    rw [sum_hRr]; exact div_nonneg (by norm_num) a0R_pos.le
  exact chebF_sos_nonneg hRr 8 hs hx

theorem laiC_zero : laiC 0 = 3 / 2 := by
  have := sos_const_eq hRr 8 (3 / 2 : ℝ) (by rw [sum_hRr]; exact a0R_pos.ne')
  exact this

/-- The rational form of the coefficients (for the data side). -/
def laiCq (k : ℕ) : ℚ := (3 / 2 : ℚ) * ((aI k : ℤ) : ℚ) / ((aI 0 : ℤ) : ℚ)

theorem laiC_eq_q (k : ℕ) : laiC k = ((laiCq k : ℚ) : ℝ) := by
  unfold laiC laiCq
  rw [sum_hRr, sosCoef_eq]
  push_cast
  have h1 : ((aI 0 : ℤ) : ℝ) ≠ 0 := a0R_pos.ne'
  field_simp

/-- `LaiDecayData.hpos`, `LaiDecayData.hc0` for `c = laiC`. -/
theorem laiC_data : (∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ chebF laiC 8 x) ∧ laiC 0 = 3 / 2 :=
  ⟨laiC_hpos, laiC_zero⟩

/-! ### G-b: chains of cells -/

/-- Boolean chain test for a list of `(θ, ρ)`: radii `≥ 0`, centres nondecreasing, and consecutive
cells overlap: `(θ' - θ) · kq ≤ ρ + ρ'` (`kq` an upper bound of the scale `s` of the centres `s θ`). -/
def chainOK (kq : ℚ) : List (ℚ × ℚ) → Bool
  | [] => true
  | [p] => decide (0 ≤ p.2)
  | p :: q :: t => decide (0 ≤ p.2 ∧ p.1 ≤ q.1 ∧ (q.1 - p.1) * kq ≤ p.2 + q.2) && chainOK kq (q :: t)

theorem chainOK_nonneg {kq : ℚ} : ∀ {L : List (ℚ × ℚ)}, chainOK kq L = true → ∀ p ∈ L, 0 ≤ p.2
  | [], _, p, hp => by simp at hp
  | [q], h, p, hp => by
      simp only [chainOK, decide_eq_true_eq] at h
      simp only [List.mem_singleton] at hp; subst hp; exact h
  | q :: r :: t, h, p, hp => by
      simp only [chainOK, Bool.and_eq_true, decide_eq_true_eq] at h
      rcases List.mem_cons.1 hp with rfl | hp
      · exact h.1.1
      · exact chainOK_nonneg h.2 p hp

theorem chainOK_chain {kq : ℚ} {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ (kq : ℝ)) :
    ∀ {L : List (ℚ × ℚ)}, chainOK kq L = true →
      Chain (L.map fun p => (s * (p.1 : ℝ), (p.2 : ℝ)))
  | [], _ => trivial
  | [q], _ => trivial
  | p :: q :: t, h => by
      simp only [chainOK, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨h0, h1, h2⟩, h3⟩ := h
      have ih := chainOK_chain hs0 hs h3
      simp only [List.map_cons] at ih ⊢
      refine ⟨?_, ?_, ih⟩
      · exact mul_le_mul_of_nonneg_left (by exact_mod_cast h1) hs0
      · have h1' : (0 : ℝ) ≤ ((q.1 : ℝ) - p.1) := by
          have : (p.1 : ℝ) ≤ q.1 := by exact_mod_cast h1
          linarith
        have e : (q.1 - p.1) * kq ≤ p.2 + q.2 := h2
        have e' : ((q.1 : ℝ) - p.1) * (kq : ℝ) ≤ (p.2 : ℝ) + q.2 := by exact_mod_cast e
        nlinarith [mul_le_mul_of_nonneg_left hs h1']

/-- **Cover of an interval by a chain.** -/
theorem chainOK_cover {kq : ℚ} {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ (kq : ℝ)) (p : ℚ × ℚ)
    (t : List (ℚ × ℚ)) (hok : chainOK kq (p :: t) = true) {lo hi : ℝ}
    (hlo : s * (p.1 : ℝ) - p.2 ≤ lo) (hhi : hi ≤ s * (((p :: t).getLast (by simp)).1 : ℝ) +
      (((p :: t).getLast (by simp)).2 : ℝ)) :
    ∀ z ∈ Icc lo hi, ∃ q ∈ p :: t, |z - s * (q.1 : ℝ)| ≤ (q.2 : ℝ) := by
  intro z hz
  have hnn := chainOK_nonneg hok
  have hch := chainOK_chain hs0 hs hok
  set f : ℚ × ℚ → ℝ × ℝ := fun p => (s * (p.1 : ℝ), (p.2 : ℝ)) with hf
  have hrad : ∀ x ∈ t.map f, 0 ≤ x.2 := by
    intro x hx
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hx
    show (0:ℝ) ≤ (q.2:ℝ)
    exact_mod_cast hnn q (List.mem_cons_of_mem _ hq)
  by_cases hza : z ≤ s * (p.1 : ℝ)
  · exact ⟨p, by simp, by rw [abs_le]; constructor <;> linarith [hz.1]⟩
  · have hza := not_le.1 hza
    by_cases hzb : z ≤ s * (((p :: t).getLast (by simp)).1 : ℝ)
    · have hm : (p :: t).map f = f p :: t.map f := rfl
      have hl : ((f p) :: t.map f).getLast (by simp) = f ((p :: t).getLast (by simp)) := by
        simpa [hm] using List.getLast_map (f := f) (l := p :: t) (by simp)
      have key := chain_cover (t.map f) (f p).1 (f p).2 (show (0:ℝ) ≤ (p.2:ℝ) by exact_mod_cast hnn p (by simp)) hrad
        (by simpa [hf] using hch) z hza.le (by rw [hl]; exact hzb)
      obtain ⟨p', hp', hz'⟩ := key
      rw [← hm] at hp'
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp'
      exact ⟨q, hq, hz'⟩
    · have hzb := not_le.1 hzb
      refine ⟨(p :: t).getLast (by simp), List.getLast_mem _, ?_⟩
      rw [abs_le]; constructor <;> linarith [hz.2]


/-- Pointwise form: if every cell of the chain proves `Q` on its interval, `Q` holds on `[lo, hi]`. -/
theorem cover_pred (Q : ℝ → Prop) {kq : ℚ} {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ (kq : ℝ)) (p : ℚ × ℚ)
    (t : List (ℚ × ℚ)) (hok : chainOK kq (p :: t) = true) {lo hi : ℝ}
    (hlo : s * (p.1 : ℝ) - p.2 ≤ lo) (hhi : hi ≤ s * (((p :: t).getLast (by simp)).1 : ℝ) +
      (((p :: t).getLast (by simp)).2 : ℝ))
    (hcell : ∀ q ∈ p :: t, ∀ x ∈ Icc (s * (q.1 : ℝ) - q.2) (s * (q.1 : ℝ) + q.2), Q x) :
    ∀ z ∈ Icc lo hi, Q z := by
  intro z hz
  obtain ⟨q, hq, hzq⟩ := chainOK_cover hs0 hs p t hok hlo hhi z hz
  exact hcell q hq z (by rw [abs_le] at hzq; constructor <;> linarith [hzq.1, hzq.2])

/-- `1 + w²/2 + w⁴/24 + w⁶/720 + w⁸/40320 ≤ cosh w`. -/
theorem cosh_lb (w : ℝ) : 1 + w ^ 2 / 2 + w ^ 4 / 24 + w ^ 6 / 720 + w ^ 8 / 40320 ≤ Real.cosh w := by
  have h := sum_le_hasSum (Finset.range 5) (fun n _ => by
    have : 0 ≤ w ^ (2 * n) := (even_two_mul n).pow_nonneg w
    positivity) (Real.hasSum_cosh w)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
  norm_num at h
  linarith

theorem cosh_wA : (97 / 93 : ℝ) ≤ Real.cosh (146127 / 500000) := by
  have := cosh_lb (146127 / 500000); norm_num at this ⊢; linarith

theorem cosh_wB : (103 / 93 : ℝ) ≤ Real.cosh (459681 / 1000000) := by
  have := cosh_lb (459681 / 1000000); norm_num at this ⊢; linarith

/-- **`LaiCover` from four chains of cells.**  The cell hypotheses are exactly the conclusions of
`cellA_sound`, `cellG_sound` (`s = -1`, `s = 1`) and `cellR_sound` (with `Wan` unfolded; centres
`π θ`, `θ, ρ : ℚ`, for the arm `A`; `θ, ρ : ℚ` for `w` and `y`).  Endpoint conditions are rational
inequalities (`π < 31416/10^4`). -/
theorem laiCover_of_chains (c : ℕ → ℝ) (N : ℕ) (wA wB : ℝ) (hwA0 : 0 ≤ wA) (hwB0 : 0 ≤ wB)
    (hwA : 97 / 93 ≤ Real.cosh wA) (hwB : 103 / 93 ≤ Real.cosh wB)
    -- A: centres `π θ`, φ ∈ [0, π]
    (pA : ℚ × ℚ) (tA : List (ℚ × ℚ)) (hA : chainOK (31416 / 10000) (pA :: tA) = true)
    (hA0 : 0 ≤ pA.1 ∧ pA.1 * (31416 / 10000) ≤ pA.2)
    (hA1 : ((pA :: tA).getLast (by simp)).1 ≤ 1 ∧
      (1 - ((pA :: tA).getLast (by simp)).1) * (31416 / 10000) ≤ ((pA :: tA).getLast (by simp)).2)
    (hcA : ∀ q ∈ pA :: tA, ∀ x ∈ Icc (Real.pi * (q.1 : ℝ) - q.2) (Real.pi * (q.1 : ℝ) + q.2),
      Wan c N (DecayInstance.laiM + DecayInstance.laiH * ((Real.cos x : ℝ) : ℂ)) ≤ laiEll)
    -- G0: w ∈ [0, wA]
    (pG : ℚ × ℚ) (tG : List (ℚ × ℚ)) (hG : chainOK 1 (pG :: tG) = true)
    (hG0 : (pG.1 : ℝ) - pG.2 ≤ 0)
    (hG1 : wA ≤ (((pG :: tG).getLast (by simp)).1 : ℝ) + (((pG :: tG).getLast (by simp)).2 : ℝ))
    (hcG : ∀ q ∈ pG :: tG, ∀ w ∈ Icc ((q.1 : ℝ) - q.2) ((q.1 : ℝ) + q.2),
      Wan c N (DecayInstance.laiM + DecayInstance.laiH * ((((-1 : ℝ) * Real.cosh w : ℝ)) : ℂ)) ≤ laiEll)
    -- G1: w ∈ [0, wB]
    (pH : ℚ × ℚ) (tH : List (ℚ × ℚ)) (hH : chainOK 1 (pH :: tH) = true)
    (hH0 : (pH.1 : ℝ) - pH.2 ≤ 0)
    (hH1 : wB ≤ (((pH :: tH).getLast (by simp)).1 : ℝ) + (((pH :: tH).getLast (by simp)).2 : ℝ))
    (hcH : ∀ q ∈ pH :: tH, ∀ w ∈ Icc ((q.1 : ℝ) - q.2) ((q.1 : ℝ) + q.2),
      Wan c N (DecayInstance.laiM + DecayInstance.laiH * ((((1 : ℝ) * Real.cosh w : ℝ)) : ℂ)) ≤ laiEll)
    -- R: y ∈ [0, 11/10]
    (pR : ℚ × ℚ) (tR : List (ℚ × ℚ)) (hR : chainOK 1 (pR :: tR) = true)
    (hR0 : (pR.1 : ℝ) - pR.2 ≤ 0)
    (hR1 : (11 / 10 : ℝ) ≤ (((pR :: tR).getLast (by simp)).1 : ℝ) + (((pR :: tR).getLast (by simp)).2 : ℝ))
    (hcR : ∀ q ∈ pR :: tR, ∀ y ∈ Icc ((q.1 : ℝ) - q.2) ((q.1 : ℝ) + q.2),
      Wan c N (DecayInstance.laiP + Complex.I * (y : ℂ)) ≤ laiEll) :
    LaiCover c N laiEll wA wB := by
  have hπ := Real.pi_lt_d4
  have hπ0 := Real.pi_pos
  refine ⟨hwA0, hwB0, hwA, hwB, ?_, ?_, ?_, ?_⟩
  · have := cover_pred (fun x => Wan c N (DecayInstance.laiM + DecayInstance.laiH * ((Real.cos x : ℝ) : ℂ)) ≤ laiEll)
      (kq := 31416 / 10000) (s := Real.pi) hπ0.le (by push_cast; linarith) pA tA hA
      (lo := 0) (hi := Real.pi) (by
        have h1 : (pA.1 : ℝ) * (31416 / 10000) ≤ pA.2 := by
          have := (Rat.cast_le (K := ℝ)).2 hA0.2; push_cast at this; exact this
        have h2 : (0 : ℝ) ≤ pA.1 := by exact_mod_cast hA0.1
        nlinarith) (by
        have h1 : (((1 : ℚ) - ((pA :: tA).getLast (by simp)).1) * (31416 / 10000) : ℚ) ≤
            ((pA :: tA).getLast (by simp)).2 := hA1.2
        have h1' : (1 - (((pA :: tA).getLast (by simp)).1 : ℝ)) * (31416 / 10000) ≤
            (((pA :: tA).getLast (by simp)).2 : ℝ) := by
          have := (Rat.cast_le (K := ℝ)).2 h1; push_cast at this; exact this
        have h2 : (((pA :: tA).getLast (by simp)).1 : ℝ) ≤ 1 := by exact_mod_cast hA1.1
        nlinarith) hcA
    exact fun θ hθ => this θ hθ
  · exact fun w hw => cover_pred (fun w => Wan c N (DecayInstance.laiM + DecayInstance.laiH * ((((-1 : ℝ) * Real.cosh w : ℝ)) : ℂ)) ≤ laiEll)
      (kq := 1) (s := 1) zero_le_one (by norm_num) pG tG hG (lo := 0) (hi := wA)
      (by simpa using hG0) (by simpa using hG1) (by simpa using hcG) w hw
  · exact fun w hw => cover_pred (fun w => Wan c N (DecayInstance.laiM + DecayInstance.laiH * ((((1 : ℝ) * Real.cosh w : ℝ)) : ℂ)) ≤ laiEll)
      (kq := 1) (s := 1) zero_le_one (by norm_num) pH tH hH (lo := 0) (hi := wB)
      (by simpa using hH0) (by simpa using hH1) (by simpa using hcH) w hw
  · exact fun y hy => cover_pred (fun y => Wan c N (DecayInstance.laiP + Complex.I * (y : ℂ)) ≤ laiEll)
      (kq := 1) (s := 1) zero_le_one (by norm_num) pR tR hR (lo := 0) (hi := 11 / 10)
      (by simpa using hR0) (by simpa using hR1) (by simpa using hcR) y hy


/-! ### G-d: sup bounds of the cross tower, enclosure of the cell bound, and `LaiEnergyOK` -/

/-- `U_j = (Σ_{m < 5-j} (|tq_{j+m}| + te_{j+m}) r^m/m! + T₅ r^{5-j}/(5-j)!)/j!`: the sup bound of
`|f^{(j)}|/j!` on a cell from centre enclosures `tq ± te` (`j ≤ 4`) and `|f⁽⁵⁾| ≤ T₅`. -/
def supB (tq te : ℕ → ℚ) (T5 r : ℝ) (j : ℕ) : ℝ :=
  ((∑ m ∈ range (5 - j), (((|tq (j + m)| + te (j + m) : ℚ)) : ℝ) * r ^ m / (m.factorial : ℝ)) +
    T5 * r ^ (5 - j) / ((5 - j).factorial : ℝ)) / (j.factorial : ℝ)

theorem tower_sup_le {f : ℕ → ℝ → ℝ} {c r : ℝ} (hf : IsTower f c r 5) {tq te : ℕ → ℚ} {T5 : ℝ}
    (hc : ∀ j ≤ 4, |f j c - (tq j : ℝ)| ≤ (te j : ℝ))
    (h5 : ∀ x ∈ Icc (c - r) (c + r), |f 5 x| ≤ T5) (j : ℕ) (hj : j ≤ 5) :
    ∀ x ∈ Icc (c - r) (c + r), |f j x| / (j.factorial : ℝ) ≤ supB tq te T5 r j := by
  intro x hx
  have hxr : |x - c| ≤ r := abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
  obtain ⟨m, hm⟩ : ∃ m, m = 5 - j := ⟨_, rfl⟩
  have hjm : j + m = 5 := by omega
  have htay := CatalanMeasure.CellCert.taylor_tower' c r T5 m (fun k => f (j + k))
    (fun k hk => hf.cont (j + k) (by omega))
    (fun k hk y hy => hf.der (j + k) (by omega) y hy)
    (by intro y hy; show |f (j + m) y| ≤ T5; rw [hjm]; exact h5 y hy) x hx
  simp only [add_zero] at htay
  have hB : ∀ k < m, |f (j + k) c| ≤ ((|tq (j + k)| + te (j + k) : ℚ) : ℝ) := by
    intro k hk
    have h := hc (j + k) (by omega)
    have := abs_sub_abs_le_abs_sub (f (j + k) c) (tq (j + k) : ℝ)
    push_cast
    linarith
  have hr : 0 ≤ r := (abs_nonneg _).trans hxr
  have hsum : |∑ k ∈ range m, f (j + k) c * (x - c) ^ k / (k.factorial : ℝ)| ≤
      ∑ k ∈ range m, (((|tq (j + k)| + te (j + k) : ℚ)) : ℝ) * r ^ k / (k.factorial : ℝ) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k hk => ?_)
    have hk' := Finset.mem_range.1 hk
    have hkf : (0 : ℝ) < (k.factorial : ℝ) := by positivity
    rw [abs_div, abs_mul, abs_pow, Nat.abs_cast]
    refine div_le_div_of_nonneg_right ?_ hkf.le
    exact mul_le_mul (hB k hk') (pow_le_pow_left₀ (abs_nonneg _) hxr k) (by positivity)
      ((abs_nonneg _).trans (hB k hk'))
  have hT : T5 * |x - c| ^ m / (m.factorial : ℝ) ≤ T5 * r ^ m / (m.factorial : ℝ) := by
    have hT5 : 0 ≤ T5 := (abs_nonneg _).trans (h5 c ⟨by linarith, by linarith⟩)
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hxr m) hT5) (by positivity)
  have hfj : |f j x| ≤ ∑ k ∈ range m, (((|tq (j + k)| + te (j + k) : ℚ)) : ℝ) * r ^ k / (k.factorial : ℝ)
      + T5 * r ^ m / (m.factorial : ℝ) := by
    have := abs_sub_abs_le_abs_sub (f j x) (∑ k ∈ range m, f (j + k) c * (x - c) ^ k / (k.factorial : ℝ))
    linarith
  unfold supB
  rw [← hm]
  exact div_le_div_of_nonneg_right hfj (by positivity)

/-- enclosure of the cosine tower `Ftow` at `x = π n / 128`, by the checked table. -/
theorem Ftow_enc {c : ℕ → ℝ} {cq : ℕ → ℚ} (N : ℕ) (hc : ∀ k ≤ N, (cq k : ℝ) = c k) (j n : ℕ) :
    |Ftow c N j (Real.pi * (n : ℝ) / 128) -
        (((∑ k ∈ range (N + 1), cq k * (k : ℚ) ^ j * CatalanCore.Lai.DecayTrig.cosTm (k * n + 64 * j) : ℚ)) : ℝ)| ≤
      (((∑ k ∈ range (N + 1), |cq k * (k : ℚ) ^ j| * CatalanCore.Lai.DecayTrig.trigE : ℚ)) : ℝ) := by
  unfold Ftow
  push_cast
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k hk => ?_)
  have hkN : k ≤ N := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
  rw [← hc k hkN]
  have hcos : |Real.cos (Real.pi * (((k * n + 64 * j : ℕ)) : ℝ) / 128) -
      (CatalanCore.Lai.DecayTrig.cosTm (k * n + 64 * j) : ℝ)| ≤ (CatalanCore.Lai.DecayTrig.trigE : ℝ) :=
    (CatalanCore.Lai.DecayTrig.trig_enc_nat _).1
  have e : Real.cos ((k : ℝ) * (Real.pi * (n : ℝ) / 128) + (j : ℝ) * (Real.pi / 2)) =
      Real.cos (Real.pi * (((k * n + 64 * j : ℕ)) : ℝ) / 128) := by
    congr 1; push_cast; ring
  rw [e, ← mul_sub, abs_mul]
  have h2 := mul_le_mul_of_nonneg_left hcos (abs_nonneg ((cq k : ℝ) * (k : ℝ) ^ j))
  push_cast at h2 ⊢
  exact h2

theorem prod_le_enc {g f gq fq ge fe : ℝ} (hg : |g - gq| ≤ ge) (hf : |f - fq| ≤ fe) :
    g * f ≤ gq * fq + |gq| * fe + |fq| * ge + ge * fe := by
  have hge : 0 ≤ ge := (abs_nonneg _).trans hg
  have e : g * f = gq * fq + gq * (f - fq) + fq * (g - gq) + (g - gq) * (f - fq) := by ring
  have a1 : gq * (f - fq) ≤ |gq| * fe := by
    calc gq * (f - fq) ≤ |gq * (f - fq)| := le_abs_self _
      _ = |gq| * |f - fq| := abs_mul _ _
      _ ≤ |gq| * fe := mul_le_mul_of_nonneg_left hf (abs_nonneg _)
  have a2 : fq * (g - gq) ≤ |fq| * ge := by
    calc fq * (g - gq) ≤ |fq * (g - gq)| := le_abs_self _
      _ = |fq| * |g - gq| := abs_mul _ _
      _ ≤ |fq| * ge := mul_le_mul_of_nonneg_left hg (abs_nonneg _)
  have a3 : (g - gq) * (f - fq) ≤ ge * fe := by
    calc (g - gq) * (f - fq) ≤ |(g - gq) * (f - fq)| := le_abs_self _
      _ = |g - gq| * |f - fq| := abs_mul _ _
      _ ≤ ge * fe := mul_le_mul hg hf (abs_nonneg _) hge
  rw [e]; linarith

/-- The product tower at `a` is bounded by the interval product of the two enclosures. -/
theorem mulTower_le_enc {Gt Ft : ℕ → ℝ → ℝ} {a : ℝ} {gq ge fq fe : ℕ → ℝ} (j : ℕ)
    (hg : ∀ i ≤ j, |Gt i a - gq i| ≤ ge i) (hf : ∀ i ≤ j, |Ft i a - fq i| ≤ fe i) :
    mulTower Gt Ft j a ≤ ∑ ij ∈ antidiagonal j, (j.choose ij.1 : ℝ) *
      (gq ij.1 * fq ij.2 + |gq ij.1| * fe ij.2 + |fq ij.2| * ge ij.1 + ge ij.1 * fe ij.2) := by
  unfold mulTower
  refine Finset.sum_le_sum fun ij hij => ?_
  have hs := Finset.mem_antidiagonal.1 hij
  exact mul_le_mul_of_nonneg_left (prod_le_enc (hg ij.1 (by omega)) (hf ij.2 (by omega)))
    (Nat.cast_nonneg _)

theorem crossCellBound_le (Gt : ℕ → ℝ → ℝ) (c : ℕ → ℝ) (N : ℕ) {a r E u0 u2 u4 : ℝ} (hr : 0 ≤ r)
    (h0 : mulTower Gt (Ftow c N) 0 a ≤ u0) (h2 : mulTower Gt (Ftow c N) 2 a ≤ u2)
    (h4 : mulTower Gt (Ftow c N) 4 a ≤ u4) :
    crossCellBound Gt c N a r E ≤ 2 * (u0 * r + u2 / 2 * (r ^ 3 / 3) + u4 / 24 * (r ^ 5 / 5)) +
      E * (r ^ 6 / 3) := by
  unfold crossCellBound
  have p3 : 0 ≤ r ^ 3 / 3 := by positivity
  have p5 : 0 ≤ r ^ 5 / 5 := by positivity
  nlinarith [mul_le_mul_of_nonneg_right h0 hr,
    mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right h2 (by norm_num : (0:ℝ) ≤ 2)) p3,
    mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right h4 (by norm_num : (0:ℝ) ≤ 24)) p5]

/-- The cross tower of Lai's design. -/
abbrev crossT (c : ℕ → ℝ) (N : ℕ) : ℕ → ℝ → ℝ :=
  potT (starRingEnd ℂ DecayInstance.laiM) (starRingEnd ℂ DecayInstance.laiH) c N
    (cosCurve DecayInstance.laiM DecayInstance.laiH)

/-- **`LaiEnergyOK` from per-cell data.**  For an exact partition `0 = a₀ ≤ ⋯ ≤ a_n = π`:
* `hcen`: at each centre the tower values `j ≤ 4` of the cross potential are enclosed by `tq ± te`;
* `h5`: `|G⁽⁵⁾|/120 ≤ U5` on the cell (`cross_U5_le`);
* `hE`: `Σ_{i+j=5} U_{ij} V_j ≤ E` for the sup bounds `supB`;
* `hfin`: the final inequality (the cell bounds `crossCellBound ≤ …` via `crossCellBound_le`,
  `mulTower_le_enc`, `Ftow_enc`). -/
theorem laiEnergyOK_of_cells {c : ℕ → ℝ} {N : ℕ} (hpos : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ chebF c N x)
    (n : ℕ) (a : ℕ → ℝ) (a0 : a 0 = 0) (an : a n = Real.pi) (hmono : ∀ i < n, a i ≤ a (i + 1))
    (tq te : ℕ → ℕ → ℚ) (U5 : ℕ → ℝ) (Er : ℕ → ℝ)
    (hcen : ∀ i < n, ∀ j ≤ 4,
      |crossT c N j ((a i + a (i + 1)) / 2) - (tq i j : ℝ)| ≤ (te i j : ℝ))
    (h5 : ∀ i < n, ∀ x ∈ Icc (a i) (a (i + 1)), |crossT c N 5 x| / 120 ≤ U5 i)
    (hE : ∀ i < n, ∑ ij ∈ antidiagonal 5,
      supB (tq i) (te i) (120 * U5 i) ((a (i + 1) - a i) / 2) ij.1 * Vf c N ij.2 ≤ Er i)
    (hfin : 2 * (-(c 0 ^ 2 * (Real.log ‖DecayInstance.laiH‖ - Real.log 2)) +
          ∑ k ∈ Finset.range N, c (k + 1) ^ 2 / (2 * ((k + 1 : ℕ) : ℝ))) +
      2 * ((1 / Real.pi) * ∑ i ∈ Finset.range n,
        crossCellBound (crossT c N) c N
          ((a i + a (i + 1)) / 2) ((a (i + 1) - a i) / 2) (Er i)) ≤ 208871 / 10 ^ 5) :
    LaiEnergyOK c N := by
  have hh' : starRingEnd ℂ DecayInstance.laiH ≠ 0 :=
    (_root_.map_ne_zero (starRingEnd ℂ)).2 DecayInstance.laiH_ne
  have e1 : ∀ i, (a i + a (i + 1)) / 2 - (a (i + 1) - a i) / 2 = a i := fun i => by ring
  have e2 : ∀ i, (a i + a (i + 1)) / 2 + (a (i + 1) - a i) / 2 = a (i + 1) := fun i => by ring
  refine ⟨n, a, fun i j => supB (tq i) (te i) (120 * U5 i) ((a (i + 1) - a i) / 2) j, Er,
    a0, an, hmono, ?_, hE, hfin⟩
  intro i hi x hx j hj
  have hT := isTower_cross (M := DecayInstance.laiM) (h := DecayInstance.laiH) hh' hpos
    lai_hsep ((a i + a (i + 1)) / 2) ((a (i + 1) - a i) / 2)
  have hx' : x ∈ Icc ((a i + a (i + 1)) / 2 - (a (i + 1) - a i) / 2)
      ((a i + a (i + 1)) / 2 + (a (i + 1) - a i) / 2) := by rw [e1, e2]; exact hx
  exact tower_sup_le hT (hcen i hi) (fun y hy => by
      have := h5 i hi y (by rw [e1, e2] at hy; exact hy)
      rw [div_le_iff₀ (by norm_num : (0:ℝ) < 120)] at this
      linarith) j hj x hx'



/-! ### G-e: the atom numbers `a(x*)`, `a'(x*)` as closed forms -/

/-- For a conjugation-symmetric integrand, the integral against `σ = s₊ + s̄₊` is twice that against `s₊`. -/
theorem integral_sig2_eq (g : ℂ → ℝ) (hg : Measurable g) (hgc : ∀ u, g (starRingEnd ℂ u) = g u)
    {M h : ℂ} {c : ℕ → ℝ} {N : ℕ} (hI : MeasureTheory.Integrable g (sig2 M h c N)) :
    ∫ u, g u ∂(sig2 M h c N) = 2 * ∫ u, g u ∂(segMeasure M h c N) := by
  unfold sig2 at hI ⊢
  obtain ⟨h1, h2⟩ := MeasureTheory.integrable_add_measure.mp hI
  rw [MeasureTheory.integral_add_measure h1 h2, ← DecayInstance.map_conj_segMeasure M h c N,
    MeasureTheory.integral_map Complex.continuous_conj.measurable.aemeasurable hg.aestronglyMeasurable]
  simp only [hgc]
  ring

theorem integral_log_seg {M h : ℂ} {c : ℕ → ℝ} {N : ℕ} (x : ℝ) :
    ∫ u, Real.log ‖(x : ℂ) + u‖ ∂(segMeasure M h c N) = -logPotC (segMeasure M h c N) (-(x : ℂ)) := by
  unfold logPotC
  rw [neg_neg]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  show Real.log ‖(x : ℂ) + u‖ = Real.log ‖-(x : ℂ) - u‖
  rw [show -(x : ℂ) - u = -((x : ℂ) + u) by ring, norm_neg]

theorem integrable_inv_seg {M h : ℂ} (hh : h ≠ 0) {c : ℕ → ℝ} {N : ℕ}
    (hpos : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ chebF c N x) {s : ℂ} (hs : 1 < jc ((s - M) / h)) :
    MeasureTheory.Integrable (fun u : ℂ => ((s - u) ^ 1)⁻¹) (segMeasure M h c N) := by
  have hd0 := seg_dist_pos hh hs
  have key : ∀ p : ℂ → ℝ, Measurable p → (∀ u : ℂ, |p u| ≤ ‖((s - u) ^ 1)⁻¹‖) →
      MeasureTheory.Integrable p (segMeasure M h c N) := by
    intro p hp hb
    refine (integrable_segMeasure_iff (M := M) (h := h) hpos hp).2 ?_
    refine MeasureTheory.Integrable.mono'
      (MeasureTheory.integrable_const ((∑ k ∈ Finset.range (N + 1), |c k|) /
        (‖h‖ * (jc ((s - M) / h) - 1)))) ?_ (MeasureTheory.ae_of_all _ fun θ => ?_)
    · exact ((continuous_chebF_cos c N).measurable.mul
        (hp.comp (by fun_prop : Measurable fun θ : ℝ => M + h * (Real.cos θ : ℂ)))).aestronglyMeasurable
    · rw [norm_mul, Real.norm_eq_abs, div_eq_mul_inv]
      refine mul_le_mul (abs_chebF_le c N (cos_mem θ)) ?_ (abs_nonneg _)
        (Finset.sum_nonneg fun k _ => abs_nonneg _)
      refine (hb _).trans ?_
      have := norm_sub_seg_ge (M := M) (s := s) hh (cos_mem θ)
      rw [norm_inv, norm_pow, pow_one]
      exact inv_anti₀ hd0 this
  have hre := key (fun u => (((s - u) ^ 1)⁻¹).re) (by fun_prop) (fun u => Complex.abs_re_le_norm _)
  have him := key (fun u => (((s - u) ^ 1)⁻¹).im) (by fun_prop) (fun u => Complex.abs_im_le_norm _)
  have := (hre.ofReal (𝕜 := ℂ)).add ((him.ofReal (𝕜 := ℂ)).const_mul Complex.I)
  refine this.congr (Filter.Eventually.of_forall fun u => ?_)
  simp only [Pi.add_apply]
  apply Complex.ext <;> simp

/-- `∫ ln1 u x dμ = -Re S₁(-x)`. -/
theorem integral_ln1_seg {M h : ℂ} (hh : h ≠ 0) {c : ℕ → ℝ} {N : ℕ}
    (hpos : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ chebF c N x) {x : ℝ} (hs : 1 < jc ((-(x : ℂ) - M) / h)) :
    ∫ u, ln1 u x ∂(segMeasure M h c N) = -(segSt M h c N 1 (-(x : ℂ))).re := by
  have hI := integrable_inv_seg hh hpos hs
  unfold segSt
  have hre := integral_re hI
  simp only [RCLike.re_to_complex] at hre
  rw [← hre, ← MeasureTheory.integral_neg]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  show ln1 u x = -(((-(x : ℂ) - u) ^ 1)⁻¹).re
  simp only [pow_one, Complex.inv_re, Complex.normSq_apply, Complex.sub_re, Complex.neg_re,
    Complex.ofReal_re, Complex.sub_im, Complex.neg_im, Complex.ofReal_im, ln1]
  have : (-x - u.re) * (-x - u.re) + (0 - u.im - 0) * (0 - u.im - 0) =
      (x + u.re) ^ 2 + u.im ^ 2 := by ring
  rw [show (-x - u.re) * (-x - u.re) + (-0 - u.im) * (-0 - u.im) = (x + u.re) ^ 2 + u.im ^ 2 by ring]
  field_simp
  ring

/-- **`ha0` from the closed form.**  `x* = 2211/500`, `ζ₀ = (-x* - M)/h`; the value
`a(x*) = ω(x*) - 4 U^{s₊}(-x*)` with `U^{s₊}` the closed form of `logPotC_segMeasure`. -/
theorem lai_ha0_of_closed {c : ℕ → ℝ} {N : ℕ} (hpos : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ chebF c N x)
    {a0 : ℝ}
    (hs : 1 < jc ((-((2211 / 500 : ℝ) : ℂ) - DecayInstance.laiM) / DecayInstance.laiH))
    (hv : omegaF 3 2 2 6 (2211 / 500) - 2 * (2 *
        (-c 0 * Real.log ‖DecayInstance.laiH‖ -
          c 0 * Real.log (jR ((-((2211 / 500 : ℝ) : ℂ) - DecayInstance.laiM) / DecayInstance.laiH) / 2) +
        ∑ k ∈ Finset.range N, c (k + 1) *
          ((jphi ((-((2211 / 500 : ℝ) : ℂ) - DecayInstance.laiM) / DecayInstance.laiH) ^ (k + 1))⁻¹).re /
            ((k + 1 : ℕ) : ℝ))) ≤ a0) :
    omegaF 3 2 2 6 (2211 / 500) +
      2 * ∫ u, Real.log ‖((2211 / 500 : ℝ) : ℂ) + u‖ ∂(laiSigma c N) ≤ a0 := by
  haveI := isFiniteMeasure_sig2 (M := DecayInstance.laiM) (h := DecayInstance.laiH) hpos
  have hσ := ballMajA_sig2 (M := DecayInstance.laiM) DecayInstance.laiH_ne c N
  have hI := DecayInstance.laiSigma_hint hσ (2211 / 500) ⟨by norm_num, by norm_num⟩
  have e1 : ∫ u, Real.log ‖((2211 / 500 : ℝ) : ℂ) + u‖ ∂(laiSigma c N) =
      2 * -logPotC (segMeasure DecayInstance.laiM DecayInstance.laiH c N) (-((2211 / 500 : ℝ) : ℂ)) := by
    rw [← integral_log_seg (M := DecayInstance.laiM) (h := DecayInstance.laiH) (c := c) (N := N)]
    exact integral_sig2_eq _ (Real.measurable_log.comp (by fun_prop)) (fun u => by
      show Real.log ‖((2211 / 500 : ℝ) : ℂ) + starRingEnd ℂ u‖ = Real.log ‖((2211 / 500 : ℝ) : ℂ) + u‖
      have : ((2211 / 500 : ℝ) : ℂ) + starRingEnd ℂ u = starRingEnd ℂ (((2211 / 500 : ℝ) : ℂ) + u) := by
        rw [map_add, Complex.conj_ofReal]
      rw [this]; exact congrArg Real.log (RCLike.norm_conj _)) hI
  rw [e1, logPotC_segMeasure DecayInstance.laiH_ne hpos hs]
  linarith

/-- **`hA` from the closed form.**  `a'(x*) = ω'(x*) - 4 Re S₁(-x*)`, `S₁ = (h q)⁻¹(c₀ + Σ c_{k+1} φ^{-(k+1)})`. -/
theorem lai_hA_of_closed {c : ℕ → ℝ} {N : ℕ} (hpos : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ chebF c N x)
    {AA : ℝ}
    (hs : 1 < jc ((-((2211 / 500 : ℝ) : ℂ) - DecayInstance.laiM) / DecayInstance.laiH))
    (hv : |omegaD1 3 2 2 6 (2211 / 500) - 2 * (2 *
      ((DecayInstance.laiH * jq ((-((2211 / 500 : ℝ) : ℂ) - DecayInstance.laiM) / DecayInstance.laiH))⁻¹ *
        ((c 0 : ℂ) + ∑ k ∈ Finset.range N, (c (k + 1) : ℂ) *
          (jphi ((-((2211 / 500 : ℝ) : ℂ) - DecayInstance.laiM) / DecayInstance.laiH))⁻¹ ^ (k + 1))).re)| ≤ AA) :
    |omegaD1 3 2 2 6 (2211 / 500) + 2 * ∫ u, ln1 u (2211 / 500) ∂(laiSigma c N)| ≤ AA := by
  haveI := isFiniteMeasure_sig2 (M := DecayInstance.laiM) (h := DecayInstance.laiH) hpos
  have hI := DecayInstance.laiSigma_hint1 (c := c) (N := N)
  have e1 : ∫ u, ln1 u (2211 / 500) ∂(laiSigma c N) =
      2 * -(segSt DecayInstance.laiM DecayInstance.laiH c N 1 (-((2211 / 500 : ℝ) : ℂ))).re := by
    rw [← integral_ln1_seg DecayInstance.laiH_ne hpos hs]
    exact integral_sig2_eq _ (by unfold ln1; fun_prop) (fun u => by simp [ln1]) hI
  rw [e1, segSt_one DecayInstance.laiH_ne hpos hs]
  convert hv using 2
  ring


/-- **Checked root.**  A rational `φ_q` with `|φ_q| > 1` and a small residual of `φ² - 2ζφ + 1`
encloses `jphi ζ`: `|jphi ζ - φ_q| (|φ_q| - 1) ≤ |φ_q² - 2 ζ φ_q + 1|`. -/
theorem jphi_close {ζ φq : ℂ} (h : 1 < jc ζ) (hq : 1 < ‖φq‖) :
    ‖jphi ζ - φq‖ * (‖φq‖ - 1) ≤ ‖φq ^ 2 - 2 * ζ * φq + 1‖ := by
  obtain ⟨hφ1, hJ⟩ := jphi_spec h
  set φ := jphi ζ with hφ
  have hφ0 : φ ≠ 0 := jphi_ne_zero h
  have hζ : 2 * ζ = φ + φ⁻¹ := by
    rw [← hJ]; unfold jJ; ring
  have hid : φq ^ 2 - 2 * ζ * φq + 1 = (φq - φ) * (φq - φ⁻¹) := by
    rw [show 2 * ζ * φq = (2 * ζ) * φq by ring, hζ]; field_simp; ring
  have hinv : ‖φ⁻¹‖ ≤ 1 := by
    rw [norm_inv]; exact inv_le_one_of_one_le₀ hφ1.le
  have h2 : ‖φq‖ - 1 ≤ ‖φq - φ⁻¹‖ := by
    have := norm_sub_norm_le φq φ⁻¹
    linarith
  rw [hid, norm_mul, norm_sub_rev φ φq]
  exact mul_le_mul_of_nonneg_left h2 (norm_nonneg _)

end

end CatalanCore.Lai.DecayGlue

open CatalanCore.Lai.DecayGlue in
#print axioms laiC_data
open CatalanCore.Lai.DecayGlue in
#print axioms laiCover_of_chains
open CatalanCore.Lai.DecayGlue in
#print axioms cosh_wA
open CatalanCore.Lai.DecayGlue in
#print axioms cosh_wB
open CatalanCore.Lai.DecayGlue in
#print axioms laiEnergyOK_of_cells
open CatalanCore.Lai.DecayGlue in
#print axioms lai_ha0_of_closed
open CatalanCore.Lai.DecayGlue in
#print axioms lai_hA_of_closed
open CatalanCore.Lai.DecayGlue in
#print axioms jphi_close
open CatalanCore.Lai.DecayGlue in
#print axioms crossCellBound_le
open CatalanCore.Lai.DecayGlue in
#print axioms Ftow_enc
