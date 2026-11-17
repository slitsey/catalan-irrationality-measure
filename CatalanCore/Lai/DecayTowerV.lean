module

public import CatalanCore.Lai.DecayCells
public import CatalanCore.Lai.DecayGlue
public import CatalanMeasure.GenD.Signed.LogEval
public import CatalanCore.Lai.DecayTowerSeg

@[expose] public section

open Set Real Finset
open CatalanCore.Zeta5.Potential CatalanMeasure.GenD.Signed.LogEval CatalanMeasure.Cert CatalanMeasure.CellCert OAI.InternalCatalan CatalanCore.Zeta5.Cells CatalanMeasure.GenD.Signed.TaylorCell
  CatalanCore.Tools.Joukowski CatalanCore.Decay.ComplexTaylor CatalanCore.Lai.DecayCells
  CatalanCore.Uniform.Decay.NearCells CatalanCore.Lai.DecayTowerSeg

namespace CatalanCore.Lai.DecayTowerV

noncomputable section

/-! ### R9 (a): rational trigonometry at `a' = 2 arctan τ` -/

theorem trig_two_arctan (τ : ℝ) :
    Real.cos (2 * Real.arctan τ) = (1 - τ ^ 2) / (1 + τ ^ 2) ∧
    Real.sin (2 * Real.arctan τ) = 2 * τ / (1 + τ ^ 2) := by
  have hp : 0 < 1 + τ ^ 2 := by positivity
  have hsq : Real.sqrt (1 + τ ^ 2) ^ 2 = 1 + τ ^ 2 := Real.sq_sqrt hp.le
  have hs0 : 0 < Real.sqrt (1 + τ ^ 2) := Real.sqrt_pos.2 hp
  constructor
  · rw [Real.cos_two_mul, Real.cos_arctan, div_pow, hsq]
    field_simp
    ring
  · rw [Real.sin_two_mul, Real.sin_arctan, Real.cos_arctan]
    field_simp
    rw [hsq]

/-- the powers `(cos (k a), sin (k a))` from rational `cos a`, `sin a` -/
def rotPow (cc sn : ℚ) : ℕ → ℚ × ℚ
  | 0 => (1, 0)
  | k + 1 => ((rotPow cc sn k).1 * cc - (rotPow cc sn k).2 * sn,
      (rotPow cc sn k).2 * cc + (rotPow cc sn k).1 * sn)

theorem rotPow_spec {a : ℝ} {cc sn : ℚ} (hc : (cc : ℝ) = Real.cos a) (hs : (sn : ℝ) = Real.sin a)
    (k : ℕ) : ((rotPow cc sn k).1 : ℝ) = Real.cos ((k : ℝ) * a) ∧
      ((rotPow cc sn k).2 : ℝ) = Real.sin ((k : ℝ) * a) := by
  induction k with
  | zero => simp [rotPow]
  | succ k ih =>
    obtain ⟨h1, h2⟩ := ih
    simp only [rotPow, Rat.cast_sub, Rat.cast_mul, Rat.cast_add, h1, h2, hc, hs]
    have e : ((k + 1 : ℕ) : ℝ) * a = (k : ℝ) * a + a := by push_cast; ring
    rw [e, Real.cos_add, Real.sin_add]
    constructor <;> ring

/-- `cos (x + j π/2)` from `cos x`, `sin x`. -/
def cosJ (c s : ℚ) (j : ℕ) : ℚ :=
  if j % 4 = 0 then c else if j % 4 = 1 then -s else if j % 4 = 2 then -c else s

theorem cosJ_spec {x : ℝ} {c s : ℚ} (hc : (c : ℝ) = Real.cos x) (hs : (s : ℝ) = Real.sin x)
    (j : ℕ) : (cosJ c s j : ℝ) = Real.cos (x + (j : ℝ) * (Real.pi / 2)) := by
  have hj : (j : ℝ) * (Real.pi / 2) = ((j / 4 : ℕ) : ℝ) * (2 * Real.pi) + ((j % 4 : ℕ) : ℝ) * (Real.pi / 2) := by
    have : (j : ℝ) = 4 * ((j / 4 : ℕ) : ℝ) + ((j % 4 : ℕ) : ℝ) := by exact_mod_cast (Nat.div_add_mod j 4).symm
    rw [this]; ring
  rw [show x + (j : ℝ) * (Real.pi / 2) = (x + ((j % 4 : ℕ) : ℝ) * (Real.pi / 2)) + ((j / 4 : ℕ) : ℝ) * (2 * Real.pi) by
    rw [hj]; ring, Real.cos_add_nat_mul_two_pi]
  have hm : j % 4 < 4 := Nat.mod_lt _ (by norm_num)
  unfold cosJ
  interval_cases h : j % 4
  · simp [hc]
  · simp [hs, Real.cos_add_pi_div_two]
  · simp only [if_neg (by norm_num : ¬ (2 = 0)), if_neg (by norm_num : ¬ (2 = 1)), if_true]
    push_cast
    rw [show (2 : ℝ) * (Real.pi / 2) = Real.pi by ring, Real.cos_add_pi, hc]
  · simp only [if_neg (by norm_num : ¬ (3 = 0)), if_neg (by norm_num : ¬ (3 = 1)), if_neg (by norm_num : ¬ (3 = 2))]
    push_cast
    rw [show (3 : ℝ) * (Real.pi / 2) = Real.pi / 2 + Real.pi by ring, ← add_assoc, Real.cos_add_pi,
      Real.cos_add_pi_div_two, hs]
    simp

/-- The A tower at a point with rational `cos a`, `sin a`. -/
def ownATr (K0q : ℚ) (wq : ℕ → ℚ) (N j : ℕ) (cc sn : ℚ) : ℚ :=
  (if j = 0 then K0q else 0) + ∑ k ∈ Finset.range N,
    wq (k + 1) / ((k + 1 : ℕ) : ℚ) * ((k + 1 : ℕ) : ℚ) ^ j *
      cosJ (rotPow cc sn (k + 1)).1 (rotPow cc sn (k + 1)).2 j

theorem ownAT_enc_rot {K0 : ℝ} {K0q eK : ℚ} (hK0 : |K0 - (K0q : ℝ)| ≤ (eK : ℝ)) {w : ℕ → ℝ}
    {wq : ℕ → ℚ} (N : ℕ) (hw : ∀ k < N, (wq (k + 1) : ℝ) = w (k + 1)) {a : ℝ} {cc sn : ℚ}
    (hc : (cc : ℝ) = Real.cos a) (hs : (sn : ℝ) = Real.sin a) (j : ℕ) :
    |ownAT K0 w N j a - ((ownATr K0q wq N j cc sn : ℚ) : ℝ)| ≤ (if j = 0 then (eK : ℝ) else 0) := by
  have hterm : ∀ k ∈ Finset.range N,
      w (k + 1) / ((k + 1 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ) ^ j *
          Real.cos (((k + 1 : ℕ) : ℝ) * a + (j : ℝ) * (Real.pi / 2)) =
        (((wq (k + 1) / ((k + 1 : ℕ) : ℚ) * ((k + 1 : ℕ) : ℚ) ^ j *
          cosJ (rotPow cc sn (k + 1)).1 (rotPow cc sn (k + 1)).2 j : ℚ)) : ℝ) := by
    intro k hk
    have hr := rotPow_spec hc hs (k + 1)
    have hj := cosJ_spec hr.1 hr.2 j
    rw [← hw k (Finset.mem_range.1 hk)]
    push_cast
    rw [hj]; push_cast; ring_nf
  have hsum := Finset.sum_congr rfl hterm
  unfold ownAT ownATr
  rw [Rat.cast_add, Rat.cast_sum, ← hsum]
  have e : ((if j = 0 then K0 else 0) + ∑ k ∈ Finset.range N,
        w (k + 1) / ((k + 1 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ) ^ j *
          Real.cos (((k + 1 : ℕ) : ℝ) * a + (j : ℝ) * (Real.pi / 2))) -
      ((((if j = 0 then K0q else 0 : ℚ)) : ℝ) + ∑ k ∈ Finset.range N,
        w (k + 1) / ((k + 1 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ) ^ j *
          Real.cos (((k + 1 : ℕ) : ℝ) * a + (j : ℝ) * (Real.pi / 2))) =
      (if j = 0 then K0 else 0) - (((if j = 0 then K0q else 0 : ℚ)) : ℝ) := by ring
  rw [e]
  by_cases hj : j = 0 <;> simp [hj, hK0]

/-! ### R9 (b): the G arm at `x = -log ρ` -/

theorem cosh_neg_log {ρ : ℝ} (hρ : 0 < ρ) : Real.cosh (-Real.log ρ) = (ρ + ρ⁻¹) / 2 := by
  rw [Real.cosh_neg, Real.cosh_eq, Real.exp_log hρ, Real.exp_neg, Real.exp_log hρ]

theorem sinh_neg_log {ρ : ℝ} (hρ : 0 < ρ) : Real.sinh (-Real.log ρ) = (ρ⁻¹ - ρ) / 2 := by
  rw [Real.sinh_eq, neg_neg, Real.exp_log hρ, Real.exp_neg, Real.exp_log hρ]

/-- `armG` at `x = -log ρ`, entrywise. -/
theorem armG_neg_log (M h : ℂ) (s : ℝ) {ρ : ℝ} (hρ : 0 < ρ) (i : ℕ) :
    armG M h s i (-Real.log ρ) = (if i = 0 then M else 0) +
      h * ((s * (if i % 2 = 0 then (ρ + ρ⁻¹) / 2 else (ρ⁻¹ - ρ) / 2) : ℝ) : ℂ) := by
  unfold armG coshT
  by_cases hi : i % 2 = 0
  · simp [hi, cosh_neg_log hρ]
  · simp [hi, sinh_neg_log hρ]

/-! ### R9 (c): `cellG_sound'` with `Ym i = ‖h‖ sinh w` for odd `i` -/

def YmG (h : ℂ) (whi : ℝ) (i : ℕ) : ℝ :=
  ‖h‖ * (if i % 2 = 0 then Real.cosh whi else Real.sinh whi)

theorem abs_coshT_le' {i : ℕ} {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    |coshT i x| ≤ if i % 2 = 0 then Real.cosh y else Real.sinh y := by
  unfold coshT
  split_ifs
  · rw [abs_of_pos (Real.cosh_pos x)]
    exact Real.cosh_le_cosh.2 (by rw [abs_of_nonneg hx, abs_of_nonneg (hx.trans hxy)]; exact hxy)
  · rw [abs_of_nonneg (Real.sinh_nonneg_iff.2 hx)]
    exact Real.sinh_le_sinh.2 hxy

theorem norm_armG_le' (M h : ℂ) {s : ℝ} (hs : |s| = 1) {i : ℕ} (hi : 1 ≤ i) {x y : ℝ} (hx : 0 ≤ x)
    (hxy : x ≤ y) : ‖armG M h s i x‖ ≤ YmG h y i := by
  have hi0 : i ≠ 0 := by omega
  unfold armG YmG
  rw [if_neg hi0, zero_add, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, hs, one_mul]
  exact mul_le_mul_of_nonneg_left (abs_coshT_le' hx hxy) (norm_nonneg _)

/-- **R9, `cellG_sound'`**: the G cell with the true majorant `‖h‖ sinh w` for odd derivatives. -/
theorem cellG_sound' (e r B K θ w₁ w₂ : ℝ) (he : 0 ≤ e) (hr : 0 ≤ r) {M h : ℂ} (hh : h ≠ 0)
    {cf : ℕ → ℝ} {N : ℕ} (hpos : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ chebF cf N x) {s : ℝ}
    (hs : s = 1 ∨ s = -1) {a ρ whi : ℝ} (ha : 0 ≤ a - ρ) (hwhi : a + ρ ≤ whi)
    (hdom : ∀ x ∈ Icc (a - ρ) (a + ρ), psiDom B K (M + h * ((s * Real.cosh x : ℝ) : ℂ)))
    {TV T2 : ℝ}
    (hV : VCell e r B K θ (armG M h s 0 a) (YmG h whi) ρ TV)
    {M₂ h₂ : ℂ} (hh₂ : h₂ ≠ 0) {c₂ : ℕ → ℝ} {N₂ : ℕ}
    (hpos₂ : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ chebF c₂ N₂ x)
    (hX : SegCell (armG M h s 0 a) (YmG h whi) ρ M₂ h₂ (c₂ 0) T2)
    {E : ℕ → ℝ} (hE : ∀ k < N, Real.exp (-(((k + 1 : ℕ) : ℝ) * (a - ρ))) ≤ E k)
    {tq te : ℕ → ℚ} {TR rq ℓ : ℚ} (hrq : (rq : ℝ) = ρ)
    (hTenc : ∀ j ≤ 4,
      |wedgeTower (vTower e r B K θ (r * (K * Real.log K - K) - e * (B * Real.log B - B))
          (armG M h s))
        (ownGT (-cf 0 * Real.log ‖h‖ + cf 0 * Real.log 2) (cf 0) s cf N)
        (potT M₂ h₂ c₂ N₂ (armG M h s)) w₁ w₂ j a - (tq j : ℝ)| ≤ (te j : ℝ))
    (hTR : TV + |w₁| * (∑ k ∈ Finset.range N, |cf (k + 1)| * ((k + 1 : ℕ) : ℝ) ^ 4 * E k) +
      |w₂| * T2 ≤ (TR : ℝ))
    (hok : wedgeCellOk tq te TR rq ℓ = true) :
    ∀ x ∈ Icc (a - ρ) (a + ρ),
      vAnal e r B K θ (M + h * ((s * Real.cosh x : ℝ) : ℂ)) +
        w₁ * logPotC (segMeasure M h cf N) (M + h * ((s * Real.cosh x : ℝ) : ℂ)) +
        w₂ * logPotC (segMeasure M₂ h₂ c₂ N₂) (M + h * ((s * Real.cosh x : ℝ) : ℂ)) ≤ (ℓ : ℝ) := by
  have habs : |s| = 1 := by rcases hs with rfl | rfl <;> simp
  have hx0 : ∀ x ∈ Icc (a - ρ) (a + ρ), 0 ≤ x := fun x hx => ha.trans hx.1
  have key := wedgeField_cell_sound e r B K θ w₁ w₂ he hr (γ := armG M h s)
    (fun i _ x => hasDerivAt_armG M h s i x) (continuous_armG M h s 5) (a := a) (ρ := ρ)
    (Ym := YmG h whi)
    (fun x hx i hi _ => norm_armG_le' M h habs hi (hx0 x hx) (hx.2.trans hwhi))
    (fun x hx => by rw [armG_zero]; exact hdom x hx) hV
    (U₁ := fun x => logPotC (segMeasure M h cf N) (M + h * ((s * Real.cosh x : ℝ) : ℂ)))
    (f₁ := ownGT (-cf 0 * Real.log ‖h‖ + cf 0 * Real.log 2) (cf 0) s cf N)
    (isTower_ownGT _ _ s cf N a ρ) (fun x hx => logPotC_eq_ownGT hh hpos hs (hx0 x hx))
    (fun x hx => abs_ownGT5_le _ _ s habs cf N x E (fun k hk =>
      (Real.exp_le_exp.2 (by nlinarith [hx.1, (by positivity : (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ))])).trans
        (hE k hk)))
    hh₂ hpos₂ hX hrq hTenc hTR hok
  intro x hx
  have := key x hx
  rw [armG_zero] at this
  exact this


/-! ### Gaussian rationals -/

structure GQ where
  re : ℚ
  im : ℚ

namespace GQ

def add (x y : GQ) : GQ := ⟨x.re + y.re, x.im + y.im⟩
def sub (x y : GQ) : GQ := ⟨x.re - y.re, x.im - y.im⟩
def mul (x y : GQ) : GQ := ⟨x.re * y.re - x.im * y.im, x.re * y.im + x.im * y.re⟩
def sc (c : ℚ) (x : GQ) : GQ := ⟨c * x.re, c * x.im⟩
def inv (x : GQ) : GQ := ⟨x.re / (x.re ^ 2 + x.im ^ 2), -x.im / (x.re ^ 2 + x.im ^ 2)⟩
def pw (x : GQ) : ℕ → GQ
  | 0 => ⟨1, 0⟩
  | n + 1 => mul (pw x n) x
def toC (x : GQ) : ℂ := ⟨(x.re : ℝ), (x.im : ℝ)⟩

theorem toC_add (x y : GQ) : toC (add x y) = toC x + toC y := by
  apply Complex.ext <;> simp [toC, add]
theorem toC_sub (x y : GQ) : toC (sub x y) = toC x - toC y := by
  apply Complex.ext <;> simp [toC, sub]
theorem toC_mul (x y : GQ) : toC (mul x y) = toC x * toC y := by
  apply Complex.ext <;> simp [toC, mul]
theorem toC_sc (c : ℚ) (x : GQ) : toC (sc c x) = (c : ℂ) * toC x := by
  apply Complex.ext <;> simp [toC, sc]
theorem toC_inv (x : GQ) : toC (inv x) = (toC x)⁻¹ := by
  apply Complex.ext
  · simp only [toC, inv, Complex.inv_re, Complex.normSq_apply]; push_cast; ring
  · simp only [toC, inv, Complex.inv_im, Complex.normSq_apply]; push_cast; ring
theorem toC_pw (x : GQ) (n : ℕ) : toC (pw x n) = toC x ^ n := by
  induction n with
  | zero => apply Complex.ext <;> simp [toC, pw]
  | succ n ih => rw [pw, toC_mul, ih, pow_succ]

end GQ

/-- the Faà di Bruno polynomials over `GQ` (orders `1..4`). -/
def fdbG (D Y : ℕ → GQ) : ℕ → GQ
  | 1 => GQ.mul (D 1) (Y 1)
  | 2 => GQ.add (GQ.mul (D 2) (GQ.mul (Y 1) (Y 1))) (GQ.mul (D 1) (Y 2))
  | 3 => GQ.add (GQ.add (GQ.mul (D 3) (GQ.mul (Y 1) (GQ.mul (Y 1) (Y 1))))
      (GQ.sc 3 (GQ.mul (D 2) (GQ.mul (Y 1) (Y 2))))) (GQ.mul (D 1) (Y 3))
  | 4 => GQ.add (GQ.add (GQ.add (GQ.mul (D 4) (GQ.mul (GQ.mul (Y 1) (Y 1)) (GQ.mul (Y 1) (Y 1))))
      (GQ.sc 6 (GQ.mul (D 3) (GQ.mul (GQ.mul (Y 1) (Y 1)) (Y 2)))))
      (GQ.mul (D 2) (GQ.add (GQ.sc 3 (GQ.mul (Y 2) (Y 2))) (GQ.sc 4 (GQ.mul (Y 1) (Y 3))))))
      (GQ.mul (D 1) (Y 4))
  | _ => ⟨0, 0⟩

theorem toC_fdbG (D Y : ℕ → GQ) (j : ℕ) (hj1 : 1 ≤ j) (hj : j ≤ 4) :
    GQ.toC (fdbG D Y j) = fdb (fun k => GQ.toC (D k)) (fun i => GQ.toC (Y i)) j := by
  interval_cases j <;>
    simp only [fdbG, fdb, GQ.toC_add, GQ.toC_mul, GQ.toC_sc] <;> push_cast <;> ring

/-- Only the `D 1` slot enters `fdb` linearly with coefficient `Y j`. -/
theorem fdb_sub_D1 (D D' Y : ℕ → ℂ) (hD : ∀ k, 2 ≤ k → D k = D' k) (j : ℕ) (hj1 : 1 ≤ j)
    (hj : j ≤ 4) : fdb D Y j - fdb D' Y j = (D 1 - D' 1) * Y j := by
  have h2 := hD 2 (by norm_num)
  have h3 := hD 3 (by norm_num)
  have h4 := hD 4 (by norm_num)
  interval_cases j <;> simp only [fdb, h2, h3, h4] <;> ring

theorem toC_const (c : ℚ) : GQ.toC ⟨c, 0⟩ = (c : ℂ) := by
  apply Complex.ext <;> simp [GQ.toC]

/-! ### Enclosure combinators -/

def eadd (p q : ℚ × ℚ) : ℚ × ℚ := (p.1 + q.1, p.2 + q.2)
def esub (p q : ℚ × ℚ) : ℚ × ℚ := (p.1 - q.1, p.2 + q.2)
def emul (w : ℚ) (p : ℚ × ℚ) : ℚ × ℚ := (w * p.1, qabs w * p.2)

theorem Enc_add {x y : ℝ} {p q : ℚ × ℚ} (hx : Enc x p) (hy : Enc y q) : Enc (x + y) (eadd p q) :=
  Enc.add hx hy
theorem Enc_sub {x y : ℝ} {p q : ℚ × ℚ} (hx : Enc x p) (hy : Enc y q) : Enc (x - y) (esub p q) :=
  Enc.sub hx hy
theorem Enc_mul (w : ℚ) {x : ℝ} {p : ℚ × ℚ} (hx : Enc x p) : Enc ((w : ℝ) * x) (emul w p) :=
  Enc.mulQ w hx

/-! ### `log ‖z‖` and `arg z` of a Gaussian rational -/

/-- `(log ‖z‖, arg z)` enclosures of a Gaussian rational. -/
def lgA (nL nA : ℕ) (z : GQ) : Option ((ℚ × ℚ) × (ℚ × ℚ)) :=
  match logQ nL (z.re * z.re + z.im * z.im), argQ nA z.re z.im with
  | some l, some a => some ((l.1 / 2, l.2 / 2), a)
  | _, _ => none

theorem lgA_spec {nL nA : ℕ} {z : GQ} {L A : ℚ × ℚ} (h : lgA nL nA z = some (L, A)) :
    Enc (Real.log ‖GQ.toC z‖) L ∧ Enc (Complex.arg (GQ.toC z)) A := by
  unfold lgA at h
  split at h
  · rename_i l a hl ha
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨hpos, hE⟩ := logQ_spec hl
    refine ⟨?_, argQ_spec ha⟩
    have hq : (0 : ℝ) < (z.re : ℝ) * z.re + (z.im : ℝ) * z.im := by exact_mod_cast hpos
    have hz : GQ.toC z ≠ 0 := by
      intro h0
      have h1 : (z.re : ℝ) = 0 := by simpa [GQ.toC] using congrArg Complex.re h0
      have h2 : (z.im : ℝ) = 0 := by simpa [GQ.toC] using congrArg Complex.im h0
      rw [h1, h2] at hq; simp at hq
    have hn : 0 < ‖GQ.toC z‖ := norm_pos_iff.2 hz
    have h2 : Real.log ‖GQ.toC z‖ = Real.log (((z.re * z.re + z.im * z.im : ℚ)) : ℝ) / 2 := by
      have e : ‖GQ.toC z‖ ^ 2 = (((z.re * z.re + z.im * z.im : ℚ)) : ℝ) := by
        rw [Complex.sq_norm, Complex.normSq_apply]; simp [GQ.toC]
      have := congrArg Real.log e
      rw [Real.log_pow] at this
      push_cast at this ⊢
      linarith
    unfold Enc at hE ⊢
    dsimp only at hE ⊢
    rw [h2]
    have : Real.log (((z.re * z.re + z.im * z.im : ℚ)) : ℝ) / 2 - ((l.1 / 2 : ℚ) : ℝ) =
        (Real.log (((z.re * z.re + z.im * z.im : ℚ)) : ℝ) - (l.1 : ℝ)) / 2 := by push_cast; ring
    rw [this, abs_div, abs_two]
    push_cast at hE ⊢
    linarith
  · simp at h

theorem re_mul_log (α z : ℂ) :
    (α * Complex.log z).re = α.re * Real.log ‖z‖ - α.im * Complex.arg z := by
  simp [Complex.mul_re, Complex.log_re, Complex.log_im]

/-! ### The V tower at a rational point -/

/-- `Ψ̃ = 5 s log s - 3 (s-2) log (2-s) - 2 (s+6) log (s+6) + 6 + π i (6 - s)` for Lai. -/
theorem psiT_lai (s : ℂ) : psiT 3 2 2 6 (2 * Real.pi) s =
    5 * s * Complex.log s + (-3 * (s - 2)) * Complex.log (2 - s) +
      (-2 * (s + 6)) * Complex.log (s + 6) + 6 + (Real.pi : ℂ) * Complex.I * (6 - s) := by
  unfold psiT
  push_cast
  ring

/-- the rational derivative chain `D̃_k` of `Ψ̃`, with `D̃_1 = d1` supplied. -/
def vD (s d1 : GQ) : ℕ → GQ
  | 0 => ⟨0, 0⟩
  | 1 => d1
  | n + 2 => GQ.sc (n.factorial : ℚ) (GQ.sub (GQ.add
      (GQ.sc (5 * (-1) ^ n) (GQ.pw (GQ.inv s) (n + 1)))
      (GQ.sc 3 (GQ.pw (GQ.inv (GQ.sub ⟨2, 0⟩ s)) (n + 1))))
      (GQ.sc (2 * (-1) ^ n) (GQ.pw (GQ.inv (GQ.add s ⟨6, 0⟩)) (n + 1))))

theorem toC_vD (s d1 : GQ) (n : ℕ) :
    GQ.toC (vD s d1 (n + 2)) = psiTower 3 2 2 6 (2 * Real.pi) (n + 2) (GQ.toC s) := by
  simp only [vD, psiTower, GQ.toC_sc, GQ.toC_sub, GQ.toC_add, GQ.toC_pw, GQ.toC_inv, toC_const]
  push_cast
  simp only [inv_pow, div_eq_mul_inv]
  ring

/-- the enclosure data of the V tower at `s`: `(Ψ̃ real part + 0, Re D1, Im D1)` -/
def vEncOut (nL nA : ℕ) (κE : ℚ × ℚ) (s : GQ) : Option ((ℚ × ℚ) × (ℚ × ℚ) × (ℚ × ℚ)) :=
  match lgA nL nA s, lgA nL nA (GQ.sub ⟨2, 0⟩ s), lgA nL nA (GQ.add s ⟨6, 0⟩) with
  | some (L1, A1), some (L2, A2), some (L3, A3) =>
    let P : ℚ × ℚ := (4 * PI4, 4 * PI4E)
    some (
      eadd (eadd (eadd (eadd (eadd κE (6, 0)) (emul s.im P))
        (esub (emul (5 * s.re) L1) (emul (5 * s.im) A1)))
        (esub (emul (-3 * (s.re - 2)) L2) (emul (-3 * s.im) A2)))
        (esub (emul (-2 * (s.re + 6)) L3) (emul (-2 * s.im) A3)),
      esub (esub (emul 5 L1) (emul 3 L2)) (emul 2 L3),
      esub (esub (esub (emul 5 A1) (emul 3 A2)) (emul 2 A3)) P)
  | _, _, _ => none

theorem pi_enc : Enc Real.pi (4 * PI4, 4 * PI4E) := by
  have h := pi4_spec
  unfold Enc at h ⊢
  have e : Real.pi - ((4 * PI4 : ℚ) : ℝ) = 4 * (Real.pi / 4 - (PI4 : ℝ)) := by push_cast; ring
  rw [e, abs_mul]
  push_cast
  have : |(4 : ℝ)| = 4 := by norm_num
  rw [this]
  linarith

def vTq (s d1 : GQ) (Y : ℕ → GQ) (j : ℕ) : ℚ := (fdbG (vD s d1) Y j).re
def vTe (eu ev : ℚ) (Y : ℕ → GQ) (j : ℕ) : ℚ := eu * |(Y j).re| + ev * |(Y j).im|

theorem fdb_congr_Y (D Y Y' : ℕ → ℂ) (hY : ∀ i, 1 ≤ i → i ≤ 4 → Y i = Y' i) (j : ℕ)
    (hj : j ≤ 4) : fdb D Y j = fdb D Y' j := by
  have h1 := hY 1 (by norm_num) (by norm_num)
  have h2 := hY 2 (by norm_num) (by norm_num)
  have h3 := hY 3 (by norm_num) (by norm_num)
  have h4 := hY 4 (by norm_num) (by norm_num)
  interval_cases j <;> simp only [fdb, h1, h2, h3, h4]


theorem psiTower_one_re (s : ℂ) : (psiTower 3 2 2 6 (2 * Real.pi) 1 s).re =
    5 * Real.log ‖s‖ - 3 * Real.log ‖2 - s‖ - 2 * Real.log ‖s + 6‖ := by
  simp only [psiTower]
  simp [Complex.log_re]
  left; norm_num

theorem psiTower_one_im (s : ℂ) : (psiTower 3 2 2 6 (2 * Real.pi) 1 s).im =
    5 * Complex.arg s - 3 * Complex.arg (2 - s) - 2 * Complex.arg (s + 6) - Real.pi := by
  simp only [psiTower]
  simp [Complex.log_im]
  ring

theorem vD1_part {s : GQ} {Dr Di : ℚ × ℚ}
    (hre : Enc (psiTower 3 2 2 6 (2 * Real.pi) 1 (GQ.toC s)).re Dr)
    (him : Enc (psiTower 3 2 2 6 (2 * Real.pi) 1 (GQ.toC s)).im Di)
    {γ : ℕ → ℝ → ℂ} {a : ℝ} (hs : γ 0 a = GQ.toC s) {Y : ℕ → GQ}
    (hY : ∀ i, 1 ≤ i → i ≤ 4 → γ i a = GQ.toC (Y i)) (j : ℕ) (hj1 : 1 ≤ j) (hj4 : j ≤ 4) :
    |(fdb (fun k => psiTower 3 2 2 6 (2 * Real.pi) k (γ 0 a)) (fun i => γ i a) j).re -
        ((vTq s ⟨Dr.1, Di.1⟩ Y j : ℚ) : ℝ)| ≤ ((vTe Dr.2 Di.2 Y j : ℚ) : ℝ) := by
  set d1 : GQ := ⟨Dr.1, Di.1⟩ with hd1
  set Dc : ℕ → ℂ := fun k => psiTower 3 2 2 6 (2 * Real.pi) k (GQ.toC s) with hDc
  set Dt : ℕ → ℂ := fun k => GQ.toC (vD s d1 k) with hDt
  have hD : ∀ k, 2 ≤ k → Dc k = Dt k := by
    intro k hk
    obtain ⟨n, rfl⟩ : ∃ n, k = n + 2 := ⟨k - 2, by omega⟩
    exact (toC_vD s d1 n).symm
  have e1 : fdb (fun k => psiTower 3 2 2 6 (2 * Real.pi) k (γ 0 a)) (fun i => γ i a) j =
      fdb Dc (fun i => GQ.toC (Y i)) j := by
    rw [hs]
    exact fdb_congr_Y _ _ _ hY j hj4
  have e2 := fdb_sub_D1 Dc Dt (fun i => GQ.toC (Y i)) hD j hj1 hj4
  have e3 : GQ.toC (fdbG (vD s d1) Y j) = fdb Dt (fun i => GQ.toC (Y i)) j :=
    toC_fdbG (vD s d1) Y j hj1 hj4
  have e4 : ((vTq s d1 Y j : ℚ) : ℝ) = (fdb Dt (fun i => GQ.toC (Y i)) j).re := by
    rw [← e3]; simp [vTq, GQ.toC]
  rw [e1, e4, ← Complex.sub_re, e2, Complex.mul_re]
  have h1 : Dc 1 - Dt 1 = ⟨(Dc 1).re - (Dr.1 : ℝ), (Dc 1).im - (Di.1 : ℝ)⟩ := by
    apply Complex.ext <;> simp [hDt, vD, hd1, GQ.toC]
  rw [h1]
  simp only [vTe, GQ.toC, Rat.cast_add, Rat.cast_mul, Rat.cast_abs]
  unfold Enc at hre him
  have a1 : |((Dc 1).re - (Dr.1 : ℝ)) * (Y j).re| ≤ (Dr.2 : ℝ) * |((Y j).re : ℝ)| := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_right hre (abs_nonneg _)
  have a2 : |((Dc 1).im - (Di.1 : ℝ)) * (Y j).im| ≤ (Di.2 : ℝ) * |((Y j).im : ℝ)| := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_right him (abs_nonneg _)
  calc _ ≤ |((Dc 1).re - (Dr.1 : ℝ)) * (Y j).re| + |((Dc 1).im - (Di.1 : ℝ)) * (Y j).im| :=
        abs_sub _ _
    _ ≤ _ := by simpa using add_le_add a1 a2

theorem vTower_encQ {nL nA : ℕ} {κ : ℝ} {κE t0 d1r d1i : ℚ × ℚ} (hκ : Enc κ κE) {s : GQ}
    (h : vEncOut nL nA κE s = some (t0, d1r, d1i)) {γ : ℕ → ℝ → ℂ} {a : ℝ}
    (hs : γ 0 a = GQ.toC s) {Y : ℕ → GQ} (hY : ∀ i, 1 ≤ i → i ≤ 4 → γ i a = GQ.toC (Y i)) :
    Enc (vTower 3 2 2 6 (2 * Real.pi) κ γ 0 a) t0 ∧
    ∀ j, 1 ≤ j → j ≤ 4 →
      |vTower 3 2 2 6 (2 * Real.pi) κ γ j a - ((vTq s ⟨d1r.1, d1i.1⟩ Y j : ℚ) : ℝ)| ≤
        ((vTe d1r.2 d1i.2 Y j : ℚ) : ℝ) := by
  unfold vEncOut at h
  split at h
  · rename_i L1 A1 L2 A2 L3 A3 hl1 hl2 hl3
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    obtain ⟨EL1, EA1⟩ := lgA_spec hl1
    obtain ⟨EL2, EA2⟩ := lgA_spec hl2
    obtain ⟨EL3, EA3⟩ := lgA_spec hl3
    have z2 : GQ.toC (GQ.sub ⟨2, 0⟩ s) = 2 - GQ.toC s := by rw [GQ.toC_sub, toC_const]; norm_num
    have z3 : GQ.toC (GQ.add s ⟨6, 0⟩) = GQ.toC s + 6 := by rw [GQ.toC_add, toC_const]; norm_num
    rw [z2] at EL2 EA2
    rw [z3] at EL3 EA3
    have hP := pi_enc
    constructor
    · -- value
      have e0 : vTower 3 2 2 6 (2 * Real.pi) κ γ 0 a =
          ((κ + ((6 : ℚ) : ℝ)) + (s.im : ℝ) * Real.pi +
            (((5 * s.re : ℚ) : ℝ) * Real.log ‖GQ.toC s‖ - ((5 * s.im : ℚ) : ℝ) * Complex.arg (GQ.toC s))) +
            (((-3 * (s.re - 2) : ℚ) : ℝ) * Real.log ‖2 - GQ.toC s‖ -
              ((-3 * s.im : ℚ) : ℝ) * Complex.arg (2 - GQ.toC s)) +
            (((-2 * (s.re + 6) : ℚ) : ℝ) * Real.log ‖GQ.toC s + 6‖ -
              ((-2 * s.im : ℚ) : ℝ) * Complex.arg (GQ.toC s + 6)) := by
        simp only [vTower, reTower, if_true, hs, psiT_lai]
        have r1 := re_mul_log (5 * GQ.toC s) (GQ.toC s)
        have r2 := re_mul_log (-3 * (GQ.toC s - 2)) (2 - GQ.toC s)
        have r3 := re_mul_log (-2 * (GQ.toC s + 6)) (GQ.toC s + 6)
        simp only [Complex.add_re, r1, r2, r3]
        simp [GQ.toC]
        push_cast
        ring
      rw [e0]
      exact Enc_add (Enc_add (Enc_add (Enc_add (Enc_add hκ (Enc.const 6)) (Enc_mul s.im hP))
        (Enc_sub (Enc_mul _ EL1) (Enc_mul _ EA1)))
        (Enc_sub (Enc_mul _ EL2) (Enc_mul _ EA2)))
        (Enc_sub (Enc_mul _ EL3) (Enc_mul _ EA3))
    · intro j hj1 hj4
      have hj0 : j ≠ 0 := by omega
      have hre : Enc (psiTower 3 2 2 6 (2 * Real.pi) 1 (GQ.toC s)).re
          (esub (esub (emul 5 L1) (emul 3 L2)) (emul 2 L3)) := by
        rw [psiTower_one_re]
        exact Enc_sub (Enc_sub (by simpa using Enc_mul 5 EL1) (by simpa using Enc_mul 3 EL2))
          (by simpa using Enc_mul 2 EL3)
      have him : Enc (psiTower 3 2 2 6 (2 * Real.pi) 1 (GQ.toC s)).im
          (esub (esub (esub (emul 5 A1) (emul 3 A2)) (emul 2 A3)) (4 * PI4, 4 * PI4E)) := by
        rw [psiTower_one_im]
        exact Enc_sub (Enc_sub (Enc_sub (by simpa using Enc_mul 5 EA1) (by simpa using Enc_mul 3 EA2))
          (by simpa using Enc_mul 2 EA3)) hP
      have key := vD1_part hre him hs hY j hj1 hj4
      have e : vTower 3 2 2 6 (2 * Real.pi) κ γ j a =
          (fdb (fun k => psiTower 3 2 2 6 (2 * Real.pi) k (γ 0 a)) (fun i => γ i a) j).re := by
        simp [vTower, reTower, hj0]
      rw [e]
      exact key
  · simp at h


/-! ### R12 (a): the V part of a cell from rational data -/

/-- the majorant chain of `Ψ̃` for Lai with `π` replaced by `31416/10^4`, rational. -/
def psiDmQ (d1 d2 d3 L1 L2 L3 : ℚ) : ℕ → ℚ
  | 0 => 0
  | 1 => 5 * L1 + 3 * L2 + 2 * L3 + 11 * (31416 / 10000)
  | n + 2 => (n.factorial : ℚ) * (5 / d1 ^ (n + 1) + 3 / d2 ^ (n + 1) + 2 / d3 ^ (n + 1))

theorem psiDm_le {d1 d2 d3 L1 L2 L3 : ℚ} (k : ℕ) :
    psiDm 3 2 (2 * Real.pi) (d1 : ℝ) d2 d3 L1 L2 L3 k ≤ ((psiDmQ d1 d2 d3 L1 L2 L3 k : ℚ) : ℝ) := by
  have hpi := Real.pi_lt_d4
  have hpi0 := Real.pi_pos
  match k with
  | 0 => simp [psiDm, psiDmQ]
  | 1 =>
    simp only [psiDm, psiDmQ]
    push_cast
    have : |2 * Real.pi - 3 * Real.pi| = Real.pi := by
      rw [show 2 * Real.pi - 3 * Real.pi = -Real.pi by ring, abs_neg, abs_of_pos hpi0]
    rw [show ((3 : ℝ) * Real.pi) = (3 : ℝ) * Real.pi from rfl]
    norm_num
    have e : |2 * Real.pi - 3 * Real.pi| = Real.pi := this
    linarith
  | n + 2 => exact le_of_eq (by simp only [psiDm, psiDmQ]; push_cast; norm_num)

theorem fdbBound_mono {Dm Dm' Ym Ym' : ℕ → ℝ} (hD0 : ∀ k, 1 ≤ k → k ≤ 5 → 0 ≤ Dm k)
    (hY0 : ∀ i, 1 ≤ i → i ≤ 5 → 0 ≤ Ym i)
    (hD : ∀ k, 1 ≤ k → k ≤ 5 → Dm k ≤ Dm' k) (hY : ∀ i, 1 ≤ i → i ≤ 5 → Ym i ≤ Ym' i) :
    fdbBound Dm Ym ≤ fdbBound Dm' Ym' := by
  have d1 := hD 1 (by norm_num) (by norm_num); have d2 := hD 2 (by norm_num) (by norm_num)
  have d3 := hD 3 (by norm_num) (by norm_num); have d4 := hD 4 (by norm_num) (by norm_num)
  have d5 := hD 5 (by norm_num) (by norm_num)
  have y1 := hY 1 (by norm_num) (by norm_num); have y2 := hY 2 (by norm_num) (by norm_num)
  have y3 := hY 3 (by norm_num) (by norm_num); have y4 := hY 4 (by norm_num) (by norm_num)
  have y5 := hY 5 (by norm_num) (by norm_num)
  have e1 := hD0 1 (by norm_num) (by norm_num); have e2 := hD0 2 (by norm_num) (by norm_num)
  have e3 := hD0 3 (by norm_num) (by norm_num); have e4 := hD0 4 (by norm_num) (by norm_num)
  have e5 := hD0 5 (by norm_num) (by norm_num)
  have z1 := hY0 1 (by norm_num) (by norm_num); have z2 := hY0 2 (by norm_num) (by norm_num)
  have z3 := hY0 3 (by norm_num) (by norm_num); have z4 := hY0 4 (by norm_num) (by norm_num)
  have z5 := hY0 5 (by norm_num) (by norm_num)
  have p1 := e1.trans d1; have p2 := e2.trans d2; have p3 := e3.trans d3; have p4 := e4.trans d4
  have p5 := e5.trans d5; have q1 := z1.trans y1; have q2 := z2.trans y2; have q3 := z3.trans y3
  have q4 := z4.trans y4; have q5 := z5.trans y5
  unfold fdbBound
  gcongr

/-- one pole of a cell: `q ≤ ‖P‖`-side data.  `n = |P|²`, `q² ≤ n ≤ p²`, `b ≥ Ym₁ ρ`; returns `L`
with `-L ≤ log (q - b)` and `log (p + b) ≤ L`. -/
def vPole (nL : ℕ) (n q p b : ℚ) : Option ℚ :=
  if 0 < q - b ∧ 0 ≤ b ∧ 0 ≤ p ∧ q * q ≤ n ∧ n ≤ p * p then
    match logQ nL (q - b), logQ nL (p + b) with
    | some (v, e), some (v', e') => some (max 0 (max (e - v) (v' + e')))
    | _, _ => none
  else none

theorem vPole_spec {nL : ℕ} {n q p b L : ℚ} {P : ℂ} (hP : ‖P‖ ^ 2 = (n : ℝ))
    (h : vPole nL n q p b = some L) {w : ℝ} (hw0 : 0 ≤ w) (hw : w ≤ (b : ℝ)) :
    0 < ((q - b : ℚ) : ℝ) ∧ ((q - b : ℚ) : ℝ) ≤ ‖P‖ - w ∧ (0 : ℝ) ≤ L ∧
      -(L : ℝ) ≤ Real.log ((q - b : ℚ) : ℝ) ∧ Real.log (‖P‖ + w) ≤ (L : ℝ) := by
  unfold vPole at h
  split_ifs at h with hc
  obtain ⟨hqb, hb0, hp0q, hqn, hnp⟩ := hc
  split at h
  · rename_i v e v' e' h1 h2
    simp only [Option.some.injEq] at h
    subst h
    obtain ⟨hq0, E1⟩ := logQ_spec h1
    obtain ⟨hp0, E2⟩ := logQ_spec h2
    have hqb' : (0 : ℝ) < ((q - b : ℚ) : ℝ) := by exact_mod_cast hqb
    have hb0' : (0 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb0
    have hqn' : ((q : ℝ)) * q ≤ (n : ℝ) := by exact_mod_cast hqn
    have hnp' : (n : ℝ) ≤ (p : ℝ) * p := by exact_mod_cast hnp
    have hq0' : (0 : ℝ) < (q : ℝ) := by
      have : ((q : ℝ)) - b > 0 := by simpa using hqb'
      linarith
    have hN : 0 ≤ ‖P‖ := norm_nonneg _
    have hqle : (q : ℝ) ≤ ‖P‖ := by
      by_contra hlt
      push_neg at hlt
      nlinarith [hP, hqn', hN, hq0', mul_pos (sub_pos.2 hlt) (add_pos_of_pos_of_nonneg hq0' hN)]
    have hple : ‖P‖ ≤ (p : ℝ) := by
      have hp0 : (0 : ℝ) ≤ p := by exact_mod_cast hp0q
      by_contra hlt
      push_neg at hlt
      nlinarith [hP, hnp', hN, hp0, mul_pos (sub_pos.2 hlt) (add_pos_of_pos_of_nonneg (lt_of_le_of_lt hp0 hlt) hN)]
    refine ⟨hqb', ?_, by exact_mod_cast le_max_left _ _, ?_, ?_⟩
    · push_cast at hqb' ⊢; linarith
    · have := (abs_le.mp E1).2
      have h2 : -(((max 0 (max (e - v) (v' + e')) : ℚ)) : ℝ) ≤ Real.log ((q - b : ℚ) : ℝ) := by
        have hm : (e - v : ℚ) ≤ max 0 (max (e - v) (v' + e')) :=
          le_trans (le_max_left _ _) (le_max_right _ _)
        have hm' : ((e - v : ℚ) : ℝ) ≤ ((max 0 (max (e - v) (v' + e')) : ℚ) : ℝ) := by exact_mod_cast hm
        have h3 := (abs_le.mp E1).1
        generalize ((max 0 (max (e - v) (v' + e')) : ℚ) : ℝ) = Lr at hm' ⊢
        push_cast at hm' h3 ⊢
        linarith
      exact h2
    · have hpos : 0 < ‖P‖ + w := by
        have : (0 : ℝ) < ((q - b : ℚ) : ℝ) := hqb'
        push_cast at this
        linarith
      have hle : ‖P‖ + w ≤ ((p + b : ℚ) : ℝ) := by push_cast; linarith
      have hl1 := Real.log_le_log hpos hle
      have h3 := (abs_le.mp E2).2
      have hm : (v' + e' : ℚ) ≤ max 0 (max (e - v) (v' + e')) :=
        le_trans (le_max_right _ _) (le_max_right _ _)
      have hm' : ((v' + e' : ℚ) : ℝ) ≤ ((max 0 (max (e - v) (v' + e')) : ℚ) : ℝ) := by exact_mod_cast hm
      generalize ((max 0 (max (e - v) (v' + e')) : ℚ) : ℝ) = Lr at hm' ⊢
      push_cast at hm' h3 hl1 ⊢
      linarith
  · simp at h


def nsq (x : GQ) : ℚ := x.re ^ 2 + x.im ^ 2

theorem norm_sq_toC (x : GQ) : ‖GQ.toC x‖ ^ 2 = ((nsq x : ℚ) : ℝ) := by
  rw [Complex.sq_norm, Complex.normSq_apply]; simp [GQ.toC, nsq]; ring

theorem fdbBound_cast (Dm Ym : ℕ → ℚ) :
    ((fdbBound Dm Ym : ℚ) : ℝ) = fdbBound (fun k => (Dm k : ℝ)) (fun i => (Ym i : ℝ)) := by
  unfold fdbBound; push_cast; rfl

theorem psiDm_nonneg {d1 d2 d3 L1 L2 L3 : ℝ} (hd1 : 0 < d1) (hd2 : 0 < d2) (hd3 : 0 < d3)
    (h1 : 0 ≤ L1) (h2 : 0 ≤ L2) (h3 : 0 ≤ L3) (k : ℕ) :
    0 ≤ psiDm 3 2 (2 * Real.pi) d1 d2 d3 L1 L2 L3 k := by
  have hp := Real.pi_pos
  match k with
  | 0 => simp [psiDm]
  | 1 => simp only [psiDm]; positivity
  | n + 2 => simp only [psiDm]; positivity

/-- **R12 (V part).** The `VCell` of a cell from rational pole data. -/
def mkVCell {nL : ℕ} {z : GQ} {Ym : ℕ → ℝ} {ρ : ℝ} {b : ℚ} (hρ : 0 ≤ ρ)
    (hY0 : ∀ i, 1 ≤ i → i ≤ 5 → 0 ≤ Ym i) (hb : Ym 1 * ρ ≤ (b : ℝ))
    {q1 q2 q3 p1 p2 p3 L1 L2 L3 : ℚ}
    (h1 : vPole nL (nsq z) q1 p1 b = some L1)
    (h2 : vPole nL (nsq (GQ.sub ⟨2, 0⟩ z)) q2 p2 b = some L2)
    (h3 : vPole nL (nsq (GQ.add z ⟨6, 0⟩)) q3 p3 b = some L3)
    {YmQ : ℕ → ℚ} (hYQ : ∀ i, 1 ≤ i → i ≤ 5 → Ym i ≤ (YmQ i : ℝ)) {TV : ℚ}
    (hTV : fdbBound (psiDmQ (q1 - b) (q2 - b) (q3 - b) L1 L2 L3) YmQ ≤ TV) :
    VCell 3 2 2 6 (2 * Real.pi) (GQ.toC z) Ym ρ (TV : ℝ) := by
  have hw0 : 0 ≤ Ym 1 * ρ := mul_nonneg (hY0 1 (by norm_num) (by norm_num)) hρ
  have z2 : GQ.toC (GQ.sub ⟨2, 0⟩ z) = 2 - GQ.toC z := by rw [GQ.toC_sub, toC_const]; norm_num
  have z3 : GQ.toC (GQ.add z ⟨6, 0⟩) = GQ.toC z + 6 := by rw [GQ.toC_add, toC_const]; norm_num
  obtain ⟨a1, b1, c1, d1, e1⟩ := vPole_spec (norm_sq_toC z) h1 hw0 hb
  obtain ⟨a2, b2, c2, d2, e2⟩ := vPole_spec (norm_sq_toC _) h2 hw0 hb
  obtain ⟨a3, b3, c3, d3, e3⟩ := vPole_spec (norm_sq_toC _) h3 hw0 hb
  rw [z2] at b2 e2
  rw [z3] at b3 e3
  refine ⟨((q1 - b : ℚ) : ℝ), ((q2 - b : ℚ) : ℝ), ((q3 - b : ℚ) : ℝ), L1, L2, L3, a1, a2, a3,
    ?_, ?_, ?_, d1, ?_, d2, ?_, d3, ?_, ?_⟩
  · exact b1
  · simpa using b2
  · exact b3
  · exact e1
  · simpa using e2
  · exact e3
  · refine le_trans (fdbBound_mono (fun k _ _ => psiDm_nonneg a1 a2 a3 c1 c2 c3 k) hY0
      (fun k _ _ => psiDm_le k) hYQ) ?_
    have := (Rat.cast_le (K := ℝ)).2 hTV
    rw [fdbBound_cast] at this
    exact this


/-! ### R12 (b): the combined tower enclosure and the A cell at a rational point -/

def wTq (tqV tq1 tq2 : ℕ → ℚ) (j : ℕ) : ℚ := tqV j + (-2) * tq1 j + (-2) * tq2 j
def wTe (teV te1 te2 : ℕ → ℚ) (j : ℕ) : ℚ := teV j + |(-2 : ℚ)| * te1 j + |(-2 : ℚ)| * te2 j

/-- the V tower data `(tq, te)` for `j ≤ 4` from `vEncOut`. -/
def vTW (t0 d1r d1i : ℚ × ℚ) (s : GQ) (Y : ℕ → GQ) : (ℕ → ℚ) × (ℕ → ℚ) :=
  (fun j => if j = 0 then t0.1 else vTq s ⟨d1r.1, d1i.1⟩ Y j,
   fun j => if j = 0 then t0.2 else vTe d1r.2 d1i.2 Y j)

theorem cell_tenc {nL nA : ℕ} {κ : ℝ} {κE t0 d1r d1i : ℚ × ℚ} (hκ : Enc κ κE) {s : GQ}
    (hv : vEncOut nL nA κE s = some (t0, d1r, d1i)) {γ : ℕ → ℝ → ℂ} {a : ℝ}
    (hs : γ 0 a = GQ.toC s) {Y : ℕ → GQ} (hY : ∀ i, 1 ≤ i → i ≤ 4 → γ i a = GQ.toC (Y i))
    {f₁ f₂ : ℕ → ℝ → ℝ} {tq1 te1 tq2 te2 : ℕ → ℚ}
    (h1 : ∀ j ≤ 4, |f₁ j a - (tq1 j : ℝ)| ≤ (te1 j : ℝ))
    (h2 : ∀ j ≤ 4, |f₂ j a - (tq2 j : ℝ)| ≤ (te2 j : ℝ)) :
    ∀ j ≤ 4, |wedgeTower (vTower 3 2 2 6 (2 * Real.pi) κ γ) f₁ f₂ (((-2 : ℚ)) : ℝ) (((-2 : ℚ)) : ℝ) j a -
        ((wTq (vTW t0 d1r d1i s Y).1 tq1 tq2 j : ℚ) : ℝ)| ≤
      ((wTe (vTW t0 d1r d1i s Y).2 te1 te2 j : ℚ) : ℝ) := by
  intro j hj
  obtain ⟨v0, vj⟩ := vTower_encQ hκ hv hs hY
  have hV : |vTower 3 2 2 6 (2 * Real.pi) κ γ j a - (((vTW t0 d1r d1i s Y).1 j : ℚ) : ℝ)| ≤
      (((vTW t0 d1r d1i s Y).2 j : ℚ) : ℝ) := by
    by_cases hj0 : j = 0
    · subst hj0; simpa [vTW, Enc] using v0
    · have := vj j (by omega) hj
      simpa [vTW, hj0] using this
  have := wedgeTower_enc (fV := vTower 3 2 2 6 (2 * Real.pi) κ γ) (f₁ := f₁) (f₂ := f₂) (a := a)
    (-2) (-2) (tqV := (vTW t0 d1r d1i s Y).1) (teV := (vTW t0 d1r d1i s Y).2) (tq1 := tq1)
    (te1 := te1) (tq2 := tq2) (te2 := te2) (j := j) hV (h1 j hj) (h2 j hj)
  simpa [wTq, wTe] using this

theorem cos_two_arctan_q (τ : ℚ) :
    (((1 - τ ^ 2) / (1 + τ ^ 2) : ℚ) : ℝ) = Real.cos (2 * Real.arctan (τ : ℝ)) ∧
    (((2 * τ) / (1 + τ ^ 2) : ℚ) : ℝ) = Real.sin (2 * Real.arctan (τ : ℝ)) := by
  obtain ⟨h1, h2⟩ := trig_two_arctan (τ : ℝ)
  rw [h1, h2]; push_cast; exact ⟨rfl, rfl⟩


theorem armA_rat (M h : ℂ) {a : ℝ} {cc sn : ℚ} (hc : (cc : ℝ) = Real.cos a)
    (hs : (sn : ℝ) = Real.sin a) (i : ℕ) :
    armA M h i a = (if i = 0 then M else 0) + h * ((cosJ cc sn i : ℚ) : ℂ) := by
  unfold armA
  rw [← cosJ_spec hc hs i]
  simp

/-- the rational sum `Σ_{k<N} |c_{k+1}| (k+1)^4` -/
def ownSumQ (cq : ℕ → ℚ) (N : ℕ) : ℚ := ∑ k ∈ Finset.range N, |cq (k + 1)| * ((k + 1 : ℕ) : ℚ) ^ 4

/-- **R12 (A kind).**  A cell at the rational-trigonometry point `a' = 2 arctan τ`. -/
theorem cellA_rat {c : ℕ → ℝ} {N : ℕ} (hpos : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ chebF c N x)
    {M h : ℂ} (hh : h ≠ 0) (hMh : |h.im| < M.im) {Mq hq : GQ} (hM : GQ.toC Mq = M)
    (hH : GQ.toC hq = h) (τ : ℚ) {ρ' : ℚ} (hρ' : 0 ≤ ρ')
    {nL nA : ℕ} {κE t0 d1r d1i : ℚ × ℚ}
    (hκ : Enc (2 * (6 * Real.log 6 - 6) - 3 * (2 * Real.log 2 - 2)) κE)
    (hv : vEncOut nL nA κE
      ⟨Mq.re + hq.re * ((1 - τ ^ 2) / (1 + τ ^ 2)), Mq.im + hq.im * ((1 - τ ^ 2) / (1 + τ ^ 2))⟩ =
        some (t0, d1r, d1i))
    {K0q eK : ℚ} (hK0 : |(-c 0 * Real.log ‖h‖ + c 0 * Real.log 2) - (K0q : ℝ)| ≤ (eK : ℝ))
    {cq : ℕ → ℚ} (hcq : ∀ k < N, (cq (k + 1) : ℝ) = c (k + 1))
    {M₂ h₂ : ℂ} (hh₂ : h₂ ≠ 0) {c₂ : ℕ → ℝ} {N₂ : ℕ}
    (hpos₂ : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ chebF c₂ N₂ x) {tq2 te2 : ℕ → ℚ}
    (hseg : ∀ j ≤ 4, |potT M₂ h₂ c₂ N₂ (armA M h) j (2 * Real.arctan (τ : ℝ)) - (tq2 j : ℝ)| ≤
      (te2 j : ℝ))
    {T2q : ℚ}
    (hX : SegCell (armA M h 0 (2 * Real.arctan (τ : ℝ))) (fun _ => ‖h‖) (ρ' : ℝ) M₂ h₂ (c₂ 0)
      (T2q : ℝ))
    {bh : ℚ} (hbh : ‖h‖ ≤ (bh : ℝ)) {q1 q2 q3 p1 p2 p3 L1 L2 L3 : ℚ}
    (h1 : vPole nL (nsq ⟨Mq.re + hq.re * ((1 - τ ^ 2) / (1 + τ ^ 2)),
        Mq.im + hq.im * ((1 - τ ^ 2) / (1 + τ ^ 2))⟩) q1 p1 (bh * ρ') = some L1)
    (h2 : vPole nL (nsq (GQ.sub ⟨2, 0⟩ ⟨Mq.re + hq.re * ((1 - τ ^ 2) / (1 + τ ^ 2)),
        Mq.im + hq.im * ((1 - τ ^ 2) / (1 + τ ^ 2))⟩)) q2 p2 (bh * ρ') = some L2)
    (h3 : vPole nL (nsq (GQ.add ⟨Mq.re + hq.re * ((1 - τ ^ 2) / (1 + τ ^ 2)),
        Mq.im + hq.im * ((1 - τ ^ 2) / (1 + τ ^ 2))⟩ ⟨6, 0⟩)) q3 p3 (bh * ρ') = some L3)
    {TV : ℚ}
    (hTV : fdbBound (psiDmQ (q1 - bh * ρ') (q2 - bh * ρ') (q3 - bh * ρ') L1 L2 L3) (fun _ => bh) ≤ TV)
    {TR ℓ : ℚ} (hTR : TV + 2 * ownSumQ cq N + 2 * T2q ≤ TR)
    (hok : wedgeCellOk
      (wTq (vTW t0 d1r d1i ⟨Mq.re + hq.re * ((1 - τ ^ 2) / (1 + τ ^ 2)),
          Mq.im + hq.im * ((1 - τ ^ 2) / (1 + τ ^ 2))⟩
        (fun i => GQ.sc (cosJ ((1 - τ ^ 2) / (1 + τ ^ 2)) (2 * τ / (1 + τ ^ 2)) i) hq)).1
        (fun j => ownATr K0q cq N j ((1 - τ ^ 2) / (1 + τ ^ 2)) (2 * τ / (1 + τ ^ 2))) tq2)
      (wTe (vTW t0 d1r d1i ⟨Mq.re + hq.re * ((1 - τ ^ 2) / (1 + τ ^ 2)),
          Mq.im + hq.im * ((1 - τ ^ 2) / (1 + τ ^ 2))⟩
        (fun i => GQ.sc (cosJ ((1 - τ ^ 2) / (1 + τ ^ 2)) (2 * τ / (1 + τ ^ 2)) i) hq)).2
        (fun j => if j = 0 then eK else 0) te2) TR ρ' ℓ = true) :
    ∀ x ∈ Icc (2 * Real.arctan (τ : ℝ) - ρ') (2 * Real.arctan (τ : ℝ) + ρ'),
      vAnal 3 2 2 6 (2 * Real.pi) (M + h * (Real.cos x : ℂ)) +
        (-2) * logPotC (segMeasure M h c N) (M + h * (Real.cos x : ℂ)) +
        (-2) * logPotC (segMeasure M₂ h₂ c₂ N₂) (M + h * (Real.cos x : ℂ)) ≤ (ℓ : ℝ) := by
  set cc : ℚ := (1 - τ ^ 2) / (1 + τ ^ 2) with hcc
  set sn : ℚ := 2 * τ / (1 + τ ^ 2) with hsn
  set a : ℝ := 2 * Real.arctan (τ : ℝ) with ha
  obtain ⟨hc, hs⟩ := cos_two_arctan_q τ
  rw [← hcc] at hc
  rw [← hsn] at hs
  set sq : GQ := ⟨Mq.re + hq.re * cc, Mq.im + hq.im * cc⟩ with hsq
  set Yq : ℕ → GQ := fun i => GQ.sc (cosJ cc sn i) hq with hYq
  have hz : armA M h 0 a = GQ.toC sq := by
    rw [armA_rat M h hc hs 0, if_pos rfl, ← hM, ← hH, hsq]
    apply Complex.ext <;> simp [GQ.toC, cosJ] <;> (try ring)
  have hYi : ∀ i, 1 ≤ i → i ≤ 4 → armA M h i a = GQ.toC (Yq i) := by
    intro i hi _
    rw [armA_rat M h hc hs i, if_neg (by omega), zero_add, hYq, GQ.toC_sc, hH]
    try simp
    try ring
  have hρ : (0 : ℝ) ≤ (ρ' : ℝ) := by exact_mod_cast hρ'
  have hY0 : ∀ i, 1 ≤ i → i ≤ 5 → 0 ≤ (fun _ : ℕ => ‖h‖) i := fun i _ _ => norm_nonneg _
  have hb : (fun _ : ℕ => ‖h‖) 1 * (ρ' : ℝ) ≤ ((bh * ρ' : ℚ) : ℝ) := by
    push_cast
    exact mul_le_mul_of_nonneg_right hbh hρ
  have hV := mkVCell (nL := nL) (z := sq) (Ym := fun _ => ‖h‖) (ρ := (ρ' : ℝ)) hρ hY0 hb
    h1 h2 h3 (YmQ := fun _ => bh) (fun i _ _ => hbh) hTV
  rw [← hz] at hV
  have hTenc := cell_tenc (γ := armA M h) (a := a) (f₁ := ownAT (-c 0 * Real.log ‖h‖ + c 0 * Real.log 2) c N)
    (f₂ := potT M₂ h₂ c₂ N₂ (armA M h)) hκ hv hz hYi
    (tq1 := fun j => ownATr K0q cq N j cc sn) (te1 := fun j => if j = 0 then eK else 0)
    (fun j _ => by
      have := ownAT_enc_rot (K0 := -c 0 * Real.log ‖h‖ + c 0 * Real.log 2) (N := N) hK0 hcq hc hs j
      by_cases hj0 : j = 0 <;> simpa [hj0] using this)
    hseg
  have hhd : ∀ x ∈ Icc (a - ρ') (a + ρ'), psiDom 2 6 (M + h * (Real.cos x : ℂ)) :=
    fun x _ => psiDom_of_im_pos 2 6 (armA_im_pos hMh x)
  have key := cellA_sound 3 2 2 6 (2 * Real.pi) (((-2 : ℚ)) : ℝ) (((-2 : ℚ)) : ℝ) (by norm_num)
    (by norm_num) hh hpos hhd hV hh₂ hpos₂ hX (rq := ρ') (ℓ := ℓ) rfl
    (by simpa using hTenc) ?_ hok
  · intro x hx
    have := key x hx
    simpa using this
  · -- the remainder
    have hs1 : ∑ k ∈ Finset.range N, |c (k + 1)| * ((k + 1 : ℕ) : ℝ) ^ 4 = (ownSumQ cq N : ℝ) := by
      unfold ownSumQ
      push_cast
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [hcq k (Finset.mem_range.1 hk)]
    rw [hs1]
    have := (Rat.cast_le (K := ℝ)).2 hTR
    push_cast at this ⊢
    simp only [abs_neg, abs_two, Rat.cast_neg, Rat.cast_ofNat]
    linarith


/-! ### R9 (d): the cell theorem with the own potential identified only for `x ≥ 0` -/

theorem wedgeField_cell_sound_nn (e r B K θ w₁ w₂ : ℝ) (he : 0 ≤ e) (hr : 0 ≤ r)
    {γ : ℕ → ℝ → ℂ} (hγd : ∀ i < 5, ∀ x, HasDerivAt (γ i) (γ (i + 1) x) x)
    (hγc : Continuous (γ 5)) {a ρ : ℝ} {Ym : ℕ → ℝ}
    (hY : ∀ x ∈ Icc (a - ρ) (a + ρ), ∀ i, 1 ≤ i → i ≤ 5 → ‖γ i x‖ ≤ Ym i)
    (hdom : ∀ x ∈ Icc (a - ρ) (a + ρ), psiDom B K (γ 0 x))
    {TV T1 T2 : ℝ} (hV : VCell e r B K θ (γ 0 a) Ym ρ TV)
    {U₁ : ℝ → ℝ} {f₁ : ℕ → ℝ → ℝ} (hf₁ : IsTower f₁ a ρ 5)
    (hU₁ : ∀ x ∈ Icc (a - ρ) (a + ρ), 0 ≤ x → U₁ x = f₁ 0 x)
    (hT1 : ∀ x ∈ Icc (a - ρ) (a + ρ), |f₁ 5 x| ≤ T1)
    {M₂ h₂ : ℂ} (hh₂ : h₂ ≠ 0) {c₂ : ℕ → ℝ} {N₂ : ℕ}
    (hpos₂ : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ chebF c₂ N₂ x) (hX : SegCell (γ 0 a) Ym ρ M₂ h₂ (c₂ 0) T2)
    {tq te : ℕ → ℚ} {TR rq ℓ : ℚ} (hrq : (rq : ℝ) = ρ)
    (hTenc : ∀ j ≤ 4,
      |wedgeTower (vTower e r B K θ (r * (K * Real.log K - K) - e * (B * Real.log B - B)) γ) f₁
        (potT M₂ h₂ c₂ N₂ γ) w₁ w₂ j a - (tq j : ℝ)| ≤ (te j : ℝ))
    (hTR : TV + |w₁| * T1 + |w₂| * T2 ≤ (TR : ℝ))
    (hok : wedgeCellOk tq te TR rq ℓ = true) :
    ∀ x ∈ Icc (a - ρ) (a + ρ), 0 ≤ x →
      vAnal e r B K θ (γ 0 x) + w₁ * U₁ x +
        w₂ * logPotC (segMeasure M₂ h₂ c₂ N₂) (γ 0 x) ≤ (ℓ : ℝ) := by
  set κV : ℝ := r * (K * Real.log K - K) - e * (B * Real.log B - B) with hκV
  have hS : ∀ x ∈ Icc (a - ρ) (a + ρ), ‖γ 1 x‖ ≤ Ym 1 := fun x hx =>
    hY x hx 1 le_rfl (by norm_num)
  have hVt := isTower_vTower e r B K θ κV hγd hγc hdom
  have hdl : ∀ x ∈ Icc (a - ρ) (a + ρ), hX.dlo ≤ ‖h₂‖ * (jc ((γ 0 x - M₂) / h₂) - 1) :=
    fun x hx => dlo_cell hh₂ (fun y => hγd 0 (by norm_num) y) hS hX.hdlo hx
  have hreg : ∀ x ∈ Icc (a - ρ) (a + ρ), 1 < jc ((γ 0 x - M₂) / h₂) := fun x hx =>
    one_lt_jc_of_dlo hh₂ hX.hdlo0 (hdl x hx)
  have hXt := isTower_potT hh₂ hpos₂ hγd hγc hreg
  have hf := isTower_wedgeTower (w₁ := w₁) (w₂ := w₂) hVt hf₁ hXt
  have hTRx : ∀ x ∈ Icc (a - ρ) (a + ρ),
      |wedgeTower (vTower e r B K θ κV γ) f₁ (potT M₂ h₂ c₂ N₂ γ) w₁ w₂ 5 x| ≤ (TR : ℝ) := by
    intro x hx
    obtain ⟨p1l, p1u⟩ := pole_cell_bounds hγd hS 0 hx
    obtain ⟨p2l, p2u⟩ := pole_cell_bounds hγd hS (B : ℂ) hx
    obtain ⟨p3l, p3u⟩ := pole_cell_bounds hγd hS (-(K : ℂ)) hx
    simp only [sub_zero, sub_neg_eq_add] at p1l p1u p3l p3u
    rw [norm_sub_rev (γ 0 a) (B : ℂ), norm_sub_rev (γ 0 x) (B : ℂ)] at p2l p2u
    have hv := abs_vTower5_le e r B K θ κV he hr hV.hd1 hV.hd2 hV.hd3
      (hV.hdc1.trans p1l) (hV.hdc2.trans p2l) (hV.hdc3.trans p3l)
      (abs_log_le_of_bounds hV.hd1 (hV.hdc1.trans p1l) p1u hV.hLa1 hV.hLb1)
      (abs_log_le_of_bounds hV.hd2 (hV.hdc2.trans p2l) p2u hV.hLa2 hV.hLb2)
      (abs_log_le_of_bounds hV.hd3 (hV.hdc3.trans p3l) p3u hV.hLa3 hV.hLb3) (hY x hx)
    have hc := abs_potT5_le hh₂ hpos₂ (hreg x hx) hX.hdlo0 (hdl x hx) (hY x hx)
    have hw := abs_wedgeTower5_le (w₁ := w₁) (w₂ := w₂) hv (hT1 x hx) hc
    have hT2 := hX.hT
    have hTV := hV.hTV
    have hm : |w₂| * fdbBound (fun k => ((k - 1).factorial : ℝ) * c₂ 0 / hX.dlo ^ k) Ym ≤
        |w₂| * T2 := mul_le_mul_of_nonneg_left hT2 (abs_nonneg _)
    linarith
  have hrq' : (rq : ℝ) = ρ := hrq
  have key := wedgeCellOk_sound hf hrq' hTenc hTRx hok
  intro x hx hx0
  have h0 := key x hx
  have e0 : wedgeTower (vTower e r B K θ κV γ) f₁ (potT M₂ h₂ c₂ N₂ γ) w₁ w₂ 0 x =
      vAnal e r B K θ (γ 0 x) + w₁ * U₁ x +
        w₂ * logPotC (segMeasure M₂ h₂ c₂ N₂) (γ 0 x) := by
    unfold wedgeTower
    rw [hU₁ x hx hx0]
    simp [vTower, reTower, potT, hκV, vAnal]
  rw [← e0]
  exact h0



theorem abs_coshT_le'' {i : ℕ} {x y : ℝ} (hxy : |x| ≤ y) :
    |coshT i x| ≤ if i % 2 = 0 then Real.cosh y else Real.sinh y := by
  have hy : 0 ≤ y := (abs_nonneg _).trans hxy
  unfold coshT
  split_ifs
  · rw [abs_of_pos (Real.cosh_pos x)]
    exact Real.cosh_le_cosh.2 (by rw [abs_of_nonneg hy]; exact hxy)
  · rw [Real.abs_sinh]
    exact Real.sinh_le_sinh.2 hxy

theorem norm_armG_le'' (M h : ℂ) {s : ℝ} (hs : |s| = 1) {i : ℕ} (hi : 1 ≤ i) {x y : ℝ}
    (hxy : |x| ≤ y) : ‖armG M h s i x‖ ≤ YmG h y i := by
  have hi0 : i ≠ 0 := by omega
  unfold armG YmG
  rw [if_neg hi0, zero_add, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, hs, one_mul]
  exact mul_le_mul_of_nonneg_left (abs_coshT_le'' hxy) (norm_nonneg _)

/-- **G cell, extended to the left of `0`.**  As `cellG_sound'` but without `0 ≤ a - ρ`: the
conclusion is for the points of the cell with `x ≥ 0`; `|x| ≤ whi` on the cell. -/
theorem cellG_sound_nn (e r B K θ w₁ w₂ : ℝ) (he : 0 ≤ e) (hr : 0 ≤ r) {M h : ℂ} (hh : h ≠ 0)
    {cf : ℕ → ℝ} {N : ℕ} (hpos : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ chebF cf N x) {s : ℝ}
    (hs : s = 1 ∨ s = -1) {a ρ whi : ℝ} (hwhi : ∀ x ∈ Icc (a - ρ) (a + ρ), |x| ≤ whi)
    (hdom : ∀ x ∈ Icc (a - ρ) (a + ρ), psiDom B K (M + h * ((s * Real.cosh x : ℝ) : ℂ)))
    {TV T2 : ℝ}
    (hV : VCell e r B K θ (armG M h s 0 a) (YmG h whi) ρ TV)
    {M₂ h₂ : ℂ} (hh₂ : h₂ ≠ 0) {c₂ : ℕ → ℝ} {N₂ : ℕ}
    (hpos₂ : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ chebF c₂ N₂ x)
    (hX : SegCell (armG M h s 0 a) (YmG h whi) ρ M₂ h₂ (c₂ 0) T2)
    {E : ℕ → ℝ} (hE : ∀ k < N, Real.exp (-(((k + 1 : ℕ) : ℝ) * (a - ρ))) ≤ E k)
    {tq te : ℕ → ℚ} {TR rq ℓ : ℚ} (hrq : (rq : ℝ) = ρ)
    (hTenc : ∀ j ≤ 4,
      |wedgeTower (vTower e r B K θ (r * (K * Real.log K - K) - e * (B * Real.log B - B))
          (armG M h s))
        (ownGT (-cf 0 * Real.log ‖h‖ + cf 0 * Real.log 2) (cf 0) s cf N)
        (potT M₂ h₂ c₂ N₂ (armG M h s)) w₁ w₂ j a - (tq j : ℝ)| ≤ (te j : ℝ))
    (hTR : TV + |w₁| * (∑ k ∈ Finset.range N, |cf (k + 1)| * ((k + 1 : ℕ) : ℝ) ^ 4 * E k) +
      |w₂| * T2 ≤ (TR : ℝ))
    (hok : wedgeCellOk tq te TR rq ℓ = true) :
    ∀ x ∈ Icc (a - ρ) (a + ρ), 0 ≤ x →
      vAnal e r B K θ (M + h * ((s * Real.cosh x : ℝ) : ℂ)) +
        w₁ * logPotC (segMeasure M h cf N) (M + h * ((s * Real.cosh x : ℝ) : ℂ)) +
        w₂ * logPotC (segMeasure M₂ h₂ c₂ N₂) (M + h * ((s * Real.cosh x : ℝ) : ℂ)) ≤ (ℓ : ℝ) := by
  have habs : |s| = 1 := by rcases hs with rfl | rfl <;> simp
  have key := wedgeField_cell_sound_nn e r B K θ w₁ w₂ he hr (γ := armG M h s)
    (fun i _ x => hasDerivAt_armG M h s i x) (continuous_armG M h s 5) (a := a) (ρ := ρ)
    (Ym := YmG h whi)
    (fun x hx i hi _ => norm_armG_le'' M h habs hi (hwhi x hx))
    (fun x hx => by rw [armG_zero]; exact hdom x hx) hV
    (U₁ := fun x => logPotC (segMeasure M h cf N) (M + h * ((s * Real.cosh x : ℝ) : ℂ)))
    (f₁ := ownGT (-cf 0 * Real.log ‖h‖ + cf 0 * Real.log 2) (cf 0) s cf N)
    (isTower_ownGT _ _ s cf N a ρ) (fun x hx hx0 => logPotC_eq_ownGT hh hpos hs hx0)
    (fun x hx => abs_ownGT5_le _ _ s habs cf N x E (fun k hk =>
      (Real.exp_le_exp.2 (by nlinarith [hx.1, (by positivity : (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ))])).trans
        (hE k hk)))
    hh₂ hpos₂ hX hrq hTenc hTR hok
  intro x hx hx0
  have := key x hx hx0
  rw [armG_zero] at this
  exact this


/-- `Σ |c_{k+1}| (k+1)^4 ρl^{k+1}` -/
def ownSumGQ (cq : ℕ → ℚ) (N : ℕ) (ρl : ℚ) : ℚ :=
  ∑ k ∈ Finset.range N, |cq (k + 1)| * ((k + 1 : ℕ) : ℚ) ^ 4 * ρl ^ (k + 1)

/-- cosh / sinh coefficient at `-log ρ` as a rational -/
def chQ (ρ : ℚ) (i : ℕ) : ℚ := if i % 2 = 0 then (ρ + ρ⁻¹) / 2 else (ρ⁻¹ - ρ) / 2

theorem chQ_spec {ρ : ℚ} (hρ : 0 < ρ) (i : ℕ) :
    (if i % 2 = 0 then (((ρ : ℚ) : ℝ) + ((ρ : ℚ) : ℝ)⁻¹) / 2 else (((ρ : ℚ) : ℝ)⁻¹ - (ρ : ℝ)) / 2) =
      ((chQ ρ i : ℚ) : ℝ) := by
  unfold chQ; split_ifs <;> push_cast <;> rfl

/-- **R12 (G kind).**  A G cell at `a' = -log ρq`, `ρq` rational. -/
theorem cellG_rat {c : ℕ → ℝ} {N : ℕ} (hpos : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ chebF c N x)
    {M h : ℂ} (hh : h ≠ 0) {Mq hq : GQ} (hM : GQ.toC Mq = M) (hH : GQ.toC hq = h)
    {sg : ℚ} (hsg : sg = 1 ∨ sg = -1) {ρq ρ' : ℚ} (hρq : 0 < ρq) (hρq1 : ρq ≤ 1) (hρ' : 0 ≤ ρ')
    (hρ'1 : ρ' < 1)
    (hIm : 0 < M.im - |h.im| * ((chQ (ρq * (1 - ρ')) 0 : ℚ) : ℝ))
    {nL nA : ℕ} {κE t0 d1r d1i : ℚ × ℚ}
    (hκ : Enc (2 * (6 * Real.log 6 - 6) - 3 * (2 * Real.log 2 - 2)) κE)
    (hv : vEncOut nL nA κE
      ⟨Mq.re + hq.re * (sg * chQ ρq 0), Mq.im + hq.im * (sg * chQ ρq 0)⟩ = some (t0, d1r, d1i))
    {K0q eK c0q lq el : ℚ} (hK0 : |(-c 0 * Real.log ‖h‖ + c 0 * Real.log 2) - (K0q : ℝ)| ≤ (eK : ℝ))
    (hc0 : (c0q : ℝ) = c 0) (hl : |Real.log (ρq : ℝ) - (lq : ℝ)| ≤ (el : ℝ))
    {cq : ℕ → ℚ} (hcq : ∀ k < N, (cq (k + 1) : ℝ) = c (k + 1))
    {M₂ h₂ : ℂ} (hh₂ : h₂ ≠ 0) {c₂ : ℕ → ℝ} {N₂ : ℕ}
    (hpos₂ : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ chebF c₂ N₂ x) {tq2 te2 : ℕ → ℚ}
    (hseg : ∀ j ≤ 4, |potT M₂ h₂ c₂ N₂ (armG M h (sg : ℝ)) j (-Real.log (ρq : ℝ)) - (tq2 j : ℝ)| ≤
      (te2 j : ℝ))
    {T2q : ℚ}
    (hX : SegCell (armG M h (sg : ℝ) 0 (-Real.log (ρq : ℝ)))
      (YmG h (-Real.log ((ρq * (1 - ρ') : ℚ) : ℝ))) (ρ' : ℝ) M₂ h₂ (c₂ 0) (T2q : ℝ))
    {bh : ℚ} (hbh : ‖h‖ ≤ (bh : ℝ)) {q1 q2 q3 p1 p2 p3 L1 L2 L3 : ℚ}
    (h1 : vPole nL (nsq ⟨Mq.re + hq.re * (sg * chQ ρq 0), Mq.im + hq.im * (sg * chQ ρq 0)⟩)
      q1 p1 (bh * chQ (ρq * (1 - ρ')) 1 * ρ') = some L1)
    (h2 : vPole nL (nsq (GQ.sub ⟨2, 0⟩
      ⟨Mq.re + hq.re * (sg * chQ ρq 0), Mq.im + hq.im * (sg * chQ ρq 0)⟩))
      q2 p2 (bh * chQ (ρq * (1 - ρ')) 1 * ρ') = some L2)
    (h3 : vPole nL (nsq (GQ.add ⟨Mq.re + hq.re * (sg * chQ ρq 0), Mq.im + hq.im * (sg * chQ ρq 0)⟩
      ⟨6, 0⟩)) q3 p3 (bh * chQ (ρq * (1 - ρ')) 1 * ρ') = some L3)
    {TV : ℚ}
    (hTV : fdbBound (psiDmQ (q1 - bh * chQ (ρq * (1 - ρ')) 1 * ρ')
      (q2 - bh * chQ (ρq * (1 - ρ')) 1 * ρ') (q3 - bh * chQ (ρq * (1 - ρ')) 1 * ρ') L1 L2 L3)
      (fun i => bh * chQ (ρq * (1 - ρ')) i) ≤ TV)
    {TR ℓ : ℚ} (hTR : TV + 2 * ownSumGQ cq N (ρq / (1 - ρ')) + 2 * T2q ≤ TR)
    (hok : wedgeCellOk
      (wTq (vTW t0 d1r d1i ⟨Mq.re + hq.re * (sg * chQ ρq 0), Mq.im + hq.im * (sg * chQ ρq 0)⟩
        (fun i => GQ.sc (sg * chQ ρq i) hq)).1
        (fun j => ownGTq K0q c0q sg (fun k => cq k) N j ρq lq) tq2)
      (wTe (vTW t0 d1r d1i ⟨Mq.re + hq.re * (sg * chQ ρq 0), Mq.im + hq.im * (sg * chQ ρq 0)⟩
        (fun i => GQ.sc (sg * chQ ρq i) hq)).2
        (fun j => if j = 0 then eK + |c0q| * el else 0) te2) TR ρ' ℓ = true) :
    ∀ x ∈ Icc (-Real.log (ρq : ℝ) - ρ') (-Real.log (ρq : ℝ) + ρ'), 0 ≤ x →
      vAnal 3 2 2 6 (2 * Real.pi) (M + h * (((sg : ℝ) * Real.cosh x : ℝ) : ℂ)) +
        (-2) * logPotC (segMeasure M h c N) (M + h * (((sg : ℝ) * Real.cosh x : ℝ) : ℂ)) +
        (-2) * logPotC (segMeasure M₂ h₂ c₂ N₂) (M + h * (((sg : ℝ) * Real.cosh x : ℝ) : ℂ)) ≤
          (ℓ : ℝ) := by
  have hρR : (0 : ℝ) < (ρq : ℝ) := by exact_mod_cast hρq
  have hρ'R : (0 : ℝ) ≤ (ρ' : ℝ) := by exact_mod_cast hρ'
  have hρ'1R : (ρ' : ℝ) < 1 := by exact_mod_cast hρ'1
  have hρ1R : (ρq : ℝ) ≤ 1 := by exact_mod_cast hρq1
  set ρh : ℚ := ρq * (1 - ρ') with hρh
  have hρh0 : (0 : ℝ) < (ρh : ℝ) := by
    rw [hρh]; push_cast; exact mul_pos hρR (by linarith)
  have hρh1 : (ρh : ℝ) ≤ 1 := by
    rw [hρh]; push_cast; nlinarith
  set s : ℝ := (sg : ℝ) with hsdef
  have hs1 : s = 1 ∨ s = -1 := by
    rcases hsg with h | h <;> simp [hsdef, h]
  set a : ℝ := -Real.log (ρq : ℝ) with ha
  set whi : ℝ := -Real.log ((ρh : ℚ) : ℝ) with hwdef
  have hcoshw : ∀ i, YmG h whi i = ‖h‖ * ((chQ ρh i : ℚ) : ℝ) := by
    intro i
    unfold YmG
    rw [← chQ_spec (by rw [hρh]; exact mul_pos hρq (by linarith [show (ρ' : ℚ) < 1 from hρ'1]))]
    by_cases hi : i % 2 = 0
    · simp [hi, hwdef, cosh_neg_log hρh0]
    · simp [hi, hwdef, sinh_neg_log hρh0]
  have hch0 : ∀ i, (0 : ℝ) ≤ ((chQ ρh i : ℚ) : ℝ) := by
    intro i
    rw [← chQ_spec (by rw [hρh]; exact mul_pos hρq (by linarith [show (ρ' : ℚ) < 1 from hρ'1]))]
    split_ifs
    · have : (0 : ℝ) < (ρh : ℝ)⁻¹ := inv_pos.2 hρh0
      linarith
    · have h1 : (ρh : ℝ) ≤ 1 := hρh1
      have h2 : (1 : ℝ) ≤ (ρh : ℝ)⁻¹ := (one_le_inv₀ hρh0).2 h1
      linarith
  have hY0 : ∀ i, 1 ≤ i → i ≤ 5 → 0 ≤ YmG h whi i := fun i _ _ => by
    rw [hcoshw]; exact mul_nonneg (norm_nonneg _) (hch0 i)
  have hρ : (0 : ℝ) ≤ (ρ' : ℝ) := hρ'R
  have hb : YmG h whi 1 * (ρ' : ℝ) ≤ ((bh * chQ ρh 1 * ρ' : ℚ) : ℝ) := by
    rw [hcoshw]; push_cast
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hbh (hch0 1)) hρ
  have hYQ : ∀ i, 1 ≤ i → i ≤ 5 → YmG h whi i ≤ (((fun i => bh * chQ ρh i) i : ℚ) : ℝ) := by
    intro i _ _
    rw [hcoshw]; push_cast
    exact mul_le_mul_of_nonneg_right hbh (hch0 i)
  set sq : GQ := ⟨Mq.re + hq.re * (sg * chQ ρq 0), Mq.im + hq.im * (sg * chQ ρq 0)⟩ with hsq
  set Yq : ℕ → GQ := fun i => GQ.sc (sg * chQ ρq i) hq with hYq
  have hρq' : 0 < ρq := hρq
  have harm : ∀ i, armG M h s i a = (if i = 0 then M else 0) +
      h * (((sg * chQ ρq i : ℚ) : ℝ) : ℂ) := by
    intro i
    have hc := chQ_spec hρq' i
    rw [ha, armG_neg_log M h s hρR i]
    simp only [Rat.cast_mul, Complex.ofReal_mul]
    rw [← hc]
  have hz : armG M h s 0 a = GQ.toC sq := by
    rw [harm 0, if_pos rfl, ← hM, ← hH, hsq]
    apply Complex.ext <;> simp [GQ.toC] <;> (try ring)
  have hYi : ∀ i, 1 ≤ i → i ≤ 4 → armG M h s i a = GQ.toC (Yq i) := by
    intro i hi _
    rw [harm i, if_neg (by omega), zero_add, hYq, GQ.toC_sc, hH]
    push_cast
    ring
  have hV := mkVCell (nL := nL) (z := sq) (Ym := YmG h whi) (ρ := (ρ' : ℝ)) hρ hY0 hb h1 h2 h3
    hYQ hTV
  rw [← hz] at hV
  have hTenc := cell_tenc (γ := armG M h s) (a := a)
    (f₁ := ownGT (-c 0 * Real.log ‖h‖ + c 0 * Real.log 2) (c 0) s c N)
    (f₂ := potT M₂ h₂ c₂ N₂ (armG M h s)) hκ hv hz hYi
    (tq1 := fun j => ownGTq K0q c0q sg (fun k => cq k) N j ρq lq)
    (te1 := fun j => if j = 0 then eK + |c0q| * el else 0)
    (fun j _ => by
      have := ownGT_enc_rho (K0 := -c 0 * Real.log ‖h‖ + c 0 * Real.log 2) (c0 := c 0) (s := s)
        (K0q := K0q) (eK := eK) (c0q := c0q) (sq := sg) (ρq := ρq) (lq := lq) (el := el)
        (w := c) (wq := fun k => cq k) N hK0 hc0 rfl hcq hρR hl j
      by_cases hj0 : j = 0
      · subst hj0
        simp only [if_true, Rat.cast_add, Rat.cast_mul, Rat.cast_abs, hc0] at this ⊢
        exact this
      · simpa [hj0] using this)
    hseg
  have hwhi : ∀ x ∈ Icc (a - ρ') (a + ρ'), |x| ≤ whi := by
    intro x hx
    have hlog1 : Real.log (1 - (ρ' : ℝ)) ≤ -(ρ' : ℝ) := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 - ρ' by linarith)
      linarith
    have hw : a + ρ' ≤ whi := by
      rw [hwdef, hρh]
      push_cast
      rw [Real.log_mul hρR.ne' (by linarith)]
      rw [ha]; linarith
    have ha0 : 0 ≤ a := by
      rw [ha]; have := Real.log_nonpos hρR.le hρ1R; linarith
    rw [abs_le]; constructor <;> linarith [hx.1, hx.2]
  have hdom : ∀ x ∈ Icc (a - ρ') (a + ρ'), psiDom 2 6 (M + h * ((s * Real.cosh x : ℝ) : ℂ)) := by
    intro x hx
    apply psiDom_of_im_pos
    have hxw := hwhi x hx
    have hc1 : Real.cosh x ≤ Real.cosh whi :=
      Real.cosh_le_cosh.2 (by rw [abs_of_nonneg (abs_nonneg x |>.trans hxw)]; exact hxw)
    have hc2 : Real.cosh whi = ((chQ ρh 0 : ℚ) : ℝ) := by
      rw [← chQ_spec (by rw [hρh]; exact mul_pos hρq (by linarith [show (ρ' : ℚ) < 1 from hρ'1]))]
      simp [hwdef, cosh_neg_log hρh0]
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
      add_zero]
    have habs : |h.im * (s * Real.cosh x)| ≤ |h.im| * ((chQ ρh 0 : ℚ) : ℝ) := by
      rw [abs_mul, abs_mul, abs_of_pos (Real.cosh_pos x)]
      rcases hs1 with h1 | h1 <;> rw [h1] <;> simp <;>
        exact mul_le_mul_of_nonneg_left (hc1.trans hc2.le) (abs_nonneg _)
    linarith [neg_abs_le (h.im * (s * Real.cosh x))]
  have hE : ∀ k < N, Real.exp (-(((k + 1 : ℕ) : ℝ) * (a - ρ'))) ≤
      (((ρq / (1 - ρ')) ^ (k + 1) : ℚ) : ℝ) := by
    intro k _
    have e1 : -(((k + 1 : ℕ) : ℝ) * (a - ρ')) = ((k + 1 : ℕ) : ℝ) * (Real.log ρq + ρ') := by
      rw [ha]; ring
    rw [e1, Real.exp_nat_mul, Real.exp_add, Real.exp_log hρR]
    push_cast
    refine pow_le_pow_left₀ (mul_nonneg hρR.le (Real.exp_pos _).le) ?_ _
    have := Real.exp_bound_div_one_sub_of_interval hρ'R hρ'1R
    rw [div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_left this hρR.le
  have key := cellG_sound_nn 3 2 2 6 (2 * Real.pi) (((-2 : ℚ)) : ℝ) (((-2 : ℚ)) : ℝ) (by norm_num)
    (by norm_num) hh hpos hs1 (whi := whi) hwhi hdom hV hh₂ hpos₂ hX
    (E := fun k => (((ρq / (1 - ρ')) ^ (k + 1) : ℚ) : ℝ)) hE (rq := ρ') (ℓ := ℓ) rfl
    (by simpa using hTenc) ?_ hok
  · intro x hx hx0
    have := key x hx hx0
    simpa using this
  · have hs1' : ∑ k ∈ Finset.range N, |c (k + 1)| * ((k + 1 : ℕ) : ℝ) ^ 4 *
        (((ρq / (1 - ρ')) ^ (k + 1) : ℚ) : ℝ) = (ownSumGQ cq N (ρq / (1 - ρ')) : ℝ) := by
      unfold ownSumGQ
      push_cast
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [hcq k (Finset.mem_range.1 hk)]
    rw [hs1']
    have := (Rat.cast_le (K := ℝ)).2 hTR
    push_cast at this ⊢
    simp only [abs_neg, abs_two, Rat.cast_neg, Rat.cast_ofNat]
    linarith


/-- **R12 (R kind).**  An R cell on the ray `p + i x`, centre `a` and radius `ρ` rational. -/
theorem cellR_rat {p : ℂ} {pq : GQ} (hp : GQ.toC pq = p) {a ρ : ℚ} (hρ : 0 ≤ ρ)
    (hIm : 0 < p.im + ((a : ℝ) - ρ))
    {nL nA : ℕ} {κE t0 d1r d1i : ℚ × ℚ}
    (hκ : Enc (2 * (6 * Real.log 6 - 6) - 3 * (2 * Real.log 2 - 2)) κE)
    (hv : vEncOut nL nA κE ⟨pq.re, pq.im + a⟩ = some (t0, d1r, d1i))
    {M₁ h₁ : ℂ} (hh₁ : h₁ ≠ 0) {c₁ : ℕ → ℝ} {N₁ : ℕ}
    (hpos₁ : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ chebF c₁ N₁ x) {tq1 te1 : ℕ → ℚ}
    (hseg1 : ∀ j ≤ 4, |potT M₁ h₁ c₁ N₁ (lineC p Complex.I) j (a : ℝ) - (tq1 j : ℝ)| ≤ (te1 j : ℝ))
    {T1q : ℚ}
    (hX₁ : SegCell (lineC p Complex.I 0 (a : ℝ)) (fun i => if i = 1 then 1 else 0) (ρ : ℝ) M₁ h₁ (c₁ 0)
      (T1q : ℝ))
    {M₂ h₂ : ℂ} (hh₂ : h₂ ≠ 0) {c₂ : ℕ → ℝ} {N₂ : ℕ}
    (hpos₂ : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ chebF c₂ N₂ x) {tq2 te2 : ℕ → ℚ}
    (hseg2 : ∀ j ≤ 4, |potT M₂ h₂ c₂ N₂ (lineC p Complex.I) j (a : ℝ) - (tq2 j : ℝ)| ≤ (te2 j : ℝ))
    {T2q : ℚ}
    (hX₂ : SegCell (lineC p Complex.I 0 (a : ℝ)) (fun i => if i = 1 then 1 else 0) (ρ : ℝ) M₂ h₂ (c₂ 0)
      (T2q : ℝ))
    {q1 q2 q3 p1 p2 p3 L1 L2 L3 : ℚ}
    (h1 : vPole nL (nsq ⟨pq.re, pq.im + a⟩) q1 p1 ρ = some L1)
    (h2 : vPole nL (nsq (GQ.sub ⟨2, 0⟩ ⟨pq.re, pq.im + a⟩)) q2 p2 ρ = some L2)
    (h3 : vPole nL (nsq (GQ.add ⟨pq.re, pq.im + a⟩ ⟨6, 0⟩)) q3 p3 ρ = some L3)
    {TV : ℚ}
    (hTV : fdbBound (psiDmQ (q1 - ρ) (q2 - ρ) (q3 - ρ) L1 L2 L3) (fun i => if i = 1 then 1 else 0)
      ≤ TV)
    {TR ℓ : ℚ} (hTR : TV + 2 * T1q + 2 * T2q ≤ TR)
    (hok : wedgeCellOk
      (wTq (vTW t0 d1r d1i ⟨pq.re, pq.im + a⟩
        (fun i => if i = 1 then ⟨0, 1⟩ else ⟨0, 0⟩)).1 tq1 tq2)
      (wTe (vTW t0 d1r d1i ⟨pq.re, pq.im + a⟩
        (fun i => if i = 1 then ⟨0, 1⟩ else ⟨0, 0⟩)).2 te1 te2) TR ρ ℓ = true) :
    ∀ x ∈ Icc ((a : ℝ) - ρ) ((a : ℝ) + ρ),
      vAnal 3 2 2 6 (2 * Real.pi) (p + Complex.I * (x : ℂ)) +
        (-2) * logPotC (segMeasure M₁ h₁ c₁ N₁) (p + Complex.I * (x : ℂ)) +
        (-2) * logPotC (segMeasure M₂ h₂ c₂ N₂) (p + Complex.I * (x : ℂ)) ≤ (ℓ : ℝ) := by
  have hρR : (0 : ℝ) ≤ (ρ : ℝ) := by exact_mod_cast hρ
  set sq : GQ := ⟨pq.re, pq.im + a⟩ with hsq
  set Yq : ℕ → GQ := fun i => if i = 1 then ⟨0, 1⟩ else ⟨0, 0⟩ with hYq
  have hz : lineC p Complex.I 0 (a : ℝ) = GQ.toC sq := by
    rw [← hp, hsq]
    apply Complex.ext <;> simp [lineC, GQ.toC]
  have hYi : ∀ i, 1 ≤ i → i ≤ 4 → lineC p Complex.I i (a : ℝ) = GQ.toC (Yq i) := by
    intro i hi _
    by_cases h1 : i = 1
    · subst h1; apply Complex.ext <;> simp [lineC, hYq, GQ.toC]
    · have : i ≠ 0 := by omega
      apply Complex.ext <;> simp [lineC, hYq, GQ.toC, h1, this]
  have hY0 : ∀ i, 1 ≤ i → i ≤ 5 → 0 ≤ (fun i : ℕ => if i = 1 then (1 : ℝ) else 0) i := by
    intro i _ _; by_cases h : i = 1 <;> simp [h]
  have hb : (fun i : ℕ => if i = 1 then (1 : ℝ) else 0) 1 * (ρ : ℝ) ≤ (ρ : ℝ) := by simp
  have hV := mkVCell (nL := nL) (z := sq) (Ym := fun i => if i = 1 then 1 else 0) (ρ := (ρ : ℝ))
    hρR hY0 hb h1 h2 h3 (YmQ := fun i => if i = 1 then 1 else 0)
    (fun i _ _ => by by_cases h : i = 1 <;> simp [h]) hTV
  rw [← hz] at hV
  have hTenc := cell_tenc (γ := lineC p Complex.I) (a := (a : ℝ))
    (f₁ := potT M₁ h₁ c₁ N₁ (lineC p Complex.I)) (f₂ := potT M₂ h₂ c₂ N₂ (lineC p Complex.I))
    hκ hv hz hYi hseg1 hseg2
  have hdom : ∀ x ∈ Icc ((a : ℝ) - ρ) ((a : ℝ) + ρ), psiDom 2 6 (p + Complex.I * (x : ℂ)) := by
    intro x hx
    apply psiDom_of_im_pos
    simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im]
    simp
    linarith [hx.1]
  have key := cellR_sound 3 2 2 6 (2 * Real.pi) (((-2 : ℚ)) : ℝ) (((-2 : ℚ)) : ℝ) (by norm_num)
    (by norm_num) p Complex.I (by simp) hdom hV hh₁ hpos₁ hX₁ hh₂ hpos₂ hX₂ (rq := ρ) (ℓ := ℓ) rfl
    (by simpa using hTenc) ?_ hok
  · intro x hx
    have := key x hx
    simpa using this
  · have := (Rat.cast_le (K := ℝ)).2 hTR
    push_cast at this ⊢
    simp only [abs_neg, abs_two, Rat.cast_ofNat]
    linarith


/-! ### R13: containment of the chain cell in the evaluation cell, and `LaiCover` from cells -/

/-- the A-cell offset `ε ≥ |π θ − 2 arctan τ|` from `atanQ` and `PI4`. -/
def epsA (θ v e : ℚ) : ℚ := |θ| * (4 * PI4E) + |4 * PI4 * θ - 2 * v| + 2 * e

theorem epsA_spec {nA : ℕ} {τ θ v e : ℚ} (h : atanQ nA τ = some (v, e)) :
    |Real.pi * (θ : ℝ) - 2 * Real.arctan (τ : ℝ)| ≤ (epsA θ v e : ℝ) := by
  have h1 := atanQ_spec h
  have h2 := pi4_spec
  unfold epsA
  push_cast
  have e1 : Real.pi * (θ : ℝ) - 2 * Real.arctan (τ : ℝ) =
      (θ : ℝ) * (4 * (Real.pi / 4 - (PI4 : ℝ))) + (4 * (PI4 : ℝ) * θ - 2 * (v : ℝ)) +
        2 * ((v : ℝ) - Real.arctan (τ : ℝ)) := by ring
  rw [e1]
  have a1 : |(θ : ℝ) * (4 * (Real.pi / 4 - (PI4 : ℝ)))| ≤ |(θ : ℝ)| * (4 * (PI4E : ℝ)) := by
    rw [abs_mul, abs_mul]
    have : |(4 : ℝ)| = 4 := by norm_num
    rw [this]
    exact mul_le_mul_of_nonneg_left (by nlinarith [h2]) (abs_nonneg _)
  have a3 : |2 * ((v : ℝ) - Real.arctan (τ : ℝ))| ≤ 2 * (e : ℝ) := by
    rw [abs_mul, abs_sub_comm]
    have : |(2 : ℝ)| = 2 := by norm_num
    rw [this]; linarith
  calc _ ≤ |(θ : ℝ) * (4 * (Real.pi / 4 - (PI4 : ℝ))) + (4 * (PI4 : ℝ) * θ - 2 * (v : ℝ))| +
        |2 * ((v : ℝ) - Real.arctan (τ : ℝ))| := abs_add_le _ _
    _ ≤ |(θ : ℝ) * (4 * (Real.pi / 4 - (PI4 : ℝ)))| + |4 * (PI4 : ℝ) * θ - 2 * (v : ℝ)| +
        |2 * ((v : ℝ) - Real.arctan (τ : ℝ))| := add_le_add (abs_add_le _ _) le_rfl
    _ ≤ _ := by linarith

theorem contain_A {nA : ℕ} {τ θ v e ρ ρ' : ℚ} (h : atanQ nA τ = some (v, e))
    (hρ : ρ + epsA θ v e ≤ ρ') :
    ∀ x ∈ Icc (Real.pi * (θ : ℝ) - ρ) (Real.pi * (θ : ℝ) + ρ),
      x ∈ Icc (2 * Real.arctan (τ : ℝ) - ρ') (2 * Real.arctan (τ : ℝ) + ρ') := by
  intro x hx
  have h1 := abs_le.mp (epsA_spec (θ := θ) h)
  have h2 : (ρ : ℝ) + (epsA θ v e : ℝ) ≤ ρ' := by exact_mod_cast hρ
  constructor <;> linarith [hx.1, hx.2]

/-- the G-cell offset `ε ≥ |θ + log ρq|`. -/
def epsG (θ l el : ℚ) : ℚ := |θ + l| + el

theorem contain_G {nL : ℕ} {ρq θ l el ρ ρ' : ℚ} (h : logQ nL ρq = some (l, el))
    (hρ : ρ + epsG θ l el ≤ ρ') :
    ∀ w ∈ Icc ((θ : ℝ) - ρ) ((θ : ℝ) + ρ),
      w ∈ Icc (-Real.log (ρq : ℝ) - ρ') (-Real.log (ρq : ℝ) + ρ') := by
  intro w hw
  obtain ⟨_, E⟩ := logQ_spec h
  have E' := abs_le.mp E
  have h2 : (ρ : ℝ) + (epsG θ l el : ℝ) ≤ ρ' := by exact_mod_cast hρ
  unfold epsG at h2
  push_cast at h2
  have h3 := abs_le.mp (le_refl |(θ : ℝ) + (l : ℝ)|)
  have h4 : (θ : ℝ) + l ≤ |(θ : ℝ) + l| := le_abs_self _
  have h5 : -|(θ : ℝ) + l| ≤ (θ : ℝ) + l := neg_abs_le _
  constructor <;> linarith [hw.1, hw.2, E'.1, E'.2]

/-- **R13.**  `LaiCover` from per-cell soundness predicates on the three chains and the ray. -/
theorem laiCover_of_cells (c : ℕ → ℝ) (N : ℕ) (wA wB : ℝ) (hwA0 : 0 ≤ wA) (hwB0 : 0 ≤ wB)
    (hwA : 97 / 93 ≤ Real.cosh wA) (hwB : 103 / 93 ≤ Real.cosh wB)
    (pA : ℚ × ℚ) (tA : List (ℚ × ℚ)) (hA : DecayGlue.chainOK (31416 / 10000) (pA :: tA) = true)
    (hA0 : 0 ≤ pA.1 ∧ pA.1 * (31416 / 10000) ≤ pA.2)
    (hA1 : ((pA :: tA).getLast (by simp)).1 ≤ 1 ∧
      (1 - ((pA :: tA).getLast (by simp)).1) * (31416 / 10000) ≤ ((pA :: tA).getLast (by simp)).2)
    (pG : ℚ × ℚ) (tG : List (ℚ × ℚ)) (hG : DecayGlue.chainOK 1 (pG :: tG) = true)
    (hG0 : (pG.1 : ℝ) - pG.2 ≤ 0)
    (hG1 : wA ≤ (((pG :: tG).getLast (by simp)).1 : ℝ) + (((pG :: tG).getLast (by simp)).2 : ℝ))
    (pH : ℚ × ℚ) (tH : List (ℚ × ℚ)) (hH : DecayGlue.chainOK 1 (pH :: tH) = true)
    (hH0 : (pH.1 : ℝ) - pH.2 ≤ 0)
    (hH1 : wB ≤ (((pH :: tH).getLast (by simp)).1 : ℝ) + (((pH :: tH).getLast (by simp)).2 : ℝ))
    (pR : ℚ × ℚ) (tR : List (ℚ × ℚ)) (hR : DecayGlue.chainOK 1 (pR :: tR) = true)
    (hR0 : (pR.1 : ℝ) - pR.2 ≤ 0)
    (hR1 : (11 / 10 : ℝ) ≤ (((pR :: tR).getLast (by simp)).1 : ℝ) +
      (((pR :: tR).getLast (by simp)).2 : ℝ))
    (okA okG okH okR : ℚ × ℚ → Prop)
    (sA : ∀ q, okA q → ∀ x ∈ Icc (Real.pi * (q.1 : ℝ) - q.2) (Real.pi * (q.1 : ℝ) + q.2),
      DecayInstance.Wan c N (DecayInstance.laiM + DecayInstance.laiH * ((Real.cos x : ℝ) : ℂ)) ≤
        DecayInstance.laiEll)
    (sG : ∀ q, okG q → ∀ w ∈ Icc ((q.1 : ℝ) - q.2) ((q.1 : ℝ) + q.2),
      DecayInstance.Wan c N (DecayInstance.laiM +
        DecayInstance.laiH * ((((-1 : ℝ) * Real.cosh w : ℝ)) : ℂ)) ≤ DecayInstance.laiEll)
    (sH : ∀ q, okH q → ∀ w ∈ Icc ((q.1 : ℝ) - q.2) ((q.1 : ℝ) + q.2),
      DecayInstance.Wan c N (DecayInstance.laiM +
        DecayInstance.laiH * ((((1 : ℝ) * Real.cosh w : ℝ)) : ℂ)) ≤ DecayInstance.laiEll)
    (sR : ∀ q, okR q → ∀ y ∈ Icc ((q.1 : ℝ) - q.2) ((q.1 : ℝ) + q.2),
      DecayInstance.Wan c N (DecayInstance.laiP + Complex.I * (y : ℂ)) ≤ DecayInstance.laiEll)
    (cA : ∀ q ∈ pA :: tA, okA q) (cG : ∀ q ∈ pG :: tG, okG q) (cH : ∀ q ∈ pH :: tH, okH q)
    (cR : ∀ q ∈ pR :: tR, okR q) :
    DecayInstance.LaiCover c N DecayInstance.laiEll wA wB :=
  DecayGlue.laiCover_of_chains c N wA wB hwA0 hwB0 hwA hwB pA tA hA hA0 hA1
    (fun q hq x hx => sA q (cA q hq) x hx) pG tG hG hG0 hG1 (fun q hq w hw => sG q (cG q hq) w hw)
    pH tH hH hH0 hH1 (fun q hq w hw => sH q (cH q hq) w hw) pR tR hR hR0 hR1
    (fun q hq y hy => sR q (cR q hq) y hy)


/-! ### R12 (segment part): `SegCell` from the rational data of `segTower_encQ` -/

def segCell_of_enc {M h : ℂ} {c : ℕ → ℝ} (P : SegQ)
    (hpos : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ chebF c P.N x)
    (hc : ∀ k ≤ P.N, (P.cq k : ℝ) = c k)
    (Mq sq : CQ) (hM : Mq.toC = M) (hh : P.hq.toC = h) (hne : P.hq.nsq ≠ 0)
    (R δ dq hlo : ℚ) (hR : 1 < R) (hRφ : R ^ 2 ≤ P.φq.nsq) (hδ : 0 ≤ δ)
    (hs : (sq.sub (Mq.add (P.hq.mul P.ζ))).nsq ≤ δ ^ 2)
    (hlo0 : 0 ≤ hlo) (hlo2 : hlo ^ 2 ≤ P.hq.nsq)
    (hdq : dq ≤ hlo * ((R + R⁻¹) / 2 - 1) - δ)
    {Ym : ℕ → ℝ} {ρ : ℝ} (hρ : 0 ≤ ρ) {b : ℚ} (hb : Ym 1 * ρ ≤ (b : ℝ)) {YmQ : ℕ → ℚ}
    (hYm : ∀ i, 1 ≤ i → i ≤ 5 → 0 ≤ Ym i ∧ Ym i ≤ (YmQ i : ℝ)) (hdb : 0 < dq - b) {T : ℚ}
    (hT : fdbBound (fun k => (((k - 1).factorial : ℕ) : ℚ) * P.cq 0 / (dq - b) ^ k) YmQ ≤ T) :
    SegCell sq.toC Ym ρ M h (c 0) (T : ℝ) := by
  have hh0 : h ≠ 0 := by rw [← hh]; exact CQ.toC_ne_zero hne
  have hRr : (1 : ℝ) < R := by exact_mod_cast hR
  have hφsq : (R : ℝ) ^ 2 ≤ ‖P.φq.toC‖ ^ 2 := by
    rw [norm_toC_sq]; exact_mod_cast hRφ
  have hφR : (R : ℝ) ≤ ‖P.φq.toC‖ := by
    by_contra hcon
    push Not at hcon
    nlinarith [norm_nonneg P.φq.toC]
  have hφ1 : 1 < ‖P.φq.toC‖ := lt_of_lt_of_le hRr hφR
  have hφ0 : P.φq.toC ≠ 0 := norm_pos_iff.1 (by linarith)
  have hφnsq : P.φq.nsq ≠ 0 := nsq_ne_of_toC hφ0
  have hζ := toC_zeta P hφnsq
  have hjcz : jc P.ζ.toC = (‖P.φq.toC‖ + ‖P.φq.toC‖⁻¹) / 2 := by rw [hζ]; exact jc_jJ hφ0
  have hδs : ‖sq.toC - (M + h * P.ζ.toC)‖ ≤ δ := by
    have e : (sq.sub (Mq.add (P.hq.mul P.ζ))).toC = sq.toC - (M + h * P.ζ.toC) := by
      rw [CQ.toC_sub, CQ.toC_add, CQ.toC_mul, hM, hh]
    have h2 : ‖sq.toC - (M + h * P.ζ.toC)‖ ^ 2 ≤ (δ : ℝ) ^ 2 := by
      rw [← e, norm_toC_sq]; exact_mod_cast hs
    by_contra hcon
    push Not at hcon
    nlinarith [norm_nonneg (sq.toC - (M + h * P.ζ.toC)), (by exact_mod_cast hδ : (0 : ℝ) ≤ δ)]
  have hlh : (hlo : ℝ) ≤ ‖h‖ := by
    have h2 : (hlo : ℝ) ^ 2 ≤ ‖h‖ ^ 2 := by
      rw [← hh, norm_toC_sq]; exact_mod_cast hlo2
    by_contra hcon
    push Not at hcon
    nlinarith [norm_nonneg h, (by exact_mod_cast hlo0 : (0 : ℝ) ≤ hlo)]
  have hjcR : ((R : ℝ) + (R : ℝ)⁻¹) / 2 ≤ jc P.ζ.toC := by
    rw [hjcz]; have := add_inv_mono hRr.le hφR; linarith
  have hseg0 := seg_dist_lb (M := M) (h := h) (s := sq.toC) (s' := M + h * P.ζ.toC)
    (ζ0 := P.ζ.toC) (δ := δ) (hlo := hlo) (R := R) hh0 rfl hjcR hRr.le hδs
    (by exact_mod_cast hlo0) hlh
  have hdq' : (dq : ℝ) ≤ hlo * (((R : ℝ) + (R : ℝ)⁻¹) / 2 - 1) - δ := by exact_mod_cast hdq
  have hdist : (dq : ℝ) ≤ ‖h‖ * (jc ((sq.toC - M) / h) - 1) :=
    hdq'.trans (hseg0 sq.toC (right_mem_segment ℝ _ _))
  have hdb' : (0 : ℝ) < ((dq - b : ℚ) : ℝ) := by exact_mod_cast hdb
  have hb0 : (0 : ℝ) ≤ (b : ℝ) :=
    (mul_nonneg (hYm 1 (by norm_num) (by norm_num)).1 hρ).trans hb
  have hdpos : (0 : ℝ) < dq := by
    have : (0 : ℝ) < (dq : ℝ) - b := by push_cast at hdb'; exact hdb'
    linarith
  have hseg : ∀ w ∈ segment ℝ (M + h * P.ζ.toC) sq.toC,
      (dq : ℝ) ≤ ‖h‖ * (jc ((w - M) / h) - 1) := fun w hw => hdq'.trans (hseg0 w hw)
  have hc0 : 0 ≤ c 0 := by
    have := norm_segSt_le_of_seg hh0 hpos hdpos
      (hseg _ (left_mem_segment ℝ _ _)) 0
    simp only [pow_zero, div_one] at this
    exact (norm_nonneg _).trans this
  have hcq0 : (P.cq 0 : ℝ) = c 0 := hc 0 (Nat.zero_le _)
  refine ⟨((dq - b : ℚ) : ℝ), hdb', ?_, ?_⟩
  · push_cast at hdb' ⊢
    linarith
  · have hD0 : ∀ k, 1 ≤ k → k ≤ 5 → 0 ≤ ((k - 1).factorial : ℝ) * c 0 / ((dq - b : ℚ) : ℝ) ^ k :=
      fun k _ _ => by positivity
    have hmono := fdbBound_mono (Dm := fun k => ((k - 1).factorial : ℝ) * c 0 / ((dq - b : ℚ) : ℝ) ^ k)
      (Dm' := fun k => (((((k - 1).factorial : ℕ) : ℚ) * P.cq 0 / (dq - b) ^ k : ℚ) : ℝ))
      (Ym := Ym) (Ym' := fun i => (YmQ i : ℝ)) hD0 (fun i hi1 hi5 => (hYm i hi1 hi5).1)
      (fun k _ _ => by
        push_cast
        rw [hcq0]) (fun i hi1 hi5 => (hYm i hi1 hi5).2)
    refine hmono.trans ?_
    rw [← fdbBound_cast]
    exact_mod_cast hT


/-! ### R3, R4 (energy centres): re-centring and the order-`j` majorant of `potT` -/

/-- **R3, `tower_recentre`** (Lemma 4, mean value step). -/
theorem tower_recentre {f : ℕ → ℝ → ℝ} {c r : ℝ} (hf : IsTower f c r 5) {a' x : ℝ}
    (ha : a' ∈ Icc (c - r) (c + r)) (hx : x ∈ Icc (c - r) (c + r)) {j : ℕ} (hj : j ≤ 4) {B : ℝ}
    (hB : ∀ y ∈ Icc (c - r) (c + r), |f (j + 1) y| ≤ B) :
    |f j x - f j a'| ≤ B * |x - a'| := by
  have key : ∀ lo hi : ℝ, lo ∈ Icc (c - r) (c + r) → hi ∈ Icc (c - r) (c + r) → lo ≤ hi →
      |f j hi - f j lo| ≤ B * (hi - lo) := by
    intro lo hi hlo hhi hle
    rcases hle.eq_or_lt with rfl | hlt
    · simp
    · have hc : ContinuousOn (f j) (Icc lo hi) :=
        (hf.cont j (by omega)).mono (Icc_subset_Icc hlo.1 hhi.2)
      obtain ⟨ξ, hξ, hd⟩ := exists_hasDerivAt_eq_slope (f j) (f (j + 1)) hlt hc
        (fun y hy => hf.der j (by omega) y ⟨by linarith [hlo.1, hy.1], by linarith [hhi.2, hy.2]⟩)
      have hξ' : ξ ∈ Icc (c - r) (c + r) := ⟨by linarith [hlo.1, hξ.1], by linarith [hhi.2, hξ.2]⟩
      have h1 := hB ξ hξ'
      rw [hd] at h1
      have hp : 0 < hi - lo := by linarith
      rw [abs_div, abs_of_pos hp, div_le_iff₀ hp] at h1
      linarith
  rcases le_total a' x with h | h
  · have := key a' x ha hx h
    rwa [abs_of_nonneg (sub_nonneg.2 h)]
  · have := key x a' hx ha h
    rw [abs_sub_comm, abs_of_nonpos (sub_nonpos.2 h), neg_sub]
    exact this

theorem norm_fdb_le_bound (D Y : ℕ → ℂ) (η Ym : ℕ → ℝ) {j : ℕ} (hj1 : 1 ≤ j) (hj : j ≤ 5)
    (hD : ∀ k, 1 ≤ k → k ≤ j → ‖D k‖ ≤ η k) (hY : ∀ i, 1 ≤ i → i ≤ j → ‖Y i‖ ≤ Ym i) :
    ‖fdb D Y j‖ ≤ fdb η Ym j := by
  have h0 : fdb (fun _ => (0 : ℂ)) Y j = 0 := by
    interval_cases j <;> simp [fdb]
  have := norm_fdb_sub_le D (fun _ => 0) Y η Ym hj1 hj (fun k hk1 hkj => by simpa using hD k hk1 hkj) hY
  rwa [h0, sub_zero] at this

/-- **R4 (potT).** The order-`j` majorant of the segment tower, `1 ≤ j ≤ 5`. -/
theorem abs_potT_le {M h : ℂ} (hh : h ≠ 0) {c : ℕ → ℝ} {N : ℕ}
    (hpos : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ chebF c N x) {γ : ℕ → ℝ → ℂ} {x dlo : ℝ} {Ym : ℕ → ℝ}
    (hreg : 1 < jc ((γ 0 x - M) / h)) (hdlo0 : 0 < dlo)
    (hdlo : dlo ≤ ‖h‖ * (jc ((γ 0 x - M) / h) - 1)) (hY : ∀ i, 1 ≤ i → i ≤ 5 → ‖γ i x‖ ≤ Ym i)
    {j : ℕ} (hj1 : 1 ≤ j) (hj5 : j ≤ 5) :
    |potT M h c N γ j x| ≤ fdb (fun k => ((k - 1).factorial : ℝ) * c 0 / dlo ^ k) Ym j := by
  have hne : j ≠ 0 := by omega
  simp only [potT, hne, if_false]
  refine (Complex.abs_re_le_norm _).trans ?_
  refine norm_fdb_le_bound _ _ _ Ym hj1 hj5 (fun k hk1 hk5 => ?_) (fun i hi1 hi5 => hY i hi1 (by omega))
  have hb := norm_segSt_le hh hpos (s := γ 0 x) hreg k
  simp only [segD, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Complex.norm_natCast]
  calc ((k - 1).factorial : ℝ) * ‖segSt M h c N k (γ 0 x)‖
      ≤ ((k - 1).factorial : ℝ) * (c 0 / (‖h‖ * (jc ((γ 0 x - M) / h) - 1)) ^ k) :=
        mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg _)
    _ ≤ ((k - 1).factorial : ℝ) * (c 0 / dlo ^ k) := by
        refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
        refine div_le_div_of_nonneg_left ?_ (pow_pos hdlo0 k) (pow_le_pow_left₀ hdlo0.le hdlo k)
        rw [← integral_chebF c N]
        exact MeasureTheory.integral_nonneg fun θ => hpos _ (cos_mem θ)
    _ = _ := by ring


end

end CatalanCore.Lai.DecayTowerV
