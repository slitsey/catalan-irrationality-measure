module

public import CatalanCore.Lai.DecayInstance
public import CatalanCore.Lai.DecayEnergy
public import CatalanCore.Lai.Family
public import CatalanCore.Uniform.Measure.NV0

@[expose] public section

/-!
# Lai decay assembly (ledger LD22, LD23)

`lai_wedge_D` (LD22) and `lai_plane_decay`, `lai_ratio_decay` (LD23, `HasScaledDecay`) from the built
`Lai.DecayInstance.lai_decay_instance` (LD10), the tail and atoms (`Lai.DecayTail`), the energy
(`Lai.DecayEnergy.energy_conj_pair_le`, LD14) and the cell soundness (`Lai.DecayCells`, LD18).

The W2 data enter as the fields of `LaiDecayData` (every field a statement the generator must prove):

* `hpos`, `hc0`: `f = Σ c_k T_k ≥ 0` on `[-1, 1]` with `c₀ = 3/2` (LD21, the SOS identity);
* `hcov : LaiCover c N laiEll wA wB`: the 40 cell checks (LD19);
* `ha0`, `hA`, `hρ`: the atom numbers `a(x*)`, `|a'(x*)|` and `a0 + AA²/(98/100) ≤ ℓ + ρ`;
* `henergy : LaiEnergyOK c N`: the partition, the per-cell tower bounds `U`, `E` and the energy
  inequality `I(σ) ≤ 208871/10^5`.

Say μ, never B, for the irrationality measure.
-/

open MeasureTheory Set Real Filter Topology Finset Polynomial

namespace CatalanCore.Lai.DecayCert

open CatalanCore.Lai CatalanCore.Lai.DecayInstance CatalanCore.Lai.DecayDual CatalanCore.Lai.DecayEnergy
  CatalanCore.Decay.ComplexEnergy CatalanCore.Decay.WedgeBounds CatalanCore.Decay.ComplexTaylor
  CatalanCore.Tools.Joukowski CatalanCore.Uniform
open CatalanCore.Zeta5.Potential (chebF)

/-! ### 1. Numerical inputs -/

/-- `log 3 > 1.0986122884`. -/
theorem log_three_gt : (10986122884 / 10 ^ 10 : ℝ) < Real.log 3 := by
  have h2 := Real.log_two_gt_d9
  have hs := Real.hasSum_log_sub_log_of_abs_lt_one (x := (1 / 5 : ℝ)) (by norm_num [abs_of_pos])
  have hp := sum_le_hasSum (Finset.range 8) (fun i _ => by positivity) hs
  have e1 : Real.log (1 + 1 / 5) - Real.log (1 - 1 / 5) = Real.log 3 - Real.log 2 := by
    rw [← Real.log_div (by norm_num) (by norm_num), ← Real.log_div (by norm_num) (by norm_num)]
    congr 1
    norm_num
  rw [e1] at hp
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hp
  norm_num at hp h2 ⊢
  linarith

/-- `jc ζ > 1` off the real axis. -/
theorem one_lt_jc_of_im_ne {ζ : ℂ} (h : ζ.im ≠ 0) : 1 < jc ζ := by
  unfold jc
  have ha : ‖ζ - 1‖ ^ 2 = (ζ.re - 1) ^ 2 + ζ.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
  have hb : ‖ζ + 1‖ ^ 2 = (ζ.re + 1) ^ 2 + ζ.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
  have htri : 2 ≤ ‖ζ - 1‖ + ‖ζ + 1‖ := by
    have := norm_sub_le (ζ + 1) (ζ - 1)
    have e : ζ + 1 - (ζ - 1) = 2 := by ring
    rw [e] at this
    simp at this
    linarith [norm_nonneg (ζ - 1)]
  by_contra hcon
  have hle : ‖ζ - 1‖ + ‖ζ + 1‖ ≤ 2 := by linarith
  have heq : ‖ζ - 1‖ + ‖ζ + 1‖ = 2 := le_antisymm hle htri
  have hy : 0 < ζ.im ^ 2 := by positivity
  have h1 : ‖ζ - 1‖ = 1 - ζ.re := by
    have : (‖ζ - 1‖ - ‖ζ + 1‖) * (‖ζ - 1‖ + ‖ζ + 1‖) = -4 * ζ.re := by
      nlinarith [ha, hb]
    rw [heq] at this
    linarith
  rw [h1] at ha
  nlinarith [ha, hy]

/-- The segment `[M, h]` of Lai's design is off its mirror image. -/
theorem lai_hsep : ∀ x ∈ Icc (-1 : ℝ) 1,
    1 < jc ((DecayInstance.laiM + DecayInstance.laiH * (x : ℂ) - starRingEnd ℂ DecayInstance.laiM) / starRingEnd ℂ DecayInstance.laiH) := by
  intro x hx
  apply one_lt_jc_of_im_ne
  have hn : 0 < Complex.normSq (starRingEnd ℂ DecayInstance.laiH) := by
    rw [Complex.normSq_pos]
    exact (_root_.map_ne_zero _).2 laiH_ne
  rw [Complex.div_im]
  simp only [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.conj_re, Complex.conj_im, Complex.sub_re, Complex.add_re, Complex.mul_re, laiM_re, laiM_im,
    laiH_re, laiH_im]
  have hx1 := hx.1
  have hx2 := hx.2
  have : (0 : ℝ) < Complex.normSq (starRingEnd ℂ DecayInstance.laiH) := hn
  rw [Complex.normSq_apply] at this ⊢
  simp only [Complex.conj_re, Complex.conj_im, laiH_re, laiH_im] at this ⊢
  rw [← sub_div]
  apply div_ne_zero _ this.ne'
  nlinarith

/-! ### 2. The W2 data -/

/-- The energy data (LD14): an exact angle partition `0 = a₀ ≤ ⋯ ≤ a_n = π`, the per-cell bounds
`U i j ≥ |G^{(j)}|/j!` of the cross potential tower on `[a_i, a_{i+1}]`, the per-cell remainders
`E i ≥ Σ_{j+k=5} U i j f_k`, and the certified inequality `I(σ) ≤ 208871/10^5` (self energy in closed
form plus `(2/π) Σ_cells crossCellBound`). -/
def LaiEnergyOK (c : ℕ → ℝ) (N : ℕ) : Prop :=
  ∃ (n : ℕ) (a : ℕ → ℝ) (Ur : ℕ → ℕ → ℝ) (Er : ℕ → ℝ),
    a 0 = 0 ∧ a n = Real.pi ∧ (∀ i < n, a i ≤ a (i + 1)) ∧
    (∀ i < n, ∀ x ∈ Icc (a i) (a (i + 1)), ∀ j ≤ 5,
      |potT (starRingEnd ℂ DecayInstance.laiM) (starRingEnd ℂ DecayInstance.laiH) c N (cosCurve DecayInstance.laiM DecayInstance.laiH) j x| /
        (j.factorial : ℝ) ≤ Ur i j) ∧
    (∀ i < n, ∑ ij ∈ Finset.antidiagonal 5, Ur i ij.1 * Vf c N ij.2 ≤ Er i) ∧
    2 * (-(c 0 ^ 2 * (Real.log ‖DecayInstance.laiH‖ - Real.log 2)) +
          ∑ k ∈ Finset.range N, c (k + 1) ^ 2 / (2 * ((k + 1 : ℕ) : ℝ))) +
      2 * ((1 / Real.pi) * ∑ i ∈ Finset.range n,
        crossCellBound (potT (starRingEnd ℂ DecayInstance.laiM) (starRingEnd ℂ DecayInstance.laiH) c N (cosCurve DecayInstance.laiM DecayInstance.laiH)) c N
          ((a i + a (i + 1)) / 2) ((a (i + 1) - a i) / 2) (Er i)) ≤ 208871 / 10 ^ 5

/-- The decay data of the Lai wedge (everything W2 supplies). -/
structure LaiDecayData (c : ℕ → ℝ) (N : ℕ) (wA wB a0 AA : ℝ) : Prop where
  hpos : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ chebF c N x
  hc0 : c 0 = 3 / 2
  hcov : LaiCover c N laiEll wA wB
  ha0 : omegaF 3 2 2 6 (2211 / 500) +
    2 * ∫ u, Real.log ‖((2211 / 500 : ℝ) : ℂ) + u‖ ∂(laiSigma c N) ≤ a0
  hA : |omegaD1 3 2 2 6 (2211 / 500) + 2 * ∫ u, ln1 u (2211 / 500) ∂(laiSigma c N)| ≤ AA
  hρ : a0 + AA ^ 2 / (2 * (49 / 100)) ≤ laiEll + 4294856306 / 10 ^ 8
  henergy : LaiEnergyOK c N

/-- The decay exponent `D(σ, ℓ) = -(κ - energyC σ + 3 ℓ)`, `κ = 27/2 - 9 log 3`, at `ℓ = laiEll`. -/
noncomputable def laiD (c : ℕ → ℝ) (N : ℕ) : ℝ :=
  -((3 : ℝ) ^ 2 * (3 / 2 - Real.log 3) - energyC (laiSigma c N) + 3 * laiEll)

/-- The energy: `I(σ) = -energyC σ ≤ 208871/10^5`. -/
theorem lai_energy_le {c : ℕ → ℝ} {N : ℕ} (hpos : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ chebF c N x)
    (h : LaiEnergyOK c N) : -energyC (laiSigma c N) ≤ 208871 / 10 ^ 5 := by
  obtain ⟨n, a, Ur, Er, a0, an, hmono, hU, hE, hb⟩ := h
  exact (energy_conj_pair_le laiH_ne hpos lai_hsep a0 an hmono hU hE).trans hb

/-- **LD22.**  `D ≥ 3344010000/10^8` and `ρ̄ = a0 + AA²/(98/100) - ℓ ≤ 4294856306/10^8`. -/
theorem lai_wedge_D {c : ℕ → ℝ} {N : ℕ} {wA wB a0 AA : ℝ} (d : LaiDecayData c N wA wB a0 AA) :
    3344010000 / 10 ^ 8 ≤ laiD c N ∧
      a0 + AA ^ 2 / (2 * (49 / 100)) - laiEll ≤ 4294856306 / 10 ^ 8 := by
  refine ⟨?_, by linarith [d.hρ]⟩
  have h1 := lai_energy_le d.hpos d.henergy
  have h2 := log_three_gt
  unfold laiD
  norm_num [laiEll] at h1 h2 ⊢
  linarith

/-! ### 3. The decay estimate, uniform in `λ ≤ Λ` -/

theorem decay_core {c : ℕ → ℝ} {N : ℕ} {wA wB a0 AA : ℝ} (d : LaiDecayData c N wA wB a0 AA)
    {ε : ℝ} (hε : 0 < ε) {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    ∃ R : ℕ, ∀ n : ℕ, R ≤ n → ∀ a b t : ℝ, 0 < laiLam a b → laiLam a b ≤ Λ →
      |t| ≤ laiLam a b * Real.exp (-((4294856306 / 10 ^ 8 : ℝ) * n)) →
      |MvPolynomial.aeval ![a, b, a * zeta3 + b * zeta4 + t] (laiJ n)| ≤
        Real.exp (-(3344010000 / 10 ^ 8 - ε) * (n : ℝ) ^ 2) := by
  obtain ⟨R₀, hR₀⟩ := lai_decay_instance d.hpos d.hc0 d.hcov d.ha0 d.hA
    (ρ := 4294856306 / 10 ^ 8) d.hρ (ε / 2) (by linarith)
  have hD := (lai_wedge_D d).1
  obtain ⟨R₁, hR₁⟩ := exists_nat_ge (6 * Real.log Λ / ε)
  refine ⟨max R₀ R₁, fun n hn a b t hl hlΛ ht => ?_⟩
  have hn0 : R₀ ≤ n := (le_max_left _ _).trans hn
  have hn1 : (R₁ : ℝ) ≤ n := by exact_mod_cast (le_max_right _ _).trans hn
  have h := hR₀ n hn0 a b t hl ht
  have hlogΛ : 0 ≤ Real.log Λ := Real.log_nonneg hΛ
  have hn' : 6 * Real.log Λ / ε ≤ n := hR₁.trans hn1
  have hnn : (0 : ℝ) ≤ n := by positivity
  have hpow : laiLam a b ^ (3 * n) ≤ Real.exp (3 * n * Real.log Λ) := by
    calc laiLam a b ^ (3 * n) ≤ Λ ^ (3 * n) := pow_le_pow_left₀ hl.le hlΛ _
      _ = Real.exp (3 * n * Real.log Λ) := by
        rw [← Real.exp_log (show 0 < Λ by linarith), ← Real.exp_nat_mul, Real.exp_log (by linarith)]
        push_cast; ring_nf
  have hlin : 3 * (n : ℝ) * Real.log Λ ≤ ε / 2 * (n : ℝ) ^ 2 := by
    have : 6 * Real.log Λ ≤ ε * n := by
      have := (div_le_iff₀ hε).mp hn'
      linarith
    nlinarith [this, hnn]
  calc _ ≤ laiLam a b ^ (3 * n) * Real.exp (-(-((3 : ℝ) ^ 2 * (3 / 2 - Real.log 3) -
          energyC (laiSigma c N) + 3 * laiEll) - ε / 2) * (n : ℝ) ^ 2) := h
    _ ≤ Real.exp (3 * n * Real.log Λ) * Real.exp (-(laiD c N - ε / 2) * (n : ℝ) ^ 2) := by
        unfold laiD
        exact mul_le_mul hpow le_rfl (Real.exp_pos _).le (Real.exp_pos _).le
    _ ≤ Real.exp (-(3344010000 / 10 ^ 8 - ε) * (n : ℝ) ^ 2) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        nlinarith [mul_nonneg hnn hnn, sq_nonneg (n : ℝ)]

/-! ### 4. LD23 -/

/-- **LD23 (plane).**  For `b ≠ 0`, `HasScaledDecay` of the plane family `aζ(3) + bζ(4)` at the
scale `n`, with `D = 3344010000/10^8`, `ρ = 4294856306/10^8`. -/
theorem lai_plane_decay {c : ℕ → ℝ} {N : ℕ} {wA wB a0 AA : ℝ} (d : LaiDecayData c N wA wB a0 AA)
    (a b : ℤ) (hb : b ≠ 0) :
    HasScaledDecay (laiPlaneFam a b) id (3344010000 / 10 ^ 8) (4294856306 / 10 ^ 8) := by
  have hb1 : (1 : ℝ) ≤ |(b : ℝ)| := by
    have : (1 : ℤ) ≤ |b| := Int.one_le_abs hb
    exact_mod_cast this
  have hl1 : (1 : ℝ) ≤ laiLam (a : ℝ) (b : ℝ) := by
    unfold laiLam; linarith [abs_nonneg (a : ℝ)]
  intro ε hε
  obtain ⟨R, hR⟩ := decay_core d hε hl1 (Λ := laiLam (a : ℝ) (b : ℝ))
  refine ⟨R, fun (n : ℕ) _ hRn t ht => ?_⟩
  have hRn' : R ≤ n := hRn
  have ht' : |t| ≤ laiLam (a : ℝ) (b : ℝ) * Real.exp (-((4294856306 / 10 ^ 8 : ℝ) * n)) := by
    refine ht.trans ?_
    have : Real.exp (-(4294856306 / 10 ^ 8 + ε) * ((id n : ℕ) : ℝ)) ≤
        Real.exp (-((4294856306 / 10 ^ 8 : ℝ) * n)) := by
      apply Real.exp_le_exp.mpr
      simp only [id]
      nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    calc _ ≤ Real.exp (-((4294856306 / 10 ^ 8 : ℝ) * n)) := this
      _ ≤ _ := le_mul_of_one_le_left (Real.exp_pos _).le hl1
  have key := hR n hRn' (a : ℝ) (b : ℝ) t (by linarith) le_rfl ht'
  show |(laiPlaneFam a b).evalR n ((laiPlaneFam a b).const + t)| ≤ _
  rw [plane_evalR]
  simpa [laiPlaneFam, id] using key

/-- **LD23 (ratio).**  `HasScaledDecay` of the ratio family at `y* = ζ(3)/ζ(4)`. -/
theorem lai_ratio_decay {c : ℕ → ℝ} {N : ℕ} {wA wB a0 AA : ℝ} (d : LaiDecayData c N wA wB a0 AA) :
    HasScaledDecay laiRatioFam id (3344010000 / 10 ^ 8) (4294856306 / 10 ^ 8) := by
  intro ε hε
  obtain ⟨R, hR⟩ := decay_core d hε (show (1 : ℝ) ≤ 6 by norm_num)
  refine ⟨R, fun (n : ℕ) _ hRn t ht => ?_⟩
  have hRn' : R ≤ n := hRn
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hexp : Real.exp (-(4294856306 / 10 ^ 8 + ε) * ((id n : ℕ) : ℝ)) ≤
      Real.exp (-((4294856306 / 10 ^ 8 : ℝ) * n)) := by
    apply Real.exp_le_exp.mpr
    simp only [id]
    nlinarith
  have hexp1 : Real.exp (-((4294856306 / 10 ^ 8 : ℝ) * n)) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith
  have ht1 : |t| ≤ Real.exp (-((4294856306 / 10 ^ 8 : ℝ) * n)) := ht.trans hexp
  have hys := ystar_bounds
  have h4p := zeta4_pos
  have h4l := zeta4_le
  have hy1 : (1 : ℝ) < zeta3 / zeta4 := hys.1
  have hy2 : zeta3 / zeta4 < 6 / 5 := hys.2
  have htl : |t| ≤ 1 := ht1.trans hexp1
  have hab : |zeta3 / zeta4 + t| ≤ 11 / 5 := by
    have h5 := abs_le.mp htl
    rw [abs_le]; constructor <;> linarith [h5.1, h5.2]
  have hlam : laiLam 1 (-(zeta3 / zeta4 + t)) = 3 + |zeta3 / zeta4 + t| := by
    unfold laiLam; rw [abs_neg]; simp
  have hpos : 0 < laiLam 1 (-(zeta3 / zeta4 + t)) := by rw [hlam]; positivity
  have hle : laiLam 1 (-(zeta3 / zeta4 + t)) ≤ 6 := by rw [hlam]; linarith
  have hwin : |t * zeta4| ≤ laiLam 1 (-(zeta3 / zeta4 + t)) *
      Real.exp (-((4294856306 / 10 ^ 8 : ℝ) * n)) := by
    rw [abs_mul, abs_of_pos h4p, hlam]
    have h0 := abs_nonneg (zeta3 / zeta4 + t)
    have hE := (Real.exp_pos (-((4294856306 / 10 ^ 8 : ℝ) * n)))
    nlinarith [mul_le_mul ht1 h4l h4p.le (Real.exp_pos _).le, mul_nonneg h0 hE.le]
  have key := hR n hRn' 1 (-(zeta3 / zeta4 + t)) (t * zeta4) hpos hle hwin
  have h3 : (1 : ℝ) * zeta3 + -(zeta3 / zeta4 + t) * zeta4 + t * zeta4 = 0 := by
    field_simp
    ring
  rw [h3] at key
  show |laiRatioFam.evalR n (laiRatioFam.const + t)| ≤ _
  rw [ratio_evalR]
  simpa [laiRatioFam, id] using key

end CatalanCore.Lai.DecayCert

open CatalanCore.Lai.DecayCert in
#print axioms lai_wedge_D
open CatalanCore.Lai.DecayCert in
#print axioms lai_plane_decay
open CatalanCore.Lai.DecayCert in
#print axioms lai_ratio_decay
