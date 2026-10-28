module

public import CatalanCore.Uniform.Decay.Cert.Data

@[expose] public section

/-!
# Soundness of the elementary checks (lane D, package D5)

`basicOk_sound`: `D.basicOk = true` yields every semantic hypothesis of the bridge
(`exists_certCoreGs_poly` / `exists_hybridDecayDataS`) that is not a potential/energy cell:
nonvanishing segments, Bernstein bounds, exact mass, radius, conjugation involution, the smoothing
loss, and both covers.
-/

namespace CatalanCore.Uniform.Decay.Cert

open Finset CatalanCore.Uniform.Decay.Spline CatalanCore.Uniform.Decay.Tools

theorem norm_mk_le {x y R : ℚ} (h : x ^ 2 + y ^ 2 ≤ R ^ 2) (hR : 0 ≤ R) :
    ‖(⟨(x : ℝ), (y : ℝ)⟩ : ℂ)‖ ≤ (R : ℝ) := by
  have h' : (x : ℝ) ^ 2 + (y : ℝ) ^ 2 ≤ (R : ℝ) ^ 2 := by exact_mod_cast h
  have hR' : (0 : ℝ) ≤ R := by exact_mod_cast hR
  have hsq : ‖(⟨(x : ℝ), (y : ℝ)⟩ : ℂ)‖ ^ 2 = (x : ℝ) ^ 2 + (y : ℝ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp only; ring
  by_contra hc
  push_neg at hc
  nlinarith [norm_nonneg (⟨(x : ℝ), (y : ℝ)⟩ : ℂ)]

theorem le_norm_mk {x y L : ℚ} (h : L ^ 2 ≤ x ^ 2 + y ^ 2) (hL : 0 ≤ L) :
    (L : ℝ) ≤ ‖(⟨(x : ℝ), (y : ℝ)⟩ : ℂ)‖ := by
  have h' : (L : ℝ) ^ 2 ≤ (x : ℝ) ^ 2 + (y : ℝ) ^ 2 := by exact_mod_cast h
  have hL' : (0 : ℝ) ≤ L := by exact_mod_cast hL
  have hsq : ‖(⟨(x : ℝ), (y : ℝ)⟩ : ℂ)‖ ^ 2 = (x : ℝ) ^ 2 + (y : ℝ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp only; ring
  by_contra hc
  push_neg at hc
  nlinarith [norm_nonneg (⟨(x : ℝ), (y : ℝ)⟩ : ℂ)]

namespace SplineData

variable {D : SplineData}

theorem all_finRange {p : Fin D.n → Bool} (h : (List.finRange D.n).all p = true) (i : Fin D.n) :
    p i = true := by
  rw [List.all_eq_true] at h
  exact h i (List.mem_finRange i)

/-- Facts from `segOk`. -/
theorem segOk_facts (hR : 0 ≤ D.Rc) {i : Fin D.n} (h : D.segOk i = true) :
    D.A i ≠ D.B i ∧ D.l i ≠ [] ∧ bernOkK (D.l i) 0 (D.M i) = true ∧
    0 < (D.seg i).Lq ∧ 0 ≤ D.M i ∧ ((D.seg i).Lq : ℝ) ≤ ‖D.B i - D.A i‖ ∧
    ‖D.A i‖ ≤ (D.Rc : ℝ) ∧ ‖D.B i‖ ≤ (D.Rc : ℝ) ∧ (D.seg i).tau < D.n := by
  simp only [segOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h4m⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  refine ⟨?_, h2, h3, h4, h4m, ?_, norm_mk_le h6 hR, norm_mk_le h7 hR, h8⟩
  · intro heq
    have hx := congrArg Complex.re heq
    have hy := congrArg Complex.im heq
    simp only [SplineData.A, SplineData.B] at hx hy
    rcases h1 with h1 | h1
    · exact h1 (by exact_mod_cast hx)
    · exact h1 (by exact_mod_cast hy)
  · have e : D.B i - D.A i = ⟨(((D.seg i).bx - (D.seg i).ax : ℚ) : ℝ),
        (((D.seg i).byy - (D.seg i).ay : ℚ) : ℝ)⟩ := by
      apply Complex.ext <;> simp [SplineData.A, SplineData.B]
    rw [e]
    exact le_norm_mk h5 h4.le

/-- Facts from `conjOk`. -/
theorem conjOk_facts {i : Fin D.n} (h : D.conjOk i = true) :
    (D.seg (D.tauF i)).ax = (D.seg i).ax ∧ (D.seg (D.tauF i)).ay = -(D.seg i).ay ∧
    (D.seg (D.tauF i)).bx = (D.seg i).bx ∧ (D.seg (D.tauF i)).byy = -(D.seg i).byy ∧
    (D.seg (D.tauF i)).coef = (D.seg i).coef ∧ (D.seg (D.tauF i)).tau = i.1 := by
  simp only [conjOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

theorem tauF_val (hseg : ∀ i : Fin D.n, (D.seg i).tau < D.n) (i : Fin D.n) :
    (D.tauF i).1 = (D.seg i).tau := by
  simp [tauF, hseg i]

/-- Everything `basicOk` establishes, in the form the bridge consumes. -/
structure BasicFacts (D : SplineData) : Prop where
  hM : 0 < D.Mq
  hε0 : 0 < (D.ε : ℝ)
  hε1 : (D.ε : ℝ) < 1
  r0_pos : 0 < D.r0
  W_pos : 0 < D.W
  hρ : 0 < (D.rho : ℝ)
  hθ : 0 < D.theta
  hηS : 0 < D.etaS
  hRc : 0 ≤ (D.Rc : ℝ)
  hcc : 0 ≤ (D.ccert : ℝ)
  hccert : 2 * ((D.mprime : ℝ) - D.gmin) ≤ D.ccert
  hAB : ∀ i, D.A i ≠ D.B i
  hne : ∀ i, D.l i ≠ []
  hbern : ∀ i, bernOkK (D.l i) 0 (D.M i) = true
  hmass : ∑ i : Fin D.n, ∑ j ∈ range ((D.l i).length - 1 + 1), coeffs (D.l i) j / ((j : ℚ) + 1) = 1
  hAR : ∀ i, ‖D.A i‖ ≤ (D.Rc : ℝ)
  hBR : ∀ i, ‖D.B i‖ ≤ (D.Rc : ℝ)
  hτ : Function.Involutive D.tauF
  hAτ : ∀ i, D.A (D.tauF i) = (starRingEnd ℂ) (D.A i)
  hBτ : ∀ i, D.B (D.tauF i) = (starRingEnd ℂ) (D.B i)
  hlτ : ∀ i, D.l (D.tauF i) = D.l i
  hloss : Real.pi * (D.rho : ℝ) * Bs D.A D.B (fun i => (D.M i : ℝ)) ≤ D.lossS
  hray : ∀ u : ℝ, (0 : ℝ) ≤ u → u ≤ D.umax → ∃ p ∈ D.rayBoxes, (p.1 : ℝ) ≤ u ∧ u ≤ p.2
  hline : ∀ x : ℝ, (0 : ℝ) ≤ x → x ≤ 1 → ∃ p ∈ D.lineCells, (p.1 : ℝ) ≤ x ∧ x ≤ p.2
  hD : D.Dt ≤ 2 * (D.Mq * D.mprime + D.dim * D.Scap) - D.Mq ^ 2 * D.Ibound + D.Inu
    - (2 * D.Mq ^ 2 * (D.lossS + D.theta) + 2 * D.dim * D.etaS
      + D.Mq ^ 2 * (D.V * D.lossS + 2 * D.V * D.theta))

theorem basicOk_sound (h : D.basicOk = true) : BasicFacts D := by
  simp only [basicOk, dofOk, Bool.and_assoc, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hM, hε0, hε1, hr0, hW, hρ, hθ, hη, hRc, hcc, hcert, hseg, hconj, hmass, hl0, hloss,
    hray, hline, hD⟩ := h
  have hsegF : ∀ i, D.segOk i = true := fun i => all_finRange hseg i
  have F := fun i => segOk_facts hRc (hsegF i)
  have hconjF := fun i => conjOk_facts (all_finRange hconj i)
  have htauLt : ∀ i, (D.seg i).tau < D.n := fun i => (F i).2.2.2.2.2.2.2.2
  have hBs : Bs D.A D.B (fun i => (D.M i : ℝ)) ≤ (D.BsQ : ℝ) := by
    unfold Bs BsQ
    push_cast
    exact Finset.sum_le_sum fun i _ => div_le_div_of_nonneg_left (by exact_mod_cast (F i).2.2.2.2.1)
      (by exact_mod_cast (F i).2.2.2.1) (F i).2.2.2.2.2.1
  have hBs0 : 0 ≤ Bs D.A D.B (fun i => (D.M i : ℝ)) :=
    Finset.sum_nonneg fun i _ => div_nonneg (Rat.cast_nonneg.mpr (F i).2.2.2.2.1) (norm_nonneg _)
  have hlossR : (315 / 100 : ℝ) * D.rho * D.BsQ ≤ D.lossS := by
    have := (Rat.cast_le (K := ℝ)).2 hloss
    push_cast at this
    exact this
  have hρR : (0 : ℝ) < D.rho := by exact_mod_cast hρ
  have hpi : Real.pi ≤ 315 / 100 := by have := Real.pi_lt_d2; norm_num at this ⊢; linarith
  refine ⟨hM, by exact_mod_cast hε0, by exact_mod_cast hε1, hr0, hW, hρR, hθ, hη,
    by exact_mod_cast hRc, by exact_mod_cast hcc, ?_, fun i => (F i).1, fun i => (F i).2.1,
    fun i => (F i).2.2.1, hmass, fun i => (F i).2.2.2.2.2.2.1, fun i => (F i).2.2.2.2.2.2.2.1,
    fun i => Fin.ext (by rw [tauF_val htauLt]; exact (hconjF i).2.2.2.2.2),
    ?_, ?_, fun i => (hconjF i).2.2.2.2.1, ?_, fun u hu => coverOk_sound hray u (by simpa using hu), fun u hu hu1 => coverOk_sound hline u (by simpa using hu) (by simpa using hu1), hD⟩
  · exact_mod_cast hcert
  · intro i
    obtain ⟨a1, a2, -, -, -, -⟩ := hconjF i
    apply Complex.ext <;> simp [SplineData.A, a1, a2]
  · intro i
    obtain ⟨-, -, b1, b2, -, -⟩ := hconjF i
    apply Complex.ext <;> simp [SplineData.B, b1, b2]
  · calc Real.pi * (D.rho : ℝ) * Bs D.A D.B (fun i => (D.M i : ℝ))
        ≤ (315 / 100 : ℝ) * D.rho * Bs D.A D.B (fun i => (D.M i : ℝ)) := by
          apply mul_le_mul_of_nonneg_right _ hBs0
          exact mul_le_mul_of_nonneg_right hpi hρR.le
      _ ≤ (315 / 100 : ℝ) * D.rho * D.BsQ := mul_le_mul_of_nonneg_left hBs (by positivity)
      _ ≤ D.lossS := hlossR

end SplineData

end CatalanCore.Uniform.Decay.Cert
