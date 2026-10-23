module

public import CatalanCore.Decay.Integ

@[expose] public section

/-!
# Rectangular integration step (WP-H2-core)

The two-family analogue of `Integ.integrand_le`, `det_bound`, `theoremN`.  The pointwise energy bound
is a hypothesis `RectEnergy` on the pair of node families `(s, t)` (supplied by `energy_rect`), so this
file is independent of the certificate.

* `integrand_le_rect` : `∏‖w‖ · ‖C(z,s)‖ ‖C(z,t)‖ ≤ e^T ∏ v_e`.
* `det_bound_rect`    : `‖det (norm · T[s,t])‖ ≤ (1/k!) e^T (atomMass + 2 A^e/β_e)^k`.
* `theoremN_rect`     : `|det T[s,t]| ≤ exp (T + N log M0)` for `k ≤ N`, `N0 ≤ R`.
-/

open Finset MeasureTheory Set
open CatalanLambda.Decay (cexpr)

namespace CatalanCore

variable {sl : ℝ}

namespace Frame

open Decay

variable {Fr : Frame}

/-- The pointwise energy hypothesis for a pair of node families (row nodes `s`, column nodes `t`):
for distinct free points (atoms / ray points) left of the poles, and every weight `q` obeying the
field bound with parameter `e`, `∑ log q + ½ (log‖C(x,s)‖² + log‖C(x,t)‖²) ≤ T`. -/
def RectEnergy (Fr : Frame) (sl : ℝ) (N0 k : ℕ) (e m0 Cl T : ℝ) (s t : Fin k → ℕ) : Prop :=
  ∀ (x : Fin k → ℂ), Function.Injective x → (∀ l, Fr.IsAtom N0 (x l) ∨ Fr.IsRay sl N0 (x l)) →
    (∀ l, m0 ≤ -(x l).re) → ∀ (q : Fin k → ℝ),
    (∀ l, Real.log (q l) ≤ (1 - e) * (Cl - 2 * Real.pi * |(x l).im|)) →
    ∑ l, Real.log (q l) + (1 / 2) * (Real.log (‖cexpr x (fun i => (s i : ℂ))‖ ^ 2)
        + Real.log (‖cexpr x (fun i => (t i : ℂ))‖ ^ 2)) ≤ T

lemma cexpr_zero_of_not_inj {k : ℕ} (x y : Fin k → ℂ) (hinj : ¬ Function.Injective x) :
    cexpr x y = 0 := by
  unfold Function.Injective at hinj
  push Not at hinj
  obtain ⟨a, b, hab, hne⟩ := hinj
  have key : ∀ l l' : Fin k, l < l' → x l = x l' → cexpr x y = 0 := by
    intro l l' hlt hxe
    unfold cexpr
    rw [div_eq_zero_iff]; left
    refine Finset.prod_eq_zero (Finset.mem_univ l) (Finset.prod_eq_zero (Finset.mem_Ioi.2 hlt) ?_)
    rw [hxe, sub_self, zero_mul]
  rcases lt_trichotomy a b with h1 | h1 | h1
  · exact key a b h1 hab
  · exact absurd h1 hne
  · exact key b a h1 hab.symm

/-- **Pointwise bound for the rectangular Andréief integrand.** -/
theorem integrand_le_rect (hFr : Fr.DecayOKs sl) {e : ℝ} (he0 : 0 < e) (he1 : e < 1)
    {m0 : ℝ} (hm0xs : m0 ≤ Fr.xs) (hm0μ : ∀ i, m0 ≤ Fr.μ i) {N0 k : ℕ} {s t : Fin k → ℕ}
    {T : ℝ} (hE : RectEnergy Fr sl N0 k e m0 (max (Real.log Fr.Aco) 0) T s t) (z : Fin k → Fr.XT N0) :
    (∏ l, ‖Fr.wT sl N0 (z l)‖) *
        (‖cexpr (fun l => Fr.ptT sl N0 (z l)) (fun i => (s i : ℂ))‖ *
          ‖cexpr (fun l => Fr.ptT sl N0 (z l)) (fun i => (t i : ℂ))‖)
      ≤ Real.exp T * ∏ l, vEps Fr sl e N0 (z l) := by
  classical
  have hC := hFr.contour
  set x : Fin k → ℂ := fun l => Fr.ptT sl N0 (z l) with hx
  have hv0 : 0 ≤ ∏ l, vEps Fr sl e N0 (z l) :=
    Finset.prod_nonneg (fun l _ => vEps_nonneg hC e N0 _)
  by_cases hinj : Function.Injective x
  · have hq0 : ∀ l, 0 < qEps Fr sl e N0 (z l) := fun l => qEps_pos hC e N0 _
    have hA := hE x hinj (fun l => ptT_atom_or_ray N0 (z l))
      (fun l => ptT_re hC hm0xs hm0μ N0 (z l))
      (fun l => qEps Fr sl e N0 (z l))
      (fun l => log_qEps_le hFr.slope.pos hC he1 N0 (z l))
    have hP0 : 0 ≤ ‖cexpr x (fun i => (s i : ℂ))‖ * ‖cexpr x (fun i => (t i : ℂ))‖ := by positivity
    have hP : 0 < ∏ l, qEps Fr sl e N0 (z l) := Finset.prod_pos (fun l _ => hq0 l)
    have step1 : (∏ l, ‖Fr.wT sl N0 (z l)‖) ≤ ∏ l, (vEps Fr sl e N0 (z l) * qEps Fr sl e N0 (z l)) :=
      Finset.prod_le_prod₀ (fun l _ => norm_nonneg _)
        (fun l _ => norm_wT_le_vq hC hFr.slope e N0 _)
    have step2 : (∏ l, qEps Fr sl e N0 (z l)) *
          (‖cexpr x (fun i => (s i : ℂ))‖ * ‖cexpr x (fun i => (t i : ℂ))‖) ≤ Real.exp T := by
      by_cases h0 : ‖cexpr x (fun i => (s i : ℂ))‖ * ‖cexpr x (fun i => (t i : ℂ))‖ = 0
      · rw [h0, mul_zero]; exact (Real.exp_pos _).le
      · have hpos : 0 < ‖cexpr x (fun i => (s i : ℂ))‖ * ‖cexpr x (fun i => (t i : ℂ))‖ :=
          lt_of_le_of_ne hP0 (Ne.symm h0)
        have hs0 : ‖cexpr x (fun i => (s i : ℂ))‖ ≠ 0 := fun h => h0 (by rw [h, zero_mul])
        have ht0 : ‖cexpr x (fun i => (t i : ℂ))‖ ≠ 0 := fun h => h0 (by rw [h, mul_zero])
        rw [← Real.log_le_iff_le_exp (mul_pos hP hpos), Real.log_mul hP.ne' hpos.ne',
          Real.log_prod (fun l _ => (hq0 l).ne'), Real.log_mul hs0 ht0]
        have e1 : Real.log (‖cexpr x (fun i => (s i : ℂ))‖ ^ 2) = 2 * Real.log ‖cexpr x (fun i => (s i : ℂ))‖ := by
          rw [Real.log_pow]; norm_num
        have e2 : Real.log (‖cexpr x (fun i => (t i : ℂ))‖ ^ 2) = 2 * Real.log ‖cexpr x (fun i => (t i : ℂ))‖ := by
          rw [Real.log_pow]; norm_num
        linarith
    calc (∏ l, ‖Fr.wT sl N0 (z l)‖) *
          (‖cexpr x (fun i => (s i : ℂ))‖ * ‖cexpr x (fun i => (t i : ℂ))‖)
        ≤ (∏ l, (vEps Fr sl e N0 (z l) * qEps Fr sl e N0 (z l))) *
          (‖cexpr x (fun i => (s i : ℂ))‖ * ‖cexpr x (fun i => (t i : ℂ))‖) :=
          mul_le_mul_of_nonneg_right step1 hP0
      _ = (∏ l, vEps Fr sl e N0 (z l)) * ((∏ l, qEps Fr sl e N0 (z l)) *
          (‖cexpr x (fun i => (s i : ℂ))‖ * ‖cexpr x (fun i => (t i : ℂ))‖)) := by
          rw [Finset.prod_mul_distrib]; ring
      _ ≤ (∏ l, vEps Fr sl e N0 (z l)) * Real.exp T := mul_le_mul_of_nonneg_left step2 hv0
      _ = _ := by ring
  · have hz0 := cexpr_zero_of_not_inj x (fun i => (s i : ℂ)) hinj
    rw [hz0]; simp
    positivity

/-- **The integrated bound for `norm · T[s,t]`.** -/
theorem det_bound_rect (hFr : Fr.DecayOKs sl) {e : ℝ} (he0 : 0 < e) (he1 : e < 1)
    {m0 : ℝ} (hm0xs : m0 ≤ Fr.xs) (hm0μ : ∀ i, m0 ≤ Fr.μ i) {N0 k : ℕ} {s t : Fin k → ℕ}
    (hs : Function.Injective s) (ht : Function.Injective t) {T : ℝ}
    (hE : RectEnergy Fr sl N0 k e m0 (max (Real.log Fr.Aco) 0) T s t) :
    ‖(Matrix.of fun i j : Fin k => (((Fr.norm : ℝ) * Fr.Tent (s i) (t j) : ℝ) : ℂ)).det‖
      ≤ (1 / (k.factorial : ℝ)) * (Real.exp T
          * (Fr.atomMass N0 + 2 * (Fr.Aco ^ e / betaE sl e)) ^ k) := by
  classical
  have hC := hFr.contour
  have hb := Fr.tent_andreief_bound_rect hC hFr.slope N0 k s t hs ht
  have hmeas := integrable_vEps hFr.slope.pos hC he0 N0
  have hGi : Integrable (fun z : Fin k → Fr.XT N0 => Real.exp T * ∏ l, vEps Fr sl e N0 (z l))
      (Measure.pi fun _ => Fr.muT N0) :=
    (Integrable.fintype_prod (f := fun (_ : Fin k) (x : Fr.XT N0) => vEps Fr sl e N0 x)
      (μ := fun _ => Fr.muT N0) (fun _ => hmeas)).const_mul _
  have hle : ∫ z : Fin k → Fr.XT N0, (∏ l, ‖Fr.wT sl N0 (z l)‖) *
            (‖(∏ l, ∏ l' ∈ Finset.Ioi l,
                ((Fr.ptT sl N0 (z l') - Fr.ptT sl N0 (z l)) * ((s l : ℂ) - s l')))
              / ∏ l, ∏ i, (Fr.ptT sl N0 (z l) - s i)‖ *
            ‖(∏ l, ∏ l' ∈ Finset.Ioi l,
                ((Fr.ptT sl N0 (z l') - Fr.ptT sl N0 (z l)) * ((t l : ℂ) - t l')))
              / ∏ l, ∏ i, (Fr.ptT sl N0 (z l) - t i)‖) ∂(Measure.pi fun _ => Fr.muT N0)
      ≤ ∫ z : Fin k → Fr.XT N0, Real.exp T * ∏ l, vEps Fr sl e N0 (z l)
          ∂(Measure.pi fun _ => Fr.muT N0) := by
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall (fun z => ?_)) hGi
      (Filter.Eventually.of_forall (fun z => ?_))
    · positivity
    · exact integrand_le_rect hFr he0 he1 hm0xs hm0μ hE z
  have hG : ∫ z : Fin k → Fr.XT N0, Real.exp T * ∏ l, vEps Fr sl e N0 (z l)
        ∂(Measure.pi fun _ => Fr.muT N0)
      = Real.exp T * (Fr.atomMass N0 + 2 * (Fr.Aco ^ e / betaE sl e)) ^ k := by
    rw [integral_const_mul, integral_fintype_prod_eq_pow (fun x => vEps Fr sl e N0 x),
      integral_vEps hFr.slope.pos hC he0]
    simp
  calc _ ≤ _ := hb
    _ ≤ (1 / (k.factorial : ℝ)) * (Real.exp T
          * (Fr.atomMass N0 + 2 * (Fr.Aco ^ e / betaE sl e)) ^ k) := by
        rw [← hG]
        exact mul_le_mul_of_nonneg_left hle (by positivity)

/-- **Theorem N, rectangular.**  Every `k × k` rectangular minor `T[s,t]` (row nodes `s`, column
nodes `t`, `k ≤ Nn`, atoms with `N0 ≤ R`) satisfies
`|det T[s,t]| ≤ exp (T + Nn · log M0)`, `M0 = Wabs R + (Wabs ⌈xs⌉ + 2A^e/β_e + 1)`. -/
theorem theoremN_rect (hFr : Fr.DecayOKs' sl) {e : ℝ} (he0 : 0 < e) (he1 : e < 1)
    {m0 : ℝ} (hm0xs : m0 ≤ Fr.xs) (hm0μ : ∀ i, m0 ≤ Fr.μ i) {N0 k Nn : ℕ} (hkN : k ≤ Nn)
    {R : ℝ} (hR : (N0 : ℝ) ≤ R) {s t : Fin k → ℕ}
    (hs : Function.Injective s) (ht : Function.Injective t) {T : ℝ}
    (hE : RectEnergy Fr sl N0 k e m0 (max (Real.log Fr.Aco) 0) T s t) :
    |(Matrix.of fun i j : Fin k => Fr.Tent (s i) (t j)).det|
      ≤ Real.exp (T + Nn * Real.log (Fr.Wabs * R + (Fr.Wabs * ⌈(Fr.xs : ℝ)⌉₊
          + 2 * (Fr.Aco ^ e / betaE sl e) + 1))) := by
  have hC := hFr.contour
  set M : Matrix (Fin k) (Fin k) ℝ := Matrix.of fun i j => Fr.Tent (s i) (t j) with hM
  have hnorm : (1 : ℝ) ≤ Fr.norm := by exact_mod_cast hFr.norm_ge
  have hcast : (Matrix.of fun i j : Fin k => (((Fr.norm : ℝ) * Fr.Tent (s i) (t j) : ℝ) : ℂ))
      = Complex.ofRealHom.mapMatrix ((Fr.norm : ℝ) • M) := by
    ext i j; simp [hM]
  have hdet : ‖(Matrix.of fun i j : Fin k => (((Fr.norm : ℝ) * Fr.Tent (s i) (t j) : ℝ) : ℂ)).det‖
      = (Fr.norm : ℝ) ^ k * |M.det| := by
    rw [hcast, ← RingHom.map_det, Matrix.det_smul]
    simp [Complex.norm_real, abs_mul, abs_of_pos (show (0 : ℝ) < Fr.norm by linarith)]
  have hb := det_bound_rect hFr.toDecayOKs he0 he1 hm0xs hm0μ hs ht hE
  rw [hdet] at hb
  set cE : ℝ := 2 * (Fr.Aco ^ e / betaE sl e) with hcE
  have hAp := Aco_pos hC
  have hcE0 : 0 ≤ cE := by
    have := betaE_pos hFr.slope.pos he0
    positivity
  have hW0 := Fr.Wabs_nonneg
  have hR0 : 0 ≤ R := le_trans (Nat.cast_nonneg _) hR
  set M0 : ℝ := Fr.Wabs * R + (Fr.Wabs * ⌈(Fr.xs : ℝ)⌉₊ + cE + 1) with hM0
  have hM01 : 1 ≤ M0 := by
    have : (0 : ℝ) ≤ Fr.Wabs * R := by positivity
    have : (0 : ℝ) ≤ Fr.Wabs * ⌈(Fr.xs : ℝ)⌉₊ := by positivity
    linarith
  have hbase : Fr.atomMass N0 + cE ≤ M0 := by
    have h1 := Fr.atomMass_le N0
    have h2 : ((N0 : ℝ) + ⌈(Fr.xs : ℝ)⌉₊) * Fr.Wabs ≤ Fr.Wabs * R + Fr.Wabs * ⌈(Fr.xs : ℝ)⌉₊ := by
      nlinarith
    rw [hM0]; linarith
  have hbase0 : 0 ≤ Fr.atomMass N0 + cE := by
    have : 0 ≤ Fr.atomMass N0 := by
      unfold atomMass
      exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    linarith
  have hpow : (Fr.atomMass N0 + cE) ^ k ≤ M0 ^ Nn :=
    (pow_le_pow_left₀ hbase0 hbase k).trans (pow_le_pow_right₀ hM01 hkN)
  have hMh : M0 ^ Nn = Real.exp (Nn * Real.log M0) := by
    rw [mul_comm, Real.exp_mul, Real.exp_log (by linarith)]; simp
  have hfac : (1 : ℝ) ≤ k.factorial := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero k)
  have hE0 := Real.exp_pos T
  have step : (Fr.norm : ℝ) ^ k * |M.det| ≤ Real.exp T * M0 ^ Nn := by
    refine hb.trans ?_
    calc (1 / (k.factorial : ℝ)) * (Real.exp T * (Fr.atomMass N0 + cE) ^ k)
        ≤ 1 * (Real.exp T * (Fr.atomMass N0 + cE) ^ k) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          rw [div_le_one (by linarith)]; exact hfac
      _ ≤ Real.exp T * M0 ^ Nn := by
          rw [one_mul]; exact mul_le_mul_of_nonneg_left hpow hE0.le
  have h1 : |M.det| ≤ (Fr.norm : ℝ) ^ k * |M.det| := by
    nlinarith [abs_nonneg M.det, one_le_pow₀ hnorm (n := k)]
  refine (h1.trans step).trans (le_of_eq ?_)
  rw [hMh, ← Real.exp_add]

end Frame
end CatalanCore
