module

public import CatalanCore.Uniform.Decay.PolyChain.Integ
public import CatalanCore.Uniform.Decay.Jet.Window
public import CatalanCore.Uniform.Decay.Cert.AllMinor
public import CatalanCore.Uniform.Decay.Cert.FullTent
public import CatalanCore.Uniform.Decay.PolyChain.AllMinor
public import CatalanCore.Uniform.Decay.PolyChain.CheckMain

@[expose] public section
set_option Elab.async false

/-!
# Theorem N for jets (lane H, wave H2c; ledger S15)

The jet copy of `integrand_le_poly`, `det_bound_poly` and `theoremN_poly` (`PolyChain.Integ`).  The reference
frame `Fr` supplies the polygon space `Fr.XT N0` (atoms and the two rays), the positions `polyPt`, the
majorant `vP`, `qP` and the energy hypothesis `PolyEnergy`, exactly as in `PolyChain`; what changes is the
integrand: a `JetRep` carries the weight `W`, the row functions `rows` (the jets of the Cauchy rows at the
atoms), the Löwner entries `Φ` and the three facts a jet source gives:

* `weight`: `‖W‖` is at most `cw` times the majorant `vP · qP` of the reference;
* `andreief`: the rectangular Andréief bound for the minors of `Φ`, in terms of the determinants of the rows;
* `jet` (Lemma J): the determinant of the rows is at most `exp (k (c1 + c2 log (k+1)))` times the Cauchy
  expression of the reference positions.

`theoremN_jet`: every `k × k` minor of `Φ` is at most
`exp (T + Nn (log (cw M0) + 2 c1 + 2 c2 log (Nn+1)))`, the extra `O(Nn log Nn)` being absorbed later into `o(r²)`.
-/

open Finset MeasureTheory Set
open CatalanLambda.Decay (cexpr)

namespace CatalanCore.Uniform.Decay.Jet

open CatalanCore CatalanCore.Decay CatalanCore.Uniform.Decay.Polygon CatalanCore.Uniform.Decay.PolyChain
  CatalanCore.Uniform.Support

/-- A jet source over the reference frame `Fr`. -/
structure JetRep (Fr : Frame) (N0 : ℕ) (pts : List ℂ) (d : ℂ) (C : ℝ) where
  W : Fr.XT N0 → ℂ
  rows : ℕ → Fr.XT N0 → ℂ
  Φ : ℕ → ℕ → ℝ
  cw : ℝ
  hcw : 1 ≤ cw
  c1 : ℝ
  c2 : ℝ
  hc1 : 0 ≤ c1
  hc2 : 0 ≤ c2
  weight : ∀ e : ℝ, 0 < e → e < 1 → ∀ z, ‖W z‖ ≤ cw * (vP Fr N0 pts d C e z * qP Fr N0 pts d C e z)
  andreief : ∀ (k : ℕ) (s t : Fin k → ℕ), Function.Injective s → Function.Injective t →
    ‖(Matrix.of fun i j : Fin k => ((Φ (s i) (t j) : ℝ) : ℂ)).det‖ ≤
      (1 / (k.factorial : ℝ)) * ∫ z : Fin k → Fr.XT N0,
        (∏ l, ‖W (z l)‖) *
          (‖(Matrix.of fun i l : Fin k => rows (s i) (z l)).det‖ *
            ‖(Matrix.of fun j l : Fin k => rows (t j) (z l)).det‖) ∂(Measure.pi fun _ => Fr.muT N0)
  jet : ∀ (k : ℕ) (s : Fin k → ℕ), Function.Injective s → ∀ z : Fin k → Fr.XT N0,
    ‖(Matrix.of fun i l : Fin k => rows (s i) (z l)).det‖ ≤
      Real.exp (k * (c1 + c2 * Real.log ((k : ℝ) + 1))) *
        ‖cexpr (fun l => polyPt Fr N0 pts d (z l)) (fun i => (s i : ℂ))‖

variable {Fr : Frame}

/-- **Pointwise bound of the jet Andréief integrand.** -/
theorem integrand_le_jet {N0 : ℕ} {pts : List ℂ} {d : ℂ} {C V : ℝ}
    (hS : SourceRep Fr N0 pts d C V) (J : JetRep Fr N0 pts d C) {e : ℝ} (he0 : 0 < e) (he1 : e < 1)
    {k : ℕ} {s t : Fin k → ℕ} (hs : Function.Injective s) (ht : Function.Injective t) {T : ℝ}
    (hE : PolyEnergy Fr N0 pts d k e (Real.log (amp C)) T s t) (z : Fin k → Fr.XT N0) :
    (∏ l, ‖J.W (z l)‖) *
        (‖(Matrix.of fun i l : Fin k => J.rows (s i) (z l)).det‖ *
          ‖(Matrix.of fun j l : Fin k => J.rows (t j) (z l)).det‖)
      ≤ J.cw ^ k * Real.exp (k * (J.c1 + J.c2 * Real.log ((k : ℝ) + 1))) ^ 2 *
        (Real.exp T * ∏ l, vP Fr N0 pts d C e (z l)) := by
  classical
  set x : Fin k → ℂ := fun l => polyPt Fr N0 pts d (z l) with hx
  set Jf : ℝ := Real.exp (k * (J.c1 + J.c2 * Real.log ((k : ℝ) + 1))) with hJf
  have hJf0 : 0 ≤ Jf := (Real.exp_pos _).le
  have hv0 : 0 ≤ ∏ l, vP Fr N0 pts d C e (z l) :=
    Finset.prod_nonneg (fun l _ => vP_nonneg N0 pts d C e _)
  have hcw0 : 0 ≤ J.cw := by linarith [J.hcw]
  have hbs := J.jet k s hs z
  have hbt := J.jet k t ht z
  have hq0 : ∀ l, 0 < qP Fr N0 pts d C e (z l) := fun l => qP_pos N0 pts d C e _
  have hW : (∏ l, ‖J.W (z l)‖) ≤
      J.cw ^ k * ∏ l, (vP Fr N0 pts d C e (z l) * qP Fr N0 pts d C e (z l)) := by
    calc (∏ l, ‖J.W (z l)‖) ≤ ∏ l, (J.cw * (vP Fr N0 pts d C e (z l) * qP Fr N0 pts d C e (z l))) :=
          Finset.prod_le_prod₀ (fun l _ => norm_nonneg _) (fun l _ => J.weight e he0 he1 _)
      _ = _ := by rw [Finset.prod_mul_distrib]; simp
  by_cases hinj : Function.Injective x
  · have hA := hE x hinj (fun l => ⟨z l, rfl⟩)
      (fun l => qP Fr N0 pts d C e (z l)) (fun l => log_qP_le hS he1 (z l))
    have hP0 : 0 ≤ ‖cexpr x (fun i => (s i : ℂ))‖ * ‖cexpr x (fun i => (t i : ℂ))‖ := by positivity
    have hP : 0 < ∏ l, qP Fr N0 pts d C e (z l) := Finset.prod_pos (fun l _ => hq0 l)
    have step2 : (∏ l, qP Fr N0 pts d C e (z l)) *
          (‖cexpr x (fun i => (s i : ℂ))‖ * ‖cexpr x (fun i => (t i : ℂ))‖) ≤ Real.exp T := by
      by_cases h0 : ‖cexpr x (fun i => (s i : ℂ))‖ * ‖cexpr x (fun i => (t i : ℂ))‖ = 0
      · rw [h0, mul_zero]; exact (Real.exp_pos _).le
      · have hpos := lt_of_le_of_ne hP0 (Ne.symm h0)
        have hs0 : ‖cexpr x (fun i => (s i : ℂ))‖ ≠ 0 := fun h => h0 (by rw [h, zero_mul])
        have ht0 : ‖cexpr x (fun i => (t i : ℂ))‖ ≠ 0 := fun h => h0 (by rw [h, mul_zero])
        rw [← Real.log_le_iff_le_exp (mul_pos hP hpos), Real.log_mul hP.ne' hpos.ne',
          Real.log_prod (fun l _ => (hq0 l).ne'), Real.log_mul hs0 ht0]
        have e1 : Real.log (‖cexpr x (fun i => (s i : ℂ))‖ ^ 2)
            = 2 * Real.log ‖cexpr x (fun i => (s i : ℂ))‖ := by
          rw [Real.log_pow]; norm_num
        have e2 : Real.log (‖cexpr x (fun i => (t i : ℂ))‖ ^ 2)
            = 2 * Real.log ‖cexpr x (fun i => (t i : ℂ))‖ := by
          rw [Real.log_pow]; norm_num
        linarith
    have hdets : ‖(Matrix.of fun i l : Fin k => J.rows (s i) (z l)).det‖ *
        ‖(Matrix.of fun j l : Fin k => J.rows (t j) (z l)).det‖ ≤
        Jf ^ 2 * (‖cexpr x (fun i => (s i : ℂ))‖ * ‖cexpr x (fun i => (t i : ℂ))‖) := by
      calc _ ≤ (Jf * ‖cexpr x (fun i => (s i : ℂ))‖) * (Jf * ‖cexpr x (fun i => (t i : ℂ))‖) :=
            mul_le_mul hbs hbt (norm_nonneg _) (by positivity)
        _ = _ := by ring
    calc (∏ l, ‖J.W (z l)‖) * (‖(Matrix.of fun i l : Fin k => J.rows (s i) (z l)).det‖ *
          ‖(Matrix.of fun j l : Fin k => J.rows (t j) (z l)).det‖)
        ≤ (J.cw ^ k * ∏ l, (vP Fr N0 pts d C e (z l) * qP Fr N0 pts d C e (z l))) *
          (Jf ^ 2 * (‖cexpr x (fun i => (s i : ℂ))‖ * ‖cexpr x (fun i => (t i : ℂ))‖)) :=
          mul_le_mul hW hdets (by positivity)
            (mul_nonneg (pow_nonneg hcw0 k) (Finset.prod_nonneg fun l _ =>
              mul_nonneg (vP_nonneg N0 pts d C e _) (hq0 l).le))
      _ = (J.cw ^ k * Jf ^ 2) * ((∏ l, vP Fr N0 pts d C e (z l)) *
          ((∏ l, qP Fr N0 pts d C e (z l)) *
            (‖cexpr x (fun i => (s i : ℂ))‖ * ‖cexpr x (fun i => (t i : ℂ))‖))) := by
          rw [Finset.prod_mul_distrib]; ring
      _ ≤ (J.cw ^ k * Jf ^ 2) * ((∏ l, vP Fr N0 pts d C e (z l)) * Real.exp T) := by
          gcongr
      _ = _ := by ring
  · have hz0 := Frame.cexpr_zero_of_not_inj x (fun i => (s i : ℂ)) hinj
    have h0 : ‖(Matrix.of fun i l : Fin k => J.rows (s i) (z l)).det‖ ≤ 0 := by
      have := hbs; rw [hz0] at this; simpa using this
    have h0' : ‖(Matrix.of fun i l : Fin k => J.rows (s i) (z l)).det‖ = 0 :=
      le_antisymm h0 (norm_nonneg _)
    rw [h0']
    simp only [zero_mul, mul_zero]
    positivity

/-- **The integrated bound for the minors of `Φ`.** -/
theorem det_bound_jet {N0 : ℕ} {pts : List ℂ} {d : ℂ} {C V : ℝ}
    (hS : SourceRep Fr N0 pts d C V) (J : JetRep Fr N0 pts d C) {e : ℝ} (he0 : 0 < e) (he1 : e < 1)
    {L : ℝ} (hL : chainLen ((Fr.xstar N0 : ℝ) : ℂ) pts ≤ L) {k : ℕ} {s t : Fin k → ℕ}
    (hs : Function.Injective s) (ht : Function.Injective t) {T : ℝ}
    (hE : PolyEnergy Fr N0 pts d k e (Real.log (amp C)) T s t) :
    ‖(Matrix.of fun i j : Fin k => ((J.Φ (s i) (t j) : ℝ) : ℂ)).det‖
      ≤ (1 / (k.factorial : ℝ)) * (J.cw ^ k *
          Real.exp (k * (J.c1 + J.c2 * Real.log ((k : ℝ) + 1))) ^ 2 * (Real.exp T
          * (Fr.atomMass N0 + 2 * (amp C ^ e * (L + ‖d‖ / ((2 * Real.pi * e) * d.im)))) ^ k)) := by
  classical
  have hb := J.andreief k s t hs ht
  have hmeas := integrable_vP hS he0
  set K : ℝ := J.cw ^ k * Real.exp (k * (J.c1 + J.c2 * Real.log ((k : ℝ) + 1))) ^ 2 with hK
  have hK0 : 0 ≤ K := by
    have : 0 ≤ J.cw := by linarith [J.hcw]
    positivity
  have hGi : Integrable (fun z : Fin k → Fr.XT N0 => K * (Real.exp T * ∏ l, vP Fr N0 pts d C e (z l)))
      (Measure.pi fun _ => Fr.muT N0) :=
    ((Integrable.fintype_prod (f := fun (_ : Fin k) (x : Fr.XT N0) => vP Fr N0 pts d C e x)
      (μ := fun _ => Fr.muT N0) (fun _ => hmeas)).const_mul _).const_mul _
  have hle : ∫ z : Fin k → Fr.XT N0, (∏ l, ‖J.W (z l)‖) *
        (‖(Matrix.of fun i l : Fin k => J.rows (s i) (z l)).det‖ *
          ‖(Matrix.of fun j l : Fin k => J.rows (t j) (z l)).det‖) ∂(Measure.pi fun _ => Fr.muT N0)
      ≤ ∫ z : Fin k → Fr.XT N0, K * (Real.exp T * ∏ l, vP Fr N0 pts d C e (z l))
          ∂(Measure.pi fun _ => Fr.muT N0) := by
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall (fun z => ?_)) hGi
      (Filter.Eventually.of_forall (fun z => ?_))
    · positivity
    · exact integrand_le_jet hS J he0 he1 hs ht hE z
  have hint0 : 0 ≤ ∫ x, vP Fr N0 pts d C e x ∂(Fr.muT N0) :=
    integral_nonneg (fun x => vP_nonneg N0 pts d C e x)
  have hG : ∫ z : Fin k → Fr.XT N0, K * (Real.exp T * ∏ l, vP Fr N0 pts d C e (z l))
        ∂(Measure.pi fun _ => Fr.muT N0)
      ≤ K * (Real.exp T * (Fr.atomMass N0 + 2 * (amp C ^ e * (L + ‖d‖ / ((2 * Real.pi * e) * d.im)))) ^ k) := by
    rw [integral_const_mul, integral_const_mul, integral_fintype_prod_eq_pow
      (fun x => vP Fr N0 pts d C e x), Fintype.card_fin]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hint0 (integral_vP_le hS he0 hL) k) (Real.exp_pos T).le) hK0
  calc _ ≤ _ := hb
    _ ≤ _ := by
        exact mul_le_mul_of_nonneg_left (hle.trans hG) (by positivity)

/-- **Theorem N for jets.** -/
theorem theoremN_jet {N0 : ℕ} {pts : List ℂ} {d : ℂ} {C V : ℝ}
    (hS : SourceRep Fr N0 pts d C V) (J : JetRep Fr N0 pts d C) (hd : 0 < d.im) {e : ℝ} (he0 : 0 < e)
    (he1 : e < 1) {L : ℝ} (hL : chainLen ((Fr.xstar N0 : ℝ) : ℂ) pts ≤ L) {k Nn : ℕ} (hkN : k ≤ Nn)
    {R : ℝ} (hR : (N0 : ℝ) ≤ R) {s t : Fin k → ℕ}
    (hs : Function.Injective s) (ht : Function.Injective t) {T : ℝ}
    (hE : PolyEnergy Fr N0 pts d k e (Real.log (amp C)) T s t) :
    |(Matrix.of fun i j : Fin k => J.Φ (s i) (t j)).det|
      ≤ Real.exp (T + Nn * (Real.log (J.cw * (Fr.Wabs * R + (Fr.Wabs * ⌈(Fr.xs : ℝ)⌉₊
          + 2 * (amp C ^ e * (L + ‖d‖ / ((2 * Real.pi * e) * d.im))) + 1))) +
          2 * (J.c1 + J.c2 * Real.log ((Nn : ℝ) + 1)))) := by
  set M : Matrix (Fin k) (Fin k) ℝ := Matrix.of fun i j => J.Φ (s i) (t j) with hM
  have hcast : (Matrix.of fun i j : Fin k => ((J.Φ (s i) (t j) : ℝ) : ℂ))
      = Complex.ofRealHom.mapMatrix M := by
    ext i j; simp [hM]
  have hdet : ‖(Matrix.of fun i j : Fin k => ((J.Φ (s i) (t j) : ℝ) : ℂ)).det‖ = |M.det| := by
    rw [hcast, ← RingHom.map_det]
    simp
  have hb := det_bound_jet hS J he0 he1 hL hs ht hE
  rw [hdet] at hb
  have hL0 : 0 ≤ L := (chainLen_nonneg _ _).trans hL
  set cE : ℝ := 2 * (amp C ^ e * (L + ‖d‖ / ((2 * Real.pi * e) * d.im))) with hcE
  have hcE0 : 0 ≤ cE := by
    have := amp_pos C
    have : 0 < (2 * Real.pi * e) * d.im := by have := Real.pi_pos; positivity
    rw [hcE]; positivity
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
      unfold Frame.atomMass
      exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    linarith
  have hcw : 1 ≤ J.cw := J.hcw
  have hcwM : 1 ≤ J.cw * M0 := by nlinarith
  have hpow : J.cw ^ k * (Fr.atomMass N0 + cE) ^ k ≤ (J.cw * M0) ^ Nn := by
    rw [← mul_pow]
    exact (pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hbase (by linarith)) k).trans
      (pow_le_pow_right₀ hcwM hkN)
  have hfac : (1 : ℝ) ≤ k.factorial := by
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero k)
  have hkN' : (k : ℝ) ≤ Nn := by exact_mod_cast hkN
  have hJ2 : Real.exp (k * (J.c1 + J.c2 * Real.log ((k : ℝ) + 1))) ^ 2 ≤
      Real.exp (Nn * (2 * (J.c1 + J.c2 * Real.log ((Nn : ℝ) + 1)))) := by
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.2
    have hl : Real.log ((k : ℝ) + 1) ≤ Real.log ((Nn : ℝ) + 1) :=
      Real.log_le_log (by positivity) (by linarith)
    have h1 : J.c1 + J.c2 * Real.log ((k : ℝ) + 1) ≤ J.c1 + J.c2 * Real.log ((Nn : ℝ) + 1) := by
      have := J.hc2
      nlinarith
    have h0 : 0 ≤ J.c1 + J.c2 * Real.log ((k : ℝ) + 1) := by
      have := J.hc1
      have := J.hc2
      have := Real.log_nonneg (show (1 : ℝ) ≤ (k : ℝ) + 1 by linarith [Nat.cast_nonneg (α := ℝ) k])
      positivity
    push_cast
    nlinarith
  have hE0 := Real.exp_pos T
  have hmain : |M.det| ≤ Real.exp T * (J.cw * M0) ^ Nn *
      Real.exp (Nn * (2 * (J.c1 + J.c2 * Real.log ((Nn : ℝ) + 1)))) := by
    refine hb.trans ?_
    calc (1 / (k.factorial : ℝ)) * (J.cw ^ k * Real.exp (k * (J.c1 + J.c2 * Real.log ((k : ℝ) + 1))) ^ 2 *
          (Real.exp T * (Fr.atomMass N0 + cE) ^ k))
        = (1 / (k.factorial : ℝ)) * (Real.exp T * (J.cw ^ k * (Fr.atomMass N0 + cE) ^ k) *
          Real.exp (k * (J.c1 + J.c2 * Real.log ((k : ℝ) + 1))) ^ 2) := by ring
      _ ≤ 1 * (Real.exp T * (J.cw * M0) ^ Nn *
          Real.exp (Nn * (2 * (J.c1 + J.c2 * Real.log ((Nn : ℝ) + 1))))) := by
          apply mul_le_mul _ _ (by positivity) (by norm_num)
          · rw [div_le_one (by linarith)]; exact hfac
          · exact mul_le_mul (mul_le_mul_of_nonneg_left hpow hE0.le) hJ2 (by positivity)
              (by positivity)
      _ = _ := by ring
  refine hmain.trans (le_of_eq ?_)
  have hpos : 0 < J.cw * M0 := by linarith
  have e1 : (J.cw * M0) ^ Nn = Real.exp (Nn * Real.log (J.cw * M0)) := by
    rw [Real.exp_nat_mul, Real.exp_log hpos]
  rw [e1, ← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

/-- The hybrid matrix of two sequences at `x = const` is the matrix of the entries `Φ` on the node lists. -/
theorem seqFullN_eq_phi (f g : ℕ → ℚ) (Φ : ℕ → ℕ → ℝ) (const : ℝ)
    (hΦ : ∀ x y, Φ x y = (lw f g x y : ℝ) + (if x = y then const else 0))
    {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (c : ι → ℕ) (xs ys : κ → ℕ) (hc : Function.Injective c)
    (hcy : ∀ a j, c a ≠ ys j) (hxc : ∀ i b, xs i ≠ c b) (hxy : ∀ i j, xs i ≠ ys j) :
    seqFullN f g c xs ys const =
      Matrix.of fun p q => Φ (Sum.elim c xs p) (Sum.elim c ys q) := by
  ext p q
  rcases p with a | i <;> rcases q with b | j
  · have he : (c a = c b) ↔ a = b := ⟨fun h => hc h, fun h => by rw [h]⟩
    simp [seqFullN, Rect.Blk, Matrix.fromBlocks, Matrix.one_apply, hΦ, he, add_comm]
  · simp [seqFullN, Rect.Blk, Matrix.fromBlocks, hΦ, hcy a j]
  · simp [seqFullN, Rect.Blk, Matrix.fromBlocks, hΦ, hxc i b]
  · simp [seqFullN, Rect.Blk, Matrix.fromBlocks, hΦ, hxy i j]

/-- The logarithmic budget of the jets: `Nn (log (cw (A r + B)) + 2 (c1 + c2 log (Nn+1))) ≤ K r (log (r+1) + 1)`. -/
theorem jet_N_log_le {Nn Mm rc A B r cw c1 c2 : ℝ} (hN0 : 0 ≤ Nn) (hMm : 0 ≤ Mm) (hrc : 0 ≤ rc)
    (hA : 0 ≤ A) (hB : 1 ≤ B) (hr : 1 ≤ r) (hN : Nn ≤ Mm * r + rc) (hcw : 1 ≤ cw)
    (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2) :
    Nn * (Real.log (cw * (A * r + B)) + 2 * (c1 + c2 * Real.log (Nn + 1))) ≤
      (((Mm + rc) * (1 + |Real.log (cw * A + cw * B)|)) + 2 * c1 * (Mm + rc) +
        2 * c2 * (Mm + rc) * (1 + Real.log (Mm + rc + 1))) * r * (Real.log (r + 1) + 1) := by
  have h1 := CatalanCore.Uniform.Decay.Cert.N_log_le (Nn := Nn) (Mm := Mm) (rc := rc) (A := cw * A)
    (B := cw * B) (r := r) hN0 hMm hrc (by positivity) (by nlinarith) hr hN
  have e1 : cw * (A * r + B) = cw * A * r + cw * B := by ring
  rw [e1]
  have hr1 : 0 ≤ Real.log (r + 1) := Real.log_nonneg (by linarith)
  have hNr : Nn ≤ (Mm + rc) * r := by nlinarith
  have hl2 : Real.log (Nn + 1) ≤ Real.log (Mm + rc + 1) + Real.log (r + 1) := by
    rw [← Real.log_mul (by positivity) (by linarith)]
    exact Real.log_le_log (by linarith) (by nlinarith)
  have hl0 : 0 ≤ Real.log (Mm + rc + 1) := Real.log_nonneg (by linarith)
  have hlogN : 0 ≤ Real.log (Nn + 1) := Real.log_nonneg (by linarith)
  have hsum : Real.log (Mm + rc + 1) + Real.log (r + 1) ≤
      (1 + Real.log (Mm + rc + 1)) * (Real.log (r + 1) + 1) := by nlinarith
  have h2 : Nn * (2 * (c1 + c2 * Real.log (Nn + 1))) ≤
      (2 * c1 * (Mm + rc) + 2 * c2 * (Mm + rc) * (1 + Real.log (Mm + rc + 1))) * r *
        (Real.log (r + 1) + 1) := by
    have hlN : Real.log (Nn + 1) ≤ (1 + Real.log (Mm + rc + 1)) * (Real.log (r + 1) + 1) :=
      hl2.trans hsum
    calc Nn * (2 * (c1 + c2 * Real.log (Nn + 1)))
        = 2 * c1 * Nn + 2 * c2 * (Nn * Real.log (Nn + 1)) := by ring
      _ ≤ 2 * c1 * ((Mm + rc) * r) + 2 * c2 * (((Mm + rc) * r) *
          ((1 + Real.log (Mm + rc + 1)) * (Real.log (r + 1) + 1))) := by
          gcongr
      _ ≤ 2 * c1 * ((Mm + rc) * r) * (Real.log (r + 1) + 1) + 2 * c2 * (((Mm + rc) * r) *
          ((1 + Real.log (Mm + rc + 1)) * (Real.log (r + 1) + 1))) := by
          have : 2 * c1 * ((Mm + rc) * r) ≤ 2 * c1 * ((Mm + rc) * r) * (Real.log (r + 1) + 1) := by
            have h0 : 0 ≤ 2 * c1 * ((Mm + rc) * r) := by positivity
            nlinarith
          linarith
      _ = _ := by ring
  have : Nn * (Real.log (cw * A * r + cw * B) + 2 * (c1 + c2 * Real.log (Nn + 1))) =
      Nn * Real.log (cw * A * r + cw * B) + Nn * (2 * (c1 + c2 * Real.log (Nn + 1))) := by ring
  rw [this]
  nlinarith [h1, h2]

open Matrix CatalanCore.Uniform CatalanLambda.Decay Rect CatalanCore.Uniform.Decay.Assembly
  CatalanCore.Uniform.Decay.Cert in
set_option maxHeartbeats 8000000 in
/-- **Jet energy estimate gives `SeqAllMinorDecay`.** -/
theorem hasSeqAllMinorDecay_of_certG_poly (G : BlockGeom) {Fr : Frame} (hC : Fr.ContourOK)
    (hAR : ∀ i : Fin Fr.d, ((⌊Fr.xs - Fr.μ i⌋ : ℤ) : ℚ) + Fr.μ i ≤ Fr.n0off)
    {P : RatPolygon} (hP : P.OK)
    {K : ℕ} {ρ ε : ℝ} {c : Fin K → ℂ} {wt : Fin K → ℝ}
    (F : CertCoreP P K ρ ε c wt) (hw0 : ∀ k, 0 ≤ wt k) {Rc : ℝ}
    (hc : ∀ k, ‖c k‖ ≤ Rc)
    (hg : ∀ s : ℂ, F.g s = (G.totalMass : ℝ) * Usig ρ c wt s - G.nodePot s +
      (1 - ε) * Real.pi * |s.im|)
    {Bd : ℝ} (hBd0 : 0 ≤ Bd) (hBc : ∀ i, ((G.common.block i).v : ℝ) ≤ Bd)
    (hBr : ∀ i, ((G.row.block i).v : ℝ) ≤ Bd) (hBq : ∀ i, ((G.column.block i).v : ℝ) ≤ Bd)
    {m0 : ℝ} (hm0 : 0 < m0) (hm0μ : ∀ i, m0 ≤ Fr.μ i)
    {e : ℝ} (he0 : 0 < e) (heε : e < ε) {ℓ cB : ℝ}
    (hℓ : ∀ (r a : ℕ), a ∈ (G.geometry r).C → ℓ ≤ F.g ((a : ℂ) / (r : ℂ)))
    (hcB : 2 * ((F.mprime : ℝ) - ℓ) ≤ cB)
    (f g : ℕ → ℚ) (const : ℝ) (cw0 c10 c20 : ℝ)
    (hJall : ∃ J : ∀ r : ℕ, Rmin Fr P ≤ (r : ℝ) →
      JetRep Fr (N0Of Fr P.r0 r) (physL Fr P r) P.tailDir (CP Fr (P.qRat : ℝ)),
      (∀ r hr x y, (J r hr).Φ x y = (lw f g x y : ℝ) + (if x = y then const else 0)) ∧
      (∀ r hr, (J r hr).cw = cw0) ∧ (∀ r hr, (J r hr).c1 = c10) ∧ (∀ r hr, (J r hr).c2 = c20)) :
    SeqAllMinorDecay f g const G.geometry
      (2 * (G.totalMass : ℝ) * F.mprime + 2 * ((Fr.d : ℝ) * F.Sbase)
        - (G.totalMass : ℝ) ^ 2 * F.Ibound + G.nodeEnergy) cB := by
  classical
  intro δ hδ
  have hM := G.totalMass_nonneg'
  have hxs : (0 : ℝ) < Fr.xs := by exact_mod_cast hC.xs_pos
  have hr0 : (0 : ℝ) < P.r0 := by exact_mod_cast hP.r0_pos
  have hW0 : (0 : ℝ) < F.W := by exact_mod_cast F.W_pos
  have he1 : e < 1 := lt_trans heε F.hε1
  have hv0 : (0 : ℝ) ≤ P.vRat := by exact_mod_cast P.vRat_nonneg
  have hn0 : (0 : ℝ) ≤ Fr.n0off := Nat.cast_nonneg _
  set Cq : ℝ := CP Fr (P.qRat : ℝ) with hCq
  set a0 : ℝ := P.r0 + P.vRat + Fr.xs + Fr.n0off + 1 with ha0
  have ha1 : 1 ≤ a0 := by rw [ha0]; linarith
  set m1 : ℝ := min m0 1 with hm1d
  have hm1 : 0 < m1 := lt_min hm0 one_pos
  obtain ⟨R0, hR0⟩ := G.energy_geom_small_d (K := K) (ρ := ρ) (ε := ε) (c := c) (wt := wt) F.hρ hw0
    F.hm hc F.g hg hBd0 hBc hBr hBq hm1 ha1 (mp := (F.mprime : ℝ)) (Ibd := (F.Ibound : ℝ))
    (Scap := (Fr.d : ℝ) * F.Sbase)
    (Cdef := (Fr.d : ℝ) * ∑ i, max ((F.mprime : ℝ) - F.segG i) 0)
    F.hε0 he0 heε (log_amp_nonneg Cq) F.I_ok hcB (half_pos hδ)
  have hW1 := Fr.Wabs_nonneg
  have hAp := amp_pos Cq
  have hd := RatPolygon.tailDir_im_pos hP
  set L0 : ℝ := chainLen 0 (P.verts.map P.off) with hL0d
  have hL00 : 0 ≤ L0 := chainLen_nonneg _ _
  set Dd : ℝ := ‖P.tailDir‖ / ((2 * Real.pi * e) * P.tailDir.im) with hDd
  have hDd0 : 0 ≤ Dd := by
    have : 0 < (2 * Real.pi * e) * P.tailDir.im := by have := Real.pi_pos; positivity
    positivity
  have hAe : 0 ≤ amp Cq ^ e := by positivity
  set A : ℝ := Fr.Wabs * P.r0 + 2 * (amp Cq ^ e * L0) with hA
  have hA0 : 0 ≤ A := by positivity
  set c1 : ℝ := Fr.Wabs * ⌈(Fr.xs : ℝ)⌉₊ + 2 * (amp Cq ^ e * Dd) + 1 with hc1
  have hc1' : 1 ≤ c1 := by
    have : 0 ≤ Fr.Wabs * ⌈(Fr.xs : ℝ)⌉₊ := by positivity
    have : 0 ≤ amp Cq ^ e * Dd := by positivity
    rw [hc1]; linarith
  obtain ⟨J, hΦ, hJcw, hJc1, hJc2⟩ := hJall
  have hcw1 : ∀ r hr, 1 ≤ cw0 := fun r hr => by have := (J r hr).hcw; rwa [hJcw r hr] at this
  have hKcw : 1 ≤ cw0 := by
    obtain ⟨R3', hR3'⟩ : ∃ R3 : ℕ, Rmin Fr P ≤ (R3 : ℝ) := ⟨⌈Rmin Fr P⌉₊, Nat.le_ceil _⟩
    exact hcw1 _ hR3'
  have hKc10 : 0 ≤ c10 := by
    obtain ⟨R3', hR3'⟩ : ∃ R3 : ℕ, Rmin Fr P ≤ (R3 : ℝ) := ⟨⌈Rmin Fr P⌉₊, Nat.le_ceil _⟩
    have := (J _ hR3').hc1; rwa [hJc1 _ hR3'] at this
  have hKc20 : 0 ≤ c20 := by
    obtain ⟨R3', hR3'⟩ : ∃ R3 : ℕ, Rmin Fr P ≤ (R3 : ℝ) := ⟨⌈Rmin Fr P⌉₊, Nat.le_ceil _⟩
    have := (J _ hR3').hc2; rwa [hJc2 _ hR3'] at this
  have hMrc : (0 : ℝ) ≤ (G.totalMass : ℝ) + G.rowConst := by
    have : (0 : ℝ) ≤ G.rowConst := Nat.cast_nonneg _
    positivity
  set Kc : ℝ := (((G.totalMass : ℝ) + G.rowConst) * (1 + |Real.log (cw0 * A + cw0 * c1)|)) +
    2 * c10 * ((G.totalMass : ℝ) + G.rowConst) +
    2 * c20 * ((G.totalMass : ℝ) + G.rowConst) *
      (1 + Real.log ((G.totalMass : ℝ) + G.rowConst + 1)) with hKc
  have hKc0 : 0 ≤ Kc := by
    have hl : 0 ≤ Real.log ((G.totalMass : ℝ) + G.rowConst + 1) := Real.log_nonneg (by linarith)
    rw [hKc]; positivity
  obtain ⟨R2, hR2⟩ := eventually_rlog_le hKc0 (half_pos hδ)
  obtain ⟨R3, hR3⟩ : ∃ R3 : ℕ, ∀ r : ℕ, R3 ≤ r →
      Rmin Fr P ≤ (r : ℝ) ∧ 1 + (Fr.n0off : ℝ) + Fr.xs ≤ F.W * r := by
    refine ⟨⌈Rmin Fr P + (1 + (Fr.n0off : ℝ) + Fr.xs) / F.W⌉₊, fun r hr => ?_⟩
    have hX : Rmin Fr P + (1 + (Fr.n0off : ℝ) + Fr.xs) / F.W ≤ r :=
      (Nat.le_ceil _).trans (by exact_mod_cast hr)
    have hR1 : (1 : ℝ) ≤ Rmin Fr P := le_max_left _ _
    have h2 : 0 ≤ (1 + (Fr.n0off : ℝ) + Fr.xs) / F.W := by positivity
    refine ⟨by linarith, ?_⟩
    have : (1 + (Fr.n0off : ℝ) + Fr.xs) / F.W ≤ r := by linarith
    rwa [div_le_iff₀ hW0, mul_comm] at this
  obtain ⟨R4, hR4⟩ : ∃ R4 : ℕ, ∀ r : ℕ, R4 ≤ r → 0 < (G.geometry r).C.card := by
    have hpos : (0 : ℝ) < (G.common.mass : ℝ) := by exact_mod_cast G.common_pos
    refine ⟨⌈(G.common.n : ℝ) / G.common.mass⌉₊ + 1, fun r hr => ?_⟩
    have hX : (G.common.n : ℝ) / G.common.mass < r := by
      have := Nat.le_ceil ((G.common.n : ℝ) / G.common.mass)
      have h2 : ((⌈(G.common.n : ℝ) / G.common.mass⌉₊ + 1 : ℕ) : ℝ) ≤ r := by exact_mod_cast hr
      push_cast at h2
      linarith
    have h3 : (G.common.n : ℝ) < G.common.mass * r := by
      rwa [div_lt_iff₀ hpos, mul_comm] at hX
    have h4 := (G.card_common r).1
    have h5 : (G.common.n : ℚ) < G.common.mass * r := by exact_mod_cast h3
    have h6 : (0 : ℚ) < ((G.geometry r).C.card : ℚ) := by linarith
    exact_mod_cast h6
  refine ⟨max (max R0 R2) (max R3 R4), fun r hr S => ?_⟩
  have hrR0 : R0 ≤ r := (le_max_left _ _).trans ((le_max_left _ _).trans hr)
  have hrR2 : R2 ≤ r := (le_max_right _ _).trans ((le_max_left _ _).trans hr)
  have hrR3 : R3 ≤ r := (le_max_left _ _).trans ((le_max_right _ _).trans hr)
  have hrR4 : R4 ≤ r := (le_max_right _ _).trans ((le_max_right _ _).trans hr)
  obtain ⟨hRmin, hWr⟩ := hR3 r hrR3
  have hCpos := hR4 r hrR4
  have hr1 : (1 : ℝ) ≤ r := (le_max_left _ _).trans hRmin
  have hrpos : 0 < r := by exact_mod_cast (lt_of_lt_of_le one_pos hr1)
  have hrposR : (0 : ℝ) < r := by linarith
  obtain ⟨hS, hH⟩ := polygonRep_scaled hC hP hRmin
  have hq : (|(P.qRat : ℝ)| + 2 + Fr.n0off) / (P.r0 : ℝ) ≤ r :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans hRmin
  have hfl := floor_ge (Fr := Fr) hP hq
  have hn : Fr.n0off ≤ ⌊(P.r0 : ℝ) * r⌋₊ := by
    have : (Fr.n0off : ℝ) ≤ (⌊(P.r0 : ℝ) * r⌋₊ : ℝ) := by
      have : 0 ≤ |(P.qRat : ℝ)| := abs_nonneg _
      linarith
    exact_mod_cast this
  set N0 : ℕ := N0Of Fr P.r0 r with hN0d
  obtain ⟨Jr, hJr⟩ : ∃ Jr, Jr = J r hRmin := ⟨_, rfl⟩
  have hΦr : ∀ x y, Jr.Φ x y = (lw f g x y : ℝ) + (if x = y then const else 0) := by
    subst hJr; exact hΦ r hRmin
  have hcwr : Jr.cw = cw0 := by subst hJr; exact hJcw r hRmin
  have hc1r : Jr.c1 = c10 := by subst hJr; exact hJc1 r hRmin
  have hc2r : Jr.c2 = c20 := by subst hJr; exact hJc2 r hRmin
  -- the head
  have hN1 : (N0 : ℝ) + Fr.n0off ≤ P.r0 * r := by
    rw [hN0d, N0Of_cast hn]
    have := Nat.floor_le (show (0 : ℝ) ≤ P.r0 * r by positivity)
    linarith
  have hH' : |hShift Fr P.r0 r| ≤ (F.W : ℝ) * r := by linarith
  have hmk : (G.geometry r).k = (G.geometry r).X'.card := rfl
  set k := S.card + (G.geometry r).k with hk
  let eq : (S ⊕ Fin (G.geometry r).k) ≃ Fin k := Fintype.equivFinOfCardEq (by simp [k])
  let s : Fin k → Fin ((G.geometry r).C.card + (G.geometry r).X'.card) := fun i => sIdx G r S (eq.symm i)
  have hrow : ∀ p, (G.nodeEnum r).nR (sIdx G r S p) =
      Sum.elim (fun a : S => ((a.1 : (G.geometry r).C) : ℕ)) (G.geometry r).xs p := by
    rintro (a | j)
    · exact nR_sIdx_inl a
    · exact nR_sIdx_inr j
  have hcol : ∀ p, (G.nodeEnum r).nQ (sIdx G r S p) =
      Sum.elim (fun a : S => ((a.1 : (G.geometry r).C) : ℕ)) (G.geometry r).ys p := by
    rintro (a | j)
    · exact nQ_sIdx_inl a
    · exact nQ_sIdx_inr j
  have hRinj : Function.Injective (fun i => (G.nodeEnum r).nR (s i)) := by
    intro a b h
    have h' : (G.nodeEnum r).nR (sIdx G r S (eq.symm a)) = (G.nodeEnum r).nR (sIdx G r S (eq.symm b)) := h
    rw [hrow, hrow] at h'
    exact eq.symm.injective (rowN_inj S h')
  have hQinj : Function.Injective (fun i => (G.nodeEnum r).nQ (s i)) := by
    intro a b h
    have h' : (G.nodeEnum r).nQ (sIdx G r S (eq.symm a)) = (G.nodeEnum r).nQ (sIdx G r S (eq.symm b)) := h
    rw [hcol, hcol] at h'
    exact eq.symm.injective (colN_inj S h')
  have hs : Function.Injective s := fun a b h => hRinj (by simp only [h])
  have hkeep : ∀ b : Fin ((G.geometry r).C.card + (G.geometry r).X'.card), (G.geometry r).C.card ≤ (b : ℕ) → ∃ i, s i = b := by
    intro b hb
    refine ⟨eq (Sum.inr ⟨(b : ℕ) - (G.geometry r).C.card, by have := b.isLt; omega⟩), ?_⟩
    show sIdx G r S (eq.symm (eq (Sum.inr _))) = b
    rw [Equiv.symm_apply_apply]
    exact Fin.ext (by show (G.geometry r).C.card + ((b : ℕ) - (G.geometry r).C.card) = b.val; omega)
  have hkN : k ≤ (G.geometry r).C.card + (G.geometry r).X'.card := by
    have : S.card ≤ (G.geometry r).C.card := by simpa using Finset.card_le_univ S
    simp only [hk]; omega
  have hcommon : ∀ b : Fin ((G.geometry r).C.card + (G.geometry r).X'.card), (b : ℕ) < (G.geometry r).C.card →
      ℓ ≤ F.g (((G.nodeEnum r).nR b : ℂ) / r) := fun b hb => hℓ r _ ((G.nodeEnum r).commonMem b hb)
  have hRE : PolyEnergy Fr N0 (physL Fr P r) P.tailDir k e (Real.log (amp Cq))
      (-((r : ℝ) ^ 2 * (2 * (G.totalMass : ℝ) * F.mprime + 2 * ((Fr.d : ℝ) * F.Sbase)
        - (G.totalMass : ℝ) ^ 2 * F.Ibound + G.nodeEnergy - δ / 2))
      + cB * r * ((((G.geometry r).C.card + (G.geometry r).X'.card : ℕ) : ℝ) - k))
      (fun i => (G.nodeEnum r).nR (s i)) (fun i => (G.nodeEnum r).nQ (s i)) := by
    intro x hxi hz q hq
    choose y hy using hz
    have hdist : ∀ l (t : ℝ), 0 ≤ t → m1 ≤ ‖x l - (t : ℂ)‖ := by
      intro l t ht
      rw [← hy l]; exact poly_dist hS hm0μ (y l) ht
    have hV : |Fr.xstar N0| + r * (P.vRat : ℝ) ≤ a0 * r := by
      have := growth_const_le hC hP hRmin
      rw [ha0]; nlinarith
    have hBN : (N0 : ℝ) + Fr.n0off ≤ a0 * r := by
      rw [ha0]; nlinarith
    have hnorm : ∀ l, ‖x l‖ ≤ a0 * r + 2 * |(x l).im| := by
      intro l
      rw [← hy l]; exact poly_norm hS hAR hBN hV (y l)
    have hcap := lemmaBG_gen hAR F hrpos hN1 x hxi
      (fun l => by rw [← hy l]; exact poly_atom_or_ge F hrpos hH' (y l))
    exact hR0 (r := r) (N := (G.geometry r).C.card + (G.geometry r).X'.card) (nc := (G.geometry r).C.card) hrR0
      (by omega) (G.nodeEnum r) x hxi hdist hnorm s hs hkeep q hq hcap hcommon
  have hLc : chainLen ((Fr.xstar N0 : ℝ) : ℂ) (physL Fr P r) ≤ r * L0 := by
    have e1 : physL Fr P r = P.physPts (Fr.xstar N0) r := (physPts_eq_scaled P Fr r).symm
    rw [e1, RatPolygon.chainLen_physPts P _ hrposR.le]
  have hdetN := theoremN_jet hS Jr hd he0 he1 hLc (Nn := (G.geometry r).C.card + (G.geometry r).X'.card)
    (k := k) hkN (R := (P.r0 : ℝ) * r) (by linarith) hRinj hQinj hRE
  have hfull : (seqFullN f g (fun a : S => ((a.1 : (G.geometry r).C) : ℕ)) (G.geometry r).xs
      (G.geometry r).ys const).det =
      (Matrix.of fun i j : Fin k => Jr.Φ ((G.nodeEnum r).nR (s i)) ((G.nodeEnum r).nQ (s j))).det := by
    have hxm : ∀ i, (G.geometry r).xs i ∈ (G.geometry r).X' := fun i => Finset.orderEmbOfFin_mem _ _ i
    have hym : ∀ j, (G.geometry r).ys j ∈ (G.geometry r).Y' := fun j => Finset.orderEmbOfFin_mem _ _ j
    rw [seqFullN_eq_phi f g Jr.Φ const hΦr _ _ _
      (fun a b h => Subtype.ext (Subtype.ext h))
      (fun a j h => Finset.disjoint_left.mp (G.geometry r).disjCY a.1.2
        (by have := hym j; rwa [← h] at this))
      (fun i b h => Finset.disjoint_left.mp (G.geometry r).disjCX b.1.2
        (by have := hxm i; rwa [h] at this))
      (fun i j h => Finset.disjoint_left.mp (G.geometry r).disjXY (hxm i)
        (by have := hym j; rwa [← h] at this))]
    rw [← Matrix.det_submatrix_equiv_self eq]
    congr 1
    ext p q
    simp only [Matrix.submatrix_apply, Matrix.of_apply, s, Equiv.symm_apply_apply, hrow, hcol]
  rw [hfull]
  refine hdetN.trans (Real.exp_le_exp.2 ?_)
  have hNrows : ((G.geometry r).C.card + (G.geometry r).X'.card : ℕ) = (G.geometry r).rows.card := by
    rw [← G.rows_card_eq_N (G.nodeEnum r)]
  have hNle : (((G.geometry r).C.card + (G.geometry r).X'.card : ℕ) : ℝ) ≤ (G.totalMass : ℝ) * r + G.rowConst := by
    have := (abs_le.1 (G.card_rows_bound r)).2
    rw [hNrows]; linarith
  have habs := jet_N_log_le (Nn := (((G.geometry r).C.card + (G.geometry r).X'.card : ℕ) : ℝ))
    (Mm := (G.totalMass : ℝ)) (rc := G.rowConst) (A := A) (B := c1) (r := r) (cw := cw0) (c1 := c10)
    (c2 := c20) (Nat.cast_nonneg _) hM (Nat.cast_nonneg _) hA0 hc1' hr1 hNle hKcw hKc10 hKc20
  have hR2r := hR2 r hrR2
  have hsub : ((((G.geometry r).C.card - S.card : ℕ)) : ℝ) = ((G.geometry r).C.card : ℝ) - S.card := by
    have : S.card ≤ (G.geometry r).C.card := by simpa using Finset.card_le_univ S
    exact Nat.cast_sub this
  have hNk : ((((G.geometry r).C.card + (G.geometry r).X'.card : ℕ) : ℝ)) - k = ((G.geometry r).C.card : ℝ) - S.card := by
    simp only [hk]; push_cast; rw [show (((G.geometry r).k : ℕ) : ℝ) = (G.geometry r).X'.card by exact_mod_cast hmk]; ring
  have hM0 : Fr.Wabs * ((P.r0 : ℝ) * r) + (Fr.Wabs * ⌈(Fr.xs : ℝ)⌉₊
      + 2 * (amp Cq ^ e * (r * L0 + ‖P.tailDir‖ / ((2 * Real.pi * e) * P.tailDir.im))) + 1)
      = A * r + c1 := by
    rw [hA, hc1, hDd]; ring
  rw [hM0, hcwr, hc1r, hc2r]
  have hmain : (((G.geometry r).C.card + (G.geometry r).X'.card : ℕ) : ℝ) *
      (Real.log (cw0 * (A * r + c1)) + 2 * (c10 + c20 * Real.log ((((G.geometry r).C.card +
        (G.geometry r).X'.card : ℕ) : ℝ) + 1))) ≤ δ / 2 * (r : ℝ) ^ 2 := habs.trans hR2r
  rw [hsub, hNk]
  nlinarith [hmain]


/-- Decay may be weakened in both parameters. -/
theorem SeqAllMinorDecay.mono {f g : ℕ → ℚ} {const : ℝ} {G : NodeFamily} {D D' c c' : ℝ} (hc : 0 ≤ c)
    (hD : D' ≤ D) (hcc : c ≤ c') (h : SeqAllMinorDecay f g const G D c) :
    SeqAllMinorDecay f g const G D' c' := by
  intro δ hδ
  obtain ⟨R0, hR0⟩ := h δ hδ
  refine ⟨R0, fun r hr S => (hR0 r hr S).trans (Real.exp_le_exp.2 ?_)⟩
  have h1 : (0 : ℝ) ≤ (r : ℝ) ^ 2 := by positivity
  have h2 : (0 : ℝ) ≤ (r : ℝ) * (((G r).C.card - S.card : ℕ) : ℝ) :=
    mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  nlinarith

/-- Bounded-selector window for a block geometry from the all-minor estimate (two sequences). -/
theorem BlockGeom.hasScaledDecay_of_seq_allMinor (G : BlockGeom) (f g : ℕ → ℚ) (const : ℝ) (depth : ℕ)
    {D c : ℝ} (hc : 0 ≤ c) (hminor : SeqAllMinorDecay f g const G.geometry D c) :
    HasScaledDecay (seqFamily f g const G.geometry depth) (SeqFamily.scale G.geometry) D c := by
  have hγ : (0 : ℝ) ≤ (G.common.mass : ℝ) := by
    exact_mod_cast G.common_pos.le
  have hcount : ∀ r, (((G.geometry r).C.card : ℕ) : ℝ) ≤ (G.common.mass : ℝ) * r + G.common.n := by
    intro r
    have := (G.card_common r).2
    exact_mod_cast this
  exact scaledDecay_of_seq_all_minors f g const G.geometry depth hc hγ (Nat.cast_nonneg _) hcount hminor

open Finset intervalIntegral MeasureTheory CatalanCore.Uniform.Decay.Spline
  CatalanCore.Uniform.Decay.Tools CatalanCore.Uniform.Decay.Assembly in
open CatalanCore.Uniform.Decay.Cert in
/-- **From the polygon checker to the window contract, for the Löwner family of a datum's sequences.** -/
theorem hasScaledDecay_of_check_jet (G : BlockGeom) {Fr : Frame} (hC : Fr.ContourOK)
    (hAR : ∀ i : Fin Fr.d, ((⌊Fr.xs - Fr.μ i⌋ : ℤ) : ℚ) + Fr.μ i ≤ Fr.n0off)
    (R : PolyCellRules G.nodePot) (D : SplineData) (P : RatPolygon)
    (hchk : D.checkP R P = true) (hMq : D.Mq = G.totalMass)
    (hd : D.dim = Fr.d) (hInu : (D.Inu : ℝ) ≤ G.nodeEnergy)
    (hVc : ∀ s, G.nodePot ((starRingEnd ℂ) s) = G.nodePot s)
    (hUc : ContinuousOn (fun x : ℝ => G.nodePot (x : ℂ)) (Set.Icc (-(P.r0 : ℝ)) 0))
    (hsupp : ∀ r a : ℕ, a ∈ (G.geometry r).C → (a : ℝ) ≤ r)
    {Bd : ℝ} (hBd0 : 0 ≤ Bd) (hBc : ∀ i, ((G.common.block i).v : ℝ) ≤ Bd)
    (hBr : ∀ i, ((G.row.block i).v : ℝ) ≤ Bd) (hBq : ∀ i, ((G.column.block i).v : ℝ) ≤ Bd)
    {m0 : ℝ} (hm0 : 0 < m0) (hm0μ : ∀ i, m0 ≤ Fr.μ i)
    {e : ℝ} (he0 : 0 < e) (heε : e < (D.ε : ℝ)) (depth : ℕ)
    (f g : ℕ → ℚ) (const : ℝ) (cw0 c10 c20 : ℝ)
    (hJall :
      ∃ J : ∀ r : ℕ, Rmin Fr P ≤ (r : ℝ) →
      JetRep Fr (N0Of Fr P.r0 r) (physL Fr P r) P.tailDir (CP Fr (P.qRat : ℝ)),
      (∀ r hr x y, (J r hr).Φ x y = (lw f g x y : ℝ) + (if x = y then const else 0)) ∧
      (∀ r hr, (J r hr).cw = cw0) ∧ (∀ r hr, (J r hr).c1 = c10) ∧ (∀ r hr, (J r hr).c2 = c20)) :
    HasScaledDecay (seqFamily f g const G.geometry depth) (SeqFamily.scale G.geometry)
      (D.Dt : ℝ) (D.ccert : ℝ) := by
  classical
  obtain ⟨B, hP, _, C, hCW, hCm, hCg, hCS, hCI, hCc⟩ := SplineData.checkP_sound hchk
  have hne := B.hne
  have hbd : ∀ i, ∀ t : ℝ, 0 ≤ t → t ≤ 1 → (0 : ℝ) ≤ D.f i t ∧ D.f i t ≤ (D.M i : ℝ) := by
    intro i t h0 h1
    have := ratPoly_bounds (hne i) (B.hbern i) h0 h1
    unfold SplineData.f
    simpa using this
  have hf : ∀ i, Continuous (D.f i) := fun i => continuous_ratPoly (D.l i)
  have hf0 : ∀ i t, 0 ≤ t → t ≤ 1 → 0 ≤ D.f i t := fun i t h0 h1 => (hbd i t h0 h1).1
  have hM : ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) 1, |D.f i t| ≤ ((fun i => (D.M i : ℝ)) i) := by
    intro i t ht
    have := hbd i t ht.1 ht.2
    rw [abs_of_nonneg this.1]; exact this.2
  have hmass : ∑ i, ∫ t in (0 : ℝ)..1, D.f i t = 1 := by
    have := B.hmass
    simp_rw [SplineData.f, integral_ratPoly]
    rw [← Rat.cast_sum]
    have h2 : (∑ i : Fin D.n, ∑ j ∈ range ((D.l i).length - 1 + 1),
        coeffs (D.l i) j / ((j : ℚ) + 1)) = 1 := this
    rw [h2]; norm_num
  have hV : Vp D.f ≤ ((1 : ℚ) : ℝ) := by
    have h1 : Vp D.f = ∑ i, ∫ t in (0 : ℝ)..1, D.f i t := by
      unfold Vp
      refine Finset.sum_congr rfl (fun i _ => ?_)
      refine intervalIntegral.integral_congr (fun t ht => ?_)
      have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by simpa [Set.uIcc_of_le zero_le_one] using ht
      exact abs_of_nonneg (hf0 i t ht'.1 ht'.2)
    rw [h1, hmass]; norm_num
  have hτf : ∀ i, D.f (D.tauF i) = D.f i := by
    intro i; simp [SplineData.f, B.hlτ i]
  have hMq0 : 0 ≤ D.Mq := B.hM.le
  have hρ : (0 : ℝ) < D.rho := B.hρ
  obtain ⟨K, c, wt, F, hg, hFW, hFmp, hFgm, hFcc, hFS, hFI, hVb, hR, hw0⟩ :=
    exists_certCoreGsNuP hP.r0_pos hMq0 hVc B.hε0 B.hε1 C B.hAB hf hM hρ hmass hV
      B.hAR B.hBR B.hτ B.hAτ B.hBτ hτf hUc hf0 B.hloss B.hθ B.hηS
  -- bring to the form of `hasAllMinorDecay_of_certG`
  have hg' : ∀ s : ℂ, F.g s = (G.totalMass : ℝ) * CatalanLambda.Decay.Usig D.rho c wt s -
      G.nodePot s + (1 - (D.ε : ℝ)) * Real.pi * |s.im| := by
    intro s; rw [hg s, hMq]
  have hℓ : ∀ (r a : ℕ), a ∈ (G.geometry r).C → (F.gmin : ℝ) ≤ F.g ((a : ℂ) / (r : ℂ)) := by
    intro r a ha
    have hx0 : (0 : ℝ) ≤ (a : ℝ) / r := by positivity
    have hx1 : (a : ℝ) / r ≤ 1 := by
      rcases Nat.eq_zero_or_pos r with h0 | h0
      · subst h0; simp
      · rw [div_le_one (by exact_mod_cast h0)]; exact hsupp r a ha
    obtain ⟨p, hp, h1, h2⟩ := F.line_cover _ hx0 hx1
    have := F.line_ok p hp _ h1 h2
    have e : ((a : ℂ) / (r : ℂ)) = ⟨(a : ℝ) / r, 0⟩ := by
      have h3 : ((a : ℂ) / (r : ℂ)) = (((a : ℝ) / r : ℝ) : ℂ) := by push_cast; rfl
      rw [h3]; apply Complex.ext <;> simp
    rw [e]; exact this
  have hcB : 2 * ((F.mprime : ℝ) - F.gmin) ≤ (F.ccert : ℝ) := by
    have h1 := F.ccert_ge
    exact h1
  have hall := hasSeqAllMinorDecay_of_certG_poly G hC hAR hP F hw0 hR hg' hBd0 hBc hBr hBq
    hm0 hm0μ he0 heε hℓ hcB f g const cw0 c10 c20 hJall
  have hccR : (F.ccert : ℝ) = D.ccert := by rw [hFcc, hCc]
  have hcc0 : (0 : ℝ) ≤ D.ccert := by exact_mod_cast B.hcc
  -- the decay exponent
  have hmpR : (F.mprime : ℝ) = D.mprime - D.Mq * (D.lossS + D.theta) := by
    rw [hFmp, hCm]; push_cast; ring
  have hSR : (F.Sbase : ℝ) = D.Scap - D.etaS := by rw [hFS, hCS]; push_cast; ring
  have hIR : (F.Ibound : ℝ) = D.Ibound + 1 * D.lossS + 2 * 1 * D.theta := by
    rw [hFI, hCI]; push_cast; ring
  have hDle : (D.Dt : ℝ) ≤ 2 * (G.totalMass : ℝ) * F.mprime + 2 * ((Fr.d : ℝ) * F.Sbase)
      - (G.totalMass : ℝ) ^ 2 * F.Ibound + G.nodeEnergy := by
    have hD := B.hD
    simp only [SplineData.V] at hD
    have hDR : (D.Dt : ℝ) ≤ 2 * ((D.Mq : ℝ) * D.mprime + D.dim * D.Scap) - (D.Mq : ℝ) ^ 2 * D.Ibound
        + D.Inu - (2 * (D.Mq : ℝ) ^ 2 * (D.lossS + D.theta) + 2 * D.dim * D.etaS
          + (D.Mq : ℝ) ^ 2 * (1 * D.lossS + 2 * 1 * D.theta)) := by exact_mod_cast hD
    have hMR : (D.Mq : ℝ) = G.totalMass := by rw [hMq]
    have hdR : (D.dim : ℝ) = Fr.d := by exact_mod_cast hd
    rw [hmpR, hSR, hIR, ← hMR, ← hdR]
    nlinarith [hDR, hInu]
  have hmono := SeqAllMinorDecay.mono (by rw [hccR]; exact hcc0) hDle
    (le_of_eq hccR) hall
  exact BlockGeom.hasScaledDecay_of_seq_allMinor G f g const depth hcc0 hmono


end CatalanCore.Uniform.Decay.Jet

#print axioms CatalanCore.Uniform.Decay.Jet.integrand_le_jet
#print axioms CatalanCore.Uniform.Decay.Jet.theoremN_jet
#print axioms CatalanCore.Uniform.Decay.Jet.seqFullN_eq_phi
#print axioms CatalanCore.Uniform.Decay.Jet.jet_N_log_le
#print axioms CatalanCore.Uniform.Decay.Jet.hasSeqAllMinorDecay_of_certG_poly
#print axioms CatalanCore.Uniform.Decay.Jet.hasScaledDecay_of_check_jet
