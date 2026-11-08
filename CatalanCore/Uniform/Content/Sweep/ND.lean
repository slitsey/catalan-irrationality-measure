module

public import CatalanCore.Uniform.NV.StepWronskian
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

@[expose] public section

/-!
# Theorem ND: the class matrix `B̄_X` is nonsingular (lane H, wave H2b; ledger N10)

`PLANE2-ROW-SIMPLIFICATION-2026-11-07` §1.  Let `p` be prime, `κ, k' ≥ 0` with `p > κ + 2k'`, and
`s : ℕ → 𝔽_p` with `(t+1)² (s(t+1) - s(t)) = c ≠ 0` on the `2k'` nodes `κ, …, κ+2k'-1` (for the sweep,
`s(j) = -Σ_{i ≤ j} i⁻²` and `c = -1`).  `B̄_X` has rows `[0,κ) ∪ J_X`, columns `[0,κ) ∪ J_Y`
(`J_X = {κ, κ+2, …}`, `J_Y = {κ+1, κ+3, …}`), `X` on the diagonal of the `[0,κ)` block and the divided
differences `(s(j) - s(l))/(j - l)` elsewhere.  Then `det B̄_X ≠ 0` in `𝔽_p[X]`, for every `g` and every
`s` below `κ`.

The proof is the characteristic-`p` copy of `NV.no_step_antidifference` (the pole `-1` of `(X+1)²` is
isolated in its orbit, which has `p` points): a kernel vector of the cross block `D(κ,k')` gives a pair
`(u, w)` of degree `≤ k'-1` with `w = s·u` on the `2k'` nodes; the step defect has `2k'-1` roots and
degree `≤ 2k'-2`, so vanishes; after the gcd reduction the closure under `x ↦ x ± 1` forces `p` roots on
`u`.  Then `X` occurs only on the diagonal of the `[0,κ)` block, and one Schur complement of the cross
block leaves a characteristic polynomial.  No table, no closed form.
-/
open Polynomial Finset Matrix

namespace CatalanCore.Uniform.Content.Sweep.ND

open CatalanCore.Uniform.NV

variable {p : ℕ} [Fact p.Prime]

/-- The step defect of the cleared increment `c (x+1)⁻²`: `(X+1)² (w(X+1) u - w u(X+1)) - c u u(X+1)`. -/
noncomputable abbrev defect (c : ZMod p) (w u : (ZMod p)[X]) : (ZMod p)[X] :=
  stepDefect 1 ((X + 1) ^ 2) (C c) w u

theorem defect_eval (c : ZMod p) (w u : (ZMod p)[X]) (x : ZMod p) :
    (defect c w u).eval x =
      (x + 1) ^ 2 * (w.eval (x + 1) * u.eval x - w.eval x * u.eval (x + 1)) -
        c * u.eval x * u.eval (x + 1) := by
  simp [defect, stepDefect, stepWronskian, eval_shiftBy]

theorem coprime_eval_ne {K : Type*} [Field K] {a b : K[X]} (h : IsCoprime a b)
    {x : K} (hb : b.eval x = 0) : a.eval x ≠ 0 := by
  obtain ⟨s, t, hst⟩ := h
  intro ha
  have he := congrArg (fun P : K[X] => P.eval x) hst
  simp [ha, hb] at he

/-- Coprime pair with vanishing defect: `u` vanishes identically (a nonzero polynomial of degree
`< p` with `p` roots), in characteristic `p`. -/
theorem coprime_defect_zero {c : ZMod p} (hc : c ≠ 0) {w u : (ZMod p)[X]}
    (hcp : IsCoprime w u) (hu : u ≠ 0) (hdeg : u.natDegree < p)
    (h0 : defect c w u = 0) : False := by
  have he (x : ZMod p) : (x + 1) ^ 2 * (w.eval (x + 1) * u.eval x - w.eval x * u.eval (x + 1)) =
      c * u.eval x * u.eval (x + 1) := by
    have := congrArg (fun P : (ZMod p)[X] => P.eval x) h0
    simp only [defect_eval, eval_zero] at this
    linear_combination this
  have hwz (x : ZMod p) (hx : u.eval x = 0) : w.eval x ≠ 0 := coprime_eval_ne hcp hx
  have hup : ∀ x : ZMod p, x ≠ -1 → u.eval x = 0 → u.eval (x + 1) = 0 := by
    intro x hx hux
    have hx1 : (x + 1) ^ 2 ≠ 0 := pow_ne_zero 2 (fun h => hx (by linear_combination h))
    have := he x
    rw [hux] at this
    have h2 : (x + 1) ^ 2 * (-(w.eval x * u.eval (x + 1))) = 0 := by
      linear_combination this
    have h3 := (mul_eq_zero.mp h2).resolve_left hx1
    exact (mul_eq_zero.mp (neg_eq_zero.mp h3)).resolve_left (hwz x hux)
  have hdown : ∀ x : ZMod p, x ≠ -1 → u.eval (x + 1) = 0 → u.eval x = 0 := by
    intro x hx hux
    have hx1 : (x + 1) ^ 2 ≠ 0 := pow_ne_zero 2 (fun h => hx (by linear_combination h))
    have := he x
    rw [hux] at this
    have h2 : (x + 1) ^ 2 * (w.eval (x + 1) * u.eval x) = 0 := by
      linear_combination this
    have h3 := (mul_eq_zero.mp h2).resolve_left hx1
    exact (mul_eq_zero.mp h3).resolve_left (hwz (x + 1) hux)
  have hstart : u.eval (-1) = 0 ∨ u.eval 0 = 0 := by
    have h1 := he (-1)
    have hz : (-1 + 1 : ZMod p) = 0 := by ring
    simp only [hz] at h1
    have h2 : c * u.eval (-1) * u.eval 0 = 0 := by linear_combination -h1
    rcases mul_eq_zero.mp h2 with h | h
    · exact Or.inl ((mul_eq_zero.mp h).resolve_left hc)
    · exact Or.inr h
  have hne (n : ℕ) (hn : n + 1 < p) : ((n : ZMod p) + 1) ≠ 0 := by
    intro h
    have h' : ((n + 1 : ℕ) : ZMod p) = 0 := by push_cast; exact h
    rw [ZMod.natCast_eq_zero_iff] at h'
    exact absurd (Nat.le_of_dvd (Nat.succ_pos n) h') (by omega)
  have hallroots : ∀ x : ZMod p, u.eval x = 0 := by
    rcases hstart with hm | h0
    · have hb : ∀ n : ℕ, n < p → u.eval (-1 - (n : ZMod p)) = 0 := by
        intro n
        induction n with
        | zero => intro _; simpa using hm
        | succ n ih =>
          intro hn
          have h1 := ih (by omega)
          have hne' : (-1 - ((n + 1 : ℕ) : ZMod p)) ≠ -1 := by
            intro h
            apply hne n hn
            push_cast at h
            linear_combination -h
          apply hdown _ hne'
          have : (-1 - ((n + 1 : ℕ) : ZMod p)) + 1 = -1 - (n : ZMod p) := by push_cast; ring
          rw [this]; exact h1
      intro x
      have := hb (-1 - x).val (ZMod.val_lt _)
      rw [ZMod.natCast_zmod_val] at this
      have e : (-1 - (-1 - x) : ZMod p) = x := by ring
      rwa [e] at this
    · have hf : ∀ n : ℕ, n < p → u.eval (n : ZMod p) = 0 := by
        intro n
        induction n with
        | zero => intro _; simpa using h0
        | succ n ih =>
          intro hn
          have h1 := ih (by omega)
          have hne' : (n : ZMod p) ≠ -1 := by
            intro h
            apply hne n hn
            linear_combination h
          have := hup _ hne' h1
          simpa using this
      intro x
      have := hf x.val (ZMod.val_lt _)
      rwa [ZMod.natCast_zmod_val] at this
  apply hu
  exact Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' u Finset.univ (fun x _ => hallroots x)
    (by simpa using hdeg)


/-- No polynomial pair has vanishing defect (the gcd reduction of `coprime_defect_zero`). -/
theorem defect_ne_zero {c : ZMod p} (hc : c ≠ 0) (w u : (ZMod p)[X]) (hu : u ≠ 0)
    (hdeg : u.natDegree < p) : defect c w u ≠ 0 := by
  classical
  intro heq
  let g := GCDMonoid.gcd w u
  have hg : g ≠ 0 := gcd_ne_zero_of_right hu
  let w0 := w / g
  let u0 := u / g
  have hw : g * w0 = w := EuclideanDomain.mul_div_cancel' hg (gcd_dvd_left _ _)
  have hu' : g * u0 = u := EuclideanDomain.mul_div_cancel' hg (gcd_dvd_right _ _)
  have hcp : IsCoprime w0 u0 := isCoprime_div_gcd_div_gcd hu
  have hu0 : u0 ≠ 0 := right_div_gcd_ne_zero hu
  have hsg : shiftBy 1 g ≠ 0 := by
    intro hz
    have hback := congrArg (fun P : (ZMod p)[X] => P.comp (X - C 1)) hz
    have hid : (shiftBy 1 g).comp (X - C 1) = g := by
      simp only [shiftBy, comp_assoc, add_comp, X_comp, C_comp]
      convert g.comp_X using 1
      congr 1
      ring
    rw [hid, zero_comp] at hback
    exact hg hback
  apply coprime_defect_zero hc hcp hu0
  · calc u0.natDegree ≤ (g * u0).natDegree := by
          rw [natDegree_mul hg hu0]; omega
      _ = u.natDegree := by rw [hu']
      _ < p := hdeg
  · apply mul_left_cancel₀ (mul_ne_zero hg hsg)
    calc (g * shiftBy 1 g) * defect c w0 u0 = defect c w u := by
          rw [← hw, ← hu']
          simp only [defect, stepDefect, stepWronskian, shiftBy, mul_comp]
          ring
      _ = 0 := heq
      _ = (g * shiftBy 1 g) * 0 := by ring


/-! ### The kernel of the `κ`-shifted Löwner block -/

section Kernel

variable (κ k' : ℕ) (s : ℕ → ZMod p)

/-- The cross block `(s(y_j) - s(x_l))/(y_j - x_l)` for `x_l = κ+2l`, `y_j = κ+2j+1`. -/
noncomputable def crossBlock : Matrix (Fin k') (Fin k') (ZMod p) :=
  Matrix.of fun l j => (s (κ + 2 * j + 1) - s (κ + 2 * l)) /
    (((κ + 2 * j + 1 : ℕ) : ZMod p) - ((κ + 2 * l : ℕ) : ZMod p))

theorem cast_inj_of_lt {a b : ℕ} (ha : a < p) (hb : b < p) (h : (a : ZMod p) = (b : ZMod p)) : a = b := by
  have := (ZMod.natCast_eq_natCast_iff' a b p).mp h
  rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this

theorem crossBlock_det_ne_zero (hk : 1 ≤ k') (hp : κ + 2 * k' < p) {c : ZMod p} (hc : c ≠ 0)
    (hstep : ∀ i, i + 1 < 2 * k' →
      ((κ + i + 1 : ℕ) : ZMod p) ^ 2 * (s (κ + i + 1) - s (κ + i)) = c) :
    (crossBlock κ k' s).det ≠ 0 := by
  classical
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  set y : Fin k' → ZMod p := fun j => ((κ + 2 * j + 1 : ℕ) : ZMod p) with hy
  set x : Fin k' → ZMod p := fun l => ((κ + 2 * l : ℕ) : ZMod p) with hx
  have hyinj : Function.Injective y := by
    intro a b h
    have := cast_inj_of_lt (by have := a.2; omega) (by have := b.2; omega) h
    exact Fin.ext (by omega)
  have hxy (l j : Fin k') : x l - y j ≠ 0 := by
    intro h
    have := cast_inj_of_lt (by have := l.2; omega) (by have := j.2; omega) (sub_eq_zero.mp h)
    omega
  let P : Fin k' → (ZMod p)[X] := fun j => ∏ i ∈ univ.erase j, (X - C (y i))
  let u : (ZMod p)[X] := ∑ j, C (v j) * P j
  let w : (ZMod p)[X] := ∑ j, C (v j * s (κ + 2 * j + 1)) * P j
  have hPdeg (j : Fin k') : (P j).natDegree ≤ k' - 1 := by
    refine (natDegree_prod_le _ _).trans ?_
    calc ∑ i ∈ univ.erase j, (X - C (y i)).natDegree ≤ ∑ i ∈ univ.erase j, 1 :=
          Finset.sum_le_sum (f := fun i : Fin k' => (X - C (y i)).natDegree) (g := fun _ => 1) (fun i _ => by simp [natDegree_X_sub_C])
      _ = k' - 1 := by simp [card_erase_of_mem]
  have hudeg : u.natDegree ≤ k' - 1 :=
    natDegree_sum_le_of_forall_le _ _ (fun j _ => (natDegree_C_mul_le _ _).trans (hPdeg j))
  have hwdeg : w.natDegree ≤ k' - 1 :=
    natDegree_sum_le_of_forall_le _ _ (fun j _ => (natDegree_C_mul_le _ _).trans (hPdeg j))
  have hPy (i j : Fin k') (hij : i ≠ j) : (P i).eval (y j) = 0 := by
    simp only [P, eval_prod, eval_sub, eval_X, eval_C]
    exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨Ne.symm hij, mem_univ _⟩) (sub_self _)
  have hPyj (j : Fin k') : (P j).eval (y j) ≠ 0 := by
    simp only [P, eval_prod, eval_sub, eval_X, eval_C]
    exact Finset.prod_ne_zero_iff.mpr (fun i hi =>
      sub_ne_zero.mpr (fun h => (Finset.mem_erase.mp hi).1 (hyinj h).symm))
  have huy (j : Fin k') : u.eval (y j) = v j * (P j).eval (y j) := by
    simp only [u, eval_finsetSum, eval_mul, eval_C]
    rw [Finset.sum_eq_single j]
    · intro i _ hij; rw [hPy i j hij, mul_zero]
    · intro h; exact absurd (mem_univ _) h
  have hwy (j : Fin k') : w.eval (y j) = v j * s (κ + 2 * j + 1) * (P j).eval (y j) := by
    simp only [w, eval_finsetSum, eval_mul, eval_C]
    rw [Finset.sum_eq_single j]
    · intro i _ hij; rw [hPy i j hij, mul_zero]
    · intro h; exact absurd (mem_univ _) h
  have hu0 : u ≠ 0 := by
    obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hv0 (funext hcon)
    intro hz
    have := huy j
    rw [hz, eval_zero] at this
    exact mul_ne_zero hj (hPyj j) this.symm
  have hnodeY (j : Fin k') : w.eval (y j) = s (κ + 2 * j + 1) * u.eval (y j) := by
    rw [hwy, huy]; ring
  have hnodeX (l : Fin k') : w.eval (x l) = s (κ + 2 * l) * u.eval (x l) := by
    have hPl : ∏ i, (x l - y i) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hxy l i)
    have hPe (j : Fin k') : (P j).eval (x l) * (x l - y j) = ∏ i, (x l - y i) := by
      simp only [P, eval_prod, eval_sub, eval_X, eval_C]
      rw [mul_comm]
      exact Finset.mul_prod_erase univ (fun i => x l - y i) (mem_univ j)
    have hrow := congrFun hv l
    simp only [crossBlock, Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply] at hrow
    have hq (j : Fin k') : (P j).eval (x l) = (∏ i, (x l - y i)) / (x l - y j) := by
      rw [eq_div_iff (hxy l j)]; exact hPe j
    have key : w.eval (x l) - s (κ + 2 * l) * u.eval (x l) =
        -(∏ i, (x l - y i)) * ∑ j : Fin k', (s (κ + 2 * j + 1) - s (κ + 2 * l)) /
          (y j - x l) * v j := by
      simp only [u, w, eval_finsetSum, eval_mul, eval_C]
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [hq j]
      have h1 : x l - y j ≠ 0 := hxy l j
      have h2 : y j - x l ≠ 0 := fun h => h1 (by linear_combination -h)
      field_simp
      ring
    have hy' : ∑ j : Fin k', (s (κ + 2 * j + 1) - s (κ + 2 * l)) / (y j - x l) * v j = 0 := by
      convert hrow using 2
    rw [hy', mul_zero] at key
    linear_combination key
  have hnode (i : ℕ) (hi : i < 2 * k') : w.eval ((κ + i : ℕ) : ZMod p) =
      s (κ + i) * u.eval ((κ + i : ℕ) : ZMod p) := by
    rcases Nat.even_or_odd' i with ⟨a, rfl | rfl⟩
    · have ha : a < k' := by omega
      exact hnodeX ⟨a, ha⟩
    · have ha : a < k' := by omega
      have := hnodeY ⟨a, ha⟩
      simp only [hy] at this
      have e : κ + (2 * a + 1) = κ + 2 * a + 1 := by omega
      rw [e]; exact this
  -- the defect vanishes on the `2k' - 1` edges
  have hE : defect c w u = 0 := by
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero (defect c w u)
      (ι := Fin (2 * k' - 1)) (f := fun i => ((κ + i : ℕ) : ZMod p))
    · intro a b hab
      have := cast_inj_of_lt (by have := a.2; omega) (by have := b.2; omega) hab
      exact Fin.ext (by omega)
    · intro i
      have hi := i.2
      have h0 := hnode i (by omega)
      have h1 := hnode (i + 1) (by omega)
      apply stepDefect_eval_zero 1 ((X + 1) ^ 2) (C c) w u _ (s (κ + i)) (s (κ + (i + 1))) h0
      · have e : ((κ + i : ℕ) : ZMod p) + 1 = ((κ + (i + 1) : ℕ) : ZMod p) := by push_cast; ring
        rw [e]; exact h1
      · have e : ((κ + i : ℕ) : ZMod p) + 1 = ((κ + i + 1 : ℕ) : ZMod p) := by push_cast; ring
        simp only [eval_pow, eval_add, eval_X, eval_one, eval_C]
        rw [e]
        have := hstep i (by omega)
        have e2 : κ + (i + 1) = κ + i + 1 := by omega
        rw [e2]; exact this
    · refine lt_of_le_of_lt (natDegree_stepDefect_le 1 ((X + 1) ^ 2) (C c) w u 2 (k' - 1)
        le_rfl ?_ ?_ hwdeg hudeg) ?_
      · simp [natDegree_pow]
      · simp
      · simp only [Fintype.card_fin]; omega
  exact defect_ne_zero hc w u hu0 (by omega) hE

end Kernel


/-! ### The class matrix `B̄_X` over `𝔽_p[X]` -/

section ClassMatrix

variable (κ k' : ℕ) (s g : ℕ → ZMod p)

/-- Constants of the class matrix: the `[0,κ)` block (diagonal `g`), the borders, and the cross block. -/
noncomputable def blockA : Matrix (Fin κ) (Fin κ) (ZMod p) :=
  Matrix.of fun a b => if a = b then g a else
    (s b - s a) / (((b : ℕ) : ZMod p) - ((a : ℕ) : ZMod p))

noncomputable def blockB : Matrix (Fin κ) (Fin k') (ZMod p) :=
  Matrix.of fun a j => (s (κ + 2 * j + 1) - s a) / (((κ + 2 * j + 1 : ℕ) : ZMod p) - ((a : ℕ) : ZMod p))

noncomputable def blockC : Matrix (Fin k') (Fin κ) (ZMod p) :=
  Matrix.of fun l b => (s b - s (κ + 2 * l)) / (((b : ℕ) : ZMod p) - ((κ + 2 * l : ℕ) : ZMod p))

/-- `B̄_X`: rows `[0,κ) ∪ J_X`, columns `[0,κ) ∪ J_Y`, `X` on the diagonal of the `[0,κ)` block. -/
noncomputable def Bbar : Matrix (Fin κ ⊕ Fin k') (Fin κ ⊕ Fin k') (ZMod p)[X] :=
  Matrix.fromBlocks ((X : (ZMod p)[X]) • (1 : Matrix (Fin κ) (Fin κ) (ZMod p)[X]) +
      (blockA κ s g).map C) ((blockB κ k' s).map C) ((blockC κ k' s).map C)
    ((crossBlock κ k' s).map C)

theorem det_X_add_map {ι : Type*} [Fintype ι] [DecidableEq ι] (N : Matrix ι ι (ZMod p)) :
    ((X : (ZMod p)[X]) • (1 : Matrix ι ι (ZMod p)[X]) + N.map C).det ≠ 0 := by
  have h : (X : (ZMod p)[X]) • (1 : Matrix ι ι (ZMod p)[X]) + N.map C = (-N).charmatrix := by
    ext a b
    by_cases hab : a = b <;> simp [Matrix.charmatrix_apply, hab, Matrix.one_apply]
  rw [h]
  exact (Matrix.charpoly_monic (-N)).ne_zero

/-- **Theorem ND.**  For `p > κ + 2k'` and `s` with `(t+1)² (s(t+1) - s(t)) = c ≠ 0` on the `2k'`
nodes `κ, …, κ+2k'-1`, `det B̄_X ≠ 0` in `𝔽_p[X]`, for every `g` and every `s` below `κ`. -/
theorem det_Bbar_ne_zero (hp : κ + 2 * k' < p) {c : ZMod p} (hc : c ≠ 0)
    (hstep : ∀ i, i + 1 < 2 * k' →
      ((κ + i + 1 : ℕ) : ZMod p) ^ 2 * (s (κ + i + 1) - s (κ + i)) = c) :
    (Bbar κ k' s g).det ≠ 0 := by
  have hD : IsUnit (crossBlock κ k' s).det := by
    rcases Nat.eq_zero_or_pos k' with h0 | h0
    · subst h0; simp
    · exact (crossBlock_det_ne_zero κ k' s h0 hp hc hstep).isUnit
  set D0 := crossBlock κ k' s with hD0
  set φ : Matrix (Fin k') (Fin k') (ZMod p) →+* Matrix (Fin k') (Fin k') (ZMod p)[X] :=
    (C : ZMod p →+* (ZMod p)[X]).mapMatrix with hφ
  have hD' : IsUnit (D0.map (C : ZMod p →+* (ZMod p)[X])).det := by
    have : (D0.map (C : ZMod p →+* (ZMod p)[X])).det = C D0.det := by
      simpa using (RingHom.map_det (C : ZMod p →+* (ZMod p)[X]) D0).symm
    rw [this]; exact hD.map _
  letI : Invertible (D0.map (C : ZMod p →+* (ZMod p)[X])) :=
    Matrix.invertibleOfIsUnitDet _ hD'
  unfold Bbar
  rw [Matrix.det_fromBlocks₂₂]
  refine mul_ne_zero hD'.ne_zero ?_
  have hinv : ⅟(D0.map (C : ZMod p →+* (ZMod p)[X])) = (D0⁻¹).map C := by
    apply invOf_eq_right_inv
    have h1 : D0 * D0⁻¹ = 1 := Matrix.mul_nonsing_inv _ hD
    have := congrArg ((C : ZMod p →+* (ZMod p)[X]).mapMatrix) h1
    simpa using this
  rw [hinv]
  have hS : (X : (ZMod p)[X]) • (1 : Matrix (Fin κ) (Fin κ) (ZMod p)[X]) + (blockA κ s g).map C -
      (blockB κ k' s).map C * (D0⁻¹).map C * (blockC κ k' s).map C =
      (X : (ZMod p)[X]) • (1 : Matrix (Fin κ) (Fin κ) (ZMod p)[X]) +
        (blockA κ s g - blockB κ k' s * D0⁻¹ * blockC κ k' s).map C := by
    have := map_sub (C : ZMod p →+* (ZMod p)[X]).mapMatrix (blockA κ s g)
      (blockB κ k' s * D0⁻¹ * blockC κ k' s)
    simp only [RingHom.mapMatrix_apply] at this
    rw [Matrix.map_mul, Matrix.map_mul] at this
    rw [this]; abel
  rw [hS]
  exact det_X_add_map _



/-- `det B̄_X ≠ 0` in the fraction field `𝔽_p(ξ)` of any transcendental `ξ` (e.g. in the residue field
of `ℤ_(p)[X]_(p)` at `X`). -/
theorem det_Bbar_map_ne_zero {F : Type*} [Field F] [Algebra (ZMod p) F] (ξ : F)
    (hξ : Transcendental (ZMod p) ξ) (hp : κ + 2 * k' < p) {c : ZMod p} (hc : c ≠ 0)
    (hstep : ∀ i, i + 1 < 2 * k' →
      ((κ + i + 1 : ℕ) : ZMod p) ^ 2 * (s (κ + i + 1) - s (κ + i)) = c) :
    ((Bbar κ k' s g).map (Polynomial.aeval ξ : (ZMod p)[X] →ₐ[ZMod p] F)).det ≠ 0 := by
  have hinj : Function.Injective (Polynomial.aeval ξ : (ZMod p)[X] →ₐ[ZMod p] F) :=
    (transcendental_iff_injective.mp hξ)
  have := (RingHom.map_det (Polynomial.aeval ξ : (ZMod p)[X] →ₐ[ZMod p] F).toRingHom (Bbar κ k' s g))
  intro h0
  apply det_Bbar_ne_zero κ k' s g hp hc hstep
  apply hinj
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, RingHom.mapMatrix_apply] at this
  rw [map_zero, this]
  exact h0

end ClassMatrix

end CatalanCore.Uniform.Content.Sweep.ND

#print axioms CatalanCore.Uniform.Content.Sweep.ND.crossBlock_det_ne_zero
#print axioms CatalanCore.Uniform.Content.Sweep.ND.det_Bbar_ne_zero
#print axioms CatalanCore.Uniform.Content.Sweep.ND.det_Bbar_map_ne_zero
