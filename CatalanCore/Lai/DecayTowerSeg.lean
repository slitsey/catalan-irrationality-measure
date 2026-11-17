module

public import CatalanCore.Decay.ComplexTaylor
public import CatalanCore.Uniform.Decay.NearCells.CQ
public import CatalanMeasure.GenD.Signed.LogEval

@[expose] public section

/-!
# Segment towers at a rational point (Lai decay, rows R1, R2, R5-R8, R10 of DECAY-CELLS-SIMPLE)

Generic in the segment `{M + h x : |x| ≤ 1}`, the Chebyshev density `f = Σ_{k ≤ N} c_k T_k ≥ 0`
and any real curve `γ`.  The segment tower `potT` (the potential `U^ν ∘ γ` and the derivatives
`Re fdb (segD k ∘ γ) (γ^{(i)}) j`, `j ≤ 4`) is enclosed by exact Gaussian-rational arithmetic at the
point `s̃ = M + h J(φ̃)` for a rational `φ̃` (`|φ̃| > 1`), with no root and no ball arithmetic.

* **R1** Gaussian rationals: `CatalanCore.Uniform.Decay.NearCells.CQ` (built, imported).
* **R2** `fdb_sub`, `norm_fdb_sub_le` (the majorant of a difference of Faà di Bruno values).
* **R5** `hasDerivAt_jq_inv`, `hasDerivAt_segFC`: `d(q⁻¹)/dζ = -ζ q⁻³`, `dF_j/dζ = -q⁻¹ F_{j+1}`.
* **R6** `step_closed`, `segSt_closed`: `h^m S_m` for `m = 1..4` as closed forms in `ζ, q⁻¹, F_j`.
* **R7** `segD_pert`: `‖D_k(s) - D_k(s̃)‖ ≤ ‖s - s̃‖ k! c₀/d^{k+1}`.
* **R8** `logPotC_pert`: `|U(s) - U(s̃)| ≤ ‖s - s̃‖ c₀/d`.
* **R10** `SegQ`, `fdbQ`, `SegQ.Tq`, `SegQ.Te`, `segTower_encQ`: the rational enclosure of `potT`.
-/

open Set Finset MeasureTheory Filter Topology
open CatalanCore.Zeta5.Potential CatalanCore.Zeta5.Cells CatalanCore.Tools.Joukowski
  CatalanCore.Decay.ComplexTaylor CatalanCore.Uniform.Decay.NearCells
  CatalanMeasure.GenD.Signed.LogEval

namespace CatalanCore.Lai.DecayTowerSeg

/-- R2a: `fdb` is additive in `D`. -/
theorem fdb_sub (D D' Y : ℕ → ℂ) (j : ℕ) :
    fdb D Y j - fdb D' Y j = fdb (fun k => D k - D' k) Y j := by
  rcases j with _ | _ | _ | _ | _ | _ | j <;> simp [fdb] <;> ring

private theorem nb_mul {a b : ℂ} {A B : ℝ} (ha : ‖a‖ ≤ A) (hb : ‖b‖ ≤ B) : ‖a * b‖ ≤ A * B := by
  rw [norm_mul]; exact mul_le_mul ha hb (norm_nonneg _) ((norm_nonneg _).trans ha)

private theorem nb_pow {a : ℂ} {A : ℝ} (ha : ‖a‖ ≤ A) (n : ℕ) : ‖a ^ n‖ ≤ A ^ n := by
  rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) ha n

private theorem nb_add {a b : ℂ} {A B : ℝ} (ha : ‖a‖ ≤ A) (hb : ‖b‖ ≤ B) : ‖a + b‖ ≤ A + B :=
  (norm_add_le _ _).trans (add_le_add ha hb)

private theorem nb_lit (n : ℕ) [n.AtLeastTwo] : ‖(OfNat.ofNat n : ℂ)‖ ≤ (OfNat.ofNat n : ℝ) := by
  simp

/-- R2 (Lemma 5): the majorant of a difference of two Faà di Bruno values. -/
theorem norm_fdb_sub_le (D D' Y : ℕ → ℂ) (η Ym : ℕ → ℝ) {j : ℕ} (hj1 : 1 ≤ j) (hj : j ≤ 5)
    (hD : ∀ k, 1 ≤ k → k ≤ j → ‖D k - D' k‖ ≤ η k)
    (hY : ∀ i, 1 ≤ i → i ≤ j → ‖Y i‖ ≤ Ym i) :
    ‖fdb D Y j - fdb D' Y j‖ ≤ fdb η Ym j := by
  rw [fdb_sub]
  set E : ℕ → ℂ := fun k => D k - D' k with hE
  have e : ∀ k, 1 ≤ k → k ≤ j → ‖E k‖ ≤ η k := hD
  interval_cases j
  · have e1 := e 1 (by norm_num) (by norm_num)
    have y1 := hY 1 (by norm_num) (by norm_num)
    simpa [fdb] using nb_mul e1 y1
  · have e1 := e 1 (by norm_num) (by norm_num)
    have e2 := e 2 (by norm_num) (by norm_num)
    have y1 := hY 1 (by norm_num) (by norm_num)
    have y2 := hY 2 (by norm_num) (by norm_num)
    simpa [fdb] using nb_add (nb_mul e2 (nb_pow y1 2)) (nb_mul e1 y2)
  · have e1 := e 1 (by norm_num) (by norm_num)
    have e2 := e 2 (by norm_num) (by norm_num)
    have e3 := e 3 (by norm_num) (by norm_num)
    have y1 := hY 1 (by norm_num) (by norm_num)
    have y2 := hY 2 (by norm_num) (by norm_num)
    have y3 := hY 3 (by norm_num) (by norm_num)
    simpa [fdb] using nb_add (nb_add (nb_mul e3 (nb_pow y1 3))
      (nb_mul (nb_mul (nb_mul (nb_lit 3) e2) y1) y2)) (nb_mul e1 y3)
  · have e1 := e 1 (by norm_num) (by norm_num)
    have e2 := e 2 (by norm_num) (by norm_num)
    have e3 := e 3 (by norm_num) (by norm_num)
    have e4 := e 4 (by norm_num) (by norm_num)
    have y1 := hY 1 (by norm_num) (by norm_num)
    have y2 := hY 2 (by norm_num) (by norm_num)
    have y3 := hY 3 (by norm_num) (by norm_num)
    have y4 := hY 4 (by norm_num) (by norm_num)
    simpa [fdb] using nb_add (nb_add (nb_add (nb_mul e4 (nb_pow y1 4))
      (nb_mul (nb_mul (nb_mul (nb_lit 6) e3) (nb_pow y1 2)) y2))
      (nb_mul e2 (nb_add (nb_mul (nb_lit 3) (nb_pow y2 2))
        (nb_mul (nb_mul (nb_lit 4) y1) y3)))) (nb_mul e1 y4)
  · have e1 := e 1 (by norm_num) (by norm_num)
    have e2 := e 2 (by norm_num) (by norm_num)
    have e3 := e 3 (by norm_num) (by norm_num)
    have e4 := e 4 (by norm_num) (by norm_num)
    have e5 := e 5 (by norm_num) (by norm_num)
    have y1 := hY 1 (by norm_num) (by norm_num)
    have y2 := hY 2 (by norm_num) (by norm_num)
    have y3 := hY 3 (by norm_num) (by norm_num)
    have y4 := hY 4 (by norm_num) (by norm_num)
    have y5 := hY 5 (by norm_num) (by norm_num)
    simpa [fdb] using nb_add (nb_add (nb_add (nb_add (nb_mul e5 (nb_pow y1 5))
      (nb_mul (nb_mul (nb_mul (nb_lit 10) e4) (nb_pow y1 3)) y2))
      (nb_mul e3 (nb_add (nb_mul (nb_mul (nb_lit 15) y1) (nb_pow y2 2))
        (nb_mul (nb_mul (nb_lit 10) (nb_pow y1 2)) y3))))
      (nb_mul e2 (nb_add (nb_mul (nb_mul (nb_lit 10) y2) y3) (nb_mul (nb_mul (nb_lit 5) y1) y4))))
      (nb_mul e1 y5)

/-- `F_j(ψ) = Σ_{k ≤ N} k^j c_k ψ^k` (`0^0 = 1`). -/
def segFC (c : ℕ → ℝ) (N : ℕ) (ψ : ℂ) (j : ℕ) : ℂ :=
  ∑ k ∈ Finset.range (N + 1), ((k : ℂ) ^ j * (c k : ℂ)) * ψ ^ k

/-- R5 (Lemma 1): `d(q⁻¹)/dζ = -ζ q⁻³`. -/
theorem hasDerivAt_jq_inv {ζ : ℂ} (h : 1 < jc ζ) :
    HasDerivAt (fun z => (jq z)⁻¹) (-(ζ * (jq ζ)⁻¹ ^ 3)) ζ := by
  have hq := jq_ne_zero h
  refine ((hasDerivAt_jq h).inv hq).congr_deriv ?_
  field_simp

/-- R5 (Lemma 1): `dF_j/dζ = -q⁻¹ F_{j+1}`. -/
theorem hasDerivAt_segFC {ζ : ℂ} (h : 1 < jc ζ) (c : ℕ → ℝ) (N j : ℕ) :
    HasDerivAt (fun z => segFC c N (jphi z)⁻¹ j)
      (-((jq ζ)⁻¹ * segFC c N (jphi ζ)⁻¹ (j + 1))) ζ := by
  have hq := jq_ne_zero h
  unfold segFC
  have key : HasDerivAt (fun z => ∑ k ∈ Finset.range (N + 1),
      ((k : ℂ) ^ j * (c k : ℂ)) * (jphi z)⁻¹ ^ k)
      (∑ k ∈ Finset.range (N + 1),
        ((k : ℂ) ^ j * (c k : ℂ)) * (-(k : ℂ) * (jphi ζ ^ k)⁻¹ / jq ζ)) ζ := by
    refine HasDerivAt.fun_sum fun k _ => ?_
    have := (hasDerivAt_jphi_inv_pow h k).const_mul ((k : ℂ) ^ j * (c k : ℂ))
    simpa only [inv_pow] using this
  refine key.congr_deriv ?_
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [inv_pow]
  field_simp
  ring

/-- the step of Lemma 2: `G_{m+1} = -(1/m) ∂_ζ G_m`. -/
theorem step_closed {M h : ℂ} (hh : h ≠ 0) {c : ℕ → ℝ} {N : ℕ}
    (hpos : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ chebF c N x) {m : ℕ} (hm : 1 ≤ m)
    (G Gn : ℂ → ℂ)
    (hG : ∀ s, 1 < jc ((s - M) / h) → h ^ m * segSt M h c N m s = G ((s - M) / h))
    (hd : ∀ ζ, 1 < jc ζ → ∃ g', HasDerivAt G g' ζ ∧ -(1 / (m : ℂ)) * g' = Gn ζ) :
    ∀ s, 1 < jc ((s - M) / h) → h ^ (m + 1) * segSt M h c N (m + 1) s = Gn ((s - M) / h) := by
  intro s hs
  obtain ⟨g', hg', hgn⟩ := hd _ hs
  have f1 : HasDerivAt (fun s => h ^ m * segSt M h c N m s)
      (h ^ m * (-(m : ℂ) * segSt M h c N (m + 1) s)) s :=
    (hasDerivAt_segSt hh hpos hs m).const_mul _
  have hζ : HasDerivAt (fun s : ℂ => (s - M) / h) (1 / h) s := by
    simpa using ((hasDerivAt_id s).sub_const M).div_const h
  have f2 : HasDerivAt (fun s => G ((s - M) / h)) (g' * (1 / h)) s :=
    HasDerivAt.comp s hg' hζ
  have hev : (fun s => G ((s - M) / h)) =ᶠ[𝓝 s] fun s => h ^ m * segSt M h c N m s := by
    have hopen : IsOpen {s : ℂ | 1 < jc ((s - M) / h)} :=
      isOpen_jc.preimage (by fun_prop)
    filter_upwards [hopen.mem_nhds hs] with t ht
    exact (hG t ht).symm
  have f3 := f2.congr_of_eventuallyEq hev.symm
  have e := f1.unique f3
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have e2 : g' = -(h ^ (m + 1) * ((m : ℂ) * segSt M h c N (m + 1) s)) := by
    have e' : g' = h ^ m * (-(m : ℂ) * segSt M h c N (m + 1) s) * h := by
      field_simp at e ⊢
      linear_combination -e
    rw [e']; ring
  rw [← hgn, e2]
  field_simp

/-- R6 (Lemma 2): closed forms of `h^m S_m`, `m = 1..4`. -/
theorem segSt_closed {M h : ℂ} (hh : h ≠ 0) {c : ℕ → ℝ} {N : ℕ}
    (hpos : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ chebF c N x) {s : ℂ} (hs : 1 < jc ((s - M) / h)) :
    (h * segSt M h c N 1 s =
      (jq ((s - M) / h))⁻¹ * segFC c N (jphi ((s - M) / h))⁻¹ 0) ∧
    (h ^ 2 * segSt M h c N 2 s =
      ((s - M) / h) * (jq ((s - M) / h))⁻¹ ^ 3 * segFC c N (jphi ((s - M) / h))⁻¹ 0 +
        (jq ((s - M) / h))⁻¹ ^ 2 * segFC c N (jphi ((s - M) / h))⁻¹ 1) ∧
    (h ^ 3 * segSt M h c N 3 s =
      (1 / 2) * (3 * ((s - M) / h) ^ 2 * (jq ((s - M) / h))⁻¹ ^ 5 *
          segFC c N (jphi ((s - M) / h))⁻¹ 0
        - (jq ((s - M) / h))⁻¹ ^ 3 * segFC c N (jphi ((s - M) / h))⁻¹ 0
        + 3 * ((s - M) / h) * (jq ((s - M) / h))⁻¹ ^ 4 * segFC c N (jphi ((s - M) / h))⁻¹ 1
        + (jq ((s - M) / h))⁻¹ ^ 3 * segFC c N (jphi ((s - M) / h))⁻¹ 2)) ∧
    (h ^ 4 * segSt M h c N 4 s =
      (5 / 2) * ((s - M) / h) ^ 3 * (jq ((s - M) / h))⁻¹ ^ 7 * segFC c N (jphi ((s - M) / h))⁻¹ 0
      - (3 / 2) * ((s - M) / h) * (jq ((s - M) / h))⁻¹ ^ 5 * segFC c N (jphi ((s - M) / h))⁻¹ 0
      + (5 / 2) * ((s - M) / h) ^ 2 * (jq ((s - M) / h))⁻¹ ^ 6 * segFC c N (jphi ((s - M) / h))⁻¹ 1
      - (2 / 3) * (jq ((s - M) / h))⁻¹ ^ 4 * segFC c N (jphi ((s - M) / h))⁻¹ 1
      + ((s - M) / h) * (jq ((s - M) / h))⁻¹ ^ 5 * segFC c N (jphi ((s - M) / h))⁻¹ 2
      + (1 / 6) * (jq ((s - M) / h))⁻¹ ^ 4 * segFC c N (jphi ((s - M) / h))⁻¹ 3) := by
  have du : ∀ ζ, 1 < jc ζ → HasDerivAt (fun z => (jq z)⁻¹) (-(ζ * (jq ζ)⁻¹ ^ 3)) ζ :=
    fun ζ h => hasDerivAt_jq_inv h
  have dF : ∀ j ζ, 1 < jc ζ → HasDerivAt (fun z => segFC c N (jphi z)⁻¹ j)
      (-((jq ζ)⁻¹ * segFC c N (jphi ζ)⁻¹ (j + 1))) ζ :=
    fun j ζ h => hasDerivAt_segFC h c N j
  have h1 : ∀ s, 1 < jc ((s - M) / h) → h ^ 1 * segSt M h c N 1 s =
      (fun z => (jq z)⁻¹ * segFC c N (jphi z)⁻¹ 0) ((s - M) / h) := by
    intro s hs
    rw [segSt_one hh hpos hs]
    have hq := jq_ne_zero hs
    have hF0 : segFC c N (jphi ((s - M) / h))⁻¹ 0 = (c 0 : ℂ) + ∑ k ∈ Finset.range N,
        (c (k + 1) : ℂ) * (jphi ((s - M) / h))⁻¹ ^ (k + 1) := by
      simp only [segFC]
      rw [Finset.sum_range_succ']
      simp [add_comm]
    simp only
    rw [hF0]
    field_simp
  have h2 := step_closed hh hpos (m := 1) le_rfl _
    (fun z => z * (jq z)⁻¹ ^ 3 * segFC c N (jphi z)⁻¹ 0 + (jq z)⁻¹ ^ 2 * segFC c N (jphi z)⁻¹ 1)
    h1 (by
      intro ζ hζ
      refine ⟨_, ((du ζ hζ).fun_mul (dF 0 ζ hζ)), ?_⟩
      simp only [Nat.cast_one]; ring)
  have h3 := step_closed hh hpos (m := 2) (by norm_num) _
    (fun z => (1 / 2) * (3 * z ^ 2 * (jq z)⁻¹ ^ 5 * segFC c N (jphi z)⁻¹ 0
        - (jq z)⁻¹ ^ 3 * segFC c N (jphi z)⁻¹ 0
        + 3 * z * (jq z)⁻¹ ^ 4 * segFC c N (jphi z)⁻¹ 1 + (jq z)⁻¹ ^ 3 * segFC c N (jphi z)⁻¹ 2))
    h2 (by
      intro ζ hζ
      have e1 := ((hasDerivAt_id ζ).fun_mul ((du ζ hζ).fun_pow 3)).fun_mul (dF 0 ζ hζ)
      have e2 := ((du ζ hζ).fun_pow 2).fun_mul (dF 1 ζ hζ)
      refine ⟨_, e1.fun_add e2, ?_⟩
      simp only [id, Nat.cast_ofNat, Nat.reduceSub, pow_one]; ring)
  have h4 := step_closed hh hpos (m := 3) (by norm_num) _
    (fun z => (5 / 2) * z ^ 3 * (jq z)⁻¹ ^ 7 * segFC c N (jphi z)⁻¹ 0
      - (3 / 2) * z * (jq z)⁻¹ ^ 5 * segFC c N (jphi z)⁻¹ 0
      + (5 / 2) * z ^ 2 * (jq z)⁻¹ ^ 6 * segFC c N (jphi z)⁻¹ 1
      - (2 / 3) * (jq z)⁻¹ ^ 4 * segFC c N (jphi z)⁻¹ 1
      + z * (jq z)⁻¹ ^ 5 * segFC c N (jphi z)⁻¹ 2
      + (1 / 6) * (jq z)⁻¹ ^ 4 * segFC c N (jphi z)⁻¹ 3)
    h3 (by
      intro ζ hζ
      have a0 := dF 0 ζ hζ
      have a1 := dF 1 ζ hζ
      have a2 := dF 2 ζ hζ
      have u2 := (du ζ hζ).fun_pow 2
      have u3 := (du ζ hζ).fun_pow 3
      have u4 := (du ζ hζ).fun_pow 4
      have u5 := (du ζ hζ).fun_pow 5
      have z2 := (hasDerivAt_id ζ).fun_pow 2
      have t1 := ((z2.const_mul 3).fun_mul u5).fun_mul a0
      have t2 := u3.fun_mul a0
      have t3 := (((hasDerivAt_id ζ).const_mul 3).fun_mul u4).fun_mul a1
      have t4 := u3.fun_mul a2
      refine ⟨_, ((((t1.fun_sub t2).fun_add t3).fun_add t4).const_mul (1 / 2)), ?_⟩
      simp only [id, Nat.cast_ofNat, Nat.reduceSub, pow_one, Nat.reduceMul]; ring)
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [pow_one] using h1 s hs
  · exact h2 s hs
  · exact h3 s hs
  · exact h4 s hs

/-- on the perturbation segment the distance `d` also controls `‖S_m‖`: `‖S_m w‖ ≤ c₀ / d^m`. -/
theorem norm_segSt_le_of_seg {M h : ℂ} (hh : h ≠ 0) {c : ℕ → ℝ} {N : ℕ}
    (hpos : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ chebF c N x) {w : ℂ} {d : ℝ} (hd : 0 < d)
    (hw : d ≤ ‖h‖ * (jc ((w - M) / h) - 1)) (m : ℕ) :
    ‖segSt M h c N m w‖ ≤ c 0 / d ^ m := by
  have hjc : 1 < jc ((w - M) / h) := by
    have hh0 : 0 < ‖h‖ := norm_pos_iff.2 hh
    by_contra hcon
    push Not at hcon
    nlinarith
  have := norm_segSt_le hh hpos hjc m
  refine this.trans ?_
  have hc0 : 0 ≤ c 0 := by
    have h1 := norm_segSt_le hh hpos hjc 0
    have h2 : 0 ≤ ‖segSt M h c N 0 w‖ := norm_nonneg _
    simp at h1
    linarith
  exact div_le_div_of_nonneg_left hc0 (pow_pos hd m) (pow_le_pow_left₀ hd.le hw m)

/-- R7 (Lemma 3, complex): perturbation of `D_k`. -/
theorem segD_pert {M h : ℂ} (hh : h ≠ 0) {c : ℕ → ℝ} {N : ℕ}
    (hpos : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ chebF c N x) {s s' : ℂ} {d : ℝ} (hd : 0 < d)
    (hseg : ∀ w ∈ segment ℝ s' s, d ≤ ‖h‖ * (jc ((w - M) / h) - 1)) {k : ℕ} (hk : 1 ≤ k) :
    ‖segD M h c N k s - segD M h c N k s'‖ ≤
      ‖s - s'‖ * (((k.factorial : ℕ) : ℝ) * c 0 / d ^ (k + 1)) := by
  have hjc : ∀ w ∈ segment ℝ s' s, 1 < jc ((w - M) / h) := by
    intro w hw
    have h1 := hseg w hw
    have hh0 : 0 < ‖h‖ := norm_pos_iff.2 hh
    by_contra hcon
    push Not at hcon
    nlinarith
  have key := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := segD M h c N k) (f' := fun w => segD M h c N (k + 1) w)
    (C := ((k.factorial : ℕ) : ℝ) * c 0 / d ^ (k + 1)) (s := segment ℝ s' s) (x := s') (y := s)
    (fun w hw => (hasDerivAt_segD hh hpos (hjc w hw) hk).hasDerivWithinAt)
    (fun w hw => by
      have hn := norm_segSt_le_of_seg hh hpos hd (hseg w hw) (k + 1)
      have e : ‖segD M h c N (k + 1) w‖ = (k.factorial : ℝ) * ‖segSt M h c N (k + 1) w‖ := by
        simp [segD]
      rw [e]
      calc (k.factorial : ℝ) * ‖segSt M h c N (k + 1) w‖
          ≤ (k.factorial : ℝ) * (c 0 / d ^ (k + 1)) :=
            mul_le_mul_of_nonneg_left hn (Nat.cast_nonneg _)
        _ = _ := by ring)
    (convex_segment s' s) (left_mem_segment ℝ s' s) (right_mem_segment ℝ s' s)
  rw [mul_comm]
  exact key

/-- R8 (Lemma 3, `U`): perturbation of the logarithmic potential. -/
theorem logPotC_pert {M h : ℂ} (hh : h ≠ 0) {c : ℕ → ℝ} {N : ℕ}
    (hpos : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ chebF c N x) {s s' : ℂ} {d : ℝ} (hd : 0 < d)
    (hseg : ∀ w ∈ segment ℝ s' s, d ≤ ‖h‖ * (jc ((w - M) / h) - 1)) :
    |logPotC (segMeasure M h c N) s - logPotC (segMeasure M h c N) s'| ≤ ‖s - s'‖ * (c 0 / d) := by
  set γ : ℝ → ℂ := fun t => s' + (t : ℂ) * (s - s') with hγ
  have hγd : ∀ t, HasDerivAt γ (s - s') t := by
    intro t
    have := ((hasDerivAt_id t).ofReal_comp.mul_const (s - s')).const_add s'
    simpa [hγ] using this
  have hmem : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ segment ℝ s' s := by
    intro t ht
    rw [segment_eq_image']
    exact ⟨t, ht, by simp [hγ, Complex.real_smul]⟩
  have hjc : ∀ t ∈ Icc (0 : ℝ) 1, 1 < jc ((γ t - M) / h) := by
    intro t ht
    have h1 := hseg _ (hmem t ht)
    have hh0 : 0 < ‖h‖ := norm_pos_iff.2 hh
    by_contra hcon
    push Not at hcon
    nlinarith
  have key := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun t => logPotC (segMeasure M h c N) (γ t))
    (f' := fun t => -(((s - s') * segSt M h c N 1 (γ t)).re))
    (C := ‖s - s'‖ * (c 0 / d)) (s := Icc (0 : ℝ) 1) (x := 0) (y := 1)
    (fun t ht => (hasDerivAt_logPotC_seg hh hpos hγd (continuous_const) (hjc t ht)).hasDerivWithinAt)
    (fun t ht => by
      have hn := norm_segSt_le_of_seg hh hpos hd (hseg _ (hmem t ht)) 1
      rw [Real.norm_eq_abs, abs_neg]
      refine (Complex.abs_re_le_norm _).trans ?_
      rw [norm_mul]
      calc ‖s - s'‖ * ‖segSt M h c N 1 (γ t)‖ ≤ ‖s - s'‖ * (c 0 / d ^ 1) :=
            mul_le_mul_of_nonneg_left hn (norm_nonneg _)
        _ = _ := by ring)
    (convex_Icc 0 1) (by simp) (by simp)
  have e0 : γ 0 = s' := by simp [hγ]
  have e1 : γ 1 = s := by simp [hγ]
  simp only [e0, e1, sub_zero, Real.norm_eq_abs, abs_one, mul_one] at key
  exact key

/-! ### R10: rational data and the enclosure -/

/-- Faà di Bruno over Gaussian rationals (orders `0..4`). -/
def fdbQ (D Y : ℕ → CQ) : ℕ → CQ
  | 0 => D 0
  | 1 => (D 1).mul (Y 1)
  | 2 => ((D 2).mul ((Y 1).pow 2)).add ((D 1).mul (Y 2))
  | 3 => (((D 3).mul ((Y 1).pow 3)).add (CQ.smul 3 (((D 2).mul (Y 1)).mul (Y 2)))).add
      ((D 1).mul (Y 3))
  | 4 => ((((D 4).mul ((Y 1).pow 4)).add (CQ.smul 6 (((D 3).mul ((Y 1).pow 2)).mul (Y 2)))).add
      ((D 2).mul (CQ.add (CQ.smul 3 ((Y 2).pow 2)) (CQ.smul 4 ((Y 1).mul (Y 3)))))).add
      ((D 1).mul (Y 4))
  | _ => CQ.zero

/-- The rational data of a segment: `h`, the rational point `φ̃` (`|φ̃| > 1`), the coefficients
`c_k` and the degree `N`. -/
structure SegQ where
  hq : CQ
  φq : CQ
  cq : ℕ → ℚ
  N : ℕ

namespace SegQ

/-- `ψ̃ = φ̃⁻¹`. -/
def ψ (P : SegQ) : CQ := P.φq.inv
/-- `ζ̃ = J(φ̃) = (φ̃ + ψ̃)/2`. -/
def ζ (P : SegQ) : CQ := CQ.smul (1 / 2) (P.φq.add P.ψ)
/-- `ũ = q̃⁻¹`, `q̃ = (φ̃ - ψ̃)/2`. -/
def u (P : SegQ) : CQ := (CQ.smul (1 / 2) (P.φq.sub P.ψ)).inv
/-- `F_j(ψ̃) = Σ_{k ≤ N} k^j c_k ψ̃^k`. -/
def F (P : SegQ) (j : ℕ) : CQ :=
  CQ.sumTo (fun k => CQ.smul (P.cq k * ((k : ℚ) ^ j)) (P.ψ.pow k)) (P.N + 1)
/-- The closed forms `G_m = h^m S_m` of Lemma 2 at `ζ̃` (`m = 1..4`). -/
def G (P : SegQ) : ℕ → CQ
  | 1 => P.u.mul (P.F 0)
  | 2 => ((P.ζ.mul (P.u.pow 3)).mul (P.F 0)).add ((P.u.pow 2).mul (P.F 1))
  | 3 => CQ.smul (1 / 2) ((((CQ.smul 3 ((P.ζ.pow 2).mul (P.u.pow 5))).sub (P.u.pow 3)).mul (P.F 0)).add
      (((CQ.smul 3 (P.ζ.mul (P.u.pow 4))).mul (P.F 1)).add ((P.u.pow 3).mul (P.F 2))))
  | 4 => (((((CQ.smul (5 / 2) ((P.ζ.pow 3).mul (P.u.pow 7))).sub
        (CQ.smul (3 / 2) (P.ζ.mul (P.u.pow 5)))).mul (P.F 0)).add
      (((CQ.smul (5 / 2) ((P.ζ.pow 2).mul (P.u.pow 6))).sub (CQ.smul (2 / 3) (P.u.pow 4))).mul (P.F 1))).add
      ((P.ζ.mul (P.u.pow 5)).mul (P.F 2))).add (CQ.smul (1 / 6) ((P.u.pow 4).mul (P.F 3)))
  | _ => CQ.zero
/-- `D̃_k = (-1)^k (k-1)! G_k / h^k`: `D_k = segD` at `s̃ = M + h ζ̃`. -/
def D (P : SegQ) (k : ℕ) : CQ :=
  CQ.smul ((-1) ^ k * ((k - 1).factorial : ℚ)) ((P.G k).mul (P.hq.inv.pow k))
/-- `U(s̃)`, from enclosures `l1 ≈ log |h|²`, `l2 ≈ log (|φ̃|²/4)`. -/
def U0 (P : SegQ) (l1 l2 : ℚ) : ℚ :=
  -P.cq 0 * (l1 + l2) / 2 +
    ∑ k ∈ Finset.range P.N, P.cq (k + 1) / ((k + 1 : ℕ) : ℚ) * (P.ψ.pow (k + 1)).re

/-- The rational tower values: `j = 0` the potential, `1 ≤ j ≤ 4` the real part of `fdb`. -/
def Tq (P : SegQ) (l1 l2 : ℚ) (Y : ℕ → CQ) (j : ℕ) : ℚ :=
  if j = 0 then P.U0 l1 l2 else (fdbQ P.D Y j).re

/-- The tower error: `δ c₀/d + c₀ (e₁ + e₂)/2` for `j = 0`, else `fdb (δ k! c₀/d^{k+1}) Ym j`. -/
def Te (P : SegQ) (e1 e2 d δ : ℚ) (Ym : ℕ → ℚ) (j : ℕ) : ℚ :=
  if j = 0 then δ * P.cq 0 / d + P.cq 0 * (e1 + e2) / 2
  else fdb (fun k => δ * ((k.factorial : ℕ) : ℚ) * P.cq 0 / d ^ (k + 1)) Ym j

end SegQ

theorem toC_fdbQ (D Y : ℕ → CQ) {j : ℕ} (hj : j ≤ 4) :
    (fdbQ D Y j).toC = fdb (fun k => (D k).toC) (fun i => (Y i).toC) j := by
  interval_cases j <;>
    simp [fdbQ, fdb, CQ.toC_add, CQ.toC_mul, CQ.toC_smul, CQ.toC_pow] <;> ring

theorem fdb_congr_Y {R : Type*} [CommRing R] (D Y Y' : ℕ → R) {j : ℕ} (hj : j ≤ 5)
    (h : ∀ i, 1 ≤ i → i ≤ j → Y i = Y' i) : fdb D Y j = fdb D Y' j := by
  interval_cases j
  · simp [fdb]
  · simp [fdb, h 1 (by norm_num) (by norm_num)]
  · simp [fdb, h 1 (by norm_num) (by norm_num), h 2 (by norm_num) (by norm_num)]
  · simp [fdb, h 1 (by norm_num) (by norm_num), h 2 (by norm_num) (by norm_num),
      h 3 (by norm_num) (by norm_num)]
  · simp [fdb, h 1 (by norm_num) (by norm_num), h 2 (by norm_num) (by norm_num),
      h 3 (by norm_num) (by norm_num), h 4 (by norm_num) (by norm_num)]
  · simp [fdb, h 1 (by norm_num) (by norm_num), h 2 (by norm_num) (by norm_num),
      h 3 (by norm_num) (by norm_num), h 4 (by norm_num) (by norm_num),
      h 5 (by norm_num) (by norm_num)]

theorem cast_fdb_rat (D Y : ℕ → ℚ) (j : ℕ) :
    (((fdb D Y j : ℚ)) : ℝ) = fdb (fun k => (D k : ℝ)) (fun i => (Y i : ℝ)) j := by
  rcases j with _ | _ | _ | _ | _ | _ | j <;> simp [fdb]

/-- the distance of the perturbation segment from `[M - |h|, M + |h|]`-type segment: if `jc ζ0`
is at least `(R + R⁻¹)/2` and `s'` is `M + h ζ0`, then on `[s', s]` the distance is at least
`hlo ((R + R⁻¹)/2 - 1) - δ`. -/
theorem seg_dist_lb {M h s s' ζ0 : ℂ} {δ hlo R : ℝ} (hh : h ≠ 0) (hs0 : s' = M + h * ζ0)
    (hjc : (R + R⁻¹) / 2 ≤ jc ζ0) (hR : 1 ≤ R) (hδ : ‖s - s'‖ ≤ δ) (hlo0 : 0 ≤ hlo)
    (hlh : hlo ≤ ‖h‖) :
    ∀ w ∈ segment ℝ s' s, hlo * ((R + R⁻¹) / 2 - 1) - δ ≤ ‖h‖ * (jc ((w - M) / h) - 1) := by
  intro w hw
  rw [segment_eq_image'] at hw
  obtain ⟨θ, hθ, rfl⟩ := hw
  have hh0 : 0 < ‖h‖ := norm_pos_iff.2 hh
  have hn : ‖θ • (s - s')‖ ≤ δ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hθ.1]
    nlinarith [hθ.1, hθ.2, norm_nonneg (s - s')]
  have e : (s' + θ • (s - s') - M) / h - ζ0 = (θ • (s - s')) / h := by
    rw [hs0]; field_simp; ring
  have hl := jc_lipschitz ((s' + θ • (s - s') - M) / h) ζ0
  rw [e, norm_div] at hl
  have hl2 : jc ζ0 - ‖θ • (s - s')‖ / ‖h‖ ≤ jc ((s' + θ • (s - s') - M) / h) := by
    have := (abs_le.1 hl).1; linarith
  have hR0 : 0 < R := by linarith
  have hpos : 0 ≤ (R + R⁻¹) / 2 - 1 := by
    have : R + R⁻¹ - 2 = (R - 1) ^ 2 / R := by field_simp; ring
    have h2 : 0 ≤ (R - 1) ^ 2 / R := by positivity
    linarith
  have h3 : ‖h‖ * (jc ((s' + θ • (s - s') - M) / h) - 1) ≥
      ‖h‖ * (jc ζ0 - 1) - ‖θ • (s - s')‖ := by
    have : ‖h‖ * (‖θ • (s - s')‖ / ‖h‖) = ‖θ • (s - s')‖ := by field_simp
    nlinarith
  have h4 : hlo * ((R + R⁻¹) / 2 - 1) ≤ ‖h‖ * ((R + R⁻¹) / 2 - 1) :=
    mul_le_mul_of_nonneg_right hlh hpos
  have h5 : ‖h‖ * ((R + R⁻¹) / 2 - 1) ≤ ‖h‖ * (jc ζ0 - 1) :=
    mul_le_mul_of_nonneg_left (by linarith) hh0.le
  linarith

theorem nsq_ne_of_toC {a : CQ} (h : a.toC ≠ 0) : a.nsq ≠ 0 := by
  intro h0; apply h
  have : Complex.normSq a.toC = 0 := by rw [← CQ.nsq_cast, h0]; simp
  exact Complex.normSq_eq_zero.1 this

theorem norm_toC_sq (a : CQ) : ‖a.toC‖ ^ 2 = (a.nsq : ℝ) := by
  rw [CQ.nsq_cast, Complex.normSq_eq_norm_sq]

theorem add_inv_mono {R t : ℝ} (hR : 1 ≤ R) (ht : R ≤ t) : R + R⁻¹ ≤ t + t⁻¹ := by
  have hR0 : 0 < R := by linarith
  have ht0 : 0 < t := by linarith
  rw [← sub_nonneg]
  have e : t + t⁻¹ - (R + R⁻¹) = (t - R) * (t * R - 1) / (t * R) := by field_simp; ring
  rw [e]
  have : 0 ≤ t * R - 1 := by nlinarith
  positivity

section facts
variable (P : SegQ)

theorem toC_psi (hφ : P.φq.nsq ≠ 0) : P.ψ.toC = P.φq.toC⁻¹ := CQ.toC_inv _ hφ

theorem toC_zeta (hφ : P.φq.nsq ≠ 0) : P.ζ.toC = jJ P.φq.toC := by
  unfold SegQ.ζ jJ
  rw [CQ.toC_smul, CQ.toC_add, toC_psi P hφ]; push_cast; ring

theorem toC_u (hφ : P.φq.nsq ≠ 0) (hq : (P.φq.toC - P.φq.toC⁻¹) / 2 ≠ 0) :
    P.u.toC = ((P.φq.toC - P.φq.toC⁻¹) / 2)⁻¹ := by
  unfold SegQ.u
  have e : (CQ.smul (1 / 2) (P.φq.sub P.ψ)).toC = (P.φq.toC - P.φq.toC⁻¹) / 2 := by
    rw [CQ.toC_smul, CQ.toC_sub, toC_psi P hφ]; push_cast; ring
  rw [CQ.toC_inv _ (nsq_ne_of_toC (by rw [e]; exact hq)), e]

theorem toC_F {c : ℕ → ℝ} (hc : ∀ k ≤ P.N, (P.cq k : ℝ) = c k) (hφ : P.φq.nsq ≠ 0) (j : ℕ) :
    (P.F j).toC = segFC c P.N P.φq.toC⁻¹ j := by
  unfold SegQ.F segFC
  rw [CQ.toC_sumTo]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [CQ.toC_smul, CQ.toC_pow, toC_psi P hφ]
  have := hc k (by have := Finset.mem_range.1 hk; omega)
  rw [← this]
  push_cast
  ring

theorem toC_D {M h : ℂ} {c : ℕ → ℝ} (hc : ∀ k ≤ P.N, (P.cq k : ℝ) = c k)
    (hpos : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ chebF c P.N x) (hh : P.hq.toC = h) (hne : P.hq.nsq ≠ 0)
    (hφ : P.φq.nsq ≠ 0) (hφ1 : 1 < ‖P.φq.toC‖) {k : ℕ} (hk1 : 1 ≤ k) (hk4 : k ≤ 4) :
    (P.D k).toC = segD M h c P.N k (M + h * P.ζ.toC) := by
  have hh0 : h ≠ 0 := by rw [← hh]; exact CQ.toC_ne_zero hne
  have hφ0 : P.φq.toC ≠ 0 := norm_pos_iff.1 (by linarith)
  have hζ := toC_zeta P hφ
  have hs : (M + h * P.ζ.toC - M) / h = P.ζ.toC := by field_simp; ring
  have hjc1 : 1 < jc P.ζ.toC := by rw [hζ]; exact one_lt_jc_jJ hφ1
  have hjphi : jphi P.ζ.toC = P.φq.toC := by rw [hζ]; exact jphi_jJ hφ1
  have hjq : jq P.ζ.toC = (P.φq.toC - P.φq.toC⁻¹) / 2 := by unfold jq; rw [hjphi]
  have hq0 : (P.φq.toC - P.φq.toC⁻¹) / 2 ≠ 0 := by rw [← hjq]; exact jq_ne_zero hjc1
  have hu := toC_u P hφ hq0
  have hF := toC_F P hc hφ
  have cl := segSt_closed hh0 hpos (s := M + h * P.ζ.toC) (by rw [hs]; exact hjc1)
  rw [hs, hjphi, hjq] at cl
  obtain ⟨c1, c2, c3, c4⟩ := cl
  have hG : (P.G k).toC = h ^ k * segSt M h c P.N k (M + h * P.ζ.toC) := by
    interval_cases k <;>
    simp only [SegQ.G, CQ.toC_mul, CQ.toC_add, CQ.toC_sub, CQ.toC_pow, CQ.toC_smul, hu, hF]
    · rw [pow_one, c1]
    · rw [c2]
    · rw [c3]; push_cast; ring
    · rw [c4]; push_cast; ring
  have hhi : P.hq.inv.toC = h⁻¹ := by rw [CQ.toC_inv _ hne, hh]
  unfold SegQ.D segD
  rw [CQ.toC_smul, CQ.toC_mul, CQ.toC_pow, hhi, hG]
  push_cast
  simp only [inv_pow]
  field_simp

end facts

/-- **R10, `segTower_encQ`.** The segment tower `potT` of `ν = f dω` on `{M + h x}` along a curve
`γ`, at a point `x` where `γ 0 x = s` is a Gaussian rational within `δ` of the rational point
`s̃ = M + h J(φ̃)`, is enclosed for `j ≤ 4` by the rational `Tq` with error `Te`. -/
theorem segTower_encQ {M h : ℂ} {c : ℕ → ℝ} (P : SegQ)
    (hpos : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ chebF c P.N x)
    (hc : ∀ k ≤ P.N, (P.cq k : ℝ) = c k)
    (Mq sq : CQ) (hM : Mq.toC = M) (hh : P.hq.toC = h) (hne : P.hq.nsq ≠ 0)
    {γ : ℕ → ℝ → ℂ} {x : ℝ} (Yq : ℕ → CQ) (Ym : ℕ → ℚ)
    (hγ0 : γ 0 x = sq.toC) (hγ : ∀ i, 1 ≤ i → i ≤ 4 → γ i x = (Yq i).toC)
    (hY : ∀ i, 1 ≤ i → i ≤ 4 → 0 ≤ Ym i ∧ (Yq i).nsq ≤ Ym i ^ 2)
    (R δ dq hlo l1 e1 l2 e2 : ℚ) (n1 n2 : ℕ)
    (hR : 1 < R) (hRφ : R ^ 2 ≤ P.φq.nsq) (hδ : 0 ≤ δ)
    (hs : (sq.sub (Mq.add (P.hq.mul P.ζ))).nsq ≤ δ ^ 2)
    (hlo0 : 0 ≤ hlo) (hlo2 : hlo ^ 2 ≤ P.hq.nsq)
    (hd : 0 < dq) (hdq : dq ≤ hlo * ((R + R⁻¹) / 2 - 1) - δ)
    (hl1 : logQ n1 P.hq.nsq = some (l1, e1)) (hl2 : logQ n2 (P.φq.nsq / 4) = some (l2, e2)) :
    ∀ j ≤ 4, |potT M h c P.N γ j x - ((P.Tq l1 l2 Yq j : ℚ) : ℝ)| ≤
      ((P.Te e1 e2 dq δ Ym j : ℚ) : ℝ) := by
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
  have hs' : (M + h * P.ζ.toC - M) / h = P.ζ.toC := by field_simp; ring
  have hjcz : jc P.ζ.toC = (‖P.φq.toC‖ + ‖P.φq.toC‖⁻¹) / 2 := by rw [hζ]; exact jc_jJ hφ0
  have hjc1 : 1 < jc P.ζ.toC := by rw [hζ]; exact one_lt_jc_jJ hφ1
  have hjphi : jphi P.ζ.toC = P.φq.toC := by rw [hζ]; exact jphi_jJ hφ1
  have hjR : jR P.ζ.toC = ‖P.φq.toC‖ := by rw [hζ]; exact jR_jJ hφ1.le
  -- the distance of the perturbation segment
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
  have hdpos : (0 : ℝ) < dq := by exact_mod_cast hd
  have hseg : ∀ w ∈ segment ℝ (M + h * P.ζ.toC) sq.toC,
      (dq : ℝ) ≤ ‖h‖ * (jc ((w - M) / h) - 1) := fun w hw => hdq'.trans (hseg0 w hw)
  have hc0 : 0 ≤ c 0 := by
    have := norm_segSt_le_of_seg hh0 hpos hdpos
      (hseg _ (left_mem_segment ℝ _ _)) 0
    simp only [pow_zero, div_one] at this
    exact (norm_nonneg _).trans this
  have hcq0 : (P.cq 0 : ℝ) = c 0 := hc 0 (Nat.zero_le _)
  intro j hj
  by_cases hj0 : j = 0
  · -- the potential itself
    subst hj0
    simp only [potT, SegQ.Tq, SegQ.Te, ite_true]
    rw [hγ0]
    have p1 := logPotC_pert hh0 hpos hdpos hseg
    have p1' : |logPotC (segMeasure M h c P.N) sq.toC -
        logPotC (segMeasure M h c P.N) (M + h * P.ζ.toC)| ≤ δ * (c 0 / dq) := by
      refine p1.trans ?_
      exact mul_le_mul hδs le_rfl (div_nonneg hc0 hdpos.le) (by exact_mod_cast hδ)
    have p2 := logPotC_segMeasure hh0 hpos (s := M + h * P.ζ.toC) (by rw [hs']; exact hjc1)
    rw [hs', hjR, hjphi] at p2
    -- the logarithms
    obtain ⟨hq1, el1⟩ := logQ_spec hl1
    obtain ⟨hq2, el2⟩ := logQ_spec hl2
    unfold Enc at el1 el2
    simp only at el1 el2
    have lh : Real.log ‖h‖ = Real.log ((P.hq.nsq : ℚ) : ℝ) / 2 := by
      rw [← norm_toC_sq, hh, Real.log_pow]
      push_cast; ring
    have lφ : Real.log (‖P.φq.toC‖ / 2) = Real.log (((P.φq.nsq / 4 : ℚ)) : ℝ) / 2 := by
      have : (((P.φq.nsq / 4 : ℚ)) : ℝ) = (‖P.φq.toC‖ / 2) ^ 2 := by
        push_cast; rw [← norm_toC_sq]; ring
      rw [this, Real.log_pow]; push_cast; ring
    have hU0 : ((P.U0 l1 l2 : ℚ) : ℝ) = -c 0 * (l1 + l2) / 2 + ∑ k ∈ Finset.range P.N,
        c (k + 1) * ((P.φq.toC ^ (k + 1))⁻¹).re / ((k + 1 : ℕ) : ℝ) := by
      unfold SegQ.U0
      push_cast
      rw [hcq0]
      congr 1
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk' := hc (k + 1) (by have := Finset.mem_range.1 hk; omega)
      rw [hk', ← CQ.toC_re, CQ.toC_pow, toC_psi P hφnsq, inv_pow]
      ring
    rw [hU0]
    have p3 : |logPotC (segMeasure M h c P.N) (M + h * P.ζ.toC) -
        (-c 0 * (l1 + l2) / 2 + ∑ k ∈ Finset.range P.N,
          c (k + 1) * ((P.φq.toC ^ (k + 1))⁻¹).re / ((k + 1 : ℕ) : ℝ))| ≤
        c 0 * (e1 + e2) / 2 := by
      rw [p2, lh, lφ]
      have e : -c 0 * (Real.log (((P.hq.nsq : ℚ) : ℝ)) / 2) - c 0 * (Real.log
          (((P.φq.nsq / 4 : ℚ)) : ℝ) / 2) + ∑ k ∈ Finset.range P.N,
            c (k + 1) * ((P.φq.toC ^ (k + 1))⁻¹).re / ((k + 1 : ℕ) : ℝ) -
          (-c 0 * (l1 + l2) / 2 + ∑ k ∈ Finset.range P.N,
            c (k + 1) * ((P.φq.toC ^ (k + 1))⁻¹).re / ((k + 1 : ℕ) : ℝ)) =
          -(c 0 / 2) * ((Real.log (((P.hq.nsq : ℚ) : ℝ)) - l1) +
            (Real.log (((P.φq.nsq / 4 : ℚ)) : ℝ) - l2)) := by ring
      rw [e, abs_mul, abs_neg, abs_of_nonneg (by linarith : 0 ≤ c 0 / 2)]
      have := abs_add_le (Real.log (((P.hq.nsq : ℚ) : ℝ)) - l1)
        (Real.log (((P.φq.nsq / 4 : ℚ)) : ℝ) - l2)
      have h3 : c 0 / 2 * (|Real.log (((P.hq.nsq : ℚ) : ℝ)) - l1| +
          |Real.log (((P.φq.nsq / 4 : ℚ)) : ℝ) - l2|) ≤ c 0 / 2 * (e1 + e2) :=
        mul_le_mul_of_nonneg_left (add_le_add el1 el2) (by linarith)
      nlinarith
    have hcast : ((δ * P.cq 0 / dq + P.cq 0 * (e1 + e2) / 2 : ℚ) : ℝ) =
        δ * (c 0 / dq) + c 0 * (e1 + e2) / 2 := by
      push_cast; rw [hcq0]; ring
    rw [hcast]
    refine le_trans (abs_sub_le _ (logPotC (segMeasure M h c P.N) (M + h * P.ζ.toC)) _) ?_
    linarith
  · -- the derivative tower
    have hj1 : 1 ≤ j := Nat.one_le_iff_ne_zero.2 hj0
    simp only [potT, SegQ.Tq, SegQ.Te, hj0, ↓reduceIte]
    rw [hγ0, cast_fdb_rat]
    have e1 : (((fdbQ P.D Yq j).re : ℚ) : ℝ) =
        (fdb (fun k => (P.D k).toC) (fun i => γ i x) j).re := by
      rw [← CQ.toC_re, toC_fdbQ _ _ hj]
      congr 1
      exact fdb_congr_Y _ _ _ (j := j) (by omega) (fun i h1 h2 => (hγ i h1 (by omega)).symm)
    rw [e1]
    have hηeq : (fun k => (((δ * ((k.factorial : ℕ) : ℚ) * P.cq 0 / dq ^ (k + 1) : ℚ)) : ℝ)) =
        fun k => (δ : ℝ) * ((k.factorial : ℕ) : ℝ) * c 0 / (dq : ℝ) ^ (k + 1) := by
      funext k; push_cast; rw [hcq0]
    rw [hηeq]
    have key := norm_fdb_sub_le (fun k => segD M h c P.N k sq.toC) (fun k => (P.D k).toC)
      (fun i => γ i x) (fun k => (δ : ℝ) * ((k.factorial : ℕ) : ℝ) * c 0 / (dq : ℝ) ^ (k + 1))
      (fun i => (Ym i : ℝ)) hj1 (by omega)
      (fun k hk1 hk2 => by
        rw [toC_D P hc hpos hh hne hφnsq hφ1 hk1 (by omega)]
        have := segD_pert hh0 hpos hdpos hseg hk1
        refine this.trans ?_
        have hf : 0 ≤ ((k.factorial : ℕ) : ℝ) * c 0 / (dq : ℝ) ^ (k + 1) := by positivity
        calc _ ≤ (δ : ℝ) * (((k.factorial : ℕ) : ℝ) * c 0 / (dq : ℝ) ^ (k + 1)) :=
              mul_le_mul_of_nonneg_right hδs hf
          _ = _ := by ring)
      (fun i hi1 hi2 => by
        rw [hγ i hi1 (by omega)]
        obtain ⟨hy0, hy1⟩ := hY i hi1 (by omega)
        have h2 : ‖(Yq i).toC‖ ^ 2 ≤ (Ym i : ℝ) ^ 2 := by
          rw [norm_toC_sq]; exact_mod_cast hy1
        by_contra hcon
        push Not at hcon
        nlinarith [norm_nonneg (Yq i).toC, (by exact_mod_cast hy0 : (0 : ℝ) ≤ Ym i)])
    refine le_trans ?_ key
    rw [← Complex.sub_re]
    exact (Complex.abs_re_le_norm _)

/-! ### A tiny regression instance (`h = 1`, `φ̃ = 2`, `f = 3/2`: `S₁ = 2`, `S₂ = 40/9` at `ζ̃ = 5/4`) -/

/-- `kcost`: negligible (a few rational operations). -/
example :
    let P : SegQ := ⟨⟨1, 0⟩, ⟨2, 0⟩, fun k => if k = 0 then 3 / 2 else 0, 0⟩
    (P.D 1).re = -2 ∧ (P.D 1).im = 0 ∧ (P.D 2).re = 40 / 9 ∧ (P.D 2).im = 0 := by
  -- kcost: 0.01 s
  decide +kernel

end CatalanCore.Lai.DecayTowerSeg
