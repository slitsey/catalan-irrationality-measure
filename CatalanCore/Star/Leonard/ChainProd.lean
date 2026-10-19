module

public import CatalanCore.Star.Leonard.DStep
public import CatalanCore.Linalg.KrylovChain

/-!
# Explicit chain products for `u(T~, Π c_{y_0})` (package H4)

`bkdet_Ttil_chain`: for a chain of Cauchy columns `c_{y_0}, c_{y_1}, …` with
`T~ c_{y_j} = l_j c_{y_{j+1}} + (lower) + (range W_Y)`,
`u(T~, Π c_{y_0}) = (∏_k ∏_{j<k} l_j) · cauFac(Y ∪ {y_j})`.
Instances: downward from `S` and from `0` (leading coefficient `l(y) = -τ(-θ-y)`), upward from `1`
(leading coefficient `r(y) = -σ(-θ-y-1)`).  Each is nonzero (cyclicity hypotheses of `ds_concrete`).
-/

@[expose] public section

open Finset Matrix

namespace CatalanCore.Star.Leonard

variable {F : Type*} [Field F]

/-- The Cauchy factor of a family `v` of shifts. -/
noncomputable def cauFac (θ : F) {N : ℕ} (v : Fin N → F) : F :=
  (∏ i : Fin N, ∏ j ∈ Finset.Ioi i, ((((j : ℕ) : F) - ((i : ℕ) : F)) * (v j - v i))) /
    ∏ i : Fin N, ∏ j : Fin N, (θ + ((i : ℕ) : F) + v j)

lemma gen_add {θ : F} (hθ : Gen θ) (a : ℕ) (z : ℤ) : θ + (a : F) + (z : F) ≠ 0 := by
  have := hθ ((a : ℤ) + z)
  push_cast at this
  rwa [← add_assoc] at this

lemma cauFac_ne_zero [CharZero F] {θ : F} (hθ : Gen θ) {N : ℕ} (v : Fin N → ℤ)
    (hv : Function.Injective v) : cauFac θ (fun j => (v j : F)) ≠ 0 := by
  unfold cauFac
  refine div_ne_zero (Finset.prod_ne_zero_iff.2 fun i _ => Finset.prod_ne_zero_iff.2
    fun j hj => mul_ne_zero ?_ ?_) (Finset.prod_ne_zero_iff.2 fun i _ => Finset.prod_ne_zero_iff.2
    fun j _ => gen_add hθ i (v j))
  · have hlt : i < j := Finset.mem_Ioi.1 hj
    have : (i : ℕ) < j := hlt
    intro h
    have : ((j : ℕ) : F) = ((i : ℕ) : F) := by linear_combination h
    have := Nat.cast_injective this
    omega
  · intro h
    have h2 : (v j : F) = (v i : F) := by linear_combination h
    have h3 := hv (Int.cast_injective h2)
    have h4 : i < j := Finset.mem_Ioi.1 hj
    exact absurd h3 (ne_of_gt h4)

/-- `Π` kills `range W_Y`, and `Π x = x - W_Y (…)`. -/
lemma projB_props [CharZero F] (m n S : ℕ) (θ : F)
    (hΔ : IsUnit ((Wb (m + n) θ (bX m (S : ℤ)))ᵀ * Wb (m + n) θ (bY m (S : ℤ))).det) :
    (∀ x ∈ CatalanCore.Wsp (Wb (m + n) θ (bY m (S : ℤ))),
      projB (m + n) θ (bX m (S : ℤ)) (bY m (S : ℤ)) *ᵥ x = 0) ∧
    (∀ x, ∃ a : Fin m → F, projB (m + n) θ (bX m (S : ℤ)) (bY m (S : ℤ)) *ᵥ x =
      x - Wb (m + n) θ (bY m (S : ℤ)) *ᵥ a) := by
  set WX := Wb (m + n) θ (bX m (S : ℤ))
  set WY := Wb (m + n) θ (bY m (S : ℤ))
  have hMG : ((WXᵀ * WY)⁻¹) * (WXᵀ * WY) = 1 := Matrix.nonsing_inv_mul _ hΔ
  refine ⟨?_, fun x => ⟨((WXᵀ * WY)⁻¹ * WXᵀ) *ᵥ x, ?_⟩⟩
  · rintro x ⟨a, rfl⟩
    change projB (m + n) θ (bX m (S : ℤ)) (bY m (S : ℤ)) *ᵥ (WY *ᵥ a) = 0
    unfold projB
    rw [Matrix.mulVec_mulVec, Matrix.sub_mul, Matrix.one_mul]
    have : WY * (WXᵀ * WY)⁻¹ * WXᵀ * WY = WY := by
      calc WY * (WXᵀ * WY)⁻¹ * WXᵀ * WY = WY * ((WXᵀ * WY)⁻¹ * (WXᵀ * WY)) := by
            simp only [Matrix.mul_assoc]
        _ = WY := by rw [hMG, Matrix.mul_one]
    rw [this]; simp
  · unfold projB
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
    rfl

theorem bkdet_Ttil_chain [CharZero F] (m n S : ℕ) (hm : 1 ≤ m) (θ : F) (hθ : Gen θ)
    (hΔ : IsUnit ((Wb (m + n) θ (bX m (S : ℤ)))ᵀ * Wb (m + n) θ (bY m (S : ℤ))).det)
    (y : ℕ → ℤ) (l : ℕ → F)
    (hc : ∀ j, j + 1 < n → ∃ a b : F, ∃ w ∈ CatalanCore.Wsp (Wb (m + n) θ (bY m (S : ℤ))),
      Ttil (m + n) m S θ *ᵥ wcol (m + n) θ (y j) = l j • wcol (m + n) θ (y (j + 1))
        + a • wcol (m + n) θ (y j) + b • wcol (m + n) θ (y (j - 1)) + w) :
    CatalanCore.bkdet (Wb (m + n) θ (bY m (S : ℤ))) (Ttil (m + n) m S θ)
        (projB (m + n) θ (bX m (S : ℤ)) (bY m (S : ℤ)) *ᵥ wcol (m + n) θ (y 0)) =
      (∏ k : Fin n, ∏ j ∈ Finset.range k, l j) *
        cauFac θ (Fin.addCases (fun i : Fin m => ((bY m (S : ℤ) i : ℤ) : F))
          (fun j : Fin n => ((y j : ℤ) : F))) := by
  obtain ⟨hPW, hPc⟩ := projB_props m n S θ hΔ
  rw [CatalanCore.bkdet_chain_proj (Ttil_preserves_WY m n S hm θ hθ) hPW hPc
    (Ttil_comm_projB m n S hm θ hθ hΔ) (fun j => wcol (m + n) θ (y j)) l hc]
  congr 1
  have hne : ∀ (a : Fin (m + n)) (j : Fin (m + n)),
      θ + ((a : ℕ) : F) + Fin.addCases (fun i : Fin m => ((bY m (S : ℤ) i : ℤ) : F))
        (fun j : Fin n => ((y j : ℤ) : F)) j ≠ 0 := by
    intro a j
    refine Fin.addCases (fun i => ?_) (fun j => ?_) j
    · simp only [Fin.addCases_left]; exact gen_add hθ a _
    · simp only [Fin.addCases_right]; exact gen_add hθ a _
  exact CatalanCore.bmat_cauchy_det θ _ _ hne

/-- the border sum of `Σ κ_j c_{S+2j+1}` lies in `range W_Y`. -/
lemma sum_border_mem (m n S : ℕ) (θ : F) (κ : ℕ → F) :
    (∑ j ∈ Finset.range m, κ j • wcol (m + n) θ ((S + 2 * j + 1 : ℕ) : ℤ)) ∈
      CatalanCore.Wsp (Wb (m + n) θ (bY m (S : ℤ))) := by
  refine Submodule.sum_mem _ fun j hj => Submodule.smul_mem _ _ ?_
  have hj' := Finset.mem_range.1 hj
  have : wcol (m + n) θ ((S + 2 * j + 1 : ℕ) : ℤ) = fun a => Wb (m + n) θ (bY m (S : ℤ)) a ⟨j, hj'⟩ := by
    funext a; simp [Wb, bY, wcol]; ring_nf
  rw [this]; exact col_mem_Wsp _ ⟨j, hj'⟩

/-- (CC) with explicit coefficients for `y + 1 ≤ S`. -/
lemma Ttil_rel [CharZero F] (m n S : ℕ) (hm : 1 ≤ m) (θ : F) (hθ : Gen θ) (y : ℤ)
    (hy : y + 1 ≤ (S : ℤ)) :
    ∃ d : F, ∃ w ∈ CatalanCore.Wsp (Wb (m + n) θ (bY m (S : ℤ))),
      Ttil (m + n) m S θ *ᵥ wcol (m + n) θ y =
        (-tau (m + n) m S θ (-θ - y)) • wcol (m + n) θ (y - 1) + d • wcol (m + n) θ y
          + (-sigma (m + n) m S θ (-θ - y - 1)) • wcol (m + n) θ (y + 1) + w := by
  obtain ⟨κ, h⟩ := Ttil_col (m + n) m S hm θ hθ y hy
  exact ⟨_, _, sum_border_mem m n S θ κ, h⟩

/-- (CC) at the top `y = S`: no `c_{S+1}` term. -/
lemma Ttil_rel_top [CharZero F] (m n S : ℕ) (hm : 1 ≤ m) (θ : F) (hθ : Gen θ) :
    ∃ d : F, ∃ w ∈ CatalanCore.Wsp (Wb (m + n) θ (bY m (S : ℤ))),
      Ttil (m + n) m S θ *ᵥ wcol (m + n) θ (S : ℤ) =
        (-tau (m + n) m S θ (-θ - (S : ℤ))) • wcol (m + n) θ ((S : ℤ) - 1) + d • wcol (m + n) θ (S : ℤ)
          + w := by
  obtain ⟨κ, h⟩ := Ttil_col_all (m + n) m S hm θ hθ S le_rfl
  have hb : (bP (m + n) m (S : F) θ).eval (-(((S : ℤ) : ℤ) : F) - 1) = 0 := by
    unfold bP
    simp only [Polynomial.eval_neg, Polynomial.eval_mul, eval_lin]
    have : (1 : F) * (-(((S : ℤ) : ℤ) : F) - 1) + ((S : F) + 1) = 0 := by push_cast; ring
    rw [this]; ring
  rw [hb, zero_div, zero_smul, add_zero] at h
  exact ⟨_, _, sum_border_mem m n S θ κ, h⟩

/-! ### Nonvanishing of the chain coefficients -/

lemma pp_ne_zero [CharZero F] (K : ℕ) (θ : F) (hθ : Gen θ) (y : ℤ) (h1 : y ≠ 1) :
    pp K θ (-θ - (y : F)) ≠ 0 := by
  unfold pp
  refine mul_ne_zero (mul_ne_zero ?_ ?_) ?_
  · intro h; apply hθ (y - 1); push_cast; linear_combination -h
  · intro h
    have : ((1 - y : ℤ) : F) = 0 := by push_cast; linear_combination h
    exact h1 (by have := Int.cast_eq_zero.1 this; omega)
  · intro h; apply hθ ((K : ℤ) - 1 + y); push_cast; linear_combination h

lemma pp_ne_zero' [CharZero F] (K : ℕ) (θ : F) (hθ : Gen θ) (y : ℤ) (h0 : y ≠ 0) :
    pp K θ (-θ - (y : F) - 1) ≠ 0 := by
  unfold pp
  refine mul_ne_zero (mul_ne_zero ?_ ?_) ?_
  · intro h; apply hθ y; push_cast; linear_combination -h
  · intro h
    have : ((y : ℤ) : F) = 0 := by linear_combination -h
    exact h0 (Int.cast_eq_zero.1 this)
  · intro h; apply hθ ((K : ℤ) + y); push_cast; linear_combination h

lemma tau_ne_zero_chain [CharZero F] (m n S : ℕ) (θ : F) (hθ : Gen θ) (y : ℤ) (h1 : y ≠ 1)
    (hQ : ∀ i : ℕ, i ≤ m → (S : ℤ) + 2 * i + 1 - y ≠ 0)
    (hP : ∀ i : ℕ, i < m → (S : ℤ) + 2 * (i + 1) - y ≠ 0) :
    tau (m + n) m S θ (-θ - (y : F)) ≠ 0 := by
  unfold tau
  refine div_ne_zero (mul_ne_zero (pp_ne_zero _ θ hθ y h1) ?_) ?_
  · refine Finset.prod_ne_zero_iff.2 fun i hi => ?_
    have := hQ i (by have := Finset.mem_range.1 hi; omega)
    intro h; apply this
    have h2 : (((S : ℤ) + 2 * i + 1 - y : ℤ) : F) = 0 := by push_cast; linear_combination h
    exact_mod_cast h2
  · refine Finset.prod_ne_zero_iff.2 fun i hi => ?_
    have := hP i (Finset.mem_range.1 hi)
    intro h; apply this
    have h2 : (((S : ℤ) + 2 * (i + 1) - y : ℤ) : F) = 0 := by push_cast; linear_combination h
    exact_mod_cast h2

lemma sigma_ne_zero_chain [CharZero F] (m n S : ℕ) (θ : F) (hθ : Gen θ) (y : ℤ) (h0 : y ≠ 0)
    (hP : ∀ i : ℕ, i < m → (S : ℤ) + 2 * i + 1 - y ≠ 0)
    (hQ : ∀ i : ℕ, i + 1 < m → (S : ℤ) + 2 * i + 2 - y ≠ 0) :
    sigma (m + n) m S θ (-θ - (y : F) - 1) ≠ 0 := by
  unfold sigma
  refine div_ne_zero (mul_ne_zero (pp_ne_zero' _ θ hθ y h0) ?_) ?_
  · refine Finset.prod_ne_zero_iff.2 fun i hi => ?_
    have := hP i (Finset.mem_range.1 hi)
    intro h; apply this
    have h2 : (((S : ℤ) + 2 * i + 1 - y : ℤ) : F) = 0 := by push_cast; linear_combination h
    exact_mod_cast h2
  · refine Finset.prod_ne_zero_iff.2 fun i hi => ?_
    have := hQ i (by have := Finset.mem_range.1 hi; omega)
    intro h; apply this
    have h2 : (((S : ℤ) + 2 * i + 2 - y : ℤ) : F) = 0 := by push_cast; linear_combination h
    exact_mod_cast h2

end CatalanCore.Star.Leonard
