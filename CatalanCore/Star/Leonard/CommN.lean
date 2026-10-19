module

public import CatalanCore.Star.Leonard.CCAll
public import CatalanCore.Star.Leonard.Invariance
public import CatalanCore.Linalg.Telescope

/-!
# `[N_S, T~] x ∈ range W_Y` for `x ∈ ker W_Xᵀ` (package H4, `(Comm)`)

`N_S = Σ_{y=1}^{S} c_y c_yᵀ` with `c_y = wcol K θ y`.  From `Ttil_col_all`, `TtilT_col_all` and the
abstract `telescope` lemma; the boundary terms vanish since `l(1) = r(0) = l(S+1) = 0` and
`c_{S+1} ∈ range WY`.
-/

@[expose] public section

open Finset Matrix Polynomial

namespace CatalanCore.Star.Leonard

variable {F : Type*} [Field F]

theorem comm_N_mem [CharZero F] (m n S : ℕ) (hm : 1 ≤ m) (θ : F) (hθ : Gen θ)
    (x : Fin (m + n) → F) (hx : (Wb (m + n) θ (bX m (S : ℤ)))ᵀ *ᵥ x = 0) :
    (Nsum (fun y : ℕ => wcol (m + n) θ (y : ℤ)) S *ᵥ (Ttil (m + n) m S θ *ᵥ x)
        - Ttil (m + n) m S θ *ᵥ (Nsum (fun y : ℕ => wcol (m + n) θ (y : ℤ)) S *ᵥ x)) ∈
      CatalanCore.Wsp (Wb (m + n) θ (bY m (S : ℤ))) := by
  set T := Ttil (m + n) m S θ with hT
  set WY := Wb (m + n) θ (bY m (S : ℤ)) with hWY
  set WX := Wb (m + n) θ (bX m (S : ℤ)) with hWX
  set c : ℕ → Fin (m + n) → F := fun y => wcol (m + n) θ (y : ℤ) with hc
  set l : ℕ → F := fun y => -tau (m + n) m S θ (-θ - ((y : ℤ) : F)) with hl
  set d : ℕ → F := fun y => (Dz (m + n) m (S : F) θ (gg (m + n) m S)
    (cc0 (m + n) m θ (gg (m + n) m S))).eval (-((y : ℤ) : F)) with hd
  set r : ℕ → F := fun y => (bP (m + n) m (S : F) θ).eval (-((y : ℤ) : F) - 1) /
    (Qh m (S : F)).eval (-((y : ℤ) : F) - 1) with hr
  have hwY : ∀ (j : ℕ) (hj : j < m), wcol (m + n) θ ((S + 2 * j + 1 : ℕ) : ℤ) =
      fun a => WY a ⟨j, hj⟩ := by
    intro j hj; funext a; simp [hWY, Wb, bY, wcol]; ring_nf
  have hwX : ∀ (j : ℕ) (hj : j < m), wcol (m + n) θ ((S + 2 * j + 2 : ℕ) : ℤ) =
      fun a => WX a ⟨j, hj⟩ := by
    intro j hj; funext a; simp [hWX, Wb, bX, wcol]; ring_nf
  have hdotX : ∀ (j : ℕ) (hj : j < m), wcol (m + n) θ ((S + 2 * j + 2 : ℕ) : ℤ) ⬝ᵥ x = 0 := by
    intro j hj
    rw [hwX j hj]
    have := congrFun hx ⟨j, hj⟩
    simpa [Matrix.mulVec, dotProduct] using this
  have hmemY : ∀ (κ : ℕ → F), (∑ j ∈ Finset.range m,
      κ j • wcol (m + n) θ ((S + 2 * j + 1 : ℕ) : ℤ)) ∈ CatalanCore.Wsp WY := by
    intro κ
    refine Submodule.sum_mem _ fun j hj => Submodule.smul_mem _ _ ?_
    have := Finset.mem_range.1 hj
    rw [hwY j this]; exact col_mem_Wsp WY ⟨j, this⟩
  have hl1 : l 1 = 0 := by
    simp only [hl]
    have hp : pp (m + n) θ (-θ - (((1 : ℕ) : ℤ) : F)) = 0 := by
      unfold pp; push_cast; ring
    have : tau (m + n) m S θ (-θ - (((1 : ℕ) : ℤ) : F)) = 0 := by
      unfold tau; rw [hp]; simp
    rw [this]; simp
  have hr0 : r 0 = 0 := by
    simp only [hr]
    have : (bP (m + n) m (S : F) θ).eval (-(((0 : ℕ) : ℤ) : F) - 1) = 0 := by
      have hp : (pz (m + n) θ).eval (-(((0 : ℕ) : ℤ) : F) - 1) = 0 := by
        unfold pz; simp only [eval_mul, eval_lin]; push_cast; ring
      unfold bP
      simp only [eval_neg, eval_mul]
      rw [hp]; ring
    rw [this]; simp
  have hcprev : ∀ y : ℕ, 1 ≤ y → c (y - 1) = wcol (m + n) θ ((y : ℤ) - 1) := by
    intro y h1; simp only [hc]; congr 1; omega
  have hcnext : ∀ y : ℕ, c (y + 1) = wcol (m + n) θ ((y : ℤ) + 1) := by
    intro y; simp only [hc, Nat.cast_add, Nat.cast_one]
  have hCC : ∀ y, 1 ≤ y → y ≤ S →
      T *ᵥ c y - l y • c (y - 1) - d y • c y - r y • c (y + 1) ∈ CatalanCore.Wsp WY := by
    intro y h1 h2
    obtain ⟨κ, h⟩ := Ttil_col_all (m + n) m S hm θ hθ y h2
    have h' : T *ᵥ c y = l y • c (y - 1) + d y • c y + r y • c (y + 1)
        + ∑ j ∈ Finset.range m, κ j • wcol (m + n) θ ((S + 2 * j + 1 : ℕ) : ℤ) := by
      rw [hcprev y h1, hcnext y]; exact h
    have : l y • c (y - 1) + d y • c y + r y • c (y + 1)
        + ∑ j ∈ Finset.range m, κ j • wcol (m + n) θ ((S + 2 * j + 1 : ℕ) : ℤ)
        - l y • c (y - 1) - d y • c y - r y • c (y + 1) =
        ∑ j ∈ Finset.range m, κ j • wcol (m + n) θ ((S + 2 * j + 1 : ℕ) : ℤ) := by abel
    rw [h', this]; exact hmemY κ
  have hRC : ∀ y, 1 ≤ y → y ≤ S → (Tᵀ *ᵥ c y) ⬝ᵥ x =
      r (y - 1) * (c (y - 1) ⬝ᵥ x) + d y * (c y ⬝ᵥ x) + l (y + 1) * (c (y + 1) ⬝ᵥ x) := by
    intro y h1 h2
    obtain ⟨κ, h⟩ := TtilT_col_all (m + n) m S hm θ hθ y h2
    have hrr : r (y - 1) = -sigma (m + n) m S θ (-θ - ((y : ℤ) : F)) := by
      have := res_r (m + n) m S hm θ (((y - 1 : ℕ)) : ℤ) (by omega)
      simp only [hr]; rw [this]
      congr 2
      push_cast [Nat.cast_sub h1]; ring
    have hll : l (y + 1) = -tau (m + n) m S θ (-θ - ((y : ℤ) : F) - 1) := by
      simp only [hl]; congr 2; push_cast; ring
    have h' : Tᵀ *ᵥ c y = (-sigma (m + n) m S θ (-θ - ((y : ℤ) : F))) • c (y - 1) + d y • c y
        + (-tau (m + n) m S θ (-θ - ((y : ℤ) : F) - 1)) • c (y + 1)
        + ∑ j ∈ Finset.range m, κ j • wcol (m + n) θ ((S + 2 * j + 2 : ℕ) : ℤ) := by
      rw [hcprev y h1, hcnext y]; exact h
    have hsum : (∑ j ∈ Finset.range m, κ j • wcol (m + n) θ ((S + 2 * j + 2 : ℕ) : ℤ)) ⬝ᵥ x = 0 := by
      have e : (∑ j ∈ Finset.range m, κ j • wcol (m + n) θ ((S + 2 * j + 2 : ℕ) : ℤ)) ⬝ᵥ x =
          ∑ j ∈ Finset.range m, κ j * (wcol (m + n) θ ((S + 2 * j + 2 : ℕ) : ℤ) ⬝ᵥ x) := by
        simp only [dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul,
          Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
      rw [e]
      exact Finset.sum_eq_zero fun j hj => by rw [hdotX j (Finset.mem_range.1 hj), mul_zero]
    rw [h', add_dotProduct, add_dotProduct, add_dotProduct, hsum, smul_dotProduct, smul_dotProduct,
      smul_dotProduct, hrr, hll]
    simp only [smul_eq_mul, add_zero]
  have key := telescope c T l d r (CatalanCore.Wsp WY) x hl1 hr0 S hCC hRC
  have hlS : l (S + 1) = 0 := by
    have h0 := tau_border (m + n) m S θ 0 hm
    simp only [hl]
    have : tau (m + n) m S θ (-θ - (((S + 1 : ℕ) : ℤ) : F)) = 0 := by
      convert h0 using 2; push_cast; ring
    rw [this]; simp
  have hcS1 : c (S + 1) ∈ CatalanCore.Wsp WY := by
    have := hwY 0 hm
    have e : c (S + 1) = wcol (m + n) θ ((S + 2 * 0 + 1 : ℕ) : ℤ) := by
      simp only [hc]
    rw [e, this]; exact col_mem_Wsp WY ⟨0, hm⟩
  rw [hlS, zero_mul, zero_smul, zero_sub] at key
  have hB : (r S * (c S ⬝ᵥ x)) • c (S + 1) ∈ CatalanCore.Wsp WY := Submodule.smul_mem _ _ hcS1
  have := Submodule.sub_mem _ key hB
  simpa using this

end CatalanCore.Star.Leonard
