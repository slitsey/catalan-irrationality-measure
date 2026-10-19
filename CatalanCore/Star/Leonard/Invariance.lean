module

public import CatalanCore.Star.Leonard.RCY
public import CatalanCore.Linalg.KrylovV

/-!
# (T1), (T2): `T~` preserves `range W_Y` and `ker W_Xᵀ` (package H2 consequences)

For `K = m + n`; `WY = Wb K θ (bY m S)`, `WX = Wb K θ (bX m S)`.
-/

@[expose] public section

open Finset Matrix Polynomial

namespace CatalanCore.Star.Leonard

variable {F : Type*} [Field F]

lemma mulVec_eq_sum_cols {r c : ℕ} (W : Matrix (Fin r) (Fin c) F) (v : Fin c → F) :
    W *ᵥ v = ∑ i : Fin c, v i • (fun a => W a i) := by
  ext a; simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]

lemma col_mem_Wsp {r c : ℕ} (W : Matrix (Fin r) (Fin c) F) (i : Fin c) :
    (fun a => W a i) ∈ LinearMap.range (Matrix.mulVecLin W) :=
  ⟨Pi.single i 1, by ext a; simp [Matrix.mulVec, dotProduct, Pi.single_apply]⟩

/-- **(T2).**  `T~` preserves `span WY`. -/
theorem Ttil_preserves_WY [CharZero F] (m n S : ℕ) (hm : 1 ≤ m) (θ : F) (hθ : Gen θ) :
    ∀ x ∈ CatalanCore.Wsp (Wb (m + n) θ (bY m (S : ℤ))),
      Ttil (m + n) m S θ *ᵥ x ∈ CatalanCore.Wsp (Wb (m + n) θ (bY m (S : ℤ))) := by
  set W := Wb (m + n) θ (bY m (S : ℤ)) with hW
  have hwc : ∀ (i : ℕ) (hi : i < m), wcol (m + n) θ ((S + 2 * i + 1 : ℕ) : ℤ) = fun a => W a ⟨i, hi⟩ := by
    intro i hi; funext a; simp [hW, Wb, bY, wcol]; ring_nf
  have hcol : ∀ i : Fin m, Ttil (m + n) m S θ *ᵥ (fun a => W a i) ∈ CatalanCore.Wsp W := by
    intro i
    obtain ⟨d, κ, h⟩ := Ttil_colY (m + n) m S hm θ hθ i i.2
    have hc : (fun a => W a i) = wcol (m + n) θ ((S + 2 * (i : ℕ) + 1 : ℕ) : ℤ) := by
      rw [hwc i i.2]
    rw [hc, h]
    refine Submodule.add_mem _ (Submodule.smul_mem _ _ ?_) (Submodule.sum_mem _ fun i' hi' => ?_)
    · rw [← hc]; exact col_mem_Wsp W i
    · refine Submodule.smul_mem _ _ ?_
      have := Finset.mem_range.1 hi'
      rw [hwc i' this]; exact col_mem_Wsp W ⟨i', this⟩
  intro x hx
  obtain ⟨c, rfl⟩ := hx
  change Ttil (m + n) m S θ *ᵥ (W *ᵥ c) ∈ _
  rw [mulVec_eq_sum_cols W c, Matrix.mulVec_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [Matrix.mulVec_smul]
  exact Submodule.smul_mem _ _ (hcol i)


/-- **(T1).**  `T~` preserves `ker W_Xᵀ`. -/
theorem Ttil_preserves_ker_WX [CharZero F] (m n S : ℕ) (hm : 1 ≤ m) (θ : F) (hθ : Gen θ) :
    ∀ x : Fin (m + n) → F, (Wb (m + n) θ (bX m (S : ℤ)))ᵀ *ᵥ x = 0 →
      (Wb (m + n) θ (bX m (S : ℤ)))ᵀ *ᵥ (Ttil (m + n) m S θ *ᵥ x) = 0 := by
  set W := Wb (m + n) θ (bX m (S : ℤ)) with hW
  have hwc : ∀ (i : ℕ) (hi : i < m), wcol (m + n) θ ((S + 2 * i + 2 : ℕ) : ℤ) = fun a => W a ⟨i, hi⟩ := by
    intro i hi; funext a; simp [hW, Wb, bX, wcol]; ring_nf
  have hdot : ∀ (y : Fin (m + n) → F) (i : Fin m), (Wᵀ *ᵥ y) i = (fun a => W a i) ⬝ᵥ y := by
    intro y i; simp [Matrix.mulVec, dotProduct]
  intro x hx
  ext i
  rw [hdot, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
  obtain ⟨d, κ, h⟩ := TtilT_colY (m + n) m S hm θ hθ i i.2
  have hc : (fun a => W a i) = wcol (m + n) θ ((S + 2 * (i : ℕ) + 2 : ℕ) : ℤ) := by
    rw [hwc i i.2]
  have h0 : ∀ i' : Fin m, (fun a => W a i') ⬝ᵥ x = 0 := fun i' => by
    rw [← hdot, hx]; rfl
  have hsum : (∑ i' ∈ Finset.range m, κ i' • wcol (m + n) θ ((S + 2 * i' + 2 : ℕ) : ℤ)) ⬝ᵥ x =
      ∑ i' ∈ Finset.range m, κ i' * (wcol (m + n) θ ((S + 2 * i' + 2 : ℕ) : ℤ) ⬝ᵥ x) := by
    simp only [dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [hc, h, add_dotProduct, smul_dotProduct, hsum, ← hc, h0 i, smul_zero, zero_add,
    Pi.zero_apply]
  refine Finset.sum_eq_zero fun i' hi' => ?_
  have := Finset.mem_range.1 hi'
  rw [hwc i' this, h0 ⟨i', this⟩, mul_zero]

end CatalanCore.Star.Leonard
