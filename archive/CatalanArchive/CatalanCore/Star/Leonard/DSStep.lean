module

public import CatalanCore.Star.Leonard.DSRatio
public import CatalanCore.Star.Leonard.HD2

/-!
# The diagonal step as a ratio (package H7, (B1))

`uu m n S θ = u(Ã_{θ,S}, Π c_S)`.  For `n ≤ S`, `θ > 0` generic:

`uu m n (S+1) (θ-1) = uu m n S θ · (dsK m n S · Tp1 (m+n) θ n)`,

`Tp1 K θ n = ∏_{j<n} ((θ+K-1-j)/(θ+j))^{2(n-1-j)}` (support `c ≥ 0`), `dsK` a `θ`-free product of integers.
-/

@[expose] public section

open Finset Matrix

namespace CatalanCore.Star.Leonard

noncomputable def uu (m n S : ℕ) (θ : ℚ) : ℚ :=
  CatalanCore.bkdet (Wb (m + n) θ (bY m (S : ℤ))) (Atil m n S θ)
    (projB (m + n) θ (bX m (S : ℤ)) (bY m (S : ℤ)) *ᵥ wcol (m + n) θ (S : ℤ))

lemma uu_shift (m n S : ℕ) (θ : ℚ) :
    uu m n (S + 1) (θ - 1) =
      CatalanCore.bkdet (Wb (m + n) θ (bY m (S : ℤ))) (Atil m n (S + 1) (θ - 1))
        (projB (m + n) θ (bX m (S : ℤ)) (bY m (S : ℤ)) *ᵥ wcol (m + n) θ (S : ℤ)) := by
  unfold uu
  rw [Wb_shift_Y, projB_shift, wcol_shift_nat]

lemma gen_sub_one {θ : ℚ} (h : Gen θ) : Gen (θ - 1) := by
  intro z; have := h (z - 1); push_cast at this; intro h'; apply this; linear_combination h'

/-- the `θ`-free constant of the diagonal step -/
noncomputable def dsK (m n S : ℕ) : ℚ :=
  (dnC m S (m + n) n 0 * dnC m (S + 1) (m + n) n ((S + 1 : ℕ) : ℤ) *
    cnum (Fin.addCases (fun i : Fin m => ((bY m (S : ℤ) i : ℤ) : ℚ))
      (fun j : Fin n => ((((0 : ℤ) - ((j : ℕ) : ℤ) : ℤ)) : ℚ)) : Fin (m + n) → ℚ) *
    cnum (Fin.addCases (fun i : Fin m => ((bY m ((S + 1 : ℕ) : ℤ) i : ℤ) : ℚ))
      (fun j : Fin n => (((((S + 1 : ℕ) : ℤ) - ((j : ℕ) : ℤ) : ℤ)) : ℚ)) : Fin (m + n) → ℚ)) /
  (dnC m S (m + n) n (S : ℤ) * upC m (S + 1) (m + n) n 1 *
    cnum (Fin.addCases (fun i : Fin m => ((bY m (S : ℤ) i : ℤ) : ℚ))
      (fun j : Fin n => ((((S : ℤ) - ((j : ℕ) : ℤ) : ℤ)) : ℚ)) : Fin (m + n) → ℚ) *
    cnum (Fin.addCases (fun i : Fin m => ((bY m ((S + 1 : ℕ) : ℤ) i : ℤ) : ℚ))
      (fun j : Fin n => ((((1 : ℤ) + ((j : ℕ) : ℤ) : ℤ)) : ℚ)) : Fin (m + n) → ℚ))

lemma fin_prod_range2 (K n : ℕ) (f : ℕ → ℕ → ℚ) :
    ∏ i : Fin K, ∏ j : Fin n, f i j = ∏ i ∈ range K, ∏ j ∈ range n, f i j := by
  rw [Fin.prod_univ_eq_prod_range (fun i => ∏ j : Fin n, f i j) K]
  exact Finset.prod_congr rfl fun i _ => Fin.prod_univ_eq_prod_range (fun j => f i j) n

theorem ds_step (m n S : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) (hS : n ≤ S) (θ : ℚ) (hθ0 : 0 < θ)
    (hθ : Gen θ) :
    uu m n (S + 1) (θ - 1) = uu m n S θ * (dsK m n S * Tp1 ((m + n : ℕ)) θ n) := by
  have hθ' := gen_sub_one hθ
  have hΔ : IsUnit ((Wb (m + n) θ (bX m (S : ℤ)))ᵀ * Wb (m + n) θ (bY m (S : ℤ))).det :=
    isUnit_iff_ne_zero.2 (Delta_ne_pos (m + n) m S (by omega) θ hθ0)
  have E := ds_explicit m n S hm θ hθ hθ' hΔ hS hn
  rw [← uu_shift] at E
  have h0 : lprodDown m n S θ 0 * cauFac θ (Fin.addCases (fun i : Fin m => ((bY m (S : ℤ) i : ℤ) : ℚ))
      (fun j : Fin n => ((((0 : ℤ) - ((j : ℕ) : ℤ) : ℤ)) : ℚ)) : Fin (m + n) → ℚ) ≠ 0 := by
    have := u_down_0_ne m n S hm θ hθ hΔ hS hn
    rw [u_down_0 m n S hm θ hθ hΔ hS hn] at this; exact this
  have h1 : lprodDown m n (S + 1) (θ - 1) ((S + 1 : ℕ) : ℤ) *
      cauFac (θ - 1) (Fin.addCases (fun i : Fin m => ((bY m ((S + 1 : ℕ) : ℤ) i : ℤ) : ℚ))
        (fun j : Fin n => (((((S + 1 : ℕ) : ℤ) - ((j : ℕ) : ℤ) : ℤ)) : ℚ)) : Fin (m + n) → ℚ) ≠ 0 := by
    have := u_down_shift_ne m n S hm θ hθ' hΔ hS
    rw [u_down_shift_eq m n S hm θ hθ' hΔ hS] at this; exact this
  have h2 : lprodDown m n S θ (S : ℤ) * cauFac θ (Fin.addCases (fun i : Fin m => ((bY m (S : ℤ) i : ℤ) : ℚ))
      (fun j : Fin n => ((((S : ℤ) - ((j : ℕ) : ℤ) : ℤ)) : ℚ)) : Fin (m + n) → ℚ) ≠ 0 := by
    have := u_down_S_ne m n S hm θ hθ hΔ hS
    rw [u_down_S m n S hm θ hθ hΔ hS] at this; exact this
  have h3 : lprodUp m n (S + 1) (θ - 1) 1 *
      cauFac (θ - 1) (Fin.addCases (fun i : Fin m => ((bY m ((S + 1 : ℕ) : ℤ) i : ℤ) : ℚ))
        (fun j : Fin n => ((((1 : ℤ) + ((j : ℕ) : ℤ) : ℤ)) : ℚ)) : Fin (m + n) → ℚ) ≠ 0 := by
    have := u_up_shift_ne m n S hm θ hθ' hΔ hS
    rw [u_up_shift_eq m n S hm θ hθ' hΔ hS] at this; exact this
  have hu : uu m n S θ = CatalanCore.bkdet (Wb (m + n) θ (bY m (S : ℤ))) (Atil m n S θ)
      (projB (m + n) θ (bX m (S : ℤ)) (bY m (S : ℤ)) *ᵥ wcol (m + n) θ (S : ℤ)) := rfl
  rw [← hu] at E
  have hT0 : dnT (m + n) n θ 0 = Lp1 (m + n) θ n := by
    unfold dnT Lp1
    refine Finset.prod_congr rfl fun k _ => Finset.prod_congr rfl fun j _ => ?_
    push_cast; ring
  have hTSp : dnT (m + n) n (θ - 1) (((S + 1 : ℕ) : ℤ)) = dnT (m + n) n θ (S : ℤ) := by
    unfold dnT
    refine Finset.prod_congr rfl fun k _ => Finset.prod_congr rfl fun j _ => ?_
    push_cast; ring
  have hU1 : upT (m + n) n (θ - 1) 1 = Mp1 (m + n) θ n := by
    unfold upT Mp1
    refine Finset.prod_congr rfl fun k _ => Finset.prod_congr rfl fun j _ => ?_
    push_cast; ring
  have hDY : (∏ i : Fin (m + n), ∏ l : Fin m,
      (θ - 1 + ((i : ℕ) : ℚ) + ((bY m (((S + 1 : ℕ)) : ℤ) l : ℤ) : ℚ))) =
      ∏ i : Fin (m + n), ∏ l : Fin m, (θ + ((i : ℕ) : ℚ) + ((bY m (S : ℤ) l : ℤ) : ℚ)) := by
    refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun l _ => ?_
    simp only [bY]; push_cast; ring
  have hDS : (∏ i : Fin (m + n), ∏ j : Fin n,
      (θ - 1 + ((i : ℕ) : ℚ) + (((((S + 1 : ℕ) : ℤ) - ((j : ℕ) : ℤ) : ℤ)) : ℚ))) =
      ∏ i : Fin (m + n), ∏ j : Fin n, (θ + ((i : ℕ) : ℚ) + ((((S : ℤ) - ((j : ℕ) : ℤ) : ℤ)) : ℚ)) := by
    refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
    push_cast; ring
  have hPh : Ph1 (m + n) θ n =
      (∏ i : Fin (m + n), ∏ j : Fin n,
        (θ - 1 + ((i : ℕ) : ℚ) + ((((1 : ℤ) + ((j : ℕ) : ℤ) : ℤ)) : ℚ))) /
      (∏ i : Fin (m + n), ∏ j : Fin n, (θ + ((i : ℕ) : ℚ) + ((((0 : ℤ) - ((j : ℕ) : ℤ) : ℤ)) : ℚ))) := by
    rw [fin_prod_range2 (m + n) n (fun i j => θ - 1 + (i : ℚ) + (((1 : ℤ) + (j : ℤ) : ℤ) : ℚ)),
      fin_prod_range2 (m + n) n (fun i j => θ + (i : ℚ) + (((0 : ℤ) - (j : ℤ) : ℤ) : ℚ)),
      ← Finset.prod_div_distrib]
    unfold Ph1
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    push_cast; ring_nf
  simp only [lprodDown_eq, lprodUp_eq, cauFac_split, hT0, hTSp, hU1, hDY, hDS] at E h0 h1 h2 h3
  rw [← Id1 (m + n) θ hθ0 hθ n, hPh]
  unfold dsK
  simp only [ne_eq, mul_eq_zero, div_eq_zero_iff, not_or] at h0 h1 h2 h3
  obtain ⟨⟨hdc0, hLp⟩, hcn0, hDY0, hDc0⟩ := h0
  obtain ⟨⟨hdcSp, hTS⟩, hcnSp, -, hDS0⟩ := h1
  obtain ⟨⟨hdcS, -⟩, hcnS, -, -⟩ := h2
  obtain ⟨⟨hupC, hMp⟩, hcn1, -, hDc1⟩ := h3
  have key : ∀ (u u' P0 P1 P2 P3 K' : ℚ), u * P0 * P1 = u' * P2 * P3 → P2 * P3 ≠ 0 →
      P0 * P1 = K' * (P2 * P3) → u' = u * K' := by
    intro u u' P0 P1 P2 P3 K' hE hne hK
    apply mul_right_cancel₀ hne
    calc u' * (P2 * P3) = u * P0 * P1 := by rw [← mul_assoc]; exact hE.symm
      _ = u * (P0 * P1) := by ring
      _ = u * K' * (P2 * P3) := by rw [hK]; ring
  refine key _ _ _ _ _ _ _ E ?_ ?_
  · exact mul_ne_zero (mul_ne_zero (mul_ne_zero hdcS hTS) (div_ne_zero hcnS (mul_ne_zero hDY0 hDS0)))
      (mul_ne_zero (mul_ne_zero hupC hMp) (div_ne_zero hcn1 (mul_ne_zero hDY0 hDc1)))
  · field_simp

end CatalanCore.Star.Leonard
