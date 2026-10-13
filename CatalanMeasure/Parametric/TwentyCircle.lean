module
public import CatalanMeasure.QuadCircle
public import Mathlib.Analysis.Complex.ExponentialBounds
@[expose] public section
namespace CatalanMeasure.Parametric.TwentyCircle
noncomputable section
def twentyRadius : ℚ := 1001 / 1000
@[irreducible] def twentyCircleK : ℚ := 10^14
def twentyCirclePieces : List (ℚ × ℚ × ℚ) := [((1 / 1000 : ℚ), (1001 / 1000 : ℚ), (173435983 / 100000000 : ℚ)),
  ((1001 / 1000 : ℚ), (1501 / 1000 : ℚ), (229346987 / 100000000 : ℚ)),
  ((1501 / 1000 : ℚ), (813 / 500 : ℚ), (60730599 / 25000000 : ℚ)),
  ((813 / 500 : ℚ), (3377 / 2000 : ℚ), (49933597 / 20000000 : ℚ)),
  ((3377 / 2000 : ℚ), (1751 / 1000 : ℚ), (32048557 / 12500000 : ℚ)),
  ((1751 / 1000 : ℚ), (7129 / 4000 : ℚ), (259739881 / 100000000 : ℚ)),
  ((7129 / 4000 : ℚ), (14383 / 8000 : ℚ), (26141349 / 10000000 : ℚ)),
  ((14383 / 8000 : ℚ), (3627 / 2000 : ℚ), (263085733 / 100000000 : ℚ)),
  ((3627 / 2000 : ℚ), (14633 / 8000 : ℚ), (132378317 / 50000000 : ℚ)),
  ((14633 / 8000 : ℚ), (7379 / 4000 : ℚ), (13321311 / 5000000 : ℚ)),
  ((7379 / 4000 : ℚ), (14883 / 8000 : ℚ), (53618903 / 20000000 : ℚ)),
  ((14883 / 8000 : ℚ), (469 / 250 : ℚ), (269761543 / 100000000 : ℚ)),
  ((469 / 250 : ℚ), (7629 / 4000 : ℚ), (273091891 / 100000000 : ℚ)),
  ((7629 / 4000 : ℚ), (3877 / 2000 : ℚ), (276417443 / 100000000 : ℚ)),
  ((3877 / 2000 : ℚ), (2001 / 1000 : ℚ), (70763709 / 25000000 : ℚ))]
def twentyCirclePieceOK (p : ℚ × ℚ × ℚ) : Bool :=
  decide (0 ≤ p.1) && decide (p.1 ≤ p.2.1) && decide (p.2.1 ≤ twentyRadius+1) &&
  decide (0 ≤ p.2.2) && decide ((twentyRadius+p.2.1)^2-1 ≤ p.2.2^2) &&
  decide ((twentyRadius+p.2.1+p.2.2)^18 *
    (2*(twentyRadius^2+1)-p.1^2)^1 * twentyRadius^4 ≤ twentyCircleK)
def twentyCircleCovers : ℚ → List (ℚ × ℚ × ℚ) → Bool
  | c, [] => decide (c = twentyRadius+1)
  | c, p::l => decide (p.1=c) && twentyCirclePieceOK p && twentyCircleCovers p.2.1 l

theorem twentyCircle_endpoint :
    ((twentyRadius:ℝ)+(twentyRadius+1)+
      Real.sqrt (((twentyRadius:ℝ)+(twentyRadius+1))^2-1))^18 *
      (2*((twentyRadius:ℝ)^2+1)-(twentyRadius+1)^2)^1 *
      (twentyRadius:ℝ)^4 ≤ (twentyCircleK:ℝ) := by
  have hs : Real.sqrt (((twentyRadius:ℝ)+(twentyRadius+1))^2-1) ≤ 3 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num [twentyRadius]
  have hr0 : 0 ≤ (twentyRadius:ℝ) :=by norm_num [twentyRadius]
  have hraw : 0 ≤ 2*((twentyRadius:ℝ)^2+1)-(twentyRadius+1)^2 :=by
    norm_num [twentyRadius]
  have hbase0 : 0 ≤ (twentyRadius:ℝ)+(twentyRadius+1)+
      Real.sqrt (((twentyRadius:ℝ)+(twentyRadius+1))^2-1) :=by positivity
  have hbase : (twentyRadius:ℝ)+(twentyRadius+1)+
      Real.sqrt (((twentyRadius:ℝ)+(twentyRadius+1))^2-1) ≤
      (twentyRadius:ℝ)+(twentyRadius+1)+3 :=by linarith only [hs]
  calc _ ≤ ((twentyRadius:ℝ)+(twentyRadius+1)+3)^18 *
      (2*((twentyRadius:ℝ)^2+1)-(twentyRadius+1)^2)^1 *
      (twentyRadius:ℝ)^4 := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hbase0 hbase 18)
            (pow_nonneg hraw 1)) (pow_nonneg hr0 4)
    _ ≤ (twentyCircleK:ℝ) := by norm_num [twentyRadius,twentyCircleK]

theorem twentyCircleCovers_spec {c : ℚ} {l : List (ℚ × ℚ × ℚ)}
    (h : twentyCircleCovers c l = true) {s : ℝ}
    (hs : (c:ℝ) ≤ s) (hs2 : s ≤ (twentyRadius:ℝ)+1) :
    ((twentyRadius:ℝ)+s+Real.sqrt (((twentyRadius:ℝ)+s)^2-1))^18 *
      (2*((twentyRadius:ℝ)^2+1)-s^2)^1 * (twentyRadius:ℝ)^4 ≤
      (twentyCircleK:ℝ) := by
  induction l generalizing c with
  | nil =>
    simp only [twentyCircleCovers,decide_eq_true_eq] at h
    subst h
    have he : s = (twentyRadius:ℝ)+1 := by
      push_cast at hs
      linarith
    rw [he]
    exact twentyCircle_endpoint
  | cons p l ih =>
    simp only [twentyCircleCovers,twentyCirclePieceOK,Bool.and_eq_true,decide_eq_true_eq] at h
    obtain ⟨⟨hc,⟨⟨⟨⟨⟨h0,h01⟩,h12⟩,hu0⟩,hu⟩,hK⟩⟩,hrest⟩ := h
    subst hc
    by_cases hs1 : s ≤ p.2.1
    · have hs0 : 0 ≤ s := le_trans (by exact_mod_cast h0) hs
      have hr0 : (0:ℝ) ≤ twentyRadius := by norm_num [twentyRadius]
      have hp0 : (0:ℝ) ≤ p.1 := by exact_mod_cast h0
      have hsq : Real.sqrt (((twentyRadius:ℝ)+s)^2-1) ≤ p.2.2 := by
        rw [Real.sqrt_le_left (by exact_mod_cast hu0)]
        have hh : ((twentyRadius:ℝ)+(p.2.1:ℝ))^2-1 ≤ (p.2.2:ℝ)^2 := by exact_mod_cast hu
        nlinarith
      have hA : (twentyRadius:ℝ)+s+Real.sqrt (((twentyRadius:ℝ)+s)^2-1) ≤
          (twentyRadius:ℝ)+p.2.1+p.2.2 := by linarith
      have hB : (2*((twentyRadius:ℝ)^2+1)-s^2)^1 ≤
          (2*((twentyRadius:ℝ)^2+1)-(p.1:ℝ)^2)^1 := by
        apply pow_le_pow_left₀
        · have hsend := hs2
          norm_num [twentyRadius] at hsend ⊢
          nlinarith
        · nlinarith
      have hK' : ((twentyRadius:ℝ)+(p.2.1:ℝ)+p.2.2)^18 *
          (2*((twentyRadius:ℝ)^2+1)-(p.1:ℝ)^2)^1 *
          (twentyRadius:ℝ)^4 ≤ (twentyCircleK:ℝ) := by exact_mod_cast hK
      calc _ ≤ ((twentyRadius:ℝ)+(p.2.1:ℝ)+p.2.2)^18 *
          (2*((twentyRadius:ℝ)^2+1)-(p.1:ℝ)^2)^1 * (twentyRadius:ℝ)^4 := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            apply mul_le_mul
            · exact pow_le_pow_left₀ (by positivity) hA 18
            · exact hB
            · have hss : s^2 ≤ ((twentyRadius:ℝ)+1)^2 :=pow_le_pow_left₀ hs0 hs2 2
              simp only [pow_one]
              nlinarith only [hss,sq_nonneg ((twentyRadius:ℝ)-1)]
            · have hp1 : (0:ℝ) ≤ p.2.1 := le_trans hs0 hs1
              have hp2 : (0:ℝ) ≤ p.2.2 := by exact_mod_cast hu0
              positivity
        _ ≤ (twentyCircleK:ℝ) := hK'
    · exact ih hrest (le_of_lt (not_le.mp hs1))

set_option maxRecDepth 4000 in
set_option maxHeartbeats 800000 in
theorem twentyCircleCovers_true :
    twentyCircleCovers (twentyRadius-1) twentyCirclePieces = true := by decide +kernel

/-- Exact uniform radius certificate for the restricted 18N-dimensional row space. -/
theorem twentyCircle_ineq {s : ℝ} (hs0 : (twentyRadius:ℝ)-1 ≤ s)
    (hs2 : s ≤ (twentyRadius:ℝ)+1) :
    ((twentyRadius:ℝ)+s+Real.sqrt (((twentyRadius:ℝ)+s)^2-1))^18 *
      (2*((twentyRadius:ℝ)^2+1)-s^2)^1 * (twentyRadius:ℝ)^4 ≤
      (twentyCircleK:ℝ) :=
  twentyCircleCovers_spec twentyCircleCovers_true (by simpa using hs0) hs2

theorem twentyCircleK_le_exp : (twentyCircleK:ℝ) ≤ Real.exp 33 := by
  have he : (2.7182818283:ℝ) ≤ Real.exp 1 := Real.exp_one_gt_d9.le
  rw [show (33:ℝ) = (33:ℕ)*1 by norm_num,Real.exp_nat_mul]
  calc (twentyCircleK:ℝ) ≤ (2.7182818283:ℝ)^33 := by norm_num [twentyCircleK]
    _ ≤ Real.exp 1 ^33 := pow_le_pow_left₀ (by norm_num) he 33
end
end CatalanMeasure.Parametric.TwentyCircle
