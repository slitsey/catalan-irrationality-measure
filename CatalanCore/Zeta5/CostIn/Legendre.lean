module

public import CatalanCore.Zeta5.Frames.Normalizer
public import CatalanCore.Zeta5.CostIn.Gamma

@[expose] public section

/-!
# ZC17 (third module): the Legendre sum `v_p(S_K)` against `p N₀(K/p)`

For `p² > 2K` (so only the first prime power occurs, `Local.SValuation.vS_eq_firstPower`):
`vSK_approx : 0 ≤ v_p(S_K) - p N₀(K/p) ≤ ⌊2h/p⌋`, `K = 40 n`, `h = 37 n`.
The floor sum `∑_{i<h} ⌊2i/p⌋` is compared with the layer function `layer p J h` of `Frames.ClassData`
from both sides (`sum_floor_le_layer` and the new `layer_le_sum_floor`: the defect is `½ #{i < h : p ∣ 2i+1}`).
-/

open Finset

namespace Apery.CostIn

section layerbound
variable {p : ℕ}

/-- One step of the layer function: the exact step is `⌊2i/p⌋` plus `1/2` when `p ∣ 2i+1`. -/
lemma layer_step_le (hp : 0 < p) (J i : ℕ) :
    layer p J ((i : ℝ) + 1) - layer p J i ≤
      ((2 * i / p : ℕ) : ℝ) + (if p ∣ 2 * i + 1 then 1 / 2 else 0) := by
  unfold layer
  rw [← Finset.sum_sub_distrib]
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have key : ∀ j ∈ Icc 1 J, max 0 ((i : ℝ) + 1 - j * p / 2) - max 0 ((i : ℝ) - j * p / 2) ≤
      (if j * p ≤ 2 * i then (1 : ℝ) else 0) + (if j * p = 2 * i + 1 then 1 / 2 else 0) := by
    intro j _
    by_cases h1 : j * p ≤ 2 * i
    · have h1' : (j : ℝ) * p ≤ 2 * i := by exact_mod_cast h1
      rw [if_pos h1, if_neg (by omega), max_eq_right (by linarith), max_eq_right (by linarith)]
      linarith
    · by_cases h2 : j * p = 2 * i + 1
      · have h2' : (j : ℝ) * p = 2 * i + 1 := by exact_mod_cast h2
        rw [if_neg h1, if_pos h2, max_eq_left (by linarith : (i : ℝ) - j * p / 2 ≤ 0),
          max_eq_right (by linarith : 0 ≤ (i : ℝ) + 1 - j * p / 2)]
        linarith
      · have h3 : 2 * i + 2 ≤ j * p := by omega
        have h3' : (2 : ℝ) * i + 2 ≤ j * p := by exact_mod_cast h3
        rw [if_neg h1, if_neg h2, max_eq_left (by linarith), max_eq_left (by linarith)]
        norm_num
  refine (Finset.sum_le_sum key).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_boole, ← Finset.sum_filter]
  have hA : (((Icc 1 J).filter fun j => j * p ≤ 2 * i).card : ℝ) ≤ ((2 * i / p : ℕ) : ℝ) := by
    have : ((Icc 1 J).filter fun j => j * p ≤ 2 * i).card ≤ 2 * i / p := by
      calc _ ≤ (Icc 1 (2 * i / p)).card := by
            refine Finset.card_le_card fun j hj => ?_
            simp only [Finset.mem_filter, Finset.mem_Icc] at hj ⊢
            exact ⟨hj.1.1, (Nat.le_div_iff_mul_le hp).mpr hj.2⟩
        _ = 2 * i / p := by simp
    exact_mod_cast this
  have hB : ∑ j ∈ (Icc 1 J).filter (fun j => j * p = 2 * i + 1), (1 / 2 : ℝ) ≤
      (if p ∣ 2 * i + 1 then 1 / 2 else 0) := by
    rw [Finset.sum_const, nsmul_eq_mul]
    by_cases hd : p ∣ 2 * i + 1
    · rw [if_pos hd]
      have hc : ((Icc 1 J).filter fun j => j * p = 2 * i + 1).card ≤ 1 := by
        refine Finset.card_le_one.mpr fun a ha b hb => ?_
        simp only [Finset.mem_filter] at ha hb
        exact Nat.eq_of_mul_eq_mul_right hp (ha.2.trans hb.2.symm)
      have : (((Icc 1 J).filter fun j => j * p = 2 * i + 1).card : ℝ) ≤ 1 := by exact_mod_cast hc
      linarith
    · rw [if_neg hd]
      have : (Icc 1 J).filter (fun j => j * p = 2 * i + 1) = ∅ := by
        refine Finset.filter_eq_empty_iff.mpr fun j _ hj => hd ⟨j, by rw [← hj]; ring⟩
      rw [this]; simp
  linarith

lemma count_dvd_le (hp : 0 < p) (H : ℕ) :
    ((range H).filter fun i => p ∣ 2 * i + 1).card ≤ 2 * H / p := by
  induction H with
  | zero => simp
  | succ H ih =>
    rw [Finset.range_add_one, Finset.filter_insert]
    by_cases hd : p ∣ 2 * H + 1
    · rw [if_pos hd, Finset.card_insert_of_notMem (by simp)]
      obtain ⟨k, hk⟩ := hd
      have h1 : k ≤ (2 * (H + 1)) / p := (Nat.le_div_iff_mul_le hp).mpr (by nlinarith)
      have h2 : 2 * H / p < k := (Nat.div_lt_iff_lt_mul hp).mpr (by nlinarith)
      omega
    · rw [if_neg hd]
      have : 2 * H / p ≤ 2 * (H + 1) / p := Nat.div_le_div_right (by omega)
      omega

/-- The layer function exceeds the Legendre floor sum by at most `⌊2H/p⌋ / 2`. -/
lemma layer_le_sum_floor (hp : 0 < p) (J H : ℕ) :
    layer p J (H : ℝ) ≤ (∑ i ∈ range H, ((2 * i / p : ℕ) : ℝ)) + ((2 * H / p : ℕ) : ℝ) / 2 := by
  have h0 : layer p J 0 = 0 := by
    unfold layer
    refine Finset.sum_eq_zero fun j hj => ?_
    have := (Finset.mem_Icc.mp hj).1
    have : (0 : ℝ) ≤ j * p / 2 := by positivity
    exact max_eq_left (by linarith)
  have hmain : ∀ H : ℕ, layer p J (H : ℝ) ≤ (∑ i ∈ range H, ((2 * i / p : ℕ) : ℝ)) +
      (1 / 2 : ℝ) * (((range H).filter fun i => p ∣ 2 * i + 1).card : ℝ) := by
    intro H
    induction H with
    | zero => simp [h0]
    | succ H ih =>
      have hs := layer_step_le hp J H
      rw [Finset.sum_range_succ, Finset.range_add_one, Finset.filter_insert]
      push_cast
      by_cases hd : p ∣ 2 * H + 1
      · rw [if_pos hd] at hs ⊢
        rw [Finset.card_insert_of_notMem (by simp)]
        push_cast
        linarith
      · rw [if_neg hd] at hs ⊢
        linarith
  have := hmain H
  have hc : (((range H).filter fun i => p ∣ 2 * i + 1).card : ℝ) ≤ ((2 * H / p : ℕ) : ℝ) := by
    exact_mod_cast count_dvd_le hp H
  linarith

end layerbound


section vsk
variable {p : ℕ}

lemma sum_Icc_lin (m : ℕ) (h p : ℝ) :
    ∑ j ∈ Icc 1 m, (h - (j : ℝ) * p / 2) = m * h - p * m * (m + 1) / 4 := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_Icc_succ_top (by omega), ih]; push_cast; ring

lemma layer_closed (hp : 0 < p) (h : ℕ) :
    layer p (2 * h / p + 1) (h : ℝ) = ((2 * h / p : ℕ) : ℝ) * h
      - p * ((2 * h / p : ℕ) : ℝ) * (((2 * h / p : ℕ) : ℝ) + 1) / 4 := by
  obtain ⟨m, hm⟩ : ∃ m, m = 2 * h / p := ⟨_, rfl⟩
  rw [← hm]
  unfold layer
  rw [Finset.sum_Icc_succ_top (by omega)]
  have hlt : 2 * h < (m + 1) * p := by
    have := Nat.lt_mul_div_succ (2 * h) hp
    rw [← hm] at this
    nlinarith
  have hlast : max 0 ((h : ℝ) - ((m + 1 : ℕ) : ℝ) * p / 2) = 0 := by
    apply max_eq_left
    have : (2 : ℝ) * h < (m + 1) * p := by exact_mod_cast hlt
    push_cast; linarith
  rw [hlast, add_zero]
  have : ∀ j ∈ Icc 1 m, max 0 ((h : ℝ) - j * p / 2) = h - j * p / 2 := by
    intro j hj
    apply max_eq_right
    have h1 : j * p ≤ 2 * h := by
      have := (Nat.le_div_iff_mul_le hp).mp (hm ▸ (Finset.mem_Icc.mp hj).2)
      exact this
    have : (j : ℝ) * p ≤ 2 * h := by exact_mod_cast h1
    linarith
  rw [Finset.sum_congr rfl this, sum_Icc_lin]

lemma floor_nat_div (a p : ℕ) : ⌊(a : ℝ) / (p : ℝ)⌋ = ((a / p : ℕ) : ℤ) := by
  rw [Int.floor_div_natCast, Int.floor_natCast]
  exact (Int.natCast_div a p).symm

lemma sum_icc_eq_range (h : ℕ) (hh : 1 ≤ h) (f : ℕ → ℕ) (hf : f 0 = 0) :
    ∑ i ∈ Icc 1 (h - 1), f i = ∑ i ∈ range h, f i := by
  obtain ⟨k, rfl⟩ : ∃ k, h = k + 1 := ⟨h - 1, by omega⟩
  rw [Finset.sum_range_succ', hf, add_zero, Nat.add_sub_cancel]
  exact (sum_range_shift f k).symm

end vsk


/-- **The Legendre sum `v_p(S_K)` against `p N₀(K/p)`** (ZC16 to ZC17): for `p² > 2K`,
`0 ≤ v_p(S_K) - p N₀(K/p) ≤ ⌊2h/p⌋`, `K = 40 n`, `h = 37 n`. -/
theorem vSK_approx {n p : ℕ} (hp : p.Prime) (hn : 0 < n) (hp2 : 2 * (40 * n) < p ^ 2) :
    0 ≤ (vSK n p : ℝ) - p * N0 (((40 * n : ℕ) : ℝ) / (p : ℝ)) ∧
      (vSK n p : ℝ) - p * N0 (((40 * n : ℕ) : ℝ) / (p : ℝ)) ≤ ((2 * (37 * n) / p : ℕ) : ℝ) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp0 : 0 < p := hp.pos
  have hv := vS_eq_firstPower hn hp hp2
  have h4 : padicValNat p 4 = 0 := padicValNat.eq_zero_of_not_dvd (fun hd => by
    have := Nat.le_of_dvd (by norm_num) hd
    nlinarith [hp.two_le])
  have hA : ∑ i ∈ Icc 1 (37 * n - 1), (((2 * i) / p : ℕ) : ℤ) =
      ((∑ i ∈ range (37 * n), (2 * i / p : ℕ) : ℕ) : ℤ) := by
    rw [← Nat.cast_sum, sum_icc_eq_range (37 * n) (by omega) (fun i => 2 * i / p) (by simp)]
  have hvZ : vSK n p = 2 * (37 * n : ℤ) * (((40 * n) / p : ℕ) : ℤ)
      - 12 * (37 * n : ℤ) * (((3 * n) / p : ℕ) : ℤ)
      - 2 * ((∑ i ∈ range (37 * n), (2 * i / p : ℕ) : ℕ) : ℤ) := by
    unfold vSK
    rw [hv, hA, h4]; simp
  have hvR : (vSK n p : ℝ) = 2 * (37 * n) * (((40 * n) / p : ℕ) : ℝ)
      - 12 * (37 * n) * (((3 * n) / p : ℕ) : ℝ)
      - 2 * ∑ i ∈ range (37 * n), (((2 * i / p : ℕ)) : ℝ) := by
    have := congrArg (fun z : ℤ => (z : ℝ)) hvZ
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, Int.cast_ofNat] at this
    push_cast at this
    exact this
  -- the real side
  set Q : ℕ := 40 * n / p with hQ
  set qN : ℕ := 3 * n / p with hqN
  set m : ℕ := 2 * (37 * n) / p with hm
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp0
  have hx1 : ⌊((40 * n : ℕ) : ℝ) / (p : ℝ)⌋ = (Q : ℤ) := floor_nat_div (40 * n) p
  have hx2 : ⌊3 / 40 * (((40 * n : ℕ) : ℝ) / (p : ℝ))⌋ = (qN : ℤ) := by
    have : 3 / 40 * (((40 * n : ℕ) : ℝ) / (p : ℝ)) = ((3 * n : ℕ) : ℝ) / (p : ℝ) := by
      push_cast; field_simp
    rw [this]; exact floor_nat_div (3 * n) p
  have hx3 : ⌊2 * (37 / 40 * (((40 * n : ℕ) : ℝ) / (p : ℝ)))⌋ = (m : ℤ) := by
    have : 2 * (37 / 40 * (((40 * n : ℕ) : ℝ) / (p : ℝ))) = ((2 * (37 * n) : ℕ) : ℝ) / (p : ℝ) := by
      push_cast; field_simp
    rw [this]; exact floor_nat_div (2 * (37 * n)) p
  have hN0 : (p : ℝ) * N0 (((40 * n : ℕ) : ℝ) / (p : ℝ)) =
      2 * (37 * n) * (Q : ℝ) - 12 * (37 * n) * (qN : ℝ)
        - 2 * ((m : ℝ) * (37 * n) - p * m * (m + 1) / 4) := by
    unfold N0 Jf
    rw [hx1, hx2, hx3]
    push_cast
    field_simp
    ring
  have hlay := layer_closed hp0 (37 * n)
  have hJ : 2 * (37 * n) ≤ (m + 1) * p := by
    have := Nat.lt_mul_div_succ (2 * (37 * n)) hp0
    rw [← hm] at this
    nlinarith
  have hlow := sum_floor_le_layer (p := p) (m + 1) (37 * n) hJ
  have hup := layer_le_sum_floor hp0 (m + 1) (37 * n)
  rw [← hm] at hlay hup
  rw [hvR, hN0]
  push_cast at hlow hup hlay
  constructor <;> nlinarith [hlow, hup, hlay]

end Apery.CostIn
