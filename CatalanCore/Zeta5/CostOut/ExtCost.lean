module

public import CatalanCore.Zeta5.CostOut.ExtBridge
public import CatalanCore.Zeta5.CostOut.OuterCost

@[expose] public section

/-!
# ZC19: `γ_p^ext = p Γ(K/p) + O(1)` and the outer cost `W_out(θ) = min(T_out(θ), θ R(1/θ))`

* `zc19_gamma`: `|γ_p^ext - p Γ(K/p)| ≤ 83` for `ExtHyp p n` (`p ≥ 101` prime, `K/3 < p ≤ K`).
* `zc19_cost`: `|(-v_p(S_K) - γ_p^ext) - p R(K/p)| ≤ 86` with `R = Rg` (`neg_Gam_sub_N0`).
* `zc19_outer_cost`: the best cost on `K/3 < p ≤ 2h` is `K W_out(p/K) + O(1)`.
-/

open Finset

namespace CatalanCore.Zeta5.CostOut

open Apery Apery.CostIn CatalanCore.Zeta5.Sum

theorem pN0_eq {n p : ℕ} (hn : 1 ≤ n) (h1 : 40 * n < 3 * p) (hpK : p ≤ 40 * n) :
    (p : ℝ) * N0 ((40 * n : ℝ) / p)
      = -((scalarPart n p ((40 * n / p : ℕ) : ℤ) : ℤ) : ℝ) := by
  have hp0n : 0 < p := by omega
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp0n
  have hxe : (40 * n : ℝ) / p = ((40 * n : ℕ) : ℝ) / p := by push_cast; ring
  have hfl' : ⌊(40 * n : ℝ) / p⌋ = ((40 * n / p : ℕ) : ℤ) := by rw [hxe]; exact floorR_div _ _
  have e3 : (3 / 40 : ℝ) * ((40 * n : ℝ) / p) = ((3 * n : ℕ) : ℝ) / p := by
    push_cast; field_simp
  have hN : 3 * n < p := by omega
  have hfl3 : ⌊(3 / 40 : ℝ) * ((40 * n : ℝ) / p)⌋ = 0 := by
    rw [e3, floorR_div, Nat.div_eq_of_lt hN]; rfl
  have ew : 2 * ((37 / 40 : ℝ) * ((40 * n : ℝ) / p)) = ((74 * n : ℕ) : ℝ) / p := by
    push_cast; field_simp; ring
  have hM : ⌊2 * ((37 / 40 : ℝ) * ((40 * n : ℝ) / p))⌋ = ((74 * n / p : ℕ) : ℤ) := by
    rw [ew, floorR_div]
  have hd := Nat.div_add_mod (74 * n) p
  have hlt := Nat.mod_lt (74 * n) hp0n
  have hMb : 1 ≤ 74 * n / p ∧ 74 * n / p ≤ 5 := by
    constructor
    · exact (Nat.le_div_iff_mul_le hp0n).mpr (by omega)
    · have : 74 * n / p < 6 := (Nat.div_lt_iff_lt_mul hp0n).mpr (by omega)
      omega
  unfold N0 Jf
  rw [hfl', hfl3, hM]
  unfold scalarPart
  generalize 40 * n / p = q
  have hMlo : p * (74 * n / p) ≤ 74 * n := by omega
  have hMhi : 74 * n < p * (74 * n / p) + p := by omega
  generalize 74 * n / p = M at hMb hMlo hMhi ⊢
  have hMlo' : (p : ℝ) * M ≤ 74 * n := by exact_mod_cast hMlo
  have hMhi' : 74 * (n : ℝ) < p * M + p := by exact_mod_cast hMhi
  have hpx : (p : ℝ) * (40 * n / p) = 40 * n := by field_simp
  push_cast
  have e : (p : ℝ) * (2 * (37 / 40) * (40 * (n : ℝ) / p) * q - 2 * 6 * (37 / 40) * (40 * (n : ℝ) / p) * 0
      - 2 * ((M : ℝ) * (37 / 40 * (40 * (n : ℝ) / p)) - (M : ℝ) * ((M : ℝ) + 1) / 4))
      = 74 * n * q - 74 * n * M + p * M * (M + 1) / 2 := by
    field_simp; ring
  rw [e]
  rcases (by omega : M = 1 ∨ M = 2 ∨ M = 3 ∨ M = 4 ∨ M = 5) with rfl | rfl | rfl | rfl | rfl
  · push_cast at hMlo' hMhi'
    push_cast
    rw [max_eq_right (by linarith : (0:ℝ) ≤ (74 * (n : ℝ) - (p : ℝ))), max_eq_left (by linarith : (74 * (n : ℝ) - 2 * (p : ℝ)) ≤ (0:ℝ)), max_eq_left (by linarith : (74 * (n : ℝ) - 3 * (p : ℝ)) ≤ (0:ℝ)), max_eq_left (by linarith : (74 * (n : ℝ) - 4 * (p : ℝ)) ≤ (0:ℝ)), max_eq_left (by linarith : (74 * (n : ℝ) - 5 * (p : ℝ)) ≤ (0:ℝ))]
    ring
  · push_cast at hMlo' hMhi'
    push_cast
    rw [max_eq_right (by linarith : (0:ℝ) ≤ (74 * (n : ℝ) - (p : ℝ))), max_eq_right (by linarith : (0:ℝ) ≤ (74 * (n : ℝ) - 2 * (p : ℝ))), max_eq_left (by linarith : (74 * (n : ℝ) - 3 * (p : ℝ)) ≤ (0:ℝ)), max_eq_left (by linarith : (74 * (n : ℝ) - 4 * (p : ℝ)) ≤ (0:ℝ)), max_eq_left (by linarith : (74 * (n : ℝ) - 5 * (p : ℝ)) ≤ (0:ℝ))]
    ring
  · push_cast at hMlo' hMhi'
    push_cast
    rw [max_eq_right (by linarith : (0:ℝ) ≤ (74 * (n : ℝ) - (p : ℝ))), max_eq_right (by linarith : (0:ℝ) ≤ (74 * (n : ℝ) - 2 * (p : ℝ))), max_eq_right (by linarith : (0:ℝ) ≤ (74 * (n : ℝ) - 3 * (p : ℝ))), max_eq_left (by linarith : (74 * (n : ℝ) - 4 * (p : ℝ)) ≤ (0:ℝ)), max_eq_left (by linarith : (74 * (n : ℝ) - 5 * (p : ℝ)) ≤ (0:ℝ))]
    ring
  · push_cast at hMlo' hMhi'
    push_cast
    rw [max_eq_right (by linarith : (0:ℝ) ≤ (74 * (n : ℝ) - (p : ℝ))), max_eq_right (by linarith : (0:ℝ) ≤ (74 * (n : ℝ) - 2 * (p : ℝ))), max_eq_right (by linarith : (0:ℝ) ≤ (74 * (n : ℝ) - 3 * (p : ℝ))), max_eq_right (by linarith : (0:ℝ) ≤ (74 * (n : ℝ) - 4 * (p : ℝ))), max_eq_left (by linarith : (74 * (n : ℝ) - 5 * (p : ℝ)) ≤ (0:ℝ))]
    ring
  · push_cast at hMlo' hMhi'
    push_cast
    rw [max_eq_right (by linarith : (0:ℝ) ≤ (74 * (n : ℝ) - (p : ℝ))), max_eq_right (by linarith : (0:ℝ) ≤ (74 * (n : ℝ) - 2 * (p : ℝ))), max_eq_right (by linarith : (0:ℝ) ≤ (74 * (n : ℝ) - 3 * (p : ℝ))), max_eq_right (by linarith : (0:ℝ) ≤ (74 * (n : ℝ) - 4 * (p : ℝ))), max_eq_right (by linarith : (0:ℝ) ≤ (74 * (n : ℝ) - 5 * (p : ℝ)))]
    ring

section ExtPart

variable {p n : ℕ} (H : Apery.ExtHyp p n)
include H

/-- **ZC19, first half.** `|γ_p^ext - p Γ(K/p)| ≤ 83`. -/
theorem zc19_gamma :
    |(gammaExt H : ℝ) - (p : ℝ) * Gam ((40 * n : ℝ) / p)| ≤ 83 := by
  have hodd : p % 2 = 1 := by have := H.p_odd; omega
  have h := ExtHyp.gammaExt_close H
  rw [p_Gam_eq (by have := H.n3; omega) H.hout H.hpK hodd]
  have h' : |((gammaExt H : ℚ) : ℝ) - (((pGam2 n p : ℚ) / 2 : ℚ) : ℝ)| ≤ 83 := by
    rw [← Rat.cast_sub, ← Rat.cast_abs]
    exact_mod_cast h
  simpa using h'

/-- The extension cost `-v_p(S_K) - γ_p^ext` of the prime `p`. -/
noncomputable def costExt : ℝ := -(vSK n p : ℝ) - (gammaExt H : ℝ)

/-- **ZC19, cost form.** `|(-v_p(S_K) - γ_p^ext) - p R(K/p)| ≤ 86`, `R = Rg`. -/
theorem zc19_cost :
    |costExt H - (p : ℝ) * CatalanCore.Zeta5.Profile.Rg ((40 * n : ℝ) / p)| ≤ 86 := by
  have hodd : p % 2 = 1 := by have := H.p_odd; omega
  have : Fact p.Prime := ⟨H.prime⟩
  have hn : 1 ≤ n := by have := H.n3; omega
  have hR : (p : ℝ) * CatalanCore.Zeta5.Profile.Rg ((40 * n : ℝ) / p)
      = -((p : ℝ) * Gam ((40 * n : ℝ) / p)) + ((scalarPart n p ((40 * n / p : ℕ) : ℤ) : ℤ) : ℝ) := by
    rw [← neg_Gam_sub_N0, mul_sub, pN0_eq hn H.hout H.hpK]
    ring
  have hs := scalar_bound n p (40 * n / p) hodd rfl
  have hvs : (vSK n p : ℝ) = (vSz n p : ℝ) := by rw [vSK_outer hn H.hout]
  have hg := zc19_gamma H
  unfold costExt
  rw [hR, hvs]
  have h1 : (-3 : ℝ) ≤ -(vSz n p : ℝ) - ((scalarPart n p ((40 * n / p : ℕ) : ℤ) : ℤ) : ℝ) := by
    exact_mod_cast hs.1
  have h2 : -(vSz n p : ℝ) - ((scalarPart n p ((40 * n / p : ℕ) : ℤ) : ℤ) : ℝ) ≤ 0 := by
    exact_mod_cast hs.2
  rw [abs_le] at hg ⊢
  constructor <;> linarith [hg.1, hg.2]

/-- **The exponent**: `v_p^G(Δ_K) ≥ max (γ_p^out, γ_p^ext)`. -/
theorem zc19_exponent :
    GV p (Δ n) (max (gammaOut n p : ℚ) (gammaExt H)) := by
  have : Fact p.Prime := ⟨H.prime⟩
  have hn : 1 ≤ n := by have := H.n3; omega
  have h1 : GV p (Δ n) (gammaOut n p : ℚ) := zc14_outer hn H.hout H.hpK
  have h2 : GV p (Δ n) (gammaExt H) := H.zc18_ext
  rcases le_total (gammaOut n p : ℚ) (gammaExt H) with h | h
  · rw [max_eq_right h]; exact h2
  · rw [max_eq_left h]; exact h1

end ExtPart

/-- The outer cost function `W_out(θ) = min(T_out(θ), θ R(1/θ))` on `1/3 < θ ≤ 1`, and `T_out = T₀`
for `θ > 1` (where the extension does not apply). -/
noncomputable def Wout (θ : ℝ) : ℝ :=
  if θ ≤ 1 then min (T0 θ) (θ * CatalanCore.Zeta5.Profile.Rg (1 / θ)) else T0 θ

open Classical in
/-- The best signed outer cost at `p`: `min (w_out, -v_p(S_K) - γ_p^ext)` where the extension
applies (`p ≥ 101` prime, `K/3 < p ≤ K`), and `w_out` otherwise. -/
noncomputable def wBest (n p : ℕ) : ℝ :=
  if H : Apery.ExtHyp p n then min (wOut n p : ℝ) (costExt H) else (wOut n p : ℝ)

/-- The best cost is `-v_p(S_K) - max (γ_p^out, γ_p^ext)`: the exponent of `zc19_exponent`. -/
theorem wBest_eq {p n : ℕ} (H : Apery.ExtHyp p n) : wBest n p = -(vSK n p : ℝ) - max (gammaOut n p : ℝ) (gammaExt H : ℝ) := by
  have hpK := H.hpK
  unfold wBest wOut costExt
  simp only [dif_pos H, hpK, ite_true]
  push_cast
  rcases le_total (gammaOut n p : ℝ) (gammaExt H : ℝ) with h | h
  · rw [max_eq_right h, min_eq_right (by linarith)]
  · rw [max_eq_left h, min_eq_left (by linarith)]


/-- **ZC19, outer cost.** For a prime `p ≥ 101` with `K/3 < p ≤ 2h`:
`|wBest - K · W_out(p/K)| ≤ 86`. -/
theorem zc19_outer_cost {n p : ℕ} (hp : p.Prime) (h101 : 101 ≤ p) (hn : 1 ≤ n)
    (h1 : 40 * n < 3 * p) (h2 : p ≤ 2 * (37 * n)) :
    |wBest n p - (40 * n : ℝ) * Wout ((p : ℝ) / (40 * n))| ≤ 86 := by
  have : Fact p.Prime := ⟨hp⟩
  have hK0 : (0 : ℝ) < 40 * n := by positivity
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hz := zc20_outer hn h1 h2
  by_cases hpK : p ≤ 40 * n
  · have H : Apery.ExtHyp p n := ⟨hp, h101, h1, hpK⟩
    have hc := zc19_cost H
    have hθ : (p : ℝ) / (40 * n) ≤ 1 := by
      rw [div_le_one hK0]; exact_mod_cast hpK
    unfold Wout wBest
    simp only [hθ, ite_true, dif_pos H]
    have e1 : (40 * n : ℝ) * min (T0 ((p : ℝ) / (40 * n)))
        ((p : ℝ) / (40 * n) * CatalanCore.Zeta5.Profile.Rg (1 / ((p : ℝ) / (40 * n))))
        = min ((40 * n : ℝ) * T0 ((p : ℝ) / (40 * n)))
          ((p : ℝ) * CatalanCore.Zeta5.Profile.Rg ((40 * n : ℝ) / p)) := by
      rw [mul_min_of_nonneg _ _ hK0.le, one_div_div]
      congr 1
      field_simp
    rw [e1]
    refine (abs_min_sub_min_le_max _ _ _ _).trans ?_
    refine max_le (hz.trans (by norm_num)) ?_
    exact hc.trans (by norm_num)
  · have hpK' : ¬ (p ≤ 40 * n) := hpK
    have hθ : ¬ ((p : ℝ) / (40 * n) ≤ 1) := by
      rw [not_le, one_lt_div hK0]; exact_mod_cast (by omega : 40 * n < p)
    have hnH : ¬ Apery.ExtHyp p n := fun H => hpK' H.hpK
    unfold Wout wBest
    simp only [hθ, ite_false, dif_neg hnH]
    exact hz.trans (by norm_num)

end CatalanCore.Zeta5.CostOut

#print axioms CatalanCore.Zeta5.CostOut.zc19_outer_cost
#print axioms CatalanCore.Zeta5.CostOut.zc19_gamma
#print axioms CatalanCore.Zeta5.CostOut.zc19_cost
#print axioms CatalanCore.Zeta5.CostOut.zc19_exponent
#print axioms CatalanCore.Zeta5.CostOut.wBest_eq
