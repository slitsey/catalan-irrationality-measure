module

public import CatalanCore.Uniform.Bank.Plane2.Content.Core

@[expose] public section
set_option Elab.async false

open Polynomial Finset Matrix CatalanCore.Basic CatalanCore.Arith.Hybrid

/-!
# Plane 2 content: the band rows (lane H, wave P210-A; ledger P210, P213)

* `brBand_cov`, `brPlain_cov`: the price covariance (T1) of the band branches under the lattice shift
  `(r, p, m) ↦ (r + 41 p, p, m + 3 p)` (`b = 41`, `a = 3`, `Kc = 3 · (41 + 3) = 132`): the price grows by `132 p`.
* `real_brBand`: `Real v u (brBand par W k)` for every band `k ≥ 1` (`par ≡ k` mod 2) and each of the five symmetric
  dual vectors of `vecs`, generically in `k`; `real_brPlain`: `Real v u brPlain`.  Both are the sweep row `P₁`
  (`Sweep.RowP1.row_P1`) on the family `p2Q`, with the cell weight `wc W` (one weight per cell of the two
  periods meeting the window); the dual hypothesis is the `4 × 4` table `VecDual`, transported to every `u`
  (`u = 0` included) by `w3_cell_mono`.  The datum needs `v ≠ 0` (`p ∤ v` for `p > p2N0 v`).
-/

namespace CatalanCore.Uniform.Bank.Plane2.Content

open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Support CatalanCore.Uniform.Content.Sweep
  CatalanCore.Uniform.Content.Shape CatalanCore.Uniform.Content.Wire
  CatalanCore.Uniform.Content.BankShared CatalanCore.Uniform.Content.BankShared.Check
  CatalanCore.Uniform.Content.BankShared.KTerm CatalanCore.Uniform.Content.BankShared.TwoTerm

/-! ### (T1) price covariance -/

theorem dist_le (p m : ℕ) : min (m % p) (p - m % p) ≤ m :=
  le_trans (min_le_left _ _) (Nat.mod_le m p)

/-- The window sum only sees `p`, `vk 0` and the two window ends. -/
theorem wsum_congr (W : Vec) (lo hi : KExpr) (r r' p m m' : ℕ) (kv : ℕ → ℕ)
    (hlo : lo.evalN r p m kv = lo.evalN r' p m' kv) (hhi : hi.evalN r p m kv = hi.evalN r' p m' kv) :
    (wsum W lo hi).evalN r p m kv = (wsum W lo hi).evalN r' p m' kv := by
  simp [wsum, clen, cstart, cend, hk, KExpr.evalN, hlo, hhi]

/-- **(T1)** the price of the band branch at the shifted configuration `(r + 41 p, p, m + 3 p)` is the base
price plus `Kc p = 132 p`. -/
theorem brBand_cov (par : ℕ) (W : Vec) (k : ℕ) (r p m : ℕ) (kv : ℕ → ℕ) :
    (brBand par W k).τ.evalN (r + 41 * p) p (m + 3 * p) kv = (brBand par W k).τ.evalN r p m kv + 132 * p := by
  have hs : (r + 41 * p) % p = r % p := Nat.add_mul_mod_self_right _ _ _
  have hd : (m + 3 * p) % p = m % p := Nat.add_mul_mod_self_right _ _ _
  have hw : (wsum W (winLo par) (winHi par)).evalN (r + 41 * p) p (m + 3 * p) kv =
      (wsum W (winLo par) (winHi par)).evalN r p m kv := by
    apply wsum_congr <;> (simp only [winLo, winHi]; split_ifs <;> simp [KExpr.evalN, hs, hd])
  have hle := dist_le p m
  simp only [brBand, KExpr.evalN]
  rw [hw, hd]
  omega

/-- **(T1)** for the plain row. -/
theorem brPlain_cov (r p m : ℕ) (kv : ℕ → ℕ) :
    brPlain.τ.evalN (r + 41 * p) p (m + 3 * p) kv = brPlain.τ.evalN r p m kv + 132 * p := by
  have hd : (m + 3 * p) % p = m % p := Nat.add_mul_mod_self_right _ _ _
  have hle := dist_le p m
  simp only [brPlain, KExpr.evalN]
  rw [hd]
  omega

/-! ### The cell weight of a vector -/

/-- The weight of the node `t` for the vector `W` on the cells `[a, a+h), [a+h, a+p), [a+p, a+p+h), [a+p+h, ∞)`
(`h = (p+1)/2`). -/
def wc (W : Vec) (p a t : ℕ) : ℕ :=
  if t < a + (p + 1) / 2 then W.1 else if t < a + p then W.2.1
  else if t < a + p + (p + 1) / 2 then W.2.2.1 else W.2.2.2

/-- The `4 × 4` dual table: `W_c + W_c' ≥ w3` for the cells `0, 1` (period `b`), `2, 3` (period `b+1`). -/
def VecDual (W : Vec) : Prop :=
  1 ≤ W.1 + W.2.1 ∧ 1 ≤ W.2.2.1 + W.2.2.2 ∧ 2 ≤ W.1 + W.2.2.1 ∧ 2 ≤ W.1 + W.2.2.2 ∧
    2 ≤ W.2.1 + W.2.2.1 ∧ 2 ≤ W.2.1 + W.2.2.2

theorem vecs_dual {W : Vec} (h : W ∈ vecs) : VecDual W := by
  unfold vecs at h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h <;> subst h <;> unfold VecDual <;> decide

theorem cell_one {p j t : ℕ} (hp : 0 < p) (h1 : j * p ≤ t) (h2 : t < j * p + p) :
    cell p 1 t = (j, if p + 1 ≤ 2 * (t - j * p) then 1 else 0) := by
  have hdiv : t / p = j := (div_win hp).2 ⟨h1, h2⟩
  have hmod : t % p = t - j * p := by
    have := Nat.div_add_mod t p
    rw [hdiv, Nat.mul_comm] at this
    omega
  unfold cell half
  simp [hdiv, hmod]

/-- Each node of the two periods `[b p, b p + 2 p)` lies in one of the four cells; the weight and the `u = 1` cell. -/
theorem cell_cases (W : Vec) {p b s : ℕ} (hp : p % 2 = 1) (hp0 : 0 < p) (h1 : b * p ≤ s) (h2 : s < b * p + 2 * p) :
    (cell p 1 s = (b, 0) ∧ wc W p (b * p) s = W.1) ∨ (cell p 1 s = (b, 1) ∧ wc W p (b * p) s = W.2.1) ∨
    (cell p 1 s = (b + 1, 0) ∧ wc W p (b * p) s = W.2.2.1) ∨
    (cell p 1 s = (b + 1, 1) ∧ wc W p (b * p) s = W.2.2.2) := by
  have hb1 : (b + 1) * p = b * p + p := by ring
  by_cases hlt : s < b * p + p
  · have hc := cell_one hp0 h1 hlt
    by_cases hh : s < b * p + (p + 1) / 2
    · left
      refine ⟨?_, by unfold wc; rw [if_pos hh]⟩
      rw [hc]
      have : (if p + 1 ≤ 2 * (s - b * p) then 1 else 0) = 0 := by rw [if_neg]; omega
      rw [this]
    · right; left
      refine ⟨?_, by unfold wc; rw [if_neg hh, if_pos hlt]⟩
      rw [hc]
      have : (if p + 1 ≤ 2 * (s - b * p) then 1 else 0) = 1 := by rw [if_pos]; omega
      rw [this]
  · have h1' : (b + 1) * p ≤ s := by omega
    have h2' : s < (b + 1) * p + p := by omega
    have hc := cell_one hp0 h1' h2'
    rw [hb1] at hc
    by_cases hh : s < b * p + p + (p + 1) / 2
    · right; right; left
      refine ⟨?_, by unfold wc; rw [if_neg (by omega), if_neg hlt, if_pos hh]⟩
      rw [hc]
      have : (if p + 1 ≤ 2 * (s - (b * p + p)) then 1 else 0) = 0 := by rw [if_neg]; omega
      rw [this]
    · right; right; right
      refine ⟨?_, by unfold wc; rw [if_neg (by omega), if_neg hlt, if_neg hh]⟩
      rw [hc]
      have : (if p + 1 ≤ 2 * (s - (b * p + p)) then 1 else 0) = 1 := by rw [if_pos]; omega
      rw [this]

/-- The dual hypothesis of `row_P1` for the weight `wc W` on the two periods, for every `u` (`u = 0` included). -/
theorem dual_wc (u : ℤ) {W : Vec} (hW : VecDual W) {p b t t' : ℕ} (hp : p % 2 = 1) (hp0 : 0 < p)
    (ht1 : b * p ≤ t) (ht2 : t < b * p + 2 * p) (ht1' : b * p ≤ t') (ht2' : t' < b * p + 2 * p) :
    w3 (cell p u t) (cell p u t') ≤ wc W p (b * p) t + wc W p (b * p) t' := by
  refine le_trans (w3_cell_mono p u t t') ?_
  obtain ⟨d1, d2, d3, d4, d5, d6⟩ := hW
  rcases cell_cases W hp hp0 ht1 ht2 with ⟨c, e⟩ | ⟨c, e⟩ | ⟨c, e⟩ | ⟨c, e⟩ <;>
  rcases cell_cases W hp hp0 ht1' ht2' with ⟨c', e'⟩ | ⟨c', e'⟩ | ⟨c', e'⟩ | ⟨c', e'⟩ <;>
  · rw [c, c', e, e']
    simp only [w3, Prod.mk.injEq]
    split_ifs <;> omega

/-! ### Sums of the cell weight over a window -/

theorem sum_ind_band (lo hi s e : ℕ) :
    ∑ t ∈ Finset.Ico lo hi, (if t ∈ Finset.Ico s e then 1 else 0) = min hi e - max lo s := by
  rw [← Finset.card_filter]
  have : (Finset.Ico lo hi).filter (fun t => t ∈ Finset.Ico s e) = Finset.Ico (max lo s) (min hi e) := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_Ico]
    omega
  rw [this, Nat.card_Ico]

theorem wc_ind (W : Vec) {p a t : ℕ} (hp : p % 2 = 1) (h1 : a ≤ t) (h2 : t < a + 2 * p) :
    wc W p a t = W.1 * (if t ∈ Finset.Ico a (a + (p + 1) / 2) then 1 else 0) +
      W.2.1 * (if t ∈ Finset.Ico (a + (p + 1) / 2) (a + p) then 1 else 0) +
      W.2.2.1 * (if t ∈ Finset.Ico (a + p) (a + p + (p + 1) / 2) then 1 else 0) +
      W.2.2.2 * (if t ∈ Finset.Ico (a + p + (p + 1) / 2) (a + 2 * p) then 1 else 0) := by
  simp only [wc, Finset.mem_Ico]
  split_ifs <;> omega

/-- The sum of the weight over a window `[a + lx, a + hx)` inside the two periods, in positions relative to `a`. -/
theorem sum_wc (W : Vec) {p a lo hi lx hx : ℕ} (hp : p % 2 = 1) (hlo : lo = a + lx) (hhi : hi = a + hx)
    (hx2 : hx ≤ 2 * p) :
    ∑ t ∈ Finset.Ico lo hi, wc W p a t =
      W.1 * (min hx ((p + 1) / 2) - max lx 0) + W.2.1 * (min hx p - max lx ((p + 1) / 2)) +
      W.2.2.1 * (min hx (p + (p + 1) / 2) - max lx p) + W.2.2.2 * (min hx (2 * p) - max lx (p + (p + 1) / 2)) := by
  subst hlo hhi
  rw [Finset.sum_congr rfl (fun t ht => wc_ind W hp (by simp only [Finset.mem_Ico] at ht; omega)
    (by simp only [Finset.mem_Ico] at ht; omega))]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, sum_ind_band]
  have e1 : min (a + hx) (a + (p + 1) / 2) - max (a + lx) a = min hx ((p + 1) / 2) - max lx 0 := by omega
  have e2 : min (a + hx) (a + p) - max (a + lx) (a + (p + 1) / 2) = min hx p - max lx ((p + 1) / 2) := by omega
  have e3 : min (a + hx) (a + p + (p + 1) / 2) - max (a + lx) (a + p) =
      min hx (p + (p + 1) / 2) - max lx p := by omega
  have e4 : min (a + hx) (a + 2 * p) - max (a + lx) (a + p + (p + 1) / 2) =
      min hx (2 * p) - max lx (p + (p + 1) / 2) := by omega
  rw [e1, e2, e3, e4]

/-! ### The row `P₁` on the family -/

/-- The sweep domain from the guard `r ≤ 400 p` and the border of `p2G`. -/
theorem p2_guard_band {r p m N0 : ℕ} (hN0 : 919 ≤ N0) (hp : N0 < p) (hg : r ≤ 400 * p)
    (hb : 41 * (2 * m) < 6 * r + 41) : 2 * (r + 2 * m) + 2 * p < p * p := by
  have h920 : 920 ≤ p := by omega
  have : 920 * p ≤ p * p := Nat.mul_le_mul_right p h920
  omega

/-- **Row `P₁` on the family `p2Q`** (`p ≤ 2 m`, guard `r ≤ 400 p`), for any symmetric dual `w` of `W₃` on `E`. -/
theorem p2_P1_gle (v u : ℤ) (hv : v ≠ 0) {r p m : ℕ} [hp : Fact p.Prime] (S : Finset (p2G.geometry r).C)
    (hm : (p2G.geometry r).k = m) (hr : r % 2 = 0) (hPb : p2Pbad < p) (hN0 : p2N0 v < p)
    (hg : r ≤ 400 * p) (hb : 41 * (2 * m) < 6 * r + 41) (h2m : p ≤ 2 * m) (w : ℕ → ℕ)
    (hdual : ∀ t ∈ P1E p r m, ∀ t' ∈ P1E p r m, w3 (cell p u t) (cell p u t') ≤ w t + w t') :
    GLE p (3 * (r + m) - 3 * min (m % p) (p - m % p) + ∑ t ∈ P1E p r m, w t) (p2Q v u r S) := by
  subst hm
  have hp5 : 5 ≤ p := by unfold p2Pbad at hPb; omega
  have hodd : p % 2 = 1 := by
    rcases hp.out.eq_two_or_odd with h | h
    · omega
    · exact h
  have hpv : ¬ (p : ℤ) ∣ v := by
    intro h
    have h1 : p ∣ v.natAbs := Int.natCast_dvd.1 h
    have h2 : 0 < v.natAbs := Int.natAbs_pos.2 hv
    have h3 := Nat.le_of_dvd h2 h1
    have h4 : v.natAbs ≤ p2N0 v := le_max_right _ _
    omega
  have hN : 2 * (r + 2 * (p2G.geometry r).k) + 2 * p < p * p :=
    p2_guard_band (N0 := p2N0 v) (by unfold p2N0; exact le_max_left _ _) hN0 hg hb
  rw [p2Q_eq v u r hr S]
  exact row_P1 v u hpv hodd hp5 h2m hN _ (p2Q_inj r S) (p2Q_lt r hr S) w hdual

/-! ### The window and the norm in the band `k` -/

theorem P1E_even {p r m k : ℕ} (hp0 : 0 < p) (h1 : k * p ≤ 2 * m) (h2 : 2 * m < (k + 1) * p) (hk : k % 2 = 0) :
    P1E p r m = Finset.Ico r (r + (2 * m - k * p)) := by
  have hkp : (k + 1) * p = k * p + p := by ring
  have hq : 2 * m / p = k := (div_win hp0).2 ⟨h1, by omega⟩
  have hs : 2 * m % p = 2 * m - k * p := by
    have := Nat.div_add_mod (2 * m) p
    rw [hq, Nat.mul_comm] at this
    omega
  unfold P1E
  rw [hq, hs]
  simp [hk]

theorem P1E_odd {p r m k : ℕ} (hp0 : 0 < p) (h1 : k * p ≤ 2 * m) (h2 : 2 * m < (k + 1) * p) (hk : k % 2 = 1) :
    P1E p r m = Finset.Ico (r + (2 * m - k * p)) (r + p) := by
  have hkp : (k + 1) * p = k * p + p := by ring
  have hq : 2 * m / p = k := (div_win hp0).2 ⟨h1, by omega⟩
  have hs : 2 * m % p = 2 * m - k * p := by
    have := Nat.div_add_mod (2 * m) p
    rw [hq, Nat.mul_comm] at this
    omega
  unfold P1E
  rw [hq, hs]
  have : ¬ k % 2 = 0 := by omega
  simp [this]

/-- The norm `‖m‖_p` in the band `k`: `2‖m‖ = 2m - k p` for even `k`, `= (k+1) p - 2m` for odd `k`. -/
theorem dist_band {p m k : ℕ} (hp : p % 2 = 1) (hp0 : 0 < p) (h1 : k * p ≤ 2 * m) (h2 : 2 * m < (k + 1) * p) :
    (k % 2 = 0 → 2 * min (m % p) (p - m % p) = 2 * m - k * p) ∧
    (k % 2 = 1 → 2 * min (m % p) (p - m % p) = (k + 1) * p - 2 * m) := by
  obtain ⟨k', e, hke, he⟩ : ∃ k' e, k = 2 * k' + e ∧ e ≤ 1 := ⟨k / 2, k % 2, by omega, by omega⟩
  subst hke
  have hkp : (2 * k' + e) * p = 2 * (k' * p) + e * p := by ring
  have hkp1 : (2 * k' + e + 1) * p = 2 * (k' * p) + e * p + p := by ring
  rcases (by omega : e = 0 ∨ e = 1) with rfl | rfl
  · refine ⟨fun _ => ?_, fun h => by omega⟩
    obtain ⟨s, hs⟩ : ∃ s, s = 2 * m - 2 * (k' * p) := ⟨_, rfl⟩
    have hmm : m = s / 2 + k' * p := by omega
    have hmod : m % p = s / 2 := by
      calc m % p = (s / 2 + k' * p) % p := by rw [← hmm]
        _ = (s / 2) % p := Nat.add_mul_mod_self_right _ _ _
        _ = s / 2 := Nat.mod_eq_of_lt (by omega)
    rw [hmod]
    omega
  · refine ⟨fun h => by omega, fun _ => ?_⟩
    obtain ⟨s, hs⟩ : ∃ s, s = 2 * m - 2 * (k' * p) - p := ⟨_, rfl⟩
    have hmm : m = (p + s) / 2 + k' * p := by omega
    have hmod : m % p = (p + s) / 2 := by
      calc m % p = ((p + s) / 2 + k' * p) % p := by rw [← hmm]
        _ = ((p + s) / 2) % p := Nat.add_mul_mod_self_right _ _ _
        _ = (p + s) / 2 := Nat.mod_eq_of_lt (by omega)
    rw [hmod]
    omega

/-- Decomposition of `r`. -/
theorem r_decomp (r p : ℕ) : r = (r / p) * p + r % p := by
  have := Nat.div_add_mod r p
  rw [Nat.mul_comm] at this
  omega

/-! ### The band conditions -/

theorem band_conds {par : ℕ} {W : Vec} {k r p m : ℕ} {kv : ℕ → ℕ}
    (h : ∀ cd ∈ (brBand par W k).conds, cd.Holds r p m kv) :
    k * p ≤ 2 * m ∧ 2 * m < (k + 1) * p ∧ r ≤ 400 * p := by
  have c1 := h ⟨0, -(k : ℤ), 2, [], 0, false⟩ (by simp [brBand])
  have c2 := h ⟨0, (k : ℤ) + 1, -2, [], 0, true⟩ (by simp [brBand])
  have c3 := h gGuard (by simp [brBand])
  simp only [KCond.Holds, KCond.L, dot, gGuard, if_true, Bool.false_eq_true, if_false] at c1 c2 c3
  refine ⟨?_, ?_, ?_⟩
  · have : (k : ℤ) * p ≤ 2 * m := by linarith
    exact_mod_cast this
  · have : (2 * m : ℤ) < (k + 1) * p := by linarith
    exact_mod_cast this
  · have : (r : ℤ) ≤ 400 * p := by linarith
    exact_mod_cast this

/-! ### `Real` of the band branches -/

theorem real_brBand (v u : ℤ) (hv : v ≠ 0) (par : ℕ) {W : Vec} (hW : W ∈ vecs) (k : ℕ) (hk1 : 1 ≤ k)
    (hpar : par % 2 = k % 2) : Real v u (brBand par W k) := by
  intro r p _ S kv hr hr0 hPb hN0 hqN hkv hconds
  obtain ⟨hb1, hb2, hg⟩ := band_conds hconds
  have hVD := vecs_dual hW
  have hp5 : 5 ≤ p := by unfold p2Pbad at hPb; omega
  have hp0 : 0 < p := by omega
  have hodd : p % 2 = 1 := by
    rcases (inferInstance : Fact p.Prime).out.eq_two_or_odd with h | h
    · omega
    · exact h
  have hkv0 : kv 0 = (p + 1) / 2 := by omega
  have hbord := (p2_border hr).2
  have hkp : (k + 1) * p = k * p + p := by ring
  have hkpp : p ≤ k * p := Nat.le_mul_of_pos_left p hk1
  obtain ⟨hdE, hdO⟩ := dist_band (m := p2G.borderSize r) hodd hp0 hb1 hb2
  have hrd := r_decomp r p
  have hsp : r % p < p := Nat.mod_lt _ hp0
  have hdl := dist_le p (p2G.borderSize r)
  have hmle : 2 * p2G.borderSize r < r % p + 2 * (p2G.borderSize r) + 1 := by omega
  by_cases hpe : k % 2 = 0
  · -- even band: window `[r, r + (2m - k p))`
    have hpe' : par % 2 = 0 := by omega
    have hP := P1E_even (r := r) hp0 hb1 hb2 hpe
    have key := p2_P1_gle v u hv S (geometry_k_eq_borderSize p2G r) hr hPb hN0 hg hbord (by omega)
      (wc W p ((r / p) * p)) (by
        intro t ht t' ht'
        rw [hP, Finset.mem_Ico] at ht ht'
        exact dual_wc u hVD hodd hp0 (by omega) (by omega) (by omega) (by omega))
    refine ⟨_, key, le_of_eq ?_⟩
    rw [hP, sum_wc W hodd (lo := r) (hi := r + (2 * p2G.borderSize r - k * p)) (lx := r % p)
      (hx := r % p + 2 * min (p2G.borderSize r % p) (p - p2G.borderSize r % p)) (a := (r / p) * p)
      (by omega) (by omega) (by omega)]
    simp only [brBand, KExpr.evalN, wsum, clen, cstart, cend, winLo, winHi, hpe', if_true, hk, hkv0]
  · -- odd band: window `[r + (2m - k p), r + p)`
    have hpo : ¬ par % 2 = 0 := by omega
    have hpo1 : k % 2 = 1 := by omega
    have hP := P1E_odd (r := r) hp0 hb1 hb2 hpo1
    have hd1 := hdO hpo1
    have key := p2_P1_gle v u hv S (geometry_k_eq_borderSize p2G r) hr hPb hN0 hg hbord (by omega)
      (wc W p ((r / p) * p)) (by
        intro t ht t' ht'
        rw [hP, Finset.mem_Ico] at ht ht'
        exact dual_wc u hVD hodd hp0 (by omega) (by omega) (by omega) (by omega))
    refine ⟨_, key, le_of_eq ?_⟩
    rw [hP, sum_wc W hodd (lo := r + (2 * p2G.borderSize r - k * p)) (hi := r + p)
      (lx := r % p + p - 2 * min (p2G.borderSize r % p) (p - p2G.borderSize r % p)) (hx := r % p + p)
      (a := (r / p) * p) (by omega) (by omega) (by omega)]
    simp only [brBand, KExpr.evalN, wsum, clen, cstart, cend, winLo, winHi, hpo, if_false, hk, hkv0]

/-- `Real` of the plain row `3 (r + m) ∸ ‖m‖`, `p ≤ 2 m`: the unit dual on the window of length `2 ‖m‖`. -/
theorem real_brPlain (v u : ℤ) (hv : v ≠ 0) : Real v u brPlain := by
  intro r p _ S kv hr hr0 hPb hN0 hqN hkv hconds
  have c1 := hconds ⟨0, -1, 2, [], 0, false⟩ (by simp [brPlain])
  have c3 := hconds gGuard (by simp [brPlain])
  simp only [KCond.Holds, KCond.L, dot, gGuard, if_true, Bool.false_eq_true, if_false] at c1 c3
  have h2m : p ≤ 2 * p2G.borderSize r := by
    have : (p : ℤ) ≤ 2 * p2G.borderSize r := by linarith
    exact_mod_cast this
  have hg : r ≤ 400 * p := by
    have : (r : ℤ) ≤ 400 * p := by linarith
    exact_mod_cast this
  have hp5 : 5 ≤ p := by unfold p2Pbad at hPb; omega
  have hp0 : 0 < p := by omega
  have hodd : p % 2 = 1 := by
    rcases (inferInstance : Fact p.Prime).out.eq_two_or_odd with h | h
    · omega
    · exact h
  have hbord := (p2_border hr).2
  obtain ⟨k, hkdef⟩ : ∃ k, k = 2 * p2G.borderSize r / p := ⟨_, rfl⟩
  have hkw := (div_win (u := 2 * p2G.borderSize r) hp0 (j := k)).1 hkdef.symm
  obtain ⟨hb1, hb2'⟩ := hkw
  have hkp : (k + 1) * p = k * p + p := by ring
  have hb2 : 2 * p2G.borderSize r < (k + 1) * p := by omega
  obtain ⟨hdE, hdO⟩ := dist_band (m := p2G.borderSize r) hodd hp0 hb1 hb2
  have hdl := dist_le p (p2G.borderSize r)
  have hsp : r % p < p := Nat.mod_lt _ hp0
  have hrd := r_decomp r p
  by_cases hpe : k % 2 = 0
  · have hP := P1E_even (r := r) hp0 hb1 hb2 hpe
    have hd1 := hdE hpe
    have key := p2_P1_gle v u hv S (geometry_k_eq_borderSize p2G r) hr hPb hN0 hg hbord h2m
      (fun _ => 1) (fun t _ t' _ => by simpa using w3_le_two (cell p u t) (cell p u t'))
    refine ⟨_, key, le_of_eq ?_⟩
    rw [hP]
    simp only [Finset.sum_const, Nat.card_Ico, smul_eq_mul, mul_one, brPlain, KExpr.evalN]
    omega
  · have hpo1 : k % 2 = 1 := by omega
    have hP := P1E_odd (r := r) hp0 hb1 hb2 hpo1
    have hd1 := hdO hpo1
    have key := p2_P1_gle v u hv S (geometry_k_eq_borderSize p2G r) hr hPb hN0 hg hbord h2m
      (fun _ => 1) (fun t _ t' _ => by simpa using w3_le_two (cell p u t) (cell p u t'))
    refine ⟨_, key, le_of_eq ?_⟩
    rw [hP]
    simp only [Finset.sum_const, Nat.card_Ico, smul_eq_mul, mul_one, brPlain, KExpr.evalN]
    omega

end CatalanCore.Uniform.Bank.Plane2.Content

#print axioms CatalanCore.Uniform.Bank.Plane2.Content.brBand_cov
#print axioms CatalanCore.Uniform.Bank.Plane2.Content.brPlain_cov
#print axioms CatalanCore.Uniform.Bank.Plane2.Content.real_brBand
#print axioms CatalanCore.Uniform.Bank.Plane2.Content.real_brPlain
