module

public import CatalanCore.Uniform.Bank.Plane2.Content.Core
public import CatalanCore.Uniform.Content.Sweep.RowE1
public import CatalanCore.Uniform.Content.Sweep.RowE2

@[expose] public section
set_option Elab.async false

open Polynomial Finset Matrix CatalanCore.Basic CatalanCore.Arith.Hybrid

/-!
# Plane 2 content: the rows `E₁`, `E₂` as `Real` (lane H, wave P210-B; ledger P206, P207, P210)

`Real v u (brE1 W)` and `Real v u (brE2 W)` for the five symmetric dual vectors `W ∈ vecs`.

* `p2_guard`: the guard `400 p ≥ r` with `p > 919` gives `p² > 2 N + 2 p` (`N = r + 2m`).  (The general
  `sweep_sq_guard` with `t = 1/400` does not apply at `N₀ = 919`: it needs `(N₀ - 2)/400 ≥ 2 (1 + 2α)`, i.e.
  `2.2925 ≥ 2.29268`, false by `1.8e-4`.  Here the exact border bound `41 (2m) < 6r + 41` is used instead.)
* `cw W h p x`: the potential of the dual vector `W` at the position `x` relative to `a = p ⌊r/p⌋`, i.e. on the
  four cells `[0,h)`, `[h,p)`, `[p,p+h)`, `[p+h,2p)`; `dual_cw`: `w₃ ≤ cw + cw` for every `W ∈ vecs`, every `u`
  (through `w3_cell_mono`);
* `sum_cw`: `∑_k cw (sp + k)` is `∑_c W_c len_c` (the window price of `Cat.wsum`).
-/

namespace CatalanCore.Uniform.Bank.Plane2.Content

open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Support CatalanCore.Uniform.Content.Sweep
  CatalanCore.Uniform.Content.Shape CatalanCore.Uniform.Content.Wire
  CatalanCore.Uniform.Content.BankShared CatalanCore.Uniform.Content.BankShared.Check
  CatalanCore.Uniform.Content.BankShared.KTerm KExpr CatalanCore.Uniform.Content.BankShared.TwoTerm

/-! ### Prime facts and the guard -/

theorem p2N0_ge (v : ℤ) : 919 ≤ p2N0 v ∧ v.natAbs ≤ p2N0 v := ⟨le_max_left _ _, le_max_right _ _⟩

theorem p2_p920 {v : ℤ} {p : ℕ} (h : p2N0 v < p) : 920 ≤ p := by
  have := (p2N0_ge v).1
  omega

/-- **The guard**: `400 p ≥ r` and `p ≥ 920` give `2 (r + 2m) + 2p < p²`. -/
theorem p2_guard {r p : ℕ} (hr : r % 2 = 0) (hp : 920 ≤ p) (hg : r ≤ 400 * p) :
    2 * (r + 2 * p2G.borderSize r) + 2 * p < p * p := by
  obtain ⟨h1, h2⟩ := p2_border hr
  have h3 : 920 * p ≤ p * p := Nat.mul_le_mul_right p hp
  omega

theorem p2_not_dvd {v : ℤ} (hv : v ≠ 0) {p : ℕ} (h : p2N0 v < p) : ¬ (p : ℤ) ∣ v := by
  intro hd
  have h1 : p ∣ v.natAbs := Int.natCast_dvd.1 hd
  have h2 : 0 < v.natAbs := Int.natAbs_pos.2 hv
  have h3 := Nat.le_of_dvd h2 h1
  have := (p2N0_ge v).2
  omega

theorem p2_hp5 {p : ℕ} (h : p2Pbad < p) : 5 ≤ p := by unfold p2Pbad at h; omega

theorem p2_odd {p : ℕ} [hp : Fact p.Prime] (hp5 : 5 ≤ p) : p % 2 = 1 := by
  rcases hp.out.eq_two_or_odd with h | h
  · omega
  · exact h

/-! ### Reading the conditions -/

theorem holds_ns {r p m : ℕ} {kv : ℕ → ℕ} {cr cp cm c1 : ℤ}
    (h : KCond.Holds ⟨cr, cp, cm, [], c1, false⟩ r p m kv) : 0 ≤ cr * r + cp * p + cm * m + c1 := by
  simpa [KCond.Holds, KCond.L, dot] using h

theorem holds_s {r p m : ℕ} {kv : ℕ → ℕ} {cr cp cm c1 : ℤ}
    (h : KCond.Holds ⟨cr, cp, cm, [], c1, true⟩ r p m kv) : 0 < cr * r + cp * p + cm * m + c1 := by
  simpa [KCond.Holds, KCond.L, dot] using h

/-- The member polynomial with the window rank written as an arbitrary `m` equal to the border size. -/
theorem p2Q_eq_m (v u : ℤ) (r : ℕ) (hr : r % 2 = 0) (S : Finset (p2G.geometry r).C) {m : ℕ}
    (hm : (p2G.geometry r).k = m) :
    p2Q v u r S = (seqFullN (fS v u) (eS v u) (fun a : S => ((a.1 : (p2G.geometry r).C) : ℕ))
      (fun i : Fin m => r + 2 * (i : ℕ)) (fun i : Fin m => r + 2 * (i : ℕ) + 1) (X : ℚ[X])).det := by
  subst hm
  exact p2Q_eq v u r hr S

theorem p2_k_eq (r : ℕ) : (p2G.geometry r).k = p2G.borderSize r := geometry_k_eq_borderSize p2G r

/-! ### The potentials of a dual vector -/

/-- The potential of `W` at the position `x` (relative to `p ⌊r/p⌋`); `h = (p+1)/2`. -/
def cw (W : Vec) (h p x : ℕ) : ℕ :=
  if x < h then W.1 else if x < p then W.2.1 else if x < p + h then W.2.2.1 else W.2.2.2

/-- Indicator of `[s, e)`. -/
def ind (s e x : ℕ) : ℕ := if s ≤ x ∧ x < e then 1 else 0

theorem cw_eq (W : Vec) (h p x : ℕ) (hx : x < 2 * p) (hh : h ≤ p) :
    cw W h p x = W.1 * ind 0 h x + W.2.1 * ind h p x + W.2.2.1 * ind p (p + h) x +
      W.2.2.2 * ind (p + h) (2 * p) x := by
  unfold cw ind
  split_ifs <;> omega

theorem sum_ind (s e sp n : ℕ) :
    ∑ k ∈ range n, ind s e (sp + k) = min (sp + n) e - max sp s := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih]
    unfold ind
    split_ifs <;> omega

/-- The window price: `∑_{k<n} cw (sp + k)` is `∑_c W_c len_c` of the window `[sp, sp + n)`. -/
theorem sum_cw (W : Vec) (h p sp n : ℕ) (hh : h ≤ p) (hn : sp + n ≤ 2 * p) :
    ∑ k ∈ range n, cw W h p (sp + k) =
      W.1 * (min (sp + n) h - max sp 0) + W.2.1 * (min (sp + n) p - max sp h) +
        W.2.2.1 * (min (sp + n) (p + h) - max sp p) + W.2.2.2 * (min (sp + n) (2 * p) - max sp (p + h)) := by
  calc ∑ k ∈ range n, cw W h p (sp + k)
      = ∑ k ∈ range n, (W.1 * ind 0 h (sp + k) + W.2.1 * ind h p (sp + k) + W.2.2.1 * ind p (p + h) (sp + k) +
        W.2.2.2 * ind (p + h) (2 * p) (sp + k)) :=
        sum_congr rfl fun k hk => cw_eq W h p _ (by have := mem_range.1 hk; omega) hh
    _ = _ := by
      simp only [sum_add_distrib, ← mul_sum, sum_ind]

/-- The potentials on the rows `sp + 2i` and the columns `sp + 2j + 1` add up to the window sum. -/
theorem sum_pot (f : ℕ → ℕ) (sp m : ℕ) :
    ∑ i ∈ range m, f (sp + 2 * i) + ∑ j ∈ range m, f (sp + 2 * j + 1) = ∑ k ∈ range (2 * m), f (sp + k) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have e : 2 * (m + 1) = 2 * m + 1 + 1 := by ring
    have e1 : sp + (2 * m + 1) = sp + 2 * m + 1 := by ring
    rw [e, sum_range_succ, sum_range_succ, sum_range_succ, sum_range_succ, e1]
    omega

/-- The price of the window `[sp, sp + 2m)` in `Cat.wsum` is the sum of the potentials. -/
theorem wsum_eval (W : Vec) (r p m : ℕ) (kv : ℕ → ℕ) (hh : kv 0 ≤ p) (hn : r % p + 2 * m ≤ 2 * p) :
    (wsum W .sp (.add .sp (.smul 2 .vm))).evalN r p m kv = ∑ k ∈ range (2 * m), cw W (kv 0) p (r % p + k) := by
  rw [sum_cw W (kv 0) p (r % p) (2 * m) hh hn]
  simp [wsum, clen, cstart, cend, hk, KExpr.evalN]

/-! ### The dual inequality for the five vectors -/

theorem cell_lo {p h : ℕ} (hp : 0 < p) (hh : 2 * h = p + 1) (b y : ℕ) (hy : y < p) :
    cell p 1 (p * b + y) = (b, if h ≤ y then 1 else 0) := by
  have e1 : (p * b + y) / p = b := by rw [Nat.mul_add_div hp, Nat.div_eq_of_lt hy]; simp
  have e2 : (p * b + y) % p = y := by
    rw [Nat.mul_add_mod]; exact Nat.mod_eq_of_lt hy
  unfold cell half
  rw [e1, e2]
  simp only [one_ne_zero, ite_false]
  congr 1
  split_ifs <;> omega

theorem cell_hi {p h : ℕ} (hp : 0 < p) (hh : 2 * h = p + 1) (b y : ℕ) (hy1 : p ≤ y) (hy2 : y < 2 * p) :
    cell p 1 (p * b + y) = (b + 1, if h ≤ y - p then 1 else 0) := by
  obtain ⟨z, rfl⟩ : ∃ z, y = p + z := ⟨y - p, by omega⟩
  have hz : z < p := by omega
  have e0 : p * b + (p + z) = p * (b + 1) + z := by ring
  have e1 : (p * (b + 1) + z) / p = b + 1 := by rw [Nat.mul_add_div hp, Nat.div_eq_of_lt hz]
  have e2 : (p * (b + 1) + z) % p = z := by
    rw [Nat.mul_add_mod]; exact Nat.mod_eq_of_lt hz
  unfold cell half
  rw [e0, e1, e2]
  simp only [one_ne_zero, ite_false]
  congr 1
  have : p + z - p = z := by omega
  rw [this]
  split_ifs <;> omega

set_option maxHeartbeats 4000000 in
theorem dual_cw {W : Vec} (hW : W ∈ vecs) {p h : ℕ} (hp : 0 < p) (hh : 2 * h = p + 1) (u : ℤ) (b x x' : ℕ)
    (hx : x < 2 * p) (hx' : x' < 2 * p) :
    w3 (cell p u (p * b + x)) (cell p u (p * b + x')) ≤ cw W h p x + cw W h p x' := by
  refine (w3_cell_mono p u _ _).trans ?_
  unfold vecs at hW
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hW
  rcases lt_or_ge x p with h1 | h1 <;> rcases lt_or_ge x' p with h2 | h2
  · rw [cell_lo hp hh b x h1, cell_lo hp hh b x' h2]
    unfold w3 cw
    simp only [Prod.mk.injEq, true_and]
    rcases hW with rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> split_ifs <;> omega
  · rw [cell_lo hp hh b x h1, cell_hi hp hh b x' h2 hx']
    unfold w3 cw
    simp only [Prod.mk.injEq, true_and]
    rcases hW with rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> split_ifs <;> omega
  · rw [cell_hi hp hh b x h1 hx, cell_lo hp hh b x' h2]
    unfold w3 cw
    simp only [Prod.mk.injEq, true_and]
    rcases hW with rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> split_ifs <;> omega
  · rw [cell_hi hp hh b x h1 hx, cell_hi hp hh b x' h2 hx']
    unfold w3 cw
    simp only [Prod.mk.injEq, true_and]
    rcases hW with rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> split_ifs <;> omega

/-! ### The rows -/

/-- **`Real` for the row `E₁`** (Theorem 6, `p > 2m`), for each of the five symmetric duals. -/
theorem real_E1 (v u : ℤ) (hv : v ≠ 0) {W : Vec} (hW : W ∈ vecs) : Real v u (brE1 W) := by
  intro r p _ S kv hr hr0 hPb hN0 hN hk hcond
  have hp5 := p2_hp5 hPb
  have hodd := p2_odd (p := p) hp5
  have hpv := p2_not_dvd hv hN0
  have hp0 : 0 < p := by omega
  have hc1 := holds_s (hcond ⟨0, 1, -2, [], 0, true⟩ (by simp [brE1]))
  have hg := holds_ns (hcond gGuard (by simp [brE1]))
  have hN' := p2_guard hr (p2_p920 hN0) (by simp at hg; omega)
  obtain ⟨m, hmdef⟩ : ∃ m, m = p2G.borderSize r := ⟨_, rfl⟩
  rw [← hmdef] at hN' hc1 hg ⊢
  have h2m : 2 * m < p := by omega
  have hsp := Nat.mod_lt r hp0
  have hn : r % p + 2 * m ≤ 2 * p := by omega
  have hkp : kv 0 ≤ p := by omega
  have hdual : ∀ i j, i < m → j < m →
      w3 (cell p u (r + 2 * i)) (cell p u (r + 2 * j + 1)) ≤
        cw W (kv 0) p (r % p + 2 * i) + cw W (kv 0) p (r % p + 2 * j + 1) := by
    intro i j hi hj
    have hd := Nat.div_add_mod r p
    have e1 : r + 2 * i = p * (r / p) + (r % p + 2 * i) := by omega
    have e2 : r + 2 * j + 1 = p * (r / p) + (r % p + 2 * j + 1) := by omega
    have := dual_cw hW hp0 hk u (r / p) (r % p + 2 * i) (r % p + 2 * j + 1) (by omega) (by omega)
    rw [← e1, ← e2] at this
    exact this
  refine ⟨3 * r + ∑ i ∈ range m, cw W (kv 0) p (r % p + 2 * i) + ∑ j ∈ range m, cw W (kv 0) p (r % p + 2 * j + 1),
    ?_, ?_⟩
  · rw [p2Q_eq_m v u r hr S (hmdef ▸ p2_k_eq r)]
    exact row_E1 (p := p) v u hpv hodd hp5 h2m hN' (fun a : S => ((a.1 : (p2G.geometry r).C) : ℕ))
      (p2Q_inj r S) (p2Q_lt r hr S) (fun i => cw W (kv 0) p (r % p + 2 * i))
      (fun j => cw W (kv 0) p (r % p + 2 * j + 1)) hdual
  · have hw := wsum_eval W r p m kv hkp hn
    rw [← sum_pot (cw W (kv 0) p) (r % p) m] at hw
    simp only [brE1, KExpr.evalN]
    rw [hw]
    omega

/-- **`Real` for the row `E₂`** (Theorem 7, `p ≤ r`, `N ≤ 2p`), for each of the five symmetric duals. -/
theorem real_E2 (v u : ℤ) (hv : v ≠ 0) {W : Vec} (hW : W ∈ vecs) : Real v u (brE2 W) := by
  intro r p _ S kv hr hr0 hPb hN0 hN hk hcond
  have hp5 := p2_hp5 hPb
  have hpv := p2_not_dvd hv hN0
  have hp0 : 0 < p := by omega
  have hc1 := holds_ns (hcond ⟨1, -1, 0, [], 0, false⟩ (by simp [brE2]))
  have hc2 := holds_ns (hcond ⟨-1, 2, -2, [], 0, false⟩ (by simp [brE2]))
  have hg := holds_ns (hcond gGuard (by simp [brE2]))
  have hN' := p2_guard hr (p2_p920 hN0) (by simp at hg; omega)
  obtain ⟨m, hmdef⟩ : ∃ m, m = p2G.borderSize r := ⟨_, rfl⟩
  rw [← hmdef] at hN' hc1 hc2 hg ⊢
  have hpr : p ≤ r := by omega
  have hN2 : r + 2 * m ≤ 2 * p := by omega
  have hb1 : 0 < r / p := Nat.div_pos hpr hp0
  have hb2 : p * 1 ≤ p * (r / p) := Nat.mul_le_mul_left p hb1
  have hd := Nat.div_add_mod r p
  have hsp := Nat.mod_lt r hp0
  have hn : r % p + 2 * m ≤ 2 * p := by omega
  have hkp : kv 0 ≤ p := by omega
  have hdual : ∀ i j, i < m → j < m →
      w3 (cell p u (r + 2 * i)) (cell p u (r + 2 * j + 1)) ≤
        cw W (kv 0) p (r % p + 2 * i) + cw W (kv 0) p (r % p + 2 * j + 1) := by
    intro i j hi hj
    have e1 : r + 2 * i = p * (r / p) + (r % p + 2 * i) := by omega
    have e2 : r + 2 * j + 1 = p * (r / p) + (r % p + 2 * j + 1) := by omega
    have := dual_cw hW hp0 hk u (r / p) (r % p + 2 * i) (r % p + 2 * j + 1) (by omega) (by omega)
    rw [← e1, ← e2] at this
    exact this
  refine ⟨4 * r - 2 * p + 2 * m + ∑ i ∈ range m, cw W (kv 0) p (r % p + 2 * i) +
      ∑ j ∈ range m, cw W (kv 0) p (r % p + 2 * j + 1), ?_, ?_⟩
  · rw [p2Q_eq_m v u r hr S (hmdef ▸ p2_k_eq r)]
    exact row_E2 (p := p) v u hpv hp5 hpr hN2 hN' (fun a : S => ((a.1 : (p2G.geometry r).C) : ℕ))
      (p2Q_inj r S) (p2Q_lt r hr S) (fun i => cw W (kv 0) p (r % p + 2 * i))
      (fun j => cw W (kv 0) p (r % p + 2 * j + 1)) hdual
  · have hw := wsum_eval W r p m kv hkp hn
    rw [← sum_pot (cw W (kv 0) p) (r % p) m] at hw
    simp only [brE2, KExpr.evalN]
    rw [hw]
    omega

end CatalanCore.Uniform.Bank.Plane2.Content

#print axioms CatalanCore.Uniform.Bank.Plane2.Content.p2_guard
#print axioms CatalanCore.Uniform.Bank.Plane2.Content.dual_cw
#print axioms CatalanCore.Uniform.Bank.Plane2.Content.sum_cw
#print axioms CatalanCore.Uniform.Bank.Plane2.Content.real_E1
#print axioms CatalanCore.Uniform.Bank.Plane2.Content.real_E2
