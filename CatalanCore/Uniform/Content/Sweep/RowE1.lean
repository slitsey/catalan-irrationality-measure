module

public import CatalanCore.Uniform.Content.Sweep.RowNodes

@[expose] public section

/-!
# Row `E₁` (lane H, wave H2b; ledger P206)

`PLANE2-SIMPLIFICATION` Theorem 6: for `p > 2m` (`k = 0`, `k' = 0`, `κ = ⌊r/p⌋ + 1`, `ξ = X`) and
potentials `uX`, `uY` on the window rows `r + 2 i` and columns `r + 2 j + 1` with `W₃ ≤ uX i + uY j`,
every coefficient of the determinant of every member (any retained set `c` of common nodes below `r`) has
`p`-adic denominator at most `3 r + ∑ uX + ∑ uY`.  Hypotheses: `p ≥ 5`, `p ∤ v`, `p² > 2 (r + 2m) + 2p`;
no table and no (ND).

The virtual nodes `[r + 2m, κ p)` are labels of both types.  With the integer potentials
`φR = 1, φC = 2` on X-parity virtual nodes and `φR = 2, φC = 1` on Y-parity ones (so `φR + φC = 3` on each,
the congruent weight), every pair of labels is covered (`e1_pair`): the class of a label (`oc_node`)
agrees across rows and columns exactly when the parities match, which is what the split uses.  The sum
condition of `RowNodes.member_gle_P` is an equality, checked pointwise on nodes (`e1_point`).
-/

open Polynomial Finset Matrix CatalanCore.Basic CatalanCore.Arith.Hybrid
open CatalanCore.Uniform.Support CatalanCore.Uniform.Content.Sweep.Gen

namespace CatalanCore.Uniform.Content.Sweep

section E1Tools

variable {p : ℕ} [hp : Fact p.Prime] {u : ℤ}

/-- The class of a row-type label node (system `π = (r+1) % 2`). -/
theorem ocR_eq (hodd : p % 2 = 1) (κ r n : ℕ) :
    oc p κ ((r + 1) % 2) (n % p) =
      if n % 2 = (r + 1) % 2 then (n / p + κ) % 2 else (n / p + κ + 1) % 2 :=
  oc_node hodd (by omega) n

/-- The class of a column-type label node (system `1 - π`). -/
theorem ocC_eq (hodd : p % 2 = 1) (κ r n : ℕ) :
    oc p κ (1 - (r + 1) % 2) (n % p) =
      if n % 2 = r % 2 then (n / p + κ) % 2 else (n / p + κ + 1) % 2 := by
  have h := oc_node (p := p) hodd (σ := 1 - (r + 1) % 2) (κ := κ) (by omega) n
  rw [h]
  have e : (1 - (r + 1) % 2) = r % 2 := by omega
  rw [e]

/-- `Wlab` is at most the cell weight when the patterns agree in one period. -/
theorem Wlab_le_w3 (kR kC : Bool) (oR oC n n' : ℕ) (hnc : n % p ≠ n' % p)
    (hpat : n / p = n' / p → kR = kC ∧ oR = oC) :
    Wlab u p kR kC oR oC n n' ≤ w3 (cell p u n) (cell p u n') := by
  unfold Wlab w3 cell
  rw [if_neg hnc]
  by_cases hper : n / p = n' / p
  · obtain ⟨h1, h2⟩ := hpat hper
    by_cases hh : half p u n = half p u n'
    · simp [h1, h2, hper, hh]
    · simp [h1, h2, hper, hh]
  · have : ¬ (kR = kC ∧ oR = oC ∧ n / p = n' / p) := fun h => hper h.2.2
    simp [this, hper]

theorem cong_eq {n n' : ℕ} (h1 : n < n' + p) (h2 : n' < n + p) (h : n % p = n' % p) : n = n' := by
  have hd := (dvd_sub_iff (p := p) n n').2 h
  have : ((n : ℤ) - n') = 0 := by
    apply Int.eq_zero_of_abs_lt_dvd hd
    rw [abs_lt]
    constructor <;> omega
  omega

theorem period_ne {n n' : ℕ} (h : n / p = n' / p) (hne : n ≠ n') : n % p ≠ n' % p := by
  intro hm
  apply hne
  have e1 := Nat.div_add_mod n p
  have e2 := Nat.div_add_mod n' p
  rw [h, hm] at e1
  omega


end E1Tools

section E1Pot

variable {p : ℕ} [hp : Fact p.Prime] {u : ℤ}

/-- Potential split of the virtual nodes: `1` on X-parity nodes, `2` on Y-parity nodes. -/
def a1 (r t : ℕ) : ℕ := if (t - r) % 2 = 0 then 1 else 2

def phiR1 (r m : ℕ) (uX : ℕ → ℕ) (t : ℕ) : ℕ :=
  if t < r then 3 else if t < r + 2 * m then (if (t - r) % 2 = 0 then uX ((t - r) / 2) else 0) else a1 r t

def phiC1 (r m : ℕ) (uY : ℕ → ℕ) (t : ℕ) : ℕ :=
  if t < r then 3 else if t < r + 2 * m then (if (t - r) % 2 = 1 then uY ((t - r) / 2) else 0) else 3 - a1 r t

theorem e1_pair (hodd : p % 2 = 1) {r m κ : ℕ} (hm : 2 * m < p) (hκ1 : r < κ * p) (hκ2 : (κ - 1) * p ≤ r)
    (hκ0 : 1 ≤ κ) (uX uY : ℕ → ℕ)
    (hdual : ∀ i j, i < m → j < m → w3 (cell p u (r + 2 * i)) (cell p u (r + 2 * j + 1)) ≤ uX i + uY j)
    (n n' : ℕ) (kR kC : Bool)
    (hn : (r ≤ n ∧ (n - r) % 2 = 0 ∧ n < r + 2 * m) ∨ (r + 2 * m ≤ n ∧ n < κ * p))
    (hn' : (r ≤ n' ∧ (n' - r) % 2 = 1 ∧ n' < r + 2 * m) ∨ (r + 2 * m ≤ n' ∧ n' < κ * p))
    (hkR : kR = true ↔ κ * p ≤ n) (hkC : kC = true ↔ κ * p ≤ n') :
    Wlab u p kR kC (oc p κ ((r + 1) % 2) (n % p)) (oc p κ (1 - (r + 1) % 2) (n' % p)) n n' ≤
      phiR1 r m uX n + phiC1 r m uY n' := by
  have hp0 : 0 < p := hp.out.pos
  have hpR := ocR_eq (p := p) hodd κ r n
  have hpC := ocC_eq (p := p) hodd κ r n'
  -- periods of the nodes below `κ p` that are at least `r`
  have hper : ∀ x, r ≤ x → x < κ * p → x / p = κ - 1 := by
    intro x h1 h2
    apply le_antisymm
    · have : x / p < κ := (Nat.div_lt_iff_lt_mul hp0).2 h2
      omega
    · rw [Nat.le_div_iff_mul_le hp0]; omega
  have hkind : ∀ x : ℕ, (κ * p ≤ x ↔ κ ≤ x / p) := fun x => (Nat.le_div_iff_mul_le hp0).symm
  have hbool : n / p = n' / p → kR = kC := by
    intro h
    have : (κ * p ≤ n ↔ κ * p ≤ n') := by rw [hkind, hkind, h]
    exact Bool.eq_iff_iff.2 ((hkR.trans this).trans hkC.symm)
  rcases hn with ⟨hn1, hn2, hn3⟩ | ⟨hn1, hn2⟩ <;> rcases hn' with ⟨hm1, hm2, hm3⟩ | ⟨hm1, hm2⟩
  · -- window row, window column
    have hne : n % p ≠ n' % p := by
      intro h; have := cong_eq (by omega) (by omega) h; omega
    have h1 : phiR1 r m uX n = uX ((n - r) / 2) := by
      unfold phiR1; rw [if_neg (by omega), if_pos hn3, if_pos hn2]
    have h2 : phiC1 r m uY n' = uY ((n' - r) / 2) := by
      unfold phiC1; rw [if_neg (by omega), if_pos hm3, if_pos hm2]
    rw [h1, h2]
    refine le_trans (Wlab_le_w3 kR kC _ _ n n' hne ?_) ?_
    · intro hper'
      refine ⟨hbool hper', ?_⟩
      rw [hpR, hpC, if_neg (by omega), if_neg (by omega), hper']
    · have := hdual ((n - r) / 2) ((n' - r) / 2) (by omega) (by omega)
      have e1 : r + 2 * ((n - r) / 2) = n := by omega
      have e2 : r + 2 * ((n' - r) / 2) + 1 = n' := by omega
      rw [e1, e2] at this; exact this
  · -- window row, virtual column
    have hne : n % p ≠ n' % p :=
      period_ne (by rw [hper n hn1 (by omega), hper n' (by omega) hm2]) (by omega)
    have h1 : phiR1 r m uX n = uX ((n - r) / 2) := by
      unfold phiR1; rw [if_neg (by omega), if_pos hn3, if_pos hn2]
    have h2 : phiC1 r m uY n' = 3 - a1 r n' := by
      unfold phiC1; rw [if_neg (by omega), if_neg (by omega)]
    rw [h1, h2]
    have hle := Wlab_le_w3 (u := u) kR kC (oc p κ ((r + 1) % 2) (n % p)) (oc p κ (1 - (r + 1) % 2) (n' % p)) n n' hne
    have hle2 : Wlab u p kR kC (oc p κ ((r + 1) % 2) (n % p)) (oc p κ (1 - (r + 1) % 2) (n' % p)) n n' ≤ 2 := by
      unfold Wlab; rw [if_neg hne]; split_ifs <;> omega
    unfold a1
    by_cases hpar : (n' - r) % 2 = 0
    · rw [if_pos hpar]; omega
    · rw [if_neg hpar]
      have := hle (by
        intro hper'
        refine ⟨hbool hper', ?_⟩
        rw [hpR, hpC, if_neg (by omega), if_neg (by omega), hper'])
      have h3 : w3 (cell p u n) (cell p u n') ≤ 1 := by
        unfold w3 cell
        have hp' : n / p = n' / p := by rw [hper n hn1 (by omega), hper n' (by omega) hm2]
        simp only [hp', if_true]
        split_ifs <;> omega
      omega
  · -- virtual row, window column
    have hne : n % p ≠ n' % p :=
      period_ne (by rw [hper n (by omega) hn2, hper n' hm1 (by omega)]) (by omega)
    have h1 : phiR1 r m uX n = a1 r n := by
      unfold phiR1; rw [if_neg (by omega), if_neg (by omega)]
    have h2 : phiC1 r m uY n' = uY ((n' - r) / 2) := by
      unfold phiC1; rw [if_neg (by omega), if_pos hm3, if_pos hm2]
    rw [h1, h2]
    have hle := Wlab_le_w3 (u := u) kR kC (oc p κ ((r + 1) % 2) (n % p)) (oc p κ (1 - (r + 1) % 2) (n' % p)) n n' hne
    have hle2 : Wlab u p kR kC (oc p κ ((r + 1) % 2) (n % p)) (oc p κ (1 - (r + 1) % 2) (n' % p)) n n' ≤ 2 := by
      unfold Wlab; rw [if_neg hne]; split_ifs <;> omega
    unfold a1
    by_cases hpar : (n - r) % 2 = 0
    · rw [if_pos hpar]
      have := hle (by
        intro hper'
        refine ⟨hbool hper', ?_⟩
        rw [hpR, hpC, if_neg (by omega), if_neg (by omega), hper'])
      have h3 : w3 (cell p u n) (cell p u n') ≤ 1 := by
        unfold w3 cell
        have hp' : n / p = n' / p := by rw [hper n (by omega) hn2, hper n' hm1 (by omega)]
        simp only [hp', if_true]
        split_ifs <;> omega
      omega
    · rw [if_neg hpar]; omega
  · -- virtual row, virtual column
    have h1 : phiR1 r m uX n = a1 r n := by
      unfold phiR1; rw [if_neg (by omega), if_neg (by omega)]
    have h2 : phiC1 r m uY n' = 3 - a1 r n' := by
      unfold phiC1; rw [if_neg (by omega), if_neg (by omega)]
    rw [h1, h2]
    have hle3 := Wlab_le u p kR kC (oc p κ ((r + 1) % 2) (n % p)) (oc p κ (1 - (r + 1) % 2) (n' % p)) n n'
    by_cases hnn : n = n'
    · subst hnn; unfold a1; split_ifs <;> omega
    · have hne : n % p ≠ n' % p :=
        period_ne (by rw [hper n (by omega) hn2, hper n' (by omega) hm2]) hnn
      have hle2 : Wlab u p kR kC (oc p κ ((r + 1) % 2) (n % p)) (oc p κ (1 - (r + 1) % 2) (n' % p)) n n' ≤ 2 := by
        unfold Wlab; rw [if_neg hne]; split_ifs <;> omega
      unfold a1
      split_ifs <;> omega


end E1Pot

section E1Main

variable {p : ℕ} [hp : Fact p.Prime]

theorem sum_ite_range (B : ℕ) (s : Finset ℕ) (hs : s ⊆ Finset.range B) (f : ℕ → ℕ) :
    ∑ t ∈ Finset.range B, (if t ∈ s then f t else 0) = ∑ t ∈ s, f t := by
  rw [← Finset.sum_filter]
  congr 1
  ext t
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨_, h⟩; exact h
  · intro h; exact ⟨Finset.mem_range.1 (hs h), h⟩

/-- Window nodes of X parity / Y parity. -/
def FXs (r m : ℕ) : Finset ℕ := (Finset.Ico r (r + 2 * m)).filter (fun t => (t - r) % 2 = 0 ∧ r ≤ t)
def FYs (r m : ℕ) : Finset ℕ := (Finset.Ico r (r + 2 * m)).filter (fun t => (t - r) % 2 = 1 ∧ r ≤ t)

/-- The pointwise comparison behind the sum condition of row `E₁`. -/
theorem e1_point (r m κ : ℕ) (uX uY : ℕ → ℕ) (t : ℕ) :
    ((if t ∈ TRs p κ 0 r m then phiR1 r m uX t else 0) + (if t ∈ ORs p κ 0 r m then phiR1 r m uX t else 0) +
      (if t ∈ TCs p κ 0 r m then phiC1 r m uY t else 0) + (if t ∈ OCs p κ 0 r m then phiC1 r m uY t else 0) +
      3 * (if t ∈ FXs r m then 1 else 0)) ≤
    ((if t ∈ FXs r m then phiR1 r m uX t else 0) +
      (if t ∈ FYs r m then phiC1 r m uY t else 0) +
      3 * ((if t ∈ TRs p κ 0 r m then 1 else 0) + (if t ∈ ORs p κ 0 r m then 1 else 0))) := by
  unfold TRs TCs ORs OCs Tdel FXs FYs phiR1 phiC1 a1
  simp only [Finset.mem_filter, Finset.mem_Ico, mul_zero, add_zero]
  split_ifs <;> omega

end E1Main

section E1Thm

variable {p : ℕ} [hp : Fact p.Prime]

/-- **Row `E₁`** (`PLANE2-SIMPLIFICATION` Theorem 6, `p > 2m`): for every retained set `c` of common nodes
below `r` and potentials `uX`, `uY` on the window rows and columns with `W₃ ≤ uX + uY`, every coefficient
of the determinant of the member has `p`-adic denominator at most `3 r + ∑ uX + ∑ uY`.  The prime `p ≥ 5`
satisfies `p² > 2 N + 2 p` (`N = r + 2m`) and `p ∤ v`; nothing else (no table). -/
theorem row_E1 (v u : ℤ) (hpv : ¬ (p : ℤ) ∣ v) (hodd : p % 2 = 1) (hp5 : 5 ≤ p)
    {r m : ℕ} (hm : 2 * m < p) (hN : 2 * (r + 2 * m) + 2 * p < p * p)
    {ι : Type} [Fintype ι] [DecidableEq ι] (c : ι → ℕ) (hcinj : Function.Injective c)
    (hcr : ∀ i, c i < r) (uX uY : ℕ → ℕ)
    (hdual : ∀ i j, i < m → j < m → w3 (cell p u (r + 2 * i)) (cell p u (r + 2 * j + 1)) ≤ uX i + uY j) :
    GLE p (3 * r + ∑ i ∈ Finset.range m, uX i + ∑ j ∈ Finset.range m, uY j)
      (seqFullN (fS v u) (eS v u) c
        (fun i : Fin m => r + 2 * (i : ℕ)) (fun i : Fin m => r + 2 * (i : ℕ) + 1) (X : ℚ[X])).det := by
  classical
  have hp0 : 0 < p := hp.out.pos
  obtain ⟨κ, hκdef⟩ : ∃ κ, κ = r / p + 1 := ⟨_, rfl⟩
  have hκ1 : r < κ * p := by
    rw [hκdef, Nat.mul_comm]; exact Nat.lt_mul_div_succ r hp0
  have hκ2 : (κ - 1) * p ≤ r := by
    rw [hκdef, Nat.add_sub_cancel]; exact Nat.div_mul_le_self r p
  have hκ0 : 1 ≤ κ := by rw [hκdef]; exact Nat.le_add_left 1 _
  obtain ⟨N', hN'def⟩ : ∃ N', N' = ((r + 2 * m) / p + 1) * p := ⟨_, rfl⟩
  have hN'le : N' ≤ (r + 2 * m) + p := by
    rw [hN'def, Nat.add_mul, Nat.one_mul]
    have := Nat.div_mul_le_self (r + 2 * m) p
    omega
  have hN2 : 2 * N' < p * p := by omega
  have hH : (κ + 2 * 0) * p ≤ N' := by
    rw [hN'def, hκdef]
    simp only [mul_zero, add_zero]
    exact Nat.mul_le_mul_right p (Nat.add_le_add_right (Nat.div_le_div_right (by omega)) 1)
  have hcompl : ∀ n, n < r + 2 * m → (n / p + 1) * p ≤ N' := by
    intro n hn
    rw [hN'def]
    exact Nat.mul_le_mul_right p (Nat.add_le_add_right (Nat.div_le_div_right (by omega)) 1)
  have hκH : κ * p ≤ N' := by simpa using hH
  refine member_gle_P (p := p) (k' := 0) (κ := κ) v u hpv hodd hp5 hN2 hκ1 hH hcompl c hcinj hcr
    (phiR1 r m uX) (phiC1 r m uY) ?_ ?_ ?_ ?_ ?_ (3 * r + ∑ i ∈ Finset.range m, uX i + ∑ j ∈ Finset.range m, uY j) ?_
  · intro t ht; constructor <;> simp [phiR1, phiC1, ht]
  · intro n hn n' hn'
    simp only [TRs, TCs, Tdel, Finset.mem_filter, Finset.mem_Ico, mul_zero, add_zero] at hn hn'
    exact e1_pair hodd hm hκ1 hκ2 hκ0 uX uY hdual n n' false false (by omega) (by omega)
      ⟨fun h => absurd h (by simp), fun h => by omega⟩ ⟨fun h => absurd h (by simp), fun h => by omega⟩
  · intro n hn n' hn'
    simp only [TRs, OCs, Tdel, Finset.mem_filter, Finset.mem_Ico, mul_zero, add_zero] at hn hn'
    exact e1_pair hodd hm hκ1 hκ2 hκ0 uX uY hdual n n' false true (by omega) (by omega)
      ⟨fun h => absurd h (by simp), fun h => by omega⟩ ⟨fun _ => by omega, fun _ => rfl⟩
  · intro n hn n' hn'
    simp only [ORs, TCs, Tdel, Finset.mem_filter, Finset.mem_Ico, mul_zero, add_zero] at hn hn'
    exact e1_pair hodd hm hκ1 hκ2 hκ0 uX uY hdual n n' true false (by omega) (by omega)
      ⟨fun _ => by omega, fun _ => rfl⟩ ⟨fun h => absurd h (by simp), fun h => by omega⟩
  · intro n hn n' hn'
    simp only [ORs, OCs, Finset.mem_filter, Finset.mem_Ico, mul_zero, add_zero] at hn hn'
    exact e1_pair hodd hm hκ1 hκ2 hκ0 uX uY hdual n n' true true (by omega) (by omega)
      ⟨fun _ => by omega, fun _ => rfl⟩ ⟨fun _ => by omega, fun _ => rfl⟩
  · -- the sum condition
    have hX : ∑ i ∈ Finset.range m, uX i = ∑ t ∈ FXs r m, phiR1 r m uX t := by
      have h := sum_stride r m 0 (by norm_num) (fun t => r ≤ t) (phiR1 r m uX)
      rw [FXs, ← h]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi := Finset.mem_range.1 hi
      rw [if_pos (by omega)]
      unfold phiR1
      rw [if_neg (by omega), if_pos (by omega), if_pos (by omega)]
      congr 1; omega
    have hY : ∑ i ∈ Finset.range m, uY i = ∑ t ∈ FYs r m, phiC1 r m uY t := by
      have h := sum_stride r m 1 (by norm_num) (fun t => r ≤ t) (phiC1 r m uY)
      rw [FYs, ← h]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi := Finset.mem_range.1 hi
      rw [if_pos (by omega)]
      unfold phiC1
      rw [if_neg (by omega), if_pos (by omega), if_pos (by omega)]
      congr 1; omega
    have hcX : (FXs r m).card = m := by
      have h := sum_stride r m 0 (by norm_num) (fun t => r ≤ t) (fun _ => 1)
      rw [FXs, Finset.card_eq_sum_ones, ← h]
      simp
    set B := κ * p + r + 2 * m with hB
    have hsTR : TRs p κ 0 r m ⊆ Finset.range B := by
      intro t ht
      simp only [TRs, Tdel, Finset.mem_filter, Finset.mem_Ico, mul_zero, add_zero] at ht
      rw [Finset.mem_range]; omega
    have hsOR : ORs p κ 0 r m ⊆ Finset.range B := by
      intro t ht
      simp only [ORs, Finset.mem_filter, Finset.mem_Ico] at ht
      rw [Finset.mem_range]; omega
    have hsTC : TCs p κ 0 r m ⊆ Finset.range B := by
      intro t ht
      simp only [TCs, Tdel, Finset.mem_filter, Finset.mem_Ico, mul_zero, add_zero] at ht
      rw [Finset.mem_range]; omega
    have hsOC : OCs p κ 0 r m ⊆ Finset.range B := by
      intro t ht
      simp only [OCs, Finset.mem_filter, Finset.mem_Ico] at ht
      rw [Finset.mem_range]; omega
    have hsFX : FXs r m ⊆ Finset.range B := by
      intro t ht
      simp only [FXs, Finset.mem_filter, Finset.mem_Ico] at ht
      rw [Finset.mem_range]; omega
    have hsFY : FYs r m ⊆ Finset.range B := by
      intro t ht
      simp only [FYs, Finset.mem_filter, Finset.mem_Ico] at ht
      rw [Finset.mem_range]; omega
    have hle := Finset.sum_le_sum (s := Finset.range B) (fun t _ => e1_point (p := p) r m κ uX uY t)
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hle
    rw [sum_ite_range B _ hsTR (phiR1 r m uX), sum_ite_range B _ hsOR (phiR1 r m uX),
      sum_ite_range B _ hsTC (phiC1 r m uY), sum_ite_range B _ hsOC (phiC1 r m uY),
      sum_ite_range B _ hsFX (fun _ => 1), sum_ite_range B _ hsFX (phiR1 r m uX),
      sum_ite_range B _ hsFY (phiC1 r m uY), sum_ite_range B _ hsTR (fun _ => 1),
      sum_ite_range B _ hsOR (fun _ => 1)] at hle
    simp only [Finset.sum_const, smul_eq_mul, mul_one] at hle
    rw [hcX] at hle
    omega

end E1Thm

end CatalanCore.Uniform.Content.Sweep

#print axioms CatalanCore.Uniform.Content.Sweep.row_E1
