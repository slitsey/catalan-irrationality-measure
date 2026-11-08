module

public import CatalanCore.Uniform.Content.Sweep.Cells

@[expose] public section

/-!
# The cell action (lane H, wave H2; ledger P202)

**Lemma 2** of the sweep (`PLANE2-SIMPLIFICATION` §1.2).  Let `p ≥ 5` be prime, `(v, u)` integers, `κ ≥ 1`,
`K = [0, κp)` the union of the first `κ` complete periods, `N ≥ κp` with `2N < p²`, `H = M + p⁻³ ξ · Id`
on `[0, N)²` with `M` the Löwner matrix of the plane 2 datum and `ξ` an element of any commutative
`ℤ_(p)`-algebra `R` (for the paper `R = 𝒪 = ℤ_(p)[X]_(p)`, `ξ = X` or `pX`; nothing but the algebra
structure is used).  A function `φ` on the cells `(j, h)` (`j < κ`, `h ∈ {0, 1}`) with `φ(j, 0) ≡ φ(j, 1)`
(mod `p`) is lifted to the nodes by `φ̃ = φ ∘ cell`.  Then for every node `u < N`

  `p³ (H φ̃)(u) ≡ (𝐁 φ)(cell u)  (mod p²)`,

where

  `(𝐁 φ)(l, h) = [l < κ] (ξ + p³ G(l, h)) φ(l, h) + ∑_{j < κ, j ≠ l} p² (S(l,h) - S(j,h))/(l - j) · φ(j, h)`,

`S`, `G` the polar sums of `Sweep.Cells` at the cell (`Scell`, `Gcell`), and `𝐁` maps these functions to
functions of the same kind on the cells of every period (`cellAction_mem_V`).

The proof splits the sum over `t ∈ K` by the cell of `t` against the cell of `u`: the same cell and the other
half of the period contribute `0` and `p³ G φ` modulo `p²`; every other period contributes
`φ(j, h) s_h/(j - l) + p ∑_{h'} φ(j,h') s_{h'} ε_{h'}`, with `s_{h'} = p²(S(j,h') - S(l,h))` and
`ε_{h'}` the sum of `1/(t - u)` over the nodes `t ≠ t_u` of the cell (`t_u ≡ u` the unique node of the period
congruent to `u`), and `ε_0 + ε_1 ≡ 0` because `t - u` runs over the nonzero residues (`∑ v⁻¹ ≡ 0`).
-/

open Polynomial Finset Matrix CatalanCore.Basic CatalanCore.Arith.Hybrid
open CatalanCore.Uniform.Support

namespace CatalanCore.Uniform.Content.Sweep

section Alg

variable {p : ℕ} [hp : Fact p.Prime]

/-- `x ∈ p^k ℤ_(p)`. -/
def Dv (p : ℕ) [Fact p.Prime] (k : ℕ) (x : ℚ) : Prop := x / (p : ℚ) ^ k ∈ LocRing p

variable {k : ℕ} {x y : ℚ}

theorem Dv.intro (hy : y ∈ LocRing p) : Dv p k ((p : ℚ) ^ k * y) := by
  unfold Dv
  have : (p : ℚ) ^ k ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)
  rwa [mul_div_cancel_left₀ _ this]

theorem Dv.add (hx : Dv p k x) (hy : Dv p k y) : Dv p k (x + y) := by
  unfold Dv at *; rw [add_div]; exact (LocRing p).add_mem hx hy

theorem Dv.sub (hx : Dv p k x) (hy : Dv p k y) : Dv p k (x - y) := by
  unfold Dv at *; rw [sub_div]; exact (LocRing p).sub_mem hx hy

theorem Dv.neg (hx : Dv p k x) : Dv p k (-x) := by
  unfold Dv at *; rw [neg_div]; exact (LocRing p).neg_mem hx

theorem Dv.zero : Dv p k 0 := by unfold Dv; simpa using (LocRing p).zero_mem

theorem Dv.mono {k' : ℕ} (h : k' ≤ k) (hx : Dv p k x) : Dv p k' x := by
  unfold Dv at *
  have e : x / (p : ℚ) ^ k' = (p : ℚ) ^ (k - k') * (x / (p : ℚ) ^ k) := by
    have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
    have : (p : ℚ) ^ k = (p : ℚ) ^ k' * (p : ℚ) ^ (k - k') := by rw [← pow_add]; congr 1; omega
    rw [this]; field_simp
  rw [e]
  exact (LocRing p).mul_mem (by exact_mod_cast int_mem_locRing (ℓ := p) ((p : ℤ) ^ (k - k'))) hx

theorem Dv.sum {ι : Type*} (s : Finset ι) (f : ι → ℚ) (h : ∀ i ∈ s, Dv p k (f i)) :
    Dv p k (∑ i ∈ s, f i) := by
  unfold Dv at *
  have e : (∑ i ∈ s, f i) / (p : ℚ) ^ k = ∑ i ∈ s, f i / (p : ℚ) ^ k := by
    simp only [div_eq_mul_inv, Finset.sum_mul]
  rw [e]; exact (LocRing p).sum_mem h

theorem Dv.mul_mem (hy : y ∈ LocRing p) (hx : Dv p k x) : Dv p k (y * x) := by
  unfold Dv at *
  rw [mul_div_assoc]; exact (LocRing p).mul_mem hy hx

theorem Dv.mem (hx : Dv p k x) : x ∈ LocRing p := by
  have := (Dv.mono (Nat.zero_le k) hx)
  simpa [Dv] using this

theorem Dv.of_Vp {w : ℕ} (hx : Vp p w x) : Dv p k ((p : ℚ) ^ (w + k) * x) := by
  have : (p : ℚ) ^ (w + k) * x = (p : ℚ) ^ k * ((p : ℚ) ^ w * x) := by ring
  rw [this]; exact Dv.intro hx

end Alg

/-! ### Sums over cells -/

section CellSums

variable {p : ℕ} {u : ℤ}

/-- The sum of `F` over the nodes of the cell `c = (j, h')`. -/
def cellSum {α : Type*} [AddCommMonoid α] (p : ℕ) (u : ℤ) (c : ℕ × ℕ) (F : ℕ → α) : α :=
  ∑ r ∈ range p, if half p u r = c.2 then F (c.1 * p + r) else 0

theorem half_eq (r : ℕ) : half p u r = 0 ∨ half p u r = 1 := by
  unfold half; split_ifs <;> simp

theorem half_node (hp0 : 0 < p) (j r : ℕ) (hr : r < p) : half p u (j * p + r) = half p u r := by
  unfold half
  have : (j * p + r) % p = r := by rw [Nat.mul_comm, Nat.mul_add_mod]; exact Nat.mod_eq_of_lt hr
  rw [this, Nat.mod_eq_of_lt hr]

theorem cell_node (hp0 : 0 < p) (j r : ℕ) (hr : r < p) : cell p u (j * p + r) = (j, half p u r) := by
  unfold cell
  rw [half_node hp0 j r hr]
  have : (j * p + r) / p = j := by
    rw [Nat.mul_comm, Nat.mul_add_div hp0, Nat.div_eq_of_lt hr]; simp
  rw [this]

theorem sum_range_mul {α : Type*} [AddCommMonoid α] (F : ℕ → α) (κ : ℕ) :
    ∑ t ∈ range (κ * p), F t = ∑ j ∈ range κ, ∑ r ∈ range p, F (j * p + r) := by
  induction κ with
  | zero => simp
  | succ κ ih =>
    have e : (κ + 1) * p = κ * p + p := by ring
    rw [e, Finset.sum_range_add, ih, Finset.sum_range_succ]

theorem sum_range_cells {α : Type*} [AddCommMonoid α] (G : ℕ → α) :
    ∑ r ∈ range p, G r = (∑ r ∈ range p, if half p u r = 0 then G r else 0) +
      ∑ r ∈ range p, if half p u r = 1 then G r else 0 := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  rcases half_eq (p := p) (u := u) r with h | h <;> simp [h]

theorem sum_nodes_cells {α : Type*} [AddCommMonoid α] (F : ℕ → α) (κ : ℕ) :
    ∑ t ∈ range (κ * p), F t = ∑ j ∈ range κ, (cellSum p u (j, 0) F + cellSum p u (j, 1) F) := by
  rw [sum_range_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [sum_range_cells]
  rfl

end CellSums

/-! ### Inverses of integers in `ℤ_(p)`, and the reindexing by residues -/

section InvZ

variable {p : ℕ} [hp : Fact p.Prime]

theorem inv_int_mem {z : ℤ} (h : ¬ (p : ℤ) ∣ z) : (z : ℚ)⁻¹ ∈ LocRing p := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg z
  · have : ¬ p ∣ n := fun hd => h (Int.natCast_dvd_natCast.2 hd)
    simpa using inv_natCast_mem_locRing (ℓ := p) this
  · have : ¬ p ∣ n := fun hd => h (by
      rw [dvd_neg]; exact Int.natCast_dvd_natCast.2 hd)
    have := inv_natCast_mem_locRing (ℓ := p) this
    push_cast
    rw [inv_neg]; exact (LocRing p).neg_mem this

/-- `1/z` as an element of `ℤ_(p)`, and `0` if `p ∣ z`. -/
noncomputable def invZ (p : ℕ) [Fact p.Prime] (z : ℤ) : LocRing p :=
  if h : ¬ (p : ℤ) ∣ z then ⟨(z : ℚ)⁻¹, inv_int_mem h⟩ else 0

theorem coe_invZ (z : ℤ) : ((invZ p z : LocRing p) : ℚ) = if (p : ℤ) ∣ z then 0 else (z : ℚ)⁻¹ := by
  unfold invZ
  by_cases h : (p : ℤ) ∣ z <;> simp [h]

theorem redQ_invZ (z : ℤ) : redQ p (invZ p z) = (z : ZMod p)⁻¹ := by
  by_cases h : (p : ℤ) ∣ z
  · have h0 : (z : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd z p).2 h
    unfold invZ; simp [h, h0]
  · have hmem : (z : ℚ) ∈ LocRing p := int_mem_locRing z
    have e : invZ p z * (⟨(z : ℚ), hmem⟩ : LocRing p) = 1 := by
      apply Subtype.ext
      unfold invZ; rw [dif_pos h]
      have hz : (z : ℚ) ≠ 0 := by
        have : z ≠ 0 := fun h0 => h (h0 ▸ dvd_zero _)
        exact_mod_cast this
      simp [inv_mul_cancel₀ hz]
    have h1 := congrArg (redQ p) e
    rw [map_mul, map_one] at h1
    have h2 : redQ p (⟨(z : ℚ), hmem⟩ : LocRing p) = (z : ZMod p) := by
      rw [redQ_apply]; simp
    rw [h2] at h1
    exact eq_inv_of_mul_eq_one_left h1

/-- Summing a function of the residue over `p` consecutive integers is summing over `ZMod p`. -/
theorem sum_range_cast (H : ZMod p → ZMod p) (a : ℕ) :
    ∑ i ∈ range p, H ((a + i : ℕ) : ZMod p) = ∑ y : ZMod p, H y := by
  let φ : ℕ → ZMod p := fun i => ((a + i : ℕ) : ZMod p)
  have hinj : Set.InjOn φ (range p : Finset ℕ) := by
    intro i hi j hj hij
    have hi' := Finset.mem_range.1 (Finset.mem_coe.1 hi)
    have hj' := Finset.mem_range.1 (Finset.mem_coe.1 hj)
    have : ((a + i : ℕ) : ZMod p) = ((a + j : ℕ) : ZMod p) := hij
    rw [ZMod.natCast_eq_natCast_iff'] at this
    have h2 : i % p = j % p := Nat.ModEq.add_left_cancel' a (show a + i ≡ a + j [MOD p] from this)
    rwa [Nat.mod_eq_of_lt hi', Nat.mod_eq_of_lt hj'] at h2
  have himg : (range p).image φ = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_image_of_injOn hinj, Finset.card_range, ZMod.card]
  rw [← himg, Finset.sum_image hinj]

theorem sum_inv_zmod (hp5 : 5 ≤ p) : ∑ y : ZMod p, y⁻¹ = 0 := by
  have hcard : Fintype.card (ZMod p) = p := ZMod.card p
  have := Equiv.sum_comp (Equiv.inv (ZMod p)) (fun z => z ^ 1)
  simp only [pow_one, Equiv.inv_apply] at this
  rw [this]
  simpa using FiniteField.sum_pow_lt_card_sub_one (ZMod p) (i := 1) (by omega)

end InvZ

/-! ### Cell starts, `S` and `G` as functions of the cell -/

section CellFns

variable {p : ℕ} [hp : Fact p.Prime] (v u : ℤ)

/-- The first node of the cell `c = (j, h)`: `j p + h (p+1)/2`. -/
def cstart (p : ℕ) (c : ℕ × ℕ) : ℕ := c.1 * p + c.2 * ((p + 1) / 2)

theorem cstart_cell {u : ℤ} (hodd : p % 2 = 1) {c : ℕ × ℕ} (hc : c.2 ≤ 1) (hc0 : u = 0 → c.2 = 0) :
    cell p u (cstart p c) = c := by
  have hp0 : 0 < p := hp.out.pos
  obtain ⟨j, h⟩ := c
  simp only at hc hc0
  interval_cases h
  · simp only [cstart, zero_mul, add_zero]
    have := cell_node (u := u) hp0 j 0 hp0
    simpa [half] using this
  · have hu0 : u ≠ 0 := fun h => by have := hc0 h; omega
    have hm : (p + 1) / 2 < p := by have := hp.out.two_le; omega
    simp only [cstart, one_mul]
    rw [cell_node hp0 j _ hm]
    congr 1
    unfold half
    rw [Nat.mod_eq_of_lt hm]
    rw [if_neg hu0, if_pos (by omega)]

theorem cstart_le {u : ℤ} (hodd : p % 2 = 1) (t : ℕ) : cstart p (cell p u t) ≤ t := by
  have hp0 : 0 < p := hp.out.pos
  have h1 : (t / p) * p + t % p = t := by rw [Nat.mul_comm]; exact Nat.div_add_mod t p
  have h2 := Nat.mod_lt t hp0
  unfold cstart cell half
  simp only
  split_ifs with h h'
  · simp only [zero_mul, add_zero]; omega
  · simp only [one_mul]; omega
  · simp only [zero_mul, add_zero]; omega

/-- The polar sums `S`, `G` of a cell (the paper's `S(l,h)` and `G(l,h)`; `G = -PE` since the diagonal
entry of the Löwner matrix is `-e`). -/
noncomputable def Scell (p : ℕ) (c : ℕ × ℕ) : ℚ := PF v u p (cstart p c)
noncomputable def Gcell (p : ℕ) (c : ℕ × ℕ) : ℚ := - PE v u p (cstart p c)

theorem PF_eq_Scell (hodd : p % 2 = 1) (t : ℕ) : PF v u p t = Scell v u p (cell p u t) := by
  unfold Scell
  have hc : (cell p u t).2 ≤ 1 := by
    unfold cell half; simp only; split_ifs <;> omega
  have hc0 : u = 0 → (cell p u t).2 = 0 := fun h => by unfold cell half; simp [h]
  exact PF_eq_same_cell v u (cstart_le hodd t) (cstart_cell hodd hc hc0)

theorem PE_eq_Gcell (hodd : p % 2 = 1) (t : ℕ) : - PE v u p t = Gcell v u p (cell p u t) := by
  unfold Gcell
  have hc : (cell p u t).2 ≤ 1 := by
    unfold cell half; simp only; split_ifs <;> omega
  have hc0 : u = 0 → (cell p u t).2 = 0 := fun h => by unfold cell half; simp [h]
  rw [PE_eq_same_cell v u (cstart_le hodd t) (cstart_cell hodd hc hc0)]

end CellFns

/-! ### The entries `p³ M(n, t)` by cell -/

section KLevel

variable {p : ℕ} [hp : Fact p.Prime] (v u : ℤ) {N : ℕ}

/-- The Löwner entry of the plane 2 datum. -/
noncomputable abbrev Lm (a b : ℕ) : ℚ := lw (fS v u) (eS v u) a b

theorem Wt_le_three (a b : ℕ) : Wt p u a b ≤ 3 := by
  unfold Wt Wd w3; split_ifs <;> omega

theorem q_mem (hN : 2 * N < p * p) {a b : ℕ} (ha : a < N) (hb : b < N) :
    (p : ℚ) ^ 3 * Lm v u a b ∈ LocRing p :=
  (weight_table v u hN a b ha hb).mono (Wt_le_three u a b)

theorem Wt_same_cell {a b : ℕ} (hne : a ≠ b) (h : cell p u a = cell p u b) : Wt p u a b = 0 := by
  have hper : a / p = b / p := (Prod.mk.inj h).1
  have hmod : a % p ≠ b % p := fun hm => hne (by
    have h1 := Nat.div_add_mod a p
    have h2 := Nat.div_add_mod b p
    rw [hper, hm] at h1
    omega)
  unfold Wt; rw [if_neg hne, if_neg hmod]; unfold w3; rw [if_pos h]

theorem Wt_same_period {a b : ℕ} (hne : a ≠ b) (h : (cell p u a).1 = (cell p u b).1)
    (hc : cell p u a ≠ cell p u b) : Wt p u a b = 1 := by
  have hper : a / p = b / p := h
  have hmod : a % p ≠ b % p := fun hm => hne (by
    have h1 := Nat.div_add_mod a p
    have h2 := Nat.div_add_mod b p
    rw [hper, hm] at h1
    omega)
  unfold Wt; rw [if_neg hne, if_neg hmod]; unfold w3; rw [if_neg hc, if_pos h]

/-- Same cell, different nodes: `p³ M(n, t) ∈ p³ ℤ_(p)`. -/
theorem Dv_q_same_cell (hN : 2 * N < p * p) {a b : ℕ} (ha : a < N) (hb : b < N) (hne : a ≠ b)
    (h : cell p u a = cell p u b) : Dv p 3 ((p : ℚ) ^ 3 * Lm v u a b) := by
  have := weight_table v u hN a b ha hb
  rw [Wt_same_cell (u := u) hne h] at this
  exact Dv.intro (Vp.zero_iff.1 this)

/-- Same period, other half: `p³ M(n, t) ∈ p² ℤ_(p)`. -/
theorem Dv_q_same_period (hN : 2 * N < p * p) {a b : ℕ} (ha : a < N) (hb : b < N) (hne : a ≠ b)
    (h : (cell p u a).1 = (cell p u b).1) (hc : cell p u a ≠ cell p u b) :
    Dv p 2 ((p : ℚ) ^ 3 * Lm v u a b) := by
  have := weight_table v u hN a b ha hb
  rw [Wt_same_period (u := u) hne h hc] at this
  exact Dv.of_Vp this

/-- The diagonal entry: `p³ M(n, n) ≡ p³ G(cell n)  (mod p³)`. -/
theorem Dv_q_diag (hodd : p % 2 = 1) {a : ℕ} :
    Dv p 3 ((p : ℚ) ^ 3 * Lm v u a a - (p : ℚ) ^ 3 * Gcell v u p (cell p u a)) := by
  have e : (p : ℚ) ^ 3 * Lm v u a a - (p : ℚ) ^ 3 * Gcell v u p (cell p u a) =
      (p : ℚ) ^ 3 * (-RE v u p a) := by
    unfold Lm lw
    rw [if_pos rfl, e_eq v u (p := p), ← PE_eq_Gcell v u hodd a]
    ring
  rw [e]
  exact Dv.intro (by simpa using (LocRing p).neg_mem (RE_mem v u (p := p) a))

/-- Divided differences of `ρ` are `p`-integral. -/
theorem RF_div_mem (hp5 : 5 ≤ p) (hN : 2 * N < p * p) {a b : ℕ} (ha : a < N) (hb : b < N) (hne : a ≠ b) :
    (RF v u p b - RF v u p a) / ((b : ℚ) - a) ∈ LocRing p := by
  have lt_case : ∀ a b : ℕ, a < b → b < N → (RF v u p b - RF v u p a) / ((b : ℚ) - a) ∈ LocRing p := by
    intro a b hab hb
    by_cases hd : p ∣ b - a
    · obtain ⟨l, hl⟩ := hd
      have hl0 : 0 < l := by
        rcases Nat.eq_zero_or_pos l with h0 | h0
        · simp [h0] at hl; omega
        · exact h0
      have hlp : l < p := by
        by_contra hge
        have := Nat.mul_le_mul_left p (not_lt.1 hge)
        omega
      have hb' : b = a + l * p := by rw [Nat.mul_comm]; omega
      have h1 := regF_congr v u hp5 a l (p := p)
      rw [← hb'] at h1
      have hlq : ((b : ℚ) - a) = (l : ℚ) * p := by
        have : (b : ℚ) = a + l * p := by exact_mod_cast hb'
        linarith
      have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
      have hl0' : (l : ℚ) ≠ 0 := by exact_mod_cast hl0.ne'
      have e : (RF v u p b - RF v u p a) / ((b : ℚ) - a) =
          ((RF v u p b - RF v u p a) / p) * (l : ℚ)⁻¹ := by
        rw [hlq]; field_simp
      rw [e]
      exact (LocRing p).mul_mem h1 (inv_mem_of_lt hl0 hlp)
    · have hnd : ¬ p ∣ b - a := hd
      have e : ((b : ℚ) - a) = ((b - a : ℕ) : ℚ) := by rw [Nat.cast_sub hab.le]
      rw [e, div_eq_mul_inv]
      exact (LocRing p).mul_mem ((LocRing p).sub_mem (RF_mem v u b) (RF_mem v u a))
        (inv_natCast_mem_locRing hnd)
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · exact lt_case a b h hb
  · have := lt_case b a h ha
    have e : (RF v u p b - RF v u p a) / ((b : ℚ) - a) = (RF v u p a - RF v u p b) / ((a : ℚ) - b) := by
      have h1 : (a : ℚ) - b ≠ 0 := sub_ne_zero.2 (by exact_mod_cast hne)
      have h2 : (b : ℚ) - a ≠ 0 := sub_ne_zero.2 (by exact_mod_cast (Ne.symm hne))
      field_simp
      ring
    rw [e]; exact this

/-- `s(c) = p² (S(c) - S(cell n))`. -/
noncomputable def sdiff (p : ℕ) (n : ℕ) (c : ℕ × ℕ) : ℚ :=
  (p : ℚ) ^ 2 * (Scell v u p c - Scell v u p (cell p u n))

/-- The entry for a node `t` away from `n` is its polar part `p s(c(t))/(t - n)` plus `p³ ℤ_(p)`. -/
theorem q_decomp (hodd : p % 2 = 1) (hp5 : 5 ≤ p) (hN : 2 * N < p * p) {n t : ℕ} (hn : n < N) (ht : t < N)
    (hne : n ≠ t) :
    Dv p 3 ((p : ℚ) ^ 3 * Lm v u n t -
      (p : ℚ) * sdiff v u p n (cell p u t) * (((t : ℚ) - n)⁻¹)) := by
  have hD : ((t : ℚ) - n) ≠ 0 := sub_ne_zero.2 (by exact_mod_cast (Ne.symm hne))
  have hLm : Lm v u n t =
      ((PF v u p t - PF v u p n) + (RF v u p t - RF v u p n)) / ((t : ℚ) - n) := by
    unfold Lm lw
    rw [if_neg hne, f_eq v u (p := p), f_eq v u (p := p)]
    congr 1; ring
  have e : (p : ℚ) ^ 3 * Lm v u n t -
      (p : ℚ) * sdiff v u p n (cell p u t) * (((t : ℚ) - n)⁻¹) =
      (p : ℚ) ^ 3 * ((RF v u p t - RF v u p n) / ((t : ℚ) - n)) := by
    rw [hLm, sdiff, ← PF_eq_Scell v u hodd t, ← PF_eq_Scell v u hodd n]
    field_simp
    ring
  rw [e]
  exact Dv.intro (RF_div_mem v u hp5 hN hn ht hne)

end KLevel

/-! ### The sums `ε` of the inverse distances -/

section Eps

variable {p : ℕ} [hp : Fact p.Prime] (v u : ℤ)

theorem dvd_sub_iff (t n : ℕ) : (p : ℤ) ∣ (t : ℤ) - n ↔ t % p = n % p := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [sub_eq_zero]
  exact ZMod.natCast_eq_natCast_iff' t n p

/-- `ε_c(n)`: the sum of `1/(t - n)` over the nodes of the cell `c` not congruent to `n`. -/
noncomputable def eps (p : ℕ) [Fact p.Prime] (n : ℕ) (c : ℕ × ℕ) : ℚ :=
  cellSum p u c (fun t => ((invZ p ((t : ℤ) - n) : LocRing p) : ℚ))

/-- In a period other than that of `n`, the inverse distances to `n` over one cell are the single
congruent term `1/((j - l) p)` (in the cell of `n`'s residue) plus the integral `ε`. -/
theorem cell_inv_sum (n j h' : ℕ) :
    cellSum p u (j, h') (fun t => ((t : ℚ) - n)⁻¹) =
      (if h' = half p u n then ((((j : ℚ) - ((n / p : ℕ) : ℚ)) * p)⁻¹) else 0) + eps u p n (j, h') := by
  have hp0 : 0 < p := hp.out.pos
  unfold cellSum eps
  set ρ := n % p with hρ
  have hρp : ρ < p := Nat.mod_lt n hp0
  have hn : n = (n / p) * p + ρ := by
    have := Nat.div_add_mod n p; rw [Nat.mul_comm] at this; omega
  have hhalf : half p u ρ = half p u n := by
    unfold half; rw [Nat.mod_eq_of_lt hρp]
  have hterm : ∀ r ∈ range p,
      (if half p u r = (j, h').2 then (((j * p + r : ℕ) : ℚ) - n)⁻¹ else 0) =
        (if r = ρ then (if half p u r = (j, h').2 then ((((j : ℚ) - ((n / p : ℕ) : ℚ)) * p)⁻¹) else 0)
          else 0) +
        (if half p u r = (j, h').2 then ((invZ p (((j * p + r : ℕ) : ℤ) - n) : LocRing p) : ℚ) else 0) := by
    intro r hr
    have hrp : r < p := Finset.mem_range.1 hr
    by_cases hrρ : r = ρ
    · have hd : (p : ℤ) ∣ ((j * p + r : ℕ) : ℤ) - n := by
        rw [dvd_sub_iff, Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hrp]
        exact hrρ.trans hρ
      rw [coe_invZ, if_pos hd, if_pos hrρ]
      have : (((j * p + r : ℕ) : ℚ) - n) = ((j : ℚ) - ((n / p : ℕ) : ℚ)) * p := by
        have hn' : n = (n / p) * p + r := by rw [hrρ]; exact hn
        have hq : (n : ℚ) = ((n / p : ℕ) : ℚ) * p + r := by exact_mod_cast hn'
        push_cast; push_cast at hq; linarith
      rw [this]
      simp
    · have hnd : ¬ (p : ℤ) ∣ ((j * p + r : ℕ) : ℤ) - n := by
        rw [dvd_sub_iff, Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hrp]
        exact hrρ
      rw [coe_invZ, if_neg hnd, if_neg hrρ]
      push_cast
      simp
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_ite_eq' (range p) ρ]
  rw [if_pos (Finset.mem_range.2 hρp), hhalf]
  by_cases h : h' = half p u n
  · simp [h]
  · have : half p u n ≠ h' := fun h2 => h h2.symm
    simp [h, this]

/-- `ε_0 + ε_1 ≡ 0 (mod p)`: `t - n` runs over a complete residue system, and `∑ v⁻¹ ≡ 0`. -/
theorem eps_sum_dvd (hp5 : 5 ≤ p) (n j : ℕ) : Dv p 1 (eps u p n (j, 0) + eps u p n (j, 1)) := by
  have h1 : eps u p n (j, 0) + eps u p n (j, 1) =
      ∑ r ∈ range p, ((invZ p (((j * p + r : ℕ) : ℤ) - n) : LocRing p) : ℚ) := by
    unfold eps cellSum
    exact (sum_range_cells (fun r => ((invZ p (((j * p + r : ℕ) : ℤ) - n) : LocRing p) : ℚ))).symm
  rw [h1]
  let S : LocRing p := ∑ r ∈ range p, invZ p (((j * p + r : ℕ) : ℤ) - n)
  have hS : ((S : LocRing p) : ℚ) = ∑ r ∈ range p, ((invZ p (((j * p + r : ℕ) : ℤ) - n) : LocRing p) : ℚ) := by
    exact map_sum (LocRing p).subtype (fun r => invZ p (((j * p + r : ℕ) : ℤ) - n)) (range p)
  rw [← hS]
  have hred : redQ p S = 0 := by
    simp only [S, map_sum, redQ_invZ]
    have e : ∀ r ∈ range p, ((((j * p + r : ℕ) : ℤ) - n : ℤ) : ZMod p)⁻¹ =
        (fun y : ZMod p => (y - (n : ZMod p))⁻¹) (((0 + r : ℕ)) : ZMod p) := by
      intro r _
      push_cast
      simp
    rw [Finset.sum_congr rfl e, sum_range_cast (fun y : ZMod p => (y - (n : ZMod p))⁻¹) 0]
    have := Equiv.sum_comp (Equiv.subRight (n : ZMod p)) (fun z => z⁻¹)
    simp only [Equiv.subRight_apply] at this
    rw [this]
    exact sum_inv_zmod hp5
  obtain ⟨y, hy⟩ := (redQ_eq_zero_iff p _).1 hred
  unfold Dv
  rw [hy]
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  simp only [Subring.coe_mul, Subring.coe_natCast, pow_one]
  rw [mul_div_cancel_left₀ _ hp0]
  exact y.2

end Eps

/-! ### The two halves of a period -/

section Halves

variable {p : ℕ} [hp : Fact p.Prime] (v u : ℤ) {N : ℕ}

theorem cstart_zero (j : ℕ) : cstart p (j, 0) = j * p := by simp [cstart]
theorem cstart_one (j : ℕ) : cstart p (j, 1) = j * p + (p + 1) / 2 := by simp [cstart]

theorem Scell_halves (hodd : p % 2 = 1) (hN : 2 * N < p * p) {j : ℕ} (hj : (j + 1) * p ≤ N) :
    Dv p 1 ((p : ℚ) ^ 2 * (Scell v u p (j, 1) - Scell v u p (j, 0))) := by
  have hp0 : 0 < p := hp.out.pos
  have hm : (p + 1) / 2 < p := by have := hp.out.two_le; omega
  have h := PF_diff_same_period v u hN (s := j * p) (t := j * p + (p + 1) / 2) (N := N)
    (by omega) (by nlinarith) (by
      rw [Nat.mul_div_cancel _ hp0, Nat.mul_comm, Nat.mul_add_div hp0, Nat.div_eq_of_lt hm]; simp)
  have := Dv.of_Vp (k := 1) h
  unfold Scell
  rw [cstart_zero, cstart_one]
  simpa using this

theorem Gcell_halves (hodd : p % 2 = 1) (hN : 2 * N < p * p) {j : ℕ} (hj : (j + 1) * p ≤ N) :
    Dv p 1 ((p : ℚ) ^ 3 * (Gcell v u p (j, 0) - Gcell v u p (j, 1))) := by
  have hp0 : 0 < p := hp.out.pos
  have hm : (p + 1) / 2 < p := by have := hp.out.two_le; omega
  have h := PE_diff_same_period v u hN (s := j * p) (t := j * p + (p + 1) / 2) (N := N)
    (by omega) (by nlinarith) (by
      rw [Nat.mul_div_cancel _ hp0, Nat.mul_comm, Nat.mul_add_div hp0, Nat.div_eq_of_lt hm]; simp)
  have := Dv.of_Vp (k := 1) h
  unfold Gcell
  rw [cstart_zero, cstart_one]
  have e : (p : ℚ) ^ 3 * (-PE v u p (j * p) - -PE v u p (j * p + (p + 1) / 2)) =
      (p : ℚ) ^ (2 + 1) * (PE v u p (j * p + (p + 1) / 2) - PE v u p (j * p)) := by ring
  rw [e]; exact this

theorem sdiff_halves (hodd : p % 2 = 1) (hN : 2 * N < p * p) {j : ℕ} (hj : (j + 1) * p ≤ N) (n : ℕ) :
    Dv p 1 (sdiff v u p n (j, 1) - sdiff v u p n (j, 0)) := by
  have := Scell_halves v u hodd hN hj
  unfold sdiff
  have e : (p : ℚ) ^ 2 * (Scell v u p (j, 1) - Scell v u p (cell p u n)) -
      (p : ℚ) ^ 2 * (Scell v u p (j, 0) - Scell v u p (cell p u n)) =
      (p : ℚ) ^ 2 * (Scell v u p (j, 1) - Scell v u p (j, 0)) := by ring
  rw [e]; exact this

end Halves

/-! ### The cell sums `A_n(c) = ∑_{t ∈ c} p³ M(n, t)` -/

section ASums

variable {p : ℕ} [hp : Fact p.Prime] (v u : ℤ) {N : ℕ}

theorem cellSum_congr {α : Type*} [AddCommMonoid α] (c : ℕ × ℕ) {F G : ℕ → α}
    (h : ∀ r, r < p → half p u r = c.2 → F (c.1 * p + r) = G (c.1 * p + r)) :
    cellSum p u c F = cellSum p u c G := by
  unfold cellSum
  refine Finset.sum_congr rfl fun r hr => ?_
  by_cases hh : half p u r = c.2
  · rw [if_pos hh, if_pos hh]; exact h r (Finset.mem_range.1 hr) hh
  · rw [if_neg hh, if_neg hh]

theorem cellSum_add {α : Type*} [AddCommMonoid α] (c : ℕ × ℕ) (F G : ℕ → α) :
    cellSum p u c (fun t => F t + G t) = cellSum p u c F + cellSum p u c G := by
  unfold cellSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  split_ifs <;> simp

theorem cellSum_mul_left (c : ℕ × ℕ) (a : ℚ) (F : ℕ → ℚ) :
    cellSum p u c (fun t => a * F t) = a * cellSum p u c F := by
  unfold cellSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  split_ifs <;> simp

theorem cellSum_dv {k : ℕ} (c : ℕ × ℕ) {F : ℕ → ℚ}
    (h : ∀ r, r < p → half p u r = c.2 → Dv p k (F (c.1 * p + r))) : Dv p k (cellSum p u c F) := by
  unfold cellSum
  refine Dv.sum _ _ fun r hr => ?_
  by_cases hh : half p u r = c.2
  · rw [if_pos hh]; exact h r (Finset.mem_range.1 hr) hh
  · rw [if_neg hh]; exact Dv.zero

theorem eps_mem (n : ℕ) (c : ℕ × ℕ) : eps u p n c ∈ LocRing p := by
  unfold eps cellSum
  refine (LocRing p).sum_mem fun r _ => ?_
  split_ifs
  · exact (invZ p _).2
  · exact (LocRing p).zero_mem

/-- The cell sum `A_n(c)`. -/
noncomputable def Acell (p : ℕ) (n : ℕ) (c : ℕ × ℕ) : ℚ :=
  cellSum p u c (fun t => (p : ℚ) ^ 3 * Lm v u n t)

theorem Acell_mem (hN : 2 * N < p * p) (n : ℕ) (hn : n < N) {j h' : ℕ} (hj : (j + 1) * p ≤ N) :
    Acell v u p n (j, h') ∈ LocRing p := by
  unfold Acell cellSum
  refine (LocRing p).sum_mem fun r hr => ?_
  have hrp := Finset.mem_range.1 hr
  split_ifs
  · exact q_mem v u hN hn (by nlinarith)
  · exact (LocRing p).zero_mem

/-- Same cell as `n`: `A_n(cell n) ≡ p³ G(cell n)  (mod p³)`. -/
theorem Acell_same (hodd : p % 2 = 1) (hN : 2 * N < p * p) (n : ℕ) (hn : n < N)
    (hl : (n / p + 1) * p ≤ N) :
    Dv p 3 (Acell v u p n (n / p, half p u n) - (p : ℚ) ^ 3 * Gcell v u p (n / p, half p u n)) := by
  have hp0 : 0 < p := hp.out.pos
  obtain ⟨ρ, hρ⟩ : ∃ ρ, ρ = n % p := ⟨_, rfl⟩
  have hρp : ρ < p := by rw [hρ]; exact Nat.mod_lt n hp0
  have hn' : (n / p) * p + ρ = n := by
    have := Nat.div_add_mod n p; rw [Nat.mul_comm] at this; omega
  have hhρ : half p u ρ = half p u n := by unfold half; rw [hρ, Nat.mod_mod]
  have hsub : Acell v u p n (n / p, half p u n) - (p : ℚ) ^ 3 * Lm v u n n =
      ∑ r ∈ range p, ((if half p u r = half p u n then (p : ℚ) ^ 3 * Lm v u n ((n / p) * p + r) else 0)
        - (if r = ρ then (p : ℚ) ^ 3 * Lm v u n n else 0)) := by
    rw [Finset.sum_sub_distrib, Finset.sum_ite_eq' (range p) ρ, if_pos (Finset.mem_range.2 hρp)]
    rfl
  have hdv : Dv p 3 (Acell v u p n (n / p, half p u n) - (p : ℚ) ^ 3 * Lm v u n n) := by
    rw [hsub]
    refine Dv.sum _ _ fun r hr => ?_
    have hrp := Finset.mem_range.1 hr
    by_cases hrρ : r = ρ
    · rw [hrρ, if_pos rfl, hhρ, if_pos rfl, hn']; simpa using (Dv.zero : Dv p 3 0)
    · rw [if_neg hrρ, sub_zero]
      by_cases hh : half p u r = half p u n
      · rw [if_pos hh]
        have hnb : (n / p) * p + r < N := by nlinarith
        refine Dv_q_same_cell v u hN hn hnb ?_ ?_
        · intro heq
          apply hrρ
          omega
        · have := cell_node (u := u) hp0 (n / p) r hrp
          rw [this, hh]; rfl
      · rw [if_neg hh]; exact Dv.zero
  have hdiag := Dv_q_diag v u hodd (a := n)
  have := hdv.add hdiag
  rw [show cell p u n = (n / p, half p u n) from rfl] at this
  convert this using 1
  ring

end ASums

/-! ### The other half and the other periods -/

section AOther

variable {p : ℕ} [hp : Fact p.Prime] (v u : ℤ) {N : ℕ}

theorem cellSum_sub (c : ℕ × ℕ) (F G : ℕ → ℚ) :
    cellSum p u c (fun t => F t - G t) = cellSum p u c F - cellSum p u c G := by
  unfold cellSum
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  split_ifs <;> simp

theorem Acell_other_half (hN : 2 * N < p * p) (n : ℕ) (hn : n < N) (hl : (n / p + 1) * p ≤ N)
    {h' : ℕ} (hh : h' ≠ half p u n) : Dv p 2 (Acell v u p n (n / p, h')) := by
  have hp0 : 0 < p := hp.out.pos
  unfold Acell
  refine cellSum_dv (u := u) _ fun r hrp hr => ?_
  have hnb : (n / p) * p + r < N := by nlinarith
  have hcell : cell p u ((n / p) * p + r) = (n / p, h') := by
    rw [cell_node hp0 _ r hrp]; simp only at hr; rw [hr]
  refine Dv_q_same_period v u hN hn hnb ?_ ?_ ?_
  · intro heq
    apply hh
    have : cell p u n = cell p u ((n / p) * p + r) := by rw [← heq]
    rw [hcell] at this
    exact (Prod.mk.inj this).2.symm
  · rw [hcell]; rfl
  · rw [hcell]
    intro h
    exact hh (Prod.mk.inj h).2.symm

theorem Acell_other_period (hodd : p % 2 = 1) (hp5 : 5 ≤ p) (hN : 2 * N < p * p) (n : ℕ) (hn : n < N)
    {j : ℕ} (hjl : j ≠ n / p) (hj : (j + 1) * p ≤ N) (h' : ℕ) :
    Dv p 3 (Acell v u p n (j, h') -
      (if h' = half p u n then sdiff v u p n (j, h') / ((j : ℚ) - ((n / p : ℕ) : ℚ)) else 0) -
      (p : ℚ) * sdiff v u p n (j, h') * eps u p n (j, h')) := by
  have hp0 : 0 < p := hp.out.pos
  have hp0' : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hjl' : ((j : ℚ) - ((n / p : ℕ) : ℚ)) ≠ 0 := by
    intro h
    apply hjl
    have : (j : ℚ) = ((n / p : ℕ) : ℚ) := by linarith
    exact_mod_cast this
  -- the polar approximation
  have hG : cellSum p u (j, h') (fun t => (p : ℚ) * sdiff v u p n (cell p u t) * (((t : ℚ) - n)⁻¹)) =
      (p : ℚ) * sdiff v u p n (j, h') * cellSum p u (j, h') (fun t => ((t : ℚ) - n)⁻¹) := by
    rw [← cellSum_mul_left]
    refine cellSum_congr (u := u) (j, h') fun r hrp hr => ?_
    rw [cell_node hp0 j r hrp]; simp only at hr; rw [hr]
  have hD : Dv p 3 (cellSum p u (j, h') (fun t => (p : ℚ) ^ 3 * Lm v u n t -
      (p : ℚ) * sdiff v u p n (cell p u t) * (((t : ℚ) - n)⁻¹))) := by
    refine cellSum_dv (u := u) _ fun r hrp hr => ?_
    have hnb : j * p + r < N := by nlinarith
    refine q_decomp v u hodd hp5 hN hn hnb ?_
    intro heq
    apply hjl
    have h1 : n = j * p + r := heq
    have h2 : n / p = j := by
      rw [h1, Nat.mul_comm, Nat.mul_add_div hp0, Nat.div_eq_of_lt hrp]; simp
    exact h2.symm
  rw [cellSum_sub, hG, cell_inv_sum] at hD
  unfold Acell
  convert hD using 1
  have e : (p : ℚ) * sdiff v u p n (j, h') *
      ((if h' = half p u n then (((j : ℚ) - ((n / p : ℕ) : ℚ)) * p)⁻¹ else 0) + eps u p n (j, h')) =
      (if h' = half p u n then sdiff v u p n (j, h') / ((j : ℚ) - ((n / p : ℕ) : ℚ)) else 0) +
        (p : ℚ) * sdiff v u p n (j, h') * eps u p n (j, h') := by
    split_ifs
    · field_simp
    · ring
  rw [e]; ring

theorem sdiff_mem (hodd : p % 2 = 1) (hN : 2 * N < p * p) (n : ℕ) (hn : n < N) {j : ℕ}
    (hj : (j + 1) * p ≤ N) (h' : ℕ) (hh : h' ≤ 1) :
    sdiff v u p n (j, h') ∈ LocRing p := by
  have hp0 : 0 < p := hp.out.pos
  have hm : (p + 1) / 2 < p := by have := hp.out.two_le; omega
  have hc : cell p u n = (n / p, half p u n) := rfl
  have key : ∀ a b : ℕ, a < N → b < N → (p : ℚ) ^ 2 * (PF v u p b - PF v u p a) ∈ LocRing p := by
    intro a b ha hb
    rcases le_total a b with hab | hab
    · exact PF_diff_period v u hN hab hb
    · have this : (p : ℚ) ^ 2 * (PF v u p a - PF v u p b) ∈ LocRing p := PF_diff_period v u hN hab ha
      have e : (p : ℚ) ^ 2 * (PF v u p b - PF v u p a) = -((p : ℚ) ^ 2 * (PF v u p a - PF v u p b)) := by ring
      rw [e]; exact (LocRing p).neg_mem this
  unfold sdiff Scell
  have h1 : cstart p (j, h') < N := by
    unfold cstart
    interval_cases h' <;> simp <;> nlinarith
  have h2 := cstart_le (u := u) hodd n
  have := key (cstart p (cell p u n)) (cstart p (j, h')) (by omega) h1
  have e : (p : ℚ) ^ 2 * (PF v u p (cstart p (j, h')) - PF v u p (cstart p (cell p u n))) =
      (p : ℚ) ^ 2 * (PF v u p (cstart p (j, h')) - PF v u p (cstart p (cell p u n))) := rfl
  exact this

end AOther

/-! ### Passage to a `ℤ_(p)`-algebra -/

section RLevel

variable {p : ℕ} [hp : Fact p.Prime] {R : Type*} [CommRing R] [Algebra (LocRing p) R]

open Classical in
/-- The image in `R` of a `p`-integral rational (and `0` of any other). -/
noncomputable def toR (p : ℕ) [Fact p.Prime] {R : Type*} [CommRing R] [Algebra (LocRing p) R] (x : ℚ) : R :=
  if h : x ∈ LocRing p then algebraMap (LocRing p) R ⟨x, h⟩ else 0

theorem toR_of_mem {x : ℚ} (h : x ∈ LocRing p) :
    toR p x = (algebraMap (LocRing p) R ⟨x, h⟩ : R) := by
  unfold toR; rw [dif_pos h]

theorem toR_add {x y : ℚ} (hx : x ∈ LocRing p) (hy : y ∈ LocRing p) :
    toR p (x + y) = (toR p x : R) + toR p y := by
  rw [toR_of_mem ((LocRing p).add_mem hx hy), toR_of_mem hx, toR_of_mem hy, ← map_add]
  rfl

theorem toR_sub {x y : ℚ} (hx : x ∈ LocRing p) (hy : y ∈ LocRing p) :
    toR p (x - y) = (toR p x : R) - toR p y := by
  rw [toR_of_mem ((LocRing p).sub_mem hx hy), toR_of_mem hx, toR_of_mem hy, ← map_sub]
  rfl

theorem toR_mul {x y : ℚ} (hx : x ∈ LocRing p) (hy : y ∈ LocRing p) :
    toR p (x * y) = (toR p x : R) * toR p y := by
  rw [toR_of_mem ((LocRing p).mul_mem hx hy), toR_of_mem hx, toR_of_mem hy, ← map_mul]
  rfl

theorem toR_zero : toR p (0 : ℚ) = (0 : R) := by
  rw [toR_of_mem (LocRing p).zero_mem]; exact map_zero (algebraMap (LocRing p) R)

theorem toR_sum {ι : Type*} (s : Finset ι) (f : ι → ℚ) (h : ∀ i ∈ s, f i ∈ LocRing p) :
    toR p (∑ i ∈ s, f i) = ∑ i ∈ s, (toR p (f i) : R) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using toR_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      toR_add (h a (Finset.mem_insert_self _ _))
        ((LocRing p).sum_mem fun i hi => h i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => h i (Finset.mem_insert_of_mem hi)]

theorem toR_dvd {k : ℕ} {x : ℚ} (hx : Dv p k x) : (p : R) ^ k ∣ (toR p x : R) := by
  have hp0 : (p : ℚ) ^ k ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)
  have hy := hx
  unfold Dv at hy
  have hxe : x = (p : ℚ) ^ k * (x / (p : ℚ) ^ k) := by field_simp
  have hpk : ((p : ℚ) ^ k) ∈ LocRing p := by
    exact_mod_cast int_mem_locRing (ℓ := p) ((p : ℤ) ^ k)
  refine ⟨toR p (x / (p : ℚ) ^ k), ?_⟩
  conv_lhs => rw [hxe]
  rw [toR_mul hpk hy, toR_of_mem hpk]
  congr 1
  have : (⟨(p : ℚ) ^ k, hpk⟩ : LocRing p) = ((p : LocRing p)) ^ k := by
    apply Subtype.ext; simp
  rw [this, map_pow, map_natCast]

theorem toR_dvd_of_dvd {j k : ℕ} (hjk : j ≤ k) {x : ℚ} (hx : Dv p k x) : (p : R) ^ j ∣ (toR p x : R) :=
  toR_dvd (Dv.mono hjk hx)

/-! #### The algebra of the other periods -/

theorem alg_other0 {R : Type*} [CommRing R] (P s0 s1 e0 e1 φ0 φ1 D0 D1 c : R)
    (hD0 : P ^ 2 ∣ D0) (hD1 : P ^ 2 ∣ D1) (hs : P ∣ s1 - s0) (he : P ∣ e0 + e1) (hφ : P ∣ φ0 - φ1) :
    P ^ 2 ∣ ((c + P * s0 * e0 + D0) * φ0 + (P * s1 * e1 + D1) * φ1) - c * φ0 := by
  have hY : P ∣ s0 * e0 * φ0 + s1 * e1 * φ1 := by
    have e : s0 * e0 * φ0 + s1 * e1 * φ1 =
        s0 * φ0 * (e0 + e1) + e1 * ((s1 - s0) * φ1 - s0 * (φ0 - φ1)) := by ring
    rw [e]
    exact dvd_add (he.mul_left _) (((hs.mul_right _).sub (hφ.mul_left _)).mul_left _)
  have e : ((c + P * s0 * e0 + D0) * φ0 + (P * s1 * e1 + D1) * φ1) - c * φ0 =
      P * (s0 * e0 * φ0 + s1 * e1 * φ1) + D0 * φ0 + D1 * φ1 := by ring
  rw [e, sq]
  exact dvd_add (dvd_add (mul_dvd_mul_left P hY) ((sq P ▸ hD0).mul_right _)) ((sq P ▸ hD1).mul_right _)

theorem alg_other1 {R : Type*} [CommRing R] (P s0 s1 e0 e1 φ0 φ1 D0 D1 c : R)
    (hD0 : P ^ 2 ∣ D0) (hD1 : P ^ 2 ∣ D1) (hs : P ∣ s1 - s0) (he : P ∣ e0 + e1) (hφ : P ∣ φ0 - φ1) :
    P ^ 2 ∣ ((P * s0 * e0 + D0) * φ0 + (c + P * s1 * e1 + D1) * φ1) - c * φ1 := by
  have hY : P ∣ s0 * e0 * φ0 + s1 * e1 * φ1 := by
    have e : s0 * e0 * φ0 + s1 * e1 * φ1 =
        s0 * φ0 * (e0 + e1) + e1 * ((s1 - s0) * φ1 - s0 * (φ0 - φ1)) := by ring
    rw [e]
    exact dvd_add (he.mul_left _) (((hs.mul_right _).sub (hφ.mul_left _)).mul_left _)
  have e : ((P * s0 * e0 + D0) * φ0 + (c + P * s1 * e1 + D1) * φ1) - c * φ1 =
      P * (s0 * e0 * φ0 + s1 * e1 * φ1) + D0 * φ0 + D1 * φ1 := by ring
  rw [e, sq]
  exact dvd_add (dvd_add (mul_dvd_mul_left P hY) ((sq P ▸ hD0).mul_right _)) ((sq P ▸ hD1).mul_right _)

end RLevel

/-! ### The cell action -/

section Main

variable {p : ℕ} [hp : Fact p.Prime] (v u : ℤ) {N : ℕ}
  {R : Type*} [CommRing R] [Algebra (LocRing p) R]

theorem toR_p : toR p ((p : ℚ)) = (p : R) := by
  have hpm : ((p : ℚ)) ∈ LocRing p := by exact_mod_cast int_mem_locRing (ℓ := p) (p : ℤ)
  rw [toR_of_mem hpm]
  have : (⟨(p : ℚ), hpm⟩ : LocRing p) = (p : LocRing p) := by apply Subtype.ext; simp
  rw [this, map_natCast]

theorem G_mem (hodd : p % 2 = 1) (hN : 2 * N < p * p) {t : ℕ} (ht : t < N) :
    (p : ℚ) ^ 3 * Gcell v u p (cell p u t) ∈ LocRing p := by
  have h := PE_diff_period v u hN (Nat.zero_le t) ht
  have h0 : PE v u p 0 = 0 := by simp [PE]
  rw [h0, sub_zero] at h
  rw [← PE_eq_Gcell v u hodd t]
  have e : (p : ℚ) ^ 3 * -PE v u p t = -((p : ℚ) ^ 3 * PE v u p t) := by ring
  rw [e]; exact (LocRing p).neg_mem h

theorem unit_diff {j l : ℕ} (hjl : j ≠ l) (hj : j < p) (hl : l < p) :
    (((j : ℚ) - l))⁻¹ ∈ LocRing p := by
  have h := inv_int_mem (p := p) (z := (j : ℤ) - l) (by
    intro hd
    apply hjl
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd ((j : ℤ) - l) p).2 hd
    push_cast at this
    rw [sub_eq_zero, ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hj, Nat.mod_eq_of_lt hl] at this
    exact this)
  simpa using h

/-- The case `j = l` of the cell action. -/
theorem period_same (hodd : p % 2 = 1) (hN : 2 * N < p * p) (n : ℕ) (hn : n < N)
    (hl : (n / p + 1) * p ≤ N) (φ : ℕ × ℕ → R) :
    (p : R) ^ 2 ∣
      (toR p (Acell v u p n (n / p, 0)) * φ (n / p, 0) +
        toR p (Acell v u p n (n / p, 1)) * φ (n / p, 1)) -
      toR p ((p : ℚ) ^ 3 * Gcell v u p (n / p, half p u n)) * φ (n / p, half p u n) := by
  have hA := fun h' => Acell_mem v u hN n hn (j := n / p) (h' := h') hl
  have hG : (p : ℚ) ^ 3 * Gcell v u p (n / p, half p u n) ∈ LocRing p := G_mem v u hodd hN hn
  have hsame := Acell_same v u hodd hN n hn hl
  rcases half_eq (p := p) n with h | h
  · rw [h] at hsame hG ⊢
    have e : (toR p (Acell v u p n (n / p, 0)) * φ (n / p, 0) +
        toR p (Acell v u p n (n / p, 1)) * φ (n / p, 1)) -
        toR p ((p : ℚ) ^ 3 * Gcell v u p (n / p, 0)) * φ (n / p, 0) =
        toR p (Acell v u p n (n / p, 0) - (p : ℚ) ^ 3 * Gcell v u p (n / p, 0)) * φ (n / p, 0) +
        toR p (Acell v u p n (n / p, 1)) * φ (n / p, 1) := by
      rw [toR_sub (hA 0) hG]; ring
    rw [e]
    exact dvd_add ((toR_dvd_of_dvd (by norm_num) hsame).mul_right _)
      ((toR_dvd (Acell_other_half v u hN n hn hl (h' := 1) (by rw [h]; norm_num))).mul_right _)
  · rw [h] at hsame hG ⊢
    have e : (toR p (Acell v u p n (n / p, 0)) * φ (n / p, 0) +
        toR p (Acell v u p n (n / p, 1)) * φ (n / p, 1)) -
        toR p ((p : ℚ) ^ 3 * Gcell v u p (n / p, 1)) * φ (n / p, 1) =
        toR p (Acell v u p n (n / p, 0)) * φ (n / p, 0) +
        toR p (Acell v u p n (n / p, 1) - (p : ℚ) ^ 3 * Gcell v u p (n / p, 1)) * φ (n / p, 1) := by
      rw [toR_sub (hA 1) hG]; ring
    rw [e]
    exact dvd_add ((toR_dvd (Acell_other_half v u hN n hn hl (h' := 0) (by rw [h]; norm_num))).mul_right _)
      ((toR_dvd_of_dvd (by norm_num) hsame).mul_right _)

/-- The case `j ≠ l` of the cell action. -/
theorem period_other (hodd : p % 2 = 1) (hp5 : 5 ≤ p) (hN : 2 * N < p * p) (n : ℕ) (hn : n < N)
    {j : ℕ} (hjl : j ≠ n / p) (hj : (j + 1) * p ≤ N)
    (φ : ℕ × ℕ → R) (hφ : (p : R) ∣ φ (j, 0) - φ (j, 1)) :
    (p : R) ^ 2 ∣
      (toR p (Acell v u p n (j, 0)) * φ (j, 0) + toR p (Acell v u p n (j, 1)) * φ (j, 1)) -
      toR p (sdiff v u p n (j, half p u n) / ((j : ℚ) - ((n / p : ℕ) : ℚ))) * φ (j, half p u n) := by
  have hp0 : 0 < p := hp.out.pos
  have hjp : j < p := by nlinarith
  have hlp : n / p < p := by
    by_contra hge
    have h1 := Nat.mul_le_mul_left p (not_lt.1 hge)
    have h2 := Nat.div_mul_le_self n p
    nlinarith
  have hunit := unit_diff hjl hjp hlp
  have hsd := fun h' hh => sdiff_mem v u hodd hN n hn hj h' hh
  have hepsm := eps_mem (p := p) u n
  -- the three-term form of each cell sum
  have hform : ∀ h' : ℕ, h' ≤ 1 →
      ∃ D : ℚ, Dv p 3 D ∧ Acell v u p n (j, h') =
        (if h' = half p u n then sdiff v u p n (j, h') / ((j : ℚ) - ((n / p : ℕ) : ℚ)) else 0) +
        (p : ℚ) * sdiff v u p n (j, h') * eps u p n (j, h') + D := by
    intro h' _
    refine ⟨_, Acell_other_period v u hodd hp5 hN n hn hjl hj h', ?_⟩
    ring
  obtain ⟨D0, hD0, e0⟩ := hform 0 (by norm_num)
  obtain ⟨D1, hD1, e1⟩ := hform 1 (by norm_num)
  -- coefficients and memberships
  have hh := half_eq (p := p) (u := u) n
  have hcmem : sdiff v u p n (j, half p u n) / ((j : ℚ) - ((n / p : ℕ) : ℚ)) ∈ LocRing p := by
    rw [div_eq_mul_inv]
    exact (LocRing p).mul_mem (hsd _ (by rcases hh with h | h <;> omega)) hunit
  have hs0 := hsd 0 (by norm_num)
  have hs1 := hsd 1 (by norm_num)
  have hpsE : ∀ h', (p : ℚ) * sdiff v u p n (j, h') * eps u p n (j, h') ∈ LocRing p → True := fun _ _ => trivial
  have hmulmem : ∀ h' : ℕ, h' ≤ 1 → (p : ℚ) * sdiff v u p n (j, h') * eps u p n (j, h') ∈ LocRing p := by
    intro h' hh'
    exact (LocRing p).mul_mem ((LocRing p).mul_mem (by exact_mod_cast int_mem_locRing (ℓ := p) (p : ℤ)) (hsd h' hh'))
      (eps_mem u n _)
  have hmulR : ∀ h' : ℕ, h' ≤ 1 → toR p ((p : ℚ) * sdiff v u p n (j, h') * eps u p n (j, h')) =
      (p : R) * toR p (sdiff v u p n (j, h')) * toR p (eps u p n (j, h')) := by
    intro h' hh'
    have hpm : ((p : ℚ)) ∈ LocRing p := by exact_mod_cast int_mem_locRing (ℓ := p) (p : ℤ)
    rw [toR_mul ((LocRing p).mul_mem hpm (hsd h' hh')) (eps_mem u n _), toR_mul hpm (hsd h' hh'), toR_p]
  have hitemem : ∀ h' : ℕ, h' ≤ 1 → (if h' = half p u n then
      sdiff v u p n (j, h') / ((j : ℚ) - ((n / p : ℕ) : ℚ)) else 0) ∈ LocRing p := by
    intro h' hh'
    split_ifs with hhh
    · rw [div_eq_mul_inv]; exact (LocRing p).mul_mem (hsd h' hh') hunit
    · exact (LocRing p).zero_mem
  -- images in `R`
  have hR0 : toR p (Acell v u p n (j, 0)) =
      toR p (if 0 = half p u n then sdiff v u p n (j, 0) / ((j : ℚ) - ((n / p : ℕ) : ℚ)) else 0) +
      (p : R) * toR p (sdiff v u p n (j, 0)) * toR p (eps u p n (j, 0)) + toR p D0 := by
    rw [e0, toR_add ((LocRing p).add_mem (hitemem 0 (by norm_num)) (hmulmem 0 (by norm_num))) hD0.mem,
      toR_add (hitemem 0 (by norm_num)) (hmulmem 0 (by norm_num)), hmulR 0 (by norm_num)]
  have hR1 : toR p (Acell v u p n (j, 1)) =
      toR p (if 1 = half p u n then sdiff v u p n (j, 1) / ((j : ℚ) - ((n / p : ℕ) : ℚ)) else 0) +
      (p : R) * toR p (sdiff v u p n (j, 1)) * toR p (eps u p n (j, 1)) + toR p D1 := by
    rw [e1, toR_add ((LocRing p).add_mem (hitemem 1 (by norm_num)) (hmulmem 1 (by norm_num))) hD1.mem,
      toR_add (hitemem 1 (by norm_num)) (hmulmem 1 (by norm_num)), hmulR 1 (by norm_num)]
  have hD0' : (p : R) ^ 2 ∣ toR p D0 := toR_dvd_of_dvd (by norm_num) hD0
  have hD1' : (p : R) ^ 2 ∣ toR p D1 := toR_dvd_of_dvd (by norm_num) hD1
  -- the divisibility facts
  have hs : (p : R) ∣ toR p (sdiff v u p n (j, 1)) - toR p (sdiff v u p n (j, 0)) := by
    rw [← toR_sub hs1 hs0]
    simpa using toR_dvd (sdiff_halves v u hodd hN hj n)
  have he : (p : R) ∣ toR p (eps u p n (j, 0)) + toR p (eps u p n (j, 1)) := by
    rw [← toR_add (eps_mem u n _) (eps_mem u n _)]
    simpa using toR_dvd (eps_sum_dvd u hp5 n j)
  rcases hh with h | h
  · rw [h] at hR0 hR1 ⊢
    simp only [if_true] at hR0
    rw [if_neg (by norm_num)] at hR1
    rw [toR_zero] at hR1
    rw [hR0, hR1, zero_add]
    exact alg_other0 (p : R) _ _ _ _ _ _ _ _ _ hD0' hD1' hs he hφ
  · rw [h] at hR0 hR1 ⊢
    rw [if_neg (by norm_num)] at hR0
    simp only [if_true] at hR1
    rw [toR_zero] at hR0
    rw [hR0, hR1, zero_add]
    exact alg_other1 (p : R) _ _ _ _ _ _ _ _ _ hD0' hD1' hs he hφ

end Main

/-! ### The statement -/

section Final

variable {p : ℕ} [hp : Fact p.Prime] (v u : ℤ) {N : ℕ}
  {R : Type*} [CommRing R] [Algebra (LocRing p) R]

/-- The entry `p³ H(n, t)` of `p³ H = ξ · Id + p³ M`, an element of `R`. -/
noncomputable def Qent (ξ : R) (n t : ℕ) : R :=
  (if n = t then ξ else 0) + toR p ((p : ℚ) ^ 3 * Lm v u n t)

/-- The cell operator `𝐁`:
`(𝐁 φ)(l, h) = [l < κ] (ξ + p³ G(l, h)) φ(l, h) + ∑_{j < κ, j ≠ l} p² (S(l,h) - S(j,h))/(l - j) φ(j, h)`. -/
noncomputable def Bop (ξ : R) (κ : ℕ) (φ : ℕ × ℕ → R) (c : ℕ × ℕ) : R :=
  (if c.1 < κ then (ξ + toR p ((p : ℚ) ^ 3 * Gcell v u p c)) * φ c else 0) +
  ∑ j ∈ range κ, if j = c.1 then 0 else
    toR p ((p : ℚ) ^ 2 * (Scell v u p c - Scell v u p (j, c.2)) / ((c.1 : ℚ) - j)) * φ (j, c.2)

theorem cellSum_toR (hN : 2 * N < p * p) (n : ℕ) (hn : n < N) {j : ℕ} (hj : (j + 1) * p ≤ N)
    (φ : ℕ × ℕ → R) (h' : ℕ) :
    cellSum p u (j, h') (fun t => toR p ((p : ℚ) ^ 3 * Lm v u n t) * φ (cell p u t)) =
      toR p (Acell v u p n (j, h')) * φ (j, h') := by
  have hp0 : 0 < p := hp.out.pos
  unfold Acell cellSum
  rw [toR_sum _ _ (fun r hr => by
    have hrp := Finset.mem_range.1 hr
    split_ifs
    · exact q_mem v u hN hn (by nlinarith)
    · exact (LocRing p).zero_mem), Finset.sum_mul]
  refine Finset.sum_congr rfl fun r hr => ?_
  have hrp := Finset.mem_range.1 hr
  by_cases hh : half p u r = h'
  · simp only [hh, if_true]
    rw [cell_node hp0 j r hrp, hh]
  · simp only [hh, if_false]
    rw [toR_zero, zero_mul]

theorem Bop_eq (ξ : R) (κ : ℕ) (φ : ℕ × ℕ → R) (l h : ℕ) :
    Bop (p := p) v u ξ κ φ (l, h) =
      (if l < κ then ξ * φ (l, h) else 0) +
      ((if l < κ then toR p ((p : ℚ) ^ 3 * Gcell v u p (l, h)) * φ (l, h) else 0) +
        ∑ j ∈ range κ, if j = l then 0 else
          toR p ((p : ℚ) ^ 2 * (Scell v u p (l, h) - Scell v u p (j, h)) /
            ((l : ℚ) - j)) * φ (j, h)) := by
  unfold Bop
  by_cases hlk : l < κ
  · simp only [hlk, if_true]; ring
  · simp only [hlk, if_false]; ring

/-- **Lemma 2 (cell action).**  For `φ` on the cells with `φ(j,0) ≡ φ(j,1) (mod p)`, every node `n < N`:
`p³ (H φ̃)(n) ≡ (𝐁 φ)(cell n)  (mod p²)`. -/
theorem cell_action (hodd : p % 2 = 1) (hp5 : 5 ≤ p) (hN : 2 * N < p * p) {κ : ℕ} (hκN : κ * p ≤ N)
    (ξ : R) (φ : ℕ × ℕ → R) (hφ : ∀ j < κ, (p : R) ∣ φ (j, 0) - φ (j, 1)) (n : ℕ) (hn : n < N) :
    (p : R) ^ 2 ∣ (∑ t ∈ range (κ * p), Qent (p := p) v u ξ n t * φ (cell p u t)) -
      Bop (p := p) v u ξ κ φ (cell p u n) := by
  have hp0 : 0 < p := hp.out.pos
  have hjN : ∀ j, j < κ → (j + 1) * p ≤ N := fun j hj => by nlinarith
  -- the left side
  have hL : ∑ t ∈ range (κ * p), Qent (p := p) v u ξ n t * φ (cell p u t) =
      (if n < κ * p then ξ * φ (cell p u n) else 0) +
      ∑ j ∈ range κ, (toR p (Acell v u p n (j, 0)) * φ (j, 0) +
        toR p (Acell v u p n (j, 1)) * φ (j, 1)) := by
    have e1 : ∑ t ∈ range (κ * p), Qent (p := p) v u ξ n t * φ (cell p u t) =
        ∑ t ∈ range (κ * p), (if n = t then ξ * φ (cell p u t) else 0) +
        ∑ t ∈ range (κ * p), toR p ((p : ℚ) ^ 3 * Lm v u n t) * φ (cell p u t) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun t _ => ?_
      unfold Qent
      split_ifs <;> simp [add_mul]
    rw [e1, Finset.sum_ite_eq]
    simp only [Finset.mem_range]
    rw [sum_nodes_cells]
    congr 1
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' := hjN j (Finset.mem_range.1 hj)
    rw [cellSum_toR v u hN n hn hj', cellSum_toR v u hN n hn hj']
  have hc : cell p u n = (n / p, half p u n) := rfl
  rw [hL, hc, Bop_eq]
  have hnl : n < κ * p ↔ n / p < κ := (Nat.div_lt_iff_lt_mul hp0).symm
  by_cases hlk : n / p < κ
  · simp only [hlk, hnl.2 hlk, if_true]
    have hl : (n / p + 1) * p ≤ N := hjN _ hlk
    -- the sum over periods
    set X : R := toR p ((p : ℚ) ^ 3 * Gcell v u p (n / p, half p u n)) * φ (n / p, half p u n) with hX
    have hsplit : ∑ j ∈ range κ, (if j = n / p then X else
        toR p ((p : ℚ) ^ 2 * (Scell v u p (n / p, half p u n) - Scell v u p (j, half p u n)) /
          ((n / p : ℕ) - (j : ℚ))) * φ (j, half p u n)) = X +
        ∑ j ∈ range κ, if j = n / p then 0 else
          toR p ((p : ℚ) ^ 2 * (Scell v u p (n / p, half p u n) - Scell v u p (j, half p u n)) /
            ((n / p : ℕ) - (j : ℚ))) * φ (j, half p u n) := by
      have : ∀ j ∈ range κ, (if j = n / p then X else
          toR p ((p : ℚ) ^ 2 * (Scell v u p (n / p, half p u n) - Scell v u p (j, half p u n)) /
            ((n / p : ℕ) - (j : ℚ))) * φ (j, half p u n)) =
          (if j = n / p then X else 0) + (if j = n / p then 0 else
          toR p ((p : ℚ) ^ 2 * (Scell v u p (n / p, half p u n) - Scell v u p (j, half p u n)) /
            ((n / p : ℕ) - (j : ℚ))) * φ (j, half p u n)) := by
        intro j _; split_ifs <;> simp
      rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_ite_eq', if_pos (Finset.mem_range.2 hlk)]
    have hdiff : (ξ * φ (n / p, half p u n) +
        ∑ j ∈ range κ, (toR p (Acell v u p n (j, 0)) * φ (j, 0) +
          toR p (Acell v u p n (j, 1)) * φ (j, 1))) -
        (ξ * φ (n / p, half p u n) + (X + ∑ j ∈ range κ, if j = n / p then 0 else
          toR p ((p : ℚ) ^ 2 * (Scell v u p (n / p, half p u n) - Scell v u p (j, half p u n)) /
            ((n / p : ℕ) - (j : ℚ))) * φ (j, half p u n))) =
        ∑ j ∈ range κ, ((toR p (Acell v u p n (j, 0)) * φ (j, 0) +
          toR p (Acell v u p n (j, 1)) * φ (j, 1)) - (if j = n / p then X else
          toR p ((p : ℚ) ^ 2 * (Scell v u p (n / p, half p u n) - Scell v u p (j, half p u n)) /
            ((n / p : ℕ) - (j : ℚ))) * φ (j, half p u n))) := by
      rw [Finset.sum_sub_distrib, hsplit]; ring
    rw [hdiff]
    refine Finset.dvd_sum fun j hj => ?_
    have hjκ := Finset.mem_range.1 hj
    by_cases hjl : j = n / p
    · subst hjl
      rw [if_pos rfl]
      exact period_same v u hodd hN n hn hl φ
    · rw [if_neg hjl]
      have := period_other v u hodd hp5 hN n hn hjl (hjN j hjκ) φ (hφ j hjκ)
      have hcoef : sdiff v u p n (j, half p u n) / ((j : ℚ) - ((n / p : ℕ) : ℚ)) =
          (p : ℚ) ^ 2 * (Scell v u p (n / p, half p u n) - Scell v u p (j, half p u n)) /
            (((n / p : ℕ) : ℚ) - (j : ℚ)) := by
        have h1 : ((j : ℚ) - ((n / p : ℕ) : ℚ)) ≠ 0 := sub_ne_zero.2 (by exact_mod_cast hjl)
        have h2 : (((n / p : ℕ) : ℚ) - (j : ℚ)) ≠ 0 := sub_ne_zero.2 (by exact_mod_cast (Ne.symm hjl))
        unfold sdiff
        rw [show cell p u n = (n / p, half p u n) from rfl]
        field_simp
        ring
      rw [hcoef] at this
      exact this
  · -- `n` outside `K`: only the other periods
    simp only [hlk, mt hnl.1 hlk, if_false, zero_add]
    have hdiff : (∑ j ∈ range κ, (toR p (Acell v u p n (j, 0)) * φ (j, 0) +
        toR p (Acell v u p n (j, 1)) * φ (j, 1))) -
        (∑ j ∈ range κ, if j = n / p then 0 else
          toR p ((p : ℚ) ^ 2 * (Scell v u p (n / p, half p u n) - Scell v u p (j, half p u n)) /
            ((n / p : ℕ) - (j : ℚ))) * φ (j, half p u n)) =
        ∑ j ∈ range κ, ((toR p (Acell v u p n (j, 0)) * φ (j, 0) +
          toR p (Acell v u p n (j, 1)) * φ (j, 1)) - (if j = n / p then 0 else
          toR p ((p : ℚ) ^ 2 * (Scell v u p (n / p, half p u n) - Scell v u p (j, half p u n)) /
            ((n / p : ℕ) - (j : ℚ))) * φ (j, half p u n))) := by
      rw [Finset.sum_sub_distrib]
    show (p : R) ^ 2 ∣ _ - (∑ j ∈ range κ, if j = n / p then 0 else
          toR p ((p : ℚ) ^ 2 * (Scell v u p (n / p, half p u n) - Scell v u p (j, half p u n)) /
            ((n / p : ℕ) - (j : ℚ))) * φ (j, half p u n))
    rw [hdiff]
    refine Finset.dvd_sum fun j hj => ?_
    have hjκ := Finset.mem_range.1 hj
    have hjl : j ≠ n / p := fun h => hlk (h ▸ hjκ)
    rw [if_neg hjl]
    have := period_other v u hodd hp5 hN n hn hjl (hjN j hjκ) φ (hφ j hjκ)
    have hcoef : sdiff v u p n (j, half p u n) / ((j : ℚ) - ((n / p : ℕ) : ℚ)) =
        (p : ℚ) ^ 2 * (Scell v u p (n / p, half p u n) - Scell v u p (j, half p u n)) /
          (((n / p : ℕ) : ℚ) - (j : ℚ)) := by
      have h1 : ((j : ℚ) - ((n / p : ℕ) : ℚ)) ≠ 0 := sub_ne_zero.2 (by exact_mod_cast hjl)
      have h2 : (((n / p : ℕ) : ℚ) - (j : ℚ)) ≠ 0 := sub_ne_zero.2 (by exact_mod_cast (Ne.symm hjl))
      unfold sdiff
      rw [show cell p u n = (n / p, half p u n) from rfl]
      field_simp
      ring
    rw [hcoef] at this
    exact this

end Final

/-! ### `𝐁` preserves the congruence `φ(j,0) ≡ φ(j,1)` -/

section PreserveV

variable {p : ℕ} [hp : Fact p.Prime] (v u : ℤ) {N : ℕ}
  {R : Type*} [CommRing R] [Algebra (LocRing p) R]

theorem G_mem_cell (hodd : p % 2 = 1) (hN : 2 * N < p * p) {l : ℕ} (hl : (l + 1) * p ≤ N)
    {h : ℕ} (hh : h ≤ 1) : (p : ℚ) ^ 3 * Gcell v u p (l, h) ∈ LocRing p := by
  have hp0 : 0 < p := hp.out.pos
  have hm : (p + 1) / 2 < p := by have := hp.out.two_le; omega
  have hlt : cstart p (l, h) < N := by
    unfold cstart
    interval_cases h <;> simp <;> nlinarith
  have hPE := PE_diff_period v u hN (Nat.zero_le (cstart p (l, h))) hlt
  have h0 : PE v u p 0 = 0 := by simp [PE]
  rw [h0, sub_zero] at hPE
  unfold Gcell
  have e : (p : ℚ) ^ 3 * -PE v u p (cstart p (l, h)) = -((p : ℚ) ^ 3 * PE v u p (cstart p (l, h))) := by ring
  rw [e]; exact (LocRing p).neg_mem hPE

theorem S_diff_mem (hodd : p % 2 = 1) (hN : 2 * N < p * p) {l j : ℕ} (hl : (l + 1) * p ≤ N)
    (hj : (j + 1) * p ≤ N) {h : ℕ} (hh : h ≤ 1) :
    (p : ℚ) ^ 2 * (Scell v u p (l, h) - Scell v u p (j, h)) ∈ LocRing p := by
  have hp0 : 0 < p := hp.out.pos
  have hm : (p + 1) / 2 < p := by have := hp.out.two_le; omega
  have hlt : cstart p (l, h) < N := by
    unfold cstart
    interval_cases h <;> simp <;> nlinarith
  have hlt2 : cstart p (j, h) < N := by
    unfold cstart
    interval_cases h <;> simp <;> nlinarith
  unfold Scell
  rcases le_total (cstart p (j, h)) (cstart p (l, h)) with hab | hab
  · have := PF_diff_period v u hN hab hlt
    have e : (p : ℚ) ^ 2 * (PF v u p (cstart p (l, h)) - PF v u p (cstart p (j, h))) =
        (p : ℚ) ^ 2 * (PF v u p (cstart p (l, h)) - PF v u p (cstart p (j, h))) := rfl
    exact this
  · have := PF_diff_period v u hN hab hlt2
    have e : (p : ℚ) ^ 2 * (PF v u p (cstart p (l, h)) - PF v u p (cstart p (j, h))) =
        -((p : ℚ) ^ 2 * (PF v u p (cstart p (j, h)) - PF v u p (cstart p (l, h)))) := by ring
    rw [e]; exact (LocRing p).neg_mem this

/-- **`𝐁` maps the functions with `φ(j,0) ≡ φ(j,1) (mod p)` to functions of the same kind**, on the cells
of every period `l` (with `(l+1) p ≤ N`). -/
theorem Bop_mem_V (hodd : p % 2 = 1) (hN : 2 * N < p * p) {κ : ℕ} (hκN : κ * p ≤ N)
    (ξ : R) (φ : ℕ × ℕ → R) (hφ : ∀ j < κ, (p : R) ∣ φ (j, 0) - φ (j, 1)) {l : ℕ}
    (hl : (l + 1) * p ≤ N) :
    (p : R) ∣ Bop (p := p) v u ξ κ φ (l, 0) - Bop (p := p) v u ξ κ φ (l, 1) := by
  have hp0 : 0 < p := hp.out.pos
  have hjN : ∀ j, j < κ → (j + 1) * p ≤ N := fun j hj => by nlinarith
  have hlp : l + 1 < p := by
    by_contra hge
    have := Nat.mul_le_mul_right p (not_lt.1 hge)
    nlinarith
  rw [Bop_eq, Bop_eq]
  have hsum : ∑ j ∈ range κ, (if j = l then (0 : R) else
        toR p ((p : ℚ) ^ 2 * (Scell v u p (l, 0) - Scell v u p (j, 0)) / ((l : ℚ) - j)) * φ (j, 0)) -
      ∑ j ∈ range κ, (if j = l then (0 : R) else
        toR p ((p : ℚ) ^ 2 * (Scell v u p (l, 1) - Scell v u p (j, 1)) / ((l : ℚ) - j)) * φ (j, 1)) =
      ∑ j ∈ range κ, ((if j = l then (0 : R) else
        toR p ((p : ℚ) ^ 2 * (Scell v u p (l, 0) - Scell v u p (j, 0)) / ((l : ℚ) - j)) * φ (j, 0)) -
        (if j = l then (0 : R) else
        toR p ((p : ℚ) ^ 2 * (Scell v u p (l, 1) - Scell v u p (j, 1)) / ((l : ℚ) - j)) * φ (j, 1))) := by
    rw [Finset.sum_sub_distrib]
  have hterm : (p : R) ∣ ∑ j ∈ range κ, ((if j = l then (0 : R) else
        toR p ((p : ℚ) ^ 2 * (Scell v u p (l, 0) - Scell v u p (j, 0)) / ((l : ℚ) - j)) * φ (j, 0)) -
        (if j = l then (0 : R) else
        toR p ((p : ℚ) ^ 2 * (Scell v u p (l, 1) - Scell v u p (j, 1)) / ((l : ℚ) - j)) * φ (j, 1))) :=
    Finset.dvd_sum fun j hj => by
      have hjκ := Finset.mem_range.1 hj
      by_cases hjl : j = l
      · simp [hjl]
      · simp only [hjl, if_false]
        have hjp : j + 1 < p := by
          by_contra hge
          have := Nat.mul_le_mul_right p (not_lt.1 hge)
          have := hjN j hjκ
          nlinarith
        have hunit : (((l : ℚ) - j))⁻¹ ∈ LocRing p := unit_diff (Ne.symm hjl) (by omega) (by omega)
        have hc0 := S_diff_mem v u hodd hN hl (hjN j hjκ) (h := 0) (by norm_num)
        have hc1 := S_diff_mem v u hodd hN hl (hjN j hjκ) (h := 1) (by norm_num)
        have hd : Dv p 1 ((p : ℚ) ^ 2 * (Scell v u p (l, 0) - Scell v u p (j, 0)) -
            (p : ℚ) ^ 2 * (Scell v u p (l, 1) - Scell v u p (j, 1))) := by
          have a1 := Scell_halves v u hodd hN hl
          have a2 := Scell_halves v u hodd hN (hjN j hjκ)
          have e : (p : ℚ) ^ 2 * (Scell v u p (l, 0) - Scell v u p (j, 0)) -
              (p : ℚ) ^ 2 * (Scell v u p (l, 1) - Scell v u p (j, 1)) =
              -((p : ℚ) ^ 2 * (Scell v u p (l, 1) - Scell v u p (l, 0))) +
              (p : ℚ) ^ 2 * (Scell v u p (j, 1) - Scell v u p (j, 0)) := by ring
          rw [e]; exact a1.neg.add a2
        have e : toR p ((p : ℚ) ^ 2 * (Scell v u p (l, 0) - Scell v u p (j, 0)) / ((l : ℚ) - j)) * φ (j, 0) -
            toR p ((p : ℚ) ^ 2 * (Scell v u p (l, 1) - Scell v u p (j, 1)) / ((l : ℚ) - j)) * φ (j, 1) =
            toR p (((p : ℚ) ^ 2 * (Scell v u p (l, 0) - Scell v u p (j, 0)) -
              (p : ℚ) ^ 2 * (Scell v u p (l, 1) - Scell v u p (j, 1))) * (((l : ℚ) - j))⁻¹) * φ (j, 0) +
            toR p ((p : ℚ) ^ 2 * (Scell v u p (l, 1) - Scell v u p (j, 1)) / ((l : ℚ) - j)) *
              (φ (j, 0) - φ (j, 1)) := by
          have hac := (LocRing p).mul_mem hc0 hunit
          have hbc := (LocRing p).mul_mem hc1 hunit
          simp only [div_eq_mul_inv]
          rw [sub_mul, toR_sub hac hbc]
          ring
        rw [e]
        refine dvd_add ?_ ((hφ j hjκ).mul_left _)
        have hdd := Dv.mul_mem hunit hd
        have := toR_dvd (R := R) hdd
        simp only [pow_one] at this
        rw [show ((p : ℚ) ^ 2 * (Scell v u p (l, 0) - Scell v u p (j, 0)) -
              (p : ℚ) ^ 2 * (Scell v u p (l, 1) - Scell v u p (j, 1))) * (((l : ℚ) - j))⁻¹ =
              (((l : ℚ) - j))⁻¹ * ((p : ℚ) ^ 2 * (Scell v u p (l, 0) - Scell v u p (j, 0)) -
              (p : ℚ) ^ 2 * (Scell v u p (l, 1) - Scell v u p (j, 1))) by ring]
        exact this.mul_right _
  by_cases hlk : l < κ
  · simp only [hlk, if_true]
    have hG0 := G_mem_cell v u hodd hN hl (h := 0) (by norm_num)
    have hG1 := G_mem_cell v u hodd hN hl (h := 1) (by norm_num)
    have hGd : (p : R) ∣ toR p ((p : ℚ) ^ 3 * (Gcell v u p (l, 0) - Gcell v u p (l, 1))) := by
      have := toR_dvd (R := R) (Gcell_halves v u hodd hN hl)
      simpa [pow_one] using this
    have hφl := hφ l hlk
    have e1 : toR p ((p : ℚ) ^ 3 * Gcell v u p (l, 0)) * φ (l, 0) -
        toR p ((p : ℚ) ^ 3 * Gcell v u p (l, 1)) * φ (l, 1) =
        toR p ((p : ℚ) ^ 3 * (Gcell v u p (l, 0) - Gcell v u p (l, 1))) * φ (l, 0) +
        toR p ((p : ℚ) ^ 3 * Gcell v u p (l, 1)) * (φ (l, 0) - φ (l, 1)) := by
      have : (p : ℚ) ^ 3 * (Gcell v u p (l, 0) - Gcell v u p (l, 1)) =
          (p : ℚ) ^ 3 * Gcell v u p (l, 0) - (p : ℚ) ^ 3 * Gcell v u p (l, 1) := by ring
      rw [this, toR_sub hG0 hG1]; ring
    have : (ξ * φ (l, 0) + (toR p ((p : ℚ) ^ 3 * Gcell v u p (l, 0)) * φ (l, 0) +
        ∑ j ∈ range κ, if j = l then 0 else
          toR p ((p : ℚ) ^ 2 * (Scell v u p (l, 0) - Scell v u p (j, 0)) / ((l : ℚ) - j)) * φ (j, 0))) -
        (ξ * φ (l, 1) + (toR p ((p : ℚ) ^ 3 * Gcell v u p (l, 1)) * φ (l, 1) +
        ∑ j ∈ range κ, if j = l then 0 else
          toR p ((p : ℚ) ^ 2 * (Scell v u p (l, 1) - Scell v u p (j, 1)) / ((l : ℚ) - j)) * φ (j, 1))) =
        ξ * (φ (l, 0) - φ (l, 1)) +
        (toR p ((p : ℚ) ^ 3 * (Gcell v u p (l, 0) - Gcell v u p (l, 1))) * φ (l, 0) +
          toR p ((p : ℚ) ^ 3 * Gcell v u p (l, 1)) * (φ (l, 0) - φ (l, 1))) +
        (∑ j ∈ range κ, ((if j = l then (0 : R) else
          toR p ((p : ℚ) ^ 2 * (Scell v u p (l, 0) - Scell v u p (j, 0)) / ((l : ℚ) - j)) * φ (j, 0)) -
          (if j = l then (0 : R) else
          toR p ((p : ℚ) ^ 2 * (Scell v u p (l, 1) - Scell v u p (j, 1)) / ((l : ℚ) - j)) * φ (j, 1)))) := by
      rw [← hsum, ← e1]; ring
    rw [this]
    exact dvd_add (dvd_add (hφl.mul_left _) (dvd_add (hGd.mul_right _) (hφl.mul_left _))) hterm
  · simp only [hlk, if_false, zero_add]
    rw [hsum]; exact hterm

end PreserveV

end CatalanCore.Uniform.Content.Sweep

#print axioms CatalanCore.Uniform.Content.Sweep.cell_action
#print axioms CatalanCore.Uniform.Content.Sweep.Bop_mem_V
