module

public import CatalanCore.Uniform.Content.Sweep.Cells

@[expose] public section

open Polynomial Finset Matrix CatalanCore.Basic CatalanCore.Arith.Hybrid
open CatalanCore.Uniform.Support

/-!
# The tropical rows of the plane 2 table (lane H, wave H2b; ledger N2)

`ZETA23-NEAR-ZERO` Prop 2.3, as `GLE` bounds on the determinant of a member of the plane 2 family
(`Support.SeqFamily`): retained common nodes `cn` (injective, below `r`), the alternating window
`xs i = r + 2i`, `ys i = r + 2i + 1` (`i < m`), `N = r + 2m`, and the weight table of `Sweep.Cells`
(`2N < p²`).  Every row is `det_gle_of_dual` with explicit potentials.

* `det_gle_phi` / `row_P4` .. `row_P7`: potentials `φ = 0, 1, 3` on the cells `(0,0)`, `(0,1)` and
  the periods `≥ 1`; `v_p(den) ≤ T(r) + T(N)` with `T(n) = ∑_{t<n} φ(t)`, and the four closed forms
  `6r + 6m - 5p` (`p ≤ r`), `r + 3N - 3p` (`r ≤ p ≤ N`), `2r + 2m + 1 - p` (`N ≤ p ≤ 2r`),
  `(N - (p-1)/2)₊` (`p ≥ 2r`).
* `row_P1`: `v_p(den) ≤ 3 (r + m) - ‖m‖_p`, `‖m‖_p = min (m mod p, p - m mod p)`.  Potentials from the
  class of `N - 1 - t` mod `p` (`uRow`, `uCol`, `uRow + uCol = 3` on congruent nodes, `≥ 1` elsewhere);
  the window contributes `2m + A(2m)`, `A(n) = ∑_{j<n} (⌊j/p⌋ mod 2)`, and `A(2m) + ‖m‖_p ≤ m`
  (`Aphi_min`).

**Statement correction.**  P5 and P7 are false as stated in the paper without `2m ≤ r`, for example
`(p, r, m) = (7, 1, 3)` has `max v_p(den) = 3 > r + 3N - 3p = 1`, and `(5, 1, 3)` has `8 > 5` against P7
(exact check, `work/tools/h/h2b/py/scan.py`).  With `2m ≤ r` (the family has `m ≈ αr`, `α ≤ 1/8`) no
case fails, and the proof needs it exactly where the regimes are compared (`p ≤ N ≤ 2r`).
-/
namespace CatalanCore.Uniform.Content.Sweep

section Tropical

variable (p : ℕ) (u : ℤ)

/-- The potential `φ`: `0` on the cell `(0,0)`, `1` on `(0,1)`, `3` on periods `≥ 1`. -/
def phi (t : ℕ) : ℕ := if 1 ≤ t / p then 3 else half p u t

theorem half_le_one (t : ℕ) : half p u t ≤ 1 := by unfold half; split_ifs <;> omega

theorem Wt_le_three' (a b : ℕ) : Wt p u a b ≤ 3 := by
  unfold Wt Wd w3; split_ifs <;> omega

theorem phi_of_period {t : ℕ} (h : 1 ≤ t / p) : phi p u t = 3 := by simp [phi, h]

theorem phi_of_lt {t : ℕ} (h : t < p) : phi p u t = half p u t := by
  have : ¬ 1 ≤ t / p := by rw [Nat.div_eq_of_lt h]; omega
  simp [phi, this]

/-- The weight table is covered by `φ + φ`. -/
theorem Wt_le_phi (a b : ℕ) : Wt p u a b ≤ phi p u a + phi p u b := by
  rcases Nat.eq_zero_or_pos p with hp0 | hp0
  · subst hp0
    have h3a := half_le_one 0 u a
    have h3b := half_le_one 0 u b
    unfold Wt Wd w3 phi cell
    simp
    split_ifs <;> first | omega | (subst_vars; omega)
  by_cases h1 : 1 ≤ a / p
  · have := Wt_le_three' p u a b; rw [phi_of_period p u h1]; omega
  by_cases h2 : 1 ≤ b / p
  · have := Wt_le_three' p u a b; rw [phi_of_period p u h2]; omega
  have ha : a < p := by
    by_contra h; apply h1; exact (Nat.one_le_div_iff hp0).2 (by omega)
  have hb : b < p := by
    by_contra h; apply h2; exact (Nat.one_le_div_iff hp0).2 (by omega)
  rw [phi_of_lt p u ha, phi_of_lt p u hb]
  have hma : a % p = a := Nat.mod_eq_of_lt ha
  have hmb : b % p = b := Nat.mod_eq_of_lt hb
  have hda : a / p = 0 := Nat.div_eq_of_lt ha
  have hdb : b / p = 0 := Nat.div_eq_of_lt hb
  have h3a := half_le_one p u a
  have h3b := half_le_one p u b
  unfold Wt Wd w3 cell
  by_cases hab : a = b
  · subst hab
    simp [hda]
    split_ifs <;> omega
  · simp [hab, hma, hmb, hda, hdb]
    split_ifs <;> omega




/-- The partial sums of `φ`. -/
def Tphi (n : ℕ) : ℕ := ∑ t ∈ range n, phi p u t

theorem Tphi_le (hu : u ≠ 0) (hodd : p % 2 = 1) : ∀ {n : ℕ}, n ≤ p → Tphi p u n = n - (p + 1) / 2 := by
  intro n
  induction n with
  | zero => intro _; simp [Tphi]
  | succ n ih =>
    intro hn
    have h1 := ih (by omega)
    have hlt : n < p := by omega
    rw [Tphi, Finset.sum_range_succ, ← Tphi, h1, phi_of_lt p u hlt]
    unfold half
    rw [Nat.mod_eq_of_lt hlt, if_neg hu]
    split_ifs <;> omega

theorem Tphi_ge (hu : u ≠ 0) (hodd : p % 2 = 1) : ∀ {n : ℕ}, p ≤ n → Tphi p u n = (p - 1) / 2 + 3 * (n - p) := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
    rw [Tphi_le p u hu hodd le_rfl]; omega
  | succ n hn ih =>
    rw [Tphi, Finset.sum_range_succ, ← Tphi, ih, phi_of_period]
    · omega
    · exact (Nat.one_le_div_iff (by omega)).2 (by omega)

end Tropical

section Rows

variable {p : ℕ} [hp : Fact p.Prime] (v u : ℤ)

/-- **Tropical potential bound** (Prop 2.3, rows P4 to P7).  For a member of the plane 2 family with
retained common nodes `cn` (injective, below `r`) and the alternating window
`xs i = r + 2i`, `ys i = r + 2i + 1` (`i < m`), `N = r + 2m`, `2N < p²`: every coefficient of the
determinant is `p^{T(r) + T(N)}`-integral, `T(n) = ∑_{t<n} φ(t)`. -/
theorem det_gle_phi {ι : Type} [Fintype ι] [DecidableEq ι] (cn : ι → ℕ) (hinj : Function.Injective cn)
    {r m : ℕ} (hcr : ∀ a, cn a < r) (hN : 2 * (r + 2 * m) < p * p) :
    GLE p (Tphi p u r + Tphi p u (r + 2 * m))
      (seqFullN (fS v u) (eS v u) cn
        (fun i : Fin m => r + 2 * (i : ℕ)) (fun i : Fin m => r + 2 * (i : ℕ) + 1) (X : ℚ[X])).det := by
  have hc : ∀ a, cn a < r + 2 * m := fun a => by have := hcr a; omega
  have hx : ∀ i : Fin m, r + 2 * (i : ℕ) < r + 2 * m := fun i => by have := i.2; omega
  have hy : ∀ i : Fin m, r + 2 * (i : ℕ) + 1 < r + 2 * m := fun i => by have := i.2; omega
  have h := det_gle_of_dual v u hN cn (fun i : Fin m => r + 2 * (i : ℕ))
    (fun i : Fin m => r + 2 * (i : ℕ) + 1) hc hx hy
    (fun a => phi p u (Sum.elim cn (fun i : Fin m => r + 2 * (i : ℕ)) a))
    (fun b => phi p u (Sum.elim cn (fun i : Fin m => r + 2 * (i : ℕ) + 1) b))
    (fun a b => Wt_le_phi p u _ _)
  refine h.mono ?_
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  -- common nodes
  have hcom : ∑ a : ι, phi p u (cn a) ≤ Tphi p u r := by
    rw [← Finset.sum_image (f := fun t => phi p u t) (g := cn) (s := Finset.univ) (fun a _ b _ h => hinj h)]
    unfold Tphi
    apply Finset.sum_le_sum_of_subset
    intro t ht
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.1 ht
    exact Finset.mem_range.2 (hcr a)
  -- the window
  have hwin : ∑ i : Fin m, phi p u (r + 2 * (i : ℕ)) + ∑ i : Fin m, phi p u (r + 2 * (i : ℕ) + 1) =
      Tphi p u (r + 2 * m) - Tphi p u r := by
    have step : ∀ k : ℕ, ∑ i ∈ range k, phi p u (r + 2 * i) + ∑ i ∈ range k, phi p u (r + 2 * i + 1) =
        ∑ t ∈ range (2 * k), phi p u (r + t) := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [Finset.sum_range_succ, Finset.sum_range_succ, show 2 * (k + 1) = 2 * k + 1 + 1 by ring,
          Finset.sum_range_succ, Finset.sum_range_succ]
        have := ih
        simp only [Nat.add_assoc] at this ⊢
        omega
    have e : Tphi p u (r + 2 * m) = Tphi p u r + ∑ t ∈ range (2 * m), phi p u (r + t) := by
      unfold Tphi; rw [Finset.sum_range_add]
    rw [Fin.sum_univ_eq_sum_range (fun i => phi p u (r + 2 * i)), Fin.sum_univ_eq_sum_range
      (fun i => phi p u (r + 2 * i + 1)), step, e]
    omega
  have hle : Tphi p u r ≤ Tphi p u (r + 2 * m) := by
    unfold Tphi; apply Finset.sum_le_sum_of_subset; intro t ht
    exact Finset.mem_range.2 (by have := Finset.mem_range.1 ht; omega)
  omega




/-- The member determinant of the window geometry. -/
noncomputable abbrev rowDet {ι : Type} [Fintype ι] [DecidableEq ι] (cn : ι → ℕ) (r m : ℕ) : ℚ[X] :=
  (seqFullN (fS v u) (eS v u) cn
    (fun i : Fin m => r + 2 * (i : ℕ)) (fun i : Fin m => r + 2 * (i : ℕ) + 1) (X : ℚ[X])).det

theorem odd_of_five (hp5 : 5 ≤ p) : p % 2 = 1 := by
  rcases hp.out.eq_two_or_odd with h | h
  · omega
  · exact h

variable {ι : Type} [Fintype ι] [DecidableEq ι] (cn : ι → ℕ) (hinj : Function.Injective cn)
  {r m : ℕ} (hcr : ∀ a, cn a < r) (hN : 2 * (r + 2 * m) < p * p) (hm : 2 * m ≤ r) (hp5 : 5 ≤ p) (hu : u ≠ 0)

include hu hinj hcr hN hp5 in
/-- **Row P4** (`p ≤ r`): `v_p(den) ≤ 6r + 6m - 5p`. -/
theorem row_P4 (hpr : p ≤ r) : GLE p (6 * r + 6 * m - 5 * p) (rowDet v u cn r m) := by
  refine (det_gle_phi v u cn hinj hcr hN).mono ?_
  have ho := odd_of_five (p := p) hp5
  rw [Tphi_ge p u hu ho hpr, Tphi_ge p u hu ho (by omega)]
  omega

include hu hinj hcr hN hp5 hm in
/-- **Row P5** (`r ≤ p ≤ N`): `v_p(den) ≤ r + 3N - 3p`.  (With `2m ≤ r`; without it the row is false,
for example `(p, r, m) = (7, 1, 3)`.) -/
theorem row_P5 (hrp : r ≤ p) (hpN : p ≤ r + 2 * m) :
    GLE p (r + 3 * (r + 2 * m) - 3 * p) (rowDet v u cn r m) := by
  refine (det_gle_phi v u cn hinj hcr hN).mono ?_
  have ho := odd_of_five (p := p) hp5
  rw [Tphi_le p u hu ho hrp, Tphi_ge p u hu ho hpN]
  omega

include hu hinj hcr hN hp5 hm in
/-- **Row P6** (`N ≤ p ≤ 2r`): `v_p(den) ≤ 2r + 2m - p + 1`. -/
theorem row_P6 (hNp : r + 2 * m ≤ p) (hp2 : p ≤ 2 * r) :
    GLE p (2 * r + 2 * m + 1 - p) (rowDet v u cn r m) := by
  refine (det_gle_phi v u cn hinj hcr hN).mono ?_
  have ho := odd_of_five (p := p) hp5
  rw [Tphi_le p u hu ho (by omega), Tphi_le p u hu ho hNp]
  omega

include hu hinj hcr hN hp5 hm in
/-- **Row P7** (`p ≥ 2r`): `v_p(den) ≤ (N - (p-1)/2)₊`. -/
theorem row_P7 (hp2 : 2 * r ≤ p) :
    GLE p (r + 2 * m - (p - 1) / 2) (rowDet v u cn r m) := by
  refine (det_gle_phi v u cn hinj hcr hN).mono ?_
  have ho := odd_of_five (p := p) hp5
  rw [Tphi_le p u hu ho (by omega)]
  by_cases hNp : r + 2 * m ≤ p
  · rw [Tphi_le p u hu ho hNp]; omega
  · rw [Tphi_ge p u hu ho (by omega)]; omega

/-! ### Row P1: the residue-class potentials -/

section P1

/-- Parity of the residue: for odd `p`, `(j mod p) ≡ j + ⌊j/p⌋ (mod 2)`. -/
theorem parity_mod (p j : ℕ) (hodd : p % 2 = 1) : (j % p) % 2 = (j + j / p) % 2 := by
  have h := Nat.div_add_mod j p
  have h2 : (p * (j / p)) % 2 = (j / p) % 2 := by
    rw [Nat.mul_mod, hodd]; simp
  omega

/-- Potential of a node as a row: determined by the residue class of `N - 1 - t`. -/
def uRow (p N t : ℕ) : ℕ := if ((N - 1 - t) % p) % 2 = 0 then 2 else 1
def uCol (p N t : ℕ) : ℕ := if ((N - 1 - t) % p) % 2 = 0 then 1 else 2

theorem uRow_add_uCol (p N t : ℕ) : uRow p N t + uCol p N t = 3 := by
  unfold uRow uCol; split_ifs <;> omega

theorem uRow_cong {p N a b : ℕ} (ha : a < N) (hb : b < N) (h : a % p = b % p) :
    uRow p N a = uRow p N b := by
  have hm : (N - 1 - a) % p = (N - 1 - b) % p := by
    have h1 : N - 1 - a + a ≡ N - 1 - b + b [MOD p] := by
      have e1 : N - 1 - a + a = N - 1 := by omega
      have e2 : N - 1 - b + b = N - 1 := by omega
      rw [e1, e2]
    have h2 : N - 1 - b + a ≡ N - 1 - b + b [MOD p] := Nat.ModEq.add_left _ h
    exact Nat.ModEq.add_right_cancel' a (h1.trans h2.symm)
  unfold uRow; rw [hm]

theorem Wt_le_uRow_uCol (p N : ℕ) {a b : ℕ} (ha : a < N) (hb : b < N) :
    Wt p u a b ≤ uRow p N a + uCol p N b := by
  by_cases hab : a = b
  · subst hab
    have := uRow_add_uCol p N a
    have : Wd p u a ≤ 3 := by unfold Wd; split_ifs <;> omega
    unfold Wt; rw [if_pos rfl]; omega
  by_cases hm : a % p = b % p
  · have := uRow_cong ha hb hm
    have := uRow_add_uCol p N b
    unfold Wt; rw [if_neg hab, if_pos hm]; omega
  · have h1 : 1 ≤ uRow p N a := by unfold uRow; split_ifs <;> omega
    have h2 : 1 ≤ uCol p N b := by unfold uCol; split_ifs <;> omega
    have : w3 (cell p u a) (cell p u b) ≤ 2 := by unfold w3; split_ifs <;> omega
    unfold Wt; rw [if_neg hab, if_neg hm]; omega

/-- `∑_{j<n} (⌊j/p⌋ mod 2)`. -/
def Aphi (p n : ℕ) : ℕ := ∑ j ∈ range n, (j / p) % 2

theorem Aphi_block (p : ℕ) (hp : 0 < p) : ∀ a : ℕ, Aphi p (a * p) = p * (a / 2) := by
  intro a
  induction a with
  | zero => simp [Aphi]
  | succ a ih =>
    have e : (a + 1) * p = a * p + p := by ring
    rw [Aphi, e, Finset.sum_range_add, ← Aphi, ih]
    have : ∀ x ∈ range p, ((a * p + x) / p) % 2 = a % 2 := by
      intro x hx
      have hx := Finset.mem_range.1 hx
      have : (a * p + x) / p = a := by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ hp, Nat.div_eq_of_lt hx]; simp
      rw [this]
    rw [Finset.sum_congr rfl this]
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]
    have e2 : (a + 1) / 2 = a / 2 + a % 2 := by omega
    rw [e2, Nat.mul_add]

theorem Aphi_part (p : ℕ) (hp : 0 < p) (a b : ℕ) (hb : b ≤ p) :
    Aphi p (a * p + b) = p * (a / 2) + b * (a % 2) := by
  rw [Aphi, Finset.sum_range_add, ← Aphi, Aphi_block p hp a]
  have : ∀ x ∈ range b, ((a * p + x) / p) % 2 = a % 2 := by
    intro x hx
    have hx := Finset.mem_range.1 hx
    have : (a * p + x) / p = a := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hp, Nat.div_eq_of_lt (by omega)]; simp
    rw [this]
  rw [Finset.sum_congr rfl this]
  simp [mul_comm]

/-- The arithmetic of the sawtooth: `A(2m) + ‖m‖_p ≤ m`. -/
theorem Aphi_min (p m : ℕ) (hodd : p % 2 = 1) :
    Aphi p (2 * m) + min (m % p) (p - m % p) ≤ m := by
  have hp : 0 < p := by omega
  have hdiv := Nat.div_add_mod (2 * m) p
  set a := (2 * m) / p with ha
  set b := (2 * m) % p with hb
  have hbp : b < p := Nat.mod_lt _ hp
  have hA : Aphi p (2 * m) = p * (a / 2) + b * (a % 2) := by
    have : 2 * m = a * p + b := by rw [Nat.mul_comm a p]; omega
    rw [this]; exact Aphi_part p hp a b hbp.le
  rcases Nat.even_or_odd' a with ⟨c, hc | hc⟩
  · -- a = 2c
    rw [hA, hc]
    have h1 : 2 * m = 2 * (c * p) + b := by rw [← hdiv, hc]; ring
    have hb2 : b % 2 = 0 := by omega
    have hm : m = c * p + b / 2 := by omega
    have hmod : m % p = b / 2 := by
      rw [hm, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
    have : p * (2 * c / 2) = c * p := by
      rw [Nat.mul_div_cancel_left c (by norm_num : 0 < 2), mul_comm]
    rw [this]
    have e0 : 2 * c % 2 = 0 := by omega
    rw [e0]
    have : min (m % p) (p - m % p) ≤ m % p := min_le_left _ _
    omega
  · -- a = 2c + 1
    rw [hA, hc]
    have h1 : 2 * m = 2 * (c * p) + p + b := by rw [← hdiv, hc]; ring
    have hb2 : (p + b) % 2 = 0 := by omega
    have hm : m = c * p + (p + b) / 2 := by omega
    have hlt : (p + b) / 2 < p := by omega
    have hmod : m % p = (p + b) / 2 := by
      rw [hm, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlt]
    have : p * ((2 * c + 1) / 2) = c * p := by
      have : (2 * c + 1) / 2 = c := by omega
      rw [this, mul_comm]
    rw [this]
    have e3 : (2 * c + 1) % 2 = 1 := by omega
    rw [e3]
    have : min (m % p) (p - m % p) ≤ p - m % p := min_le_right _ _
    omega

theorem uRow_window (p N r m i : ℕ) (hodd : p % 2 = 1) (hN : N = r + 2 * m) (hi : i < m) :
    uRow p N (r + 2 * i) = 1 + ((2 * (m - 1 - i) + 1) / p) % 2 := by
  have e : N - 1 - (r + 2 * i) = 2 * (m - 1 - i) + 1 := by omega
  have h := parity_mod p (2 * (m - 1 - i) + 1) hodd
  unfold uRow; rw [e]
  split_ifs <;> omega

theorem uCol_window (p N r m i : ℕ) (hodd : p % 2 = 1) (hN : N = r + 2 * m) (hi : i < m) :
    uCol p N (r + 2 * i + 1) = 1 + ((2 * (m - 1 - i)) / p) % 2 := by
  have e : N - 1 - (r + 2 * i + 1) = 2 * (m - 1 - i) := by omega
  have h := parity_mod p (2 * (m - 1 - i)) hodd
  unfold uCol; rw [e]
  split_ifs <;> omega

theorem window_sum (p m : ℕ) :
    ∑ k ∈ range m, ((1 + ((2 * k + 1) / p) % 2) + (1 + ((2 * k) / p) % 2)) = 2 * m + Aphi p (2 * m) := by
  induction m with
  | zero => simp [Aphi]
  | succ m ih =>
    rw [Finset.sum_range_succ, ih, Aphi, Aphi, show 2 * (m + 1) = 2 * m + 1 + 1 by ring,
      Finset.sum_range_succ, Finset.sum_range_succ]
    omega

end P1
end Rows

section P1Row

variable {p : ℕ} [hp : Fact p.Prime] (v u : ℤ)
  {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **Row P1** (Prop 2.3): `v_p(den) ≤ 3 (r + m) - ‖m‖_p`, with `‖m‖_p = min (m mod p, p - m mod p)`. -/
theorem row_P1 (cn : ι → ℕ) (hinj : Function.Injective cn) {r m : ℕ} (hcr : ∀ a, cn a < r)
    (hN : 2 * (r + 2 * m) < p * p) (hp5 : 5 ≤ p) :
    GLE p (3 * (r + m) - min (m % p) (p - m % p)) (rowDet v u cn r m) := by
  have hodd := odd_of_five (p := p) hp5
  have hc : ∀ a, cn a < r + 2 * m := fun a => by have := hcr a; omega
  have hx : ∀ i : Fin m, r + 2 * (i : ℕ) < r + 2 * m := fun i => by have := i.2; omega
  have hy : ∀ i : Fin m, r + 2 * (i : ℕ) + 1 < r + 2 * m := fun i => by have := i.2; omega
  have h := det_gle_of_dual v u hN cn (fun i : Fin m => r + 2 * (i : ℕ))
    (fun i : Fin m => r + 2 * (i : ℕ) + 1) hc hx hy
    (fun a => uRow p (r + 2 * m) (Sum.elim cn (fun i : Fin m => r + 2 * (i : ℕ)) a))
    (fun b => uCol p (r + 2 * m) (Sum.elim cn (fun i : Fin m => r + 2 * (i : ℕ) + 1) b))
    (fun a b => Wt_le_uRow_uCol u p _ (by rcases a with a | i; exacts [hc a, hx i])
      (by rcases b with b | i; exacts [hc b, hy i]))
  refine h.mono ?_
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  have hcard : Fintype.card ι ≤ r := by
    have := Fintype.card_le_of_injective (fun a : ι => (⟨cn a, hcr a⟩ : Fin r))
      (fun a b hab => hinj (by simpa using hab))
    simpa using this
  have hcom : ∑ a : ι, uRow p (r + 2 * m) (cn a) + ∑ a : ι, uCol p (r + 2 * m) (cn a) = 3 * Fintype.card ι := by
    rw [← Finset.sum_add_distrib]
    simp [uRow_add_uCol, mul_comm]
  have hwin : ∑ i : Fin m, uRow p (r + 2 * m) (r + 2 * (i : ℕ)) +
      ∑ i : Fin m, uCol p (r + 2 * m) (r + 2 * (i : ℕ) + 1) = 2 * m + Aphi p (2 * m) := by
    rw [← Finset.sum_add_distrib]
    have : ∀ i : Fin m, uRow p (r + 2 * m) (r + 2 * (i : ℕ)) + uCol p (r + 2 * m) (r + 2 * (i : ℕ) + 1) =
        ((1 + ((2 * (m - 1 - (i : ℕ)) + 1) / p) % 2) + (1 + ((2 * (m - 1 - (i : ℕ))) / p) % 2)) := by
      intro i
      rw [uRow_window p _ r m i hodd rfl i.2, uCol_window p _ r m i hodd rfl i.2]
    rw [Finset.sum_congr rfl (fun i _ => this i),
      Fin.sum_univ_eq_sum_range (fun i => ((1 + ((2 * (m - 1 - i) + 1) / p) % 2) +
        (1 + ((2 * (m - 1 - i)) / p) % 2))) m,
      Finset.sum_range_reflect (fun k => ((1 + ((2 * k + 1) / p) % 2) + (1 + ((2 * k) / p) % 2))) m,
      window_sum]
  have hmin := Aphi_min p m hodd
  omega

end P1Row

end CatalanCore.Uniform.Content.Sweep


#print axioms CatalanCore.Uniform.Content.Sweep.det_gle_phi
#print axioms CatalanCore.Uniform.Content.Sweep.row_P1
#print axioms CatalanCore.Uniform.Content.Sweep.row_P4
#print axioms CatalanCore.Uniform.Content.Sweep.row_P5
#print axioms CatalanCore.Uniform.Content.Sweep.row_P6
#print axioms CatalanCore.Uniform.Content.Sweep.row_P7
