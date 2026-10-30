module

public import CatalanCore.Uniform.Content.BankShared.TwoTerm.PrefixDet
public import CatalanCore.Uniform.Content.BankShared.TwoTerm.M3D

@[expose] public section
set_option Elab.async false

/-! # The prefix rule: M3D with the border reduced modulo `p` (paper `prefix-rule-2026-10-29`)

Theorem 1 of the paper, for every frame with periodic pole data (`PoleData`, so `N < p²` and all
poles simple): write `m = n p + M` and `N_n = r + 2M`.  A window `[a, b)` with
`max(r, N_n - p) ≤ a ≤ b ≤ min(N_n, r + p)` whose interior holds no cut (`p ∣ t` or a singular `t`)
prices every deletion member at `2r + 2m - (b - a)` (debit 0).  For `n = 0` this is M3D.

The proof is the rank argument of the paper (Steps 1-5), not the tropical one:

* `B = p² Full(X)` (uniform potentials `1`) is integral; modulo `p` its entries are
  `bt s t = p² M(s, t) mod p`, which vanish off the residue classes (`bt_off`) and are invariant
  under the translation between window classes (`bt_shift`, from `V_shift`, `W_shift`);
* the residue class of the first good window position `w0` carries a template block with one
  more row than column (`card_O_lt`), hence a kernel vector `lam` (`exists_kernel`);
* translates of `lam` are left kernel vectors on the `X`-classes and right kernel vectors on the
  `Y`-classes (`row_kernel`); their pairings through the first-order part `p M(s, t) mod p`
  vanish by antisymmetry (`pair_zero`);
* `pow_dvd_det_of_pivots` (Step 5) gives one factor `p` per complete window class
  (`prefix_dvd`); a deleted common node spoils at most one class (`card_good`).

Main statements: `prefix_gle` (any frame, any member core), `preLayer` (the debit-0 layer),
`pre_gap_tt` (two-term frames on `altGeom`). -/

open Polynomial Finset Matrix CatalanCore CatalanCore.Basic CatalanCore.Linalg CatalanCore.Arith.Hybrid
  CatalanCore.Arith.Hybrid.Periodic CatalanCore.Arith.Hybrid.ChainClasses CatalanCore.Uniform
  CatalanCore.Uniform.Content.Smith CatalanCore.Uniform.Content.Wire CatalanCore.Uniform.Content.Member
  CatalanCore.Uniform.Content.Shape CatalanCore.Uniform.Content.BankShared CatalanCore.Rect

namespace CatalanCore.Uniform.Content.BankShared.TwoTerm.Pre

/-! ### Arithmetic of residues -/

section Arith

theorem eq_of_mod_eq_lt {p x y : ℕ} (h : x % p = y % p) (hxy : y ≤ x) (hx : x < y + p) : x = y := by
  have h1 := Nat.sub_mod_eq_zero_of_mod_eq h
  rw [Nat.mod_eq_of_lt (by omega : x - y < p)] at h1
  omega

theorem le_of_mod_eq_lt {p x y : ℕ} (h : x % p = y % p) (hx : y < x + p) : y ≤ x := by
  by_contra hlt
  have := eq_of_mod_eq_lt h.symm (by omega) hx
  omega

theorem eq_of_mod_eq_window {p x y lo : ℕ} (h : x % p = y % p) (hx : lo ≤ x) (hy : lo ≤ y)
    (hx' : x < lo + p) (hy' : y < lo + p) : x = y := by
  rcases le_total x y with hxy | hxy
  · exact (eq_of_mod_eq_lt h.symm hxy (by omega)).symm
  · exact eq_of_mod_eq_lt h hxy (by omega)

theorem add_le_of_mod_eq {p x y : ℕ} (hp : 0 < p) (h : x % p = y % p) (hxy : x < y) : x + p ≤ y := by
  have h2 : p ∣ y - x := Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq h.symm)
  have h3 := Nat.le_of_dvd (by omega) h2
  omega

theorem exists_add_mul {p x y : ℕ} (h : x % p = y % p) (hxy : y ≤ x) : ∃ j, x = y + p * j := by
  obtain ⟨j, hj⟩ := Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq h)
  exact ⟨j, by omega⟩

theorem mod_add_shift {p t w0 w : ℕ} (ht : t % p = w0 % p) (hw : w0 ≤ w) :
    (t + (w - w0)) % p = w % p := by
  have h : t + (w - w0) ≡ w0 + (w - w0) [MOD p] := Nat.ModEq.add_right _ ht
  rwa [Nat.add_sub_cancel' hw] at h

theorem mod_sub_shift {p t w0 w : ℕ} (ht : t % p = w % p) (hw : w0 ≤ w) (hδ : w - w0 ≤ t) :
    (t - (w - w0)) % p = w0 % p := by
  have h : t - (w - w0) + (w - w0) ≡ w0 + (w - w0) [MOD p] := by
    rw [Nat.sub_add_cancel hδ, Nat.add_sub_cancel' hw]; exact ht
  exact Nat.ModEq.add_right_cancel' _ h

theorem mul_mod_two_odd {p j : ℕ} (hp : p % 2 = 1) : (p * j) % 2 = j % 2 := by
  rw [Nat.mul_mod, hp, one_mul, Nat.mod_mod]

end Arith

/-! ### Windows and residue classes -/

/-- The window hypotheses of Theorem 1, with `m = n p + M` (so `N_n = r + 2M`). -/
structure Win (p r m n M a b : ℕ) : Prop where
  hm : m = n * p + M
  hp2 : p % 2 = 1
  hra : r ≤ a
  hab : a ≤ b
  hbp : b ≤ r + p
  hbN : b ≤ r + 2 * M
  haN : r + 2 * M ≤ a + p

/-- The nodes `t < N` of the residue class of `w`: all common nodes `t < r`, and the border nodes
with `t - r + e ≡ w - r (mod 2)` (`e = 0`: the larger side, `e = 1`: the smaller side). -/
def cls (N r p w e : ℕ) : Finset ℕ :=
  (range N).filter (fun t => t % p = w % p ∧ (t < r ∨ (t - r + e) % 2 = (w - r) % 2))

theorem mem_cls {N r p w e t : ℕ} :
    t ∈ cls N r p w e ↔ t < N ∧ t % p = w % p ∧ (t < r ∨ (t - r + e) % 2 = (w - r) % 2) := by
  unfold cls; rw [mem_filter, mem_range]

section Win

variable {p r m n M a b : ℕ}

/-- The window hypotheses with `M` in the normal form `m - n p`. -/
theorem Win.norm (W : Win p r m n M a b) : Win p r m n (m - n * p) a b := by
  have h := W.hm
  obtain rfl : M = m - n * p := by omega
  exact W

/-- A border node of the class of a window position `w0` is `w0 + p j`, `j ≤ 2n`. -/
theorem border_j (W : Win p r m n M a b) {w0 t : ℕ} (hw0a : a ≤ w0) (hw0b : w0 < b)
    (ht : t % p = w0 % p) (hrt : r ≤ t) (htN : t < r + 2 * m) : ∃ j, t = w0 + p * j ∧ j ≤ 2 * n := by
  have h1 := W.hbp; have h2 := W.haN; have h3 := W.hm
  have hwt : w0 ≤ t := le_of_mod_eq_lt ht (by omega)
  obtain ⟨j, hj⟩ := exists_add_mul ht hwt
  refine ⟨j, hj, ?_⟩
  have e : p * (2 * n + 1) = 2 * (n * p) + p := by ring
  have h4 : p * j < p * (2 * n + 1) := by omega
  have := Nat.lt_of_mul_lt_mul_left h4
  omega

/-- **Translation** `t ↦ t + (w - w0)` maps the class of `w0` into the class of `w`. -/
theorem cls_shift (W : Win p r m n M a b) [Fact p.Prime] {w0 w e t : ℕ} (hw0a : a ≤ w0)
    (hw0w : w0 ≤ w) (hwb : w < b) (ht : t ∈ cls (r + 2 * m) r p w0 e) :
    t + (w - w0) ∈ cls (r + 2 * m) r p w e := by
  rw [mem_cls] at ht ⊢
  obtain ⟨htN, htp, hpar⟩ := ht
  have h1 := W.hbp; have h2 := W.hbN; have h3 := W.hra; have h4 := W.hm
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  refine ⟨?_, mod_add_shift htp hw0w, ?_⟩
  · by_cases hr : t < r
    · have := add_le_of_mod_eq hp0 htp (by omega : t < w0)
      omega
    · obtain ⟨j, hj, hjn⟩ := border_j W hw0a (by omega) htp (by omega) htN
      have h5 : p * j ≤ p * (2 * n) := Nat.mul_le_mul_left p hjn
      have e2 : p * (2 * n) = 2 * (n * p) := by ring
      omega
  · by_cases hr : t < r
    · left
      have := add_le_of_mod_eq hp0 htp (by omega : t < w0)
      omega
    · right
      have hpar' := hpar.resolve_left hr
      omega

/-- **Translation back**: with no multiple of `p` in `(w0, w]`, the class of `w` is the
translate of the class of `w0`. -/
theorem cls_unshift (W : Win p r m n M a b) [Fact p.Prime] {w0 w e t : ℕ} (hw0a : a ≤ w0)
    (hw0w : w0 ≤ w) (hwb : w < b) (hfree0 : ∀ x, w0 < x → x ≤ w → ¬ p ∣ x)
    (ht : t ∈ cls (r + 2 * m) r p w e) :
    w - w0 ≤ t ∧ t - (w - w0) ∈ cls (r + 2 * m) r p w0 e := by
  rw [mem_cls] at ht
  obtain ⟨htN, htp, hpar⟩ := ht
  have h1 := W.hbp; have h3 := W.hra
  have hδ : w - w0 ≤ t := by
    by_cases hr : t < r
    · have hu : p ∣ w - t := Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq htp.symm)
      by_contra hc
      exact hfree0 (w - t) (by omega) (by omega) hu
    · have := le_of_mod_eq_lt htp (by omega)
      omega
  refine ⟨hδ, ?_⟩
  rw [mem_cls]
  refine ⟨by omega, mod_sub_shift htp hw0w hδ, ?_⟩
  rcases hpar with h | h
  · left; omega
  · by_cases hr : t < r
    · left; omega
    · right
      have := le_of_mod_eq_lt htp (by omega)
      omega

/-- **The template has one more row than column**: `|O(w0)| < |E(w0)|`. -/
theorem card_O_lt (W : Win p r m n M a b) {w0 : ℕ} (hw0a : a ≤ w0) (hw0b : w0 < b) :
    (cls (r + 2 * m) r p w0 1).card < (cls (r + 2 * m) r p w0 0).card := by
  have h1 := W.hbp; have h2 := W.hbN; have h3 := W.hra; have h4 := W.hm; have hp2 := W.hp2
  have hw0 : w0 ∈ cls (r + 2 * m) r p w0 0 := by
    rw [mem_cls]; exact ⟨by omega, rfl, Or.inr (by omega)⟩
  have h : (cls (r + 2 * m) r p w0 1).card ≤ ((cls (r + 2 * m) r p w0 0).erase w0).card := by
    refine Finset.card_le_card_of_injOn (fun t => if t < r then t else t + p) ?_ ?_
    · intro t ht
      rw [Finset.mem_coe, mem_cls] at ht
      rw [Finset.mem_coe, Finset.mem_erase, mem_cls]
      obtain ⟨htN, htp, hpar⟩ := ht
      by_cases hr : t < r
      · simp only [if_pos hr]
        exact ⟨by omega, htN, htp, Or.inl hr⟩
      · simp only [if_neg hr]
        have hpar' := hpar.resolve_left hr
        obtain ⟨j, hj, hjn⟩ := border_j W hw0a hw0b htp (by omega) htN
        have hpj := mul_mod_two_odd (j := j) hp2
        have hjo : j % 2 = 1 := by omega
        have h5 : p * (j + 1) ≤ p * (2 * n) := Nat.mul_le_mul_left p (by omega)
        have e2 : p * (2 * n) = 2 * (n * p) := by ring
        have e3 : p * (j + 1) = p * j + p := by ring
        refine ⟨by omega, by omega, ?_, Or.inr (by omega)⟩
        rw [Nat.add_mod_right]; exact htp
    · intro t1 _ t2 _ h
      beta_reduce at h
      split_ifs at h <;> omega
  rw [Finset.card_erase_of_mem hw0] at h
  have : 0 < (cls (r + 2 * m) r p w0 0).card := Finset.card_pos.2 ⟨w0, hw0⟩
  omega

end Win

/-! ### The reductions and their translation invariance -/

section Shift

variable {Fr : Frame} {p : ℕ} [Fact p.Prime] {N : ℕ}

/-- `p² M(s, t) mod p`: the reduction of the scaled hybrid entry. -/
noncomputable def bt (Fr : Frame) (p : ℕ) [Fact p.Prime] (s t : ℕ) : ZMod p :=
  red p ((p : ℚ) ^ 2 * Fr.Mn s t)

theorem mn_comm (Fr : Frame) (s t : ℕ) : Fr.Mn s t = Fr.Mn t s := by
  unfold Frame.Mn
  by_cases h : s = t
  · subst h; rfl
  · rw [if_neg h, if_neg (Ne.symm h), max_comm, min_comm]

theorem bt_comm (s t : ℕ) : bt Fr p s t = bt Fr p t s := by
  unfold bt; rw [mn_comm]

/-- Off the residue classes the reduction vanishes. -/
theorem bt_off (D : PoleData Fr p N) {s t : ℕ} (hs : s < N) (ht : t < N) (hst : s % p ≠ t % p) :
    bt Fr p s t = 0 := by
  have hd : ((t : ZMod p) - s) ≠ 0 := by
    intro h
    exact hst ((ZMod.natCast_eq_natCast_iff' t s p).1 (sub_eq_zero.1 h)).symm
  have g := (D.good_cross hs ht hd).ell_mul
  unfold bt
  rw [show (p : ℚ) ^ 2 * Fr.Mn s t = (p : ℚ) * ((p : ℚ) * Fr.Mn s t) by ring]
  exact g.eq

theorem sing_shift (D : PoleData Fr p N) {s w0 i : ℕ} (hs : s % p = w0 % p) :
    D.singular ((s + i : ℕ) : ℤ) ↔ D.singular ((w0 + i : ℕ) : ℤ) := by
  obtain ⟨j, hj⟩ := (Nat.ModEq.dvd hs : (p : ℤ) ∣ (w0 : ℤ) - s)
  have e : ((s + i : ℕ) : ℤ) = ((w0 + i : ℕ) : ℤ) + (-j) * p := by push_cast; linarith
  rw [e, D.periodic]

theorem V_shift (D : PoleData Fr p N) {s w0 δ : ℕ} (hs : s % p = w0 % p) (hN : s + δ < N)
    (hfree : ∀ i, 1 ≤ i → i ≤ δ → ¬ D.singular ((w0 + i : ℕ) : ℤ)) : D.V (s + δ) = D.V s := by
  rw [← sub_eq_zero, D.V_sub (Nat.le_add_right s δ)]
  refine Finset.sum_eq_zero (fun k hk => ?_)
  obtain ⟨hk1, hk2⟩ := Finset.mem_Ioc.1 hk
  refine D.dv_zero (by omega) (by omega) ?_
  have e : k = s + (k - s) := by omega
  rw [e, sing_shift D hs]
  exact hfree _ (by omega) (by omega)

theorem W_sub (D : PoleData Fr p N) {a b : ℕ} (hab : a ≤ b) :
    D.W b - D.W a = ∑ k ∈ Ioc a b, D.sv k := by
  have he (n : ℕ) : Icc 1 n = Ioc 0 n := by ext k; simp only [mem_Icc, mem_Ioc]; omega
  unfold PoleData.W
  rw [he, he, ← Finset.sum_Ioc_consecutive _ (Nat.zero_le a) hab]
  ring

theorem W_shift (D : PoleData Fr p N) {s w0 δ : ℕ} (hs : s % p = w0 % p) (hN : s + δ < N)
    (hfree : ∀ i, 1 ≤ i → i ≤ δ → ¬ D.singular ((w0 + i : ℕ) : ℤ)) : D.W (s + δ) = D.W s := by
  rw [← sub_eq_zero, W_sub D (Nat.le_add_right s δ)]
  refine Finset.sum_eq_zero (fun k hk => ?_)
  obtain ⟨hk1, hk2⟩ := Finset.mem_Ioc.1 hk
  refine D.sv_zero (by omega) (by omega) ?_
  have e : k = s + (k - s) := by omega
  rw [e, sing_shift D hs]
  exact hfree _ (by omega) (by omega)

/-- **Step 3 (translation)**: the reductions of the class blocks are translation invariant. -/
theorem bt_shift (D : PoleData Fr p N) (hNp : N < p * p) {s t w0 δ : ℕ} (hs : s % p = w0 % p)
    (ht : t % p = w0 % p) (hsN : s + δ < N) (htN : t + δ < N)
    (hfree : ∀ i, 1 ≤ i → i ≤ δ → ¬ D.singular ((w0 + i : ℕ) : ℤ)) :
    bt Fr p (s + δ) (t + δ) = bt Fr p s t := by
  have Vs := V_shift D hs hsN hfree
  have Vt := V_shift D ht htN hfree
  rcases lt_trichotomy s t with h | rfl | h
  · unfold bt
    rw [(D.good_square hNp (by omega : s + δ < t + δ) htN).eq, (D.good_square hNp h (by omega)).eq,
      Vs, Vt, show t + δ - (s + δ) = t - s by omega]
  · unfold bt
    rw [(D.good_diagonal hsN).eq, (D.good_diagonal (by omega)).eq, W_shift D hs hsN hfree]
  · rw [bt_comm (s + δ) (t + δ), bt_comm s t]
    unfold bt
    rw [(D.good_square hNp (by omega : t + δ < s + δ) hsN).eq, (D.good_square hNp h (by omega)).eq,
      Vs, Vt, show s + δ - (t + δ) = s - t by omega]

/-- The first-order reduction `p M(t, t') mod p` off the residue classes (`0` on them). -/
noncomputable def gam (D : PoleData Fr p N) (t t' : ℕ) : ZMod p :=
  if t % p ≠ t' % p then ((red p Fr.norm) * ((t' : ZMod p) - t))⁻¹ * (D.V t' - D.V t) else 0

end Shift

/-! ### The kernel vector of the template block -/

section Kernel

variable {p : ℕ} [Fact p.Prime]

theorem exists_kernel (E O : Finset ℕ) (β : ℕ → ℕ → ZMod p) (hc : O.card < E.card) :
    ∃ v : ℕ → ZMod p, (∀ t, t ∉ E → v t = 0) ∧ (∃ s ∈ E, v s ≠ 0) ∧
      ∀ t ∈ O, ∑ s ∈ E, v s * β s t = 0 := by
  classical
  let A : Matrix E O (ZMod p) := Matrix.of fun s t => β s t
  have hfr : Module.finrank (ZMod p) (O → ZMod p) < Module.finrank (ZMod p) (E → ZMod p) := by
    rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card, Fintype.card_coe,
      Fintype.card_coe]
    exact hc
  obtain ⟨v, hv, hv0⟩ :=
    (Submodule.ne_bot_iff _).1 (LinearMap.ker_ne_bot_of_finrank_lt (f := Matrix.vecMulLinear A) hfr)
  have hv' : v ᵥ* A = 0 := LinearMap.mem_ker.1 hv
  obtain ⟨s0, hs0⟩ : ∃ s0, v s0 ≠ 0 := by
    by_contra h
    push_neg at h
    exact hv0 (funext h)
  refine ⟨fun t => if h : t ∈ E then v ⟨t, h⟩ else 0, ?_, ⟨s0.1, s0.2, ?_⟩, ?_⟩
  · intro t ht
    simp only [dif_neg ht]
  · simp only [dif_pos s0.2]
    exact hs0
  · intro t ht
    have h1 := congrFun hv' ⟨t, ht⟩
    simp only [Matrix.vecMul, dotProduct, A, Matrix.of_apply, Pi.zero_apply] at h1
    rw [← Finset.sum_coe_sort E]
    calc ∑ x : E, (if h : (x : ℕ) ∈ E then v ⟨x, h⟩ else 0) * β x t
        = ∑ x : E, v x * β x t := Finset.sum_congr rfl (fun x _ => by rw [dif_pos x.2])
      _ = 0 := h1

/-- The translate of the kernel vector by `δ`. -/
def vec (lam : ℕ → ZMod p) (δ t : ℕ) : ZMod p := if δ ≤ t then lam (t - δ) else 0

/-- Pairings of translates vanish (antisymmetry). -/
theorem antisym (E : Finset ℕ) (lam V : ℕ → ZMod p) (c : ZMod p) :
    ∑ s ∈ E, lam s * (∑ s' ∈ E, lam s' * (c * (V s' - V s))) = 0 := by
  calc ∑ s ∈ E, lam s * (∑ s' ∈ E, lam s' * (c * (V s' - V s)))
      = ∑ s ∈ E, (c * lam s * (∑ s' ∈ E, lam s' * V s') - c * (lam s * V s) * (∑ s' ∈ E, lam s')) := by
        refine Finset.sum_congr rfl (fun s _ => ?_)
        simp only [Finset.mul_sum]
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl (fun s' _ => by ring)
    _ = c * (∑ s ∈ E, lam s) * (∑ s' ∈ E, lam s' * V s') -
          c * (∑ s ∈ E, lam s * V s) * (∑ s' ∈ E, lam s') := by
        rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.mul_sum,
          ← Finset.mul_sum]
    _ = 0 := by ring

end Kernel

/-! ### Translates of the kernel vector -/

section Transport

variable {p r m n M a b : ℕ} [Fact p.Prime]

theorem vec_mem (W : Win p r m n M a b) {w0 w : ℕ} (hw0a : a ≤ w0) (hw0w : w0 ≤ w) (hwb : w < b)
    {lam : ℕ → ZMod p} (hlamE : ∀ t, t ∉ cls (r + 2 * m) r p w0 0 → lam t = 0) {t : ℕ}
    (h : vec lam (w - w0) t ≠ 0) : t ∈ cls (r + 2 * m) r p w 0 := by
  unfold vec at h
  split_ifs at h with hle
  · have hmem : t - (w - w0) ∈ cls (r + 2 * m) r p w0 0 := by
      by_contra hc; exact h (hlamE _ hc)
    have := cls_shift W hw0a hw0w hwb hmem
    rwa [Nat.sub_add_cancel hle] at this
  · exact absurd rfl h

theorem sum_shift (W : Win p r m n M a b) {w0 w : ℕ} (hw0a : a ≤ w0) (hw0w : w0 ≤ w) (hwb : w < b)
    (hfree0 : ∀ x, w0 < x → x ≤ w → ¬ p ∣ x) (lam : ℕ → ZMod p) (f : ℕ → ZMod p) :
    ∑ t ∈ cls (r + 2 * m) r p w 0, vec lam (w - w0) t * f t =
      ∑ s ∈ cls (r + 2 * m) r p w0 0, lam s * f (s + (w - w0)) := by
  symm
  refine Finset.sum_nbij' (fun s => s + (w - w0)) (fun t => t - (w - w0)) ?_ ?_ ?_ ?_ ?_
  · intro s hs; exact cls_shift W hw0a hw0w hwb hs
  · intro t ht; exact (cls_unshift W hw0a hw0w hwb hfree0 ht).2
  · intro s _; simp
  · intro t ht; exact Nat.sub_add_cancel (cls_unshift W hw0a hw0w hwb hfree0 ht).1
  · intro s _
    simp only [vec, if_pos (Nat.le_add_left (w - w0) s), Nat.add_sub_cancel]

variable {Fr : Frame}

/-- **Kernel transport**: the translate of `lam` to the class of `w` kills every column node
`t'` (those of the class of `w` lie on the smaller side, `cls _ 1`). -/
theorem row_kernel (W : Win p r m n M a b) (D : PoleData Fr p (r + 2 * m)) (hNp : r + 2 * m < p * p)
    {w0 w : ℕ} (hw0a : a ≤ w0) (hw0w : w0 ≤ w) (hwb : w < b)
    (hfree0 : ∀ x, w0 < x → x ≤ w → ¬ p ∣ x)
    (hfree : ∀ i, 1 ≤ i → i ≤ w - w0 → ¬ D.singular ((w0 + i : ℕ) : ℤ))
    (lam : ℕ → ZMod p)
    (hker : ∀ t ∈ cls (r + 2 * m) r p w0 1, ∑ s ∈ cls (r + 2 * m) r p w0 0, lam s * bt Fr p s t = 0)
    {t' : ℕ} (ht'N : t' < r + 2 * m) (ht' : t' % p = w % p → t' ∈ cls (r + 2 * m) r p w 1) :
    ∑ t ∈ cls (r + 2 * m) r p w 0, vec lam (w - w0) t * bt Fr p t t' = 0 := by
  rw [sum_shift W hw0a hw0w hwb hfree0 lam (fun t => bt Fr p t t')]
  beta_reduce
  by_cases h : t' % p = w % p
  · obtain ⟨hδ, hmem⟩ := cls_unshift W hw0a hw0w hwb hfree0 (ht' h)
    obtain ⟨u, rfl⟩ : ∃ u, t' = u + (w - w0) := ⟨t' - (w - w0), by omega⟩
    rw [Nat.add_sub_cancel] at hmem
    refine (Finset.sum_congr rfl (fun s hs' => ?_)).trans (hker u hmem)
    congr 1
    exact bt_shift D hNp (mem_cls.1 hs').2.1 (mem_cls.1 hmem).2.1
      (mem_cls.1 (cls_shift W hw0a hw0w hwb hs')).1 ht'N hfree
  · refine Finset.sum_eq_zero (fun s hs' => ?_)
    have hsh := mem_cls.1 (cls_shift W hw0a hw0w hwb hs')
    rw [bt_off D hsh.1 ht'N (by rw [hsh.2.1]; exact fun e => h e.symm), mul_zero]

/-- **Step 4**: the pairings of two translates through the first-order reductions vanish. -/
theorem pair_zero (W : Win p r m n M a b) (D : PoleData Fr p (r + 2 * m))
    {w0 w1 w2 : ℕ} (hw0a : a ≤ w0) (h1 : w0 ≤ w1) (h1b : w1 < b) (h2 : w0 ≤ w2) (h2b : w2 < b)
    (hne : w1 ≠ w2)
    (hfree01 : ∀ x, w0 < x → x ≤ w1 → ¬ p ∣ x) (hfree02 : ∀ x, w0 < x → x ≤ w2 → ¬ p ∣ x)
    (hfree1 : ∀ i, 1 ≤ i → i ≤ w1 - w0 → ¬ D.singular ((w0 + i : ℕ) : ℤ))
    (hfree2 : ∀ i, 1 ≤ i → i ≤ w2 - w0 → ¬ D.singular ((w0 + i : ℕ) : ℤ))
    (lam : ℕ → ZMod p) :
    ∑ t ∈ cls (r + 2 * m) r p w1 0, vec lam (w1 - w0) t *
      (∑ t' ∈ cls (r + 2 * m) r p w2 0, vec lam (w2 - w0) t' * gam D t t') = 0 := by
  have hb := W.hbp; have hra := W.hra
  rw [sum_shift W hw0a h1 h1b hfree01 lam
    (fun t => ∑ t' ∈ cls (r + 2 * m) r p w2 0, vec lam (w2 - w0) t' * gam D t t')]
  beta_reduce
  obtain ⟨c, hc⟩ : ∃ c : ZMod p,
      c = ((red p Fr.norm) * (((w2 - w0 : ℕ) : ZMod p) - ((w1 - w0 : ℕ) : ZMod p)))⁻¹ := ⟨_, rfl⟩
  have key : ∀ s ∈ cls (r + 2 * m) r p w0 0, ∀ s' ∈ cls (r + 2 * m) r p w0 0,
      gam D (s + (w1 - w0)) (s' + (w2 - w0)) = c * (D.V s' - D.V s) := by
    intro s hs s' hs'
    have ms := mem_cls.1 hs
    have ms' := mem_cls.1 hs'
    have m1 := mem_cls.1 (cls_shift W hw0a h1 h1b hs)
    have m2 := mem_cls.1 (cls_shift W hw0a h2 h2b hs')
    have hcls : (s + (w1 - w0)) % p ≠ (s' + (w2 - w0)) % p := by
      rw [m1.2.1, m2.2.1]
      intro e
      exact hne (eq_of_mod_eq_window e (lo := a) (by omega) (by omega) (by omega) (by omega))
    have hss : (s' : ZMod p) = (s : ZMod p) :=
      (ZMod.natCast_eq_natCast_iff' s' s p).2 (ms'.2.1.trans ms.2.1.symm)
    have hdiff : ((s' + (w2 - w0) : ℕ) : ZMod p) - ((s + (w1 - w0) : ℕ) : ZMod p) =
        ((w2 - w0 : ℕ) : ZMod p) - ((w1 - w0 : ℕ) : ZMod p) := by
      push_cast; rw [hss]; ring
    unfold gam
    rw [if_pos hcls, hdiff, V_shift D ms'.2.1 m2.1 hfree2, V_shift D ms.2.1 m1.1 hfree1, hc]
  calc ∑ s ∈ cls (r + 2 * m) r p w0 0, lam s *
        (∑ t' ∈ cls (r + 2 * m) r p w2 0, vec lam (w2 - w0) t' * gam D (s + (w1 - w0)) t')
      = ∑ s ∈ cls (r + 2 * m) r p w0 0, lam s *
          (∑ s' ∈ cls (r + 2 * m) r p w0 0, lam s' * (c * (D.V s' - D.V s))) := by
        refine Finset.sum_congr rfl (fun s hs => ?_)
        congr 1
        rw [sum_shift W hw0a h2 h2b hfree02 lam (fun t' => gam D (s + (w1 - w0)) t')]
        beta_reduce
        exact Finset.sum_congr rfl (fun s' hs' => by rw [key s hs s' hs'])
    _ = 0 := antisym _ _ _ _

end Transport

/-! ### The member: nodes, lifts and the scaled matrix -/

section Member

variable {p : ℕ} [Fact p.Prime] {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Row nodes `C ⊔ X` and column nodes `C ⊔ Y` of a member with core `common`. -/
def rnode (r m : ℕ) (common : ι → ℕ) : ι ⊕ Fin m → ℕ := Sum.elim common (fun x => r + 2 * (x : ℕ))
def cnode (r m : ℕ) (common : ι → ℕ) : ι ⊕ Fin m → ℕ := Sum.elim common (fun x => r + 2 * (x : ℕ) + 1)

/-- Every common node of the class of `w` belongs to the member. -/
def ClsFull (common : ι → ℕ) (p r w : ℕ) : Prop := ∀ t, t < r → t % p = w % p → ∃ i, common i = t

instance ClsFull.dec (common : ι → ℕ) (p r w : ℕ) : Decidable (ClsFull common p r w) := by
  unfold ClsFull; infer_instance

variable {r m : ℕ} {common : ι → ℕ}

theorem rnode_inj (hinj : Function.Injective common) (hlt : ∀ i, common i < r) :
    Function.Injective (rnode r m common) := by
  intro u v h
  rcases u with u | u <;> rcases v with v | v <;> simp only [rnode, Sum.elim_inl, Sum.elim_inr] at h
  · exact congrArg Sum.inl (hinj h)
  · have := hlt u; omega
  · have := hlt v; omega
  · exact congrArg Sum.inr (Fin.ext (by omega))

theorem cnode_inj (hinj : Function.Injective common) (hlt : ∀ i, common i < r) :
    Function.Injective (cnode r m common) := by
  intro u v h
  rcases u with u | u <;> rcases v with v | v <;> simp only [cnode, Sum.elim_inl, Sum.elim_inr] at h
  · exact congrArg Sum.inl (hinj h)
  · have := hlt u; omega
  · have := hlt v; omega
  · exact congrArg Sum.inr (Fin.ext (by omega))

theorem rnode_lt (hlt : ∀ i, common i < r) (k : ι ⊕ Fin m) : rnode r m common k < r + 2 * m := by
  rcases k with i | x
  · have := hlt i; simp only [rnode, Sum.elim_inl]; omega
  · have := x.2; simp only [rnode, Sum.elim_inr]; omega

theorem cnode_lt (hlt : ∀ i, common i < r) (k : ι ⊕ Fin m) : cnode r m common k < r + 2 * m := by
  rcases k with i | x
  · have := hlt i; simp only [cnode, Sum.elim_inl]; omega
  · have := x.2; simp only [cnode, Sum.elim_inr]; omega

theorem row_cov {w : ℕ} (hw : ClsFull common p r w) (hpar : (w - r) % 2 = 0) {t : ℕ}
    (ht : t ∈ cls (r + 2 * m) r p w 0) : ∃ k, rnode r m common k = t := by
  rw [mem_cls] at ht
  obtain ⟨htN, htp, hpar'⟩ := ht
  by_cases hr : t < r
  · obtain ⟨i, hi⟩ := hw t hr htp
    exact ⟨Sum.inl i, hi⟩
  · have h := hpar'.resolve_left hr
    exact ⟨Sum.inr ⟨(t - r) / 2, by omega⟩, by simp only [rnode, Sum.elim_inr]; omega⟩

theorem col_cov {w : ℕ} (hw : ClsFull common p r w) (hpar : (w - r) % 2 = 1) {t : ℕ}
    (ht : t ∈ cls (r + 2 * m) r p w 0) : ∃ l, cnode r m common l = t := by
  rw [mem_cls] at ht
  obtain ⟨htN, htp, hpar'⟩ := ht
  by_cases hr : t < r
  · obtain ⟨i, hi⟩ := hw t hr htp
    exact ⟨Sum.inl i, hi⟩
  · have h := hpar'.resolve_left hr
    exact ⟨Sum.inr ⟨(t - r) / 2, by omega⟩, by simp only [cnode, Sum.elim_inr]; omega⟩

theorem col_in (hlt : ∀ i, common i < r) {w : ℕ} (hpar : (w - r) % 2 = 0) (l : ι ⊕ Fin m)
    (hl : cnode r m common l % p = w % p) : cnode r m common l ∈ cls (r + 2 * m) r p w 1 := by
  rw [mem_cls]
  refine ⟨cnode_lt hlt l, hl, ?_⟩
  rcases l with i | x
  · exact Or.inl (hlt i)
  · right; simp only [cnode, Sum.elim_inr]; omega

theorem row_in (hlt : ∀ i, common i < r) {w : ℕ} (hpar : (w - r) % 2 = 1) (k : ι ⊕ Fin m)
    (hk : rnode r m common k % p = w % p) : rnode r m common k ∈ cls (r + 2 * m) r p w 1 := by
  rw [mem_cls]
  refine ⟨rnode_lt hlt k, hk, ?_⟩
  rcases k with i | x
  · exact Or.inl (hlt i)
  · right; simp only [rnode, Sum.elim_inr]; omega

/-- The ring map `𝔽_p → 𝔽_p(X)`. -/
noncomputable def rc (p : ℕ) [Fact p.Prime] : ZMod p →+* RatFunc (ZMod p) :=
  (algebraMap (ZMod p)[X] (RatFunc (ZMod p))).comp Polynomial.C

/-- A total version of the inclusion `ℤ_(p) ⊆ ℚ`. -/
noncomputable def lq (p : ℕ) [Fact p.Prime] (x : ℚ) : LocRing p := by
  classical
  exact if h : x ∈ LocRing p then ⟨x, h⟩ else 0

theorem lq_coe {x : ℚ} (h : x ∈ LocRing p) : ((lq p x : LocRing p) : ℚ) = x := by
  unfold lq; rw [dif_pos h]

theorem redQ_lq {x : ℚ} (h : x ∈ LocRing p) : redQ p (lq p x) = red p x := by
  rw [redQ_apply, lq_coe h]; rfl

/-- The integral lift of a residue. -/
noncomputable def liftZ (z : ZMod p) : (LocRing p)[X] := C ((z.val : ℕ) : LocRing p)

theorem phiP_liftZ (z : ZMod p) : phiP p (liftZ z) = rc p z := by
  unfold liftZ
  rw [phiP_C, map_natCast, ZMod.natCast_zmod_val]; rfl

theorem liftZ_zero : liftZ (0 : ZMod p) = 0 := by
  simp [liftZ]

theorem toQ_C' (x : LocRing p) : toQ p (C x) = C (x : ℚ) := by simp [toQ]

theorem toQ_X' : toQ p (X : (LocRing p)[X]) = X := by simp [toQ]

variable (Fr : Frame)

/-- The scaled lift `p² Full(X)` (uniform potentials `1`). -/
noncomputable def gE (p : ℕ) [Fact p.Prime] (r m : ℕ) (common : ι → ℕ) (i j : ι ⊕ Fin m) :
    (LocRing p)[X] :=
  C (lq p ((p : ℚ) ^ 2 * Fr.Mn (rnode r m common i) (cnode r m common j))) +
    (if i = j ∧ i.isLeft = true then C ((p : ℕ) : LocRing p) ^ 2 * X else 0)

/-- The first-order lift `p Full(X)` off the residue classes (`0` on them). -/
noncomputable def hE (p : ℕ) [Fact p.Prime] (r m : ℕ) (common : ι → ℕ) (i j : ι ⊕ Fin m) :
    (LocRing p)[X] :=
  C (lq p (if rnode r m common i % p ≠ cnode r m common j % p then
    (p : ℚ) * Fr.Mn (rnode r m common i) (cnode r m common j) else 0))

theorem fullN_apply (i j : ι ⊕ Fin m) :
    FullN Fr common (fun x : Fin m => r + 2 * x.val) (fun y : Fin m => r + 2 * y.val + 1) (X : ℚ[X]) i j =
      C (Fr.Mn (rnode r m common i) (cnode r m common j)) + (if i = j ∧ i.isLeft = true then X else 0) := by
  rcases i with u | u <;> rcases j with v | v <;>
    simp [FullN, Blk, blkA, blkB, blkC, blkD, Matrix.one_apply, rnode, cnode, Polynomial.algebraMap_eq]

variable {Fr}

theorem toQ_gE (D : PoleData Fr p (r + 2 * m)) (hNp : r + 2 * m < p * p) (hlt : ∀ i, common i < r)
    (i j : ι ⊕ Fin m) :
    toQ p (gE Fr p r m common i j) = C ((p : ℚ) ^ (1 + 1)) *
      FullN Fr common (fun x : Fin m => r + 2 * x.val) (fun y : Fin m => r + 2 * y.val + 1) (X : ℚ[X]) i j := by
  have hmem := D.square_mem hNp (rnode_lt hlt i) (cnode_lt hlt j)
  rw [fullN_apply, show (1 + 1 : ℕ) = 2 from rfl]
  unfold gE
  split_ifs
  · rw [map_add, map_mul, toQ_C_natCast, toQ_X', toQ_C', lq_coe hmem, C_mul, C_pow]
    ring
  · rw [map_add, map_zero, toQ_C', lq_coe hmem, C_mul, C_pow]
    ring

theorem phiP_gE (D : PoleData Fr p (r + 2 * m)) (hNp : r + 2 * m < p * p) (hlt : ∀ i, common i < r)
    (i j : ι ⊕ Fin m) :
    phiP p (gE Fr p r m common i j) = rc p (bt Fr p (rnode r m common i) (cnode r m common j)) := by
  have hmem := D.square_mem hNp (rnode_lt hlt i) (cnode_lt hlt j)
  have h0 : phiP p (C ((p : ℕ) : LocRing p)) = 0 := (phiP_eq_zero_iff p _).2 dvd_rfl
  unfold gE
  split_ifs
  · rw [map_add, map_mul, map_pow, h0, phiP_C, redQ_lq hmem, zero_pow two_ne_zero, zero_mul, add_zero]
    rfl
  · rw [map_add, map_zero, add_zero, phiP_C, redQ_lq hmem]
    rfl

theorem gE_off (D : PoleData Fr p (r + 2 * m)) (hNp : r + 2 * m < p * p) (hlt : ∀ i, common i < r)
    {i j : ι ⊕ Fin m} (hij : rnode r m common i % p ≠ cnode r m common j % p) :
    gE Fr p r m common i j = C ((p : ℕ) : LocRing p) * hE Fr p r m common i j := by
  have hd : ((cnode r m common j : ZMod p) - rnode r m common i) ≠ 0 := by
    intro h
    exact hij ((ZMod.natCast_eq_natCast_iff' _ _ p).1 (sub_eq_zero.1 h)).symm
  have hmem1 := (D.good_cross (rnode_lt hlt i) (cnode_lt hlt j) hd).mem
  have hmem2 := D.square_mem hNp (rnode_lt hlt i) (cnode_lt hlt j)
  have hne : ¬ (i = j ∧ i.isLeft = true) := by
    rintro ⟨hij', hl⟩
    apply hij
    rw [hij'] at hl ⊢
    rcases j with j | j
    · rfl
    · simp at hl
  unfold gE hE
  rw [if_neg hne, add_zero, if_pos hij, ← C_mul]
  congr 1
  apply Subtype.ext
  rw [lq_coe hmem2, Subring.coe_mul, lq_coe hmem1, Subring.coe_natCast]
  ring

theorem phiP_hE (D : PoleData Fr p (r + 2 * m)) (hlt : ∀ i, common i < r) (i j : ι ⊕ Fin m) :
    phiP p (hE Fr p r m common i j) = rc p (gam D (rnode r m common i) (cnode r m common j)) := by
  unfold hE gam
  by_cases h : rnode r m common i % p ≠ cnode r m common j % p
  · have hd : ((cnode r m common j : ZMod p) - rnode r m common i) ≠ 0 := by
      intro e
      exact h ((ZMod.natCast_eq_natCast_iff' _ _ p).1 (sub_eq_zero.1 e)).symm
    have g := D.good_cross (rnode_lt hlt i) (cnode_lt hlt j) hd
    rw [if_pos h, if_pos h, phiP_C, redQ_lq g.mem, g.eq]
    rfl
  · rw [if_neg h, if_neg h, phiP_C, redQ_lq (LocRing p).zero_mem]
    have : red p (0 : ℚ) = 0 := by simp [red]
    rw [this]
    rfl

/-- Sums over the indices of a node family supported on covered nodes. -/
theorem sum_node {α R : Type*} [Fintype α] [AddCommMonoid R] (g : α → ℕ) (hg : Function.Injective g)
    (E : Finset ℕ) (hE : ∀ t ∈ E, ∃ x, g x = t) (f : ℕ → R) (hf : ∀ t, t ∉ E → f t = 0) :
    ∑ x, f (g x) = ∑ t ∈ E, f t := by
  classical
  rw [← Finset.sum_image (fun x _ y _ h => hg h)]
  symm
  apply Finset.sum_subset
  · intro t ht
    obtain ⟨x, rfl⟩ := hE t ht
    exact Finset.mem_image_of_mem g (Finset.mem_univ x)
  · intro t _ ht
    exact hf t ht

/-- **Counting the complete classes**: a common node missing from the member spoils at most one
window class. -/
theorem card_good (hinj : Function.Injective common) (hlt : ∀ i, common i < r) (a b : ℕ)
    (hp : b ≤ a + p) :
    b - a ≤ ((Ico a b).filter (fun w => ClsFull common p r w)).card + (r - Fintype.card ι) := by
  have hsplit := Finset.card_filter_add_card_filter_not (s := Ico a b)
    (fun w => ClsFull common p r w)
  rw [Nat.card_Ico] at hsplit
  have hbad : ((Ico a b).filter (fun w => ¬ ClsFull common p r w)).card ≤ r - Fintype.card ι := by
    have hex : ∀ w ∈ (Ico a b).filter (fun w => ¬ ClsFull common p r w),
        ∃ t, t < r ∧ t % p = w % p ∧ ¬ ∃ i, common i = t := by
      intro w hw
      have h := (mem_filter.1 hw).2
      unfold ClsFull at h
      push_neg at h
      obtain ⟨t, ht1, ht2, ht3⟩ := h
      exact ⟨t, ht1, ht2, by push_neg; exact ht3⟩
    choose! f hf using hex
    have hMis : ((range r).filter (fun t => ¬ ∃ i, common i = t)).card = r - Fintype.card ι := by
      have h1 := Finset.card_filter_add_card_filter_not (s := range r)
        (fun t => ∃ i, common i = t)
      have h2 : (range r).filter (fun t => ∃ i, common i = t) = univ.image common := by
        ext t
        simp only [mem_filter, mem_range, mem_image, mem_univ, true_and]
        constructor
        · rintro ⟨_, i, hi⟩; exact ⟨i, hi⟩
        · rintro ⟨i, hi⟩; exact ⟨hi ▸ hlt i, i, hi⟩
      rw [h2, Finset.card_image_of_injective _ hinj, card_range, Finset.card_univ] at h1
      omega
    rw [← hMis]
    refine Finset.card_le_card_of_injOn f ?_ ?_
    · intro w hw
      obtain ⟨h1, _, h3⟩ := hf w (Finset.mem_coe.1 hw)
      exact Finset.mem_coe.2 (mem_filter.2 ⟨mem_range.2 h1, h3⟩)
    · intro w1 hw1 w2 hw2 he
      have m1 := (hf w1 (Finset.mem_coe.1 hw1)).2.1
      have m2 := (hf w2 (Finset.mem_coe.1 hw2)).2.1
      have a1 := mem_Ico.1 (mem_filter.1 (Finset.mem_coe.1 hw1)).1
      have a2 := mem_Ico.1 (mem_filter.1 (Finset.mem_coe.1 hw2)).1
      rw [he] at m1
      exact eq_of_mod_eq_window (m1.symm.trans m2) a1.1 a2.1 (by omega) (by omega)
  omega

end Member

/-! ### Theorem 1 -/

section Main

variable {Fr : Frame} {p : ℕ} [Fact p.Prime] {r m n M a b : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **Steps 1-5**: `p^k ∣ det (p² Full(X))` with one factor per complete window class. -/
theorem prefix_dvd (W : Win p r m n M a b) (D : PoleData Fr p (r + 2 * m)) (hNp : r + 2 * m < p * p)
    (common : ι → ℕ) (hinj : Function.Injective common) (hlt : ∀ i, common i < r)
    (hcut : ∀ t : ℕ, a < t → t < b → ¬ p ∣ t ∧ ¬ D.singular (t : ℤ)) :
    ∃ k, b - a ≤ k + (r - Fintype.card ι) ∧
      C ((p : ℕ) : LocRing p) ^ k ∣ (Matrix.of (gE Fr p r m common)).det := by
  have W1 := W.hbp; have W3 := W.hra
  have hcount := card_good hinj hlt (p := p) a b (by omega)
  by_cases hG : ((Ico a b).filter (fun w => ClsFull common p r w)).Nonempty
  swap
  · refine ⟨0, ?_, by simp⟩
    rw [Finset.not_nonempty_iff_eq_empty] at hG
    rw [hG, Finset.card_empty] at hcount
    omega
  obtain ⟨G, hGdef⟩ : ∃ G, G = (Ico a b).filter (fun w => ClsFull common p r w) := ⟨_, rfl⟩
  rw [← hGdef] at hG hcount
  have hGm : ∀ w ∈ G, a ≤ w ∧ w < b ∧ ClsFull common p r w := by
    intro w hw
    rw [hGdef, mem_filter, mem_Ico] at hw
    exact ⟨hw.1.1, hw.1.2, hw.2⟩
  obtain ⟨w0, hw0G, hmin⟩ : ∃ w0 ∈ G, ∀ w ∈ G, w0 ≤ w :=
    ⟨G.min' hG, G.min'_mem hG, fun w hw => G.min'_le w hw⟩
  have hw0a := (hGm w0 hw0G).1
  have hw0b := (hGm w0 hw0G).2.1
  have hfree0 : ∀ w ∈ G, ∀ x, w0 < x → x ≤ w → ¬ p ∣ x := fun w hw x h1 h2 =>
    (hcut x (by omega) (by have := (hGm w hw).2.1; omega)).1
  have hfree : ∀ w ∈ G, ∀ i, 1 ≤ i → i ≤ w - w0 → ¬ D.singular ((w0 + i : ℕ) : ℤ) :=
    fun w hw i h1 h2 => (hcut (w0 + i) (by omega) (by have := (hGm w hw).2.1; omega)).2
  obtain ⟨lam, hlamE, ⟨s0, hs0E, hs0⟩, hker⟩ :=
    exists_kernel (cls (r + 2 * m) r p w0 0) (cls (r + 2 * m) r p w0 1) (bt Fr p)
      (card_O_lt W hw0a hw0b)
  have ms0 := mem_cls.1 hs0E
  -- the classes on the larger side of rows (`X`) and of columns (`Y`)
  obtain ⟨GX, hGX⟩ : ∃ GX, GX = G.filter (fun w => (w - r) % 2 = 0) := ⟨_, rfl⟩
  obtain ⟨GY, hGY⟩ : ∃ GY, GY = G.filter (fun w => ¬ (w - r) % 2 = 0) := ⟨_, rfl⟩
  have hGcard : GX.card + GY.card = G.card := by
    rw [hGX, hGY]; exact Finset.card_filter_add_card_filter_not _
  -- pivots
  obtain ⟨TX, hTX⟩ : ∃ TX : Finset (ι ⊕ Fin m),
      TX = univ.filter (fun i => ∃ w ∈ GX, rnode r m common i = s0 + (w - w0)) := ⟨_, rfl⟩
  obtain ⟨TY, hTY⟩ : ∃ TY : Finset (ι ⊕ Fin m),
      TY = univ.filter (fun j => ∃ w ∈ GY, cnode r m common j = s0 + (w - w0)) := ⟨_, rfl⟩
  have memTX : ∀ i, i ∈ TX ↔ ∃ w ∈ GX, rnode r m common i = s0 + (w - w0) := by
    intro i; rw [hTX, mem_filter]; simp
  have memTY : ∀ j, j ∈ TY ↔ ∃ w ∈ GY, cnode r m common j = s0 + (w - w0) := by
    intro j; rw [hTY, mem_filter]; simp
  have memGX : ∀ w, w ∈ GX ↔ w ∈ G ∧ (w - r) % 2 = 0 := by
    intro w; rw [hGX, mem_filter]
  have memGY : ∀ w, w ∈ GY ↔ w ∈ G ∧ (w - r) % 2 = 1 := by
    intro w; rw [hGY, mem_filter]
    constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by omega⟩
  have hcardX : GX.card ≤ TX.card := by
    refine Finset.card_le_card_of_surjOn (fun i => w0 + (rnode r m common i - s0)) ?_
    intro w hw
    obtain ⟨hwG, hwpar⟩ := (memGX w).1 (Finset.mem_coe.1 hw)
    have hm := hGm w hwG
    obtain ⟨k, hk⟩ := row_cov (m := m) hm.2.2 hwpar (cls_shift W hw0a (hmin w hwG) hm.2.1 hs0E)
    refine ⟨k, Finset.mem_coe.2 ((memTX k).2 ⟨w, Finset.mem_coe.1 hw, hk⟩), ?_⟩
    have := hmin w hwG
    simp only [hk]
    omega
  have hcardY : GY.card ≤ TY.card := by
    refine Finset.card_le_card_of_surjOn (fun j => w0 + (cnode r m common j - s0)) ?_
    intro w hw
    obtain ⟨hwG, hwpar⟩ := (memGY w).1 (Finset.mem_coe.1 hw)
    have hm := hGm w hwG
    obtain ⟨k, hk⟩ := col_cov (m := m) hm.2.2 hwpar (cls_shift W hw0a (hmin w hwG) hm.2.1 hs0E)
    refine ⟨k, Finset.mem_coe.2 ((memTY k).2 ⟨w, Finset.mem_coe.1 hw, hk⟩), ?_⟩
    have := hmin w hwG
    simp only [hk]
    omega
  refine ⟨TX.card + TY.card, by omega, ?_⟩
  have hprime : Prime (C ((p : ℕ) : LocRing p) : (LocRing p)[X]) :=
    Polynomial.prime_C_iff.2 (prime_p p)
  have hb := W.hbp
  -- the pivot of the class of `w` is the node `s0 + (w - w0)`; it determines the class
  have piv : ∀ w1 ∈ G, ∀ w2 ∈ G, ∀ t : ℕ, vec lam (w1 - w0) t ≠ 0 → t = s0 + (w2 - w0) →
      w1 = w2 := by
    intro w1 hw1 w2 hw2 t hv ht
    have hm1 := vec_mem W hw0a (hmin w1 hw1) (hGm w1 hw1).2.1 hlamE hv
    have hm2 := cls_shift W hw0a (hmin w2 hw2) (hGm w2 hw2).2.1 hs0E
    rw [← ht] at hm2
    have e := (mem_cls.1 hm1).2.1.symm.trans (mem_cls.1 hm2).2.1
    have := hmin w1 hw1; have := hmin w2 hw2
    have := (hGm w1 hw1).2.1; have := (hGm w2 hw2).2.1
    exact eq_of_mod_eq_window e (hGm w1 hw1).1 (hGm w2 hw2).1 (by omega) (by omega)
  have vecd : ∀ w ∈ G, vec lam (w - w0) (s0 + (w - w0)) = lam s0 := by
    intro w _
    unfold vec
    rw [if_pos (Nat.le_add_left _ _), Nat.add_sub_cancel]
  refine pow_dvd_det_of_pivots (phiP p) hprime (phiP_eq_zero_iff p) _ TX TY
    (fun i k => liftZ (vec lam (rnode r m common i - s0) (rnode r m common k)))
    (fun j l => liftZ (vec lam (cnode r m common j - s0) (cnode r m common l)))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- pivot entries of the row vectors
    intro i hi
    obtain ⟨w, hwX, hrn⟩ := (memTX i).1 hi
    have hwG := ((memGX w).1 hwX).1
    beta_reduce
    rw [phiP_liftZ, hrn, Nat.add_sub_cancel_left, vecd w hwG]
    exact (map_ne_zero (rc p)).2 hs0
  · intro i hi i' hi' hii'
    obtain ⟨w, hwX, hrn⟩ := (memTX i).1 hi
    obtain ⟨w', hwX', hrn'⟩ := (memTX i').1 hi'
    have hwG := ((memGX w).1 hwX).1
    have hwG' := ((memGX w').1 hwX').1
    beta_reduce
    rw [phiP_liftZ, hrn, Nat.add_sub_cancel_left]
    by_contra hv
    have hv' : vec lam (w - w0) (rnode r m common i') ≠ 0 := fun h => hv (by rw [h, map_zero])
    have := piv w hwG w' hwG' _ hv' hrn'
    subst this
    exact hii' (rnode_inj hinj hlt (hrn.trans hrn'.symm))
  · intro j hj
    obtain ⟨w, hwY, hcn⟩ := (memTY j).1 hj
    have hwG := ((memGY w).1 hwY).1
    beta_reduce
    rw [phiP_liftZ, hcn, Nat.add_sub_cancel_left, vecd w hwG]
    exact (map_ne_zero (rc p)).2 hs0
  · intro j hj j' hj' hjj'
    obtain ⟨w, hwY, hcn⟩ := (memTY j).1 hj
    obtain ⟨w', hwY', hcn'⟩ := (memTY j').1 hj'
    have hwG := ((memGY w).1 hwY).1
    have hwG' := ((memGY w').1 hwY').1
    beta_reduce
    rw [phiP_liftZ, hcn, Nat.add_sub_cancel_left]
    by_contra hv
    have hv' : vec lam (w - w0) (cnode r m common j') ≠ 0 := fun h => hv (by rw [h, map_zero])
    have := piv w hwG w' hwG' _ hv' hcn'
    subst this
    exact hjj' (cnode_inj hinj hlt (hcn.trans hcn'.symm))
  · -- rows: left kernel vectors on the `X`-classes
    intro i hi l
    obtain ⟨w, hwX, hrn⟩ := (memTX i).1 hi
    obtain ⟨hwG, hwpar⟩ := (memGX w).1 hwX
    have hm := hGm w hwG
    beta_reduce
    rw [← phiP_eq_zero_iff, map_sum]
    have e1 : ∀ k, phiP p (liftZ (vec lam (rnode r m common i - s0) (rnode r m common k)) *
        Matrix.of (gE Fr p r m common) k l) =
        rc p (vec lam (w - w0) (rnode r m common k) * bt Fr p (rnode r m common k) (cnode r m common l)) := by
      intro k
      rw [Matrix.of_apply]
      simp only [map_mul, phiP_liftZ, phiP_gE D hNp hlt, hrn, Nat.add_sub_cancel_left]
    rw [Finset.sum_congr rfl (fun k _ => e1 k), ← map_sum]
    have hs := sum_node (rnode r m common) (rnode_inj hinj hlt) (cls (r + 2 * m) r p w 0)
      (fun t ht => row_cov hm.2.2 hwpar ht)
      (fun t => vec lam (w - w0) t * bt Fr p t (cnode r m common l))
      (fun t ht => by
        by_cases hv : vec lam (w - w0) t = 0
        · simp only [hv, zero_mul]
        · exact absurd (vec_mem W hw0a (hmin w hwG) hm.2.1 hlamE hv) ht)
    beta_reduce at hs
    rw [hs, row_kernel W D hNp hw0a (hmin w hwG) hm.2.1 (hfree0 w hwG) (hfree w hwG) lam hker
      (cnode_lt hlt l) (col_in hlt hwpar l), map_zero]
  · -- columns: right kernel vectors on the `Y`-classes
    intro j hj k
    obtain ⟨w, hwY, hcn⟩ := (memTY j).1 hj
    obtain ⟨hwG, hwpar⟩ := (memGY w).1 hwY
    have hm := hGm w hwG
    beta_reduce
    rw [← phiP_eq_zero_iff, map_sum]
    have e1 : ∀ l, phiP p (Matrix.of (gE Fr p r m common) k l *
        liftZ (vec lam (cnode r m common j - s0) (cnode r m common l))) =
        rc p (vec lam (w - w0) (cnode r m common l) * bt Fr p (cnode r m common l) (rnode r m common k)) := by
      intro l
      rw [Matrix.of_apply]
      simp only [map_mul, phiP_liftZ, phiP_gE D hNp hlt, hcn, Nat.add_sub_cancel_left]
      rw [bt_comm]
      ring
    rw [Finset.sum_congr rfl (fun l _ => e1 l), ← map_sum]
    have hs := sum_node (cnode r m common) (cnode_inj hinj hlt) (cls (r + 2 * m) r p w 0)
      (fun t ht => col_cov hm.2.2 hwpar ht)
      (fun t => vec lam (w - w0) t * bt Fr p t (rnode r m common k))
      (fun t ht => by
        by_cases hv : vec lam (w - w0) t = 0
        · simp only [hv, zero_mul]
        · exact absurd (vec_mem W hw0a (hmin w hwG) hm.2.1 hlamE hv) ht)
    beta_reduce at hs
    rw [hs, row_kernel W D hNp hw0a (hmin w hwG) hm.2.1 (hfree0 w hwG) (hfree w hwG) lam hker
      (rnode_lt hlt k) (row_in hlt hwpar k), map_zero]
  · -- pairings
    intro i hi j hj
    obtain ⟨w1, hw1X, hrn⟩ := (memTX i).1 hi
    obtain ⟨hw1G, hw1par⟩ := (memGX w1).1 hw1X
    obtain ⟨w2, hw2Y, hcn⟩ := (memTY j).1 hj
    obtain ⟨hw2G, hw2par⟩ := (memGY w2).1 hw2Y
    have hm1 := hGm w1 hw1G
    have hm2 := hGm w2 hw2G
    have hw1b := hm1.2.1
    have hw2b := hm2.2.1
    have hw1a := hm1.1
    have hw2a := hm2.1
    have hne : w1 ≠ w2 := by intro h; subst h; omega
    have hδ1 : rnode r m common i - s0 = w1 - w0 := by rw [hrn]; omega
    have hδ2 : cnode r m common j - s0 = w2 - w0 := by rw [hcn]; omega
    beta_reduce
    rw [hδ1, hδ2]
    -- factor `p` out of every term
    have hterm : ∀ k l, liftZ (vec lam (w1 - w0) (rnode r m common k)) * Matrix.of (gE Fr p r m common) k l *
        liftZ (vec lam (w2 - w0) (cnode r m common l)) =
        C ((p : ℕ) : LocRing p) * (liftZ (vec lam (w1 - w0) (rnode r m common k)) *
          hE Fr p r m common k l * liftZ (vec lam (w2 - w0) (cnode r m common l))) := by
      intro k l
      rw [Matrix.of_apply]
      by_cases hkl : rnode r m common k % p ≠ cnode r m common l % p
      · rw [gE_off D hNp hlt hkl]; ring
      · have hz : vec lam (w1 - w0) (rnode r m common k) = 0 ∨
            vec lam (w2 - w0) (cnode r m common l) = 0 := by
          by_contra hc
          push_neg at hc
          have e1 := (mem_cls.1 (vec_mem W hw0a (hmin w1 hw1G) hm1.2.1 hlamE hc.1)).2.1
          have e2 := (mem_cls.1 (vec_mem W hw0a (hmin w2 hw2G) hm2.2.1 hlamE hc.2)).2.1
          push_neg at hkl
          have := hmin w1 hw1G; have := hmin w2 hw2G
          exact hne (eq_of_mod_eq_window (e1.symm.trans (hkl.trans e2)) hm1.1 hm2.1
            (by omega) (by omega))
        rcases hz with hz | hz
        · rw [hz, liftZ_zero]; ring
        · rw [hz, liftZ_zero]; ring
    simp only [hterm, ← Finset.mul_sum]
    rw [pow_two]
    refine mul_dvd_mul_left _ ?_
    rw [← phiP_eq_zero_iff, map_sum]
    have e2 : ∀ k, phiP p (∑ l, liftZ (vec lam (w1 - w0) (rnode r m common k)) * hE Fr p r m common k l *
        liftZ (vec lam (w2 - w0) (cnode r m common l))) =
        rc p (vec lam (w1 - w0) (rnode r m common k) * (∑ t' ∈ cls (r + 2 * m) r p w2 0,
          vec lam (w2 - w0) t' * gam D (rnode r m common k) t')) := by
      intro k
      have hs := sum_node (cnode r m common) (cnode_inj hinj hlt) (cls (r + 2 * m) r p w2 0)
        (fun t ht => col_cov hm2.2.2 hw2par ht)
        (fun t' => vec lam (w2 - w0) t' * gam D (rnode r m common k) t')
        (fun t ht => by
          by_cases hv : vec lam (w2 - w0) t = 0
          · simp only [hv, zero_mul]
          · exact absurd (vec_mem W hw0a (hmin w2 hw2G) hm2.2.1 hlamE hv) ht)
      beta_reduce at hs
      rw [← hs, Finset.mul_sum, map_sum, map_sum]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      simp only [map_mul, phiP_liftZ, phiP_hE D hlt]
      ring
    rw [Finset.sum_congr rfl (fun k _ => e2 k), ← map_sum]
    have hs := sum_node (rnode r m common) (rnode_inj hinj hlt) (cls (r + 2 * m) r p w1 0)
      (fun t ht => row_cov hm1.2.2 hw1par ht)
      (fun t => vec lam (w1 - w0) t * (∑ t' ∈ cls (r + 2 * m) r p w2 0,
          vec lam (w2 - w0) t' * gam D t t'))
      (fun t ht => by
        by_cases hv : vec lam (w1 - w0) t = 0
        · simp only [hv, zero_mul]
        · exact absurd (vec_mem W hw0a (hmin w1 hw1G) hm1.2.1 hlamE hv) ht)
    beta_reduce at hs
    rw [hs, pair_zero W D hw0a (hmin w1 hw1G) hm1.2.1 (hmin w2 hw2G) hm2.2.1 hne (hfree0 w1 hw1G)
      (hfree0 w2 hw2G) (hfree w1 hw1G) (hfree w2 hw2G) lam, map_zero]

/-- **Theorem 1 (prefix rule)** for any frame with periodic pole data and any member core:
`v_p(den P_S) ≤ 2r + 2m - (b - a)`. -/
theorem prefix_gle (W : Win p r m n M a b) (D : PoleData Fr p (r + 2 * m)) (hNp : r + 2 * m < p * p)
    (common : ι → ℕ) (hinj : Function.Injective common) (hlt : ∀ i, common i < r)
    (hcut : ∀ t : ℕ, a < t → t < b → ¬ p ∣ t ∧ ¬ D.singular (t : ℤ)) :
    GLE p (2 * r + 2 * m - (b - a))
      (FullN Fr common (fun x : Fin m => r + 2 * x.val) (fun y : Fin m => r + 2 * y.val + 1)
        (X : ℚ[X])).det := by
  obtain ⟨k, hk, hdvd⟩ := prefix_dvd W D hNp common hinj hlt hcut
  have hg := gle_det_of_scaled_dvd p
    (FullN Fr common (fun x : Fin m => r + 2 * x.val) (fun y : Fin m => r + 2 * y.val + 1) (X : ℚ[X]))
    (Matrix.of (gE Fr p r m common)) (fun _ => 1) (fun _ => 1)
    (fun i j => toQ_gE D hNp hlt i j) k hdvd
  refine hg.mono ?_
  have hcard : Fintype.card ι ≤ r := by
    have := Finset.card_le_card_of_injOn common (s := (univ : Finset ι)) (t := range r)
      (fun i _ => Finset.mem_coe.2 (mem_range.2 (hlt i))) (fun i _ j _ h => hinj h)
    simpa using this
  have h1 := W.hbN; have h2 := W.hra; have h3 := W.hm; have h4 := W.hab
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_sum, Fintype.card_fin, smul_eq_mul, mul_one]
  omega

/-- A trivial instance of the window hypotheses (an empty window), giving the price `2r + 2m`. -/
theorem win_triv (p r m : ℕ) (hp : 0 < p) (hp2 : p % 2 = 1) :
    Win p r m (m / p) (m % p) (r + m % p) (r + m % p) := by
  have h1 := Nat.div_add_mod' m p
  have h2 := Nat.mod_lt m hp
  exact ⟨h1.symm, hp2, by omega, le_rfl, by omega, by omega, by omega⟩

end Main

/-! ### The layer and the two-term branch -/

/-- Validity of the prefix window at the strip `n`: hybrid shape, pole data, and the window
hypotheses of Theorem 1 for `[a r p, b r p)`. -/
def preValid (G : BlockGeom) (Fr : Frame) (n : ℕ) (a b : ℕ → ℕ → ℕ) (r p : ℕ) : Prop :=
  HybShape G r ∧ ∀ [Fact p.Prime], ∃ D : PoleData Fr p (r + 2 * (G.geometry r).k),
    r + 2 * (G.geometry r).k < p * p ∧
    Win p r (G.geometry r).k n ((G.geometry r).k - n * p) (a r p) (b r p) ∧
    ∀ t : ℕ, a r p < t → t < b r p → ¬ p ∣ t ∧ ¬ D.singular (t : ℤ)

/-- **The prefix layer (debit 0)**: price `2r + 2m - (b - a)`. -/
noncomputable def preLayer (G : BlockGeom) (Fr : Frame) (depth n : ℕ) (a b : ℕ → ℕ → ℕ) :
    DebitLayer G Fr depth where
  base := fun r p => 2 * r + 2 * (G.geometry r).k - (b r p - a r p)
  debit := 0
  valid := preValid G Fr n a b
  gle := by
    intro i _ p hp hv
    rcases i with ⟨r, S⟩
    obtain ⟨hs, hv⟩ := hv
    obtain ⟨D, hN, hW, hcut⟩ := hv
    have hCmem : ∀ x : (G.geometry r).C, x.1 < r := by
      intro x
      have h : x.1 ∈ Finset.range r := by
        rw [← hs.C_eq]; exact x.2
      exact Finset.mem_range.mp h
    have hxs : (G.geometry r).xs = fun i : Fin (G.geometry r).k => r + 2 * i.val := funext hs.xs_eq
    have hys : (G.geometry r).ys = fun i : Fin (G.geometry r).k => r + 2 * i.val + 1 :=
      funext hs.ys_eq
    change GLE p (2 * r + 2 * (G.geometry r).k - (b r p - a r p) + 0 * delCount G ⟨r, S⟩)
      (Rect.FullN Fr (fun x : S => ((x.1 : (G.geometry r).C) : ℕ)) (G.geometry r).xs
        (G.geometry r).ys (X : ℚ[X])).det
    rw [hxs, hys, zero_mul, add_zero]
    exact prefix_gle hW D hN (fun x : S => ((x.1 : (G.geometry r).C) : ℕ))
      (fun x y h => Subtype.ext (Subtype.ext h)) (fun x => hCmem x.1) hcut

variable {Fr : Frame} {q o : ℕ}

/-- **The prefix branch for a two-term frame** (`altGeom c`, even `r`): at a prime `p ∤ nm`,
`p ≥ 5`, `q N < p²`, every window `[a, b)` satisfying the hypotheses of Theorem 1 at the strip
`n` with no cut point of `t ≡ 0`, `p ∣ q t - o`, `t ≡ r (mod p)` in `(a, b)` gives the price
`2r + 2m - (b - a)` (debit 0). -/
theorem pre_gap_tt (c : ℚ) (hc : 0 < c) (T : TwoTermData Fr q o) {nm : ℕ}
    (hnorm : Fr.norm = (nm : ℚ)) (depth : ℕ) (i : ((altGeom c hc).family Fr depth).ι)
    (hi : ((altGeom c hc).family Fr depth).Adm i) (hr : i.1 % 2 = 0) (p : ℕ) [Fact p.Prime]
    (hpn : ¬ p ∣ nm) (hN : q * (i.1 + 2 * (altGeom c hc).borderSize i.1) < p * p) (n a b : ℕ)
    (hW : Win p i.1 ((altGeom c hc).borderSize i.1) n ((altGeom c hc).borderSize i.1 - n * p) a b)
    (hgap : ∀ t : ℤ, (a : ℤ) < t → t < b → ¬ Cut p i.1 (ttSing p q o) t) :
    GLE p (2 * i.1 + 2 * (altGeom c hc).borderSize i.1 - (b - a))
      (((altGeom c hc).family Fr depth).Q i) := by
  have hk : ((altGeom c hc).geometry i.1).k = (altGeom c hc).borderSize i.1 :=
    geometry_k_eq_borderSize _ i.1
  have hq : 0 < q := by have := T.o_lt; have := T.o_pos; omega
  have hN' : i.1 + 2 * (altGeom c hc).borderSize i.1 < p * p :=
    lt_of_le_of_lt (Nat.le_mul_of_pos_left _ hq) hN
  have hv : preValid (altGeom c hc) Fr n (fun _ _ => a) (fun _ _ => b) i.1 p := by
    refine ⟨altGeom_hybShape c hc hr, fun [hpf : Fact p.Prime] => ?_⟩
    rw [hk]
    refine ⟨ttPoleData T hnorm p _ hpn hN, hN', hW, fun t h1 h2 => ⟨?_, ?_⟩⟩
    · rintro ⟨d, hd⟩
      refine hgap (t : ℤ) (by exact_mod_cast h1) (by exact_mod_cast h2) (Or.inr (Or.inl ⟨(d : ℤ), ?_⟩))
      rw [hd]; push_cast; ring
    · intro hs
      exact hgap (t : ℤ) (by exact_mod_cast h1) (by exact_mod_cast h2) (Or.inl hs)
  have hg := (preLayer (altGeom c hc) Fr depth n (fun _ _ => a) (fun _ _ => b)).gle i hi p hv
  simp only [preLayer, zero_mul, add_zero, hk] at hg
  exact hg

end CatalanCore.Uniform.Content.BankShared.TwoTerm.Pre

#print axioms CatalanCore.Uniform.Content.BankShared.TwoTerm.Pre.prefix_dvd
#print axioms CatalanCore.Uniform.Content.BankShared.TwoTerm.Pre.prefix_gle
#print axioms CatalanCore.Uniform.Content.BankShared.TwoTerm.Pre.pre_gap_tt
