module

public import CatalanCore.Lai.ContentL1
public import CatalanCore.Lai.ContentBasisT
public import CatalanCore.Lai.ContentLemmaR
public import CatalanCore.Lai.ContentL2Jet
public import CatalanCore.Lai.ContentL2Sum

@[expose] public section

/-!
# `CatalanCore.Lai.ContentL2Main`: Theorem L2 (LC21), by node jets

Paper: `L2-SIMPLE-2026-11-16.md` (Lemma X, the proof of Theorem L2) and `N9-LAI-CONTENT-EXACT`.
For every prime `√(8n) < p < 3n`, `v_p(J_n) ≥ LaiExact(n, p) + x₁ + x₂` (`lai_L2`).

Rows `L2S-19 … 25`:
* `fam_jets` (19): jet valuations of the elements of the family `elF` (`e_{r,i}`, `g_j`);
* `pair_classify` (20): the deficit table of Lemma X (`defF`);
* `pair_Gdata_W1`, `pair_Gdata_W2` (21): the polynomials `V, G, H` of the window pairs;
* `entry_bound` (22): every Gram entry of the family has content `≥ ⌈(2π_x + 2π_y)/2⌉`;
* `det_bound` (23): `GV.det_halfInt` with `κ = 0`;
* `pot_sum` (24): `2 Σ π = Σ pot2 + x₁ + x₂`;
* `lai_L2` (25): the assembly through `GV_laiJ_of_window`.
Imports `Lai.ContentL2Jet` (rows 01–13) and `Lai.ContentL2Sum` (rows 12, 14–18).
-/

open Finset CatalanCore.Basic CatalanCore.Arith.Hybrid CatalanCore.Content MvPolynomial
open scoped Nat

namespace CatalanCore.Lai

section FamilyData

variable {n p : ℕ}

/-- The multiplicity `μ′_r` of the local factor `q_r` of the L2 family: `μ_r` on the window
(`σ_r = σ_W`) and `μ_r + 1` off it. -/
noncomputable def mF (n p σW r : ℕ) : ℕ := mu n p r + (if sig n p r = σW then 0 else 1)

/-- Index type of the L2 family: `e_{r,i}` (`i < μ′_r`) and `g_j` (`j < x₂`). -/
abbrev FIdx (n p σW : ℕ) : Type := (Σ r : Fin p, Fin (mF n p σW r)) ⊕ Fin (xtwo n p).toNat

/-- Twice the potential: `2π(e_{r,i}) = 2i - 4 + σ_r`, `2π(g_j) = λ + 2`. -/
noncomputable def pot2F (n p σW : ℕ) : FIdx n p σW → ℤ
  | Sum.inl ⟨r, i⟩ => 2 * (i : ℤ) - 4 + (sig n p r : ℤ)
  | Sum.inr _ => lam n p + 2

/-- The order of vanishing of the element `x` at the residue `s` (own: `i`, else `μ′_s`). -/
noncomputable def nuF (n p σW : ℕ) : FIdx n p σW → ℕ → ℕ
  | Sum.inl ⟨r, i⟩, s => if (r : ℕ) = s then (i : ℕ) else mF n p σW s
  | Sum.inr _, s => mF n p σW s

/-- The deficit of the pair `(x, y)` at the residue `s`: the required content
`⌈(2π_x + 2π_y)/2⌉` minus the node bound `σ_s - 4 + ν_s(x) + ν_s(y)`. -/
noncomputable def defF (n p σW : ℕ) (x y : FIdx n p σW) (s : ℕ) : ℤ :=
  (pot2F n p σW x + pot2F n p σW y + 1) / 2 -
    ((sig n p s : ℤ) - 4 + (nuF n p σW x s : ℤ) + (nuF n p σW y s : ℤ))

/-! ### L2S-24: the potential sum -/

open Classical in
/-- **L2S-24 `pot_sum`.** `2Σπ = Σ pot2 + x₁ + x₂` (Lemma T, `d = |Z| + |N| + x₂`). -/
theorem pot_sum (h : Rng n p) (σW : ℕ) (hpar : (lam n p - (σW : ℤ)) % 2 = 0)
    (hcard : ((range p).filter (fun s => sig n p s = σW)).card = tieW n p)
    (hx2 : 0 < xtwo n p) :
    ∑ x : FIdx n p σW, pot2F n p σW x = ∑ y : LIdx n p, pot2 n p y + xone n p + xtwo n p := by
  obtain ⟨hlam, h2d, hx1, h2x⟩ := law_second_level h hx2
  have hsum := tie_sum h
  have hS := lemmaS h
  have hxt : xtwo n p = xone n p - Ncnt n p := by
    unfold xtwo at *; omega
  -- split both sums
  have eF : ∑ x : FIdx n p σW, pot2F n p σW x =
      ∑ r ∈ range p, ∑ i ∈ range (mF n p σW r), (2 * (i : ℤ) - 4 + (sig n p r : ℤ)) +
        ((xtwo n p).toNat : ℤ) * (lam n p + 2) := by
    rw [Fintype.sum_sum_type, Fintype.sum_sigma]
    congr 1
    · rw [← Fin.sum_univ_eq_sum_range (fun r => ∑ i ∈ range (mF n p σW r), (2 * (i : ℤ) - 4 + (sig n p r : ℤ))) p]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [← Fin.sum_univ_eq_sum_range (fun i => (2 * (i : ℤ) - 4 + (sig n p r : ℤ))) (mF n p σW r)]
      rfl
    · simp [pot2F]
  have eL : ∑ y : LIdx n p, pot2 n p y =
      ∑ r ∈ range p, ∑ i ∈ range (mu n p r), (2 * (i : ℤ) - 4 + (sig n p r : ℤ)) +
        (dcnt n p : ℤ) * lam n p := by
    rw [Fintype.sum_sum_type, Fintype.sum_sigma]
    congr 1
    · rw [← Fin.sum_univ_eq_sum_range (fun r => ∑ i ∈ range (mu n p r), (2 * (i : ℤ) - 4 + (sig n p r : ℤ))) p]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [← Fin.sum_univ_eq_sum_range (fun i => (2 * (i : ℤ) - 4 + (sig n p r : ℤ))) (mu n p r)]
      rfl
    · simp [pot2]
  have ex : ∀ r ∈ range p, ∑ i ∈ range (mF n p σW r), (2 * (i : ℤ) - 4 + (sig n p r : ℤ)) =
      ∑ i ∈ range (mu n p r), (2 * (i : ℤ) - 4 + (sig n p r : ℤ)) +
        ((lam n p) * (if sig n p r = σW then 0 else 1) +
          (if (lam n p - (sig n p r : ℤ)) % 2 ≠ 0 then 1 else 0)) := by
    intro r hr
    have hr' := Finset.mem_range.1 hr
    have hm := hS.2.2.1 r hr'
    unfold mF
    by_cases hw : sig n p r = σW
    · rw [if_pos hw]
      have : ¬ ((lam n p - (σW : ℤ)) % 2 ≠ 0) := by omega
      simp only [hw, if_true, mul_zero, zero_add, add_zero, this, if_false]
    · rw [if_neg hw, Finset.sum_range_succ]
      have e1 : (if (lam n p - (sig n p r : ℤ)) % 2 = 0 then (0 : ℤ) else 1) =
          (if (lam n p - (sig n p r : ℤ)) % 2 ≠ 0 then 1 else 0) := by
        by_cases hq : (lam n p - (sig n p r : ℤ)) % 2 = 0 <;> simp [hq]
      rw [e1] at hm
      simp only [if_neg hw, mul_one]
      push_cast
      linarith
  rw [eF, eL, Finset.sum_congr rfl ex, Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hN : ∑ r ∈ range p, (if (lam n p - (sig n p r : ℤ)) % 2 ≠ 0 then (1 : ℤ) else 0) = Ncnt n p := by
    unfold Ncnt
    rw [Finset.card_filter]; push_cast; rfl
  have hWc : ∑ r ∈ range p, (lam n p * (if sig n p r = σW then (0 : ℤ) else 1)) =
      lam n p * ((p : ℤ) - tieW n p) := by
    rw [← Finset.mul_sum]
    congr 1
    have : ∑ r ∈ range p, (if sig n p r = σW then (0 : ℤ) else 1) = (p : ℤ) - ((range p).filter (fun s => sig n p s = σW)).card := by
      rw [Finset.sum_ite, Finset.sum_const_zero, Finset.sum_const, zero_add]
      have h1 := Finset.card_filter_add_card_filter_not (s := range p) (fun s => sig n p s = σW)
      simp only [Finset.card_range] at h1
      simp only [nsmul_eq_mul, mul_one]
      omega
    rw [this, hcard]
  rw [hWc, hN]
  have hd : (dcnt n p : ℤ) = xtwo n p + Ncnt n p + tieZ n p := by omega
  have hxt' : (((xtwo n p).toNat : ℕ) : ℤ) = xtwo n p := by omega
  rw [hxt', hd]
  have hp' : (p : ℤ) = tieZ n p + tieW n p + Ncnt n p := by exact_mod_cast hsum.symm
  rw [hp']
  have : xone n p = xtwo n p + Ncnt n p := by omega
  rw [this]
  ring

end FamilyData

/-! ### generic products `∏ (c r - X)^{a r}` (for rows 21) -/

section Pr

variable {R : Type*} [CommRing R]

/-- the linear factor `c r - X`. -/
noncomputable def qq (c : ℕ → R) (r : ℕ) : Polynomial R := Polynomial.C (c r) - Polynomial.X

/-- `∏_{r ∈ N} (c r - X)^{a r}`. -/
noncomputable def Pr (c : ℕ → R) (N : Finset ℕ) (a : ℕ → ℕ) : Polynomial R :=
  ∏ r ∈ N, qq c r ^ a r

/-- `Pr` with the exponent at `r` lowered by one. -/
noncomputable def Pl (c : ℕ → R) (N : Finset ℕ) (a : ℕ → ℕ) (r : ℕ) : Polynomial R :=
  qq c r ^ (a r - 1) * ∏ r' ∈ N.erase r, qq c r' ^ a r'

/-- `Σ_r b_r · Pl a r`. -/
noncomputable def Ht (c : ℕ → R) (N : Finset ℕ) (a b : ℕ → ℕ) : Polynomial R :=
  ∑ r ∈ N, Polynomial.C (b r : R) * Pl c N a r

lemma Pr_congr (c : ℕ → R) (N : Finset ℕ) {a b : ℕ → ℕ} (h : ∀ r ∈ N, a r = b r) :
    Pr c N a = Pr c N b := by
  unfold Pr
  exact Finset.prod_congr rfl fun r hr => by rw [h r hr]

lemma Pl_congr (c : ℕ → R) (N : Finset ℕ) {a b : ℕ → ℕ} (h : ∀ r ∈ N, a r = b r) (r : ℕ) (hr : r ∈ N) :
    Pl c N a r = Pl c N b r := by
  unfold Pl
  rw [h r hr]
  congr 1
  exact Finset.prod_congr rfl fun r' hr' => by rw [h r' (Finset.mem_of_mem_erase hr')]

lemma Pr_mul (c : ℕ → R) (N : Finset ℕ) (a b : ℕ → ℕ) :
    Pr c N a * Pr c N b = Pr c N (fun r => a r + b r) := by
  unfold Pr
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun r _ => by rw [pow_add]

lemma Pr_eq_Pl (c : ℕ → R) (N : Finset ℕ) (a : ℕ → ℕ) {r : ℕ} (hr : r ∈ N) (ha : 1 ≤ a r) :
    Pr c N a = qq c r * Pl c N a r := by
  unfold Pr Pl
  rw [← Finset.mul_prod_erase N _ hr, ← mul_assoc, ← pow_succ']
  have : a r - 1 + 1 = a r := by omega
  rw [this]

lemma Pl_mul (c : ℕ → R) (N : Finset ℕ) (a b : ℕ → ℕ) {r : ℕ} (hr : r ∈ N) (ha : 1 ≤ a r) :
    Pr c N b * Pl c N a r = Pl c N (fun r => a r + b r) r := by
  unfold Pr Pl
  rw [← Finset.mul_prod_erase N _ hr]
  have e : ∏ r' ∈ N.erase r, qq c r' ^ (a r' + b r') =
      (∏ r' ∈ N.erase r, qq c r' ^ a r') * ∏ r' ∈ N.erase r, qq c r' ^ b r' := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun r' _ => by rw [pow_add]
  rw [e]
  have e2 : qq c r ^ (a r + b r - 1) = qq c r ^ (a r - 1) * qq c r ^ b r := by
    rw [← pow_add]; congr 1; omega
  rw [e2]
  ring

lemma derivative_Pr (c : ℕ → R) (N : Finset ℕ) (a : ℕ → ℕ) :
    Polynomial.derivative (Pr c N a) = -(Ht c N a a) := by
  classical
  unfold Pr Ht Pl
  rw [Polynomial.derivative_prod_finset, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  have hd : Polynomial.derivative (qq c r ^ a r) = -(Polynomial.C (a r : R) * qq c r ^ (a r - 1)) := by
    rw [Polynomial.derivative_pow]
    simp [qq] <;> ring
  rw [hd]
  ring

lemma eval_Pr_zero (c : ℕ → R) (N : Finset ℕ) (a : ℕ → ℕ) {m : ℕ} (hm : m ∈ N) (ha : 1 ≤ a m) :
    (Pr c N a).eval (c m) = 0 := by
  unfold Pr
  rw [Polynomial.eval_prod]
  refine Finset.prod_eq_zero hm ?_
  have : a m ≠ 0 := by omega
  simp [qq, this]

lemma eval_Pl_zero (c : ℕ → R) (N : Finset ℕ) (a : ℕ → ℕ) {m : ℕ} (hm : m ∈ N) (ha : 2 ≤ a m)
    (r : ℕ) (hr : r ∈ N) : (Pl c N a r).eval (c m) = 0 := by
  unfold Pl
  rw [Polynomial.eval_mul, Polynomial.eval_prod]
  by_cases hmr : m = r
  · subst hmr
    have : a m - 1 ≠ 0 := by omega
    simp [qq, this]
  · have : m ∈ N.erase r := Finset.mem_erase.2 ⟨hmr, hm⟩
    have h0 : a m ≠ 0 := by omega
    rw [Finset.prod_eq_zero this (by simp [qq, h0]), mul_zero]

lemma eval_derivative_Pr_zero (c : ℕ → R) (N : Finset ℕ) (a : ℕ → ℕ) {m : ℕ} (hm : m ∈ N)
    (ha : 2 ≤ a m) : (Polynomial.derivative (Pr c N a)).eval (c m) = 0 := by
  rw [derivative_Pr]
  simp only [Ht, Polynomial.eval_neg, Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_C]
  rw [Finset.sum_eq_zero fun r hr => by rw [eval_Pl_zero c N a hm ha r hr, mul_zero], neg_zero]

lemma eval_Ht_zero (c : ℕ → R) (N : Finset ℕ) (a b : ℕ → ℕ) {m : ℕ} (hm : m ∈ N) (ha : 2 ≤ a m) :
    (Ht c N a b).eval (c m) = 0 := by
  simp only [Ht, Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_C]
  exact Finset.sum_eq_zero fun r hr => by rw [eval_Pl_zero c N a hm ha r hr, mul_zero]

lemma natDegree_qq_le (c : ℕ → R) (r : ℕ) : (qq c r).natDegree ≤ 1 := by
  unfold qq
  refine (Polynomial.natDegree_sub_le _ _).trans ?_
  rw [Polynomial.natDegree_C]
  exact max_le (by norm_num) Polynomial.natDegree_X_le

lemma natDegree_Pr_le (c : ℕ → R) (N : Finset ℕ) (a : ℕ → ℕ) :
    (Pr c N a).natDegree ≤ ∑ r ∈ N, a r := by
  unfold Pr
  refine (Polynomial.natDegree_prod_le _ _).trans (Finset.sum_le_sum fun r _ => ?_)
  refine Polynomial.natDegree_pow_le.trans ?_
  have := natDegree_qq_le c r
  nlinarith

lemma natDegree_Pl_le (c : ℕ → R) (N : Finset ℕ) (a : ℕ → ℕ) {r : ℕ} (hr : r ∈ N) :
    (Pl c N a r).natDegree ≤ ∑ r' ∈ N, a r' := by
  unfold Pl
  refine (Polynomial.natDegree_mul_le).trans ?_
  have h1 : (qq c r ^ (a r - 1)).natDegree ≤ a r - 1 := by
    refine Polynomial.natDegree_pow_le.trans ?_
    have := natDegree_qq_le c r
    nlinarith
  have h2 : (∏ r' ∈ N.erase r, qq c r' ^ a r').natDegree ≤ ∑ r' ∈ N.erase r, a r' := by
    refine (Polynomial.natDegree_prod_le _ _).trans (Finset.sum_le_sum fun r' _ => ?_)
    refine Polynomial.natDegree_pow_le.trans ?_
    have := natDegree_qq_le c r'
    nlinarith
  have h3 := Finset.add_sum_erase N a hr
  omega

lemma natDegree_Ht_le (c : ℕ → R) (N : Finset ℕ) (a b : ℕ → ℕ) :
    (Ht c N a b).natDegree ≤ ∑ r ∈ N, a r := by
  unfold Ht
  refine (Polynomial.natDegree_sum_le_of_forall_le _ _ fun r hr => ?_)
  refine (Polynomial.natDegree_mul_le).trans ?_
  rw [Polynomial.natDegree_C, zero_add]
  exact natDegree_Pl_le c N a hr


lemma Ht_mul (c : ℕ → R) (N : Finset ℕ) (a a' b b' w : ℕ → ℕ)
    (hsum : ∀ r ∈ N, a r + b r = a' r + b' r)
    (hpos : ∀ r ∈ N, 1 ≤ w r → 1 ≤ a r ∧ 1 ≤ a' r) :
    Ht c N a w * Pr c N b = Pr c N b' * Ht c N a' w := by
  unfold Ht
  rw [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r hr => ?_
  by_cases hw : w r = 0
  · simp [hw]
  · obtain ⟨h1, h2⟩ := hpos r hr (by omega)
    have e1 := Pl_mul c N a b hr h1
    have e2 := Pl_mul c N a' b' hr h2
    have e3 : Pl c N (fun r => a r + b r) r = Pl c N (fun r => a' r + b' r) r :=
      Pl_congr c N (fun r' hr' => hsum r' hr') r hr
    calc Polynomial.C (w r : R) * Pl c N a r * Pr c N b
        = Polynomial.C (w r : R) * (Pr c N b * Pl c N a r) := by ring
      _ = Polynomial.C (w r : R) * (Pr c N b' * Pl c N a' r) := by rw [e1, e2, e3]
      _ = Pr c N b' * (Polynomial.C (w r : R) * Pl c N a' r) := by ring

end Pr

/-! ### L2S-23: the determinant bound -/

section DetBound

variable {σ : Type*} {p : ℕ} [hp : Fact p.Prime]

/-- **L2S-23 `det_bound`.** If `v(M_ij) ≥ ⌈(a_i + a_j)/2⌉` (`a = 2π`), then `v(det M) ≥ Σ a_i`
(`GV.det_halfInt` with `κ = 0`; the rank bound is the trivial one). -/
theorem det_bound {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι (MvPolynomial σ ℚ))
    (a : ι → ℤ) (hM : ∀ i j, GV p ((a i + a j + 1) / 2) (M i j)) :
    GV p (∑ i, a i) M.det := by
  classical
  set k : ι → ℤ := fun i => a i / 2 with hk
  set B : Finset ι := Finset.univ.filter (fun i => a i % 2 = 1) with hB
  have hmem : ∀ i, i ∈ B ↔ a i % 2 = 1 := fun i => by simp [hB]
  have hM' : ∀ i j, GV p (k i + k j + (if i ∈ B ∨ j ∈ B then 1 else 0)) (M i j) := by
    intro i j
    have e : k i + k j + (if i ∈ B ∨ j ∈ B then 1 else 0) = (a i + a j + 1) / 2 := by
      simp only [hk, hmem]
      split_ifs <;> omega
    rw [e]; exact hM i j
  have hex : ∀ i j : B, ∃ g : MvPolynomial σ (LocRing p),
      toQmv p g = C ((p : ℚ) ^ (-(k i + k j + 1))) * M i j := by
    intro i j
    have := hM' i j
    have hc : (if (i : ι) ∈ B ∨ (j : ι) ∈ B then (1 : ℤ) else 0) = 1 := by simp [i.2]
    rw [hc] at this
    exact GV.exists_lift this
  choose ZB hZB using hex
  set Z : Matrix B B (MvPolynomial σ (LocRing p)) := Matrix.of (fun i j => ZB i j) with hZ
  have hrk : (Z.map (redMv p)).rank + 0 ≤ B.card := by
    rw [add_zero, ← Fintype.card_coe B]
    exact Matrix.rank_le_card_width _
  have key := GV.det_halfInt (p := p) M k B hM' Z (fun i j => hZB i j) 0 hrk
  have hs : ∑ i, a i = 2 * ∑ i, k i + B.card + 0 := by
    have : ∀ i, a i = 2 * k i + (if i ∈ B then 1 else 0) := fun i => by
      simp only [hk, hmem]; split_ifs <;> omega
    rw [Finset.sum_congr rfl (fun i _ => this i), Finset.sum_add_distrib, ← Finset.mul_sum]
    simp [Finset.sum_ite_mem]
  rw [hs]; exact key

end DetBound

/-! ### L2S-20: the pair classification (Lemma X) -/

section PairClass

variable {n p : ℕ}

/-- the element `x` is `e_{s,i}` (it is "own" at `s`). -/
def ownAt {σW : ℕ} : FIdx n p σW → ℕ → Prop
  | Sum.inl ⟨r, _⟩, s => (r : ℕ) = s
  | Sum.inr _, _ => False

lemma resfacts (h : Rng n p) (σW : ℕ) (hpar : (lam n p - (σW : ℤ)) % 2 = 0) (t : ℕ) (ht : t < p) :
    (lam n p + 4 ≤ 2 * (mu n p t : ℤ) + sig n p t ∧ 2 * (mu n p t : ℤ) + sig n p t ≤ lam n p + 5) ∧
    (sig n p t = σW → 2 * (mu n p t : ℤ) + sig n p t = lam n p + 4) := by
  have hS := (lemmaS h).2.2.1 t ht
  refine ⟨by split_ifs at hS <;> omega, fun hw => ?_⟩
  have h0 : (lam n p - (sig n p t : ℤ)) % 2 = 0 := by rw [hw]; exact hpar
  rw [if_pos h0] at hS
  omega

lemma pot_le (h : Rng n p) (σW : ℕ) (hpar : (lam n p - (σW : ℤ)) % 2 = 0) (x : FIdx n p σW) :
    pot2F n p σW x ≤ lam n p + 2 ∧
      ∀ (r : Fin p) (i : Fin (mF n p σW r)), x = Sum.inl ⟨r, i⟩ → sig n p r = σW →
        pot2F n p σW x ≤ lam n p - 2 := by
  rcases x with ⟨r, i⟩ | j
  · have fr := resfacts h σW hpar r r.2
    have hi := i.2
    simp only [mF] at hi
    refine ⟨?_, fun r' i' he hw => ?_⟩
    · simp only [pot2F]
      split_ifs at hi <;> omega
    · obtain ⟨e1, e2⟩ := Sigma.mk.inj_iff.1 (Sum.inl.inj he)
      have e1' : r = r' := e1.symm ▸ rfl
      subst e1'
      have e2' : i = i' := (eq_of_heq e2).symm ▸ rfl
      subst e2'
      have := fr.2 hw
      simp only [pot2F]
      split_ifs at hi <;> omega
  · simp [pot2F]

lemma def_local (h : Rng n p) (σW : ℕ) (hpar : (lam n p - (σW : ℤ)) % 2 = 0)
    (x y : FIdx n p σW) (s : ℕ) (hs : s < p) :
    (sig n p s ≠ σW → defF n p σW x y s ≤ 0) ∧
    (sig n p s = σW → ¬ ownAt x s → ¬ ownAt y s →
      defF n p σW x y s = (pot2F n p σW x + pot2F n p σW y + 1) / 2 - lam n p) ∧
    (sig n p s = σW → ownAt x s → ¬ ownAt y s →
      defF n p σW x y s = (pot2F n p σW y - lam n p + 1) / 2) ∧
    (sig n p s = σW → ¬ ownAt x s → ownAt y s →
      defF n p σW x y s = (pot2F n p σW x - lam n p + 1) / 2) ∧
    (sig n p s = σW → ownAt x s → ownAt y s → defF n p σW x y s ≤ 0) := by
  have fs := resfacts h σW hpar s hs
  have hr : ∀ r : Fin p, ((r : ℕ) = s → sig n p r = sig n p s ∧ mu n p r = mu n p s) :=
    fun r e => by subst e; exact ⟨rfl, rfl⟩
  rcases x with ⟨r, i⟩ | j <;> rcases y with ⟨r', i'⟩ | j'
  · have fr := resfacts h σW hpar r r.2
    have fr' := resfacts h σW hpar r' r'.2
    have hi := i.2
    have hi' := i'.2
    have e1 := hr r
    have e2 := hr r'
    simp only [mF] at hi hi'
    refine ⟨fun hw => ?_, fun hw ho1 ho2 => ?_, fun hw ho1 ho2 => ?_, fun hw ho1 ho2 => ?_, fun hw ho1 ho2 => ?_⟩ <;>
      (simp only [defF, pot2F, nuF, ownAt, mF, not_false_eq_true, false_imp_iff, true_imp_iff, imp_true_iff, and_true, true_and, add_zero] at *) <;> by_cases c1 : (r : ℕ) = s <;> by_cases c2 : (r' : ℕ) = s <;> by_cases c3 : sig n p s = σW <;> by_cases c4 : sig n p r = σW <;> by_cases c5 : sig n p r' = σW <;>
      simp only [c1, c2, c3, c4, c5, if_true, if_false, not_true_eq_false, not_false_eq_true, false_imp_iff, true_imp_iff, imp_true_iff, and_true, true_and, add_zero, ne_eq, Nat.add_zero] at * <;> omega
  · have fr := resfacts h σW hpar r r.2
    have hi := i.2
    have e1 := hr r
    simp only [mF] at hi
    refine ⟨fun hw => ?_, fun hw ho1 ho2 => ?_, fun hw ho1 ho2 => ?_, fun hw ho1 ho2 => ?_, fun hw ho1 ho2 => ?_⟩ <;>
      (simp only [defF, pot2F, nuF, ownAt, mF, not_false_eq_true, false_imp_iff, true_imp_iff, imp_true_iff, and_true, true_and, add_zero] at *) <;> by_cases c1 : (r : ℕ) = s <;> by_cases c3 : sig n p s = σW <;> by_cases c4 : sig n p r = σW <;>
      simp only [c1, c3, c4, if_true, if_false, not_true_eq_false, not_false_eq_true, false_imp_iff, true_imp_iff, imp_true_iff, and_true, true_and, add_zero, ne_eq, Nat.add_zero] at * <;> omega
  · have fr' := resfacts h σW hpar r' r'.2
    have hi' := i'.2
    have e2 := hr r'
    simp only [mF] at hi'
    refine ⟨fun hw => ?_, fun hw ho1 ho2 => ?_, fun hw ho1 ho2 => ?_, fun hw ho1 ho2 => ?_, fun hw ho1 ho2 => ?_⟩ <;>
      (simp only [defF, pot2F, nuF, ownAt, mF, not_false_eq_true, false_imp_iff, true_imp_iff, imp_true_iff, and_true, true_and, add_zero] at *) <;> by_cases c2 : (r' : ℕ) = s <;> by_cases c3 : sig n p s = σW <;> by_cases c5 : sig n p r' = σW <;>
      simp only [c2, c3, c5, if_true, if_false, not_true_eq_false, not_false_eq_true, false_imp_iff, true_imp_iff, imp_true_iff, and_true, true_and, add_zero, ne_eq, Nat.add_zero] at * <;> omega
  · skip
    refine ⟨fun hw => ?_, fun hw ho1 ho2 => ?_, fun hw ho1 ho2 => ?_, fun hw ho1 ho2 => ?_, fun hw ho1 ho2 => ?_⟩ <;>
      (simp only [defF, pot2F, nuF, ownAt, mF, not_false_eq_true, false_imp_iff, true_imp_iff, imp_true_iff, and_true, true_and, add_zero] at *) <;> by_cases c3 : sig n p s = σW <;>
      simp only [c3, if_true, if_false, not_true_eq_false, not_false_eq_true, false_imp_iff, true_imp_iff, imp_true_iff, and_true, true_and, add_zero, ne_eq, Nat.add_zero] at * <;> omega

lemma own_pot_le (h : Rng n p) (σW : ℕ) (hpar : (lam n p - (σW : ℤ)) % 2 = 0) (y : FIdx n p σW)
    (s : ℕ) (hs : sig n p s = σW) (ho : ownAt y s) : pot2F n p σW y ≤ lam n p - 2 := by
  rcases y with ⟨r, i⟩ | j
  · simp only [ownAt] at ho
    subst ho
    exact (pot_le h σW hpar (Sum.inl ⟨r, i⟩)).2 r i rfl hs
  · exact absurd ho (by simp [ownAt])

lemma ownAt_inl {σW : ℕ} {x : FIdx n p σW} {s : ℕ} (ho : ownAt x s) :
    ∃ (r : Fin p) (i : Fin (mF n p σW r)), x = Sum.inl ⟨r, i⟩ ∧ (r : ℕ) = s := by
  rcases x with ⟨r, i⟩ | j
  · exact ⟨r, i, rfl, ho⟩
  · exact absurd ho (by simp [ownAt])

/-- **L2S-20 `pair_classify`** (Lemma X, the δ-table).  For every pair of family elements one of:
(A) every node passes; (B) `x = e_{r,i}` is own at a window residue `r` and `y` has potential
`≥ λ + 1` (`g` or an `N`-top): deficit `≤ 1` at `r` only (Lemma O); (B') symmetric;
(C) both elements have potential `≥ λ - 1` and sum `2λ+1 ≤ · ≤ 2λ+2`: deficit `≤ 1` on the window,
`0` off it (Lemma W1); (D) both `≥ λ - 1`, sum `≥ 2λ + 3`: deficit `≤ 2` on the window (Lemma W2). -/
theorem pair_classify (h : Rng n p) (σW : ℕ) (hpar : (lam n p - (σW : ℤ)) % 2 = 0)
    (x y : FIdx n p σW) :
    (∀ s < p, defF n p σW x y s ≤ 0) ∨
    (∃ (r : Fin p) (i : Fin (mF n p σW r)), x = Sum.inl ⟨r, i⟩ ∧ sig n p r = σW ∧
      lam n p + 1 ≤ pot2F n p σW y ∧ ¬ ownAt y r ∧ defF n p σW x y r ≤ 1 ∧
      ∀ s < p, s ≠ (r : ℕ) → defF n p σW x y s ≤ 0) ∨
    (∃ (r : Fin p) (i : Fin (mF n p σW r)), y = Sum.inl ⟨r, i⟩ ∧ sig n p r = σW ∧
      lam n p + 1 ≤ pot2F n p σW x ∧ ¬ ownAt x r ∧ defF n p σW x y r ≤ 1 ∧
      ∀ s < p, s ≠ (r : ℕ) → defF n p σW x y s ≤ 0) ∨
    (lam n p - 1 ≤ pot2F n p σW x ∧ lam n p - 1 ≤ pot2F n p σW y ∧
      2 * lam n p + 1 ≤ pot2F n p σW x + pot2F n p σW y ∧
      pot2F n p σW x + pot2F n p σW y ≤ 2 * lam n p + 2 ∧
      (∀ s < p, sig n p s ≠ σW → defF n p σW x y s ≤ 0) ∧
      ∀ s < p, sig n p s = σW → defF n p σW x y s ≤ 1) ∨
    (lam n p - 1 ≤ pot2F n p σW x ∧ lam n p - 1 ≤ pot2F n p σW y ∧
      2 * lam n p + 3 ≤ pot2F n p σW x + pot2F n p σW y ∧
      (∀ s < p, sig n p s ≠ σW → defF n p σW x y s ≤ 0) ∧
      ∀ s < p, sig n p s = σW → defF n p σW x y s ≤ 2) := by
  have hx := pot_le h σW hpar x
  have hy := pot_le h σW hpar y
  have hl := fun s hs => def_local h σW hpar x y s hs
  by_cases hA : ∃ (r : Fin p) (i : Fin (mF n p σW r)), x = Sum.inl ⟨r, i⟩ ∧ sig n p r = σW ∧
      lam n p + 1 ≤ pot2F n p σW y
  · obtain ⟨r, i, hxe, hw, hyp⟩ := hA
    have hnown : ¬ ownAt y r := fun ho => by have := own_pot_le h σW hpar y r hw ho; omega
    refine Or.inr (Or.inl ⟨r, i, hxe, hw, hyp, hnown, ?_, ?_⟩)
    · have := (hl r r.2).2.2.1 hw (by rw [hxe]; simp [ownAt]) hnown
      omega
    · intro s hs hne
      by_cases hws : sig n p s = σW
      · have hxn : ¬ ownAt x s := by rw [hxe]; simp only [ownAt]; omega
        have hyn : ¬ ownAt y s := fun ho => by have := own_pot_le h σW hpar y s hws ho; omega
        have := (hl s hs).2.1 hws hxn hyn
        have := hx.2 r i hxe hw
        omega
      · exact (hl s hs).1 hws
  by_cases hB : ∃ (r : Fin p) (i : Fin (mF n p σW r)), y = Sum.inl ⟨r, i⟩ ∧ sig n p r = σW ∧
      lam n p + 1 ≤ pot2F n p σW x
  · obtain ⟨r, i, hye, hw, hxp⟩ := hB
    have hnown : ¬ ownAt x r := fun ho => by have := own_pot_le h σW hpar x r hw ho; omega
    refine Or.inr (Or.inr (Or.inl ⟨r, i, hye, hw, hxp, hnown, ?_, ?_⟩))
    · have := (hl r r.2).2.2.2.1 hw hnown (by rw [hye]; simp [ownAt])
      omega
    · intro s hs hne
      by_cases hws : sig n p s = σW
      · have hyn : ¬ ownAt y s := by rw [hye]; simp only [ownAt]; omega
        have hxn : ¬ ownAt x s := fun ho => by have := own_pot_le h σW hpar x s hws ho; omega
        have := (hl s hs).2.1 hws hxn hyn
        have := hy.2 r i hye hw
        omega
      · exact (hl s hs).1 hws
  by_cases hC : lam n p - 1 ≤ pot2F n p σW x ∧ lam n p - 1 ≤ pot2F n p σW y ∧
      2 * lam n p + 1 ≤ pot2F n p σW x + pot2F n p σW y
  · obtain ⟨c1, c2, c3⟩ := hC
    have hW : ∀ s < p, sig n p s = σW → defF n p σW x y s =
        (pot2F n p σW x + pot2F n p σW y + 1) / 2 - lam n p := by
      intro s hs hws
      refine (hl s hs).2.1 hws (fun ho => ?_) (fun ho => ?_)
      · have := own_pot_le h σW hpar x s hws ho; omega
      · have := own_pot_le h σW hpar y s hws ho; omega
    by_cases hD : 2 * lam n p + 3 ≤ pot2F n p σW x + pot2F n p σW y
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨c1, c2, hD, fun s hs hws => (hl s hs).1 hws,
        fun s hs hws => by have := hW s hs hws; omega⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨c1, c2, c3, by omega, fun s hs hws => (hl s hs).1 hws,
        fun s hs hws => by have := hW s hs hws; omega⟩)))
  · refine Or.inl fun s hs => ?_
    by_cases hws : sig n p s = σW
    · by_cases ox : ownAt x s <;> by_cases oy : ownAt y s
      · exact (hl s hs).2.2.2.2 hws ox oy
      · have := (hl s hs).2.2.1 hws ox oy
        obtain ⟨r, i, hxe, hre⟩ := ownAt_inl ox
        have hsr : sig n p r = σW := by rw [hre]; exact hws
        have : ¬ (lam n p + 1 ≤ pot2F n p σW y) := fun hh => hA ⟨r, i, hxe, hsr, hh⟩
        omega
      · have := (hl s hs).2.2.2.1 hws ox oy
        obtain ⟨r, i, hye, hre⟩ := ownAt_inl oy
        have hsr : sig n p r = σW := by rw [hre]; exact hws
        have : ¬ (lam n p + 1 ≤ pot2F n p σW x) := fun hh => hB ⟨r, i, hye, hsr, hh⟩
        omega
      · have := (hl s hs).2.1 hws ox oy
        omega
    · exact (hl s hs).1 hws

end PairClass







/-! ### the L2 family and the node data -/

/-! ### integrality of the main terms and the node bound `σ - 4 + e` -/

section NodeMain

variable {n p : ℕ} [hp : Fact p.Prime]

lemma mn_GV_C {σ : Type*} {e : ℤ} {x y : ℚ} (hx : x = (p : ℚ) ^ e * y) (hy : y ∈ LocRing p) :
    GV p e (MvPolynomial.C x : MvPolynomial σ ℚ) := by
  apply GV.const
  rw [hx, ← mul_assoc, ← zpow_add₀ (p_ne_zero' (p := p)), neg_add_cancel, zpow_zero, one_mul]
  exact hy

lemma mn_mul0 {e : ℤ} {f g : MPT} (hf : GV p 0 f) (hg : GV p e g) : GV p e (f * g) := by
  simpa using hf.mul hg

lemma mn_Cmul {e : ℤ} {x : ℚ} (hx : x ∈ LocRing p) {f : MPT} (hf : GV p e f) :
    GV p e (MvPolynomial.C x * f) := mn_mul0 (GV.const_loc hx) hf

lemma mn_lam0_mem (s : ℕ) (hs : s < p) : lam0 n p s ∈ LocRing p := by
  have hpp := hp.out.pos
  have hr2 := r2_lt n p hpp
  have hr6 := r6_lt n p hpp
  unfold lam0
  have a1 : Hq 1 (r2 n p + s - eflag n p s * p) ∈ LocRing p :=
    Hq_mem 1 _ (by unfold eflag; split_ifs <;> omega)
  have a2 : Hq 1 (r6 n p + bflag n p s * p - s) ∈ LocRing p :=
    Hq_mem 1 _ (by unfold bflag; split_ifs <;> omega)
  have a3 : Hq 1 s ∈ LocRing p := Hq_mem 1 _ hs
  have c3 : (3 : ℚ) ∈ LocRing p := by exact_mod_cast int_mem_locRing (ℓ := p) 3
  have c2 : (2 : ℚ) ∈ LocRing p := by exact_mod_cast int_mem_locRing (ℓ := p) 2
  have c5 : (5 : ℚ) ∈ LocRing p := by exact_mod_cast int_mem_locRing (ℓ := p) 5
  exact (LocRing p).sub_mem ((LocRing p).add_mem ((LocRing p).mul_mem c3 a1)
    ((LocRing p).mul_mem c2 a2)) ((LocRing p).mul_mem c5 a3)

/-- the bracket of both main terms: integral when `(f0, f1)` is. -/
lemma mn_bracket (n k : ℕ) (h8 : 8 * n < p ^ 2) (hk : k ≤ 6 * n)
    {e : ℤ} {f0 f1 : MPT} (hf0 : GV p e f0) (hf1 : GV p e f1) (κ : ℚ) (hκ : κ ∈ LocRing p) :
    GV p e (MvPolynomial.C (uL (k / p)) * f1 +
        MvPolynomial.C (vL n p k (k / p) - (p : ℚ) * lam0 n p (k % p) * uL (k / p)) * f0) ∧
    GV p e (MvPolynomial.C (uaL (k / p)) * f1 + MvPolynomial.C (vaL n p k (k / p)) * f0) ∧
    GV p e (MvPolynomial.C ((p : ℚ) * κ * lam0 n p (k % p) * uL (k / p)) * f0) := by
  have hpp := hp.out.pos
  have hkp : k / p < p := by
    rw [Nat.div_lt_iff_lt_mul hpp]; simpa [pow_two] using (show k < p ^ 2 by omega)
  have hsp : k % p < p := Nat.mod_lt _ hpp
  have huL := uL_mem (p := p) _ hkp
  have hvL := vL_mem (p := p) n k _ h8 hk hkp
  have hlam := mn_lam0_mem (n := n) (k % p) hsp
  have hh2 := Hq_mem (p := p) 2 (k / p) hkp
  have hh3 := Hq_mem (p := p) 3 (k / p) hkp
  have hδ := delta_mem (p := p) n k h8 hk
  have lp' : (p : ℚ) ∈ LocRing p := natq_mem p
  have c2 : (2 : ℚ) ∈ LocRing p := by exact_mod_cast int_mem_locRing (ℓ := p) 2
  have c3' : (-3 : ℚ) ∈ LocRing p := by exact_mod_cast int_mem_locRing (ℓ := p) (-3)
  refine ⟨?_, ?_, ?_⟩
  · exact (mn_Cmul huL hf1).add (mn_Cmul ((LocRing p).sub_mem hvL ((LocRing p).mul_mem
      ((LocRing p).mul_mem lp' hlam) huL)) hf0)
  · refine (mn_Cmul ?_ hf1).add (mn_Cmul ?_ hf0)
    · unfold uaL; exact (LocRing p).mul_mem c3' hh2
    · unfold vaL
      exact (LocRing p).mul_mem c3' ((LocRing p).add_mem ((LocRing p).mul_mem hδ hh2)
        ((LocRing p).mul_mem c2 hh3))
  · exact mn_Cmul ((LocRing p).mul_mem ((LocRing p).mul_mem ((LocRing p).mul_mem lp' hκ) hlam) huL) hf0

lemma mn_ndJet_ge (n k u : ℕ) (h8 : 8 * n < p ^ 2) (hk : k ≤ 6 * n) {e : ℤ} {f0 f1 : MPT}
    (hf0 : GV p e f0) (hf1 : GV p e f1) :
    GV p ((sig n p (k % p) : ℤ) - 4 + e) (ndJet n p k u f0 f1) := by
  obtain ⟨h1, h2, -⟩ := mn_bracket n k h8 hk hf0 hf1 0 (LocRing p).zero_mem
  have lp' : (p : ℚ) ∈ LocRing p := natq_mem p
  have hc : GV p ((sig n p (k % p) : ℤ) - 4)
      (MvPolynomial.C ((p : ℚ) ^ ((sig n p (k % p) : ℤ) - 4) * u) : MPT) :=
    mn_GV_C rfl (by exact_mod_cast int_mem_locRing (ℓ := p) (u : ℤ))
  have hb : GV p 0 bT := GV.var _
  have ha : GV p 0 aT := GV.var _
  have hpa : GV p 0 (MvPolynomial.C (p : ℚ) * aT : MPT) := mn_Cmul lp' ha
  unfold ndJet
  exact hc.mul ((mn_mul0 hb h1).add (mn_mul0 hpa h2))

lemma mn_nodeJet_ge (n k : ℕ) (h8 : 8 * n < p ^ 2) (hk : k ≤ 6 * n) {e : ℤ} {f0 f1 : MPT}
    (hf0 : GV p e f0) (hf1 : GV p e f1) :
    GV p ((sig n p (k % p) : ℤ) - 4 + e) (nodeJet n p k f0 f1) := by
  have hpp := hp.out.pos
  have hkp : k / p < p := by
    rw [Nat.div_lt_iff_lt_mul hpp]; simpa [pow_two] using (show k < p ^ 2 by omega)
  have hκ : ((kapZ n p (bflag n p (k % p)) (eflag n p (k % p)) (k / p) : ℤ) : ℚ) ∈ LocRing p := by
    exact_mod_cast int_mem_locRing (ℓ := p) _
  obtain ⟨-, h2, h3⟩ := mn_bracket n k h8 hk hf0 hf1
    ((kapZ n p (bflag n p (k % p)) (eflag n p (k % p)) (k / p) : ℤ) : ℚ) hκ
  have lp' : (p : ℚ) ∈ LocRing p := natq_mem p
  have hc : GV p ((sig n p (k % p) : ℤ) - 4)
      (MvPolynomial.C ((p : ℚ) ^ ((sig n p (k % p) : ℤ) - 4) * (clZ n p (k / p) (k % p) : ℚ)) : MPT) :=
    mn_GV_C rfl (by exact_mod_cast int_mem_locRing (ℓ := p) _)
  have hb : GV p 0 bT := GV.var _
  have ha : GV p 0 aT := GV.var _
  have hTu : GV p 0 (Tu (k / p)) := GV.var _
  have hTv : GV p 0 (Tv (k / p)) := GV.var _
  have hA : GV p e (Tu (k / p) * f1 + Tv (k / p) * f0 -
      MvPolynomial.C ((p : ℚ) * (kapZ n p (bflag n p (k % p)) (eflag n p (k % p)) (k / p) : ℚ) *
        lam0 n p (k % p) * uL (k / p)) * f0) :=
    ((mn_mul0 hTu hf1).add (mn_mul0 hTv hf0)).sub h3
  have hpa : GV p 0 (MvPolynomial.C (p : ℚ) * aT *
      MvPolynomial.C (kapZ n p (bflag n p (k % p)) (eflag n p (k % p)) (k / p) : ℚ) : MPT) := by
    have := mn_mul0 (mn_Cmul lp' ha) (GV.const_loc hκ)
    simpa [mul_assoc] using this
  unfold nodeJet
  exact hc.mul ((mn_mul0 hb hA).add (mn_mul0 hpa h2))

end NodeMain

section Window

variable {n p : ℕ} [hp : Fact p.Prime]

/-- The local factors `q_r`: `P_s = shiftP A` on the window, `(X + r)^{μ′_r}` off it. -/
noncomputable def qF (n p σW μ : ℕ) (A : Polynomial MPT) (r : Fin p) : Polynomial MPT :=
  if sig n p r = σW then shiftP p μ r A else sX r ^ mF n p σW r

/-- The elements `e_{r,i}`, `g_j` of the L2 family. -/
noncomputable def elF (n p σW μ : ℕ) (A : Polynomial MPT) : FIdx n p σW → Polynomial MPT :=
  famFun (fun r : Fin p => Polynomial.X - Polynomial.C (zphi (-((r : ℕ) : ℤ)))) (qF n p σW μ A)
    (fun r : Fin p => mF n p σW r) (xtwo n p).toNat

/-- The modified nodes: `ℓ ≥ 1` and the residue lies in the window. -/
def Kset (n p σW : ℕ) : Finset ℕ :=
  (range (6 * n + 1)).filter (fun k => 1 ≤ k / p ∧ sig n p (k % p) = σW)

def sigN (n p : ℕ) (k : ℕ) : ℤ := (sig n p (k % p) : ℤ)

def clN (n p : ℕ) (k : ℕ) : ℚ := (clZ n p (k / p) (k % p) : ℚ)

/-- `τ^u_ℓ = κ_ℓ u_ℓ`, `κ_ℓ` of the window class of the residue `s0`. -/
noncomputable def tauU (n p s0 : ℕ) (l : ℕ) : ℚ :=
  if l < p then (kapZ n p (bflag n p s0) (eflag n p s0) l : ℚ) * uL l else 0

/-- `τ^v_ℓ = κ_ℓ v_ℓ`. -/
noncomputable def tauV (n p s0 : ℕ) (l : ℕ) : ℚ :=
  if l < p ∧ s0 + l * p ≤ 6 * n then
    (kapZ n p (bflag n p s0) (eflag n p s0) l : ℚ) * vL n p (s0 + l * p) l else 0

/-! ### the window node data and the node sums -/

section WinData

variable {n p : ℕ} [hp : Fact p.Prime]

lemma mn_Lc_eq (s : ℕ) : Lc n p s = q6 n p - bflag n p s := by
  unfold Lc bflag; split_ifs <;> omega

lemma mn_flags_of_sig {s s' : ℕ} (hsig : sig n p s = sig n p s') :
    bflag n p s = bflag n p s' ∧ eflag n p s = eflag n p s' := by
  have h1 := sig_eq_flags n p s
  have h2 := sig_eq_flags n p s'
  have b1 : bflag n p s ≤ 1 := by unfold bflag; split_ifs <;> omega
  have b2 : bflag n p s' ≤ 1 := by unfold bflag; split_ifs <;> omega
  have e1 : eflag n p s ≤ 1 := by unfold eflag; split_ifs <;> omega
  have e2 : eflag n p s' ≤ 1 := by unfold eflag; split_ifs <;> omega
  omega

lemma mn_Lc_bound (h : Rng n p) (s : ℕ) (hs : s < p) :
    s + Lc n p s * p ≤ 6 * n ∧ 6 * n < s + (Lc n p s + 1) * p := by
  have hpp := h.p5
  have a6 := qr6 n p (by omega)
  have hr6 := r6_lt n p (by omega)
  have hq := h.q6_ge
  unfold Lc
  have e1 : (q6 n p + 1) * p = q6 n p * p + p := by ring
  have e2 : (q6 n p - 1 + 1) * p = q6 n p * p := by
    rw [Nat.sub_add_cancel (by omega)]
  have e3 : (q6 n p - 1) * p + p = q6 n p * p := by
    rw [← e2]; ring
  split_ifs with hc
  · rw [e1]; omega
  · rw [e2]; omega

lemma mn_mem_Kset (σW k : ℕ) :
    k ∈ Kset n p σW ↔ k ≤ 6 * n ∧ 1 ≤ k / p ∧ sig n p (k % p) = σW := by
  unfold Kset
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

lemma mn_div_lt (h : Rng n p) {k : ℕ} (hk : k ≤ 6 * n) : k / p < p := by
  have hpp := h.p5
  rw [Nat.div_lt_iff_lt_mul (by omega)]
  have := h.h8
  simpa [pow_two] using (show k < p ^ 2 by omega)

lemma mn_nodeData (h : Rng n p) (σW s0 : ℕ) (hs0 : s0 < p) (hsW : sig n p s0 = σW) (k : ℕ)
    (hk : k ∈ Kset n p σW) :
    NodeData2 p n (sigN n p) (clN n p) (tauU n p s0) (tauV n p s0) k := by
  obtain ⟨hk6, hl, hsig⟩ := (mn_mem_Kset σW k).1 hk
  have hpp := h.p5
  have hsp : k % p < p := Nat.mod_lt _ (by omega)
  have hkp := mn_div_lt h hk6
  obtain ⟨hb, he⟩ := mn_flags_of_sig (n := n) (p := p) (s := s0) (s' := k % p) (by rw [hsW, hsig])
  -- the node index is at most `L`
  have hLeq : Lc n p (k % p) = Lc n p s0 := by rw [mn_Lc_eq, mn_Lc_eq, hb]
  have hkk : k % p + (k / p) * p = k := by rw [mul_comm]; exact Nat.mod_add_div k p
  obtain ⟨c1, c2⟩ := mn_Lc_bound h (k % p) hsp
  obtain ⟨d1, d2⟩ := mn_Lc_bound h s0 hs0
  have hlL : k / p ≤ Lc n p s0 := by
    by_contra hcon
    push_neg at hcon
    have : (Lc n p s0 + 1) * p ≤ (k / p) * p := Nat.mul_le_mul_right p hcon
    rw [← hLeq] at this
    omega
  have hk0 : s0 + (k / p) * p ≤ 6 * n := by
    have : (k / p) * p ≤ Lc n p s0 * p := Nat.mul_le_mul_right p hlL
    omega
  refine ⟨hl, rfl, rfl, ?_, ?_⟩
  · unfold tauU
    rw [if_pos hkp, hb, he]
  · unfold tauV
    rw [if_pos ⟨hkp, hk0⟩, hb, he]
    have d1' := laiDelta_digits (n := n) (p := p) (k := s0 + (k / p) * p) hk0
    have d2' := laiDelta_digits (n := n) (p := p) (k := k) hk6
    have q1 : (s0 + (k / p) * p) / p = k / p := by
      rw [Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hs0]; simp
    have q2 : (s0 + (k / p) * p) % p = s0 := by
      rw [Nat.add_mul_mod_self_right]; exact Nat.mod_eq_of_lt hs0
    have hv : vL n p (s0 + (k / p) * p) (k / p) = vL n p k (k / p) := by
      unfold vL
      rw [d1', d2', q1, q2, hb, he]
    rw [hv]

lemma mn_sum_fiber {M : Type*} [AddCommMonoid M] (h : Rng n p) (s : ℕ) (hs : s < p) (g : ℕ → M) :
    ∑ k ∈ (range (6 * n + 1)).filter (fun k => k % p = s), g k =
      ∑ l ∈ range (Lc n p s + 1), g (s + l * p) := by
  have hpp := h.p5
  obtain ⟨b1, b2⟩ := mn_Lc_bound h s hs
  refine Finset.sum_nbij' (fun k => k / p) (fun l => s + l * p) ?_ ?_ ?_ ?_ ?_
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk ⊢
    obtain ⟨hk6, hm⟩ := hk
    have hkk : s + (k / p) * p = k := by rw [← hm, mul_comm]; exact Nat.mod_add_div k p
    by_contra hcon
    push_neg at hcon
    have : (Lc n p s + 1) * p ≤ (k / p) * p := Nat.mul_le_mul_right p (by omega)
    omega
  · intro l hl
    simp only [Finset.mem_filter, Finset.mem_range] at hl ⊢
    have : l * p ≤ Lc n p s * p := Nat.mul_le_mul_right p (by omega)
    refine ⟨by omega, ?_⟩
    rw [Nat.add_mul_mod_self_right]; exact Nat.mod_eq_of_lt hs
  · intro k hk
    simp only [Finset.mem_filter] at hk
    show s + (k / p) * p = k
    rw [← hk.2, mul_comm]; exact Nat.mod_add_div k p
  · intro l hl
    show (s + l * p) / p = l
    rw [Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hs]; simp
  · intro k hk
    simp only [Finset.mem_filter] at hk
    show g k = g (s + (k / p) * p)
    rw [← hk.2, mul_comm]
    rw [Nat.mod_add_div k p]

lemma mn_laiLTx_res (h : Rng n p) (K : Finset ℕ) (hK6 : K ⊆ range (6 * n + 1)) (σ : ℕ → ℤ)
    (cl τu τv : ℕ → ℚ) (F : Polynomial MPT) :
    laiLTx (p := p) n K σ cl τu τv F =
      ∑ s ∈ range p, ∑ l ∈ range (Lc n p s + 1), nodeT (p := p) n K σ cl τu τv (s + l * p) F := by
  have hpp := h.p5
  rw [laiLTx_nodes n K hK6, ← Finset.sum_fiberwise_of_maps_to (g := fun k => k % p) (t := range p)
    (fun k _ => Finset.mem_range.2 (Nat.mod_lt _ (by omega)))]
  refine Finset.sum_congr rfl fun s hs => ?_
  exact mn_sum_fiber h s (Finset.mem_range.1 hs) _

theorem mn_node_pass (h : Rng n p) (σW s0 : ℕ) (hs0 : s0 < p) (hsW : sig n p s0 = σW)
    (k : ℕ) (hk : k ≤ 6 * n) (F : Polynomial MPT) (e : ℤ) (hF : JetGE p k e F) :
    GV p ((sig n p (k % p) : ℤ) - 4 + e)
      (nodeT (p := p) n (Kset n p σW) (sigN n p) (clN n p) (tauU n p s0) (tauV n p s0) k F) := by
  have hp3 : 3 ≤ p := by have := h.p5; omega
  have h8 := h.h8
  by_cases hl : 1 ≤ k / p
  · obtain ⟨u, hu, -⟩ := laiCoef_kc_p2 (p := p) h8 hp3 k hk
    have hu' : (laiCoef n k : ℚ) = (p : ℚ) ^ (sig n p (k % p)) * u := by exact_mod_cast hu
    by_cases hkK : k ∈ Kset n p σW
    · have hd := mn_nodeData h σW s0 hs0 hsW k hkK
      have h1 := nodeT_jet n (Kset n p σW) (sigN n p) (clN n p) (tauU n p s0) (tauV n p s0) h8 hp3 k hk
        hkK hd F e hF
      have h2 := (h1.mono (by omega : (sig n p (k % p) : ℤ) - 4 + e ≤ (sig n p (k % p) : ℤ) - 2 + e)).add
        (mn_nodeJet_ge n k h8 hk hF.1 hF.2)
      simpa using h2
    · have h1 := nd_jet n k h8 hp3 hk hl u hu' F e hF
      have h2 := (h1.mono (by omega : (sig n p (k % p) : ℤ) - 4 + e ≤ (sig n p (k % p) : ℤ) - 2 + e)).add
        (mn_ndJet_ge n k u h8 hk hF.1 hF.2)
      unfold nodeT
      rw [if_neg hkK, add_zero]
      simpa using h2
  · have hkp : k < p := by
      by_contra hc
      exact hl (Nat.div_pos (by omega) (by omega))
    have hkK : k ∉ Kset n p σW := fun hK => hl ((mn_mem_Kset σW k).1 hK).2.1
    have h1 := nd0_jet n k h8 hp3 hk hkp F e hF
    unfold nodeT
    rw [if_neg hkK, add_zero, Nat.mod_eq_of_lt hkp]
    exact h1.mono (by omega)

end WinData


lemma jetpow (k m : ℕ) : JetGE p k (m : ℤ) (sX (k % p) ^ m) := by
  induction m with
  | zero =>
    simpa using JetGE.of_pint (p := p) (k := k) (F := (1 : Polynomial MPT))
      (by simpa using PInt_C (p := p) (c := (1 : MPT)) GV.one)
  | succ m ih =>
    have := ih.mul (JetGE.sX_self (p := p) k)
    rw [pow_succ]; simpa [Nat.cast_succ] using this

/-- **L2S-19 `fam_jets`.** `ν_k(e_x) ≥ ord_{k mod p}(x)`. -/
theorem fam_jets (σW μ : ℕ) (hμ : ∀ r < p, sig n p r = σW → mu n p r = μ) {A : Polynomial MPT} (hA : PInt p A)
    (hAd : A.natDegree ≤ μ) (x : FIdx n p σW) (k : ℕ) :
    JetGE p k (nuF n p σW x (k % p) : ℤ) (elF n p σW μ A x) := by
  classical
  have hpp := hp.out.pos
  have hsp : k % p < p := Nat.mod_lt _ hpp
  set sF : Fin p := ⟨k % p, hsp⟩ with hsF
  have hk : k % p + (k / p) * p = k := by rw [mul_comm]; exact Nat.mod_add_div k p
  have hq : JetGE p k (mF n p σW (k % p) : ℤ) (qF n p σW μ A sF) := by
    unfold qF
    by_cases hw : sig n p (sF : ℕ) = σW
    · rw [if_pos hw]
      have hm : mF n p σW (k % p) = μ := by
        unfold mF
        rw [hμ (k % p) hsp hw, if_pos hw]; rfl
      have := JetGE.shiftP (p := p) μ (k % p) (k / p) hA hAd
      rw [hk] at this
      rw [hm]; exact this
    · rw [if_neg hw]
      exact jetpow k (mF n p σW (k % p))
  have hqP : ∀ r : Fin p, PInt p (qF n p σW μ A r) := by
    intro r
    unfold qF
    split_ifs
    · exact PInt_shiftP μ _ hA
    · exact (PInt_sX _).pow _
  have hprod : ∀ S : Finset (Fin p), JetGE p k (if sF ∈ S then (mF n p σW (k % p) : ℤ) else 0)
      (∏ r ∈ S, qF n p σW μ A r) := by
    intro S
    by_cases hS : sF ∈ S
    · rw [if_pos hS, ← Finset.mul_prod_erase S _ hS]
      have := hq.mul (JetGE.of_pint (p := p) (k := k) (PInt.prod (s := S.erase sF) fun r _ => hqP r))
      simpa using this
    · rw [if_neg hS]
      exact JetGE.of_pint (PInt.prod (s := S) fun r _ => hqP r)
  have hX : PInt p (Polynomial.X : Polynomial MPT) := PInt_X
  rcases x with ⟨r0, i⟩ | j
  · simp only [elF, famFun, Sum.elim_inl, nuF]
    have hu : sX (r0 : ℕ) = Polynomial.X - Polynomial.C (zphi (-((r0 : ℕ) : ℤ))) := sX_eq_sub _
    rw [← hu]
    by_cases he : (r0 : ℕ) = k % p
    · rw [if_pos he]
      have h1 : JetGE p k ((i : ℕ) : ℤ) (sX (r0 : ℕ) ^ (i : ℕ)) := by
        have hh : ∀ m : ℕ, JetGE p k (m : ℤ) (sX (r0 : ℕ) ^ m) := fun m => by rw [he]; exact jetpow k m
        exact hh i
      have h2 := hprod (Finset.univ.erase r0)
      have hn : sF ∉ Finset.univ.erase r0 := by
        simp only [Finset.mem_erase, not_and]
        intro hne; exact absurd (Fin.ext he.symm) hne
      rw [if_neg hn] at h2
      simpa using h1.mul h2
    · rw [if_neg he]
      have h1 : JetGE p k 0 (sX (r0 : ℕ) ^ (i : ℕ)) := JetGE.of_pint ((PInt_sX _).pow _)
      have h2 := hprod (Finset.univ.erase r0)
      have hn : sF ∈ Finset.univ.erase r0 := by
        simp only [Finset.mem_erase, Finset.mem_univ, and_true]
        intro h'; exact he (congrArg Fin.val h').symm
      rw [if_pos hn] at h2
      simpa using h1.mul h2
  · simp only [elF, famFun, Sum.elim_inr, nuF]
    have h1 : JetGE p k 0 ((Polynomial.X : Polynomial MPT) ^ (j : ℕ)) := JetGE.of_pint (hX.pow _)
    have h2 := hprod Finset.univ
    rw [if_pos (Finset.mem_univ _)] at h2
    simpa using h1.mul h2

/-- `μ′_r - i`: the order of the pole of `e_{r,i}/Π` at the root `-r`. -/
noncomputable def poleF (n p σW : ℕ) : FIdx n p σW → ℕ → ℕ
  | Sum.inl ⟨r0, i⟩, r => if (r0 : ℕ) = r then mF n p σW r - (i : ℕ) else 0
  | Sum.inr _, _ => 0

/-- the power of `X` in `g_j`. -/
def jF (n p σW : ℕ) : FIdx n p σW → ℕ
  | Sum.inl _ => 0
  | Sum.inr j => (j : ℕ)

/-- the exponent of `(X + r)` in `e_x / ∏_{W} P_s`. -/
noncomputable def exF (n p σW : ℕ) (x : FIdx n p σW) (r : ℕ) : ℕ :=
  if sig n p r = σW then 0 else mF n p σW r - poleF n p σW x r

/-- `e_x / ∏_{r ∈ W} P_r` as an integer polynomial. -/
noncomputable def ExZ (n p σW : ℕ) (x : FIdx n p σW) : Polynomial ℤ :=
  Polynomial.X ^ jF n p σW x * ∏ r ∈ range p, (Polynomial.X + Polynomial.C (r : ℤ)) ^ exF n p σW x r

lemma sX_map_zphi (r : ℕ) : (Polynomial.X + Polynomial.C (r : ℤ)).map zphi = sX r := by
  simp [sX, zphi_apply]

lemma ExZ_map (σW : ℕ) (x : FIdx n p σW) :
    (ExZ n p σW x).map zphi = Polynomial.X ^ jF n p σW x * ∏ r ∈ range p, sX r ^ exF n p σW x r := by
  unfold ExZ
  rw [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_prod]
  congr 1
  refine Finset.prod_congr rfl fun r _ => ?_
  rw [Polynomial.map_pow, sX_map_zphi]

lemma el_decomp (σW μ : ℕ) (A : Polynomial MPT) (Wf : Finset ℕ)
    (hWf : ∀ r, r ∈ Wf ↔ r < p ∧ sig n p r = σW) (x : FIdx n p σW)
    (hx : ∀ (r : Fin p) (i : Fin (mF n p σW r)), x = Sum.inl ⟨r, i⟩ → sig n p r ≠ σW) :
    elF n p σW μ A x = (∏ r ∈ Wf, shiftP p μ r A) * (ExZ n p σW x).map zphi := by
  classical
  have hWf' : Wf = (range p).filter (fun r => sig n p r = σW) := by
    ext r; simp [hWf, Finset.mem_filter, Finset.mem_range]
  set ff : ℕ → Polynomial MPT := fun r =>
    if sig n p r = σW then shiftP p μ r A else sX r ^ exF n p σW x r with hff
  have key : elF n p σW μ A x =
      Polynomial.X ^ jF n p σW x * ∏ r ∈ range p, ff r := by
    rw [← Fin.prod_univ_eq_prod_range ff p]
    rcases x with ⟨r0, i⟩ | j
    · have hr0 := hx r0 i rfl
      simp only [elF, famFun, Sum.elim_inl, jF, pow_zero, one_mul]
      rw [← Finset.mul_prod_erase Finset.univ (fun r : Fin p => ff r) (Finset.mem_univ r0)]
      congr 1
      · have : ff r0 = sX r0 ^ (i : ℕ) := by
          simp only [hff, if_neg hr0, exF, poleF, if_true]
          congr 1
          have := i.2
          omega
        rw [this, sX_eq_sub]
      · refine Finset.prod_congr rfl fun r hr => ?_
        have hne : (r : ℕ) ≠ r0 := fun h => (Finset.mem_erase.1 hr).1 (Fin.ext h)
        simp only [hff, qF, exF, poleF, if_neg (Ne.symm hne), Nat.sub_zero]
        by_cases hw : sig n p (r : ℕ) = σW <;> simp [hw]
    · simp only [elF, famFun, Sum.elim_inr, jF]
      congr 1
      refine Finset.prod_congr rfl fun r _ => ?_
      simp only [hff, qF, exF, poleF, Nat.sub_zero]
      by_cases hw : sig n p (r : ℕ) = σW <;> simp [hw]
  rw [key, ExZ_map]
  have hsplit : ∏ r ∈ range p, ff r =
      (∏ r ∈ Wf, shiftP p μ r A) * ∏ r ∈ range p, sX r ^ exF n p σW x r := by
    rw [hWf', Finset.prod_filter, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun r _ => ?_
    by_cases hw : sig n p r = σW
    · simp [hff, hw, exF]
    · simp [hff, hw]
  rw [hsplit]
  ring

/-- `c r = (r : ℤ/p²)`. -/
def cR (p : ℕ) (r : ℕ) : ZMod (p ^ 2) := (r : ZMod (p ^ 2))

/-- the exponent of `(r - X)` in `E`. -/
noncomputable def e2F (n p σW r : ℕ) : ℕ := if sig n p r = σW then 0 else gexp n p σW r

lemma Epoly_eq (σW : ℕ) : Epoly n p σW = Pr (cR p) (range p) (e2F n p σW) := rfl

lemma Qhat_eq (σW : ℕ) :
    QhatPoly n p σW = Polynomial.C ((-1 : ZMod (p ^ 2)) ^ (∑ r ∈ range p, mexp n p σW r)) *
      Pr (cR p) (range p) (mexp n p σW) := by
  unfold QhatPoly Pr
  have : ∀ r ∈ range p, (Polynomial.X - Polynomial.C (r : ZMod (p ^ 2))) ^ mexp n p σW r =
      Polynomial.C ((-1 : ZMod (p ^ 2)) ^ mexp n p σW r) * qq (cR p) r ^ mexp n p σW r := by
    intro r _
    have : Polynomial.X - Polynomial.C (r : ZMod (p ^ 2)) = Polynomial.C (-1) * qq (cR p) r := by
      simp [qq, cR]
    rw [this, mul_pow, ← Polynomial.C_pow]
  rw [Finset.prod_congr rfl this, Finset.prod_mul_distrib, ← map_prod, Finset.prod_pow_eq_pow_sum]

lemma Vneg_form (j : ℕ) (a : ℕ → ℕ) :
    Vneg p (Polynomial.X ^ j * ∏ r ∈ range p, (Polynomial.X + Polynomial.C (r : ℤ)) ^ a r) =
      (-Polynomial.X) ^ j * Pr (cR p) (range p) a := by
  unfold Vneg Pr
  rw [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_prod,
    Polynomial.mul_comp, Polynomial.pow_comp, Polynomial.X_comp, Polynomial.prod_comp]
  congr 1
  refine Finset.prod_congr rfl fun r _ => ?_
  rw [Polynomial.map_pow, Polynomial.pow_comp]
  congr 1
  simp [qq, cR]
  ring

lemma ExZ_mul (σW : ℕ) (x y : FIdx n p σW) :
    ExZ n p σW x * ExZ n p σW y = Polynomial.X ^ (jF n p σW x + jF n p σW y) *
      ∏ r ∈ range p, (Polynomial.X + Polynomial.C (r : ℤ)) ^ (exF n p σW x r + exF n p σW y r) := by
  unfold ExZ
  have : ∏ r ∈ range p, (Polynomial.X + Polynomial.C (r : ℤ)) ^ (exF n p σW x r + exF n p σW y r) =
      (∏ r ∈ range p, (Polynomial.X + Polynomial.C (r : ℤ)) ^ exF n p σW x r) *
        ∏ r ∈ range p, (Polynomial.X + Polynomial.C (r : ℤ)) ^ exF n p σW y r := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun r _ => by rw [pow_add]
  rw [this, pow_add]
  ring

lemma Vneg_deriv (V : Polynomial ℤ) :
    Vneg p (Polynomial.derivative V) = -Polynomial.derivative (Vneg p V) := by
  unfold Vneg
  rw [Polynomial.derivative_comp, Polynomial.derivative_map]
  simp

lemma resN (h : Rng n p) (σW r : ℕ) (hr : r < p) (hrW : sig n p r ≠ σW) :
    ((lam n p - (sig n p r : ℤ)) % 2 = 0 → 2 * (mu n p r : ℤ) + sig n p r = lam n p + 4 ∧
        mexp n p σW r = 2) ∧
    ((lam n p - (sig n p r : ℤ)) % 2 ≠ 0 → 2 * (mu n p r : ℤ) + sig n p r = lam n p + 5 ∧
        mexp n p σW r = 3) := by
  have hS := (lemmaS h).2.2.1 r hr
  have hm : mexp n p σW r = 2 + (if (lam n p - (sig n p r : ℤ)) % 2 ≠ 0 then 1 else 0) := by
    unfold mexp; rw [if_neg hrW]
  refine ⟨fun h0 => ?_, fun h0 => ?_⟩
  · rw [if_pos h0] at hS
    rw [hm, if_neg (by simpa using h0)]
    exact ⟨by omega, rfl⟩
  · rw [if_neg h0] at hS
    rw [hm, if_pos h0]
    exact ⟨by omega, rfl⟩

lemma pole_cases (h : Rng n p) (σW : ℕ) (x : FIdx n p σW) (r : ℕ) (hr : r < p) (hrW : sig n p r ≠ σW) :
    poleF n p σW x r = 0 ∨
      2 * (poleF n p σW x r : ℤ) + pot2F n p σW x = lam n p + (mexp n p σW r : ℤ) := by
  rcases x with ⟨r0, i⟩ | j
  · by_cases e : (r0 : ℕ) = r
    · right
      have hi := i.2
      have h1 : mF n p σW r0 = mF n p σW r := congrArg (mF n p σW) e
      have h2 : sig n p r0 = sig n p r := congrArg (sig n p) e
      have h3 : mF n p σW r = mu n p r + 1 := by unfold mF; rw [if_neg hrW]
      have fr := resN h σW r hr hrW
      simp only [poleF, pot2F, if_pos e]
      by_cases hpar : (lam n p - (sig n p r : ℤ)) % 2 = 0
      · have := fr.1 hpar; omega
      · have := fr.2 hpar; omega
    · left; simp [poleF, e]
  · left; simp [poleF]

lemma pole_bound (h : Rng n p) (σW : ℕ) (c : ℕ) (hc1 : 1 ≤ c) (hc2 : c ≤ 2)
    (x y : FIdx n p σW)
    (cx : lam n p - 1 ≤ pot2F n p σW x) (cy : lam n p - 1 ≤ pot2F n p σW y)
    (cs : 2 * lam n p + 2 * c - 1 ≤ pot2F n p σW x + pot2F n p σW y)
    (hxle : pot2F n p σW x ≤ lam n p + 2) (hyle : pot2F n p σW y ≤ lam n p + 2)
    (r : ℕ) (hr : r < p) (hrW : sig n p r ≠ σW) :
    poleF n p σW x r + poleF n p σW y r + c ≤ mexp n p σW r := by
  have hm0 : 2 ≤ mexp n p σW r := by
    unfold mexp; rw [if_neg hrW]; omega
  have hm3 : mexp n p σW r ≤ 3 := by
    unfold mexp; rw [if_neg hrW]; split_ifs <;> omega
  rcases pole_cases h σW x r hr hrW with a | a <;> rcases pole_cases h σW y r hr hrW with b | b <;>
    omega

lemma poleF_le (σW : ℕ) (x : FIdx n p σW) (r : ℕ) : poleF n p σW x r ≤ mF n p σW r := by
  rcases x with ⟨r0, i⟩ | j
  · simp only [poleF]
    split_ifs <;> omega
  · simp [poleF]

lemma poleF_W (σW : ℕ) (x : FIdx n p σW)
    (hx : ∀ (r : Fin p) (i : Fin (mF n p σW r)), x = Sum.inl ⟨r, i⟩ → sig n p r ≠ σW) (r : ℕ)
    (hr : sig n p r = σW) : poleF n p σW x r = 0 := by
  rcases x with ⟨r0, i⟩ | j
  · simp only [poleF]
    split_ifs with e
    · exact absurd (by rw [e]; exact hr) (hx r0 i rfl)
    · rfl
  · rfl

open Classical in
lemma sum_mexp (σW : ℕ) :
    ∑ r ∈ range p, mexp n p σW r = 2 * (p - ((range p).filter (fun s => sig n p s = σW)).card) +
      Ncnt n p := by
  unfold mexp
  rw [Finset.sum_add_distrib]
  congr 1
  · have e : ∀ r ∈ range p, (if sig n p r = σW then 0 else 2) = 2 * (if sig n p r = σW then 0 else 1) :=
      fun r _ => by split_ifs <;> rfl
    rw [Finset.sum_congr rfl e, ← Finset.mul_sum]
    congr 1
    have h1 := Finset.card_filter_add_card_filter_not (s := range p) (fun s => sig n p s = σW)
    simp only [Finset.card_range] at h1
    have : ∑ r ∈ range p, (if sig n p r = σW then 0 else 1) =
        ((range p).filter (fun s => ¬ sig n p s = σW)).card := by
      rw [Finset.card_filter]
      exact Finset.sum_congr rfl fun r _ => by split_ifs <;> rfl
    rw [this]; omega
  · unfold Ncnt
    rw [Finset.card_filter]

open Classical in
lemma sum_mexp_eq (h : Rng n p) (σW : ℕ)
    (hcard : ((range p).filter (fun s => sig n p s = σW)).card = tieW n p) (hx2 : 0 < xtwo n p) :
    ∑ r ∈ range p, mexp n p σW r + 2 * (xtwo n p).toNat + 2 = p := by
  obtain ⟨hlam, h2d, hx1, h2x⟩ := law_second_level h hx2
  have hsum := tie_sum h
  have hs := sum_mexp (n := n) (p := p) σW
  rw [hcard] at hs
  have hxt : xtwo n p = xone n p - Ncnt n p := by unfold xtwo at *; omega
  have : ((xtwo n p).toNat : ℤ) = xtwo n p := by omega
  omega

lemma jF_lt (σW : ℕ) (hx2 : 0 < xtwo n p) (x : FIdx n p σW) : jF n p σW x < (xtwo n p).toNat := by
  rcases x with ⟨r, i⟩ | j
  · simp only [jF]; omega
  · simp only [jF]; exact j.2

theorem pair_Gdata_core (h : Rng n p) (σW : ℕ) (hpar : (lam n p - (σW : ℤ)) % 2 = 0)
    (hx2 : 0 < xtwo n p)
    (hcard : ((range p).filter (fun s => sig n p s = σW)).card = tieW n p)
    (μ : ℕ) (A : Polynomial MPT) (Wf : Finset ℕ) (hWf : ∀ r, r ∈ Wf ↔ r < p ∧ sig n p r = σW)
    (c : ℕ) (hc1 : 1 ≤ c) (hc2 : c ≤ 2) (x y : FIdx n p σW)
    (cx : lam n p - 1 ≤ pot2F n p σW x) (cy : lam n p - 1 ≤ pot2F n p σW y)
    (cs : 2 * lam n p + 2 * c - 1 ≤ pot2F n p σW x + pot2F n p σW y) :
    ∃ (V : Polynomial ℤ) (G Hr : Polynomial (ZMod (p ^ 2))),
      elF n p σW μ A x * elF n p σW μ A y = (∏ r ∈ Wf, shiftP p μ r A) ^ 2 * V.map zphi ∧
      G * Epoly n p σW = QhatPoly n p σW * Vneg p V ∧
      Hr * Epoly n p σW = QhatPoly n p σW * Vneg p (Polynomial.derivative V) ∧
      G.natDegree ≤ p - 4 ∧ Hr.natDegree ≤ p - 4 ∧
      (∀ m, m < p → m ∉ Wf → G.eval (m : ZMod (p ^ 2)) = 0) ∧
      (c = 2 → (∀ m, m < p → m ∉ Wf → (Polynomial.derivative G).eval (m : ZMod (p ^ 2)) = 0) ∧
        (∀ m, m < p → m ∉ Wf → Hr.eval (m : ZMod (p ^ 2)) = 0)) := by
  classical
  have hxle := (pot_le h σW hpar x).1
  have hyle := (pot_le h σW hpar y).1
  have hxn : ∀ (r : Fin p) (i : Fin (mF n p σW r)), x = Sum.inl ⟨r, i⟩ → sig n p r ≠ σW :=
    fun r i he hw => by have := (pot_le h σW hpar x).2 r i he hw; omega
  have hyn : ∀ (r : Fin p) (i : Fin (mF n p σW r)), y = Sum.inl ⟨r, i⟩ → sig n p r ≠ σW :=
    fun r i he hw => by have := (pot_le h σW hpar y).2 r i he hw; omega
  have hgm : ∀ r, r < p → sig n p r ≠ σW →
      c ≤ mexp n p σW r - (poleF n p σW x r + poleF n p σW y r) := fun r hr hrW => by
    have := pole_bound h σW c hc1 hc2 x y cx cy cs hxle hyle r hr hrW
    omega
  obtain ⟨gm, hgmd⟩ : ∃ gm : ℕ → ℕ,
      gm = fun r => mexp n p σW r - (poleF n p σW x r + poleF n p σW y r) := ⟨_, rfl⟩
  obtain ⟨ex, hexd⟩ : ∃ ex : ℕ → ℕ, ex = fun r => exF n p σW x r + exF n p σW y r := ⟨_, rfl⟩
  obtain ⟨jj, hjjd⟩ : ∃ jj : ℕ, jj = jF n p σW x + jF n p σW y := ⟨_, rfl⟩
  obtain ⟨sgn, hsgn⟩ : ∃ sgn : ZMod (p ^ 2), sgn = (-1) ^ (∑ r ∈ range p, mexp n p σW r) := ⟨_, rfl⟩
  have hmexpW : ∀ r, sig n p r = σW → mexp n p σW r = 0 := by
    intro r hr
    unfold mexp
    rw [if_pos hr]
    have : ¬ ((lam n p - (sig n p r : ℤ)) % 2 ≠ 0) := by rw [hr]; omega
    simp [this]
  have hkey : ∀ r ∈ range p, gm r + e2F n p σW r = mexp n p σW r + ex r := by
    intro r hr
    have hr' := Finset.mem_range.1 hr
    by_cases hw : sig n p r = σW
    · simp [hgmd, hexd, e2F, hw, hmexpW r hw, exF, poleF_W σW x hxn r hw, poleF_W σW y hyn r hw]
    · have h1 := hgm r hr' hw
      have p1 := poleF_le σW x r
      have p2 := poleF_le σW y r
      have hm : mF n p σW r = mu n p r + 1 := by unfold mF; rw [if_neg hw]
      have he2 : e2F n p σW r = 2 * mu n p r + 2 := by unfold e2F gexp; rw [if_neg hw, if_neg hw]
      simp only [hgmd, hexd, exF, if_neg hw]
      omega
  have hgm1 : ∀ m, m < p → m ∉ Wf → 1 ≤ gm m := fun m hm hmW => by
    have : sig n p m ≠ σW := fun e => hmW ((hWf m).2 ⟨hm, e⟩)
    have := hgm m hm this
    rw [hgmd]; simp only; omega
  have hgm2 : c = 2 → ∀ m, m < p → m ∉ Wf → 2 ≤ gm m := fun hc m hm hmW => by
    have : sig n p m ≠ σW := fun e => hmW ((hWf m).2 ⟨hm, e⟩)
    have := hgm m hm this
    rw [hgmd]; simp only; omega
  have hpos : ∀ r ∈ range p, 1 ≤ ex r → 1 ≤ gm r ∧ 1 ≤ ex r := by
    intro r hr hex
    have hr' := Finset.mem_range.1 hr
    refine ⟨?_, hex⟩
    by_cases hw : sig n p r = σW
    · exfalso
      simp [hexd, exF, hw] at hex
    · have := hgm r hr' hw
      rw [hgmd]; simp only; omega
  have hP : Pr (cR p) (range p) gm * Pr (cR p) (range p) (e2F n p σW) =
      Pr (cR p) (range p) (mexp n p σW) * Pr (cR p) (range p) ex := by
    rw [Pr_mul, Pr_mul]
    exact Pr_congr _ _ (fun r hr => hkey r hr)
  have hH : Ht (cR p) (range p) gm ex * Pr (cR p) (range p) (e2F n p σW) =
      Pr (cR p) (range p) (mexp n p σW) * Ht (cR p) (range p) ex ex :=
    Ht_mul (cR p) (range p) gm ex (e2F n p σW) (mexp n p σW) ex (fun r hr => by have := hkey r hr; omega) hpos
  have hV : Vneg p (ExZ n p σW x * ExZ n p σW y) =
      (-Polynomial.X) ^ jj * Pr (cR p) (range p) ex := by
    rw [ExZ_mul, hjjd, hexd]
    exact Vneg_form _ _
  have hQ := Qhat_eq (n := n) (p := p) σW
  rw [← hsgn] at hQ
  have hdeg : jj + ∑ r ∈ range p, mexp n p σW r + 2 ≤ p - 2 := by
    have h1 := sum_mexp_eq h σW hcard hx2
    have h2 := jF_lt σW hx2 x
    have h3 := jF_lt σW hx2 y
    omega
  have hsumgm : ∑ r ∈ range p, gm r ≤ ∑ r ∈ range p, mexp n p σW r :=
    Finset.sum_le_sum fun r _ => by rw [hgmd]; exact Nat.sub_le _ _
  have hdegX : ((-Polynomial.X : Polynomial (ZMod (p ^ 2))) ^ jj).natDegree ≤ jj := by
    refine Polynomial.natDegree_pow_le.trans ?_
    rw [Polynomial.natDegree_neg]
    have := (Polynomial.natDegree_X_le : (Polynomial.X : Polynomial (ZMod (p ^ 2))).natDegree ≤ 1)
    nlinarith
  refine ⟨ExZ n p σW x * ExZ n p σW y,
    Polynomial.C sgn * ((-Polynomial.X) ^ jj * Pr (cR p) (range p) gm),
    Polynomial.C sgn * (Polynomial.C (jj : ZMod (p ^ 2)) * (-Polynomial.X) ^ (jj - 1) *
      Pr (cR p) (range p) gm + (-Polynomial.X) ^ jj * Ht (cR p) (range p) gm ex),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [el_decomp σW μ A Wf hWf x hxn, el_decomp σW μ A Wf hWf y hyn, Polynomial.map_mul]
    ring
  · rw [Epoly_eq, hQ, hV]
    linear_combination (Polynomial.C sgn * (-Polynomial.X) ^ jj) * hP
  · rw [Epoly_eq, hQ, Vneg_deriv, hV]
    have hd1 : Polynomial.derivative ((-Polynomial.X : Polynomial (ZMod (p ^ 2))) ^ jj) =
        Polynomial.C (jj : ZMod (p ^ 2)) * (-Polynomial.X) ^ (jj - 1) * (-1) := by
      rw [Polynomial.derivative_pow]; simp
    rw [Polynomial.derivative_mul, hd1, derivative_Pr]
    linear_combination
      (Polynomial.C sgn * (Polynomial.C (jj : ZMod (p ^ 2)) * (-Polynomial.X) ^ (jj - 1))) * hP +
      (Polynomial.C sgn * (-Polynomial.X) ^ jj) * hH
  · refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
    refine Polynomial.natDegree_mul_le.trans ?_
    have := natDegree_Pr_le (cR p) (range p) gm
    omega
  · refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
    refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
    · refine Polynomial.natDegree_mul_le.trans ?_
      have h1 := natDegree_Pr_le (cR p) (range p) gm
      have h2 : (Polynomial.C (jj : ZMod (p ^ 2)) * (-Polynomial.X) ^ (jj - 1)).natDegree ≤ jj - 1 := by
        refine Polynomial.natDegree_mul_le.trans ?_
        rw [Polynomial.natDegree_C, zero_add]
        refine Polynomial.natDegree_pow_le.trans ?_
        rw [Polynomial.natDegree_neg]
        have := (Polynomial.natDegree_X_le : (Polynomial.X : Polynomial (ZMod (p ^ 2))).natDegree ≤ 1)
        nlinarith
      omega
    · refine Polynomial.natDegree_mul_le.trans ?_
      have h1 := natDegree_Ht_le (cR p) (range p) gm ex
      omega
  · intro m hm hmW
    have hmr : m ∈ range p := Finset.mem_range.2 hm
    simp only [Polynomial.eval_mul, Polynomial.eval_C]
    have := eval_Pr_zero (cR p) (range p) gm hmr (hgm1 m hm hmW)
    simp only [cR] at this
    rw [this]; ring
  · intro hc
    refine ⟨fun m hm hmW => ?_, fun m hm hmW => ?_⟩
    · have hmr : m ∈ range p := Finset.mem_range.2 hm
      have h1 := eval_Pr_zero (cR p) (range p) gm hmr (hgm1 m hm hmW)
      have h2 := eval_derivative_Pr_zero (cR p) (range p) gm hmr (hgm2 hc m hm hmW)
      simp only [cR] at h1 h2
      rw [Polynomial.derivative_mul, Polynomial.derivative_C, zero_mul, zero_add, Polynomial.derivative_mul]
      simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_C, h1, h2]
      ring
    · have hmr : m ∈ range p := Finset.mem_range.2 hm
      have h1 := eval_Pr_zero (cR p) (range p) gm hmr (hgm1 m hm hmW)
      have h2 := eval_Ht_zero (cR p) (range p) gm ex hmr (hgm2 hc m hm hmW)
      simp only [cR] at h1 h2
      simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_C, h1, h2]
      ring

/-- **L2S-21 `pair_Gdata`, class W1.** -/
theorem pair_Gdata_W1 (h : Rng n p) (σW : ℕ) (hpar : (lam n p - (σW : ℤ)) % 2 = 0) (hx2 : 0 < xtwo n p)
    (hcard : ((range p).filter (fun s => sig n p s = σW)).card = tieW n p)
    (μ : ℕ) (A : Polynomial MPT)
    (Wf : Finset ℕ) (hWf : ∀ r, r ∈ Wf ↔ r < p ∧ sig n p r = σW)
    (x y : FIdx n p σW) (c1 : lam n p - 1 ≤ pot2F n p σW x) (c2 : lam n p - 1 ≤ pot2F n p σW y)
    (c3 : 2 * lam n p + 1 ≤ pot2F n p σW x + pot2F n p σW y) :
    ∃ (V : Polynomial ℤ) (G : Polynomial (ZMod (p ^ 2))),
      elF n p σW μ A x * elF n p σW μ A y = (∏ r ∈ Wf, shiftP p μ r A) ^ 2 * V.map zphi ∧
      G * Epoly n p σW = QhatPoly n p σW * Vneg p V ∧ G.natDegree ≤ p - 2 ∧
      ∀ m, m < p → m ∉ Wf → G.eval (m : ZMod (p ^ 2)) = 0 := by
  obtain ⟨V, G, Hr, h1, h2, -, h4, -, h6, -⟩ :=
    pair_Gdata_core h σW hpar hx2 hcard μ A Wf hWf 1 le_rfl (by norm_num) x y c1 c2
      (by push_cast; omega)
  exact ⟨V, G, h1, h2, by omega, h6⟩

/-- **L2S-21 `pair_Gdata`, class W2.** -/
theorem pair_Gdata_W2 (h : Rng n p) (σW : ℕ) (hpar : (lam n p - (σW : ℤ)) % 2 = 0) (hx2 : 0 < xtwo n p)
    (hcard : ((range p).filter (fun s => sig n p s = σW)).card = tieW n p)
    (μ : ℕ) (A : Polynomial MPT)
    (Wf : Finset ℕ) (hWf : ∀ r, r ∈ Wf ↔ r < p ∧ sig n p r = σW)
    (x y : FIdx n p σW) (c1 : lam n p - 1 ≤ pot2F n p σW x) (c2 : lam n p - 1 ≤ pot2F n p σW y)
    (c3 : 2 * lam n p + 3 ≤ pot2F n p σW x + pot2F n p σW y) :
    ∃ (V : Polynomial ℤ) (G Hr : Polynomial (ZMod (p ^ 2))),
      elF n p σW μ A x * elF n p σW μ A y = (∏ r ∈ Wf, shiftP p μ r A) ^ 2 * V.map zphi ∧
      G * Epoly n p σW = QhatPoly n p σW * Vneg p V ∧
      Hr * Epoly n p σW = QhatPoly n p σW * Vneg p (Polynomial.derivative V) ∧
      G.natDegree ≤ p - 4 ∧ Hr.natDegree ≤ p - 2 ∧
      (∀ m, m < p → m ∉ Wf → G.eval (m : ZMod (p ^ 2)) = 0) ∧
      (∀ m, m < p → m ∉ Wf → (Polynomial.derivative G).eval (m : ZMod (p ^ 2)) = 0) ∧
      (∀ m, m < p → m ∉ Wf → Hr.eval (m : ZMod (p ^ 2)) = 0) := by
  obtain ⟨V, G, Hr, h1, h2, h3, h4, h5, h6, h7⟩ :=
    pair_Gdata_core h σW hpar hx2 hcard μ A Wf hWf 2 (by norm_num) le_rfl x y c1 c2
      (by push_cast; omega)
  obtain ⟨h8, h9⟩ := h7 rfl
  exact ⟨V, G, Hr, h1, h2, h3, h4, by omega, h6, h8, h9⟩

/-! ### L2S-22: the entry bound -/

section EntryBound

variable {n p : ℕ} [hp : Fact p.Prime]

lemma mn_nuF_own (σW : ℕ) (r : Fin p) (i : Fin (mF n p σW r)) :
    nuF n p σW (Sum.inl ⟨r, i⟩) r = i := by simp [nuF]

lemma mn_nuF_non (σW : ℕ) (y : FIdx n p σW) (s : ℕ) (hy : ¬ ownAt y s) :
    nuF n p σW y s = mF n p σW s := by
  rcases y with ⟨r, i⟩ | j
  · simp only [ownAt] at hy
    simp [nuF, hy]
  · rfl

lemma mn_mF_W (σW μ : ℕ) (hμ : ∀ r < p, sig n p r = σW → mu n p r = μ) (r : ℕ) (hr : r < p)
    (hw : sig n p r = σW) : mF n p σW r = μ := by
  unfold mF; rw [if_pos hw, hμ r hr hw]; rfl

lemma mn_hKn (h : Rng n p) (σW s0 : ℕ) (hs0 : s0 < p) (hsW : sig n p s0 = σW) (s : ℕ) (hs : s < p)
    (hsg : sig n p s = σW) :
    s ∉ Kset n p σW ∧ ∀ l, 1 ≤ l → l ≤ Lc n p s0 → (s + l * p) ∈ Kset n p σW ∧
      NodeData2 p n (sigN n p) (clN n p) (tauU n p s0) (tauV n p s0) (s + l * p) := by
  have hpp := h.p5
  refine ⟨fun hk => ?_, fun l h1 hl => ?_⟩
  · have := ((mn_mem_Kset σW s).1 hk).2.1
    rw [Nat.div_eq_of_lt hs] at this
    omega
  · have hLs : Lc n p s = Lc n p s0 := by
      rw [mn_Lc_eq, mn_Lc_eq, (mn_flags_of_sig (n := n) (p := p) (s := s) (s' := s0)
        (by rw [hsg, hsW])).1]
    obtain ⟨b1, b2⟩ := mn_Lc_bound h s hs
    have hk6 : s + l * p ≤ 6 * n := by
      have : l * p ≤ Lc n p s0 * p := Nat.mul_le_mul_right p hl
      rw [hLs] at b1
      omega
    have hmem : (s + l * p) ∈ Kset n p σW := by
      rw [mn_mem_Kset]
      refine ⟨hk6, ?_, ?_⟩
      · rw [Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hs]; omega
      · rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hs]; exact hsg
    exact ⟨hmem, mn_nodeData h σW s0 hs0 hsW _ hmem⟩

lemma mn_tauU_mem (n s0 : ℕ) : ∀ l, tauU n p s0 l ∈ LocRing p := by
  intro l; unfold tauU; split_ifs with hl
  · exact (LocRing p).mul_mem (by exact_mod_cast int_mem_locRing (ℓ := p) _) (uL_mem l hl)
  · exact (LocRing p).zero_mem

lemma mn_tauV_mem (n s0 : ℕ) (h8 : 8 * n < p ^ 2) : ∀ l, tauV n p s0 l ∈ LocRing p := by
  intro l; unfold tauV; split_ifs with hl
  · exact (LocRing p).mul_mem (by exact_mod_cast int_mem_locRing (ℓ := p) _)
      (vL_mem n (s0 + l * p) l h8 hl.2 hl.1)
  · exact (LocRing p).zero_mem

lemma mn_elF_inl (σW μ : ℕ) (A : Polynomial MPT) (r : Fin p) (i : Fin (mF n p σW r)) :
    elF n p σW μ A (Sum.inl ⟨r, i⟩) =
      sX r ^ (i : ℕ) * ∏ r' ∈ Finset.univ.erase r, qF n p σW μ A r' := by
  simp only [elF, famFun, Sum.elim_inl]
  rw [sX_eq_sub]

lemma mn_qF_pint (σW μ : ℕ) {A : Polynomial MPT} (hA : PInt p A) (r : Fin p) :
    PInt p (qF n p σW μ A r) := by
  unfold qF
  split_ifs
  · exact PInt_shiftP μ _ hA
  · exact (PInt_sX _).pow _

lemma mn_elF_P (σW μ : ℕ) {A : Polynomial MPT} (hA : PInt p A) (x : FIdx n p σW) (r : Fin p)
    (hr : sig n p r = σW) (hx : ¬ ownAt x r) :
    ∃ R, PInt p R ∧ elF n p σW μ A x = shiftP p μ r A * R := by
  classical
  rcases x with ⟨r0, i⟩ | j
  · simp only [ownAt] at hx
    have hne : r0 ≠ r := fun e => hx (by rw [e])
    rw [mn_elF_inl]
    have hmem : r ∈ Finset.univ.erase r0 := Finset.mem_erase.2 ⟨fun e => hne e.symm, Finset.mem_univ r⟩
    refine ⟨sX r0 ^ (i : ℕ) * ∏ r' ∈ (Finset.univ.erase r0).erase r, qF n p σW μ A r', ?_, ?_⟩
    · exact ((PInt_sX _).pow _).mul (PInt.prod fun r' _ => mn_qF_pint σW μ hA r')
    · rw [← Finset.mul_prod_erase (Finset.univ.erase r0) _ hmem]
      have : qF n p σW μ A r = shiftP p μ r A := by unfold qF; rw [if_pos hr]
      rw [this]; ring
  · simp only [elF, famFun, Sum.elim_inr]
    refine ⟨Polynomial.X ^ (j : ℕ) * ∏ r' ∈ Finset.univ.erase r, qF n p σW μ A r', ?_, ?_⟩
    · exact (PInt_X.pow _).mul (PInt.prod fun r' _ => mn_qF_pint σW μ hA r')
    · rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ r)]
      have : qF n p σW μ A r = shiftP p μ r A := by unfold qF; rw [if_pos hr]
      rw [this]; ring

lemma mn_own_split (σW μ : ℕ) {A : Polynomial MPT} (hA : PInt p A) (r : Fin p)
    (i : Fin (mF n p σW r)) (hr : sig n p r = σW) (y : FIdx n p σW) (hy : ¬ ownAt y r) :
    ∃ R, PInt p R ∧ elF n p σW μ A (Sum.inl ⟨r, i⟩) * elF n p σW μ A y =
      sX r ^ (i : ℕ) * shiftP p μ r A * R := by
  obtain ⟨Ry, hRy, hy'⟩ := mn_elF_P σW μ hA y r hr hy
  refine ⟨(∏ r' ∈ Finset.univ.erase r, qF n p σW μ A r') * Ry,
    (PInt.prod fun r' _ => mn_qF_pint σW μ hA r').mul hRy, ?_⟩
  rw [mn_elF_inl, hy']
  ring

lemma mn_node_ok (h : Rng n p) (σW : ℕ) (hpar : (lam n p - (σW : ℤ)) % 2 = 0)
    (s0 : ℕ) (hs0 : s0 < p) (hsW : sig n p s0 = σW) (μ : ℕ)
    (hμ : ∀ r < p, sig n p r = σW → mu n p r = μ) (x y : FIdx n p σW) (s : ℕ) (hs : s < p)
    (l : ℕ) (hl : l ≤ Lc n p s) (hd : defF n p σW x y s ≤ 0) :
    GV p ((pot2F n p σW x + pot2F n p σW y + 1) / 2)
      (nodeT (p := p) n (Kset n p σW) (sigN n p) (clN n p) (tauU n p s0) (tauV n p s0) (s + l * p)
        (elF n p σW μ (orthA (cLoc (Lc n p s0)) μ) x * elF n p σW μ (orthA (cLoc (Lc n p s0)) μ) y)) := by
  have hpp := h.p5
  have hAP : PInt p (orthA (cLoc (Lc n p s0)) μ) := orthA_pint _ _ (fun i => GV_cLoc _ i)
  have hAd : (orthA (cLoc (Lc n p s0)) μ).natDegree ≤ μ := orthA_natDegree_le _ _
  obtain ⟨b1, b2⟩ := mn_Lc_bound h s hs
  have hk6 : s + l * p ≤ 6 * n := by
    have : l * p ≤ Lc n p s * p := Nat.mul_le_mul_right p hl
    omega
  have hkm : (s + l * p) % p = s := by
    rw [Nat.add_mul_mod_self_right]; exact Nat.mod_eq_of_lt hs
  have hj := (fam_jets σW μ hμ hAP hAd x (s + l * p)).mul (fam_jets σW μ hμ hAP hAd y (s + l * p))
  rw [hkm] at hj
  have hnp := mn_node_pass h σW s0 hs0 hsW (s + l * p) hk6 _ _ hj
  rw [hkm] at hnp
  refine hnp.mono ?_
  unfold defF at hd
  omega

end EntryBound


/-- **L2S-22 `entry_bound`.** -/
theorem entry_bound (h : Rng n p) (σW : ℕ) (hpar : (lam n p - (σW : ℤ)) % 2 = 0) (hx2 : 0 < xtwo n p)
    (hcard : ((range p).filter (fun s => sig n p s = σW)).card = tieW n p)
    (s0 : ℕ) (hs0 : s0 < p) (hsW : sig n p s0 = σW) (μ : ℕ)
    (hμ : ∀ r < p, sig n p r = σW → mu n p r = μ) (x y : FIdx n p σW) :
    GV p ((pot2F n p σW x + pot2F n p σW y + 1) / 2)
      (laiLTx (p := p) n (Kset n p σW) (sigN n p) (clN n p) (tauU n p s0) (tauV n p s0)
        (elF n p σW μ (orthA (cLoc (Lc n p s0)) μ) x * elF n p σW μ (orthA (cLoc (Lc n p s0)) μ) y)) := by
  classical
  have hpp := h.p5
  have hp3 : 3 ≤ p := by omega
  have h8 := h.h8
  obtain ⟨L, hLeq⟩ : ∃ L, L = Lc n p s0 := ⟨_, rfl⟩
  obtain ⟨A, hAeq⟩ : ∃ A, A = orthA (cLoc L) μ := ⟨_, rfl⟩
  rw [← hLeq, ← hAeq]
  have hAP : PInt p A := by rw [hAeq]; exact orthA_pint _ _ (fun i => GV_cLoc _ i)
  have hAd : A.natDegree ≤ μ := by rw [hAeq]; exact orthA_natDegree_le _ _
  obtain ⟨Wf, hWf⟩ : ∃ Wf : Finset ℕ, ∀ r, r ∈ Wf ↔ r < p ∧ sig n p r = σW :=
    ⟨(range p).filter (fun r => sig n p r = σW), fun r => by simp [Finset.mem_filter, Finset.mem_range]⟩
  have hWfe : (range p).filter (fun r => sig n p r = σW) = Wf := by
    ext r; simp only [Finset.mem_filter, Finset.mem_range]; exact (hWf r).symm
  have hLW : ∀ s ∈ Wf, Lc n p s = L := by
    intro s hs
    obtain ⟨hs1, hs2⟩ := (hWf s).1 hs
    rw [hLeq, mn_Lc_eq, mn_Lc_eq, (mn_flags_of_sig (n := n) (p := p) (s := s) (s' := s0)
      (by rw [hs2, hsW])).1]
  have hLb : ∀ s ∈ Wf, s + L * p ≤ 6 * n ∧ 6 * n < s + (L + 1) * p := by
    intro s hs
    rw [← hLW s hs]
    exact mn_Lc_bound h s ((hWf s).1 hs).1
  have hKn : ∀ s ∈ Wf, s ∉ Kset n p σW ∧ ∀ l, 1 ≤ l → l ≤ L → (s + l * p) ∈ Kset n p σW ∧
      NodeData2 p n (sigN n p) (clN n p) (tauU n p s0) (tauV n p s0) (s + l * p) := by
    intro s hs
    rw [hLeq]
    exact mn_hKn h σW s0 hs0 hsW s ((hWf s).1 hs).1 ((hWf s).1 hs).2
  have hμW : ∀ r ∈ Wf, mu n p r = μ := fun r hr => hμ r ((hWf r).1 hr).1 ((hWf r).1 hr).2
  have hs0Wf : s0 ∈ Wf := (hWf s0).2 ⟨hs0, hsW⟩
  have hres := resfacts h σW hpar s0 hs0
  have h2mu : 2 * (μ : ℤ) + σW = lam n p + 4 := by
    have := hres.2 hsW
    rw [hμ s0 hs0 hsW, hsW] at this
    exact this
  have hK6 : Kset n p σW ⊆ range (6 * n + 1) := Finset.filter_subset _ _
  rw [mn_laiLTx_res h _ hK6]
  have hnodeok : ∀ (x y : FIdx n p σW) (s : ℕ), s < p → defF n p σW x y s ≤ 0 → ∀ l ≤ Lc n p s,
      GV p ((pot2F n p σW x + pot2F n p σW y + 1) / 2)
        (nodeT (p := p) n (Kset n p σW) (sigN n p) (clN n p) (tauU n p s0) (tauV n p s0) (s + l * p)
          (elF n p σW μ A x * elF n p σW μ A y)) := by
    intro x y s hs hd l hl
    have := mn_node_ok h σW hpar s0 hs0 hsW μ hμ x y s hs l hl hd
    rw [← hLeq, ← hAeq] at this
    exact this
  have hTok : ∀ (x y : FIdx n p σW) (s : ℕ), s < p → defF n p σW x y s ≤ 0 →
      GV p ((pot2F n p σW x + pot2F n p σW y + 1) / 2)
        (∑ l ∈ range (Lc n p s + 1), nodeT (p := p) n (Kset n p σW) (sigN n p) (clN n p)
          (tauU n p s0) (tauV n p s0) (s + l * p) (elF n p σW μ A x * elF n p σW μ A y)) :=
    fun x y s hs hd => GV.sum fun l hl => hnodeok x y s hs hd l (by have := Finset.mem_range.1 hl; omega)
  -- the own case, for the pair `(x, y)`
  have caseB : ∀ (x y : FIdx n p σW) (r : Fin p) (i : Fin (mF n p σW r)), x = Sum.inl ⟨r, i⟩ →
      sig n p r = σW → ¬ ownAt y r → defF n p σW x y r ≤ 1 →
      (∀ s < p, s ≠ (r : ℕ) → defF n p σW x y s ≤ 0) →
      (∀ s < p, sig n p s ≠ σW → defF n p σW x y s ≤ 0) →
      GV p ((pot2F n p σW x + pot2F n p σW y + 1) / 2)
        (∑ s ∈ range p, ∑ l ∈ range (Lc n p s + 1), nodeT (p := p) n (Kset n p σW) (sigN n p) (clN n p)
          (tauU n p s0) (tauV n p s0) (s + l * p) (elF n p σW μ A x * elF n p σW μ A y)) := by
    intro x y r i hxe hrW hnown hdr hdo hoff
    rw [← Finset.sum_filter_add_sum_filter_not (range p) (fun s => sig n p s = σW)]
    refine GV.add ?_ (GV.sum fun s hs => hTok x y s (Finset.mem_range.1 (Finset.mem_filter.1 hs).1)
      (hoff s (Finset.mem_range.1 (Finset.mem_filter.1 hs).1) (Finset.mem_filter.1 hs).2))
    rw [hWfe]
    have hrWf : (r : ℕ) ∈ Wf := (hWf r).2 ⟨r.2, hrW⟩
    rw [← Finset.add_sum_erase Wf _ hrWf]
    refine GV.add ?_ (GV.sum fun s hs => hTok x y s ((hWf s).1 (Finset.mem_of_mem_erase hs)).1
      (hdo s ((hWf s).1 (Finset.mem_of_mem_erase hs)).1 (Finset.ne_of_mem_erase hs)))
    obtain ⟨R, hR, hF⟩ := mn_own_split σW μ hAP r i hrW y hnown
    rw [← hxe] at hF
    have hi : (i : ℕ) < μ := by
      have := i.2
      have hm := mn_mF_W σW μ hμ r r.2 hrW
      omega
    obtain ⟨hKr0, hKr⟩ := hKn r hrWf
    have hb := mn_Lc_bound h r r.2
    rw [hLW r hrWf] at hb
    have key := own_pair n (Kset n p σW) (sigN n p) (clN n p) (tauU n p s0) (tauV n p s0) h8 hp3 r r.2 L
      hb.1 hb.2 hKr hKr0 μ i hi R hR
    rw [← hAeq] at key
    have e : ∑ l ∈ range (Lc n p r + 1), nodeT (p := p) n (Kset n p σW) (sigN n p) (clN n p)
        (tauU n p s0) (tauV n p s0) (r + l * p) (elF n p σW μ A x * elF n p σW μ A y) =
        ∑ l ∈ range (L + 1), nodeT (p := p) n (Kset n p σW) (sigN n p) (clN n p)
          (tauU n p s0) (tauV n p s0) (r + l * p) (sX r ^ (i : ℕ) * shiftP p μ r A * R) := by
      rw [hLW r hrWf, hF]
    rw [e]
    refine key.mono ?_
    have hd1 := hdr
    unfold defF at hd1
    have e1 : nuF n p σW x r = (i : ℕ) := by rw [hxe]; exact mn_nuF_own σW r i
    have e2 : nuF n p σW y r = μ := by rw [mn_nuF_non σW y r hnown, mn_mF_W σW μ hμ r r.2 hrW]
    omega
  rcases pair_classify h σW hpar x y with hA
    | ⟨r, i, hxe, hrW, hyp, hnown, hdr, hdo⟩ | ⟨r, i, hye, hrW, hxp, hnown, hdr, hdo⟩
    | ⟨c1, c2, c3, c4, hoff, hon⟩ | ⟨c1, c2, c3, hoff, hon⟩
  · rw [← Finset.sum_filter_add_sum_filter_not (range p) (fun s => sig n p s = σW)]
    exact (GV.sum fun s hs => hTok x y s (Finset.mem_range.1 (Finset.mem_filter.1 hs).1)
        (hA s (Finset.mem_range.1 (Finset.mem_filter.1 hs).1))).add
      (GV.sum fun s hs => hTok x y s (Finset.mem_range.1 (Finset.mem_filter.1 hs).1)
        (hA s (Finset.mem_range.1 (Finset.mem_filter.1 hs).1)))
  · refine caseB x y r i hxe hrW hnown hdr hdo (fun s hs hsW' => hdo s hs ?_)
    intro e
    apply hsW'
    rw [e]; exact hrW
  · have := caseB y x r i hye hrW hnown (by
      have hh := hdr
      unfold defF at hh ⊢
      omega) (fun s hs hne => by
        have hh := hdo s hs hne
        unfold defF at hh ⊢
        omega) (fun s hs hsW' => by
        have hh := hdo s hs (fun e => hsW' (by rw [e]; exact hrW))
        unfold defF at hh ⊢
        omega)
    simp only [mul_comm (elF n p σW μ A y), add_comm (pot2F n p σW y)] at this
    exact this
  · rw [← Finset.sum_filter_add_sum_filter_not (range p) (fun s => sig n p s = σW)]
    refine GV.add ?_ (GV.sum fun s hs => hTok x y s (Finset.mem_range.1 (Finset.mem_filter.1 hs).1)
      (hoff s (Finset.mem_range.1 (Finset.mem_filter.1 hs).1) (Finset.mem_filter.1 hs).2))
    rw [hWfe]
    obtain ⟨V, G, h1, h2, h3, h4⟩ := pair_Gdata_W1 h σW hpar hx2 hcard μ A Wf hWf x y c1 c2 (by omega)
    obtain ⟨Kz, -, hKz⟩ := lemmaR_p2 h σW hpar
    have key := wsum_first h σW Wf hWf μ hμW L (Kset n p σW) (sigN n p) (clN n p) (tauU n p s0)
      (tauV n p s0) (mn_tauU_mem n s0) hLb hKn A hAP hAd V G h2 h3 h4 Kz
      (fun s hs => hKz s ((hWf s).1 hs).1 ((hWf s).1 hs).2)
    have e : ∑ s ∈ Wf, ∑ l ∈ range (Lc n p s + 1), nodeT (p := p) n (Kset n p σW) (sigN n p) (clN n p)
        (tauU n p s0) (tauV n p s0) (s + l * p) (elF n p σW μ A x * elF n p σW μ A y) =
        ∑ s ∈ Wf, ∑ l ∈ range (L + 1), nodeT (p := p) n (Kset n p σW) (sigN n p) (clN n p)
          (tauU n p s0) (tauV n p s0) (s + l * p) ((∏ r ∈ Wf, shiftP p μ r A) ^ 2 * V.map zphi) := by
      refine Finset.sum_congr rfl fun s hs => ?_
      rw [hLW s hs, h1]
    rw [e]
    refine key.mono ?_
    omega
  · rw [← Finset.sum_filter_add_sum_filter_not (range p) (fun s => sig n p s = σW)]
    refine GV.add ?_ (GV.sum fun s hs => hTok x y s (Finset.mem_range.1 (Finset.mem_filter.1 hs).1)
      (hoff s (Finset.mem_range.1 (Finset.mem_filter.1 hs).1) (Finset.mem_filter.1 hs).2))
    rw [hWfe]
    obtain ⟨V, G, Hr, h1, h2, h3, h4, h5, h6, h7, h8'⟩ :=
      pair_Gdata_W2 h σW hpar hx2 hcard μ A Wf hWf x y c1 c2 c3
    obtain ⟨Kz, -, hKz⟩ := lemmaR_p2 h σW hpar
    have key := wsum_second h hx2 σW Wf hWf ⟨s0, hs0Wf⟩ μ hμW L (Kset n p σW) (sigN n p) (clN n p)
      (tauU n p s0) (tauV n p s0) (mn_tauU_mem n s0) hLb hKn A hAP hAd V G Hr h2 h3 h4 h5 h6 h7 h8' Kz
      (fun s hs => hKz s ((hWf s).1 hs).1 ((hWf s).1 hs).2)
    have e : ∑ s ∈ Wf, ∑ l ∈ range (Lc n p s + 1), nodeT (p := p) n (Kset n p σW) (sigN n p) (clN n p)
        (tauU n p s0) (tauV n p s0) (s + l * p) (elF n p σW μ A x * elF n p σW μ A y) =
        ∑ s ∈ Wf, ∑ l ∈ range (L + 1), nodeT (p := p) n (Kset n p σW) (sigN n p) (clN n p)
          (tauU n p s0) (tauV n p s0) (s + l * p) ((∏ r ∈ Wf, shiftP p μ r A) ^ 2 * V.map zphi) := by
      refine Finset.sum_congr rfl fun s hs => ?_
      rw [hLW s hs, h1]
    rw [e]
    refine key.mono ?_
    have hxle := (pot_le h σW hpar x).1
    have hyle := (pot_le h σW hpar y).1
    omega

end Window

/-! ### L2S-25: Theorem L2 -/

section L2Main

variable {n p : ℕ} [hp : Fact p.Prime]

open Classical in
lemma mn_sum_mF (σW : ℕ) (hcard : ((range p).filter (fun s => sig n p s = σW)).card = tieW n p) :
    ∑ r : Fin p, mF n p σW r = ∑ r : Fin p, mu n p r + (p - tieW n p) := by
  unfold mF
  rw [Finset.sum_add_distrib]
  congr 1
  rw [Fin.sum_univ_eq_sum_range (fun r => if sig n p r = σW then 0 else 1) p]
  have h1 := Finset.card_filter_add_card_filter_not (s := range p) (fun s => sig n p s = σW)
  simp only [Finset.card_range] at h1
  have : ∑ r ∈ range p, (if sig n p r = σW then 0 else 1) =
      ((range p).filter (fun s => ¬ sig n p s = σW)).card := by
    rw [Finset.card_filter]
    exact Finset.sum_congr rfl fun r _ => by split_ifs <;> rfl
  rw [this]; omega

lemma mn_res_inj (p : ℕ) [Fact p.Prime] :
    Function.Injective fun r : Fin p => (((-((r : ℕ) : ℤ) : ℤ) : ZMod p)) := by
  intro r r' h
  have h' : ((r : ℕ) : ZMod p) = ((r' : ℕ) : ZMod p) := by
    have := neg_injective (show -((r : ℕ) : ZMod p) = -((r' : ℕ) : ZMod p) by simpa using h)
    exact this
  have h3 := (ZMod.natCast_eq_natCast_iff _ _ _).1 h'
  have := Nat.ModEq.eq_of_lt_of_lt h3 r.2 r'.2
  exact Fin.ext this

open Classical in
/-- **L2S-25 `lai_L2` (LC21): Theorem L2.**  For every prime `√(8n) < p < 3n`,
`v_p(J_n) ≥ LaiExact(n, p) + x₁ + x₂`. -/
theorem lai_L2 (h : Rng n p) :
    GV p (∑ x, pot2 n p x - nuP n p + xone n p + xtwo n p) (laiJ n) := by
  have hx1nn : 0 ≤ xone n p := by unfold xone; exact le_max_left _ _
  have hx2nn : 0 ≤ xtwo n p := by unfold xtwo; exact le_max_left _ _
  by_cases hx2 : 0 < xtwo n p
  swap
  · have h0 : xtwo n p = 0 := by omega
    have := lai_L1 h
    have e : ((xone n p).toNat : ℤ) = xone n p := by omega
    rw [h0, add_zero, ← e]
    exact this
  have hpp := h.p5
  have hp3 : 3 ≤ p := by omega
  have h8 := h.h8
  obtain ⟨σZ, σW, hne, hiff, hcZ, hcW⟩ := tie_split h
  have hcard := hcW
  obtain ⟨hlam, h2d, hx1, h2x⟩ := law_second_level h hx2
  have hsum := tie_sum h
  have hxt : xtwo n p = xone n p - Ncnt n p := by unfold xtwo at *; omega
  have hWpos : 0 < tieW n p := by omega
  obtain ⟨s0, hs0mem⟩ := Finset.card_pos.1 (by rw [hcW]; exact hWpos)
  have hs0 : s0 < p := Finset.mem_range.1 (Finset.mem_filter.1 hs0mem).1
  have hsW : sig n p s0 = σW := (Finset.mem_filter.1 hs0mem).2
  have hpar : (lam n p - (σW : ℤ)) % 2 = 0 := by
    have := ((hiff s0 hs0).2 (Or.inr hsW))
    unfold tieR at this
    rw [hsW] at this
    exact this
  obtain ⟨μ, hμd⟩ : ∃ μ, μ = mu n p s0 := ⟨_, rfl⟩
  have hμ : ∀ r < p, sig n p r = σW → mu n p r = μ := by
    intro r hr hrW
    have a1 := (resfacts h σW hpar r hr).2 hrW
    have a2 := (resfacts h σW hpar s0 hs0).2 hsW
    rw [hrW] at a1; rw [hsW] at a2
    omega
  have hμ2 : μ + 1 ≤ 2 * Lc n p s0 := by
    have := (lemmaS h).2.2.2 s0 hs0 (by rw [hsW]; exact hpar)
    omega
  have hLp : Lc n p s0 < p := by
    have : Lc n p s0 ≤ q6 n p := by unfold Lc; split_ifs <;> omega
    have h6 := mn_div_lt h (show 6 * n ≤ 6 * n from le_rfl)
    exact lt_of_le_of_lt this h6
  -- the data of the window theorem
  have hτu := mn_tauU_mem (p := p) n s0
  have hτv := mn_tauV_mem (p := p) n s0 h8
  have hdcnt : (dcnt n p : ℤ) = xtwo n p + Ncnt n p + tieZ n p := by omega
  have hN : ∑ r : Fin p, mF n p σW r + (xtwo n p).toNat = 3 * n := by
    have h1 := hsum_mu (n := n) (p := p) h
    have h2 := mn_sum_mF (n := n) (p := p) σW hcard
    have : ((xtwo n p).toNat : ℤ) = xtwo n p := by omega
    omega
  have hcardF : Fintype.card (FIdx n p σW) = 3 * n := by
    simp only [FIdx, Fintype.card_sum, Fintype.card_sigma, Fintype.card_fin]
    exact hN
  have e : (FIdx n p σW) ≃ Fin (3 * n) := Fintype.equivFinOfCardEq hcardF
  have hG : GV p (∑ x : FIdx n p σW, pot2F n p σW x)
      (Matrix.of fun x y : FIdx n p σW =>
        laiLTx (p := p) n (Kset n p σW) (sigN n p) (clN n p) (tauU n p s0) (tauV n p s0)
          (elF n p σW μ (orthA (cLoc (Lc n p s0)) μ) x * elF n p σW μ (orthA (cLoc (Lc n p s0)) μ) y)).det :=
    det_bound _ (pot2F n p σW) fun x y =>
      entry_bound h σW hpar hx2 hcard s0 hs0 hsW μ hμ x y
  have key := GV_laiJ_of_window (p := p) (S := Fin p) n (Kset n p σW) (sigN n p) (clN n p) (tauU n p s0)
    (tauV n p s0) hτu hτv (Lc n p s0) μ hLp (by omega) (fun r : Fin p => (r : ℕ)) (mn_res_inj p)
    (fun r : Fin p => sig n p r = σW) (fun r : Fin p => mF n p σW r)
    (fun r hr => mn_mF_W σW μ hμ r r.2 hr)
    (qF n p σW μ (orthA (cLoc (Lc n p s0)) μ))
    (fun r hr => by unfold qF; rw [if_pos hr])
    (fun r hr => by unfold qF; rw [if_neg hr])
    (xtwo n p).toNat hN e _ hG
  have hps := pot_sum h σW hpar hcard hx2
  rw [hps] at key
  refine key.mono (le_of_eq ?_)
  ring

end L2Main


end CatalanCore.Lai

#print axioms CatalanCore.Lai.pot_sum
#print axioms CatalanCore.Lai.det_bound
#print axioms CatalanCore.Lai.pair_classify
#print axioms CatalanCore.Lai.fam_jets
#print axioms CatalanCore.Lai.pair_Gdata_W1
#print axioms CatalanCore.Lai.pair_Gdata_W2
#print axioms CatalanCore.Lai.entry_bound
#print axioms CatalanCore.Lai.lai_L2
