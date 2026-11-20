module

public import CatalanCore.Lai.B83Weighted

@[expose] public section

/-!
# `CatalanCore.Lai.B83Cross`: the cross-residue entries of the integral block (ledger LB06)

Note `N9-LAI-SMALLPRIME-NV-2026-11-20.md` §3.4 ("Cross-residue entries vanish at threshold").
Band `8n/3 < p < 3n - 1`, classes `A = [0, A₂]` (multiplicity 4), `C = (A₂, a)` (multiplicity 3),
window `D = [a, p)`.  For two elements `e_{r,i}`, `e_{r',i'}` of the E2 basis at **different** residues
`r ≠ r'` of `A ∪ C`, with `thr = ⌈(2π_x + 2π_y)/2⌉`, the Gram entry of `L_n` at every integral point
`(a, b, X)` (`a, b ∈ ℤ_(p)`, `v(X) ≥ -3`) has `v ≥ thr + 1`: the reduction of `p^{-thr}·entry` is `0`.
These are the zero off-diagonal blocks of `intBlock` (`B83Blocks`).

* `pair_Gdata_cross`: the polynomials `V, G, H` of a window pair under the pole condition
  `poleF x r + poleF y r + c ≤ mexp r` (a variant of `pair_Gdata_core` for cross pairs);
* `cross_entry`: strict-slack off the window, and on the window either strict slack or the first/second
  order window sums (`wsum_first`, `wsum_second`, i.e. (M1) and (M2)) give `GV (thr + 1)`;
* `lb06_band`, `lb06_point`: the band statement, as a bound on `entB` and on the entry at a point.
-/

open Finset Polynomial CatalanCore.Basic CatalanCore.Content CatalanCore.Arith.Hybrid

namespace CatalanCore.Lai

noncomputable section

/-! ### Part 1: pair data for cross pairs -/

section PairData

open MvPolynomial

variable {n p : ℕ} [hp : Fact p.Prime]

/-- **Pair data for a cross-residue pair** (variant of `pair_Gdata_core`): the pole condition
`poleF x r + poleF y r + c ≤ mexp r` off the window is taken as a hypothesis (`hpb`) in place of the
potential bounds `cx, cy, cs`, which are only used to derive it for same-residue pairs. -/
theorem pair_Gdata_cross (h : Rng n p) (σW : ℕ) (hpar : (lam n p - (σW : ℤ)) % 2 = 0)
    (hx2 : 0 < xtwo n p)
    (hcard : ((range p).filter (fun s => sig n p s = σW)).card = tieW n p)
    (μ : ℕ) (A : Polynomial MPT) (Wf : Finset ℕ) (hWf : ∀ r, r ∈ Wf ↔ r < p ∧ sig n p r = σW)
    (c : ℕ) (hc1 : 1 ≤ c) (hc2 : c ≤ 2) (x y : FIdx n p σW)
    (hxn : ∀ (r : Fin p) (i : Fin (mF n p σW r)), x = Sum.inl ⟨r, i⟩ → sig n p r ≠ σW)
    (hyn : ∀ (r : Fin p) (i : Fin (mF n p σW r)), y = Sum.inl ⟨r, i⟩ → sig n p r ≠ σW)
    (hpb : ∀ r, r < p → sig n p r ≠ σW → poleF n p σW x r + poleF n p σW y r + c ≤ mexp n p σW r) :
    ∃ (V : Polynomial ℤ) (G Hr : Polynomial (ZMod (p ^ 2))),
      elF n p σW μ A x * elF n p σW μ A y = (∏ r ∈ Wf, shiftP p μ r A) ^ 2 * V.map zphi ∧
      G * Epoly n p σW = QhatPoly n p σW * Vneg p V ∧
      Hr * Epoly n p σW = QhatPoly n p σW * Vneg p (Polynomial.derivative V) ∧
      G.natDegree ≤ p - 4 ∧ Hr.natDegree ≤ p - 4 ∧
      (∀ m, m < p → m ∉ Wf → G.eval (m : ZMod (p ^ 2)) = 0) ∧
      (c = 2 → (∀ m, m < p → m ∉ Wf → (Polynomial.derivative G).eval (m : ZMod (p ^ 2)) = 0) ∧
        (∀ m, m < p → m ∉ Wf → Hr.eval (m : ZMod (p ^ 2)) = 0)) := by
  classical
  have hgm : ∀ r, r < p → sig n p r ≠ σW →
      c ≤ mexp n p σW r - (poleF n p σW x r + poleF n p σW y r) := fun r hr hrW => by
    have := hpb r hr hrW
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


end PairData

/-! ### Part 2: the strict entry bound -/

section CrossEntry

variable {n p : ℕ} [hp : Fact p.Prime]

/-- A node with strict slack (`defF ≤ -1`) is above the threshold by one. -/
lemma cross_node_ok (h : Rng n p) (σW : ℕ) (s0 : ℕ) (hs0 : s0 < p) (hsW : sig n p s0 = σW) (μ : ℕ)
    (hμ : ∀ r < p, sig n p r = σW → mu n p r = μ) (x y : FIdx n p σW) (s : ℕ) (hs : s < p)
    (l : ℕ) (hl : l ≤ Lc n p s) (hd : defF n p σW x y s ≤ -1) :
    GV p ((pot2F n p σW x + pot2F n p σW y + 1) / 2 + 1)
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

/-- **The strict entry bound for a cross pair.**  `x`, `y` are elements of non-window residues.
Off the window every node has `defF ≤ -1` (`hoff`); on the window either every node has strict slack,
or (M1) the first-order window sum applies (`pole` condition with `c = 1`, and `thr + 1 ≤ σ_W + 2μ - 3`),
or (M2) the second-order one (`c = 2`, `thr + 1 ≤ σ_W + 2μ - 2`).  Then `GV (thr + 1)`. -/
theorem cross_entry (h : Rng n p) (σW : ℕ) (hpar : (lam n p - (σW : ℤ)) % 2 = 0) (hx2 : 0 < xtwo n p)
    (hcard : ((range p).filter (fun s => sig n p s = σW)).card = tieW n p)
    (s0 : ℕ) (hs0 : s0 < p) (hsW : sig n p s0 = σW) (μ : ℕ)
    (hμ : ∀ r < p, sig n p r = σW → mu n p r = μ) (x y : FIdx n p σW)
    (hxn : ∀ (r : Fin p) (i : Fin (mF n p σW r)), x = Sum.inl ⟨r, i⟩ → sig n p r ≠ σW)
    (hyn : ∀ (r : Fin p) (i : Fin (mF n p σW r)), y = Sum.inl ⟨r, i⟩ → sig n p r ≠ σW)
    (hoff : ∀ s < p, sig n p s ≠ σW → defF n p σW x y s ≤ -1)
    (hwin : (∀ s < p, sig n p s = σW → defF n p σW x y s ≤ -1) ∨
      ((∀ r, r < p → sig n p r ≠ σW →
          poleF n p σW x r + poleF n p σW y r + 1 ≤ mexp n p σW r) ∧
        (pot2F n p σW x + pot2F n p σW y + 1) / 2 + 1 ≤ (σW : ℤ) + 2 * μ - 3) ∨
      ((∀ r, r < p → sig n p r ≠ σW →
          poleF n p σW x r + poleF n p σW y r + 2 ≤ mexp n p σW r) ∧
        (pot2F n p σW x + pot2F n p σW y + 1) / 2 + 1 ≤ (σW : ℤ) + 2 * μ - 2)) :
    GV p ((pot2F n p σW x + pot2F n p σW y + 1) / 2 + 1)
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
  have hK6 : Kset n p σW ⊆ range (6 * n + 1) := Finset.filter_subset _ _
  rw [mn_laiLTx_res h _ hK6]
  have hTok : ∀ (s : ℕ), s < p → defF n p σW x y s ≤ -1 →
      GV p ((pot2F n p σW x + pot2F n p σW y + 1) / 2 + 1)
        (∑ l ∈ range (Lc n p s + 1), nodeT (p := p) n (Kset n p σW) (sigN n p) (clN n p)
          (tauU n p s0) (tauV n p s0) (s + l * p) (elF n p σW μ A x * elF n p σW μ A y)) := by
    intro s hs hd
    refine GV.sum fun l hl => ?_
    have := cross_node_ok h σW s0 hs0 hsW μ hμ x y s hs l
      (by have := Finset.mem_range.1 hl; omega) hd
    rw [← hLeq, ← hAeq] at this
    exact this
  rw [← Finset.sum_filter_add_sum_filter_not (range p) (fun s => sig n p s = σW)]
  refine GV.add ?_ (GV.sum fun s hs => hTok s (Finset.mem_range.1 (Finset.mem_filter.1 hs).1)
    (hoff s (Finset.mem_range.1 (Finset.mem_filter.1 hs).1) (Finset.mem_filter.1 hs).2))
  rw [hWfe]
  rcases hwin with hw | ⟨hpb, hthr⟩ | ⟨hpb, hthr⟩
  · exact GV.sum fun s hs => hTok s ((hWf s).1 hs).1 (hw s ((hWf s).1 hs).1 ((hWf s).1 hs).2)
  · obtain ⟨V, G, Hr, h1, h2, -, h4, -, h6, -⟩ :=
      pair_Gdata_cross h σW hpar hx2 hcard μ A Wf hWf 1 le_rfl (by norm_num) x y hxn hyn hpb
    obtain ⟨Kz, -, hKz⟩ := lemmaR_p2 h σW hpar
    have key := wsum_first h σW Wf hWf μ hμW L (Kset n p σW) (sigN n p) (clN n p) (tauU n p s0)
      (tauV n p s0) (mn_tauU_mem n s0) hLb hKn A hAP hAd V G h2 (by omega) h6 Kz
      (fun s hs => hKz s ((hWf s).1 hs).1 ((hWf s).1 hs).2)
    have e : ∑ s ∈ Wf, ∑ l ∈ range (Lc n p s + 1), nodeT (p := p) n (Kset n p σW) (sigN n p) (clN n p)
        (tauU n p s0) (tauV n p s0) (s + l * p) (elF n p σW μ A x * elF n p σW μ A y) =
        ∑ s ∈ Wf, ∑ l ∈ range (L + 1), nodeT (p := p) n (Kset n p σW) (sigN n p) (clN n p)
          (tauU n p s0) (tauV n p s0) (s + l * p) ((∏ r ∈ Wf, shiftP p μ r A) ^ 2 * V.map zphi) := by
      refine Finset.sum_congr rfl fun s hs => ?_
      rw [hLW s hs, h1]
    rw [e]
    exact key.mono hthr
  · obtain ⟨V, G, Hr, h1, h2, h3, h4, h5, h6, h7⟩ :=
      pair_Gdata_cross h σW hpar hx2 hcard μ A Wf hWf 2 (by norm_num) le_rfl x y hxn hyn hpb
    obtain ⟨h8', h9⟩ := h7 rfl
    obtain ⟨Kz, -, hKz⟩ := lemmaR_p2 h σW hpar
    have key := wsum_second h hx2 σW Wf hWf ⟨s0, hs0Wf⟩ μ hμW L (Kset n p σW) (sigN n p) (clN n p)
      (tauU n p s0) (tauV n p s0) (mn_tauU_mem n s0) hLb hKn A hAP hAd V G Hr h2 h3 h4 (by omega) h6 h8' h9
      Kz (fun s hs => hKz s ((hWf s).1 hs).1 ((hWf s).1 hs).2)
    have e : ∑ s ∈ Wf, ∑ l ∈ range (Lc n p s + 1), nodeT (p := p) n (Kset n p σW) (sigN n p) (clN n p)
        (tauU n p s0) (tauV n p s0) (s + l * p) (elF n p σW μ A x * elF n p σW μ A y) =
        ∑ s ∈ Wf, ∑ l ∈ range (L + 1), nodeT (p := p) n (Kset n p σW) (sigN n p) (clN n p)
          (tauU n p s0) (tauV n p s0) (s + l * p) ((∏ r ∈ Wf, shiftP p μ r A) ^ 2 * V.map zphi) := by
      refine Finset.sum_congr rfl fun s hs => ?_
      rw [hLW s hs, h1]
    rw [e]
    exact key.mono hthr

end CrossEntry

/-! ### Part 3: from the node sums to the `b`-entry of `L_n` -/

section Glue

variable {n p : ℕ} [hp : Fact p.Prime]

/-- `GV (thr + 1)` of `L_n(e_x e_y)` for a cross pair (window multiplicity `μ = 0`). -/
theorem cross_laiL (h : Rng n p) (σW : ℕ) (hpar : (lam n p - (σW : ℤ)) % 2 = 0) (hx2 : 0 < xtwo n p)
    (hcard : ((range p).filter (fun s => sig n p s = σW)).card = tieW n p)
    (s0 : ℕ) (hs0 : s0 < p) (hsW : sig n p s0 = σW) (μ : ℕ)
    (hμ : ∀ r < p, sig n p r = σW → mu n p r = μ) (hμ0 : μ = 0) (x y : FIdx n p σW)
    (hxn : ∀ (r : Fin p) (i : Fin (mF n p σW r)), x = Sum.inl ⟨r, i⟩ → sig n p r ≠ σW)
    (hyn : ∀ (r : Fin p) (i : Fin (mF n p σW r)), y = Sum.inl ⟨r, i⟩ → sig n p r ≠ σW)
    (hoff : ∀ s < p, sig n p s ≠ σW → defF n p σW x y s ≤ -1)
    (hwin : (∀ s < p, sig n p s = σW → defF n p σW x y s ≤ -1) ∨
      ((∀ r, r < p → sig n p r ≠ σW →
          poleF n p σW x r + poleF n p σW y r + 1 ≤ mexp n p σW r) ∧
        (pot2F n p σW x + pot2F n p σW y + 1) / 2 + 1 ≤ (σW : ℤ) + 2 * μ - 3) ∨
      ((∀ r, r < p → sig n p r ≠ σW →
          poleF n p σW x r + poleF n p σW y r + 2 ≤ mexp n p σW r) ∧
        (pot2F n p σW x + pot2F n p σW y + 1) / 2 + 1 ≤ (σW : ℤ) + 2 * μ - 2)) :
    GV p ((pot2F n p σW x + pot2F n p σW y + 1) / 2 + 1)
      (laiL n (((ExZ n p σW x) * (ExZ n p σW y)).map (Int.castRingHom ℚ))) := by
  have h8 := h.h8
  have hE := cross_entry h σW hpar hx2 hcard s0 hs0 hsW μ hμ x y hxn hyn hoff hwin
  have hF : elF n p σW μ (orthA (cLoc (Lc n p s0)) μ) x * elF n p σW μ (orthA (cLoc (Lc n p s0)) μ) y =
      (((ExZ n p σW x) * (ExZ n p σW y)).map (Int.castRingHom ℚ)).map (MvPolynomial.C : ℚ →+* MPT) := by
    rw [elF_band σW μ hμ0 hμ, elF_band σW μ hμ0 hμ, ← Polynomial.map_mul, Polynomial.map_map]
    rfl
  rw [hF] at hE
  have hK6 : Kset n p σW ⊆ range (6 * n + 1) := Finset.filter_subset _ _
  rw [laiLTx_nodes n _ hK6] at hE
  have hg : ∀ v : TVar, GV p 0 (specT (tauU n p s0) (tauV n p s0) v) := by
    rintro (i | ⟨l, _ | _⟩)
    · exact GV.var i
    · exact GV.const_loc (mn_tauU_mem n s0 l)
    · exact GV.const_loc (mn_tauV_mem n s0 h8 l)
  have := GV.subst hE (specT (tauU n p s0) (tauV n p s0)) hg
  rw [map_sum] at this
  simp only [bind_nodeT] at this
  rwa [← laiL_eq_sum] at this

/-- The `b`-coefficient of the entry of a cross pair has `v ≥ thr + 1`. -/
theorem cross_entB (h : Rng n p) (σW : ℕ) (hpar : (lam n p - (σW : ℤ)) % 2 = 0) (hx2 : 0 < xtwo n p)
    (hcard : ((range p).filter (fun s => sig n p s = σW)).card = tieW n p)
    (s0 : ℕ) (hs0 : s0 < p) (hsW : sig n p s0 = σW) (μ : ℕ)
    (hμ : ∀ r < p, sig n p r = σW → mu n p r = μ) (hμ0 : μ = 0) (x y : FIdx n p σW)
    (hxn : ∀ (r : Fin p) (i : Fin (mF n p σW r)), x = Sum.inl ⟨r, i⟩ → sig n p r ≠ σW)
    (hyn : ∀ (r : Fin p) (i : Fin (mF n p σW r)), y = Sum.inl ⟨r, i⟩ → sig n p r ≠ σW)
    (hoff : ∀ s < p, sig n p s ≠ σW → defF n p σW x y s ≤ -1)
    (hwin : (∀ s < p, sig n p s = σW → defF n p σW x y s ≤ -1) ∨
      ((∀ r, r < p → sig n p r ≠ σW →
          poleF n p σW x r + poleF n p σW y r + 1 ≤ mexp n p σW r) ∧
        (pot2F n p σW x + pot2F n p σW y + 1) / 2 + 1 ≤ (σW : ℤ) + 2 * μ - 3) ∨
      ((∀ r, r < p → sig n p r ≠ σW →
          poleF n p σW x r + poleF n p σW y r + 2 ≤ mexp n p σW r) ∧
        (pot2F n p σW x + pot2F n p σW y + 1) / 2 + 1 ≤ (σW : ℤ) + 2 * μ - 2)) :
    (p : ℚ) ^ (-((pot2F n p σW x + pot2F n p σW y + 1) / 2 + 1)) *
      entB n (((ExZ n p σW x) * (ExZ n p σW y)).map (Int.castRingHom ℚ)) ∈ LocRing p := by
  have hv := cross_laiL h σW hpar hx2 hcard s0 hs0 hsW μ hμ hμ0 x y hxn hyn hoff hwin
  have := GV.evalPt hv ![0, 1, 0] (fun i => by fin_cases i <;> simp [(LocRing p).one_mem])
  rw [laiL_channels] at this
  simpa using this

end Glue

/-! ### Part 4: the band `8n/3 < p < 3n - 1` -/

section BandCross

variable {n p : ℕ} [hp : Fact p.Prime]

/-- The three classes of residues in the band: `A` (`σ = 0`, `μ = 3`), `C` (`σ = 2`, `μ = 2`) and the
window `D` (`σ = 5`, `μ = 0`), with their positions. -/
theorem band_sigmu (h1 : 8 * n < 3 * p) (h2 : p + 1 < 3 * n) (s : ℕ) (hs : s < p) :
    (sig n p s = 0 ∧ mu n p s = 3 ∧ s ≤ 6 * n - 2 * p) ∨
    (sig n p s = 2 ∧ mu n p s = 2 ∧ 6 * n - 2 * p < s ∧ s < p - 2 * n) ∨
    (sig n p s = 5 ∧ mu n p s = 0 ∧ p - 2 * n ≤ s) := by
  have h := band_rng (p := p) h1 h2
  have hr6 := band_r6 (p := p) h1 h2
  have hr2 := band_r2 (p := p) h1 h2
  have hlam := band_lam (p := p) h1 h2
  have hmu := mu_formula h hs
  rw [hlam] at hmu
  have e : sig n p s = (if s ≤ 6 * n - 2 * p then 0 else 2) + (if p - 2 * n ≤ s then 3 else 0) := by
    unfold sig; rw [hr6, hr2]
  by_cases c1 : s ≤ 6 * n - 2 * p
  · have c2 : ¬ p - 2 * n ≤ s := by omega
    have hsg : sig n p s = 0 := by rw [e, if_pos c1, if_neg c2]
    refine Or.inl ⟨hsg, ?_, c1⟩
    rw [hmu, hsg]; norm_num
  · by_cases c2 : p - 2 * n ≤ s
    · have hsg : sig n p s = 5 := by rw [e, if_neg c1, if_pos c2]
      refine Or.inr (Or.inr ⟨hsg, ?_, c2⟩)
      rw [hmu, hsg]; norm_num
    · have hsg : sig n p s = 2 := by rw [e, if_neg c1, if_neg c2]
      refine Or.inr (Or.inl ⟨hsg, ?_, by omega, by omega⟩)
      rw [hmu, hsg]; norm_num

theorem band_mexp (h1 : 8 * n < 3 * p) (h2 : p + 1 < 3 * n) (s : ℕ) (hs : s < p) :
    (sig n p s = 5 → mexp n p 5 s = 0) ∧ (sig n p s ≠ 5 → mexp n p 5 s = 3) := by
  have hlam := band_lam (p := p) h1 h2
  rcases band_sigmu h1 h2 s hs with ⟨hg, -⟩ | ⟨hg, -⟩ | ⟨hg, -⟩
  · refine ⟨fun e => by omega, fun _ => ?_⟩
    unfold mexp; rw [hlam, hg]; norm_num
  · refine ⟨fun e => by omega, fun _ => ?_⟩
    unfold mexp; rw [hlam, hg]; norm_num
  · refine ⟨fun _ => ?_, fun e => absurd hg e⟩
    unfold mexp; rw [hlam, hg]; norm_num

end BandCross


section BandPairs

variable {n p : ℕ} [hp : Fact p.Prime]

theorem band_mF (h1 : 8 * n < 3 * p) (h2 : p + 1 < 3 * n) (s : ℕ) (hs : s < p) :
    (sig n p s = 5 → mF n p 5 s = 0) ∧ (sig n p s ≠ 5 → mF n p 5 s = mu n p s + 1) := by
  refine ⟨fun e => ?_, fun e => ?_⟩
  · unfold mF; rw [if_pos e]
    rcases band_sigmu h1 h2 s hs with ⟨hg, -⟩ | ⟨hg, -⟩ | ⟨-, hm, -⟩ <;> omega
  · unfold mF; rw [if_neg e]

/-- **Hypotheses of `cross_entB` in the band, for two distinct residues of `A ∪ C`.**
Every node off the window has `defF ≤ -1`; on the window either every node does (`thr ≤ 0`), or the
(M1) pole condition holds (`thr = 1`), or the (M2) one (`thr = 2`).  `thr ≤ 2` always. -/
theorem band_cross_hyps (h1 : 8 * n < 3 * p) (h2 : p + 1 < 3 * n) (r r' : Fin p)
    (i : Fin (mF n p 5 r)) (i' : Fin (mF n p 5 r'))
    (hr : (r : ℕ) < p - 2 * n) (hr' : (r' : ℕ) < p - 2 * n) (hne : (r : ℕ) ≠ r') :
    (∀ s < p, sig n p s ≠ 5 → defF n p 5 (Sum.inl ⟨r, i⟩) (Sum.inl ⟨r', i'⟩) s ≤ -1) ∧
    ((∀ s < p, sig n p s = 5 → defF n p 5 (Sum.inl ⟨r, i⟩) (Sum.inl ⟨r', i'⟩) s ≤ -1) ∨
      ((∀ s, s < p → sig n p s ≠ 5 →
          poleF n p 5 (Sum.inl ⟨r, i⟩) s + poleF n p 5 (Sum.inl ⟨r', i'⟩) s + 1 ≤ mexp n p 5 s) ∧
        (pot2F n p 5 (Sum.inl ⟨r, i⟩) + pot2F n p 5 (Sum.inl ⟨r', i'⟩) + 1) / 2 + 1 ≤
          ((5 : ℕ) : ℤ) + 2 * ((0 : ℕ) : ℤ) - 3) ∨
      ((∀ s, s < p → sig n p s ≠ 5 →
          poleF n p 5 (Sum.inl ⟨r, i⟩) s + poleF n p 5 (Sum.inl ⟨r', i'⟩) s + 2 ≤ mexp n p 5 s) ∧
        (pot2F n p 5 (Sum.inl ⟨r, i⟩) + pot2F n p 5 (Sum.inl ⟨r', i'⟩) + 1) / 2 + 1 ≤
          ((5 : ℕ) : ℤ) + 2 * ((0 : ℕ) : ℤ) - 2)) := by
  have hmr := band_sigmu h1 h2 r r.2
  have hmr' := band_sigmu h1 h2 r' r'.2
  have hr5 : sig n p r ≠ 5 := by rcases hmr with ⟨a, -⟩ | ⟨a, -⟩ | ⟨a, -, c⟩ <;> omega
  have hr5' : sig n p r' ≠ 5 := by rcases hmr' with ⟨a, -⟩ | ⟨a, -⟩ | ⟨a, -, c⟩ <;> omega
  have hFr := (band_mF h1 h2 r r.2).2 hr5
  have hFr' := (band_mF h1 h2 r' r'.2).2 hr5'
  have hi := i.2
  have hi' := i'.2
  have hmx : ∀ s, s < p → sig n p s ≠ 5 → mexp n p 5 s = 3 := fun s hs => (band_mexp h1 h2 s hs).2
  have hnr : ∀ s : ℕ, s < p → sig n p s = 5 → (r : ℕ) ≠ s ∧ (r' : ℕ) ≠ s := by
    intro s hs hs5
    refine ⟨fun e => ?_, fun e => ?_⟩
    · subst e; exact hr5 hs5
    · subst e; exact hr5' hs5
  refine ⟨fun s hs hs5 => ?_, ?_⟩
  · have hms := band_sigmu h1 h2 s hs
    have hFs := (band_mF h1 h2 s hs).2 hs5
    simp only [defF, pot2F, nuF]
    by_cases c1 : (r : ℕ) = s <;> by_cases c2 : (r' : ℕ) = s
    · exact absurd (c1.trans c2.symm) hne
    · rw [if_pos c1, if_neg c2]; subst c1; omega
    · rw [if_neg c1, if_pos c2]; subst c2; omega
    · rw [if_neg c1, if_neg c2]; omega
  · have ht2 : (pot2F n p 5 (Sum.inl ⟨r, i⟩) + pot2F n p 5 (Sum.inl ⟨r', i'⟩) + 1) / 2 ≤ 2 := by
      simp only [pot2F]; omega
    by_cases ht0 : (pot2F n p 5 (Sum.inl ⟨r, i⟩) + pot2F n p 5 (Sum.inl ⟨r', i'⟩) + 1) / 2 ≤ 0
    · left
      intro s hs hs5
      obtain ⟨c1, c2⟩ := hnr s hs hs5
      have hms := band_sigmu h1 h2 s hs
      have hFs := (band_mF h1 h2 s hs).1 hs5
      simp only [defF, pot2F, nuF] at ht0 ⊢
      rw [if_neg c1, if_neg c2]; omega
    · right
      by_cases ht1 : (pot2F n p 5 (Sum.inl ⟨r, i⟩) + pot2F n p 5 (Sum.inl ⟨r', i'⟩) + 1) / 2 = 1
      · left
        refine ⟨fun s hs hs5 => ?_, by omega⟩
        have hms := band_sigmu h1 h2 s hs
        simp only [poleF, pot2F] at ht1 ⊢
        rw [hmx s hs hs5]
        by_cases c1 : (r : ℕ) = s <;> by_cases c2 : (r' : ℕ) = s
        · exact absurd (c1.trans c2.symm) hne
        · rw [if_pos c1, if_neg c2]; subst c1; omega
        · rw [if_neg c1, if_pos c2]; subst c2; omega
        · rw [if_neg c1, if_neg c2]; omega
      · right
        refine ⟨fun s hs hs5 => ?_, by omega⟩
        have hms := band_sigmu h1 h2 s hs
        simp only [poleF, pot2F] at ht0 ht1 ⊢
        rw [hmx s hs hs5]
        by_cases c1 : (r : ℕ) = s <;> by_cases c2 : (r' : ℕ) = s
        · exact absurd (c1.trans c2.symm) hne
        · rw [if_pos c1, if_neg c2]; subst c1; omega
        · rw [if_neg c1, if_pos c2]; subst c2; omega
        · rw [if_neg c1, if_neg c2]; omega

/-- **LB06 (band, `b`-channel).**  Let `e_{r,i}`, `e_{r',i'}` be two elements of the E2 basis at distinct
residues `r ≠ r'` of `A ∪ C = [0, a)`, `a = p - 2n`, and `thr = ⌈(2π_x + 2π_y)/2⌉`
(`= i + i' - 4` on `A × A`, `i + i' - 3` on `A × C`, `i + i' - 2` on `C × C`).  Then
`v_p(B) ≥ thr + 1` for `L_n(e_x e_y) = aA + bB + XC`: the reduction of `p^{-thr}·B` is `0`. -/
theorem lb06_band (h1 : 8 * n < 3 * p) (h2 : p + 1 < 3 * n) (r r' : Fin p)
    (i : Fin (mF n p 5 r)) (i' : Fin (mF n p 5 r'))
    (hr : (r : ℕ) < p - 2 * n) (hr' : (r' : ℕ) < p - 2 * n) (hne : (r : ℕ) ≠ r') :
    (p : ℚ) ^ (-((pot2F n p 5 (Sum.inl ⟨r, i⟩) + pot2F n p 5 (Sum.inl ⟨r', i'⟩) + 1) / 2 + 1)) *
      entB n (((ExZ n p 5 (Sum.inl ⟨r, i⟩)) * (ExZ n p 5 (Sum.inl ⟨r', i'⟩))).map
        (Int.castRingHom ℚ)) ∈ LocRing p := by
  classical
  have h := band_rng (p := p) h1 h2
  have hlam := band_lam (p := p) h1 h2
  have hr6 := band_r6 (p := p) h1 h2
  have hr2 := band_r2 (p := p) h1 h2
  have hs0 : p - 2 * n < p := by omega
  have hsW : sig n p (p - 2 * n) = 5 := by
    unfold sig; rw [hr6, hr2]
    have : ¬ (p - 2 * n ≤ 6 * n - 2 * p) := by omega
    simp [this]
  have hmr := band_sigmu h1 h2 r r.2
  have hmr' := band_sigmu h1 h2 r' r'.2
  have hr5 : sig n p r ≠ 5 := by rcases hmr with ⟨a, -⟩ | ⟨a, -⟩ | ⟨a, -, c⟩ <;> omega
  have hr5' : sig n p r' ≠ 5 := by rcases hmr' with ⟨a, -⟩ | ⟨a, -⟩ | ⟨a, -, c⟩ <;> omega
  obtain ⟨hoff, hwin⟩ := band_cross_hyps h1 h2 r r' i i' hr hr' hne
  have hxn : ∀ (r0 : Fin p) (i0 : Fin (mF n p 5 r0)), (Sum.inl ⟨r, i⟩ : FIdx n p 5) = Sum.inl ⟨r0, i0⟩ →
      sig n p r0 ≠ 5 := by
    intro r0 i0 he
    obtain ⟨e1, -⟩ := Sigma.mk.inj_iff.1 (Sum.inl.inj he)
    rw [← e1]; exact hr5
  have hyn : ∀ (r0 : Fin p) (i0 : Fin (mF n p 5 r0)), (Sum.inl ⟨r', i'⟩ : FIdx n p 5) = Sum.inl ⟨r0, i0⟩ →
      sig n p r0 ≠ 5 := by
    intro r0 i0 he
    obtain ⟨e1, -⟩ := Sigma.mk.inj_iff.1 (Sum.inl.inj he)
    rw [← e1]; exact hr5'
  have hcard : ((range p).filter (fun s => sig n p s = 5)).card = tieW n p := by
    rw [card_sig_five h, (band_xtwo h1 h2).2]
    unfold szD; rw [hr6, hr2]; omega
  exact cross_entB h 5 (by rw [hlam]; norm_num) (band_xtwo_pos h1 h2) hcard (p - 2 * n) hs0 hsW 0
    (fun r hr hrs => band_mu h1 h2 r hr hrs) rfl _ _ hxn hyn hoff hwin

/-- **LB06 at a point.**  For `a, b ∈ ℤ_(p)` and `v_p(X) ≥ -3`, the entry of `L_n` at `(a, b, X)` of two
basis elements at distinct residues of `A ∪ C` has `v_p ≥ thr + 1`, i.e. the reduction of `p^{-thr}` times
the entry is `0`.  (Together with the own-residue blocks `h_{i+i'}` of `B83OwnNode`/`B83DNode`, these are the
zero off-diagonal blocks of `B83.intBlock`.) -/
theorem lb06_point (h1 : 8 * n < 3 * p) (h2 : p + 1 < 3 * n) (r r' : Fin p)
    (i : Fin (mF n p 5 r)) (i' : Fin (mF n p 5 r'))
    (hr : (r : ℕ) < p - 2 * n) (hr' : (r' : ℕ) < p - 2 * n) (hne : (r : ℕ) ≠ r')
    (a b X : ℚ) (ha : a ∈ LocRing p) (hb : b ∈ LocRing p) (hX : (p : ℚ) ^ 3 * X ∈ LocRing p) :
    (p : ℚ) ^ (-((pot2F n p 5 (Sum.inl ⟨r, i⟩) + pot2F n p 5 (Sum.inl ⟨r', i'⟩) + 1) / 2 + 1)) *
      MvPolynomial.eval ![a, b, X]
        (laiL n (((ExZ n p 5 (Sum.inl ⟨r, i⟩)) * (ExZ n p 5 (Sum.inl ⟨r', i'⟩))).map
          (Int.castRingHom ℚ))) ∈ LocRing p := by
  obtain ⟨hA, -, hC⟩ := lb02_band h1 h2 (Sum.inl ⟨r, i⟩) (Sum.inl ⟨r', i'⟩)
  have hB := lb06_band h1 h2 r r' i i' hr hr' hne
  have hp0 := p_ne_zero' (p := p)
  rw [laiL_channels]
  simp only [map_add, map_mul, MvPolynomial.eval_X, MvPolynomial.eval_C]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons]
  set E := (((ExZ n p 5 (Sum.inl ⟨r, i⟩)) * (ExZ n p 5 (Sum.inl ⟨r', i'⟩))).map (Int.castRingHom ℚ)) with hE
  set t : ℤ := (pot2F n p 5 (Sum.inl ⟨r, i⟩) + pot2F n p 5 (Sum.inl ⟨r', i'⟩) + 1) / 2 with ht
  have e : (p : ℚ) ^ (-(t + 1)) * (a * entA n E + b * entB n E + X * entX n E) =
      a * ((p : ℚ) ^ (-(t + 1)) * entA n E) + b * ((p : ℚ) ^ (-(t + 1)) * entB n E) +
        (p : ℚ) ^ 3 * X * ((p : ℚ) ^ (-(t + 4)) * entX n E) := by
    have e1 : (p : ℚ) ^ (-(t + 1)) = (p : ℚ) ^ 3 * (p : ℚ) ^ (-(t + 4)) := by
      rw [show (p : ℚ) ^ 3 = (p : ℚ) ^ (3 : ℤ) by norm_cast, pz]; congr 1; ring
    rw [e1]; ring
  rw [e]
  exact (LocRing p).add_mem ((LocRing p).add_mem ((LocRing p).mul_mem ha hA) ((LocRing p).mul_mem hb hB))
    ((LocRing p).mul_mem hX hC)

end BandPairs


end

end CatalanCore.Lai

#print axioms CatalanCore.Lai.pair_Gdata_cross
#print axioms CatalanCore.Lai.cross_entry
#print axioms CatalanCore.Lai.cross_laiL
#print axioms CatalanCore.Lai.cross_entB
#print axioms CatalanCore.Lai.band_cross_hyps
#print axioms CatalanCore.Lai.lb06_band
#print axioms CatalanCore.Lai.lb06_point
