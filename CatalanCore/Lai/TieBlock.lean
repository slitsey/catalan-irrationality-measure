module

public import CatalanCore.Lai.ContentL12
public import CatalanCore.Content.ReducedLead

@[expose] public section

/-!
# `CatalanCore.Lai.TieBlock`: leading terms and reductions of the Gram entries (Theorems L1, L2)

For a pair `(x, y)` of basis elements of equal parity, the Gram entry `⟨f_x, f_y⟩` equals the sum of the
leading terms of the nodes at the *contributing* residues (those where `π_x + π_y` meets the node bound
`σ - 4 + ord_s`), up to Gauss valuation `≥ e + 1` (`lead_entry`), and any integral lift of `p^{-e}⟨f_x, f_y⟩` reduces to `b · ρ`
with `ρ` the reduction of `∑_k q_k` (`red_entry`).
-/

open Finset CatalanCore.Basic CatalanCore.Arith.Hybrid CatalanCore.Content MvPolynomial
open scoped Nat

namespace CatalanCore.Lai

section LeadEntry

variable {n p : ℕ} [hp : Fact p.Prime]

/-- exponent vector and `X`-power of the product `f_x f_y`. -/
noncomputable def nuS (n p : ℕ) (x y : LIdx n p) : Fin p → ℕ := fun r => nuL n p x r + nuL n p y r
noncomputable def wS (n p : ℕ) (x y : LIdx n p) : ℕ := wL n p x + wL n p y

/-- `ord_{k mod p}` of the product. -/
noncomputable def mmk (n p : ℕ) (x y : LIdx n p) (k : ℕ) : ℕ := mmF p (nuS n p x y) (k % p)
/-- the cofactor at residue `k mod p`. -/
noncomputable def RRk (n p : ℕ) (x y : LIdx n p) (k : ℕ) : Polynomial ℚ :=
  RRF p (wS n p x y) (nuS n p x y) (k % p)

/-- the unit part `u_k = c_k / p^{σ}`. -/
noncomputable def uk (n p k : ℕ) : ℕ := laiCoef n k / p ^ sig n p (k % p)

/-- the nodes carrying the leading terms. -/
noncomputable def Eset (n p : ℕ) (x y : LIdx n p) : Finset ℕ :=
  (range (6 * n + 1)).filter (fun k => 1 ≤ k / p ∧
    pot2 n p x + pot2 n p y = 2 * ((sig n p (k % p) : ℤ) - 4 + (mmk n p x y k : ℤ)))

/-- the leading constant of the node `k` (as in `node_lead`). -/
noncomputable def cLead (n p : ℕ) (x y : LIdx n p) (k : ℕ) : ℚ :=
  (p : ℚ) ^ (sig n p (k % p)) * (p : ℚ) ^ (mmk n p x y k) * ((p : ℚ) ^ 4)⁻¹ * (uk n p k : ℚ) *
    (RRk n p x y k).eval (-((k % p : ℕ) : ℚ)) *
    leadF (mmk n p x y k) (k / p) (uL (k / p)) (vL n p k (k / p))

lemma laiCoef_eq_uk (h : Rng n p) (k : ℕ) (hk : k ≤ 6 * n) :
    (laiCoef n k : ℚ) = (p : ℚ) ^ (sig n p (k % p)) * (uk n p k : ℚ) := by
  have hp3 : 3 ≤ p := by have := h.p5; omega
  obtain ⟨u, hu, -, -⟩ := laiCoef_unit (p := p) h.h8 hp3 k hk
  have : uk n p k = u := by
    unfold uk
    rw [hu]
    exact Nat.mul_div_cancel_left _ (pow_pos hp.out.pos _)
  rw [this]
  exact_mod_cast hu

/-- **Leading terms of a Gram entry.** -/
theorem lead_entry (h : Rng n p) (x y : LIdx n p) (hpar : pot2 n p x % 2 = pot2 n p y % 2) :
    GV p ((pot2 n p x + pot2 n p y) / 2 + 1)
      (laiL n (fL n p x * fL n p y) -
        MvPolynomial.C (∑ k ∈ Eset n p x y, cLead n p x y k) * MvPolynomial.X (1 : Fin 3)) := by
  have hp3 : 3 ≤ p := by have := h.p5; omega
  have hF : fL n p x * fL n p y = Pd p (wS n p x y) (nuS n p x y) := by
    rw [fL_eq, fL_eq, Pd_mul]; rfl
  rw [hF]
  set F := Pd p (wS n p x y) (nuS n p x y) with hFdef
  set e : ℤ := (pot2 n p x + pot2 n p y) / 2 with he
  have hpair : ∀ s (hs : s < p), pot2 n p x + pot2 n p y ≤
      2 * ((sig n p s : ℤ) - 4 + (mmF p (nuS n p x y) s : ℤ)) := by
    intro s hs
    have := pair_arith h x y s hs
    have hm : mmF p (nuS n p x y) s = nuL n p x ⟨s, hs⟩ + nuL n p y ⟨s, hs⟩ := by
      simp [mmF, hs, nuS]
    rw [hm]; push_cast; linarith
  -- part 1: remove the leading nodes
  have h1 := laiL_ge_except (p := p) n h.h8 hp3 F (fun s => mmF p (nuS n p x y) s)
    (fun s => RRF p (wS n p x y) (nuS n p x y) s) (fun s _ => RRF_int _ _ _ _)
    (fun s _ => Pd_decomp _ _ _ s) (e + 1) (Eset n p x y)
    (by intro k hk; exact (Finset.mem_filter.1 hk).1)
    (by
      intro k hk6 hkE hl
      have hs : k % p < p := Nat.mod_lt _ hp.out.pos
      have := hpair _ hs
      have hnot : ¬ (1 ≤ k / p ∧ pot2 n p x + pot2 n p y =
          2 * ((sig n p (k % p) : ℤ) - 4 + (mmk n p x y k : ℤ))) := by
        intro hc
        exact hkE (Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), hc⟩)
      have hne : pot2 n p x + pot2 n p y ≠
          2 * ((sig n p (k % p) : ℤ) - 4 + (mmk n p x y k : ℤ)) := fun hc => hnot ⟨hl, hc⟩
      unfold mmk at hne
      omega)
    (by
      intro k hk6 hkE hkp
      have := hpair k hkp
      by_cases h2 : 2 ≤ mmF p (nuS n p x y) k
      · right; exact h2
      · left
        have : min (mmF p (nuS n p x y) k) 1 ≤ 1 := min_le_right _ _
        have hm0 : mmF p (nuS n p x y) k ≤ 1 := by omega
        have hmin : min (mmF p (nuS n p x y) k) 1 = mmF p (nuS n p x y) k := by omega
        push_cast [hmin]
        omega)
  -- part 2: leading terms of the nodes in `E`
  have h2 : ∀ k ∈ Eset n p x y,
      GV p (e + 1) (laiNd n k F - MvPolynomial.C (cLead n p x y k) * MvPolynomial.X (1 : Fin 3)) := by
    intro k hk
    obtain ⟨hk1, hl, hcond⟩ := Finset.mem_filter.1 hk
    have hk6 : k ≤ 6 * n := by simpa [Nat.lt_succ_iff] using Finset.mem_range.1 hk1
    have hs : k % p < p := Nat.mod_lt _ hp.out.pos
    have hdec := Pd_decomp p (wS n p x y) (nuS n p x y) (k % p)
    have hnl := node_lead (p := p) n k h.h8 hp3 hk6 hl (uk n p k) (laiCoef_eq_uk h k hk6)
      (mmk n p x y k) (RRk n p x y k) (RRF_int _ _ _ _)
    have hFk : F = (Polynomial.X + Polynomial.C ((k % p : ℕ) : ℚ)) ^ (mmk n p x y k) * RRk n p x y k := by
      rw [hFdef]; exact hdec
    rw [hFk]
    refine hnl.mono ?_
    omega
  have h3 : GV p (e + 1) (∑ k ∈ Eset n p x y, (laiNd n k F -
      MvPolynomial.C (cLead n p x y k) * MvPolynomial.X (1 : Fin 3))) := GV.sum h2
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← map_sum] at h3
  have := h1.add h3
  simpa using this

end LeadEntry

section RedEntry

variable {n p : ℕ} [hp : Fact p.Prime]

/-- the leading constant of node `k`, scaled by `p^{-e}` at contributing residues. -/
noncomputable def qTerm (n p : ℕ) (x y : LIdx n p) (k : ℕ) : ℚ :=
  (uk n p k : ℚ) * (RRk n p x y k).eval (-((k % p : ℕ) : ℚ)) *
    leadF (mmk n p x y k) (k / p) (uL (k / p)) (vL n p k (k / p))

lemma cLead_eq (h : Rng n p) (x y : LIdx n p) (hpar : pot2 n p x % 2 = pot2 n p y % 2) (k : ℕ)
    (hk : k ∈ Eset n p x y) :
    cLead n p x y k = (p : ℚ) ^ ((pot2 n p x + pot2 n p y) / 2) * qTerm n p x y k := by
  obtain ⟨-, -, hcond⟩ := Finset.mem_filter.1 hk
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have he : (pot2 n p x + pot2 n p y) / 2 =
      (sig n p (k % p) : ℤ) - 4 + (mmk n p x y k : ℤ) := by omega
  have key : (p : ℚ) ^ ((sig n p (k % p) : ℤ) - 4 + (mmk n p x y k : ℤ)) =
      (p : ℚ) ^ (sig n p (k % p)) * (p : ℚ) ^ (mmk n p x y k) * ((p : ℚ) ^ 4)⁻¹ := by
    rw [zpow_add₀ hp0, zpow_sub₀ hp0, zpow_natCast, zpow_natCast]
    norm_num
    field_simp
  unfold cLead qTerm
  rw [he, key]
  ring

lemma qTerm_mem (h : Rng n p) (x y : LIdx n p) (k : ℕ) (hk : k ≤ 6 * n) (hkp : k / p < p) :
    qTerm n p x y k ∈ LocRing p := by
  have hs : k % p < p := Nat.mod_lt _ hp.out.pos
  unfold qTerm
  have hR : (RRk n p x y k).eval (-((k % p : ℕ) : ℚ)) ∈ LocRing p :=
    (RRF_int (p := p) _ _ _ _).eval_mem ((LocRing p).neg_mem (natq_mem _))
  have hL := leadF_mem (p := p) (mmk n p x y k) (k / p) (uL (k / p)) (vL n p k (k / p)) (natq_mem _)
    (uL_mem (p := p) _ hkp) (vL_mem (p := p) n k _ h.h8 hk hkp)
  exact (LocRing p).mul_mem ((LocRing p).mul_mem (natq_mem _) hR) hL

/-- **Reduction of a tie Gram entry.**  Any lift of `p^{-e} ⟨f_x, f_y⟩` reduces to `b · ρ`, `ρ` the
reduction of `∑_{k ∈ E} q_k`. -/
theorem red_entry (h : Rng n p) (x y : LIdx n p) (hpar : pot2 n p x % 2 = pot2 n p y % 2)
    (Z : MvPolynomial (Fin 3) (LocRing p))
    (hZ : toQmv p Z = C ((p : ℚ) ^ (-((pot2 n p x + pot2 n p y) / 2))) * laiL n (fL n p x * fL n p y)) :
    ∃ q : LocRing p, (q : ℚ) = ∑ k ∈ Eset n p x y, qTerm n p x y k ∧
      redMv p Z = algebraMap (MvPolynomial (Fin 3) (ZMod p))
        (FractionRing (MvPolynomial (Fin 3) (ZMod p))) (C (redQ p q) * X 1) := by
  have hmem : (∑ k ∈ Eset n p x y, qTerm n p x y k) ∈ LocRing p := by
    refine (LocRing p).sum_mem (fun k hk => ?_)
    obtain ⟨hk1, hl, -⟩ := Finset.mem_filter.1 hk
    have hk6 : k ≤ 6 * n := by simpa [Nat.lt_succ_iff] using Finset.mem_range.1 hk1
    have hkp : k / p < p := by
      rw [Nat.div_lt_iff_lt_mul hp.out.pos]; simpa [pow_two] using (show k < p ^ 2 by have := h.h8; omega)
    exact qTerm_mem h x y k hk6 hkp
  refine ⟨⟨_, hmem⟩, rfl, ?_⟩
  rw [← redMv_C_mul_X]
  refine redMv_lift_eq (C ⟨_, hmem⟩ * X 1) ?_ Z hZ
  have hl := lead_entry h x y hpar
  have : toQmv p (C (⟨_, hmem⟩ : LocRing p) * X (1 : Fin 3) : MvPolynomial (Fin 3) (LocRing p)) =
      C (∑ k ∈ Eset n p x y, qTerm n p x y k) * X 1 := by simp [toQmv]
  rw [this, ← mul_assoc, ← C_mul, Finset.mul_sum]
  have hc : ∑ k ∈ Eset n p x y, (p : ℚ) ^ ((pot2 n p x + pot2 n p y) / 2) * qTerm n p x y k =
      ∑ k ∈ Eset n p x y, cLead n p x y k :=
    Finset.sum_congr rfl (fun k hk => (cLead_eq h x y hpar k hk).symm)
  rw [hc]
  exact hl

end RedEntry

end CatalanCore.Lai

#print axioms CatalanCore.Lai.lead_entry
#print axioms CatalanCore.Lai.red_entry
