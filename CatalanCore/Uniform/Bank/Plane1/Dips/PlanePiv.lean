module

public import CatalanCore.Uniform.Bank.Plane1.Dips.PlaneNodes
public import CatalanCore.Uniform.Bank.Plane1.Dips.Member

@[expose] public section
set_option Elab.async false
set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option maxHeartbeats 1600000

/-! # The pivot table of the plane frames (wave R0; ledger R01-R03; package R1b)

A pivot rule on the cells `(q, eA, eB)` (`fl : ℕ → Bool → Bool → Bool`, `FlagOK`): a border node `x ≥ p` of a flagged cell
is pivoted on the common node `x - p` (the latest common node below it in its fibre: `2 m < p` puts the border block
inside `[r, r + p)`; same cell with `q - 1`; digit difference `j = 1`).  The coefficient is read off the level table,
`lamTab = (Vtab(q) - Vtab(q-1)) / Utab(q-1)`, the effective level is `vsTab = (Vtab(q) - lamTab Vtab(q-1)) / (1 - lamTab)`.
`FlagOK` asks for each flagged cell: `q ≥ 1`, `Utab(q-1) ≠ 0`, `lamTab ≠ 1`, and `lamTab ∈ ℤ[1/30]` (`Smooth5`: audit
repair A1, so that every prime `p ≥ 7` is admissible).

`hybPiv_plane` builds the `HybPiv` of `Dips.Member` from the table: `pRd`, `pCd`, `lRd`, `lCd`, `VRd`, `VCd`. -/

namespace CatalanCore.Uniform.Bank.Plane1.Dips
open Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid CatalanCore.Uniform.Bank.Plane1

/-- Rationals with denominator dividing a power of `30`. -/
def Smooth5 (x : ℚ) : Prop := ∃ (k : ℕ) (z : ℤ), x = (z : ℚ) / ((30 : ℚ) ^ k)

theorem smooth5_mem {p : ℕ} [hp : Fact p.Prime] (hp7 : 7 ≤ p) {x : ℚ} (h : Smooth5 x) : x ∈ LocRing p := by
  obtain ⟨k, z, rfl⟩ := h
  have hnd : ¬ p ∣ 30 ^ k := by
    intro hd
    have h30 : p ∣ 30 := hp.out.dvd_of_dvd_pow hd
    have : p ≤ 30 := Nat.le_of_dvd (by norm_num) h30
    have h2 : p ∣ 2 * 3 * 5 := by simpa using h30
    rcases (Nat.Prime.dvd_mul hp.out).1 h2 with h | h
    · rcases (Nat.Prime.dvd_mul hp.out).1 h with h | h
      · have := Nat.le_of_dvd (by norm_num) h; omega
      · have := Nat.le_of_dvd (by norm_num) h; omega
    · have := Nat.le_of_dvd (by norm_num) h; omega
  have : ((z : ℚ)) / ((30 : ℚ) ^ k) = (z : ℚ) * (((30 ^ k : ℕ) : ℚ))⁻¹ := by
    rw [div_eq_mul_inv]; push_cast; rfl
  rw [this]
  exact (LocRing p).mul_mem (int_mem_locRing z) (inv_natCast_mem_locRing hnd)

section Tab

variable (a b c : ℤ) (n : ℕ)

/-- The pivot coefficient at the cell `(q, eA, eB)`. -/
noncomputable def lamTab (q : ℕ) (eA eB : Bool) : ℚ :=
  (Vtab a b c n q eA eB - Vtab a b c n (q - 1) eA eB) / Utab a b c n (q - 1) eA eB

/-- The effective level `V*` of a pivoted node at the cell `(q, eA, eB)`. -/
noncomputable def vsTab (q : ℕ) (eA eB : Bool) : ℚ :=
  (Vtab a b c n q eA eB - lamTab a b c n q eA eB * Vtab a b c n (q - 1) eA eB) / (1 - lamTab a b c n q eA eB)

/-- The pivot rule on cells is admissible. -/
structure FlagOK (fl : ℕ → Bool → Bool → Bool) : Prop where
  ok : ∀ q eA eB, fl q eA eB = true → 1 ≤ q ∧ Utab a b c n (q - 1) eA eB ≠ 0 ∧
    lamTab a b c n q eA eB ≠ 1 ∧ Smooth5 (lamTab a b c n q eA eB)

end Tab

section Nodes

variable (σ : Support) (a b c : ℤ) (h0 : a + b + c = 0) (n p : ℕ) (fl : ℕ → Bool → Bool → Bool)

/-- The cell of a node: `[t mod p ≥ kA]`, `[t mod p ≥ kB]`. -/
def cA (σ : Support) (n p t : ℕ) : Bool := decide ((n * p + σ.rho) / 3 ≤ t % p)
def cB (p t : ℕ) : Bool := decide ((p + 1) / 2 ≤ t % p)

/-- A node is pivoted when it lies at or above `p` in a flagged cell. -/
def isPiv (σ : Support) (n p : ℕ) (fl : ℕ → Bool → Bool → Bool) (t : ℕ) : Bool :=
  decide (p ≤ t) && fl (t / p) (cA σ n p t) (cB p t)

theorem cell_pred {t : ℕ} [hp : Fact p.Prime] (ht : p ≤ t) :
    (t - p) / p = t / p - 1 ∧ (t - p) % p = t % p := by
  have hpos := hp.out.pos
  have h1 := Nat.div_add_mod t p
  have h2 := Nat.mod_lt t hpos
  generalize t / p = q at h1 ⊢
  generalize t % p = ξ at h1 h2 ⊢
  have hq : 1 ≤ q := by
    by_contra h
    have : q = 0 := by omega
    subst this
    omega
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  have e : t - p = ξ + p * q' := by
    rw [Nat.mul_succ] at h1
    omega
  have := (Nat.div_mod_unique hpos).2 ⟨e.symm, h2⟩
  simpa using this

end Nodes

section Defs

theorem isPiv_le {σ : Support} {n p : ℕ} {fl : ℕ → Bool → Bool → Bool} {t : ℕ} (h : isPiv σ n p fl t = true) : p ≤ t := by
  unfold isPiv at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

theorem isPiv_fl {σ : Support} {n p : ℕ} {fl : ℕ → Bool → Bool → Bool} {t : ℕ} (h : isPiv σ n p fl t = true) : fl (t / p) (cA σ n p t) (cB p t) = true := by
  unfold isPiv at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.2

/-- The row pivot of the border row `i`: the common node `r + 2 i - p` when the node is pivoted. -/
def pRd (σ : Support) (n p : ℕ) (fl : ℕ → Bool → Bool → Bool) (r m : ℕ) (hm : 2 * m < p) (i : Fin m) :
    Option (Fin r) :=
  if h : isPiv σ n p fl (r + 2 * i.1) = true then
    some ⟨r + 2 * i.1 - p, by have := isPiv_le h; have := i.2; omega⟩
  else none

/-- The column pivot of the border column `i`. -/
def pCd (σ : Support) (n p : ℕ) (fl : ℕ → Bool → Bool → Bool) (r m : ℕ) (hm : 2 * m < p) (i : Fin m) :
    Option (Fin r) :=
  if h : isPiv σ n p fl (r + 2 * i.1 + 1) = true then
    some ⟨r + 2 * i.1 + 1 - p, by have := isPiv_le h; have := i.2; omega⟩
  else none

/-- The pivot coefficient of a node (`0` if not pivoted). -/
noncomputable def lamNode (σ : Support) (a b c : ℤ) (n p : ℕ) (fl : ℕ → Bool → Bool → Bool) (t : ℕ) : ℚ :=
  if isPiv σ n p fl t = true then lamTab a b c n (t / p) (cA σ n p t) (cB p t) else 0

/-- The effective level of a node. -/
noncomputable def vsNode (σ : Support) (a b c : ℤ) (h0 : a + b + c = 0) (n p : ℕ)
    (fl : ℕ → Bool → Bool → Bool) (t : ℕ) : ℚ :=
  if isPiv σ n p fl t = true then vsTab a b c n (t / p) (cA σ n p t) (cB p t)
  else Vp p (planeFrame σ a b c h0) t


end Defs

section Hyb

variable {σ : Support} {a b c : ℤ} {h0 : a + b + c = 0} {p : ℕ} [hp : Fact p.Prime] {n : ℕ}
  {fl : ℕ → Bool → Bool → Bool} {r m : ℕ}

variable (hp7 : 7 ≤ p) (hn : n = 1 ∨ n = 2) (h3 : 3 ∣ n * p + σ.rho) (hfl : FlagOK a b c n fl)

include hp7 hn h3 hfl in
/-- **The pivot relations at a pivoted node** (digit difference `1`). -/
theorem node_piv {t : ℕ} (h : isPiv σ n p fl t = true) (hts : 3 * t < p * p) :
    lamNode σ a b c n p fl t * (1 * Up p (planeFrame σ a b c h0) (t - p)) =
        Vp p (planeFrame σ a b c h0) t - Vp p (planeFrame σ a b c h0) (t - p) ∧
      (1 - lamNode σ a b c n p fl t) * vsNode σ a b c h0 n p fl t =
        Vp p (planeFrame σ a b c h0) t - lamNode σ a b c n p fl t * Vp p (planeFrame σ a b c h0) (t - p) ∧
      lamNode σ a b c n p fl t ∈ LocRing p := by
  have hle := isPiv_le h
  obtain ⟨hq, hU, hl1, hsm⟩ := hfl.ok _ _ _ (isPiv_fl h)
  obtain ⟨hd, hm⟩ := cell_pred p hle
  have eV : Vp p (planeFrame σ a b c h0) t = Vtab a b c n (t / p) (cA σ n p t) (cB p t) := planeV_eq hp7 hn h3 t
  have eV' : Vp p (planeFrame σ a b c h0) (t - p) = Vtab a b c n (t / p - 1) (cA σ n p t) (cB p t) := by
    rw [planeV_eq hp7 hn h3, hd]
    simp only [cA, cB, hm]
  have eU' : Up p (planeFrame σ a b c h0) (t - p) = Utab a b c n (t / p - 1) (cA σ n p t) (cB p t) := by
    rw [planeU_eq hp7 hn h3, hd]
    simp only [cA, cB, hm]
  have eL : lamNode σ a b c n p fl t = lamTab a b c n (t / p) (cA σ n p t) (cB p t) := by
    simp [lamNode, h]
  have eS : vsNode σ a b c h0 n p fl t = vsTab a b c n (t / p) (cA σ n p t) (cB p t) := by
    simp [vsNode, h]
  rw [eL, eS, eV, eV', eU']
  refine ⟨?_, ?_, ?_⟩
  · unfold lamTab
    rw [one_mul]
    exact div_mul_cancel₀ _ hU
  · unfold vsTab
    exact mul_div_cancel₀ _ (sub_ne_zero.2 (Ne.symm hl1))
  · exact smooth5_mem hp7 hsm

end Hyb

section HybPlane

variable {σ : Support} {a b c : ℤ} {h0 : a + b + c = 0} {p : ℕ} [hp : Fact p.Prime] {n : ℕ}
  {fl : ℕ → Bool → Bool → Bool} {r m : ℕ}
  (hp7 : 7 ≤ p) (hn : n = 1 ∨ n = 2) (h3 : 3 ∣ n * p + σ.rho) (hfl : FlagOK a b c n fl)

include hp7 hn h3 hfl in
/-- **The pivot data of a plane flag table is a `HybPiv`**: all hypotheses of `member_gle` hold. -/
theorem hybPiv_plane (hN : 3 * (r + 2 * m) < p * p) (hm : 2 * m < p) :
    HybPiv r m p (planeFrame σ a b c h0) (pRd σ n p fl r m hm) (pCd σ n p fl r m hm)
      (fun i => lamNode σ a b c n p fl (r + 2 * i.1)) (fun i => lamNode σ a b c n p fl (r + 2 * i.1 + 1))
      (fun i => vsNode σ a b c h0 n p fl (r + 2 * i.1)) (fun i => vsNode σ a b c h0 n p fl (r + 2 * i.1 + 1)) where
  h3 := by omega
  hnorm := rfl
  v_mem t ht := Vp_mem_Q (plane_den_le σ a b c h0) (by omega)
  u_mem t ht := Up_mem_Q (plane_den_le σ a b c h0) (by omega)
  square_free U V hU hV hne := diff_not_sq_of_lt (by omega) (by omega) hne
  hm := hm
  rowP i c' h := by
    have hi := i.2
    by_cases hpv : isPiv σ n p fl (r + 2 * i.1) = true
    · have h' : pRd σ n p fl r m hm i = some ⟨r + 2 * i.1 - p, by have := isPiv_le hpv; omega⟩ := by
        simp [pRd, hpv]
      rw [h'] at h
      have hc : c'.1 = r + 2 * i.1 - p := by rw [← Option.some.inj h]
      obtain ⟨e1, e2, -⟩ := node_piv hp7 hn h3 hfl hpv (by omega)
      have hle := isPiv_le hpv
      refine ⟨1, one_pos, by omega, ?_, ?_⟩
      · rw [hc]; exact e1
      · rw [hc]; exact e2
    · simp [pRd, hpv] at h
  rowN i h := by
    have hi := i.2
    by_cases hpv : isPiv σ n p fl (r + 2 * i.1) = true
    · simp [pRd, hpv] at h
    · simp [vsNode, hpv]
  colP i c' h := by
    have hi := i.2
    by_cases hpv : isPiv σ n p fl (r + 2 * i.1 + 1) = true
    · have h' : pCd σ n p fl r m hm i = some ⟨r + 2 * i.1 + 1 - p, by have := isPiv_le hpv; omega⟩ := by
        simp [pCd, hpv]
      rw [h'] at h
      have hc : c'.1 = r + 2 * i.1 + 1 - p := by rw [← Option.some.inj h]
      obtain ⟨e1, e2, -⟩ := node_piv hp7 hn h3 hfl hpv (by omega)
      have hle := isPiv_le hpv
      refine ⟨1, one_pos, by omega, ?_, ?_⟩
      · rw [hc]; exact e1
      · rw [hc]; exact e2
    · simp [pCd, hpv] at h
  colN i h := by
    have hi := i.2
    by_cases hpv : isPiv σ n p fl (r + 2 * i.1 + 1) = true
    · simp [pCd, hpv] at h
    · simp [vsNode, hpv]
  lR_mem i := by
    have hi := i.2
    by_cases hpv : isPiv σ n p fl (r + 2 * i.1) = true
    · exact (node_piv (h0 := h0) hp7 hn h3 hfl hpv (by omega)).2.2
    · simp [lamNode, hpv]
  lC_mem i := by
    have hi := i.2
    by_cases hpv : isPiv σ n p fl (r + 2 * i.1 + 1) = true
    · exact (node_piv (h0 := h0) hp7 hn h3 hfl hpv (by omega)).2.2
    · simp [lamNode, hpv]

end HybPlane

#print axioms CatalanCore.Uniform.Bank.Plane1.Dips.node_piv
#print axioms CatalanCore.Uniform.Bank.Plane1.Dips.hybPiv_plane

end CatalanCore.Uniform.Bank.Plane1.Dips
