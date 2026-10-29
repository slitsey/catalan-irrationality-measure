import CatalanCore.Uniform.Content.BankShared.TwoTerm.Class
import CatalanCore.Uniform.Content.BankShared.Reindex
import CatalanCore.Uniform.Content.UFSimple.Closed
set_option Elab.async false

/-! # The UF hypotheses for every two-term bank (lane C4, gap C4)

`closedHyp_tt`: the hypothesis package `ClosedHyp` of `UFSimple/Closed.lean` (the closed UF
layer `ufClosedLayer`, base `closedPrice`, debit 1) holds for `TwoTermData Fr q o`, a natural norm
`nm` with `p ∤ nm`, `q (r + p) ≤ p²`, `2 m ≤ p`, and the pole residue `ρ = k` of the root class `j`
(`q k = j p + o`, `0 < j < q`).

`uf_gle_tt`: the branch statement, a member is cleared by `closedPrice m r p k` plus its deletion
count. -/

namespace CatalanCore.Uniform.Content.BankShared.TwoTerm
open Polynomial Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid CatalanCore.Uniform
  CatalanCore.Uniform.Content.Smith CatalanCore.Uniform.Content.Member CatalanCore.Uniform.Content.Shape
  CatalanCore.Uniform.Content.UFSimple CatalanCore.Uniform.Content.BankShared

variable {Fr : Frame} {q o : ℕ}

theorem closedHyp_tt (c : ℚ) (hc : 0 < c) (T : TwoTermData Fr q o) {nm : ℕ}
    (hnorm : Fr.norm = (nm : ℚ)) (r p K j : ℕ) [Fact p.Prime] (hr : r % 2 = 0) (hr0 : 0 < r)
    (hm1 : 1 ≤ (altGeom c hc).borderSize r) (hsq : q * (r + p) ≤ p * p)
    (hpm : 2 * (altGeom c hc).borderSize r ≤ p) (hpn : ¬ p ∣ nm) (hp2 : 2 < p) (hqp : q < p)
    (hK : q * K = j * p + o) (hj0 : 0 < j) (hjq : j < q) :
    ClosedHyp c hc Fr q o r p K := by
  have ho := T.o_pos
  have hoq := T.o_lt
  have hn := norm_good hnorm hpn
  have hNp : r + p < p * p := by
    have h2 : 2 * (r + p) ≤ q * (r + p) := Nat.mul_le_mul_right _ (by omega)
    omega
  have hK1 : 1 ≤ K := by
    by_contra h
    have h0 : K = 0 := by omega
    subst h0
    rw [mul_zero] at hK
    omega
  have hKp : K < p := by
    have h1 : (j + 1) * p ≤ q * p := Nat.mul_le_mul_right p hjq
    have h2 : q * K < q * p := by rw [add_one_mul] at h1; omega
    exact Nat.lt_of_mul_lt_mul_left h2
  exact
    { hr2 := hr
      hr0 := hr0
      hm1 := hm1
      hNp := hNp
      hpm := hpm
      hp2 := hp2
      hq0 := by omega
      hqp := hqp
      hsq := not_sq_dvd_of_qN T hsq
      hnorm := hn.1
      hnorm0 := hn.2
      hρ := ⟨j, by rw [Nat.mul_comm p j]; omega⟩
      hρ1 := hK1
      hρp := hKp }

/-- **UF branch** of the root class `j`: a member is cleared by `closedPrice m r p k` plus its
deletion count. -/
theorem uf_gle_tt (c : ℚ) (hc : 0 < c) (T : TwoTermData Fr q o) {nm : ℕ}
    (hnorm : Fr.norm = (nm : ℚ)) (depth : ℕ) (i : ((altGeom c hc).family Fr depth).ι)
    (hi : ((altGeom c hc).family Fr depth).Adm i) (hr : i.1 % 2 = 0) (hr0 : 0 < i.1)
    (p k j : ℕ) [Fact p.Prime] (hm1 : 1 ≤ (altGeom c hc).borderSize i.1)
    (hsq : q * (i.1 + p) ≤ p * p) (hpm : 2 * (altGeom c hc).borderSize i.1 ≤ p) (hpn : ¬ p ∣ nm)
    (hp2 : 2 < p) (hqp : q < p) (hk : q * k = j * p + o) (hj0 : 0 < j) (hjq : j < q) :
    GLE p (closedPrice ((altGeom c hc).borderSize i.1) i.1 p k + delCount (altGeom c hc) i)
      (((altGeom c hc).family Fr depth).Q i) := by
  have hH := closedHyp_tt c hc T hnorm i.1 p k j hr hr0 hm1 hsq hpm hpn hp2 hqp hk hj0 hjq
  have hv : ∀ r' p' : ℕ, ∀ [Fact p'.Prime], (r' = i.1 ∧ p' = p) →
      ClosedHyp c hc Fr q o r' p' ((fun _ => k) p') := by
    intro r' p' _ h
    obtain ⟨rfl, rfl⟩ := h
    exact hH
  have hg := (ufClosedLayer (c := c) (hc := hc) (depth := depth) T
    (fun r' p' => r' = i.1 ∧ p' = p) (fun _ => k) hv).gle i hi p ⟨rfl, rfl⟩
  refine hg.mono (le_of_eq ?_)
  show closedPrice ((altGeom c hc).borderSize i.1) i.1 p k + 1 * delCount (altGeom c hc) i = _
  rw [one_mul]

end CatalanCore.Uniform.Content.BankShared.TwoTerm
