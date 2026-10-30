module
public import CatalanMeasure.GenD.Uniform.W.Lucas.Cell
public import CatalanMeasure.GenD.Uniform.W.Combine
@[expose] public section
set_option Elab.async false

/-!
# Theorem A as a `NullityLB`

For a J-affine cell `c`, `aCond c P N p lo hi` collects the (linear) conditions under which the
positions `[lo, hi)` lie in the cell, and `aCount` is the largest such interval length.
`aCellLB c hc P hP` is the nullity lower bound `aCount - (2p - h)` (for `p` coprime to `c.modulus`,
`p ≤ h ≤ q`, `2(h - p) < p`); `aCellLB_kap_ge` is the form consumed by the ledger windows.
-/

namespace CatalanMeasure.GenD.Uniform.W.Lucas
open Module Polynomial CatalanMeasure.Parametric OAI.InternalCatalan CatalanMeasure.GenD
  CatalanMeasure.GenD.Uniform.W
noncomputable section

/-- Linear conditions for the interval `[lo, hi)` of positions of the cell `c`. -/
def aCond (c : ACell) (P : Parameters) (N p lo hi : ℕ) : Prop :=
  p ≤ P.h N ∧ P.h N ≤ P.q N ∧ 2 * (P.h N - p) < p ∧
  lo ≤ hi ∧ hi ≤ p ∧ P.h N - p ≤ hi ∧ hi - (P.h N - p) ≤ (p - 1) / 2 ∧
  -(P.g N : ℤ) ≤ c.k0 * p - ((hi - (P.h N - p) : ℕ) : ℤ) ∧
  (c.k0 + (c.K : ℤ) - 1) * p + ((hi - (P.h N - p) : ℕ) : ℤ) < (P.n N : ℤ) - P.g N ∧
  ∀ e, lo ≤ e → e < hi →
    c.S * p + e + 1 ≤ P.H N ∧ P.H N ≤ (c.S + 1) * p + e ∧
    (c.Jlo - 1) * p + (P.H N - 1 - e - c.S * p) < P.b N ∧
    P.L N ≤ (c.Jhi + 1) * p + (P.H N - 1 - e - c.S * p)

/-- The largest admissible interval length. -/
def aCount (c : ACell) (P : Parameters) (N p : ℕ) : ℕ :=
  open Classical in
  ((Finset.range (p + 1) ×ˢ Finset.range (p + 1)).filter
    fun lh => aCond c P N p lh.1 lh.2).sup fun lh => lh.2 - lh.1

/-- Theorem A for the cell `c`, as a nullity lower bound. -/
def aCellLB (c : ACell) (hc : c.Affine) (P : Parameters) (hP : Admissible P) : NullityLB P :=
  NullityLB.ofWindow P (fun N p => Nat.Coprime p c.modulus ∧ p ≤ P.q N)
    (fun N p => aCount c P N p - (2 * p - P.h N)) (by
    intro N p hN hp hp2 hH hApp
    classical
    obtain ⟨hcop, hpq⟩ := hApp
    haveI : Fact p.Prime := ⟨hp⟩
    have hbound : aCount c P N p ≤ nullity P N p + (2 * p - P.h N) := by
      unfold aCount
      apply Finset.sup_le
      intro lh hlh
      rw [Finset.mem_filter] at hlh
      obtain ⟨_, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hlh
      have := cellA_family hP hN hH hpq h0 h1 h2 c hc hcop h3 h4 h5 h6 h7 h8 h9
      omega
    omega)

theorem aCellLB_kap_ge (c : ACell) (hc : c.Affine) (P : Parameters) (hP : Admissible P)
    {N p lo hi : ℕ} (hcop : Nat.Coprime p c.modulus) (hpq : p ≤ P.q N)
    (hcd : aCond c P N p lo hi) :
    hi - lo - (2 * p - P.h N) ≤ (aCellLB c hc P hP).kap N p := by
  classical
  unfold aCellLB NullityLB.ofWindow
  simp only
  rw [if_pos ⟨hcop, hpq⟩]
  have hmem : (lo, hi) ∈ (Finset.range (p + 1) ×ˢ Finset.range (p + 1)).filter
      fun lh => aCond c P N p lh.1 lh.2 := by
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range]
    exact ⟨⟨by have := hcd.2.2.2.1; have := hcd.2.2.2.2.1; omega,
      by have := hcd.2.2.2.2.1; omega⟩, hcd⟩
  have := Finset.le_sup (f := fun lh : ℕ × ℕ => lh.2 - lh.1) hmem
  unfold aCount
  simp only at this ⊢
  omega

end
end CatalanMeasure.GenD.Uniform.W.Lucas
