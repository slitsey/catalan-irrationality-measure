import CatalanCore.Uniform.Bank.Chi3Rank.Pair2
set_option Elab.async false

/-! # Node sets of the common-minor member and the `Realizes` criterion (lane H, H16) -/

namespace CatalanCore.Uniform.Bank.Chi3Rank
open Polynomial Finset Module Matrix CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Uniform.Content.Hybrid CatalanCore.Uniform.Content.Member
  CatalanCore.Uniform.Content.RankProducer

open scoped Classical

/-- `n` is a retained common node. -/
def keptN (r : ℕ) (s : Finset (Fin r)) (n : ℕ) : Prop := ∃ h : n < r, (⟨n, h⟩ : Fin r) ∈ s

/-- Row nodes of the common-minor member. -/
abbrev rowsOf (r m : ℕ) (s : Finset (Fin r)) : s ⊕ Fin m → ℕ :=
  memberRows (fun c : Fin r => (c : ℕ)) (fun j : Fin m => r + 2 * (j : ℕ)) s

/-- Column nodes of the common-minor member. -/
abbrev colsOf (r m : ℕ) (s : Finset (Fin r)) : s ⊕ Fin m → ℕ :=
  memberCols (fun c : Fin r => (c : ℕ)) (fun j : Fin m => r + 2 * (j : ℕ) + 1) s

theorem rowN_iff (r m : ℕ) (s : Finset (Fin r)) (n : ℕ) :
    (∃ i, rowsOf r m s i = n) ↔ keptN r s n ∨ (r ≤ n ∧ n < r + 2 * m ∧ (n - r) % 2 = 0) := by
  constructor
  · rintro ⟨i, rfl⟩
    rcases i with ⟨c, hc⟩ | j
    · have e : rowsOf r m s (Sum.inl ⟨c, hc⟩) = (c : ℕ) := rfl
      rw [e]
      exact Or.inl ⟨c.2, by simpa using hc⟩
    · right
      simp only [rowsOf, memberRows, Sum.elim_inr]
      have := j.2
      refine ⟨by omega, by omega, by omega⟩
  · rintro (⟨h, hs⟩ | ⟨h1, h2, h3⟩)
    · exact ⟨Sum.inl ⟨⟨n, h⟩, hs⟩, rfl⟩
    · refine ⟨Sum.inr ⟨(n - r) / 2, by omega⟩, ?_⟩
      simp only [rowsOf, memberRows, Sum.elim_inr]
      omega

theorem colN_iff (r m : ℕ) (s : Finset (Fin r)) (n : ℕ) :
    (∃ i, colsOf r m s i = n) ↔
      keptN r s n ∨ (r + 1 ≤ n ∧ n < r + 2 * m ∧ (n - r - 1) % 2 = 0) := by
  constructor
  · rintro ⟨i, rfl⟩
    rcases i with ⟨c, hc⟩ | j
    · have e : colsOf r m s (Sum.inl ⟨c, hc⟩) = (c : ℕ) := rfl
      rw [e]
      exact Or.inl ⟨c.2, by simpa using hc⟩
    · right
      simp only [colsOf, memberCols, Sum.elim_inr]
      have := j.2
      refine ⟨by omega, by omega, by omega⟩
  · rintro (⟨h, hs⟩ | ⟨h1, h2, h3⟩)
    · exact ⟨Sum.inl ⟨⟨n, h⟩, hs⟩, rfl⟩
    · refine ⟨Sum.inr ⟨(n - r - 1) / 2, by omega⟩, ?_⟩
      simp only [colsOf, memberCols, Sum.elim_inr]
      omega

theorem rows_inj (r m : ℕ) (s : Finset (Fin r)) : Function.Injective (rowsOf r m s) := by
  intro i j h
  rcases i with ⟨c, hc⟩ | i <;> rcases j with ⟨d, hd⟩ | j <;>
    simp only [rowsOf, memberRows, Sum.elim_inl, Sum.elim_inr] at h
  · exact congrArg Sum.inl (Subtype.ext (Fin.ext h))
  · have := c.2; have := j.2; omega
  · have := d.2; have := i.2; omega
  · exact congrArg Sum.inr (Fin.ext (by omega))

theorem cols_inj (r m : ℕ) (s : Finset (Fin r)) : Function.Injective (colsOf r m s) := by
  intro i j h
  rcases i with ⟨c, hc⟩ | i <;> rcases j with ⟨d, hd⟩ | j <;>
    simp only [colsOf, memberCols, Sum.elim_inl, Sum.elim_inr] at h
  · exact congrArg Sum.inl (Subtype.ext (Fin.ext h))
  · have := c.2; have := j.2; omega
  · have := d.2; have := i.2; omega
  · exact congrArg Sum.inr (Fin.ext (by omega))

theorem rows_le (r m : ℕ) (s : Finset (Fin r)) (i : s ⊕ Fin m) : rowsOf r m s i ≤ r + 2 * m := by
  rcases i with ⟨c, hc⟩ | j
  · have := c.2; simp only [rowsOf, memberRows, Sum.elim_inl]; omega
  · have := j.2; simp only [rowsOf, memberRows, Sum.elim_inr]; omega

theorem cols_le (r m : ℕ) (s : Finset (Fin r)) (i : s ⊕ Fin m) : colsOf r m s i ≤ r + 2 * m := by
  rcases i with ⟨c, hc⟩ | j
  · have := c.2; simp only [colsOf, memberCols, Sum.elim_inl]; omega
  · have := j.2; simp only [colsOf, memberCols, Sum.elim_inr]; omega

section Realize
variable {p : ℕ} [hp : Fact p.Prime] {ι : Type*} [Fintype ι] [DecidableEq ι] {B : ℕ} {f e : ℕ → ℚ}

theorem add_mul_div_digit (x0 d : ℕ) (hx0 : x0 < p) : (x0 + p * d) / p = d := by
  rw [Nat.add_mul_div_left _ _ hp.out.pos, Nat.div_eq_of_lt hx0, zero_add]

theorem cast_node (x0 d : ℕ) : ((x0 + p * d : ℕ) : ZMod p) = (x0 : ZMod p) := by
  push_cast; simp

/-- **`Realizes` from node-level facts.** -/
theorem realizes_of (PS : PoleSplit p B f e) (a b : ι → ℕ) (x0 : ℕ) (hx0 : x0 < p)
    (c : FibreCert)
    (hrm : ∀ i, a i % p = x0 → a i / p ∈ c.R)
    (hrc : ∀ d ∈ c.R, ∃ i, a i = x0 + p * d)
    (hcm : ∀ j, b j % p = x0 → b j / p ∈ c.C)
    (hcc : ∀ d ∈ c.C, ∃ j, b j = x0 + p * d)
    (hlfr : ∀ i, a i % p = x0 → PS.Lf (a i) = c.lf (a i / p))
    (hlfc : ∀ j, b j % p = x0 → PS.Lf (b j) = c.lf (b j / p))
    (hee : ∀ i, a i % p = x0 → PS.E (a i) = c.ee (a i / p)) :
    Realizes PS a b (x0 : ZMod p) c := by
  have hmod : ∀ n : ℕ, (n : ZMod p) = (x0 : ZMod p) → n % p = x0 := fun n h => by
    rw [natCast_eq_of_mod h, Nat.mod_eq_of_lt hx0]
  refine ⟨fun i h => hrm i (hmod _ h), fun d hd => ?_, fun j h => hcm j (hmod _ h),
    fun d hd => ?_, fun i h => hlfr i (hmod _ h), fun j h => hlfc j (hmod _ h),
    fun i h => hee i (hmod _ h)⟩
  · obtain ⟨i, hi⟩ := hrc d hd
    exact ⟨i, by rw [hi]; exact cast_node x0 d, by rw [hi]; exact add_mul_div_digit x0 d hx0⟩
  · obtain ⟨j, hj⟩ := hcc d hd
    exact ⟨j, by rw [hj]; exact cast_node x0 d, by rw [hj]; exact add_mul_div_digit x0 d hx0⟩

end Realize

end CatalanCore.Uniform.Bank.Chi3Rank
