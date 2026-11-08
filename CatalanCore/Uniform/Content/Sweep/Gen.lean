module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Data.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

@[expose] public section

/-!
# Lemma G in a ring with `P² = 0` (lane H, wave H2b; ledger P204)

The generator lemma of `PLANE2-P1-ROW` §3, as pure algebra.  `S` is a commutative ring with an element
`P` (the image of `p`) with `P² = 0`; nodes are natural numbers `t = j p + ω` (`ω < p`); `Cper o` are the
periods carrying a pivot column of a residue of class `o ∈ {0,1}` (`oc ω`: the class of the residue
`ω`, by the parity of `κ p + ω`), and `PCs` is the set of pivot columns, organised by residue.

Inputs (all verified for the plane 2 matrix in `PivotG`): the congruent entries are the period matrix
`Bm` (F1), the non-congruent ones are `P (σ(c_t) - σ(c_u)) dd(ω_u, ω_t)` (F2), `Bm` is symmetric, the two
halves agree modulo `P` (`hsgh`, `hYh`), `P ∑_{a ≠ ω} dd(ω, a) = 0` (`hdd`), and `Yv b h o` solves the class
equations `∑_{j ∈ C_o} Bm h l j Yv b h o j = Γ^b_h(l)` for `l ∈ C_{1-o}`.

* `Psi_one`: `Ψ_1[a,b] = Ψ_0[b,a]` (double-sum swap, no inverse).
* `lemmaG`: with `ε(ω) = 1 - P δ E(ω)`, `Θ^b(t) = ε(ω_t) Yv b (half t) (oc ω_t) (⌊t/p⌋)`,
  `∑_{t ∈ PC} q(u,t) Θ^b(t) = ε(ω_u) β^b(u) + P δ E(ω_u) Γ^b(u)` for every node `u`.
-/
open Finset

namespace CatalanCore.Uniform.Content.Sweep.Gen

/-! ### Periods and residues -/

section Comb

variable (p κ k' π : ℕ)

/-- The column periods of a class `o ∈ {0,1}`: `[0,κ)` and the periods `κ + i` with `i < 2k'`, `i ≡ o`. -/
def Cper (o : ℕ) : Finset ℕ :=
  range κ ∪ ((range (2 * k')).filter (fun i => i % 2 = o)).image (fun i => κ + i)

/-- The class of a residue: `0` if the node `κ p + ω` has the column parity `π`, else `1`. -/
def oc (ω : ℕ) : ℕ := if (κ * p + ω) % 2 = π then 0 else 1

theorem mem_Cper {o j : ℕ} : j ∈ Cper κ k' o ↔ j < κ + 2 * k' ∧ (j < κ ∨ (j - κ) % 2 = o) := by
  unfold Cper
  simp only [Finset.mem_union, Finset.mem_range, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro (h | ⟨i, ⟨hi, hio⟩, rfl⟩)
    · exact ⟨by omega, Or.inl h⟩
    · exact ⟨by omega, Or.inr (by simpa using hio)⟩
  · rintro ⟨h1, h2 | h2⟩
    · exact Or.inl h2
    · by_cases hk : j < κ
      · exact Or.inl hk
      · exact Or.inr ⟨j - κ, ⟨by omega, h2⟩, by omega⟩

/-- The pivot columns, organised by residue. -/
def PCs : Finset ℕ :=
  (((range p).sigma fun ω => Cper κ k' (oc p κ π ω)).image fun x => x.2 * p + x.1)

theorem PCs_sum {α : Type*} [AddCommMonoid α] (hp : 0 < p) (F : ℕ → α) :
    ∑ t ∈ PCs p κ k' π, F t =
      ∑ ω ∈ range p, ∑ j ∈ Cper κ k' (oc p κ π ω), F (j * p + ω) := by
  unfold PCs
  rw [Finset.sum_image, Finset.sum_sigma]
  rintro ⟨ω, j⟩ h ⟨ω', j'⟩ h' he
  simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_range] at h h'
  simp only at he
  have h1 : (j * p + ω) % p = ω := by rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h.1]
  have h2 : (j' * p + ω') % p = ω' := by rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h'.1]
  have h3 : (j * p + ω) / p = j := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hp, Nat.div_eq_of_lt h.1]; simp
  have h4 : (j' * p + ω') / p = j' := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hp, Nat.div_eq_of_lt h'.1]; simp
  have : ω = ω' := by rw [← h1, ← h2, he]
  have : j = j' := by rw [← h3, ← h4, he]
  subst_vars; rfl

end Comb


/-! ### Lemma G in a ring with `P² = 0` -/

section LemmaG

variable {S : Type*} [CommRing S] (P : S) (p κ k' π : ℕ) (sg dd : ℕ → ℕ → S) (Yv : ℕ → ℕ → ℕ → ℕ → S)

/-- The generator of the vector index `b` at the cell `(l, h)`: `1` or `σ(l, h)`. -/
def Gam (b h l : ℕ) : S := if b = 0 then 1 else sg l h

/-- `Ψ_o[a, b] = ∑_{j ∈ C_o} Γ^a(j) Y^b_{0,o}(j)` (half `0`). -/
def Psi (o a b : ℕ) : S := ∑ j ∈ Cper κ k' o, Gam sg a 0 j * Yv b 0 o j

/-- `δ = Ψ_0[1,0] - Ψ_0[0,1]`. -/
def delta : S := Psi κ k' sg Yv 0 1 0 - Psi κ k' sg Yv 0 0 1

/-- `E(ω) = ∑_{ω' ≠ ω, o(ω') = 0} (ω' - ω)⁻¹`. -/
def Eres (ω : ℕ) : S :=
  ∑ a ∈ ((range p).erase ω).filter (fun a => oc p κ π a = 0), dd ω a

/-- `ε(ω) = 1 - p δ E(ω)`. -/
def eps (ω : ℕ) : S := 1 - P * delta κ k' sg Yv * Eres p κ π dd ω

variable {κ k'}

/-- **Antisymmetry** (`Ψ_1[a,b] = Ψ_0[b,a]`): the two class equations and the symmetry of `B`. -/
theorem Psi_one (Bm : ℕ → ℕ → ℕ → S) (hSym : ∀ h l j, Bm h l j = Bm h j l)
    (hclass : ∀ b h o, o ≤ 1 → ∀ l ∈ Cper κ k' (1 - o),
      ∑ j ∈ Cper κ k' o, Bm h l j * Yv b h o j = Gam sg b h l) (a b : ℕ) :
    Psi κ k' sg Yv 1 a b = Psi κ k' sg Yv 0 b a := by
  unfold Psi
  have h1 : ∀ j ∈ Cper κ k' 1, Gam sg a 0 j * Yv b 0 1 j =
      ∑ l ∈ Cper κ k' 0, Bm 0 j l * Yv a 0 0 l * Yv b 0 1 j := by
    intro j hj
    rw [← hclass a 0 0 (by norm_num) j (by simpa using hj), Finset.sum_mul]
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun l hl => ?_
  have h2 : ∑ j ∈ Cper κ k' 1, Bm 0 j l * Yv a 0 0 l * Yv b 0 1 j =
      Yv a 0 0 l * ∑ j ∈ Cper κ k' 1, Bm 0 l j * Yv b 0 1 j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hSym 0 j l]; ring
  rw [h2, hclass b 0 1 (by norm_num) l (by simpa using hl)]
  ring




theorem node_mod {p j ω : ℕ} (hω : ω < p) : (j * p + ω) % p = ω := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hω]

theorem node_div {p j ω : ℕ} (hp : 0 < p) (hω : ω < p) : (j * p + ω) / p = j := by
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ hp, Nat.div_eq_of_lt hω]; simp

theorem mem_PCs {t : ℕ} (hp : 0 < p) :
    t ∈ PCs p κ k' π ↔ t / p ∈ Cper κ k' (oc p κ π (t % p)) := by
  unfold PCs
  simp only [Finset.mem_image, Finset.mem_sigma, Finset.mem_range]
  constructor
  · rintro ⟨⟨ω, j⟩, ⟨h1, h2⟩, rfl⟩
    simp only at h1 h2 ⊢
    rw [node_mod h1, node_div hp h1]
    exact h2
  · intro h
    exact ⟨⟨t % p, t / p⟩, ⟨Nat.mod_lt _ hp, h⟩, by simp only; rw [Nat.mul_comm]; exact Nat.div_add_mod t p⟩

theorem mem_PCs_of {ω j : ℕ} (hp : 0 < p) (hω : ω < p) (hj : j ∈ Cper κ k' (oc p κ π ω)) :
    j * p + ω ∈ PCs p κ k' π := by
  rw [mem_PCs (p := p) (κ := κ) (k' := k') (π := π) hp, node_mod hω, node_div hp hω]
  exact hj

theorem term_red (hP : P * P = 0) (c e y yh a ah s d : S) (he : e = 1 - P * c)
    (ha : P * ah = P * a) (hy : P * yh = P * y) :
    P * (ah - s) * d * (e * yh) = P * (a - s) * d * y := by
  subst he
  linear_combination (d * yh) * ha + ((a - s) * d) * hy - (c * (ah - s) * d * yh) * hP

theorem oc_cases (p κ π ω : ℕ) : oc p κ π ω = 0 ∨ oc p κ π ω = 1 := by
  unfold oc; split_ifs <;> simp

theorem lemmaG (hP : P * P = 0) (hp : 0 < p) (N' : ℕ) (hf : ℕ → ℕ)
    (hhf : ∀ t, hf t = hf (t % p)) (hhf1 : ∀ t, hf t ≤ 1)
    (q : ℕ → ℕ → S) (Bm : ℕ → ℕ → ℕ → S)
    (hF1 : ∀ u < N', ∀ t ∈ PCs p κ k' π, u % p = t % p → q u t = Bm (hf u) (u / p) (t / p))
    (hF2 : ∀ u < N', ∀ t ∈ PCs p κ k' π, u % p ≠ t % p →
      q u t = P * (sg (t / p) (hf t) - sg (u / p) (hf u)) * dd (u % p) (t % p))
    (hSym : ∀ h l j, Bm h l j = Bm h j l)
    (hsgh : ∀ j < κ + 2 * k', ∀ h ≤ 1, P * sg j h = P * sg j 0)
    (hYh : ∀ b o, o ≤ 1 → ∀ j ∈ Cper κ k' o, ∀ h ≤ 1, P * Yv b h o j = P * Yv b 0 o j)
    (hdd : ∀ ω < p, P * ∑ a ∈ (range p).erase ω, dd ω a = 0)
    (hclass : ∀ b h o, o ≤ 1 → ∀ l ∈ Cper κ k' (1 - o),
      ∑ j ∈ Cper κ k' o, Bm h l j * Yv b h o j = Gam sg b h l)
    (u : ℕ) (hu : u < N') (b : ℕ) (hb : b ≤ 1) :
    ∑ t ∈ PCs p κ k' π, q u t *
        (eps P p κ k' π sg dd Yv (t % p) * Yv b (hf t) (oc p κ π (t % p)) (t / p)) =
      eps P p κ k' π sg dd Yv (u % p) *
          (∑ j ∈ Cper κ k' (oc p κ π (u % p)), Bm (hf u) (u / p) j * Yv b (hf u) (oc p κ π (u % p)) j) +
        P * delta κ k' sg Yv * Eres p κ π dd (u % p) * Gam sg b (hf u) (u / p) := by
  classical
  obtain ⟨ω0, hω0⟩ : ∃ ω0, ω0 = u % p := ⟨_, rfl⟩
  have hω0p : ω0 < p := by rw [hω0]; exact Nat.mod_lt _ hp
  have hfu : hf u = hf ω0 := by rw [hhf u, hω0]
  rw [PCs_sum p κ k' π hp, ← Finset.add_sum_erase (range p) _ (Finset.mem_range.2 hω0p), ← hω0, hfu]
  have hfnode : ∀ j ω, ω < p → hf (j * p + ω) = hf ω := by
    intro j ω hω; rw [hhf, node_mod hω]
  -- congruent part
  have hcong : ∑ j ∈ Cper κ k' (oc p κ π ω0), q u (j * p + ω0) *
      (eps P p κ k' π sg dd Yv ((j * p + ω0) % p) *
        Yv b (hf (j * p + ω0)) (oc p κ π ((j * p + ω0) % p)) ((j * p + ω0) / p)) =
      eps P p κ k' π sg dd Yv ω0 *
        (∑ j ∈ Cper κ k' (oc p κ π ω0), Bm (hf ω0) (u / p) j * Yv b (hf ω0) (oc p κ π ω0) j) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hmem := mem_PCs_of (p := p) (κ := κ) (k' := k') (π := π) hp hω0p hj
    rw [hF1 u hu _ hmem (by rw [node_mod hω0p, hω0]), hfu, node_mod hω0p, node_div hp hω0p, hfnode j ω0 hω0p]
    ring
  -- the other residues
  set su := sg (u / p) (hf ω0) with hsu
  have hterm : ∀ ω ∈ (range p).erase ω0, ∑ j ∈ Cper κ k' (oc p κ π ω), q u (j * p + ω) *
      (eps P p κ k' π sg dd Yv ((j * p + ω) % p) *
        Yv b (hf (j * p + ω)) (oc p κ π ((j * p + ω) % p)) ((j * p + ω) / p)) =
      P * dd ω0 ω * (Psi κ k' sg Yv (oc p κ π ω) 1 b - su * Psi κ k' sg Yv (oc p κ π ω) 0 b) := by
    intro ω hω
    have hωp : ω < p := Finset.mem_range.1 (Finset.mem_of_mem_erase hω)
    have hne : ω ≠ ω0 := Finset.ne_of_mem_erase hω
    have hoc1 : oc p κ π ω ≤ 1 := by rcases oc_cases p κ π ω with h | h <;> omega
    unfold Psi Gam
    simp only [Nat.one_ne_zero, if_false, if_true, one_mul]
    rw [Finset.mul_sum _ _ su, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hmem := mem_PCs_of (p := p) (κ := κ) (k' := k') (π := π) hp hωp hj
    have hjlt : j < κ + 2 * k' := ((mem_Cper (κ := κ) (k' := k')).1 hj).1
    rw [hF2 u hu _ hmem (by rw [node_mod hωp, ← hω0]; exact fun h => hne h.symm), hfnode j ω hωp,
      node_mod hωp, node_div hp hωp, ← hω0]
    have key := term_red P hP (delta κ k' sg Yv * Eres p κ π dd ω)
      (eps P p κ k' π sg dd Yv ω) (Yv b 0 (oc p κ π ω) j) (Yv b (hf ω) (oc p κ π ω) j)
      (sg j 0) (sg j (hf ω)) su (dd ω0 ω)
      (by unfold eps; ring) (hsgh j hjlt (hf ω) (hhf1 ω)) (hYh b (oc p κ π ω) hoc1 j hj (hf ω) (hhf1 ω))
    rw [hfu, ← hsu]
    rw [key]; ring
  rw [hcong, Finset.sum_congr rfl hterm]
  set X0 := Psi κ k' sg Yv 0 1 b - su * Psi κ k' sg Yv 0 0 b with hX0
  set X1 := Psi κ k' sg Yv 1 1 b - su * Psi κ k' sg Yv 1 0 b with hX1
  have hX : ∀ ω, Psi κ k' sg Yv (oc p κ π ω) 1 b - su * Psi κ k' sg Yv (oc p κ π ω) 0 b =
      if oc p κ π ω = 0 then X0 else X1 := by
    intro ω
    rcases oc_cases p κ π ω with h | h
    · rw [h]; simp [hX0]
    · rw [h]; simp [hX1]
  have hsplit : ∑ ω ∈ (range p).erase ω0, P * dd ω0 ω *
      (Psi κ k' sg Yv (oc p κ π ω) 1 b - su * Psi κ k' sg Yv (oc p κ π ω) 0 b) =
      X1 * (P * ∑ ω ∈ (range p).erase ω0, dd ω0 ω) + (X0 - X1) * (P * Eres p κ π dd ω0) := by
    unfold Eres
    rw [Finset.sum_filter, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ω _ => ?_
    rw [hX ω]
    split_ifs <;> ring
  rw [hsplit, hdd ω0 hω0p]
  have hD : X0 - X1 = delta κ k' sg Yv * Gam sg b (hf ω0) (u / p) := by
    have e1 := Psi_one sg Yv Bm hSym hclass 1 b
    have e2 := Psi_one sg Yv Bm hSym hclass 0 b
    obtain rfl | rfl : b = 0 ∨ b = 1 := by omega
    · simp only [hX0, hX1, delta, Gam, if_true] at e1 e2 ⊢
      rw [e1, e2]; ring
    · simp only [hX0, hX1, delta, Gam, Nat.one_ne_zero, if_false] at e1 e2 ⊢
      rw [e1, e2, hsu]; ring
  rw [hD]
  ring

end LemmaG

end CatalanCore.Uniform.Content.Sweep.Gen

#print axioms CatalanCore.Uniform.Content.Sweep.Gen.lemmaG
