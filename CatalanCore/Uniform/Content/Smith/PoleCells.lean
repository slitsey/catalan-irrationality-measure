module

public import CatalanCore.Uniform.Content.Smith.PoleTransfer

@[expose] public section

/-!
# PTg in cell form

The cumulative-coefficient form `ptg` is equivalent to the cell form of the paper: for pole indices
`k_0 ≤ k_1 ≤ … ≤ k_{n-1} ≤ k_n := p` and a balanced frame,

  `F(w) - F(u) = -(w - u) Σ_{j<n} C_j Σ_{x ∈ [k_j, k_{j+1})} 1/((x-u)(x-w))`,   `C_j = c_0 + … + c_j`

(the last cell is multiplied by `C_{n-1} = 0`).
-/

open Finset

namespace CatalanCore.Uniform.Content.Smith

variable {p : ℕ} [Fact p.Prime]

lemma ico_cells (k : ℕ → ℕ) (g : ℕ → ZMod p) {n : ℕ} (hmono : ∀ i j, i ≤ j → j ≤ n → k i ≤ k j) :
    ∀ d i, i + d = n →
      ∑ x ∈ Ico (k i) (k n), g x = ∑ j ∈ Ico i n, ∑ x ∈ Ico (k j) (k (j + 1)), g x := by
  intro d
  induction d with
  | zero => intro i hi; subst hi; simp
  | succ d ih =>
    intro i hi
    have hin : i < n := by omega
    rw [Finset.sum_eq_sum_Ico_succ_bot hin, ← ih (i + 1) (by omega),
      Finset.sum_Ico_consecutive _ (hmono i (i + 1) (by omega) (by omega))
        (hmono (i + 1) n (by omega) le_rfl)]

lemma abel_cells (c S : ℕ → ZMod p) (n : ℕ) :
    ∑ i ∈ range n, c i * ∑ j ∈ Ico i n, S j =
      ∑ j ∈ range n, (∑ i ∈ range (j + 1), c i) * S j := by
  calc ∑ i ∈ range n, c i * ∑ j ∈ Ico i n, S j
      = ∑ i ∈ range n, ∑ j ∈ Ico i n, c i * S j :=
        Finset.sum_congr rfl fun i _ => Finset.mul_sum _ _ _
    _ = ∑ j ∈ range n, ∑ i ∈ range (j + 1), c i * S j := by
        refine Finset.sum_comm' ?_
        intro i j
        simp only [mem_range, mem_Ico]
        omega
    _ = ∑ j ∈ range n, (∑ i ∈ range (j + 1), c i) * S j :=
        Finset.sum_congr rfl fun j _ => (Finset.sum_mul _ _ _).symm

/-- **Lemma PTg, cell form.** -/
theorem ptg_cells {n : ℕ} (k : ℕ → ℕ) (c : ℕ → ZMod p)
    (hmono : ∀ i j, i ≤ j → j ≤ n → k i ≤ k j) (hlast : k n = p)
    (hbal : ∑ i ∈ range n, c i = 0) {u w : ℕ} (huw : u < w) (hk : ∀ i < n, w < k i) :
    modF (fun i : Fin n => k i) (fun i : Fin n => c i) w -
        modF (fun i : Fin n => k i) (fun i : Fin n => c i) u =
      -(((w : ZMod p) - (u : ZMod p)) * ∑ j ∈ range n, (∑ i ∈ range (j + 1), c i) *
        ∑ x ∈ Ico (k j) (k (j + 1)), cauchyKer (p := p) u w x) := by
  have hbal' : ∑ i : Fin n, c i = 0 := by
    rw [Fin.sum_univ_eq_sum_range (fun i => c i) n]; exact hbal
  have hkp : ∀ i : Fin n, k i ≤ p := fun i => hlast ▸ hmono i n i.2.le le_rfl
  rw [ptg (fun i : Fin n => k i) (fun i : Fin n => c i) hbal' huw (fun i => hk i i.2) hkp]
  congr 2
  -- Σ_x cum x g x = Σ_i c_i T_i
  have hico : ∀ i : Fin n, ∑ x ∈ Ico (k i) p, cauchyKer (p := p) u w x =
      ∑ x ∈ range p, if k i ≤ x then cauchyKer (p := p) u w x else 0 := by
    intro i
    rw [← Finset.sum_filter]
    congr 1
    ext x; simp only [mem_Ico, mem_filter, mem_range]; have := hkp i; omega
  have hcs : ∑ x ∈ range p, cum (fun i : Fin n => k i) (fun i : Fin n => c i) x *
        cauchyKer (p := p) u w x =
      ∑ i : Fin n, c i * ∑ x ∈ Ico (k i) p, cauchyKer (p := p) u w x := by
    simp_rw [hico, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    unfold cum
    rw [Finset.sum_mul, Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> simp
  rw [hcs]
  -- Abel summation over the cells
  have hT : ∀ i : ℕ, i ≤ n → ∑ x ∈ Ico (k i) p, cauchyKer (p := p) u w x =
      ∑ j ∈ Ico i n, ∑ x ∈ Ico (k j) (k (j + 1)), cauchyKer (p := p) u w x := by
    intro i hi
    have := ico_cells k (cauchyKer (p := p) u w) hmono (n - i) i (by omega)
    rw [hlast] at this
    exact this
  rw [Fin.sum_univ_eq_sum_range (fun i => c i * ∑ x ∈ Ico (k i) p, cauchyKer (p := p) u w x) n]
  rw [Finset.sum_congr rfl (fun i hi => by rw [hT i (mem_range.1 hi).le])]
  exact abel_cells c (fun j => ∑ x ∈ Ico (k j) (k (j + 1)), cauchyKer (p := p) u w x) n


lemma cauchyKer_comm' (u w x : ℕ) : cauchyKer (p := p) u w x = cauchyKer (p := p) w u x := by
  unfold cauchyKer; ring

/-! ### PT as a Schur complement -/

/-- The level-zero Loewner kernel of the two-term frame `1/j - 1/(j-k)` modulo `p`
(off-diagonal `(F(b)-F(a))/(b-a)`, diagonal `E(a)`). -/
def loewK (k u w : ℕ) : ZMod p :=
  if u < w then (F2 (p := p) k w - F2 (p := p) k u) / ((w : ZMod p) - (u : ZMod p))
  else if w < u then (F2 (p := p) k u - F2 (p := p) k w) / ((u : ZMod p) - (w : ZMod p))
  else E2 (p := p) k u

/-- **Lemma PT (Schur form).**  Eliminating the level-one block `[k, p)` (coupling `s/(c-u)`,
diagonal `s²`) cancels the Loewner block exactly: for `u, w < k ≤ p`, `p ≥ 5`,

  `M[u,w] - (s²)⁻¹ Σ_{c ∈ [k,p)} (s/(c-u)) (s/(c-w)) = δ_{uw} H^{(2)}_{k-1}`,

so the Schur complement of `x I + M` is `(x + H^{(2)}_{k-1}) I`. -/
theorem pt_schur (hp5 : 5 ≤ p) {k : ℕ} (hkp : k ≤ p) {s : ZMod p} (hs : s ≠ 0) {u w : ℕ}
    (hu : u < k) (hw : w < k) :
    loewK (p := p) k u w - (s ^ 2)⁻¹ * ∑ c ∈ Ico k p,
        (s * ((c : ZMod p) - u)⁻¹) * (s * ((c : ZMod p) - w)⁻¹) =
      if u = w then H2 (p := p) (k - 1) else 0 := by
  have hsum : (s ^ 2)⁻¹ * ∑ c ∈ Ico k p, (s * ((c : ZMod p) - u)⁻¹) * (s * ((c : ZMod p) - w)⁻¹) =
      ∑ c ∈ Ico k p, cauchyKer (p := p) u w c := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    unfold cauchyKer; field_simp
  rw [hsum]
  rcases lt_trichotomy u w with huw | huw | huw
  · rw [if_neg huw.ne]
    unfold loewK; rw [if_pos huw]
    rw [pt_loewner huw hw hkp (by omega)]; ring
  · subst huw
    rw [if_pos rfl]
    unfold loewK; rw [if_neg (lt_irrefl _), if_neg (lt_irrefl _)]
    have hd := pt_diag (p := p) hp5 hkp u
    have hsq : ∀ c : ℕ, cauchyKer (p := p) u u c = ((((c : ZMod p) - u)⁻¹) ^ 2) := by
      intro c; unfold cauchyKer; ring
    simp_rw [hsq]; exact hd
  · rw [if_neg huw.ne']
    unfold loewK; rw [if_neg (not_lt.2 huw.le), if_pos huw]
    rw [pt_loewner huw hu hkp (by omega)]
    simp_rw [cauchyKer_comm' w u]; ring

end CatalanCore.Uniform.Content.Smith
