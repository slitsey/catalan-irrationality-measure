module

public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.Algebra.Polynomial.Taylor

@[expose] public section

/-!
# Barycentric identities for the pair sector

For a finite node set `Y` in a field and `wt Y b = 1/D'(b)` (`D = ∏_{b∈Y}(Z-b)`):

* `bary_off` : for `deg g < |Y|` and `a ∉ Y`,
  `∑_{b∈Y} wt b · g(b)/(a-b) = g(a)/D(a)`;
* `bary_node` : for `deg g < |Y|`, `a ∈ Y` and `g(a) = 0`,
  `∑_{b∈Y} wt b · g(b)/(a-b) = wt a · g'(a)` (the `b = a` term is `·/0 = 0`), with
  `g'(a)` the first Taylor coefficient.  No characteristic hypothesis is needed.

These are the row conditions (7) of the hybrid source after interpolation of the column loads:
an off-node row imposes a value condition, a shared node the DIRECTIONAL derivative condition.
-/

open Polynomial Finset Lagrange

namespace CatalanCore.Uniform.Content.Hybrid

variable {K : Type*} [Field K] [DecidableEq K]

/-- `1/D'(b)` for the node set `Y`. -/
noncomputable abbrev wt (Y : Finset K) (b : K) : K := nodalWeight Y id b

theorem bary_off (Y : Finset K) (g : K[X]) (hg : g.degree < #Y) {a : K} (ha : a ∉ Y) :
    ∑ b ∈ Y, wt Y b * g.eval b / (a - b) = g.eval a / (nodal Y id).eval a := by
  have hinj : Set.InjOn (id : K → K) (Y : Set K) := Set.injOn_id _
  have hx : ∀ i ∈ Y, a ≠ id i := fun i hi h => ha (h ▸ hi)
  have h1 := eq_interpolate hinj hg
  have h2 := eval_interpolate_not_at_node (s := Y) (v := id) (fun i => g.eval (id i)) hx
  rw [← h1] at h2
  have hD : (nodal Y id).eval a ≠ 0 := eval_nodal_not_at_node hx
  rw [h2, mul_div_cancel_left₀ _ hD]
  refine sum_congr rfl fun b _ => ?_
  simp only [id, div_eq_mul_inv]
  ring

lemma wt_erase {Y : Finset K} {a b : K} (ha : a ∈ Y) (hb : b ∈ Y) (hab : b ≠ a) :
    wt Y b = (b - a)⁻¹ * wt (Y.erase a) b := by
  simp only [wt, nodalWeight, id]
  have hmem : a ∈ Y.erase b := Finset.mem_erase.2 ⟨hab.symm, ha⟩
  rw [← Finset.mul_prod_erase _ _ hmem, Finset.erase_right_comm]

theorem bary_node (Y : Finset K) (g : K[X]) (hg : g.degree < #Y) {a : K} (ha : a ∈ Y)
    (hga : g.eval a = 0) :
    ∑ b ∈ Y, wt Y b * g.eval b / (a - b) = wt Y a * (taylor a g).coeff 1 := by
  -- factor `g = (Z - a) g₁`
  set g₁ := g /ₘ (X - C a) with hg₁
  have hfac : (X - C a) * g₁ = g := (mul_divByMonic_eq_iff_isRoot).2 hga
  have hcard : #(Y.erase a) + 1 = #Y := Finset.card_erase_add_one ha
  have hg₁deg : g₁.degree < #(Y.erase a) := by
    by_cases h0 : g₁ = 0
    · rw [h0, degree_zero]; exact WithBot.bot_lt_coe _
    · have hd : g.degree = 1 + g₁.degree := by
        rw [← hfac, degree_mul, degree_X_sub_C]
      have hgne : g ≠ 0 := by
        intro h; rw [h, mul_eq_zero] at hfac
        rcases hfac with h' | h'
        · exact X_sub_C_ne_zero a h'
        · exact h0 h'
      rw [degree_eq_natDegree h0] at hd ⊢
      rw [degree_eq_natDegree hgne] at hd hg
      have hd' : g.natDegree = 1 + g₁.natDegree := by exact_mod_cast hd
      have hg' : g.natDegree < #Y := by exact_mod_cast hg
      exact_mod_cast (show g₁.natDegree < #(Y.erase a) by omega)
  have hoff := bary_off (Y.erase a) g₁ hg₁deg (Finset.notMem_erase a Y)
  -- the `b = a` term vanishes
  rw [← Finset.add_sum_erase _ _ ha, sub_self, div_zero, zero_add]
  have hterm : ∀ b ∈ Y.erase a, wt Y b * g.eval b / (a - b) = wt (Y.erase a) b * g₁.eval b / (a - b) := by
    intro b hb
    have hb' := Finset.mem_erase.1 hb
    rw [wt_erase ha hb'.2 hb'.1, ← hfac, eval_mul, eval_sub, eval_X, eval_C]
    have : b - a ≠ 0 := sub_ne_zero.2 hb'.1
    field_simp
  rw [Finset.sum_congr rfl hterm, hoff]
  -- `D₀(a) = 1/wt a` and `g'(a) = g₁(a)`
  have hw : (nodal (Y.erase a) id).eval a = (wt Y a)⁻¹ := by
    rw [wt, nodalWeight_eq_eval_nodal_erase_inv, inv_inv]; rfl
  have hco : (taylor a g).coeff 1 = g₁.eval a := by
    rw [← hfac, taylor_mul, map_sub, taylor_X, taylor_C, add_sub_cancel_right, coeff_X_mul,
      taylor_coeff_zero]
  rw [hw, hco, div_inv_eq_mul, mul_comm]

end CatalanCore.Uniform.Content.Hybrid
