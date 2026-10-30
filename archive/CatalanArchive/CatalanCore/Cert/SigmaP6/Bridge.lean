module

public import CatalanLambda.Decay.ThmNCert
public import CatalanLambda.Decay.ThmNUtauForm
public import CatalanCore.Cert.SigmaP6.SegLine

@[expose] public section

/-!
# Bridge between the list-based `Cert` functions and the `Fin 699`-based `Decay` functions

`cS, mS : Fin 699 → ...` enumerate the sorted sigma list `sigD`.
-/

open Real

set_option maxRecDepth 100000

namespace CatalanCore.Cert.SigmaP6

open CatalanLambda.Cert

def ptAt (k : ℕ) : Pt := sigD.getD k (0, 0, 0)

noncomputable def cS (k : Fin 699) : ℂ := ⟨((ptAt k).1 : ℝ) / 2 ^ 40, ((ptAt k).2.1 : ℝ) / 2 ^ 40⟩
noncomputable def mS (k : Fin 699) : ℝ := ((ptAt k).2.2 : ℝ) / 2 ^ 32

theorem sigD_len : sigD.length = 699 := by decide +kernel

lemma sigD_ofFn : sigD = List.ofFn (fun k : Fin 699 => ptAt k) := by
  apply List.ext_getElem
  · rw [List.length_ofFn]; exact sigD_len
  · intro n h1 h2
    have h3 : n < sigD.length := h1
    rw [List.getElem_ofFn]
    unfold ptAt
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h3]
    rfl

lemma sum_sigma (f : Pt → ℝ) : ∑ k : Fin 699, f (ptAt k) = (sigD.map f).sum := by
  conv_rhs => rw [sigD_ofFn, List.map_ofFn, List.sum_ofFn]
  rfl

lemma Usig_eq_sum (l : List Pt) (x y : ℝ) :
    Usig l x y = (l.map (fun p => (p.2.2 : ℝ) / 2 ^ 32 * (-(1 / 2) * Real.log
      ((x - (p.1 : ℝ) / 2 ^ 40) ^ 2 + (y - (p.2.1 : ℝ) / 2 ^ 40) ^ 2 + (1 / 2048) ^ 2)))).sum := by
  induction l with
  | nil => simp [Usig]
  | cons p ps ih => simp [Usig, ih]

lemma norm_sq_mk (x y a b : ℝ) : ‖(⟨x, y⟩ : ℂ) - ⟨a, b⟩‖ ^ 2 = (x - a) ^ 2 + (y - b) ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp
  ring

theorem Usig_bridge (x y : ℝ) :
    CatalanLambda.Decay.Usig (1 / 2048 : ℝ) cS mS ⟨x, y⟩ = Usig sigD x y := by
  unfold CatalanLambda.Decay.Usig
  rw [Usig_eq_sum, ← sum_sigma]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  unfold CatalanLambda.Decay.krho mS cS
  rw [norm_sq_mk]

theorem Utau_bridge (x y : ℝ) (hx : x < 0) : CatalanLambda.Decay.Utau ⟨x, y⟩ = Utau x y := by
  rw [CatalanLambda.Decay.Utau_closed_form (by simpa using hx)]
  unfold Utau
  simp

theorem Utau_bridge_axis (x : ℝ) (h1 : x ≤ 1) : CatalanLambda.Decay.Utau ⟨x, 0⟩ = Utau x 0 := by
  rcases lt_or_ge x 0 with hx | hx
  · exact Utau_bridge x 0 hx
  · have e : (⟨x, 0⟩ : ℂ) = (x : ℂ) := Complex.ext (by simp) (by simp)
    rw [e, CatalanLambda.Decay.Utau_real hx h1, Utau_axis]
    have l1 : Real.log (x ^ 2) / 2 = Real.log x := by rw [Real.log_pow]; push_cast; ring
    have l2 : Real.log ((1 - x) ^ 2) / 2 = Real.log (1 - x) := by rw [Real.log_pow]; push_cast; ring
    rw [l1, l2]

theorem gfun_bridge (x y : ℝ) (hx : x < 0) (hy : 0 ≤ y) :
    CatalanLambda.Decay.gfun (1 / 2048 : ℝ) (1 / 1000 : ℝ) cS mS ⟨x, y⟩ = gfun sigD x y := by
  unfold CatalanLambda.Decay.gfun gfun
  rw [Usig_bridge, Utau_bridge x y hx]
  have : |(⟨x, y⟩ : ℂ).im| = y := abs_of_nonneg hy
  rw [this]
  ring

theorem gfun_bridge_axis (x : ℝ) (h1 : x ≤ 1) :
    CatalanLambda.Decay.gfun (1 / 2048 : ℝ) (1 / 1000 : ℝ) cS mS ⟨x, 0⟩ = gfun sigD x 0 := by
  unfold CatalanLambda.Decay.gfun gfun
  rw [Usig_bridge, Utau_bridge_axis x h1]
  simp

end CatalanCore.Cert.SigmaP6
