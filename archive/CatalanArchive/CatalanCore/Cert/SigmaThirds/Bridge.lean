module

public import CatalanLambda.Decay.ThmNCert
public import CatalanLambda.Decay.ThmNUtauForm
public import CatalanLambda.Cert.Bridge
public import CatalanCore.Cert.SigmaHybS.HMacro
public import CatalanCore.Cert.SigmaThirds.Sigma
public import CatalanCore.Decay.Rect.CertG

@[expose] public section

/-!
# Bridge between the list-based functions and the `Fin 2950` objects of the decay engine

`cH, mH : Fin 2950 → ...` enumerate the sorted list `sigH` (masses sum to `9/8`), `wtH = mH / (1 + 1/8)`.
`gHyb = gAlpha (1/4096) (1/1000) cH wtH (1/8) (Unu (1/8))` is the hybrid function; on `x < 0, y ≥ 0` and on the
axis `[0,1]` it equals `gHR sigH = gfun sigH - UexR`, the function the cells check.
-/

open Real

set_option maxRecDepth 100000

namespace CatalanCore.Cert.SigmaThirds

open _root_.CatalanCore.Cert.SigmaHybS

open CatalanCore.Cert.SigmaHyb (UexR)

def ptAt (k : ℕ) : Pt := sigH.getD k (0, 0, 0)

noncomputable def cH (k : Fin 2950) : ℂ := ⟨((ptAt k).1 : ℝ) / 2 ^ 40, ((ptAt k).2.1 : ℝ) / 2 ^ 40⟩
noncomputable def mH (k : Fin 2950) : ℝ := ((ptAt k).2.2 : ℝ) / 2 ^ 32
noncomputable def wtH (k : Fin 2950) : ℝ := mH k / (1 + (1 / 8 : ℝ))

theorem sigH_len : sigH.length = 2950 := by decide +kernel

lemma sigH_ofFn : sigH = List.ofFn (fun k : Fin 2950 => ptAt k) := by
  apply List.ext_getElem
  · rw [List.length_ofFn]; exact sigH_len
  · intro n h1 h2
    have h3 : n < sigH.length := h1
    rw [List.getElem_ofFn]
    unfold ptAt
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h3]
    rfl

lemma sum_sigma (f : Pt → ℝ) : ∑ k : Fin 2950, f (ptAt k) = (sigH.map f).sum := by
  conv_rhs => rw [sigH_ofFn, List.map_ofFn, List.sum_ofFn]
  rfl

lemma Usig_eq_sum (l : List Pt) (x y : ℝ) :
    Usig l x y = (l.map (fun p => (p.2.2 : ℝ) / 2 ^ 32 * (-(1 / 2) * Real.log
      ((x - (p.1 : ℝ) / 2 ^ 40) ^ 2 + (y - (p.2.1 : ℝ) / 2 ^ 40) ^ 2 + (1 / 4096) ^ 2)))).sum := by
  induction l with
  | nil => simp [Usig]
  | cons p ps ih => simp [Usig, ih]

lemma norm_sq_mk (x y a b : ℝ) : ‖(⟨x, y⟩ : ℂ) - ⟨a, b⟩‖ ^ 2 = (x - a) ^ 2 + (y - b) ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp
  ring

theorem Usig_bridge (x y : ℝ) :
    CatalanLambda.Decay.Usig (1 / 4096 : ℝ) cH mH ⟨x, y⟩ = Usig sigH x y := by
  unfold CatalanLambda.Decay.Usig
  rw [Usig_eq_sum, ← sum_sigma]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  unfold CatalanLambda.Decay.krho mH cH
  rw [norm_sq_mk]

theorem Utau_bridge (x y : ℝ) (hx : x < 0) : CatalanLambda.Decay.Utau ⟨x, y⟩ = Utau x y := by
  rw [CatalanLambda.Decay.Utau_closed_form (by simpa using hx)]
  unfold Utau
  simp

noncomputable abbrev gHyb : ℂ → ℝ :=
  CatalanCore.Cert.gAlpha (1 / 4096 : ℝ) (1 / 1000 : ℝ) cH wtH (1 / 8 : ℝ)
    (CatalanCore.Decay.Unu (1 / 8 : ℝ))

theorem gHyb_eq (s : ℂ) :
    gHyb s = CatalanLambda.Decay.Usig (1 / 4096 : ℝ) cH mH s - CatalanCore.Decay.Unu (1 / 8 : ℝ) s
      + (1 - (1 / 1000 : ℝ)) * Real.pi * |s.im| := by
  unfold gHyb CatalanCore.Cert.gAlpha
  have e : wtH = fun k => (1 / (1 + (1 / 8 : ℝ))) * mH k := by
    funext k; unfold wtH; ring
  rw [e, CatalanCore.Decay.Usig_smul]
  have : (1 + (1 / 8 : ℝ)) * ((1 / (1 + (1 / 8 : ℝ))) * CatalanLambda.Decay.Usig (1 / 4096 : ℝ) cH mH s)
      = CatalanLambda.Decay.Usig (1 / 4096 : ℝ) cH mH s := by
    field_simp
  rw [this]

/-- `g_h = gHR` in real coordinates, `x < 0`, `y ≥ 0`. -/
theorem gHyb_split (x y : ℝ) (hx : x < 0) (hy : 0 ≤ y) : gHyb ⟨x, y⟩ = gHR sigH x y := by
  rw [gHyb_eq]
  have hs : (⟨x, y⟩ : ℂ).re < 1 := by show x < 1; linarith
  have hU := CatalanCore.Cert.SigmaHyb.Uex_quarter (1 / 8 : ℝ) rfl hs
  have e2 : 4 * ((⟨x, y⟩ : ℂ) - 1) = ⟨4 * x - 4, 4 * y⟩ := by
    apply Complex.ext <;> simp <;> ring
  unfold CatalanCore.Decay.Unu
  rw [show 2 * (1 / 8 : ℝ) = 2 * (1 / 8 : ℝ) from rfl, hU, e2, Usig_bridge x y, Utau_bridge x y hx,
    CatalanLambda.Cert.Utau_bridge (4 * x - 4) (4 * y) (by linarith)]
  have hi : |(⟨x, y⟩ : ℂ).im| = y := abs_of_nonneg hy
  rw [hi]
  unfold gHR gfun CatalanCore.Cert.SigmaHyb.UexR
  norm_num
  ring

theorem gHyb_split_axis (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : gHyb ⟨x, 0⟩ = gHR sigH x 0 := by
  rw [gHyb_eq]
  have hUex : CatalanCore.Decay.Uex (2 * (1 / 8 : ℝ)) ⟨x, 0⟩ = UexR x 0 := by
    rcases lt_or_eq_of_le h1 with hlt | heq
    · have hs : (⟨x, 0⟩ : ℂ).re < 1 := hlt
      rw [CatalanCore.Cert.SigmaHyb.Uex_quarter (1 / 8 : ℝ) rfl hs]
      have e2 : 4 * ((⟨x, 0⟩ : ℂ) - 1) = ⟨4 * x - 4, 0⟩ := by
        apply Complex.ext <;> simp <;> ring
      rw [e2, CatalanLambda.Cert.Utau_bridge_axis (4 * x - 4) (by linarith)]
      unfold UexR; simp
    · subst heq
      have e1 : (⟨1, 0⟩ : ℂ) = 1 := by apply Complex.ext <;> simp
      rw [e1, show 2 * (1 / 8 : ℝ) = 1 / 4 by norm_num, CatalanCore.Cert.SigmaHyb.Uex_one (by norm_num)]
      unfold UexR
      have hu : CatalanLambda.Cert.Utau (4 * 1 - 4) (4 * 0) = 1 := by
        unfold CatalanLambda.Cert.Utau; norm_num
      rw [hu]
      have l4 : Real.log (1 / 4 : ℝ) = -(2 * Real.log 2) := by
        rw [one_div, Real.log_inv]
        have : (4 : ℝ) = 2 ^ 2 := by norm_num
        rw [this, Real.log_pow]; push_cast; ring
      rw [l4]; ring
  have hUt : CatalanLambda.Decay.Utau ⟨x, 0⟩ = Utau x 0 := by
    rcases lt_or_ge x 0 with hx | hx
    · exact Utau_bridge x 0 hx
    · have e : (⟨x, 0⟩ : ℂ) = (x : ℂ) := Complex.ext (by simp) (by simp)
      rw [e, CatalanLambda.Decay.Utau_real hx h1, Utau_axis]
      have l1 : Real.log (x ^ 2) / 2 = Real.log x := by rw [Real.log_pow]; push_cast; ring
      have l2 : Real.log ((1 - x) ^ 2) / 2 = Real.log (1 - x) := by rw [Real.log_pow]; push_cast; ring
      rw [l1, l2]
  unfold CatalanCore.Decay.Unu
  rw [hUex, hUt, Usig_bridge x 0, show |(⟨x, 0⟩ : ℂ).im| = 0 by simp]
  unfold gHR gfun
  simp only [mul_zero]
  ring

end CatalanCore.Cert.SigmaThirds
