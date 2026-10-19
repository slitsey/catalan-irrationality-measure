module

public import CatalanCore.Cert.SigmaHyb.HBox
public import CatalanCore.Cert.SigmaHyb.Data
public import CatalanCore.Cert.Facts
public import CatalanCore.Decay.Rect.CertG
public import CatalanLambda.Cert.Bridge

@[expose] public section

/-!
# Bridge: list data `lamS`, `hybS` to the `Fin K` objects, and `g_h = g_sq + (U^λ - U^ex)` in real coordinates
-/

open Real

namespace CatalanCore.Cert.SigmaHyb

open CatalanLambda.Cert

set_option maxRecDepth 100000

theorem lamS_len : lamS.length = 180 := by decide +kernel
theorem hybS_len : hybS.length = 480 := by decide +kernel
theorem hybS_perm : hybS.Perm (sigmaS ++ lamS) := by decide +kernel
theorem lamS_mass : (lamS.map (fun p => p.2.2)).sum = 2 ^ 29 := by decide +kernel

def ptAtL (l : List Pt) (k : ℕ) : Pt := l.getD k (0, 0, 0)

noncomputable def cOfL (l : List Pt) {n : ℕ} (k : Fin n) : ℂ :=
  ⟨((ptAtL l k).1 : ℝ) / 2 ^ 40, ((ptAtL l k).2.1 : ℝ) / 2 ^ 40⟩
noncomputable def mOfL (l : List Pt) {n : ℕ} (k : Fin n) : ℝ := ((ptAtL l k).2.2 : ℝ) / 2 ^ 32

lemma ofFn_gen (l : List Pt) (n : ℕ) (h : l.length = n) : l = List.ofFn (fun k : Fin n => ptAtL l k) := by
  apply List.ext_getElem
  · rw [List.length_ofFn]; exact h
  · intro i h1 h2
    have h3 : i < l.length := h1
    rw [List.getElem_ofFn]
    unfold ptAtL
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h3]
    rfl

lemma sum_gen (l : List Pt) (n : ℕ) (h : l.length = n) (f : Pt → ℝ) :
    ∑ k : Fin n, f (ptAtL l k) = (l.map f).sum := by
  conv_rhs => rw [ofFn_gen l n h, List.map_ofFn, List.sum_ofFn]
  rfl

theorem Usig_bridge_gen (l : List Pt) (n : ℕ) (h : l.length = n) (x y : ℝ) :
    CatalanLambda.Decay.Usig (1 / 1024 : ℝ) (cOfL l (n := n)) (mOfL l (n := n)) ⟨x, y⟩ = Usig l x y := by
  unfold CatalanLambda.Decay.Usig
  rw [Usig_eq_sum, ← sum_gen l n h]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  unfold CatalanLambda.Decay.krho mOfL cOfL
  rw [norm_sq_mk]

lemma usig_append' (a b : List Pt) (x y : ℝ) : Usig (a ++ b) x y = Usig a x y + Usig b x y := by
  induction a with
  | nil => simp [Usig]
  | cons p ps ih => simp only [List.cons_append, Usig, ih]; ring

lemma usig_perm {a b : List Pt} (h : a.Perm b) (x y : ℝ) : Usig a x y = Usig b x y := by
  rw [Usig_eq_sum, Usig_eq_sum]
  exact (h.map _).sum_eq

theorem usig_hyb (x y : ℝ) : Usig hybS x y = Usig sigmaS x y + Usig lamS x y := by
  rw [usig_perm hybS_perm, usig_append']

/-- the correction measure as `Fin 180` data -/
noncomputable abbrev cL : Fin 180 → ℂ := cOfL lamS
noncomputable abbrev mL : Fin 180 → ℝ := mOfL lamS
/-- the combined data -/
noncomputable abbrev cH : Fin (300 + 180) → ℂ := Fin.append cS cL
noncomputable abbrev mH : Fin (300 + 180) → ℝ := Fin.append mS mL
noncomputable abbrev wtH : Fin (300 + 180) → ℝ := fun k => mH k / (1 + (1 / 8 : ℝ))

theorem Usig_bridge_lam (x y : ℝ) :
    CatalanLambda.Decay.Usig (1 / 1024 : ℝ) cL mL ⟨x, y⟩ = Usig lamS x y :=
  Usig_bridge_gen lamS 180 lamS_len x y

/-- `g_h = g_sq + (U^λ - U^ex)` in real coordinates, `x < 0`, `y ≥ 0`. -/
theorem gH_split (x y : ℝ) (hx : x < 0) (hy : 0 ≤ y) :
    CatalanCore.Cert.gAlpha (1 / 1024 : ℝ) (1 / 1000 : ℝ) cH wtH (1 / 8 : ℝ)
        (CatalanCore.Decay.Unu (1 / 8 : ℝ)) ⟨x, y⟩
      = CatalanLambda.Decay.gfun (1 / 1024 : ℝ) (1 / 1000 : ℝ) cS mS ⟨x, y⟩
        + (Usig lamS x y - UexR x y) := by
  unfold CatalanCore.Cert.gAlpha
  have h := CatalanCore.Decay.hyb_g_decomp (1 / 1024 : ℝ) (1 / 1000 : ℝ) (1 / 8 : ℝ) (by norm_num)
    cS mS cL mL ⟨x, y⟩
  have e : (fun k : Fin (300 + 180) => (Fin.append mS mL k) / (1 + (1 / 8 : ℝ))) = wtH := rfl
  rw [e] at h
  rw [h]
  have hs : (⟨x, y⟩ : ℂ).re < 1 := by show x < 1; linarith
  have hU := Uex_quarter (1 / 8 : ℝ) rfl hs
  have e2 : 4 * ((⟨x, y⟩ : ℂ) - 1) = ⟨4 * x - 4, 4 * y⟩ := by
    apply Complex.ext <;> simp <;> ring
  rw [show 2 * (1 / 8 : ℝ) = 2 * (1 / 8 : ℝ) from rfl, hU, e2]
  rw [Usig_bridge x y, Usig_bridge_lam, Utau_bridge x y hx, Utau_bridge (4 * x - 4) (4 * y) (by linarith)]
  unfold CatalanLambda.Decay.gfun UexR
  rw [Usig_bridge x y, Utau_bridge x y hx]

theorem gH_split_axis (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    CatalanCore.Cert.gAlpha (1 / 1024 : ℝ) (1 / 1000 : ℝ) cH wtH (1 / 8 : ℝ)
        (CatalanCore.Decay.Unu (1 / 8 : ℝ)) ⟨x, 0⟩
      = CatalanLambda.Decay.gfun (1 / 1024 : ℝ) (1 / 1000 : ℝ) cS mS ⟨x, 0⟩
        + (Usig lamS x 0 - UexR x 0) := by
  unfold CatalanCore.Cert.gAlpha
  have h := CatalanCore.Decay.hyb_g_decomp (1 / 1024 : ℝ) (1 / 1000 : ℝ) (1 / 8 : ℝ) (by norm_num)
    cS mS cL mL ⟨x, 0⟩
  have e : (fun k : Fin (300 + 180) => (Fin.append mS mL k) / (1 + (1 / 8 : ℝ))) = wtH := rfl
  rw [e] at h
  rw [h]
  have hUex : CatalanCore.Decay.Uex (2 * (1 / 8 : ℝ)) ⟨x, 0⟩ = UexR x 0 := by
    rcases lt_or_eq_of_le h1 with hlt | heq
    · have hs : (⟨x, 0⟩ : ℂ).re < 1 := hlt
      rw [Uex_quarter (1 / 8 : ℝ) rfl hs]
      have e2 : 4 * ((⟨x, 0⟩ : ℂ) - 1) = ⟨4 * x - 4, 0⟩ := by
        apply Complex.ext <;> simp <;> ring
      rw [e2, Utau_bridge_axis (4 * x - 4) (by linarith)]
      unfold UexR; simp
    · subst heq
      have e1 : (⟨1, 0⟩ : ℂ) = 1 := by apply Complex.ext <;> simp
      rw [e1, show 2 * (1 / 8 : ℝ) = 1 / 4 by norm_num, Uex_one (by norm_num)]
      unfold UexR
      have hu : CatalanLambda.Cert.Utau (4 * 1 - 4) (4 * 0) = 1 := by
        unfold CatalanLambda.Cert.Utau; norm_num
      rw [hu]
      have l4 : Real.log (1 / 4 : ℝ) = -(2 * Real.log 2) := by
        rw [one_div, Real.log_inv]
        have : (4 : ℝ) = 2 ^ 2 := by norm_num
        rw [this, Real.log_pow]; push_cast; ring
      rw [l4]; ring
  rw [hUex, Usig_bridge_lam, show |(⟨x, 0⟩ : ℂ).im| = 0 by simp]
  unfold CatalanLambda.Decay.gfun
  simp only [mul_zero]
  ring_nf

end CatalanCore.Cert.SigmaHyb
