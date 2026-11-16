module

public import CatalanCore.Zeta5.Sum.OuterDefs

@[expose] public section

/-!
# `x T₀(1/x)` is affine between consecutive points of `{n/c}`: the piece rule for the outer profile

* `Ex_affine_cell` : `Ex` (`= x T₀(1/x)`) is affine on a cell free of the points `n/c`,
  `c ∈ {2, 37/20}`, on which the four guards `te − ν`, `(1+4α)x − 2`, `λx − (g₁)₊` and
  `x r − x Z` have no strict sign change.
* `cellOKE`, `chainOKE`, `Ex_chain_sound` : the decidable test and the evaluator
  `∫ Ex t t⁻³ = chain Ex l ts` (reusing `Profile.chain`).
* `cellOKH`, `chainOKH`, `Hp_chain_sound` : the same for `[Ex − Rg]₊` (the outer saving of ZC35).
-/

open Set

set_option linter.deprecated false

namespace CatalanCore.Zeta5.Sum

open CatalanCore.Zeta5.Profile

section cell

variable {l r : ℝ}

lemma WS.neg' {φ : ℝ → ℝ} (w : WS l r φ) : WS l r (fun t => -φ t) := by
  rcases w with w | w
  · right; intro t ht; have := w t ht; linarith
  · left; intro t ht; have := w t ht; linarith

lemma WS.congr' {φ ψ : ℝ → ℝ} (w : WS l r φ) (h : ∀ t ∈ Ioo l r, φ t = ψ t) : WS l r ψ := by
  rcases w with w | w
  · left; intro t ht; rw [← h t ht]; exact w t ht
  · right; intro t ht; rw [← h t ht]; exact w t ht

lemma ws_lin (hlr : l < r) {s : ℝ} (hs : s ≠ 0) (hN : NoPt s l r) (j : ℤ) :
    WS l r (fun t => s * t - j) := by
  have hm : (l + r) / 2 ∈ Ioo l r := ⟨by linarith, by linarith⟩
  by_cases h : s * ((l + r) / 2) < j
  · right
    intro t ht
    have := (sign_const_lt hs hN (n := j) ht hm).2 h
    linarith
  · left
    intro t ht
    by_contra hc
    push Not at hc
    exact h ((sign_const_lt hs hN (n := j) ht hm).1 (by linarith))

lemma max_eq_add_max0 (a b : ℝ) : max a b = b + max 0 (a - b) := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, max_eq_left (by linarith)]; ring
  · rw [max_eq_left h, max_eq_right (by linarith)]; ring

lemma one_lt_iff (h2 : NoPt 2 l r) {t m : ℝ} (ht : t ∈ Ioo l r) (hm : m ∈ Ioo l r) :
    1 < t ↔ 1 < m := by
  have a := sign_const_lt (s := 2) (by norm_num) h2 (n := 2) ht hm
  have b := ne_of_mem (s := 2) (by norm_num) h2 (n := 2) ht
  have c := ne_of_mem (s := 2) (by norm_num) h2 (n := 2) hm
  push_cast at a b c
  constructor
  · intro h
    by_contra hh
    push Not at hh
    have : 2 * m < 2 ∨ 2 * m = 2 := by
      rcases lt_or_eq_of_le (by linarith : 2 * m ≤ 2) with h' | h'
      · exact Or.inl h'
      · exact Or.inr h'
    rcases this with h' | h'
    · have := a.2 h'; linarith
    · exact c h'
  · intro h
    by_contra hh
    push Not at hh
    rcases lt_or_eq_of_le hh with h' | h'
    · have := a.1 (by linarith); linarith
    · exact b (by rw [h']; norm_num)

/-- `Ex` is affine on an admissible cell. -/
theorem Ex_affine_cell (hlr : l < r) (h2 : NoPt 2 l r) (h3 : NoPt (37 / 20) l r)
    (T0 : wsTest (gtG : ℝ → ℝ) l r) (T1 : wsTest (g1G : ℝ → ℝ) l r)
    (T2 : wsTest (g2G : ℝ → ℝ) l r) (T3 : wsTest (g3G : ℝ → ℝ) l r) :
    ∃ A B : ℝ, ∀ t ∈ Ioo l r, Ex t = A * t + B := by
  set m : ℝ := (l + r) / 2 with hmdef
  have hm : m ∈ Ioo l r := ⟨by rw [hmdef]; linarith, by rw [hmdef]; linarith⟩
  have hal : (al : ℝ) = 3 / 40 := rfl
  have hll : (lam : ℝ) = 37 / 40 := rfl
  have hfs : ∀ t ∈ Ioo l r, sg t = sg m ∧ ⌊t⌋ = ⌊m⌋ := fun t ht => sg_const h2 ht hm
  have hTri : Aff l r (fun t : ℝ => tri t) :=
    ⟨sg m, (1 - sg m) / 2 - sg m * ⌊m⌋, fun t ht => by
      obtain ⟨s1, f1⟩ := hfs t ht
      beta_reduce
      rw [tri_eq, s1, Int.fract, f1]; ring⟩
  have hnu : Aff l r (fun t : ℝ => (al : ℝ) * t) := ⟨al, 0, fun t _ => by ring⟩
  have hGt : Aff l r (gtG : ℝ → ℝ) := hTri.sub hnu
  have Wt := ws_of_test hlr hGt T0
  have hmin : Aff l r (fun t : ℝ => min (tri t) ((al : ℝ) * t)) := Aff.min hTri hnu Wt
  have hmax0 : Aff l r (fun t : ℝ => max 0 (tri t - (al : ℝ) * t)) := hGt.max0 Wt
  have hmax0' : Aff l r (fun t : ℝ => max 0 ((al : ℝ) * t - tri t)) :=
    (hnu.sub hTri).max0 (WS.congr' (WS.neg' Wt) (fun t _ => by unfold gtG; ring))
  have hrest : Aff l r (fun t : ℝ => 1 / 2 - max (tri t) ((al : ℝ) * t)) := by
    have : Aff l r (fun t : ℝ => 1 / 2 - ((al : ℝ) * t + max 0 (tri t - (al : ℝ) * t))) :=
      (Aff.of_const (1 / 2)).sub (hnu.add hmax0)
    refine this.congr (fun t _ => ?_)
    rw [max_eq_add_max0 (tri t) ((al : ℝ) * t)]
  have hlA : ∀ t ∈ Ioo l r, lA t = lA m := fun t ht => by
    unfold lA; rw [(hfs t ht).2]
  have hlB : ∀ t ∈ Ioo l r, lB t = lB m := fun t ht => by
    unfold lB
    have e := (hfs t ht)
    have hf : Int.fract t < 1 / 2 ↔ Int.fract m < 1 / 2 := fract_lt_iff_sg e.1
    rw [e.2]
    by_cases hc : Int.fract m < 1 / 2
    · rw [if_pos (hf.2 hc), if_pos hc]
    · rw [if_neg (fun hh => hc (hf.1 hh)), if_neg hc]
  have hI : Aff l r (Iint : ℝ → ℝ) := by
    have := (((hmin.const_mul ((Sq (lA m) 1 : ℚ) : ℝ)).add
      (hmax0.const_mul ((Sq (lA m) 0 : ℚ) : ℝ))).add
      (hmax0'.const_mul ((Sq (lB m) 1 : ℚ) : ℝ))).add
      (hrest.const_mul ((Sq (lB m) 0 : ℚ) : ℝ))
    refine this.congr (fun t ht => ?_)
    unfold Iint
    rw [hlA t ht, hlB t ht]
  have hZ : Aff l r (Zint : ℝ → ℝ) := by
    have := (((hmin.const_mul ((Nq (lA m) 1 : ℚ) : ℝ)).add
      (hmax0.const_mul ((Nq (lA m) 0 : ℚ) : ℝ))).add
      (hmax0'.const_mul ((Nq (lB m) 1 : ℚ) : ℝ))).add
      (hrest.const_mul ((Nq (lB m) 0 : ℚ) : ℝ))
    refine this.congr (fun t ht => ?_)
    unfold Zint
    rw [hlA t ht, hlB t ht]
  have hlam : Aff l r (fun t : ℝ => (lam : ℝ) * t) := ⟨lam, 0, fun t _ => by ring⟩
  have hGx : Aff l r (Gx : ℝ → ℝ) := by
    by_cases hc : 1 < m
    · refine (hI.const_mul 2).congr (fun t ht => ?_)
      unfold Gx
      rw [if_pos ((one_lt_iff h2 ht hm).2 hc)]
    · refine (Aff.of_const (0 : ℝ)).congr (fun t ht => ?_)
      unfold Gx
      rw [if_neg (fun hh => hc ((one_lt_iff h2 ht hm).1 hh))]
  have hZx : Aff l r (Zx : ℝ → ℝ) := by
    by_cases hc : 1 < m
    · refine hZ.congr (fun t ht => ?_)
      unfold Zx
      rw [if_pos ((one_lt_iff h2 ht hm).2 hc)]
    · refine hlam.congr (fun t ht => ?_)
      unfold Zx
      rw [if_neg (fun hh => hc ((one_lt_iff h2 ht hm).1 hh))]
  have hg1 : Aff l r (g1G : ℝ → ℝ) := ⟨1 + 4 * al, -2, fun t _ => by unfold g1G; ring⟩
  have W1 := ws_of_test hlr hg1 T1
  have hmg1 : Aff l r (fun t : ℝ => max 0 (g1G t)) := hg1.max0 W1
  have hg2 : Aff l r (g2G : ℝ → ℝ) := hlam.sub hmg1
  have W2 := ws_of_test hlr hg2 T2
  have hrx : Aff l r (rx : ℝ → ℝ) := Aff.min hlam hmg1 W2
  have hg3 : Aff l r (g3G : ℝ → ℝ) := hrx.sub hZx
  have W3 := ws_of_test hlr hg3 T3
  have hm3 : Aff l r (fun t : ℝ => min (rx t) (Zx t)) := Aff.min hrx hZx W3
  have hfl : Aff l r (fun t : ℝ => 2 * (lam : ℝ) * t * (⌊t⌋ : ℝ)) :=
    ⟨2 * lam * ⌊m⌋, 0, fun t ht => by beta_reduce; rw [(hfs t ht).2]; ring⟩
  have hsc : ∀ j : ℤ, Aff l r (fun t : ℝ => max 0 (2 * (lam : ℝ) * t - j)) := by
    intro j
    have haff : Aff l r (fun t : ℝ => 2 * (lam : ℝ) * t - j) :=
      ⟨2 * lam, -j, fun t _ => by ring⟩
    refine haff.max0 ?_
    refine WS.congr' (ws_lin hlr (s := 37 / 20) (by norm_num) h3 j) (fun t _ => ?_)
    rw [hll]; ring
  have key := (((((((hGx.const_mul (-1)).add hm3).sub hfl).add (hsc 1)).add (hsc 2)).add
    (hsc 3)).add (hsc 4)).add (hsc 5)
  obtain ⟨A, B, hAB⟩ := key
  refine ⟨A, B, fun t ht => ?_⟩
  rw [← hAB t ht]
  beta_reduce
  unfold Ex
  push_cast
  ring

end cell

/-! ### The rational test and the evaluator -/

/-- The slopes whose points `n/c` bound the cells of `Ex`. -/
def Eslopes : List ℚ := [2, 37 / 20]

/-- Decidable cell test for `Ex`. -/
def cellOKE (l r : ℚ) : Bool :=
  (Eslopes.all fun c => decide (r * c ≤ ⌊l * c⌋ + 1)) &&
    wsTestB gtG l r && wsTestB g1G l r && wsTestB g2G l r && wsTestB g3G l r

/-- Test of a whole cut list. -/
def chainOKE : ℚ → List ℚ → Bool
  | _, [] => true
  | l, r :: t => decide (l < r) && cellOKE l r && chainOKE r t

lemma chainOKE_append (ts1 ts2 : List ℚ) :
    ∀ l : ℚ, chainOKE l (ts1 ++ ts2) = (chainOKE l ts1 && chainOKE (endpt l ts1) ts2) := by
  induction ts1 with
  | nil => intro l; simp [chainOKE, endpt]
  | cons r t ih => intro l; simp [chainOKE, endpt, ih, Bool.and_assoc]

lemma cellOKE_noPt {l r : ℚ} (h : (Eslopes.all fun c => decide (r * c ≤ ⌊l * c⌋ + 1)) = true) :
    NoPt 2 l r ∧ NoPt (37 / 20) l r := by
  simp only [Eslopes, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
    decide_eq_true_eq] at h
  obtain ⟨a, b⟩ := h
  refine ⟨?_, ?_⟩
  · simpa using noPt_of_check (c := 2) (by norm_num) a
  · simpa using noPt_of_check (c := 37 / 20) (by norm_num) b

lemma cellOKE_affine {l r : ℚ} (hlr : l < r) (h : cellOKE l r = true) :
    ∃ A B : ℝ, ∀ t ∈ Ioo (l : ℝ) r, Ex t = A * t + B := by
  simp only [cellOKE, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hs, d0⟩, d1⟩, d2⟩, d3⟩ := h
  obtain ⟨n2, n3⟩ := cellOKE_noPt hs
  have hlr' : (l : ℝ) < r := by exact_mod_cast hlr
  exact Ex_affine_cell hlr' (by simpa using n2) (by simpa using n3)
    (wsTest_of_B gtG_cast d0) (wsTest_of_B g1G_cast d1) (wsTest_of_B g2G_cast d2)
    (wsTest_of_B g3G_cast d3)

lemma okChain_of_chainOKE : ∀ (ts : List ℚ) (l : ℚ), chainOKE l ts = true →
    okChain (fun l r => ∃ A B : ℝ, ∀ t ∈ Ioo (l : ℝ) r, Ex t = A * t + B) l ts := by
  intro ts
  induction ts with
  | nil => intro l _; trivial
  | cons r t ih =>
    intro l h
    simp only [chainOKE, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hlr, hc⟩, hrest⟩ := h
    exact ⟨hlr, cellOKE_affine hlr hc, ih r hrest⟩

/-- **Piece rule for the outer profile.** On a cut list passing `chainOKE`,
`∫ Ex(t) t⁻³ dt` is the rational `chain Ex l ts`. -/
theorem Ex_chain_sound (ts : List ℚ) (l : ℚ) (hl : 0 < l) (h : chainOKE l ts = true) :
    ∫ t in (l : ℝ)..(endpt l ts : ℚ), Ex t / t ^ 3 = ((chain Ex l ts : ℚ) : ℝ) :=
  (chain_sound (H := (Ex : ℝ → ℝ)) (h := (Ex : ℚ → ℚ)) (fun q => (Ex_cast q).symm) ts l hl
    (okChain_of_chainOKE ts l h)).2

/-! ### The outer saving `[Ex − Rg]₊` -/

/-- `Ex − Rg` as a guard. -/
def gHG (x : ℚ) : ℚ := Ex x - Rg x

/-- The saving density `[x T₀(1/x) − R(x)]₊`. -/
def Hp (x : ℚ) : ℚ := max 0 (Ex x - Rg x)

lemma Hp_cast (q : ℚ) : ((Hp q : ℚ) : ℝ) = max 0 (Ex (q : ℝ) - Rg (q : ℝ)) := by
  unfold Hp
  simp only [Rat.cast_max, Rat.cast_sub, Rat.cast_zero, Ex_cast, Rg_cast]

lemma gHG_cast (q : ℚ) : ((gHG q : ℚ) : ℝ) = Ex (q : ℝ) - Rg (q : ℝ) := by
  unfold gHG
  simp only [Rat.cast_sub, Ex_cast, Rg_cast]

/-- Cell test for the saving. -/
def cellOKH (l r : ℚ) : Bool := cellOK l r && cellOKE l r && wsTestB gHG l r

/-- Test of a whole cut list. -/
def chainOKH : ℚ → List ℚ → Bool
  | _, [] => true
  | l, r :: t => decide (l < r) && cellOKH l r && chainOKH r t

lemma chainOKH_append (ts1 ts2 : List ℚ) :
    ∀ l : ℚ, chainOKH l (ts1 ++ ts2) = (chainOKH l ts1 && chainOKH (endpt l ts1) ts2) := by
  induction ts1 with
  | nil => intro l; simp [chainOKH, endpt]
  | cons r t ih => intro l; simp [chainOKH, endpt, ih, Bool.and_assoc]

lemma cellOKH_affine {l r : ℚ} (hlr : l < r) (h : cellOKH l r = true) :
    ∃ A B : ℝ, ∀ t ∈ Ioo (l : ℝ) r, max 0 (Ex t - Rg t) = A * t + B := by
  simp only [cellOKH, Bool.and_eq_true] at h
  obtain ⟨⟨hR, hE⟩, hH⟩ := h
  have hlr' : (l : ℝ) < r := by exact_mod_cast hlr
  obtain ⟨n2, n3, n4, n5, n6⟩ := cellOK_noPt hR
  have hAR : Aff (l : ℝ) r (Rg : ℝ → ℝ) :=
    Rg_affine_cell hlr' (by simpa using n2) (by simpa using n3) (by simpa using n4)
      (by simpa using n5) (by simpa using n6)
  have hAE : Aff (l : ℝ) r (Ex : ℝ → ℝ) := cellOKE_affine hlr hE
  have hD : Aff (l : ℝ) r (fun t : ℝ => Ex t - Rg t) := hAE.sub hAR
  have hT : wsTest (fun t : ℝ => Ex t - Rg t) (l : ℝ) r :=
    wsTest_of_B (φ := gHG) (fun q => gHG_cast q) hH
  exact (hD.max0 (ws_of_test hlr' hD hT))

lemma okChain_of_chainOKH : ∀ (ts : List ℚ) (l : ℚ), chainOKH l ts = true →
    okChain (fun l r => ∃ A B : ℝ, ∀ t ∈ Ioo (l : ℝ) r, max 0 (Ex t - Rg t) = A * t + B) l ts := by
  intro ts
  induction ts with
  | nil => intro l _; trivial
  | cons r t ih =>
    intro l h
    simp only [chainOKH, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hlr, hc⟩, hrest⟩ := h
    exact ⟨hlr, cellOKH_affine hlr hc, ih r hrest⟩

/-- **Piece rule for the outer saving.** -/
theorem Hp_chain_sound (ts : List ℚ) (l : ℚ) (hl : 0 < l) (h : chainOKH l ts = true) :
    ∫ t in (l : ℝ)..(endpt l ts : ℚ), max 0 (Ex t - Rg t) / t ^ 3 = ((chain Hp l ts : ℚ) : ℝ) :=
  (chain_sound (H := fun t : ℝ => max 0 (Ex t - Rg t)) (h := Hp) (fun q => (Hp_cast q).symm) ts l
    hl (okChain_of_chainOKH ts l h)).2

end CatalanCore.Zeta5.Sum
