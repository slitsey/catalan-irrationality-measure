module

public import CatalanCore.Zeta5.Profile.Defs
public import CatalanCore.Zeta5.Profile.CellTools
public import CatalanCore.Zeta5.Profile.Pieces

@[expose] public section

/-!
# ZC30: `R` is affine between consecutive points of `{n/c : c ∈ 𝒞}`

`𝒞 = {2, 2λ, 2H, 1+α, 2(H−1)} = {2, 37/20, 23/10, 43/40, 3/10}` (CONTENT-LEDGER ZC30).

* `Rg_affine_cell` : if no point `n/c` (`c ∈ 𝒞`) lies in the open interval `(l, r)`, then
  `R t = A t + B` there.
* `cellOK`, `chainOK` : the decidable rational test of the hypothesis.
* `R_chain_sound` : `∫ R t / t³` over a checked cut list equals the rational `chain Rg l ts`
  (ZC30 + ZC33 for `R`).
-/

open Set

namespace CatalanCore.Zeta5.Profile

/-- `(1 − e)/2 + e (s t − k)`: the distance to the nearest integer on a branch. -/
noncomputable def trP (e k s t : ℝ) : ℝ := (1 - e) / 2 + e * (s * t - k)

/-- `R` on a cell, in terms of the integer data and the branch signs. -/
noncomputable def Phi (ef eg d1 d2 k1 k2 k3 k4 k5 t : ℝ) : ℝ :=
  t * (4 * lam + 2 * lam * (t - k1) - 12 * lam * (al * t - k2))
    + (((2 * hh * t - k3) * ((2 * hh * t - k3) - (2 * t - k4))
        - d2 * ((2 * hh * t - k3) - (2 * t - k4))
        + (2 * lam * t - k5) * (1 - (2 * lam * t - k5))) / 2
      + 9 * trP eg k2 al t * (1 - 2 * trP eg k2 al t)
      - 3 * ef * eg * (trP eg k2 al t + d1 * (trP ef k1 1 t - trP eg k2 al t)
          - 2 * trP ef k1 1 t * trP eg k2 al t))

/-- The quadratic terms of `Phi` cancel: it is affine in `t`. -/
lemma Phi_affine {ef eg : ℝ} (hef : ef = 1 ∨ ef = -1) (heg : eg = 1 ∨ eg = -1)
    (d1 d2 k1 k2 k3 k4 k5 : ℝ) :
    ∃ A B : ℝ, ∀ t, Phi ef eg d1 d2 k1 k2 k3 k4 k5 t = A * t + B := by
  refine ⟨Phi ef eg d1 d2 k1 k2 k3 k4 k5 1 - Phi ef eg d1 d2 k1 k2 k3 k4 k5 0,
    Phi ef eg d1 d2 k1 k2 k3 k4 k5 0, fun t => ?_⟩
  rcases hef with rfl | rfl <;> rcases heg with rfl | rfl <;>
    (unfold Phi trP lam al hh; ring)

lemma tri_eq (x : ℝ) : tri x = (1 - sg x) / 2 + sg x * Int.fract x := by
  unfold tri sg
  split_ifs with h
  · rw [min_eq_left (by linarith)]; ring
  · rw [min_eq_right (by linarith)]; ring

/-- Pointwise: `R t = Phi (data of t) t`. -/
lemma Rg_eq_Phi (t : ℝ) :
    Rg t = Phi (sg t) (sg (al * t)) (if tri t ≤ tri (al * t) then 1 else 0)
      (if 0 ≤ Int.fract (2 * hh * t) - Int.fract (2 * t) then 1 else 0)
      (⌊t⌋ : ℝ) (⌊al * t⌋ : ℝ) (⌊2 * hh * t⌋ : ℝ) (⌊2 * t⌋ : ℝ) (⌊2 * lam * t⌋ : ℝ) t := by
  have hmin : min (tri t) (tri (al * t))
      = tri (al * t) + (if tri t ≤ tri (al * t) then (1 : ℝ) else 0) * (tri t - tri (al * t)) := by
    split_ifs with h
    · rw [min_eq_left h]; ring
    · rw [min_eq_right (le_of_not_ge h)]; ring
  have hmax : max 0 (Int.fract (2 * hh * t) - Int.fract (2 * t))
      = (if 0 ≤ Int.fract (2 * hh * t) - Int.fract (2 * t) then (1 : ℝ) else 0)
        * (Int.fract (2 * hh * t) - Int.fract (2 * t)) := by
    split_ifs with h
    · rw [max_eq_right h]; ring
    · rw [max_eq_left (le_of_lt (not_le.1 h))]; ring
  unfold Rg Fs Qc Q1 Q2
  rw [hmin, hmax]
  simp only [tri_eq, trP, Phi, Int.fract]
  ring

section cell

variable {l r : ℝ}

lemma noPt_one (h2 : NoPt 2 l r) : NoPt 1 l r :=
  noPt_of_mul (k := 2) (by norm_num) (by norm_num) (by norm_num) h2

lemma noPt_al (h6 : NoPt (3 / 10) l r) : NoPt (al : ℝ) l r :=
  noPt_of_mul (k := 4) (by norm_num) (by unfold al; norm_num) (by unfold al; norm_num) h6

lemma noPt_2al (h6 : NoPt (3 / 10) l r) : NoPt (2 * al : ℝ) l r :=
  noPt_of_mul (k := 2) (by norm_num) (by unfold al; norm_num) (by unfold al; norm_num) h6

lemma noPt_2hh (h4 : NoPt (23 / 10) l r) : NoPt (2 * hh : ℝ) l r :=
  noPt_of_mul (k := 1) (by norm_num) (by unfold hh; norm_num) (by unfold hh; norm_num) h4

lemma noPt_2lam (h3 : NoPt (37 / 20) l r) : NoPt (2 * lam : ℝ) l r :=
  noPt_of_mul (k := 1) (by norm_num) (by unfold lam; norm_num) (by unfold lam; norm_num) h3

lemma noPt_1mal (h3 : NoPt (37 / 20) l r) : NoPt (1 - al : ℝ) l r :=
  noPt_of_mul (k := 2) (by norm_num) (by unfold al; norm_num) (by unfold al; norm_num) h3

lemma noPt_1pal (h5 : NoPt (43 / 40) l r) : NoPt (1 + al : ℝ) l r :=
  noPt_of_mul (k := 1) (by norm_num) (by unfold al; norm_num) (by unfold al; norm_num) h5

lemma noPt_2hm2 (h6 : NoPt (3 / 10) l r) : NoPt (2 * hh - 2 : ℝ) l r :=
  noPt_of_mul (k := 1) (by norm_num) (by unfold hh; norm_num) (by unfold hh; norm_num) h6

/-- On a cell, the floor of `t` and the branch sign of `{t}` are constant. -/
lemma sg_const (h2 : NoPt 2 l r) {t m : ℝ} (ht : t ∈ Ioo l r) (hm : m ∈ Ioo l r) :
    sg t = sg m ∧ ⌊t⌋ = ⌊m⌋ := by
  have f1 : ⌊t⌋ = ⌊m⌋ := by
    have := floor_const (s := 1) (by norm_num) (noPt_one h2) ht hm
    simpa using this
  refine ⟨?_, f1⟩
  unfold sg
  have := sign_const_lt (s := 2) (by norm_num) h2 (n := 2 * ⌊m⌋ + 1) ht hm
  push_cast at this
  have e : (Int.fract t < 1 / 2 ↔ Int.fract m < 1 / 2) := by
    rw [Int.fract, Int.fract, f1]
    constructor <;> intro h
    · have := this.1 (by linarith); linarith
    · have := this.2 (by linarith); linarith
  simp only [e]

/-- Same for `α t`. -/
lemma sg_const_al (h6 : NoPt (3 / 10) l r) {t m : ℝ} (ht : t ∈ Ioo l r) (hm : m ∈ Ioo l r) :
    sg (al * t) = sg (al * m) ∧ ⌊al * t⌋ = ⌊al * m⌋ := by
  have hal : (al : ℝ) = 3 / 40 := rfl
  have f2 : ⌊al * t⌋ = ⌊al * m⌋ := floor_const (by rw [hal]; norm_num) (noPt_al h6) ht hm
  refine ⟨?_, f2⟩
  unfold sg
  have := sign_const_lt (s := 2 * al) (by rw [hal]; norm_num) (noPt_2al h6)
    (n := 2 * ⌊al * m⌋ + 1) ht hm
  push_cast at this
  have e : (Int.fract (al * t) < 1 / 2 ↔ Int.fract (al * m) < 1 / 2) := by
    rw [Int.fract, Int.fract, f2]
    constructor <;> intro h
    · have := this.1 (by linarith); linarith
    · have := this.2 (by linarith); linarith
  simp only [e]

lemma aff_iff_le {s : ℝ} (hs : s ≠ 0) (hN : NoPt s l r) (n : ℤ) {t m : ℝ}
    (ht : t ∈ Ioo l r) (hm : m ∈ Ioo l r) : s * t - n ≤ 0 ↔ s * m - n ≤ 0 := by
  have := sign_const_le hs hN (n := n) ht hm
  constructor <;> intro h
  · have := this.1 (by linarith); linarith
  · have := this.2 (by linarith); linarith

/-- The branch comparison `tri t ≤ tri (α t)` is constant on a cell. -/
lemma tri_cmp_const (h3 : NoPt (37 / 20) l r) (h5 : NoPt (43 / 40) l r) {t m : ℝ}
    (ht : t ∈ Ioo l r) (hm : m ∈ Ioo l r) (e1 : sg t = sg m) (e2 : sg (al * t) = sg (al * m))
    (f1 : ⌊t⌋ = ⌊m⌋) (f2 : ⌊al * t⌋ = ⌊al * m⌋) :
    (tri t ≤ tri (al * t) ↔ tri m ≤ tri (al * m)) := by
  have hF1 : Int.fract t = t - ⌊m⌋ := by rw [Int.fract, f1]
  have hF2 : Int.fract (al * t) = al * t - ⌊al * m⌋ := by rw [Int.fract, f2]
  have hM1 : Int.fract m = m - ⌊m⌋ := rfl
  have hM2 : Int.fract (al * m) = al * m - ⌊al * m⌋ := rfl
  rw [tri_eq t, tri_eq (al * t), tri_eq m, tri_eq (al * m), e1, e2, hF1, hF2, hM1, hM2]
  have hal : (al : ℝ) = 3 / 40 := rfl
  rcases sg_sq m with hef | hef <;> rcases sg_sq (al * m) with heg | heg <;> rw [hef, heg]
  · have key := aff_iff_le (l := l) (r := r) (s := 1 - al) (by rw [hal]; norm_num)
      (noPt_1mal h3) (⌊m⌋ - ⌊al * m⌋) ht hm
    push_cast at key
    constructor <;> intro h
    · have := key.1 (by linarith); linarith
    · have := key.2 (by linarith); linarith
  · have key := aff_iff_le (l := l) (r := r) (s := 1 + al) (by rw [hal]; norm_num)
      (noPt_1pal h5) (⌊m⌋ + ⌊al * m⌋ + 1) ht hm
    push_cast at key
    constructor <;> intro h
    · have := key.1 (by linarith); linarith
    · have := key.2 (by linarith); linarith
  · have key := aff_iff_le (l := l) (r := r) (s := -(1 + al)) (by rw [hal]; norm_num)
      (by
        have := noPt_1pal h5
        exact noPt_of_mul (k := -1) (by norm_num) (by rw [hal]; norm_num) (by ring) this)
      (-(⌊m⌋ + ⌊al * m⌋ + 1)) ht hm
    push_cast at key
    constructor <;> intro h
    · have := key.1 (by linarith); linarith
    · have := key.2 (by linarith); linarith
  · have key := aff_iff_le (l := l) (r := r) (s := -(1 - al)) (by rw [hal]; norm_num)
      (by
        have := noPt_1mal h3
        exact noPt_of_mul (k := -1) (by norm_num) (by rw [hal]; norm_num) (by ring) this)
      (⌊al * m⌋ - ⌊m⌋) ht hm
    push_cast at key
    constructor <;> intro h
    · have := key.1 (by linarith); linarith
    · have := key.2 (by linarith); linarith

/-- **ZC30.** `R` is affine on every interval free of the points `n/c`, `c ∈ 𝒞`. -/
theorem Rg_affine_cell (hlr : l < r) (h2 : NoPt 2 l r) (h3 : NoPt (37 / 20) l r)
    (h4 : NoPt (23 / 10) l r) (h5 : NoPt (43 / 40) l r) (h6 : NoPt (3 / 10) l r) :
    ∃ A B : ℝ, ∀ t ∈ Ioo l r, Rg t = A * t + B := by
  set m : ℝ := (l + r) / 2 with hmdef
  have hm : m ∈ Ioo l r := ⟨by rw [hmdef]; linarith, by rw [hmdef]; linarith⟩
  have hal : (al : ℝ) = 3 / 40 := rfl
  have hhh : (hh : ℝ) = 23 / 20 := rfl
  have hll : (lam : ℝ) = 37 / 40 := rfl
  obtain ⟨A, B, hAB⟩ := Phi_affine (ef := sg m) (eg := sg (al * m)) (sg_sq m) (sg_sq (al * m))
    (if tri m ≤ tri (al * m) then 1 else 0)
    (if 0 ≤ Int.fract (2 * hh * m) - Int.fract (2 * m) then 1 else 0)
    (⌊m⌋ : ℝ) (⌊al * m⌋ : ℝ) (⌊2 * hh * m⌋ : ℝ) (⌊2 * m⌋ : ℝ) (⌊2 * lam * m⌋ : ℝ)
  refine ⟨A, B, fun t ht => ?_⟩
  obtain ⟨s1, f1⟩ := sg_const h2 ht hm
  obtain ⟨s2, f2⟩ := sg_const_al h6 ht hm
  have f3 : ⌊2 * hh * t⌋ = ⌊2 * hh * m⌋ :=
    floor_const (by rw [hhh]; norm_num) (noPt_2hh h4) ht hm
  have f4 : ⌊2 * t⌋ = ⌊2 * m⌋ := floor_const (by norm_num) h2 ht hm
  have f5 : ⌊2 * lam * t⌋ = ⌊2 * lam * m⌋ :=
    floor_const (by rw [hll]; norm_num) (noPt_2lam h3) ht hm
  have d1 : (tri t ≤ tri (al * t)) ↔ (tri m ≤ tri (al * m)) :=
    tri_cmp_const h3 h5 ht hm s1 s2 f1 f2
  have d2 : (0 ≤ Int.fract (2 * hh * t) - Int.fract (2 * t)) ↔
      (0 ≤ Int.fract (2 * hh * m) - Int.fract (2 * m)) := by
    have := sign_const_lt (s := 2 * hh - 2) (by rw [hhh]; norm_num) (noPt_2hm2 h6)
      (n := ⌊2 * hh * m⌋ - ⌊2 * m⌋) ht hm
    push_cast at this
    rw [Int.fract, Int.fract, Int.fract, Int.fract, f3, f4]
    constructor <;> intro h
    · by_contra hc
      have := this.2 (by linarith)
      linarith
    · by_contra hc
      have := this.1 (by linarith)
      linarith
  rw [Rg_eq_Phi t, s1, s2, f1, f2, f3, f4, f5]
  simp only [d1, d2]
  exact hAB t

end cell

/-! ### The rational test and the evaluator -/

/-- The five slopes `c ∈ 𝒞`. -/
def Rslopes : List ℚ := [2, 37 / 20, 23 / 10, 43 / 40, 3 / 10]

/-- Decidable test: no point `n/c`, `c ∈ 𝒞`, in the open interval `(l, r)`. -/
def cellOK (l r : ℚ) : Bool :=
  (Rslopes.all fun c => decide (r * c ≤ ⌊l * c⌋ + 1))

/-- Test of a whole cut list. -/
def chainOK : ℚ → List ℚ → Bool
  | _, [] => true
  | l, r :: t => decide (l < r) && cellOK l r && chainOK r t

lemma chainOK_append (ts1 ts2 : List ℚ) :
    ∀ l : ℚ, chainOK l (ts1 ++ ts2) = (chainOK l ts1 && chainOK (endpt l ts1) ts2) := by
  induction ts1 with
  | nil => intro l; simp [chainOK, endpt]
  | cons r t ih => intro l; simp [chainOK, endpt, ih, Bool.and_assoc]

lemma cellOK_noPt {l r : ℚ} (h : cellOK l r = true) :
    NoPt 2 l r ∧ NoPt (37 / 20) l r ∧ NoPt (23 / 10) l r ∧ NoPt (43 / 40) l r ∧
      NoPt (3 / 10) l r := by
  simp only [cellOK, Rslopes, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
    decide_eq_true_eq] at h
  obtain ⟨a, b, c, d, e⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa using noPt_of_check (c := 2) (by norm_num) a
  · simpa using noPt_of_check (c := 37 / 20) (by norm_num) b
  · simpa using noPt_of_check (c := 23 / 10) (by norm_num) c
  · simpa using noPt_of_check (c := 43 / 40) (by norm_num) d
  · simpa using noPt_of_check (c := 3 / 10) (by norm_num) e

lemma okChain_of_chainOK : ∀ (ts : List ℚ) (l : ℚ), chainOK l ts = true →
    okChain (fun l r => ∃ A B : ℝ, ∀ t ∈ Ioo (l : ℝ) r, Rg t = A * t + B) l ts := by
  intro ts
  induction ts with
  | nil => intro l _; trivial
  | cons r t ih =>
    intro l h
    simp only [chainOK, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hlr, hc⟩, hrest⟩ := h
    refine ⟨hlr, ?_, ih r hrest⟩
    obtain ⟨n2, n3, n4, n5, n6⟩ := cellOK_noPt hc
    have hlr' : (l : ℝ) < r := by exact_mod_cast hlr
    have hh : ((2 : ℚ) : ℝ) = 2 := by norm_num
    exact Rg_affine_cell hlr' (by simpa using n2) (by simpa using n3) (by simpa using n4)
      (by simpa using n5) (by simpa using n6)

lemma fract_cast (x : ℚ) : ((Int.fract x : ℚ) : ℝ) = Int.fract (x : ℝ) := Rat.cast_fract x

lemma sg_cast (x : ℚ) : ((sg x : ℚ) : ℝ) = sg (x : ℝ) := by
  unfold sg
  have hc : ∀ y : ℚ, y < 1 / 2 ↔ (y : ℝ) < 1 / 2 := by
    intro y
    have := (Rat.cast_lt (K := ℝ) (p := y) (q := 1 / 2))
    simpa using this.symm
  have hf : Int.fract x < 1 / 2 ↔ Int.fract (x : ℝ) < 1 / 2 := by
    rw [← fract_cast]; exact hc _
  split_ifs with h1 h2 h2
  · norm_num
  · exact absurd (hf.1 h1) h2
  · exact absurd (hf.2 h2) h1
  · norm_num

lemma tri_cast (x : ℚ) : ((tri x : ℚ) : ℝ) = tri (x : ℝ) := by
  unfold tri; rw [Rat.cast_min]; simp only [Rat.cast_sub, Rat.cast_one, fract_cast]

lemma Rg_cast (q : ℚ) : (((Rg q : ℚ)) : ℝ) = Rg (q : ℝ) := by
  unfold Rg Fs Qc Q1 Q2
  simp only [Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_max, Rat.cast_ofNat,
    Rat.cast_one, Rat.cast_zero, Rat.cast_min, fract_cast, sg_cast, tri_cast, lam, al, hh]

/-- **ZC30 + ZC33 for `R`.** On a cut list passing the rational test, `∫ R(t) t⁻³ dt` is the
rational `chain Rg l ts`. -/
theorem R_chain_sound (ts : List ℚ) (l : ℚ) (hl : 0 < l) (h : chainOK l ts = true) :
    ∫ t in (l : ℝ)..(endpt l ts : ℚ), Rg t / t ^ 3 = ((chain Rg l ts : ℚ) : ℝ) :=
  (chain_sound (H := (Rg : ℝ → ℝ)) (h := (Rg : ℚ → ℚ)) (fun q => (Rg_cast q).symm) ts l hl
    (okChain_of_chainOK ts l h)).2

end CatalanCore.Zeta5.Profile
