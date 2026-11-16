module

public import CatalanCore.Zeta5.Profile.RCells

@[expose] public section

/-!
# ZC27 (closed form of `g_ref`) and ZC31 (its piece rule)

`g_ref = (e − q)₊` if `T` is even, `(s − e − q)₊` if `T` is odd, where
`te = min({x}, 1−{x})`, `tn = min({αx}, 1−{αx})`, `s = 1/2 − te`, `q = (tn − te)₊`,
`T = ⌊23x/10⌋`, `u = 23x/20 − T/2`, and `e = (u − te)₊` if `{x} < 1/2`, `min(u, s)` otherwise.

* `gref_nonneg`, `gref_le_half` : `0 ≤ g_ref ≤ 1/2` (ZC27; the arithmetic gain itself is not here).
* `gref_affine_cell` : `g_ref` is affine on a cell where the floors are constant
  (`NoPt` for `2, 3/10, 23/10`) and the five guards `G1..G5` have no strict sign change
  (ZC31: the guards are `tn − te, u − te, u − s`, then `e − q, s − e − q`).
* `gref_chain_sound` : the decidable test `chainOKg` on a cut list makes
  `∫ g_ref t⁻³ = chain gref`.
-/

open Set

set_option linter.deprecated false

namespace CatalanCore.Zeta5.Profile

section Gen

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K]

/-- `T = ⌊23 x / 10⌋`. -/
def gT (x : K) : ℤ := ⌊(23 / 10 : K) * x⌋

/-- `u = 23x/20 − T/2`. -/
def gu (x : K) : K := 23 / 20 * x - (gT x : K) / 2

/-- `s = 1/2 − te`. -/
def gs (x : K) : K := 1 / 2 - tri x

/-- `q = (tn − te)₊`. -/
def gq (x : K) : K := max 0 (tri (al * x) - tri x)

/-- `e`. -/
def ge (x : K) : K :=
  if Int.fract x < 1 / 2 then max 0 (gu x - tri x) else min (gu x) (gs x)

/-- The parity refinement density `g_ref`. -/
def gref (x : K) : K :=
  if gT x % 2 = 0 then max 0 (ge x - gq x) else max 0 (gs x - ge x - gq x)

/-- Guard 1: `tn − te`. -/
def G1 (x : K) : K := tri (al * x) - tri x
/-- Guard 2: `u − te`. -/
def G2 (x : K) : K := gu x - tri x
/-- Guard 3: `u − s`. -/
def G3 (x : K) : K := gu x - gs x
/-- Guard 4: `e − q`. -/
def G4 (x : K) : K := ge x - gq x
/-- Guard 5: `s − e − q`. -/
def G5 (x : K) : K := gs x - ge x - gq x

lemma gu_bounds (x : K) : 0 ≤ gu x ∧ gu x < 1 / 2 := by
  have h0 := Int.fract_nonneg ((23 / 10 : K) * x)
  have h1 := Int.fract_lt_one ((23 / 10 : K) * x)
  have e : gu x = Int.fract ((23 / 10 : K) * x) / 2 := by
    unfold gu gT Int.fract; ring
  rw [e]; constructor <;> linarith

lemma gs_bounds (x : K) : 0 ≤ gs x ∧ gs x ≤ 1 / 2 := by
  have := tri_nonneg x; have := tri_le_half x
  unfold gs; constructor <;> linarith

lemma ge_bounds (x : K) : 0 ≤ ge x ∧ ge x ≤ 1 / 2 := by
  have hu := gu_bounds x; have hs := gs_bounds x
  have ht := tri_nonneg x
  unfold ge
  split_ifs
  · exact ⟨le_max_left _ _, max_le (by norm_num) (by linarith)⟩
  · exact ⟨le_min hu.1 hs.1, le_trans (min_le_left _ _) (by linarith)⟩

omit [IsStrictOrderedRing K] in
lemma gq_nonneg (x : K) : 0 ≤ gq x := le_max_left _ _

omit [IsStrictOrderedRing K] in
/-- ZC27: `0 ≤ g_ref`. -/
theorem gref_nonneg (x : K) : 0 ≤ gref x := by
  unfold gref; split_ifs <;> exact le_max_left _ _

/-- ZC27: `g_ref ≤ 1/2`. -/
theorem gref_le_half (x : K) : gref x ≤ 1 / 2 := by
  have he := ge_bounds x; have hs := gs_bounds x; have hq := gq_nonneg x
  unfold gref
  split_ifs
  · exact max_le (by norm_num) (by linarith)
  · exact max_le (by norm_num) (by linarith)

end Gen

/-! ### Affine pieces -/

/-- `φ` is affine on `(l, r)`. -/
def Aff (l r : ℝ) (φ : ℝ → ℝ) : Prop := ∃ a b : ℝ, ∀ t ∈ Ioo l r, φ t = a * t + b

/-- `φ` has a weakly constant sign on `(l, r)`. -/
def WS (l r : ℝ) (φ : ℝ → ℝ) : Prop :=
  (∀ t ∈ Ioo l r, 0 ≤ φ t) ∨ (∀ t ∈ Ioo l r, φ t ≤ 0)

/-- The trisection sign test for a guard `φ`: the extrapolated end values `φ(l), φ(r)` do not
have strictly opposite signs. -/
def wsTest {K : Type*} [Field K] [LinearOrder K] (φ : K → K) (l r : K) : Prop :=
  0 ≤ (2 * φ ((2 * l + r) / 3) - φ ((l + 2 * r) / 3)) *
    (2 * φ ((l + 2 * r) / 3) - φ ((2 * l + r) / 3))

/-- Boolean form over `ℚ`. -/
def wsTestB (φ : ℚ → ℚ) (l r : ℚ) : Bool :=
  decide (0 ≤ (2 * φ ((2 * l + r) / 3) - φ ((l + 2 * r) / 3)) *
    (2 * φ ((l + 2 * r) / 3) - φ ((2 * l + r) / 3)))

section affine
variable {l r : ℝ} {φ ψ : ℝ → ℝ}

lemma Aff.add (h1 : Aff l r φ) (h2 : Aff l r ψ) : Aff l r (fun t => φ t + ψ t) := by
  obtain ⟨a, b, h⟩ := h1; obtain ⟨c, d, h'⟩ := h2
  exact ⟨a + c, b + d, fun t ht => by beta_reduce; rw [h t ht, h' t ht]; ring⟩

lemma Aff.sub (h1 : Aff l r φ) (h2 : Aff l r ψ) : Aff l r (fun t => φ t - ψ t) := by
  obtain ⟨a, b, h⟩ := h1; obtain ⟨c, d, h'⟩ := h2
  exact ⟨a - c, b - d, fun t ht => by beta_reduce; rw [h t ht, h' t ht]; ring⟩

lemma Aff.const_mul (c : ℝ) (h1 : Aff l r φ) : Aff l r (fun t => c * φ t) := by
  obtain ⟨a, b, h⟩ := h1
  exact ⟨c * a, c * b, fun t ht => by beta_reduce; rw [h t ht]; ring⟩

lemma Aff.of_const (c : ℝ) : Aff l r (fun _ => c) := ⟨0, c, fun t _ => by ring⟩

lemma Aff.of_id : Aff l r (fun t => t) := ⟨1, 0, fun t _ => by ring⟩

lemma Aff.congr (h : Aff l r φ) (heq : ∀ t ∈ Ioo l r, φ t = ψ t) : Aff l r ψ := by
  obtain ⟨a, b, h⟩ := h
  exact ⟨a, b, fun t ht => by rw [← heq t ht, h t ht]⟩

lemma Aff.max0 (h : Aff l r φ) (w : WS l r φ) : Aff l r (fun t => max 0 (φ t)) := by
  rcases w with w | w
  · exact h.congr (fun t ht => (max_eq_right (w t ht)).symm)
  · exact (Aff.of_const (l := l) (r := r) 0).congr (fun t ht => (max_eq_left (w t ht)).symm)

lemma Aff.min (hu : Aff l r φ) (hs : Aff l r ψ) (w : WS l r (fun t => φ t - ψ t)) :
    Aff l r (fun t => min (φ t) (ψ t)) := by
  rcases w with w | w
  · exact hs.congr (fun t ht => (min_eq_right (by linarith [w t ht])).symm)
  · exact hu.congr (fun t ht => (min_eq_left (by linarith [w t ht])).symm)

lemma ws_of_test (hlr : l < r) (h : Aff l r φ)
    (htest : wsTest φ l r) : WS l r φ := by
  obtain ⟨a, b, h⟩ := h
  have hx : (2 * l + r) / 3 ∈ Ioo l r := ⟨by linarith, by linarith⟩
  have hy : (l + 2 * r) / 3 ∈ Ioo l r := ⟨by linarith, by linarith⟩
  unfold wsTest at htest
  rw [h _ hx, h _ hy] at htest
  have e1 : 2 * (a * ((2 * l + r) / 3) + b) - (a * ((l + 2 * r) / 3) + b) = a * l + b := by ring
  have e2 : 2 * (a * ((l + 2 * r) / 3) + b) - (a * ((2 * l + r) / 3) + b) = a * r + b := by ring
  rw [e1, e2] at htest
  have key : ∀ t ∈ Ioo l r, (r - l) * (a * t + b) = (r - t) * (a * l + b) + (t - l) * (a * r + b) := by
    intro t _; ring
  rcases mul_nonneg_iff.1 htest with ⟨p, q⟩ | ⟨p, q⟩
  · left
    intro t ht
    rw [h t ht]
    have := key t ht
    have hrt : 0 ≤ r - t := by linarith [ht.2]
    have htl : 0 ≤ t - l := by linarith [ht.1]
    have : 0 ≤ (r - l) * (a * t + b) := by
      rw [key t ht]; exact add_nonneg (mul_nonneg hrt p) (mul_nonneg htl q)
    exact nonneg_of_mul_nonneg_right this (by linarith)
  · right
    intro t ht
    rw [h t ht]
    have hrt : 0 ≤ r - t := by linarith [ht.2]
    have htl : 0 ≤ t - l := by linarith [ht.1]
    have : (r - l) * (a * t + b) ≤ 0 := by
      rw [key t ht]; exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos hrt p)
        (mul_nonpos_of_nonneg_of_nonpos htl q)
    exact nonpos_of_mul_nonpos_right this (by linarith)

end affine


section cell
variable {l r : ℝ}

lemma fract_lt_iff_sg {t m : ℝ} (h : sg t = sg m) : Int.fract t < 1 / 2 ↔ Int.fract m < 1 / 2 := by
  unfold sg at h
  by_cases a : Int.fract t < 1 / 2 <;> by_cases b : Int.fract m < 1 / 2
  · exact ⟨fun _ => b, fun _ => a⟩
  · exfalso; simp only [a, b, ↓reduceIte] at h; norm_num at h
  · exfalso; simp only [a, b, ↓reduceIte] at h; norm_num at h
  · exact ⟨fun h' => absurd h' a, fun h' => absurd h' b⟩

/-- **ZC31.** `g_ref` is affine on a cell with constant floors and no strict guard sign change. -/
theorem gref_affine_cell (hlr : l < r) (h2 : NoPt 2 l r) (h6 : NoPt (3 / 10) l r)
    (h4 : NoPt (23 / 10) l r)
    (T1 : wsTest (G1 : ℝ → ℝ) l r) (T2 : wsTest (G2 : ℝ → ℝ) l r)
    (T3 : wsTest (G3 : ℝ → ℝ) l r) (T4 : wsTest (G4 : ℝ → ℝ) l r)
    (T5 : wsTest (G5 : ℝ → ℝ) l r) :
    ∃ A B : ℝ, ∀ t ∈ Ioo l r, gref t = A * t + B := by
  set m : ℝ := (l + r) / 2 with hmdef
  have hm : m ∈ Ioo l r := ⟨by rw [hmdef]; linarith, by rw [hmdef]; linarith⟩
  have hTri : Aff l r (fun t : ℝ => tri t) :=
    ⟨sg m, (1 - sg m) / 2 - sg m * ⌊m⌋, fun t ht => by
      obtain ⟨s1, f1⟩ := sg_const h2 ht hm
      beta_reduce
      rw [tri_eq, s1, Int.fract, f1]; ring⟩
  have hTriAl : Aff l r (fun t : ℝ => tri (al * t)) :=
    ⟨sg (al * m) * al, (1 - sg (al * m)) / 2 - sg (al * m) * ⌊al * m⌋, fun t ht => by
      obtain ⟨s1, f1⟩ := sg_const_al h6 ht hm
      beta_reduce
      rw [tri_eq, s1, Int.fract, f1]; ring⟩
  have hG1 : Aff l r (G1 : ℝ → ℝ) := hTriAl.sub hTri
  have W1 := ws_of_test hlr hG1 T1
  have hq : Aff l r (gq : ℝ → ℝ) := hG1.max0 W1
  have hgT : ∀ t ∈ Ioo l r, gT t = gT m := by
    intro t ht
    unfold gT
    exact floor_const (by norm_num) h4 ht hm
  have hu : Aff l r (gu : ℝ → ℝ) :=
    ⟨23 / 20, -((gT m : ℤ) : ℝ) / 2, fun t ht => by
      unfold gu; rw [hgT t ht]; ring⟩
  have hgs : Aff l r (gs : ℝ → ℝ) := (Aff.of_const (1 / 2)).sub hTri
  have hG2 : Aff l r (G2 : ℝ → ℝ) := hu.sub hTri
  have hG3 : Aff l r (G3 : ℝ → ℝ) := hu.sub hgs
  have W2 := ws_of_test hlr hG2 T2
  have W3 := ws_of_test hlr hG3 T3
  have hge : Aff l r (ge : ℝ → ℝ) := by
    by_cases hc : Int.fract m < 1 / 2
    · refine (hG2.max0 W2).congr (fun t ht => ?_)
      have := (fract_lt_iff_sg (sg_const h2 ht hm).1).2 hc
      unfold ge; rw [if_pos this]; try rfl
    · refine (hu.min hgs W3).congr (fun t ht => ?_)
      have : ¬ Int.fract t < 1 / 2 := fun h => hc ((fract_lt_iff_sg (sg_const h2 ht hm).1).1 h)
      unfold ge; rw [if_neg this]; try rfl
  have hG4 : Aff l r (G4 : ℝ → ℝ) := hge.sub hq
  have hG5 : Aff l r (G5 : ℝ → ℝ) := (hgs.sub hge).sub hq
  have W4 := ws_of_test hlr hG4 T4
  have W5 := ws_of_test hlr hG5 T5
  have key : Aff l r (gref : ℝ → ℝ) := by
    by_cases hp : gT m % 2 = 0
    · refine (hG4.max0 W4).congr (fun t ht => ?_)
      unfold gref; rw [if_pos (by rw [hgT t ht]; exact hp)]; try rfl
    · refine (hG5.max0 W5).congr (fun t ht => ?_)
      unfold gref; rw [if_neg (by rw [hgT t ht]; exact hp)]; try rfl
  exact key

end cell

/-! ### The rational test and the evaluator -/

lemma lt_half_cast (y : ℚ) : y < 1 / 2 ↔ (y : ℝ) < 1 / 2 := by
  have := (Rat.cast_lt (K := ℝ) (p := y) (q := 1 / 2))
  simpa using this.symm

lemma gT_cast (q : ℚ) : gT (q : ℝ) = gT q := by
  unfold gT
  rw [← Rat.floor_cast (α := ℝ)]; push_cast; rfl

lemma gu_cast (q : ℚ) : ((gu q : ℚ) : ℝ) = gu (q : ℝ) := by
  unfold gu; rw [← gT_cast]; push_cast; rfl

lemma gs_cast (q : ℚ) : ((gs q : ℚ) : ℝ) = gs (q : ℝ) := by
  unfold gs; push_cast; rw [tri_cast]

lemma al_cast : ((al : ℚ) : ℝ) = (al : ℝ) := by unfold al; norm_num

lemma gq_cast (q : ℚ) : ((gq q : ℚ) : ℝ) = gq (q : ℝ) := by
  unfold gq
  simp only [Rat.cast_max, Rat.cast_sub, Rat.cast_zero, tri_cast, Rat.cast_mul, al_cast]

lemma ge_cast (q : ℚ) : ((ge q : ℚ) : ℝ) = ge (q : ℝ) := by
  unfold ge
  by_cases h : Int.fract q < 1 / 2
  · have h' : Int.fract (q : ℝ) < 1 / 2 := by rw [← fract_cast]; exact (lt_half_cast _).1 h
    rw [if_pos h, if_pos h']
    simp only [Rat.cast_max, Rat.cast_sub, Rat.cast_zero, gu_cast, tri_cast]
  · have h' : ¬ Int.fract (q : ℝ) < 1 / 2 := by
      rw [← fract_cast]; intro hc; exact h ((lt_half_cast _).2 hc)
    rw [if_neg h, if_neg h']
    simp only [Rat.cast_min, gu_cast, gs_cast]

lemma gref_cast (q : ℚ) : ((gref q : ℚ) : ℝ) = gref (q : ℝ) := by
  unfold gref
  simp only [gT_cast]
  split_ifs
  · simp only [Rat.cast_max, Rat.cast_sub, Rat.cast_zero, ge_cast, gq_cast]
  · simp only [Rat.cast_max, Rat.cast_sub, Rat.cast_zero, ge_cast, gq_cast, gs_cast]

lemma G1_cast (q : ℚ) : ((G1 q : ℚ) : ℝ) = G1 (q : ℝ) := by
  unfold G1; simp only [Rat.cast_sub, tri_cast, Rat.cast_mul, al_cast]

lemma G2_cast (q : ℚ) : ((G2 q : ℚ) : ℝ) = G2 (q : ℝ) := by
  unfold G2; simp only [Rat.cast_sub, tri_cast, gu_cast]

lemma G3_cast (q : ℚ) : ((G3 q : ℚ) : ℝ) = G3 (q : ℝ) := by
  unfold G3; simp only [Rat.cast_sub, gs_cast, gu_cast]

lemma G4_cast (q : ℚ) : ((G4 q : ℚ) : ℝ) = G4 (q : ℝ) := by
  unfold G4; simp only [Rat.cast_sub, ge_cast, gq_cast]

lemma G5_cast (q : ℚ) : ((G5 q : ℚ) : ℝ) = G5 (q : ℝ) := by
  unfold G5; simp only [Rat.cast_sub, ge_cast, gq_cast, gs_cast]

lemma wsTest_of_B {φ : ℚ → ℚ} {Φ : ℝ → ℝ} (h : ∀ q : ℚ, ((φ q : ℚ) : ℝ) = Φ q) {l r : ℚ}
    (hb : wsTestB φ l r = true) : wsTest Φ (l : ℝ) (r : ℝ) := by
  unfold wsTestB at hb
  simp only [decide_eq_true_eq] at hb
  have := (Rat.cast_le (K := ℝ)).2 hb
  push_cast at this
  simp only [h] at this
  push_cast at this
  exact this

/-- The slopes whose points `n/c` bound the cells of `g_ref`. -/
def gslopes : List ℚ := [2, 3 / 10, 23 / 10]

/-- Decidable cell test for `g_ref`. -/
def cellOKg (l r : ℚ) : Bool :=
  (gslopes.all fun c => decide (r * c ≤ ⌊l * c⌋ + 1)) &&
    wsTestB G1 l r && wsTestB G2 l r && wsTestB G3 l r && wsTestB G4 l r && wsTestB G5 l r

/-- Test of a whole cut list. -/
def chainOKg : ℚ → List ℚ → Bool
  | _, [] => true
  | l, r :: t => decide (l < r) && cellOKg l r && chainOKg r t

lemma chainOKg_append (ts1 ts2 : List ℚ) :
    ∀ l : ℚ, chainOKg l (ts1 ++ ts2) = (chainOKg l ts1 && chainOKg (endpt l ts1) ts2) := by
  induction ts1 with
  | nil => intro l; simp [chainOKg, endpt]
  | cons r t ih => intro l; simp [chainOKg, endpt, ih, Bool.and_assoc]

lemma cellOKg_affine {l r : ℚ} (hlr : l < r) (h : cellOKg l r = true) :
    ∃ A B : ℝ, ∀ t ∈ Ioo (l : ℝ) r, gref t = A * t + B := by
  simp only [cellOKg, gslopes, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
    decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨a, b, c⟩, d1⟩, d2⟩, d3⟩, d4⟩, d5⟩ := h
  have hlr' : (l : ℝ) < r := by exact_mod_cast hlr
  refine gref_affine_cell hlr' ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · simpa using noPt_of_check (c := 2) (by norm_num) a
  · simpa using noPt_of_check (c := 3 / 10) (by norm_num) b
  · simpa using noPt_of_check (c := 23 / 10) (by norm_num) c
  · exact wsTest_of_B G1_cast d1
  · exact wsTest_of_B G2_cast d2
  · exact wsTest_of_B G3_cast d3
  · exact wsTest_of_B G4_cast d4
  · exact wsTest_of_B G5_cast d5

lemma okChain_of_chainOKg : ∀ (ts : List ℚ) (l : ℚ), chainOKg l ts = true →
    okChain (fun l r => ∃ A B : ℝ, ∀ t ∈ Ioo (l : ℝ) r, gref t = A * t + B) l ts := by
  intro ts
  induction ts with
  | nil => intro l _; trivial
  | cons r t ih =>
    intro l h
    simp only [chainOKg, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hlr, hc⟩, hrest⟩ := h
    exact ⟨hlr, cellOKg_affine hlr hc, ih r hrest⟩

/-- **ZC31 + ZC33 for `g_ref`.** On a cut list passing the rational test, `∫ g_ref(t) t⁻³ dt`
is the rational `chain gref l ts`. -/
theorem gref_chain_sound (ts : List ℚ) (l : ℚ) (hl : 0 < l) (h : chainOKg l ts = true) :
    ∫ t in (l : ℝ)..(endpt l ts : ℚ), gref t / t ^ 3 = ((chain gref l ts : ℚ) : ℝ) :=
  (chain_sound (H := (gref : ℝ → ℝ)) (h := (gref : ℚ → ℚ)) (fun q => (gref_cast q).symm) ts l hl
    (okChain_of_chainOKg ts l h)).2

end CatalanCore.Zeta5.Profile
