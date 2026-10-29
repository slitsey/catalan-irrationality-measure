import CatalanCore.Uniform.Content.RankProducer.ClosedCert
import CatalanCore.Uniform.Content.UFSimple.Count
import CatalanCore.Uniform.Content.Wire.Shape
import CatalanCore.Uniform.Bank.Chi3Rank.Fibre
set_option Elab.async false

/-! # Fibre shapes of a member of a hybrid-shaped geometry (Lemma 1 of C2/PAPER.md, lane C2L)

For a geometry with `C = [0, r)`, `xs i = r + 2i`, `ys i = r + 2i + 1` (`HybShape`), a retained set
`T` and a prime `p > 2m`:

* a border node `t ∈ [r, r + 2m)` is the only border node of its residue class, its fibre has
  common digits `0..t/p - 1` (`lt_of_digit`, `digit_lt`), and it is a row iff `t - r` is even;
* a square residue `x0 < r ≤ r + 2m - p ≤ x0` has the single digit `0` and no border node.

`real_row`, `real_col`, `real_sq`: when the fibre is untouched by the deletion, the actual fibre of
the member realises `bordRow`, `bordCol`, `sqCert` with the palette of the fibre.
-/

namespace CatalanCore.Uniform.Content.RankProducer
open Finset CatalanCore CatalanCore.Basic CatalanCore.Uniform CatalanCore.Uniform.Content.Hybrid
  CatalanCore.Uniform.Content.Member CatalanCore.Uniform.Content.Wire

section Nodes
variable {G : BlockGeom} {r : ℕ}

/-- `n` is a retained common node of the member `T`. -/
def keptN (T : Finset (G.geometry r).C) (n : ℕ) : Prop := ∃ a ∈ T, (a : ℕ) = n

/-- Row nodes of the member. -/
noncomputable abbrev rowsM (T : Finset (G.geometry r).C) : T ⊕ Fin (G.geometry r).k → ℕ :=
  memberRows (fun a : (G.geometry r).C => (a : ℕ)) (G.geometry r).xs T

/-- Column nodes of the member. -/
noncomputable abbrev colsM (T : Finset (G.geometry r).C) : T ⊕ Fin (G.geometry r).k → ℕ :=
  memberCols (fun a : (G.geometry r).C => (a : ℕ)) (G.geometry r).ys T

theorem keptN_lt (hs : HybShape G r) {T : Finset (G.geometry r).C} {n : ℕ} (h : keptN T n) :
    n < r := by
  obtain ⟨⟨n', hn'⟩, _, rfl⟩ := h
  rw [hs.C_eq] at hn'
  exact Finset.mem_range.1 hn'

theorem rowsM_iff (hs : HybShape G r) (T : Finset (G.geometry r).C) (n : ℕ) :
    (∃ i, rowsM T i = n) ↔
      keptN T n ∨ (r ≤ n ∧ n < r + 2 * (G.geometry r).k ∧ (n - r) % 2 = 0) := by
  constructor
  · rintro ⟨i, rfl⟩
    rcases i with ⟨a, ha⟩ | j
    · exact Or.inl ⟨a, ha, rfl⟩
    · right
      show r ≤ (G.geometry r).xs j ∧ (G.geometry r).xs j < r + 2 * (G.geometry r).k ∧
        ((G.geometry r).xs j - r) % 2 = 0
      rw [hs.xs_eq j]
      have := j.2
      omega
  · rintro (⟨a, ha, rfl⟩ | ⟨h1, h2, h3⟩)
    · exact ⟨Sum.inl ⟨a, ha⟩, rfl⟩
    · refine ⟨Sum.inr ⟨(n - r) / 2, by omega⟩, ?_⟩
      show (G.geometry r).xs _ = n
      rw [hs.xs_eq]
      simp only
      omega

theorem colsM_iff (hs : HybShape G r) (T : Finset (G.geometry r).C) (n : ℕ) :
    (∃ i, colsM T i = n) ↔
      keptN T n ∨ (r + 1 ≤ n ∧ n < r + 2 * (G.geometry r).k ∧ (n - r) % 2 = 1) := by
  constructor
  · rintro ⟨i, rfl⟩
    rcases i with ⟨a, ha⟩ | j
    · exact Or.inl ⟨a, ha, rfl⟩
    · right
      show r + 1 ≤ (G.geometry r).ys j ∧ (G.geometry r).ys j < r + 2 * (G.geometry r).k ∧
        ((G.geometry r).ys j - r) % 2 = 1
      rw [hs.ys_eq j]
      have := j.2
      omega
  · rintro (⟨a, ha, rfl⟩ | ⟨h1, h2, h3⟩)
    · exact ⟨Sum.inl ⟨a, ha⟩, rfl⟩
    · refine ⟨Sum.inr ⟨(n - r - 1) / 2, by omega⟩, ?_⟩
      show (G.geometry r).ys _ = n
      rw [hs.ys_eq]
      simp only
      omega

theorem rowsM_inj (hs : HybShape G r) (T : Finset (G.geometry r).C) :
    Function.Injective (rowsM T) := by
  intro i j h
  rcases i with ⟨a, ha⟩ | i <;> rcases j with ⟨b, hb⟩ | j
  · exact congrArg Sum.inl (Subtype.ext (Subtype.ext h))
  · have h1 := keptN_lt hs ⟨a, ha, rfl⟩
    change (a : ℕ) = (G.geometry r).xs j at h
    rw [hs.xs_eq] at h; omega
  · have h1 := keptN_lt hs ⟨b, hb, rfl⟩
    change (G.geometry r).xs i = (b : ℕ) at h
    rw [hs.xs_eq] at h; omega
  · change (G.geometry r).xs i = (G.geometry r).xs j at h
    rw [hs.xs_eq, hs.xs_eq] at h
    exact congrArg Sum.inr (Fin.ext (by omega))

theorem colsM_inj (hs : HybShape G r) (T : Finset (G.geometry r).C) :
    Function.Injective (colsM T) := by
  intro i j h
  rcases i with ⟨a, ha⟩ | i <;> rcases j with ⟨b, hb⟩ | j
  · exact congrArg Sum.inl (Subtype.ext (Subtype.ext h))
  · have h1 := keptN_lt hs ⟨a, ha, rfl⟩
    change (a : ℕ) = (G.geometry r).ys j at h
    rw [hs.ys_eq] at h; omega
  · have h1 := keptN_lt hs ⟨b, hb, rfl⟩
    change (G.geometry r).ys i = (b : ℕ) at h
    rw [hs.ys_eq] at h; omega
  · change (G.geometry r).ys i = (G.geometry r).ys j at h
    rw [hs.ys_eq, hs.ys_eq] at h
    exact congrArg Sum.inr (Fin.ext (by omega))

theorem rowsM_lt (hs : HybShape G r) (T : Finset (G.geometry r).C) (i : T ⊕ Fin (G.geometry r).k) :
    rowsM T i < r + 2 * (G.geometry r).k := by
  have := (rowsM_iff hs T (rowsM T i)).1 ⟨i, rfl⟩
  rcases this with h | h
  · have := keptN_lt hs h; omega
  · omega

theorem colsM_lt (hs : HybShape G r) (T : Finset (G.geometry r).C) (i : T ⊕ Fin (G.geometry r).k) :
    colsM T i < r + 2 * (G.geometry r).k := by
  have := (colsM_iff hs T (colsM T i)).1 ⟨i, rfl⟩
  rcases this with h | h
  · have := keptN_lt hs h; omega
  · omega

end Nodes

section Digits
variable {p : ℕ}

/-- Two congruent nodes at distance `< p` coincide. -/
theorem eq_of_mod_eq {n t : ℕ} (hp : 0 < p) (hmod : n % p = t % p) (h1 : n < t + p)
    (h2 : t < n + p) : n = t := by
  have h : ((n : ℕ) : ZMod p) = ((t : ℕ) : ZMod p) := (ZMod.natCast_eq_natCast_iff' n t p).2 hmod
  rcases UFSimple.modEq_cases hp (by omega) (by omega) h with h | h | h <;> omega

/-- A common node (`< r`) congruent to the border node `t ≥ r` has a smaller digit. -/
theorem digit_lt_of_lt {n t r : ℕ} (hp : 0 < p) (hmod : n % p = t % p) (hn : n < r) (ht : r ≤ t) :
    n / p < t / p := by
  have e1 := Nat.div_add_mod n p
  have e2 := Nat.div_add_mod t p
  by_contra hc
  push_neg at hc
  have := Nat.mul_le_mul_left p hc
  omega

/-- Below the border node `t < r + p`, every lower digit of its class is a common node. -/
theorem lt_of_digit {t r d : ℕ} (hp : 0 < p) (ht : t < r + p) (hd : d < t / p) :
    t % p + p * d < r := by
  have e2 := Nat.div_add_mod t p
  have := Nat.mul_le_mul_left p (show d + 1 ≤ t / p from hd)
  rw [Nat.mul_add, Nat.mul_one] at this
  omega

theorem node_split (n : ℕ) : n % p + p * (n / p) = n := by
  have := Nat.div_add_mod n p; omega

theorem mod_digit {x0 d : ℕ} (hx0 : x0 < p) : (x0 + p * d) % p = x0 := by
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx0]

theorem div_digit {x0 d : ℕ} (hx0 : x0 < p) : (x0 + p * d) / p = d := by
  have hp : 0 < p := by omega
  rw [Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt hx0, zero_add]

end Digits

section Realize
variable {G : BlockGeom} {r : ℕ} {p : ℕ} [hp : Fact p.Prime] {B : ℕ} {f e : ℕ → ℚ}

/-- The fibre of an untouched row border node realises `bordRow`. -/
theorem real_row (hs : HybShape G r) (T : Finset (G.geometry r).C) (PS : PoleSplit p B f e)
    (t : ℕ) (ht1 : r ≤ t) (ht2 : t < r + 2 * (G.geometry r).k) (hpar : (t - r) % 2 = 0)
    (hpm : 2 * (G.geometry r).k < p) (hunt : ∀ d < t / p, keptN T (t % p + p * d))
    (lf ee : ℕ → ℚ) (hlf : ∀ d, PS.Lf (t % p + p * d) = lf d)
    (hee : ∀ d, PS.E (t % p + p * d) = ee d) (u : ℕ → ℚ) (i0 : ℕ) :
    Realizes PS (rowsM T) (colsM T) ((t % p : ℕ) : ZMod p) (bordRow lf ee (t / p) u i0) := by
  have hp0 := hp.out.pos
  have hx0 : t % p < p := Nat.mod_lt t hp0
  have hsplit : t % p + p * (t / p) = t := node_split t
  have hnode : ∀ n, n % p = t % p → t % p + p * (n / p) = n := fun n h => by
    have := node_split (p := p) n; rw [h] at this; exact this
  refine CatalanCore.Uniform.Bank.Chi3Rank.realizes_of PS _ _ (t % p) hx0 _ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro i hmod
    show rowsM T i / p ∈ range (t / p + 1)
    rw [Finset.mem_range]
    rcases (rowsM_iff hs T _).1 ⟨i, rfl⟩ with h | ⟨h1, h2, _⟩
    · have := digit_lt_of_lt hp0 hmod (keptN_lt hs h) ht1; omega
    · have := eq_of_mod_eq hp0 hmod (by omega) (by omega)
      rw [this]; omega
  · intro d hd
    rw [show (bordRow lf ee (t / p) u i0).R = range (t / p + 1) from rfl, Finset.mem_range] at hd
    rcases Nat.lt_or_ge d (t / p) with hlt | hge
    · exact (rowsM_iff hs T _).2 (Or.inl (hunt d hlt))
    · have hdk : d = t / p := by omega
      rw [hdk, hsplit]
      exact (rowsM_iff hs T _).2 (Or.inr ⟨ht1, ht2, hpar⟩)
  · intro j hmod
    show colsM T j / p ∈ range (t / p)
    rw [Finset.mem_range]
    rcases (colsM_iff hs T _).1 ⟨j, rfl⟩ with h | ⟨h1, h2, h3⟩
    · exact digit_lt_of_lt hp0 hmod (keptN_lt hs h) ht1
    · have := eq_of_mod_eq hp0 hmod (by omega) (by omega)
      rw [this] at h3; omega
  · intro d hd
    rw [show (bordRow lf ee (t / p) u i0).C = range (t / p) from rfl, Finset.mem_range] at hd
    exact (colsM_iff hs T _).2 (Or.inl (hunt d hd))
  · intro i hmod
    show PS.Lf (rowsM T i) = lf (rowsM T i / p)
    rw [← hlf, hnode _ hmod]
  · intro j hmod
    show PS.Lf (colsM T j) = lf (colsM T j / p)
    rw [← hlf, hnode _ hmod]
  · intro i hmod
    show PS.E (rowsM T i) = ee (rowsM T i / p)
    rw [← hee, hnode _ hmod]

/-- The fibre of an untouched column border node realises `bordCol`. -/
theorem real_col (hs : HybShape G r) (T : Finset (G.geometry r).C) (PS : PoleSplit p B f e)
    (t : ℕ) (ht1 : r ≤ t) (ht2 : t < r + 2 * (G.geometry r).k) (hpar : (t - r) % 2 = 1)
    (hpm : 2 * (G.geometry r).k < p) (hunt : ∀ d < t / p, keptN T (t % p + p * d))
    (lf ee : ℕ → ℚ) (hlf : ∀ d, PS.Lf (t % p + p * d) = lf d)
    (hee : ∀ d, PS.E (t % p + p * d) = ee d) (u : ℕ → ℚ) (i0 : ℕ) :
    Realizes PS (rowsM T) (colsM T) ((t % p : ℕ) : ZMod p) (bordCol lf ee (t / p) u i0) := by
  have hp0 := hp.out.pos
  have hx0 : t % p < p := Nat.mod_lt t hp0
  have hsplit : t % p + p * (t / p) = t := node_split t
  have hnode : ∀ n, n % p = t % p → t % p + p * (n / p) = n := fun n h => by
    have := node_split (p := p) n; rw [h] at this; exact this
  refine CatalanCore.Uniform.Bank.Chi3Rank.realizes_of PS _ _ (t % p) hx0 _ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro i hmod
    show rowsM T i / p ∈ range (t / p)
    rw [Finset.mem_range]
    rcases (rowsM_iff hs T _).1 ⟨i, rfl⟩ with h | ⟨h1, h2, h3⟩
    · exact digit_lt_of_lt hp0 hmod (keptN_lt hs h) ht1
    · have := eq_of_mod_eq hp0 hmod (by omega) (by omega)
      rw [this] at h3; omega
  · intro d hd
    rw [show (bordCol lf ee (t / p) u i0).R = range (t / p) from rfl, Finset.mem_range] at hd
    exact (rowsM_iff hs T _).2 (Or.inl (hunt d hd))
  · intro j hmod
    show colsM T j / p ∈ range (t / p + 1)
    rw [Finset.mem_range]
    rcases (colsM_iff hs T _).1 ⟨j, rfl⟩ with h | ⟨h1, h2, _⟩
    · have := digit_lt_of_lt hp0 hmod (keptN_lt hs h) ht1; omega
    · have := eq_of_mod_eq hp0 hmod (by omega) (by omega)
      rw [this]; omega
  · intro d hd
    rw [show (bordCol lf ee (t / p) u i0).C = range (t / p + 1) from rfl, Finset.mem_range] at hd
    rcases Nat.lt_or_ge d (t / p) with hlt | hge
    · exact (colsM_iff hs T _).2 (Or.inl (hunt d hlt))
    · have hdk : d = t / p := by omega
      rw [hdk, hsplit]
      exact (colsM_iff hs T _).2 (Or.inr ⟨by omega, ht2, hpar⟩)
  · intro i hmod
    show PS.Lf (rowsM T i) = lf (rowsM T i / p)
    rw [← hlf, hnode _ hmod]
  · intro j hmod
    show PS.Lf (colsM T j) = lf (colsM T j / p)
    rw [← hlf, hnode _ hmod]
  · intro i hmod
    show PS.E (rowsM T i) = ee (rowsM T i / p)
    rw [← hee, hnode _ hmod]

/-- An untouched square residue (`x0 < r`, `r + 2m ≤ x0 + p`) realises `sqCert`. -/
theorem real_sq (hs : HybShape G r) (T : Finset (G.geometry r).C) (PS : PoleSplit p B f e)
    (x0 : ℕ) (hx0 : x0 < p) (hxr : x0 < r) (hxp : r + 2 * (G.geometry r).k ≤ x0 + p)
    (hkept : keptN T x0) (lf ee : ℕ → ℚ) (hlf : ∀ d, PS.Lf (x0 + p * d) = lf d)
    (hee : ∀ d, PS.E (x0 + p * d) = ee d) :
    Realizes PS (rowsM T) (colsM T) ((x0 : ℕ) : ZMod p) (sqCert lf ee) := by
  have hp0 := hp.out.pos
  have hnode : ∀ n, n % p = x0 → x0 + p * (n / p) = n := fun n h => by
    have := node_split (p := p) n; rw [h] at this; exact this
  -- every node of the class below `r + 2m` is `x0` itself
  have hzero : ∀ n, n % p = x0 → n < r + 2 * (G.geometry r).k → n / p = 0 := by
    intro n hmod hn
    have e := hnode n hmod
    by_contra hc
    have := Nat.mul_le_mul_left p (Nat.pos_of_ne_zero hc)
    omega
  have h0 : ∀ n, n % p = x0 → n < r + 2 * (G.geometry r).k → n / p ∈ (sqCert lf ee).R := by
    intro n hmod hn
    show n / p ∈ range 1
    rw [hzero n hmod hn]; simp
  have hcov : ∀ d ∈ range 1, d = 0 := fun d hd => by simpa using hd
  refine CatalanCore.Uniform.Bank.Chi3Rank.realizes_of PS _ _ x0 hx0 _ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro i hmod; exact h0 _ hmod (rowsM_lt hs T i)
  · intro d hd
    rw [hcov d hd, Nat.mul_zero, Nat.add_zero]
    exact (rowsM_iff hs T _).2 (Or.inl hkept)
  · intro j hmod; exact h0 _ hmod (colsM_lt hs T j)
  · intro d hd
    rw [hcov d hd, Nat.mul_zero, Nat.add_zero]
    exact (colsM_iff hs T _).2 (Or.inl hkept)
  · intro i hmod
    show PS.Lf (rowsM T i) = lf (rowsM T i / p)
    rw [← hlf, hnode _ hmod]
  · intro j hmod
    show PS.Lf (colsM T j) = lf (colsM T j / p)
    rw [← hlf, hnode _ hmod]
  · intro i hmod
    show PS.E (rowsM T i) = ee (rowsM T i / p)
    rw [← hee, hnode _ hmod]

end Realize

#print axioms real_row
#print axioms real_sq
end CatalanCore.Uniform.Content.RankProducer
