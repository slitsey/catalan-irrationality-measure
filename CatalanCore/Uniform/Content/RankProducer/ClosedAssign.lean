module

public import CatalanCore.Uniform.Content.RankProducer.ClosedFibre
public import CatalanCore.Uniform.Content.RankProducer.LineCost
public import CatalanCore.Uniform.Content.RankProducer.LineScores
public import CatalanCore.Uniform.Content.RankProducer.ActiveFibres

@[expose] public section
set_option Elab.async false

/-! # The closed certificate assignment and its line price (Theorem R, lane C2L)

Given untouched row border nodes `RA`, column border nodes `CA` (`|RA| = |CA|`) and untouched square
residues `SQ` (`Assign`), `closedCert` puts the class certificate (`clsRow`, `clsCol`, `sqCert`)
on their fibres and the trivial certificate elsewhere.  For a line class `l` with nonzero reduced
moment, `closed_member` builds the `RankMember` (`RankMember.ofLine`, `w` = the class moment) and
`price_line_bound` gives

  `price + max(|RA| + |SQ|, |RA_l| + |CA_l| + 2 [l = D0] |SQ|) ≤ 2 (|T| + m)`.
-/

namespace CatalanCore.Uniform.Content.RankProducer
open Finset Module CatalanCore CatalanCore.Basic CatalanCore.Uniform CatalanCore.Uniform.Content.Hybrid
  CatalanCore.Uniform.Content.Member CatalanCore.Uniform.Content.Wire
open scoped Classical

/-- Digit of the first node `≥ r` in the residue class `x0`. -/
def kOf (r p x0 : ℕ) : ℕ := r / p + if x0 < r % p then 1 else 0

theorem kOf_eq {r p t : ℕ} (hp : 0 < p) (h1 : r ≤ t) (h2 : t < r + p) :
    kOf r p (t % p) = t / p := by
  unfold kOf
  have er := Nat.div_add_mod r p
  have et := Nat.div_add_mod t p
  have hrs := Nat.mod_lt r hp
  have hts := Nat.mod_lt t hp
  generalize r / p = h at er ⊢
  generalize r % p = s at er hrs ⊢
  generalize t / p = a at et ⊢
  generalize t % p = b at et hts ⊢
  have hA : h ≤ a := by
    by_contra hc
    push_neg at hc
    have := Nat.mul_le_mul_left p (show a + 1 ≤ h by omega)
    rw [Nat.mul_add, Nat.mul_one] at this
    omega
  split_ifs with hbs
  · rcases Nat.eq_or_lt_of_le hA with hEq | hLt
    · rw [← hEq] at et; omega
    · have hB : a ≤ h + 1 := by
        by_contra hc
        push_neg at hc
        have := Nat.mul_le_mul_left p (show h + 2 ≤ a by omega)
        rw [Nat.mul_add] at this
        omega
      omega
  · rcases Nat.eq_or_lt_of_le hA with hEq | hLt
    · omega
    · have hB : a ≤ h + 1 := by
        by_contra hc
        push_neg at hc
        have := Nat.mul_le_mul_left p (show h + 2 ≤ a by omega)
        rw [Nat.mul_add] at this
        omega
      have ha1 : a = h + 1 := by omega
      rw [ha1, Nat.mul_add, Nat.mul_one] at et
      omega

/-- Line classes: `none` is D0 (moment `(1, L(0,0))`), `some (k, z)` a bordered class. -/
abbrev LineCls := Option (ℕ × Bool)

/-- Membership of a fibre shape `(k, z)` in a line class. -/
def inCls : LineCls → ℕ → Bool → Prop
  | none, k, z => k ≤ 1 ∧ z = false
  | some (kl, zl), k, z => k = kl ∧ z = zl

/-- The line moment of a class. -/
noncomputable def clsMomL (Lz Ez : Bool → ℕ → ℚ) : LineCls → ℚ × ℚ
  | none => (1, Lz false 0)
  | some (kl, zl) => mom (Lz zl) kl (clsVec (Lz zl) (Ez zl) kl zl)

theorem mom_cls_of_inCls (Lz Ez : Bool → ℕ → ℚ) (l : LineCls) (k : ℕ) (z : Bool)
    (h : inCls l k z) : mom (Lz z) k (clsVec (Lz z) (Ez z) k z) = clsMomL Lz Ez l := by
  cases l with
  | none =>
    obtain ⟨hk, hz⟩ := h
    subst hz
    rw [clsVec_D0 _ _ _ _ ⟨hk, rfl⟩, mom_delta0]
    rfl
  | some kz =>
    obtain ⟨kl, zl⟩ := kz
    obtain ⟨hk, hz⟩ := h
    subst hk
    subst hz
    rfl

/-- The row-role class certificate. -/
noncomputable abbrev clsRow (Lz Ez : Bool → ℕ → ℚ) (k : ℕ) (z : Bool) : FibreCert :=
  bordRow (Lz z) (Ez z) k (clsVec (Lz z) (Ez z) k z) (clsIdx (Lz z) (Ez z) k z)

/-- The column-role class certificate. -/
noncomputable abbrev clsCol (Lz Ez : Bool → ℕ → ℚ) (k : ℕ) (z : Bool) : FibreCert :=
  bordCol (Lz z) (Ez z) k (clsVec (Lz z) (Ez z) k z) (clsIdx (Lz z) (Ez z) k z)

/-- The bundled hypotheses on the active fibres. -/
structure Assign {G : BlockGeom} (r m p ρ : ℕ) (T : Finset (G.geometry r).C)
    (RA CA SQ : Finset ℕ) : Prop where
  hRA : ∀ t ∈ RA, r ≤ t ∧ t < r + 2 * m ∧ (t - r) % 2 = 0 ∧ ∀ d < t / p, keptN T (t % p + p * d)
  hCA : ∀ t ∈ CA, r ≤ t ∧ t < r + 2 * m ∧ (t - r) % 2 = 1 ∧ ∀ d < t / p, keptN T (t % p + p * d)
  hSQ : ∀ x0 ∈ SQ, x0 < r ∧ r + 2 * m ≤ x0 + p ∧ x0 < ρ ∧ keptN T x0
  hcard : RA.card = CA.card
  hρp : ρ < p

section Assignment
variable {p : ℕ} [hp : Fact p.Prime] {ι : Type*} [Fintype ι] [DecidableEq ι] {B : ℕ} {f e : ℕ → ℚ}

/-- The closed certificate assignment. -/
noncomputable def closedCert (PS : PoleSplit p B f e) (a b : ι → ℕ) (r ρ : ℕ)
    (Lz Ez : Bool → ℕ → ℚ) (RA CA SQ : Finset ℕ) (x : ZMod p) : FibreCert :=
  if x.val ∈ RA.image (· % p) then clsRow Lz Ez (kOf r p x.val) (decide (ρ ≤ x.val))
  else if x.val ∈ CA.image (· % p) then clsCol Lz Ez (kOf r p x.val) (decide (ρ ≤ x.val))
  else if x.val ∈ SQ then sqCert (Lz (decide (ρ ≤ x.val))) (Ez (decide (ρ ≤ x.val)))
  else trivCert PS a b x

/-- The window of the active objects, where residues are injective. -/
theorem assign_window {G : BlockGeom} {r m ρ : ℕ} {T : Finset (G.geometry r).C}
    {RA CA SQ : Finset ℕ} (hA : Assign r m p ρ T RA CA SQ) (hpm : 2 * m < p) :
    ∀ n ∈ RA ∪ CA ∪ SQ, r + 2 * m - p ≤ n ∧ n < r + 2 * m := by
  intro n hn
  rcases Finset.mem_union.1 hn with hn | hn
  · rcases Finset.mem_union.1 hn with hn | hn
    · obtain ⟨h1, h2, -⟩ := hA.hRA n hn; omega
    · obtain ⟨h1, h2, -⟩ := hA.hCA n hn; omega
  · obtain ⟨h1, h2, -⟩ := hA.hSQ n hn; omega

theorem assign_inj {G : BlockGeom} {r m ρ : ℕ} {T : Finset (G.geometry r).C}
    {RA CA SQ : Finset ℕ} (hA : Assign r m p ρ T RA CA SQ) (hpm : 2 * m < p) :
    ∀ n ∈ RA ∪ CA ∪ SQ, ∀ n' ∈ RA ∪ CA ∪ SQ, n % p = n' % p → n = n' := by
  intro n hn n' hn' h
  have w1 := assign_window hA hpm n hn
  have w2 := assign_window hA hpm n' hn'
  exact eq_of_mod_eq hp.out.pos h (by omega) (by omega)

/-- Case analysis of the assignment at a residue. -/
theorem closedCert_cases (PS : PoleSplit p B f e) (a b : ι → ℕ) {G : BlockGeom} {r m ρ : ℕ}
    {T : Finset (G.geometry r).C} (Lz Ez : Bool → ℕ → ℚ) {RA CA SQ : Finset ℕ}
    (hA : Assign r m p ρ T RA CA SQ) (hpm : 2 * m < p) (x : ZMod p) :
    (∃ t ∈ RA, x.val = t % p ∧ closedCert PS a b r ρ Lz Ez RA CA SQ x =
        clsRow Lz Ez (t / p) (decide (ρ ≤ t % p))) ∨
      (∃ t ∈ CA, x.val = t % p ∧ closedCert PS a b r ρ Lz Ez RA CA SQ x =
        clsCol Lz Ez (t / p) (decide (ρ ≤ t % p))) ∨
      (∃ x0 ∈ SQ, x.val = x0 ∧ closedCert PS a b r ρ Lz Ez RA CA SQ x =
        sqCert (Lz false) (Ez false)) ∨
      closedCert PS a b r ρ Lz Ez RA CA SQ x = trivCert PS a b x := by
  have hp0 := hp.out.pos
  unfold closedCert
  split_ifs with h1 h2 h3
  · obtain ⟨t, ht, htx0⟩ := Finset.mem_image.1 h1
    have htx : t % p = x.val := htx0
    obtain ⟨t1, t2, -⟩ := hA.hRA t ht
    left
    refine ⟨t, ht, htx.symm, ?_⟩
    rw [← htx, kOf_eq hp0 t1 (by omega)]
  · obtain ⟨t, ht, htx0⟩ := Finset.mem_image.1 h2
    have htx : t % p = x.val := htx0
    obtain ⟨t1, t2, -⟩ := hA.hCA t ht
    right; left
    refine ⟨t, ht, htx.symm, ?_⟩
    rw [← htx, kOf_eq hp0 t1 (by omega)]
  · obtain ⟨-, -, hx3, -⟩ := hA.hSQ _ h3
    right; right; left
    refine ⟨x.val, h3, rfl, ?_⟩
    have hz : decide (ρ ≤ x.val) = false := decide_eq_false (by omega)
    rw [hz]
  · right; right; right; rfl

/-- Residues of the three kinds of active objects are pairwise distinct. -/
theorem assign_res_disj {G : BlockGeom} {r m ρ : ℕ} {T : Finset (G.geometry r).C}
    {RA CA SQ : Finset ℕ} (hA : Assign r m p ρ T RA CA SQ) (hpm : 2 * m < p) (y : ℕ) :
    (y ∈ RA.image (· % p) → y ∉ CA.image (· % p)) ∧
      (y ∈ RA.image (· % p) → y ∉ SQ) ∧ (y ∈ CA.image (· % p) → y ∉ SQ) := by
  have hinj := assign_inj hA hpm
  refine ⟨fun h1 h2 => ?_, fun h1 h2 => ?_, fun h1 h2 => ?_⟩
  · obtain ⟨t, ht, htx⟩ := Finset.mem_image.1 h1
    obtain ⟨t', ht', htx'⟩ := Finset.mem_image.1 h2
    have e1 : t % p = y := htx
    have e2 : t' % p = y := htx'
    have := hinj t (by simp [ht]) t' (by simp [ht']) (by rw [e1, e2])
    subst this
    have k1 := (hA.hRA t ht).2.2.1
    have k2 := (hA.hCA t ht').2.2.1
    omega
  · obtain ⟨t, ht, htx⟩ := Finset.mem_image.1 h1
    have e1 : t % p = y := htx
    obtain ⟨s1, s2, s3, -⟩ := hA.hSQ y h2
    have hyl : y % p = y := Nat.mod_eq_of_lt (by have := hA.hρp; omega)
    have := hinj t (by simp [ht]) y (by simp [h2]) (by rw [e1, hyl])
    have := (hA.hRA t ht).1
    omega
  · obtain ⟨t, ht, htx⟩ := Finset.mem_image.1 h1
    have e1 : t % p = y := htx
    obtain ⟨s1, s2, s3, -⟩ := hA.hSQ y h2
    have hyl : y % p = y := Nat.mod_eq_of_lt (by have := hA.hρp; omega)
    have := hinj t (by simp [ht]) y (by simp [h2]) (by rw [e1, hyl])
    have := (hA.hCA t ht).1
    omega

/-- Pointwise kill counts of the assignment. -/
theorem closedCert_kr_card (PS : PoleSplit p B f e) (a b : ι → ℕ) {G : BlockGeom} {r m ρ : ℕ}
    {T : Finset (G.geometry r).C} (Lz Ez : Bool → ℕ → ℚ) {RA CA SQ : Finset ℕ}
    (hA : Assign r m p ρ T RA CA SQ) (hpm : 2 * m < p) (x : ZMod p) :
    (closedCert PS a b r ρ Lz Ez RA CA SQ x).kr.card =
      (if x.val ∈ RA.image (· % p) then 1 else 0) + (if x.val ∈ SQ then 1 else 0) := by
  obtain ⟨d1, d2, d3⟩ := assign_res_disj hA hpm x.val
  clear hA
  unfold closedCert
  split_ifs <;> simp_all [clsRow, clsCol, bordRow, bordCol, sqCert, trivCert, FibreCert.triv]

theorem closedCert_kc_card (PS : PoleSplit p B f e) (a b : ι → ℕ) {G : BlockGeom} {r m ρ : ℕ}
    {T : Finset (G.geometry r).C} (Lz Ez : Bool → ℕ → ℚ) {RA CA SQ : Finset ℕ}
    (hA : Assign r m p ρ T RA CA SQ) (hpm : 2 * m < p) (x : ZMod p) :
    (closedCert PS a b r ρ Lz Ez RA CA SQ x).kc.card =
      (if x.val ∈ CA.image (· % p) then 1 else 0) + (if x.val ∈ SQ then 1 else 0) := by
  obtain ⟨d1, d2, d3⟩ := assign_res_disj hA hpm x.val
  clear hA
  unfold closedCert
  split_ifs <;> simp_all [clsRow, clsCol, bordRow, bordCol, sqCert, trivCert, FibreCert.triv]

/-- `Σ_x [x.val ∈ A] = |A|` for residues `A ⊆ [0, p)`. -/
theorem sum_val_ind (A : Finset ℕ) (hA : ∀ a ∈ A, a < p) :
    ∑ x : ZMod p, (if x.val ∈ A then 1 else 0) = A.card := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  simp only [Finset.sum_boole, Nat.cast_id]
  refine Finset.card_bij (fun x _ => x.val) ?_ ?_ ?_
  · intro x hx; exact (Finset.mem_filter.1 hx).2
  · intro x1 _ x2 _ h; exact ZMod.val_injective p h
  · intro a ha
    refine ⟨(a : ZMod p), Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩, ?_⟩
    · rw [ZMod.val_natCast, Nat.mod_eq_of_lt (hA a ha)]; exact ha
    · rw [ZMod.val_natCast, Nat.mod_eq_of_lt (hA a ha)]

theorem mem_colFib_of (PS : PoleSplit p B f e) (a b : ι → ℕ) (hd : DigitHyp p B a b)
    (ha : Function.Injective a) (hb : Function.Injective b) (cert : ZMod p → FibreCert)
    (hOk : ∀ x, (cert x).Ok) (hInt : ∀ x, (cert x).Integral p)
    (hReal : ∀ x, Realizes PS a b x (cert x))
    (hcard : (killRows (p := p) a cert).card = (killCols (p := p) b cert).card)
    (x : ZMod p) (d : ℕ) (hdk : d ∈ (cert x).kc) :
    x ∈ colFib PS a b hd ha hb cert hOk hInt hReal hcard := by
  rw [colFib_eq_image]
  obtain ⟨j, hj, hjd⟩ := (hReal x).c_cov d ((hOk x).kc_sub hdk)
  refine Finset.mem_image.2 ⟨j, Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩, hj⟩
  rw [hj, hjd]; exact hdk

theorem mem_rowFib_of (PS : PoleSplit p B f e) (a b : ι → ℕ) (hd : DigitHyp p B a b)
    (ha : Function.Injective a) (hb : Function.Injective b) (cert : ZMod p → FibreCert)
    (hOk : ∀ x, (cert x).Ok) (hInt : ∀ x, (cert x).Integral p)
    (hReal : ∀ x, Realizes PS a b x (cert x))
    (hcard : (killRows (p := p) a cert).card = (killCols (p := p) b cert).card)
    (x : ZMod p) (d : ℕ) (hdk : d ∈ (cert x).kr) :
    x ∈ rowFib PS a b hd ha hb cert hOk hInt hReal hcard := by
  rw [rowFib_eq_image]
  obtain ⟨i, hi, hid⟩ := (hReal x).r_cov d ((hOk x).kr_sub hdk)
  refine Finset.mem_image.2 ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩, hi⟩
  rw [hi, hid]; exact hdk

end Assignment

#print axioms kOf_eq
#print axioms closedCert_kr_card
end CatalanCore.Uniform.Content.RankProducer
