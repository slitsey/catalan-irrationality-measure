module

public import CatalanCore.Arith.Hybrid.Tropical
public import CatalanCore.Frame.Spec
public import CatalanCore.Arith.Weights
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section

/-!
# The level majorant of the hybrid and the bound `D_hyb · det Full(X) ∈ ℤ[X]` (general instance)

The valuation weight of an entry is **level valued**, with the level function an instance
parameter `lev q a` (normalised by `lev q 0 = 0`):

  `wt lev q A B = 1[lev q A ≠ lev q B] + 1[q ∣ A - B]`   (`A ≠ B`),   `2·1[lev q A > 0]`   (`A = B`),

and the `p`-adic weight of the entry `Mn A B` is `cOf p + ∑_{e ≥ 1} wt lev (p^e) A B`.
The instance proves two valuation statements (`off_val`, `diag_val`) about the sums of `Δ_k` and
`D_k`; everything else here and in `Dual*.lean` is generic.

* λ and the mirror: `lev q a = blk q a`, the number of `q`-singular indices `≤ a` (levels never
  cancel); see `SingLev.lean`.
* P6: the residue level `L(a) mod p` (levels can cancel); the instance supplies its own proof.

`Lemma trop` (`Tropical.lean`) then gives `GLE p (tropExp I r m p) (Fr.fullPoly r m)`; `tropExp`
vanishes for `p ≥ Bnd`, and `Dhyb = ∏_p p^{tropExp}` clears all denominators.
-/

open Finset Polynomial CatalanCore CatalanCore.Basic

namespace CatalanCore.Arith.Hybrid

/-- The one-level weight `w^{(q)}(A, B)` (DW §1; level-valued form). -/
def wt (lev : ℕ → ℕ → ℕ) (q A B : ℕ) : ℕ :=
  if A = B then (if 0 < lev q A then 2 else 0)
  else (if lev q A ≠ lev q B then 1 else 0) + (if (q : ℤ) ∣ (A : ℤ) - B then 1 else 0)

lemma wt_le_two (lev : ℕ → ℕ → ℕ) (q A B : ℕ) : wt lev q A B ≤ 2 := by
  unfold wt; split_ifs <;> omega

lemma wt_comm (lev : ℕ → ℕ → ℕ) (q A B : ℕ) : wt lev q A B = wt lev q B A := by
  unfold wt
  by_cases h : A = B
  · subst h; rfl
  · have h' : ¬ B = A := fun e => h e.symm
    have : ((q : ℤ) ∣ (A : ℤ) - B) ↔ ((q : ℤ) ∣ (B : ℤ) - A) := by
      rw [← dvd_neg]; simp
    simp only [h, h', if_false]
    have e1 : (lev q A ≠ lev q B) ↔ (lev q B ≠ lev q A) := ne_comm
    simp only [e1, this]

/-- Total weight over the levels `e ∈ [1, E]` of the prime `p`. -/
def levels (lev : ℕ → ℕ → ℕ) (p E : ℕ) (A B : ℕ) : ℕ := ∑ e ∈ Icc 1 E, wt lev (p ^ e) A B

/-- **Instance data of the hybrid content argument.**  Built on WP4's `ContentData` (bad primes,
`normN`, `kq`, `kq_le`, `L`), plus the level function `lev` and its valuation facts.  `Ebd` is a
bound for the sizes of the denominators below `N`. -/
structure HybInst (Fr : Frame) where
  cd : CatalanCore.Arith.ContentData Fr
  Ebd : ℕ → ℕ
  lev : ℕ → ℕ → ℕ
  /-- positions whose diagonal entry is used by `Full r m` (`DiagOK`); `diag_val` is only
  required there.  Default: all positions (λ, mirror, `ofSing`). -/
  dok : ℕ → Prop := fun _ => True
  /-- off-diagonal: `1/(b-a) · ∑_{a<k≤b} Δ_k` has valuation `≥ -levels` -/
  off_val : ∀ (p : ℕ) [Fact p.Prime] (E N lo hi : ℕ), Ebd N < p ^ (E + 1) → N < p ^ (E + 1) →
    lo < hi → hi ≤ N →
    (p : ℚ) ^ (levels lev p E lo hi) *
      ((1 / ((hi : ℚ) - lo)) * ∑ k ∈ Ioc lo hi, Fr.Delta k) ∈ LocRing p
  /-- diagonal: `∑_{k≤a} D_k` has valuation `≥ -levels` -/
  diag_val : ∀ (p : ℕ) [Fact p.Prime] (E N a : ℕ), Ebd N < p ^ (E + 1) → a ≤ N → dok a →
    (p : ℚ) ^ (levels lev p E a a) * ∑ k ∈ Icc 1 a, Fr.Dsq k ∈ LocRing p
  /-- levels vanish above `L N` for good primes -/
  lev_large : ∀ (p e N a : ℕ), p.Prime → p ∉ cd.bad → 1 ≤ e → cd.L * N < p ^ e → a ≤ N →
    lev (p ^ e) a = 0
  /-- levels vanish above `Ebd N + N` for every modulus -/
  lev_Ebd : ∀ (q N a : ℕ), Ebd N + N < q → a ≤ N → lev q a = 0

/-- The diagonal positions used by `Full r m` (`c < r`) and by the border (`r + 2 m`) are
covered by `I.dok`.  A class, so that it is threaded automatically through generic sections. -/
class HybInst.DiagOK {Fr : Frame} (I : HybInst Fr) (r m : ℕ) : Prop where
  ok : ∀ c, c < r ∨ c = r + 2 * m → I.dok c

/-- instances with all diagonal positions admissible -/
lemma HybInst.DiagOK.of_all {Fr : Frame} {I : HybInst Fr} (h : ∀ c, I.dok c) (r m : ℕ) :
    I.DiagOK r m := ⟨fun c _ => h c⟩

/-! ### Entry bounds -/

section Entries

open CatalanCore.Arith

variable {Fr : Frame} (I : HybInst Fr) (p : ℕ) [hp : Fact p.Prime] (c : ℕ)

lemma entry_gle {E N : ℕ} (hc : (p : ℚ) ^ c * (1 / (I.cd.normN : ℚ)) ∈ LocRing p)
    (hE1 : I.Ebd N < p ^ (E + 1)) (hE2 : N < p ^ (E + 1)) {A B : ℕ} (hA : A ≤ N)
    (hB : B ≤ N) (hd : A = B → I.dok A) :
    (p : ℚ) ^ (c + levels I.lev p E A B) * Fr.Mn A B ∈ LocRing p := by
  rcases lt_trichotomy A B with h | h | h
  · have hMn : Fr.Mn A B = (1 / (I.cd.normN : ℚ)) *
        ((1 / ((B : ℚ) - A)) * ∑ k ∈ Ioc A B, Fr.Delta k) := by
      unfold Frame.Mn
      rw [if_neg (by omega), I.cd.norm_eq, max_eq_right h.le, min_eq_left h.le]; ring
    have e : (p : ℚ) ^ (c + levels I.lev p E A B) * Fr.Mn A B =
        ((p : ℚ) ^ c * (1 / (I.cd.normN : ℚ))) * ((p : ℚ) ^ (levels I.lev p E A B) *
          ((1 / ((B : ℚ) - A)) * ∑ k ∈ Ioc A B, Fr.Delta k)) := by
      rw [hMn]; ring
    rw [e]
    exact (LocRing p).mul_mem hc (I.off_val p E N A B hE1 hE2 h hB)
  · subst h
    have hMn : Fr.Mn A A = -(1 / (I.cd.normN : ℚ)) * ∑ k ∈ Icc 1 A, Fr.Dsq k := by
      unfold Frame.Mn
      rw [if_pos rfl, I.cd.norm_eq]
    have e : (p : ℚ) ^ (c + levels I.lev p E A A) * Fr.Mn A A =
        -((p : ℚ) ^ c * (1 / (I.cd.normN : ℚ))) * ((p : ℚ) ^ (levels I.lev p E A A) *
          ∑ k ∈ Icc 1 A, Fr.Dsq k) := by
      rw [hMn]; ring
    rw [e]
    exact (LocRing p).mul_mem ((LocRing p).neg_mem hc) (I.diag_val p E N A hE1 hA (hd rfl))
  · have hMn : Fr.Mn A B = Fr.Mn B A := by
      unfold Frame.Mn
      rw [if_neg (by omega), if_neg (by omega), max_comm, min_comm]
    have hMn2 : Fr.Mn B A = (1 / (I.cd.normN : ℚ)) *
        ((1 / ((A : ℚ) - B)) * ∑ k ∈ Ioc B A, Fr.Delta k) := by
      unfold Frame.Mn
      rw [if_neg (by omega), I.cd.norm_eq, max_eq_right h.le, min_eq_left h.le]; ring
    have hl : levels I.lev p E A B = levels I.lev p E B A := by
      unfold levels; exact Finset.sum_congr rfl fun e _ => wt_comm _ _ _ _
    have e : (p : ℚ) ^ (c + levels I.lev p E A B) * Fr.Mn A B =
        ((p : ℚ) ^ c * (1 / (I.cd.normN : ℚ))) * ((p : ℚ) ^ (levels I.lev p E B A) *
          ((1 / ((A : ℚ) - B)) * ∑ k ∈ Ioc B A, Fr.Delta k)) := by
      rw [hMn, hl, hMn2]; ring
    rw [e]
    exact (LocRing p).mul_mem hc (I.off_val p E N B A hE1 hE2 h hA)

end Entries

/-! ### The determinant of `Full(X)` -/

section Full

variable {Fr : Frame} (I : HybInst Fr)

/-- The prime-`p` correction coming from the normalisation `normN`. -/
def cOf (p : ℕ) : ℕ := I.cd.normN.factorization p

lemma cOf_mem (p : ℕ) [hp : Fact p.Prime] :
    (p : ℚ) ^ cOf I p * (1 / (I.cd.normN : ℚ)) ∈ LocRing p := by
  have hn := I.cd.normN_pos
  have := div_mem_locRing (p := p) hn (W := p ^ cOf I p) (dvd_refl _)
  simpa [div_eq_mul_inv] using this

lemma cOf_eq_zero {p : ℕ} (hp : p.Prime) (hb : p ∉ I.cd.bad) : cOf I p = 0 := by
  unfold cOf
  exact Nat.factorization_eq_zero_of_not_dvd (I.cd.not_dvd_normN hp hb)

/-- The number of levels summed over. -/
def Elev (r m : ℕ) : ℕ := I.Ebd (r + 2 * m) + (r + 2 * m)

lemma Elev_lt (p : ℕ) (hp : 2 ≤ p) (r m : ℕ) :
    I.Ebd (r + 2 * m) < p ^ (Elev I r m + 1) ∧ r + 2 * m < p ^ (Elev I r m + 1) := by
  have h1 : Elev I r m + 1 < 2 ^ (Elev I r m + 1) := Nat.lt_two_pow_self
  have h2 : 2 ^ (Elev I r m + 1) ≤ p ^ (Elev I r m + 1) := Nat.pow_le_pow_left hp _
  simp only [Elev] at h1 h2 ⊢
  constructor <;> omega

/-- The weight table of `Full(X)` at the prime `p`. -/
def hybW (r m p : ℕ) (a b : Fin r ⊕ Fin m) : ℕ :=
  cOf I p + levels I.lev p (Elev I r m) (Frame.hybRow r m a) (Frame.hybCol r m b)

/-- The tropical exponent at `p`. -/
noncomputable def tropExp (r m p : ℕ) : ℕ := tropVal (hybW I r m p)

lemma hybRow_le (r m : ℕ) (a : Fin r ⊕ Fin m) : Frame.hybRow r m a ≤ r + 2 * m := by
  rcases a with c | i
  · simp [Frame.hybRow]; have := c.2; omega
  · simp [Frame.hybRow]

lemma hybCol_le (r m : ℕ) (a : Fin r ⊕ Fin m) : Frame.hybCol r m a ≤ r + 2 * m := by
  rcases a with c | i
  · simp [Frame.hybCol]; have := c.2; omega
  · simp [Frame.hybCol]; try (have := i.2; omega)

lemma hybDiag_lt {r m : ℕ} {a b : Fin r ⊕ Fin m} (h : Frame.hybRow r m a = Frame.hybCol r m b) :
    Frame.hybRow r m a < r ∨ Frame.hybRow r m a = r + 2 * m := by
  rcases a with c | i <;> rcases b with c' | j <;> simp [Frame.hybRow, Frame.hybCol] at h ⊢ <;>
    first | exact Or.inl c.2 | omega

/-- Entrywise form of the hybrid bound, also usable on principal restrictions. -/
theorem fullEntry_gle (p : ℕ) [Fact p.Prime] (r m : ℕ) [hd : I.DiagOK r m]
    (a b : Fin r ⊕ Fin m) :
    GLE p (hybW I r m p a b)
      ((match a, b with
        | Sum.inl c, Sum.inl c' => if c = c' then (X : ℚ[X]) else 0
        | _, _ => 0) + C (Fr.Mn (Frame.hybRow r m a) (Frame.hybCol r m b))) := by
  have h1 : GLE p (hybW I r m p a b)
      (C (Fr.Mn (Frame.hybRow r m a) (Frame.hybCol r m b))) := by
    rw [GLE.C_iff]
    exact entry_gle I p _ (cOf_mem I p) (Elev_lt I p (Fact.out : p.Prime).two_le r m).1
      (Elev_lt I p (Fact.out : p.Prime).two_le r m).2 (hybRow_le r m a) (hybCol_le r m b)
      (fun h => hd.ok _ (hybDiag_lt h))
  have hX : GLE p (hybW I r m p a b) (X : ℚ[X]) := GLE.X.mono (Nat.zero_le _)
  rcases a with c | i <;> rcases b with c' | j
  · by_cases h : c = c'
    · simpa [Matrix.of_apply, h] using hX.add h1
    · simpa [Matrix.of_apply, h] using h1
  all_goals simpa [Matrix.of_apply] using h1

/-- **The hybrid tropical bound.**  Every coefficient of `det Full(X)` is `p^{tropExp}`-integral. -/
theorem fullPoly_gle (p : ℕ) [Fact p.Prime] (r m : ℕ) [I.DiagOK r m] :
    GLE p (tropExp I r m p) (Fr.fullPoly r m) := by
  unfold Frame.fullPoly tropExp
  exact det_gle _ _ (fullEntry_gle I p r m)

lemma wt_eq_zero_of_levzero {lev : ℕ → ℕ → ℕ} {q N A B : ℕ} (hbig : N < q)
    (hA : lev q A = 0) (hB : lev q B = 0) (hAN : A ≤ N) (hBN : B ≤ N) : wt lev q A B = 0 := by
  unfold wt
  rw [hA, hB]
  by_cases h : A = B
  · simp [h]
  · rw [if_neg h]
    have hnd : ¬ ((q : ℤ) ∣ (A : ℤ) - B) := by
      intro hd
      have h0 := Int.eq_zero_of_abs_lt_dvd hd (by rw [abs_lt]; constructor <;> omega)
      omega
    simp [hnd]

lemma wt_eq_zero_of_large {p e N A B : ℕ} (hp : p.Prime) (hb : p ∉ I.cd.bad) (he : 1 ≤ e)
    (hbig : I.cd.L * N < p ^ e) (hA : A ≤ N) (hB : B ≤ N) : wt I.lev (p ^ e) A B = 0 := by
  have hL := I.cd.hL
  exact wt_eq_zero_of_levzero (lt_of_le_of_lt (Nat.le_mul_of_pos_left N hL) hbig)
    (I.lev_large p e N A hp hb he hbig hA) (I.lev_large p e N B hp hb he hbig hB) hA hB

lemma wt_eq_zero_of_Ebd {q N A B : ℕ} (hbig : I.Ebd N + N < q) (hA : A ≤ N) (hB : B ≤ N) :
    wt I.lev q A B = 0 :=
  wt_eq_zero_of_levzero (by omega) (I.lev_Ebd q N A hbig hA) (I.lev_Ebd q N B hbig hB) hA hB

/-- The prime range of the common denominator. -/
def Bnd (r m : ℕ) : ℕ := I.cd.L * (r + 2 * m) + 3 + I.cd.bad.sup id

lemma tropExp_eq_zero (r m p : ℕ) (hp : p.Prime) (hbig : Bnd I r m ≤ p) :
    tropExp I r m p = 0 := by
  unfold tropExp
  have hb : p ∉ I.cd.bad := by
    intro h
    have := Finset.le_sup (f := id) h
    unfold Bnd at hbig
    simp at this
    omega
  have hz : hybW I r m p = fun _ _ => 0 := by
    funext a b
    unfold hybW levels
    rw [cOf_eq_zero I hp hb, zero_add]
    refine Finset.sum_eq_zero (fun e he => wt_eq_zero_of_large I hp hb (Finset.mem_Icc.mp he).1
      ?_ (hybRow_le r m a) (hybCol_le r m b))
    have : p ≤ p ^ e := Nat.le_self_pow (by have := (Finset.mem_Icc.mp he).1; omega) p
    unfold Bnd at hbig
    omega
  rw [hz]
  unfold tropVal
  simp

/-- The explicit common denominator: `∏_{p < Bnd} p^{tropExp}`. -/
noncomputable def Dhyb (r m : ℕ) : ℕ :=
  ∏ p ∈ (Finset.range (Bnd I r m)).filter Nat.Prime, p ^ tropExp I r m p

lemma Dhyb_pos (r m : ℕ) : 0 < Dhyb I r m := by
  unfold Dhyb
  exact Finset.prod_pos fun p hp => pow_pos (Nat.Prime.pos (Finset.mem_filter.mp hp).2) _

/-- The tropical denominator clears any polynomial satisfying the same primewise bound. -/
theorem Dhyb_integral_of_gle (r m : ℕ) (f : ℚ[X])
    (hf : ∀ (p : ℕ) [Fact p.Prime], GLE p (tropExp I r m p) f) (i : ℕ) :
    ∃ z : ℤ, (Dhyb I r m : ℚ) * f.coeff i = z := by
  apply int_of_forall_locRing
  intro p hp
  have hgle := hf p i
  by_cases hb : p < Bnd I r m
  · have hmem : p ∈ (Finset.range (Bnd I r m)).filter Nat.Prime :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hb, hp.out⟩
    have hD : (Dhyb I r m : ℚ) = (p : ℚ) ^ tropExp I r m p *
        ((∏ q ∈ ((Finset.range (Bnd I r m)).filter Nat.Prime).erase p,
          q ^ tropExp I r m q : ℕ) : ℚ) := by
      unfold Dhyb
      rw [← Nat.cast_pow, ← Nat.cast_mul,
        Finset.mul_prod_erase _ (fun q => q ^ tropExp I r m q) hmem]
    rw [hD]
    have hR := int_mem_locRing (ℓ := p)
      ((∏ q ∈ ((Finset.range (Bnd I r m)).filter Nat.Prime).erase p,
          q ^ tropExp I r m q : ℕ) : ℤ)
    have := (LocRing p).mul_mem hgle (by simpa using hR)
    convert this using 1; push_cast; ring
  · have h0 := tropExp_eq_zero I r m p hp.out (by omega)
    rw [h0] at hgle
    simp only [pow_zero, one_mul] at hgle
    rw [mul_comm]
    exact (LocRing p).mul_mem hgle (by exact_mod_cast int_mem_locRing (ℓ := p) (Dhyb I r m : ℤ))

/-- **Integrality.**  `Dhyb · det Full(X)` has integer coefficients. -/
theorem Dhyb_integral (r m : ℕ) [I.DiagOK r m] (i : ℕ) :
    ∃ z : ℤ, (Dhyb I r m : ℚ) * (Fr.fullPoly r m).coeff i = z :=
  Dhyb_integral_of_gle I r m _ (fun p => fullPoly_gle I p r m) i

lemma log_Dhyb (r m : ℕ) :
    Real.log (Dhyb I r m) = ∑ p ∈ (Finset.range (Bnd I r m)).filter Nat.Prime,
      (tropExp I r m p : ℝ) * Real.log p := by
  unfold Dhyb
  rw [Nat.cast_prod, Real.log_prod]
  · apply Finset.sum_congr rfl
    intro p _
    rw [Nat.cast_pow, Real.log_pow]
  · intro p hp
    have := (Finset.mem_filter.mp hp).2.pos
    positivity

end Full

end CatalanCore.Arith.Hybrid
