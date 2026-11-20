module

public import CatalanCore.Lai.B83Cross
public import CatalanCore.Lai.B83OwnNode
public import CatalanCore.Lai.B83Half
public import CatalanCore.Content.HalfIntDet

@[expose] public section

/-! # `CatalanCore.Lai.B83BasisBridge`: the plain basis of §3.1 versus the Lean family `elF` (Theorem B83, assembler)

Note `N9-LAI-SMALLPRIME-NV-2026-11-20.md` §3.1.  Band `8n/3 < p < 3n - 1`, `a = p - 2n`, `A₂ = 6n - 2p`,
`K = 3n - 1 - p`.

**Result: no change of basis is needed.**  In the band the window multiplicity is `μ_W = 0`, the window
factor `∏_{r ∈ D} shiftP p 0 r (orthA ..)` of `elF` is `1` (`B83Weighted.elF_band`), and `elF = ExZ.map zphi`
with `ExZ` the integer polynomials used by `lb02_band` and `lb06_band`.  This file identifies them with the
plain basis:

* `ExZ_inl_map`: `ExZ (e_{r,i}) = (X + r)^i Π/(X + r)^{μ_r} = B83.eB A₂ a r i` (the basis of `B83OwnNode`);
* `ExZ_inr_map`: `ExZ (g_j) = X^j Π = X^j · B83Half.PiA a A₂`;
* `toF`, `fEquiv`: the index equivalence `(Fin (A₂+1) × Fin 4 ⊕ Fin (a-1-A₂) × Fin 3) ⊕ Fin K ≃ FIdx n p 5`
  (the index type of `B83Blocks.intBlock` plus the half block);
* `Gm`, `Zm`, `Zm_scaling`, `Zm_BA`: the Gram matrix of `L_n` at an integral point `(a, b, X)` with `p³X`
  integral, in these coordinates, with the exponents `ex, ey, c = 4` of `Content.det_ne_zero_of_block`
  (every entry integral after scaling; the `B × A` block vanishes mod `p`);
* `redQ_Zm`: the reduction of `Zm` is `b̄` times the reduction of the `b`-channel at `(0, 1, 0)`
  (`ZB`), outside the `B × A` block;
* `redAA_eq_intBlock`: under the plain-basis diagonal-entry statements `DiagA`, `DiagC` (the own-node and
  D-node entries `ĉΨ²·h_{i+i'}`), the reduced integral block of `Zm` is `B83.intBlock` with weights
  `b̄·wtB`; the off-residue entries vanish by `lb06_band`;
* `det_gram_ne_zero`: `det G ≠ 0` from `DiagA`, `DiagC` and the nonvanishing of the reduced half block.
-/

set_option autoImplicit false

open Finset Polynomial CatalanCore.Basic CatalanCore.Content CatalanCore.Arith.Hybrid CatalanCore.Lai

namespace CatalanCore.Lai.B83Bridge

noncomputable section

/-- Band parameters: `a = p - 2n`, `A₂ = 6n - 2p`, `8n < 3p`, `p + 1 < 3n`. -/
structure BandPar (n p A2 a : ℕ) : Prop where
  h1 : 8 * n < 3 * p
  h2 : p + 1 < 3 * n
  hA2 : A2 = 6 * n - 2 * p
  ha : a = p - 2 * n

variable {n p A2 a : ℕ}

theorem BandPar.lt (hb : BandPar n p A2 a) : A2 < a := by
  obtain ⟨h1, h2, rfl, rfl⟩ := hb; omega

theorem BandPar.ap (hb : BandPar n p A2 a) : a + 2 * n = p := by
  obtain ⟨h1, h2, rfl, rfl⟩ := hb; omega

theorem BandPar.hAp (hb : BandPar n p A2 a) : A2 + 2 * p = 6 * n := by
  obtain ⟨h1, h2, rfl, rfl⟩ := hb; omega

theorem BandPar.p11 (hb : BandPar n p A2 a) : 11 ≤ p := by
  obtain ⟨h1, h2, rfl, rfl⟩ := hb; omega

theorem BandPar.of_range (h1 : 8 * n < 3 * p) (h2 : p + 1 < 3 * n) : BandPar n p (6 * n - 2 * p) (p - 2 * n) :=
  ⟨h1, h2, rfl, rfl⟩

/-! ### Part 1: residue data -/

variable [hp : Fact p.Prime]

/-- `mF` on `A`: the multiplicity `4`. -/
theorem mF_A (hb : BandPar n p A2 a) {r : ℕ} (hr : r ≤ A2) : mF n p 5 r = 4 := by
  obtain ⟨h1, h2, rfl, rfl⟩ := hb
  have hrp : r < p := by omega
  rcases band_sigmu h1 h2 r hrp with ⟨hg, hm, -⟩ | ⟨hg, hm, hlt, -⟩ | ⟨hg, hm, hge⟩
  · rw [(band_mF h1 h2 r hrp).2 (by omega), hm]
  · omega
  · omega

/-- `mF` on `C`: the multiplicity `3`. -/
theorem mF_C (hb : BandPar n p A2 a) {r : ℕ} (hr1 : A2 < r) (hr2 : r < a) : mF n p 5 r = 3 := by
  obtain ⟨h1, h2, rfl, rfl⟩ := hb
  have hrp : r < p := by omega
  rcases band_sigmu h1 h2 r hrp with ⟨hg, hm, hle⟩ | ⟨hg, hm, hlt, -⟩ | ⟨hg, hm, hge⟩
  · omega
  · rw [(band_mF h1 h2 r hrp).2 (by omega), hm]
  · omega

/-- `mF` on the window `D`: `0`. -/
theorem mF_D (hb : BandPar n p A2 a) {r : ℕ} (hr : r < p) (hge : a ≤ r) : mF n p 5 r = 0 := by
  obtain ⟨h1, h2, rfl, rfl⟩ := hb
  rcases band_sigmu h1 h2 r hr with ⟨hg, hm, hle⟩ | ⟨hg, hm, hlt, hlt2⟩ | ⟨hg, hm, hge'⟩
  · omega
  · omega
  · exact (band_mF h1 h2 r hr).1 hg

theorem mF_lt (hb : BandPar n p A2 a) {r : ℕ} (hr : r < a) : mF n p 5 r = B83.muB A2 r := by
  by_cases hrA : r ≤ A2
  · rw [mF_A hb hrA, B83.muB_le hrA]
  · rw [mF_C hb (by omega) hr, B83.muB_gt hrA]

theorem sig_ne_five (hb : BandPar n p A2 a) {r : ℕ} (hr : r < a) : sig n p r ≠ 5 := by
  obtain ⟨h1, h2, rfl, rfl⟩ := hb
  have hrp : r < p := by omega
  rcases band_sigmu h1 h2 r hrp with ⟨hg, -⟩ | ⟨hg, -⟩ | ⟨hg, hm, hge⟩ <;> omega

theorem sig_eq_five (hb : BandPar n p A2 a) {r : ℕ} (hr : r < p) (hge : a ≤ r) : sig n p r = 5 := by
  obtain ⟨h1, h2, rfl, rfl⟩ := hb
  rcases band_sigmu h1 h2 r hr with ⟨hg, hm, hle⟩ | ⟨hg, hm, hlt, hlt2⟩ | ⟨hg, hm, hge'⟩
  · omega
  · omega
  · exact hg

theorem sig_A (hb : BandPar n p A2 a) {r : ℕ} (hr : r ≤ A2) : sig n p r = 0 := by
  obtain ⟨h1, h2, rfl, rfl⟩ := hb
  have hrp : r < p := by omega
  rcases band_sigmu h1 h2 r hrp with ⟨hg, -⟩ | ⟨hg, hm, hlt, -⟩ | ⟨hg, hm, hge⟩
  · exact hg
  · omega
  · omega

theorem sig_C (hb : BandPar n p A2 a) {r : ℕ} (hr1 : A2 < r) (hr2 : r < a) : sig n p r = 2 := by
  obtain ⟨h1, h2, rfl, rfl⟩ := hb
  have hrp : r < p := by omega
  rcases band_sigmu h1 h2 r hrp with ⟨hg, hm, hle⟩ | ⟨hg, hm, hlt, -⟩ | ⟨hg, hm, hge⟩
  · omega
  · exact hg
  · omega

theorem xtwo_toNat (hb : BandPar n p A2 a) : (xtwo n p).toNat = 3 * n - 1 - p := by
  obtain ⟨h1, h2, rfl, rfl⟩ := hb
  rw [(band_xtwo h1 h2).1]
  omega

/-! ### Part 2: `ExZ` is the plain basis -/

/-- the exponent of `(X + t)` in the element `e_{r₀,i}` of the family. -/
theorem exF_inl (hb : BandPar n p A2 a) (r0 : Fin p) (i : Fin (mF n p 5 r0)) {t : ℕ} (ht : t < p) :
    exF n p 5 (Sum.inl ⟨r0, i⟩) t =
      if t < a then (if (r0 : ℕ) = t then (i : ℕ) else B83.muB A2 t) else 0 := by
  simp only [exF, poleF]
  by_cases hs : t < a
  · rw [if_neg (sig_ne_five hb hs), if_pos hs]
    have hF := mF_lt hb hs
    by_cases hr : (r0 : ℕ) = t
    · rw [if_pos hr, if_pos hr]
      have := i.2
      subst hr
      omega
    · rw [if_neg hr, if_neg hr, hF]; rfl
  · rw [if_pos (sig_eq_five hb ht (by omega)), if_neg hs]

theorem exF_inr (hb : BandPar n p A2 a) (j : Fin (xtwo n p).toNat) {t : ℕ} (ht : t < p) :
    exF n p 5 (Sum.inr j) t = if t < a then B83.muB A2 t else 0 := by
  simp only [exF, poleF]
  by_cases hs : t < a
  · rw [if_neg (sig_ne_five hb hs), if_pos hs, mF_lt hb hs]; rfl
  · rw [if_pos (sig_eq_five hb ht (by omega)), if_neg hs]

theorem ExZ_inl (hb : BandPar n p A2 a) (r0 : Fin p) (i : Fin (mF n p 5 r0)) (hr0 : (r0 : ℕ) < a) :
    ExZ n p 5 (Sum.inl ⟨r0, i⟩) =
      (X + C ((r0 : ℕ) : ℤ)) ^ (i : ℕ) *
        ∏ t ∈ (range a).erase r0, (X + C (t : ℤ)) ^ B83.muB A2 t := by
  have hap : a ≤ p := by have := hb.ap; omega
  unfold ExZ
  simp only [jF, pow_zero, one_mul]
  have hsub : ∏ t ∈ range p, (X + C (t : ℤ)) ^ exF n p 5 (Sum.inl ⟨r0, i⟩) t =
      ∏ t ∈ range a, (X + C (t : ℤ)) ^ exF n p 5 (Sum.inl ⟨r0, i⟩) t := by
    symm
    refine Finset.prod_subset (range_subset_range.2 hap) fun t ht hnt => ?_
    rw [exF_inl hb r0 i (mem_range.1 ht), if_neg (by simpa using hnt)]
    simp
  rw [hsub, ← Finset.mul_prod_erase (range a) _ (mem_range.2 hr0)]
  congr 1
  · rw [exF_inl hb r0 i (by omega), if_pos hr0, if_pos rfl]
  · refine Finset.prod_congr rfl fun t ht => ?_
    have hne : (r0 : ℕ) ≠ t := fun h => (mem_erase.1 ht).1 h.symm
    have htl := mem_range.1 (mem_erase.1 ht).2
    rw [exF_inl hb r0 i (by omega), if_pos htl, if_neg hne]

theorem ExZ_inr (hb : BandPar n p A2 a) (j : Fin (xtwo n p).toNat) :
    ExZ n p 5 (Sum.inr j) = X ^ (j : ℕ) * ∏ t ∈ range a, (X + C (t : ℤ)) ^ B83.muB A2 t := by
  have hap : a ≤ p := by have := hb.ap; omega
  unfold ExZ
  simp only [jF]
  congr 1
  have hsub : ∏ t ∈ range p, (X + C (t : ℤ)) ^ exF n p 5 (Sum.inr j) t =
      ∏ t ∈ range a, (X + C (t : ℤ)) ^ exF n p 5 (Sum.inr j) t := by
    symm
    refine Finset.prod_subset (range_subset_range.2 hap) fun t ht hnt => ?_
    rw [exF_inr hb j (mem_range.1 ht), if_neg (by simpa using hnt)]
    simp
  rw [hsub]
  refine Finset.prod_congr rfl fun t ht => ?_
  rw [exF_inr hb j (by have := mem_range.1 ht; omega), if_pos (mem_range.1 ht)]

theorem mapC (t : ℕ) : (X + C (t : ℤ)).map (Int.castRingHom ℚ) = X + C (t : ℚ) := by
  rw [Polynomial.map_add, Polynomial.map_X, Polynomial.map_C]
  simp

/-- **`e_{r,i} = (X + r)^i Π/(X + r)^{μ_r}`** of the note (§3.1), the basis of `B83OwnNode`. -/
theorem ExZ_inl_map (hb : BandPar n p A2 a) (r0 : Fin p) (i : Fin (mF n p 5 r0)) (hr0 : (r0 : ℕ) < a) :
    (ExZ n p 5 (Sum.inl ⟨r0, i⟩)).map (Int.castRingHom ℚ) = B83.eB A2 a r0 i := by
  rw [ExZ_inl hb r0 i hr0]
  unfold B83.eB B83.PsiPoly
  simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_prod, mapC]

/-- **`g_j = X^j Π`** of the note (§3.1). -/
theorem ExZ_inr_map (hb : BandPar n p A2 a) (j : Fin (xtwo n p).toNat) :
    (ExZ n p 5 (Sum.inr j)).map (Int.castRingHom ℚ) = X ^ (j : ℕ) * B83Half.PiA a A2 := by
  rw [ExZ_inr hb j]
  unfold B83Half.PiA
  simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_prod, mapC, Polynomial.map_X, B83.muB]

/-! ### Part 3: the index equivalence -/

/-- The index type of `B83.intBlock`: `A × Fin 4 ⊕ C × Fin 3`. -/
abbrev IA (A2 a : ℕ) : Type := (Fin (A2 + 1) × Fin 4) ⊕ (Fin (a - 1 - A2) × Fin 3)

/-- The index type of the whole Gram matrix: the integral block and the half block `g_j`, `j < K`. -/
abbrev IX (n p A2 a : ℕ) : Type := IA A2 a ⊕ Fin (xtwo n p).toNat

/-- The family `FIdx n p 5` (E2 basis in the band) in the coordinates of `intBlock` plus the half block. -/
def toF (hb : BandPar n p A2 a) : IX n p A2 a → FIdx n p 5
  | Sum.inl (Sum.inl (r, i)) =>
      Sum.inl ⟨⟨r.1, by have := r.2; have := hb.lt; have := hb.ap; omega⟩,
        ⟨i.1, lt_of_lt_of_eq i.2 (mF_A hb (r := r.1) (by have := r.2; omega)).symm⟩⟩
  | Sum.inl (Sum.inr (r, i)) =>
      Sum.inl ⟨⟨A2 + 1 + r.1, by have := r.2; have := hb.ap; omega⟩,
        ⟨i.1, lt_of_lt_of_eq i.2 (mF_C hb (r := A2 + 1 + r.1) (by omega) (by have := r.2; omega)).symm⟩⟩
  | Sum.inr j => Sum.inr j

/-- Numerical coordinates of an element of `FIdx`: `(r, i)` or `j`. -/
def nu : FIdx n p 5 → (ℕ × ℕ) ⊕ ℕ
  | Sum.inl ⟨r, i⟩ => Sum.inl (r.1, i.1)
  | Sum.inr j => Sum.inr j.1

theorem nu_inj : Function.Injective (nu (n := n) (p := p)) := by
  intro x y h
  rcases x with ⟨⟨r, hr⟩, ⟨i, hi⟩⟩ | ⟨j, hj⟩ <;> rcases y with ⟨⟨r', hr'⟩, ⟨i', hi'⟩⟩ | ⟨j', hj'⟩ <;>
    simp only [nu, reduceCtorEq, Sum.inl.injEq, Sum.inr.injEq, Prod.mk.injEq] at h
  · obtain ⟨rfl, rfl⟩ := h; rfl
  · subst h; rfl

def nu0 : IX n p A2 a → (ℕ × ℕ) ⊕ ℕ
  | Sum.inl (Sum.inl (r, i)) => Sum.inl (r.1, i.1)
  | Sum.inl (Sum.inr (r, i)) => Sum.inl (A2 + 1 + r.1, i.1)
  | Sum.inr j => Sum.inr j.1

theorem nu_toF (hb : BandPar n p A2 a) (x : IX n p A2 a) : nu (toF hb x) = nu0 x := by
  rcases x with (⟨r, i⟩ | ⟨r, i⟩) | j <;> rfl

theorem nu0_inj : Function.Injective (nu0 (n := n) (p := p) (A2 := A2) (a := a)) := by
  intro x y h
  rcases x with (⟨r, i⟩ | ⟨r, i⟩) | j <;> rcases y with (⟨r', i'⟩ | ⟨r', i'⟩) | j' <;>
    simp only [nu0, reduceCtorEq, Sum.inl.injEq, Sum.inr.injEq, Prod.mk.injEq] at h
  · obtain ⟨h1, h2⟩ := h
    have e1 := Fin.ext h1
    have e2 := Fin.ext h2
    subst e1; subst e2; rfl
  · obtain ⟨h1, -⟩ := h
    have := r.2; omega
  · obtain ⟨h1, -⟩ := h
    have := r'.2; omega
  · obtain ⟨h1, h2⟩ := h
    have e1 : r = r' := Fin.ext (by omega)
    have e2 := Fin.ext h2
    subst e1; subst e2; rfl
  · rw [Fin.ext h]

theorem toF_injective (hb : BandPar n p A2 a) : Function.Injective (toF hb) := by
  intro x y h
  apply nu0_inj
  rw [← nu_toF hb x, ← nu_toF hb y, h]

theorem toF_surjective (hb : BandPar n p A2 a) : Function.Surjective (toF hb) := by
  rintro (⟨r, i⟩ | j)
  · have hr := r.2
    have hi := i.2
    have hap := hb.ap
    have hlt := hb.lt
    by_cases hrA : (r : ℕ) ≤ A2
    · have hm := mF_A hb hrA
      refine ⟨Sum.inl (Sum.inl (⟨r.1, by omega⟩, ⟨i.1, by omega⟩)), ?_⟩
      apply nu_inj
      rw [nu_toF]
      rfl
    · by_cases hra : (r : ℕ) < a
      · have hm := mF_C hb (by omega) hra
        refine ⟨Sum.inl (Sum.inr (⟨r.1 - (A2 + 1), by omega⟩, ⟨i.1, by omega⟩)), ?_⟩
        apply nu_inj
        rw [nu_toF]
        simp only [nu0, nu, Sum.inl.injEq, Prod.mk.injEq]
        exact ⟨by omega, trivial⟩
      · exfalso
        have := mF_D hb r.2 (by omega)
        omega
  · exact ⟨Sum.inr j, rfl⟩

/-- **The index equivalence**: `intBlock`'s index set plus the half block `≃` the E2 family. -/
def fEquiv (hb : BandPar n p A2 a) : IX n p A2 a ≃ FIdx n p 5 :=
  Equiv.ofBijective (toF hb) ⟨toF_injective hb, toF_surjective hb⟩

/-! ### Part 4: potentials and the exponents `ex, ey, c = 4` -/

theorem pot2F_A (hb : BandPar n p A2 a) (r : Fin (A2 + 1)) (i : Fin 4) :
    pot2F n p 5 (toF hb (Sum.inl (Sum.inl (r, i)))) = 2 * ((i : ℕ) : ℤ) - 4 := by
  have h0 := sig_A hb (show (r : ℕ) ≤ A2 by have := r.2; omega)
  simp only [toF, pot2F]
  rw [h0]; simp

theorem pot2F_C (hb : BandPar n p A2 a) (r : Fin (a - 1 - A2)) (i : Fin 3) :
    pot2F n p 5 (toF hb (Sum.inl (Sum.inr (r, i)))) = 2 * ((i : ℕ) : ℤ) - 2 := by
  have h0 := sig_C hb (show A2 < A2 + 1 + (r : ℕ) by omega) (show A2 + 1 + (r : ℕ) < a by have := r.2; omega)
  simp only [toF, pot2F]
  rw [h0]; push_cast; ring

theorem pot2F_g (hb : BandPar n p A2 a) (j : Fin (xtwo n p).toNat) :
    pot2F n p 5 (toF hb (Sum.inr j)) = 3 := by
  have := band_lam (p := p) hb.h1 hb.h2
  simp only [toF, pot2F]
  rw [this]; norm_num

/-- the row exponent `ex`: `i` on `A`, `i + 1` on `C`, `3` on `g`. -/
def exo : IX n p A2 a → ℕ
  | Sum.inl (Sum.inl (_, i)) => i.1
  | Sum.inl (Sum.inr (_, i)) => i.1 + 1
  | Sum.inr _ => 3

/-- the column exponent `ey`: `i` on `A`, `i + 1` on `C`, `4` on `g`. -/
def eyo : IX n p A2 a → ℕ
  | Sum.inl (Sum.inl (_, i)) => i.1
  | Sum.inl (Sum.inr (_, i)) => i.1 + 1
  | Sum.inr _ => 4

/-- `thr = ⌈(2π_x + 2π_y)/2⌉` as in `lb02_band`. -/
def thrF (hb : BandPar n p A2 a) (x y : IX n p A2 a) : ℤ :=
  (pot2F n p 5 (toF hb x) + pot2F n p 5 (toF hb y) + 1) / 2

/-- the one extra order of the `B × A` block. -/
def bump : IX n p A2 a → IX n p A2 a → ℤ
  | Sum.inr _, Sum.inl _ => 1
  | _, _ => 0

/-- **The exponents.**  `thr = ex + ey - 4`, plus `1` on the `B × A` block. -/
theorem thr_val (hb : BandPar n p A2 a) (x y : IX n p A2 a) :
    thrF hb x y = (exo x : ℤ) + eyo y - 4 + bump x y := by
  unfold thrF
  rcases x with (⟨r, i⟩ | ⟨r, i⟩) | j <;> rcases y with (⟨r', i'⟩ | ⟨r', i'⟩) | j' <;>
    simp only [pot2F_A hb, pot2F_C hb, pot2F_g hb, exo, eyo, bump] <;> push_cast <;> omega


/-! ### Part 5: the Gram matrix of `L_n` at an integral point, scaled -/

/-- The polynomial `e_x e_y` over `ℚ`. -/
def PF (hb : BandPar n p A2 a) (x y : IX n p A2 a) : ℚ[X] :=
  ((ExZ n p 5 (toF hb x)) * (ExZ n p 5 (toF hb y))).map (Int.castRingHom ℚ)

/-- The Gram matrix `(L_n(e_x e_y))` of the E2 basis at the point `(u, v, w) = (a, b, X)`, in the coordinates
of `B83.intBlock` plus the half block. -/
def Gm (hb : BandPar n p A2 a) (u v w : ℚ) : Matrix (IX n p A2 a) (IX n p A2 a) ℚ :=
  Matrix.of fun x y => MvPolynomial.eval ![u, v, w] (laiL n (PF hb x y))

theorem lb02_ix (hb : BandPar n p A2 a) (x y : IX n p A2 a) :
    (p : ℚ) ^ (-(thrF hb x y + 1)) * entA n (PF hb x y) ∈ LocRing p ∧
      (p : ℚ) ^ (-(thrF hb x y)) * entB n (PF hb x y) ∈ LocRing p ∧
        (p : ℚ) ^ (-(thrF hb x y + 4)) * entX n (PF hb x y) ∈ LocRing p :=
  lb02_band hb.h1 hb.h2 (toF hb x) (toF hb y)

/-- the `b`-channel entry at `(0, 1, 0)`, scaled by `p^{-thr}`: the entry of the reduced matrix `N̄`
(with `b = 1`), independent of the point. -/
def ZB (hb : BandPar n p A2 a) (x y : IX n p A2 a) : LocRing p :=
  ⟨_, (lb02_ix hb x y).2.1⟩

theorem ZB_val (hb : BandPar n p A2 a) (x y : IX n p A2 a) :
    ((ZB hb x y : LocRing p) : ℚ) = (p : ℚ) ^ (-(thrF hb x y)) * entB n (PF hb x y) := rfl

theorem pt_decomp (t : ℤ) (A B C : ℚ) (u v cX : LocRing p) :
    (p : ℚ) ^ (-t) * ((u : ℚ) * A + (v : ℚ) * B + ((cX : ℚ) / (p : ℚ) ^ 3) * C) =
      (v : ℚ) * ((p : ℚ) ^ (-t) * B) +
        (p : ℚ) * ((u : ℚ) * ((p : ℚ) ^ (-(t + 1)) * A) + (cX : ℚ) * ((p : ℚ) ^ (-(t + 4)) * C)) := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have e1 : (p : ℚ) ^ (-(t + 1)) = (p : ℚ) ^ (-t) / p := by
    rw [show -(t + 1) = -t + -1 by ring, zpow_add₀ hp0, zpow_neg_one]
    field_simp
  have e4 : (p : ℚ) ^ (-(t + 4)) = (p : ℚ) ^ (-t) / (p : ℚ) ^ 4 := by
    rw [show -(t + 4) = -t + (-((4 : ℕ) : ℤ)) by push_cast; ring, zpow_add₀ hp0, zpow_neg (p : ℚ) ((4 : ℕ) : ℤ),
      zpow_natCast]
    field_simp
  rw [e1, e4]
  field_simp
  ring

/-- **Point decomposition** (the absorption of Lemma PD, `LB01`): at `(a, b, X)` with `a, b, p³X ∈ ℤ_(p)`,
`p^{-thr}·G_{xy} = b·ZB_{xy} + p·z` with `z ∈ ℤ_(p)`. -/
theorem Gm_decomp (hb : BandPar n p A2 a) (ca cb cX : LocRing p) (x y : IX n p A2 a) :
    ∃ zU : LocRing p,
      (p : ℚ) ^ (-(thrF hb x y)) * Gm hb ca cb ((cX : ℚ) / (p : ℚ) ^ 3) x y =
        (cb : ℚ) * ((ZB hb x y : LocRing p) : ℚ) + (p : ℚ) * (zU : ℚ) := by
  obtain ⟨hA, hB, hC⟩ := lb02_ix hb x y
  refine ⟨⟨(ca : ℚ) * ((p : ℚ) ^ (-(thrF hb x y + 1)) * entA n (PF hb x y)) +
      (cX : ℚ) * ((p : ℚ) ^ (-(thrF hb x y + 4)) * entX n (PF hb x y)),
      (LocRing p).add_mem ((LocRing p).mul_mem ca.2 hA) ((LocRing p).mul_mem cX.2 hC)⟩, ?_⟩
  simp only [Gm, Matrix.of_apply]
  rw [laiL_channels]
  simp only [map_add, map_mul, MvPolynomial.eval_X, MvPolynomial.eval_C, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
  exact pt_decomp _ _ _ _ ca cb cX

theorem zpow_mem_of_le {t e : ℤ} (hte : e ≤ t) {z : ℚ} (hz : (p : ℚ) ^ (-t) * z ∈ LocRing p) :
    (p : ℚ) ^ (-e) * z ∈ LocRing p := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (sub_nonneg.2 hte)
  have : (p : ℚ) ^ (-e) * z = (p : ℚ) ^ k * ((p : ℚ) ^ (-t) * z) := by
    rw [← mul_assoc, ← zpow_natCast, ← zpow_add₀ hp0]
    congr 2
    omega
  rw [this]
  exact (LocRing p).mul_mem ((LocRing p).pow_mem (natCast_mem (LocRing p) p) k) hz

theorem bump_nonneg (x y : IX n p A2 a) : 0 ≤ bump x y := by
  rcases x with _ | _ <;> rcases y with _ | _ <;> simp [bump]

theorem Gm_mem (hb : BandPar n p A2 a) (ca cb cX : LocRing p) (x y : IX n p A2 a) :
    (p : ℚ) ^ (-((exo x : ℤ) + eyo y - 4)) * Gm hb ca cb ((cX : ℚ) / (p : ℚ) ^ 3) x y ∈ LocRing p := by
  obtain ⟨zU, h⟩ := Gm_decomp hb ca cb cX x y
  have hm : (p : ℚ) ^ (-(thrF hb x y)) * Gm hb ca cb ((cX : ℚ) / (p : ℚ) ^ 3) x y ∈ LocRing p := by
    rw [h]
    exact (LocRing p).add_mem ((LocRing p).mul_mem cb.2 (ZB hb x y).2)
      ((LocRing p).mul_mem (natCast_mem (LocRing p) p) zU.2)
  refine zpow_mem_of_le ?_ hm
  have := thr_val hb x y
  have := bump_nonneg (n := n) (p := p) (A2 := A2) (a := a) x y
  omega

/-- The scaled matrix `Z = p^{-(ex + ey - 4)}·G` over `ℤ_(p)` (entries integral by `Gm_mem`). -/
def Zm (hb : BandPar n p A2 a) (ca cb cX : LocRing p) : Matrix (IX n p A2 a) (IX n p A2 a) (LocRing p) :=
  Matrix.of fun x y => ⟨_, Gm_mem hb ca cb cX x y⟩

theorem Zm_val (hb : BandPar n p A2 a) (ca cb cX : LocRing p) (x y : IX n p A2 a) :
    ((Zm hb ca cb cX x y : LocRing p) : ℚ) =
      (p : ℚ) ^ (-((exo x : ℤ) + eyo y - 4)) * Gm hb ca cb ((cX : ℚ) / (p : ℚ) ^ 3) x y := rfl

/-- **The scaling identity of `Content.det_ne_zero_of_block`**, with `c = 4`. -/
theorem Zm_scaling (hb : BandPar n p A2 a) (ca cb cX : LocRing p) (x y : IX n p A2 a) :
    (p : ℚ) ^ 4 * Gm hb ca cb ((cX : ℚ) / (p : ℚ) ^ 3) x y =
      (p : ℚ) ^ (exo x) * ((Zm hb ca cb cX x y : LocRing p) : ℚ) * (p : ℚ) ^ (eyo y) := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  rw [Zm_val, ← zpow_natCast (p : ℚ) (exo x), ← zpow_natCast (p : ℚ) (eyo y)]
  have e : ((exo x : ℕ) : ℤ) + (-((exo x : ℤ) + eyo y - 4)) + ((eyo y : ℕ) : ℤ) = 4 := by ring
  calc (p : ℚ) ^ 4 * Gm hb ca cb ((cX : ℚ) / (p : ℚ) ^ 3) x y
      = (p : ℚ) ^ (((exo x : ℕ) : ℤ) + (-((exo x : ℤ) + eyo y - 4)) + ((eyo y : ℕ) : ℤ)) *
          Gm hb ca cb ((cX : ℚ) / (p : ℚ) ^ 3) x y := by rw [e, zpow_ofNat]
    _ = _ := by rw [zpow_add₀ hp0, zpow_add₀ hp0]; ring

/-- **The `B × A` block of `Z` vanishes mod `p`** (the hypothesis `hBA` of `det_ne_zero_of_block`). -/
theorem Zm_BA (hb : BandPar n p A2 a) (ca cb cX : LocRing p) (j : Fin (xtwo n p).toNat) (y : IA A2 a) :
    redQ p (Zm hb ca cb cX (Sum.inr j) (Sum.inl y)) = 0 := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  obtain ⟨zU, h⟩ := Gm_decomp hb ca cb cX (Sum.inr j) (Sum.inl y)
  have hthr := thr_val hb (Sum.inr j) (Sum.inl y)
  simp only [bump] at hthr
  refine (redQ_eq_zero_iff p _).2 ⟨cb * ZB hb (Sum.inr j) (Sum.inl y) + (p : LocRing p) * zU, Subtype.ext ?_⟩
  have he : -((exo (Sum.inr j : IX n p A2 a) : ℤ) + eyo (Sum.inl y : IX n p A2 a) - 4) =
      1 + (-(thrF hb (Sum.inr j) (Sum.inl y))) := by omega
  rw [Zm_val, he, zpow_add₀ hp0, zpow_one, mul_assoc, h]
  push_cast
  ring

/-- **Reduction of `Z`**: outside the `B × A` block, `redQ Z = b̄ · redQ (ZB)`. -/
theorem redQ_Zm (hb : BandPar n p A2 a) (ca cb cX : LocRing p) (x y : IX n p A2 a) (hxy : bump x y = 0) :
    redQ p (Zm hb ca cb cX x y) = redQ p cb * redQ p (ZB hb x y) := by
  obtain ⟨zU, h⟩ := Gm_decomp hb ca cb cX x y
  have hthr := thr_val hb x y
  rw [hxy] at hthr
  refine NV7.redQ_ofEq _ cb (ZB hb x y) zU ?_
  have he : -((exo x : ℤ) + eyo y - 4) = -(thrF hb x y) := by omega
  rw [Zm_val, he, h]


/-! ### Part 6: the reduced integral block is `B83.intBlock` -/

theorem zpow_split (t : ℤ) : (p : ℚ) ^ (-t) = (p : ℚ) * (p : ℚ) ^ (-(t + 1)) := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  rw [show -t = 1 + -(t + 1) by ring, zpow_add₀ hp0, zpow_one]

/-- the residue `r` of an index of the integral block (`A`: `r`; `C`: `A₂ + 1 + r`). -/
def resid : IA A2 a → ℕ
  | Sum.inl (r, _) => r.1
  | Sum.inr (r, _) => A2 + 1 + r.1

/-- **Cross-residue entries vanish** (`lb06_band`): `ZB_{xy} ≡ 0 (mod p)` for indices of the integral block
at different residues. -/
theorem ZB_cross (hb : BandPar n p A2 a) (x y : IA A2 a) (hne : resid x ≠ resid y) :
    redQ p (ZB hb (Sum.inl x) (Sum.inl y)) = 0 := by
  have ha := hb.ha
  have hlt := hb.lt
  have key : ∀ z : IA A2 a, ∃ (r : Fin p) (i : Fin (mF n p 5 r)),
      toF hb (Sum.inl z) = Sum.inl ⟨r, i⟩ ∧ (r : ℕ) = resid z ∧ resid z < a := by
    rintro (⟨r, i⟩ | ⟨r, i⟩)
    · exact ⟨_, _, rfl, rfl, by simp only [resid]; have := r.2; omega⟩
    · exact ⟨_, _, rfl, rfl, by simp only [resid]; have := r.2; omega⟩
  obtain ⟨r, i, hx, hr, hra⟩ := key x
  obtain ⟨r', i', hy, hr', hra'⟩ := key y
  have h := lb06_band hb.h1 hb.h2 r r' i i' (by omega) (by omega) (by omega)
  refine (redQ_eq_zero_iff p _).2 ⟨⟨_, h⟩, Subtype.ext ?_⟩
  rw [ZB_val]
  simp only [thrF, PF, hx, hy]
  push_cast
  rw [zpow_split, mul_assoc]

/-- the `A` diagonal blocks in the plain basis (Lemma A): the reduction of `p^{-(i+i'-4)}·L_{(0,1,0)}(e_{r,i}e_{r,i'})`
is `ĉ_rΨ_r(-r)²·h_{i+i'}` for `r ∈ A`.  This is the statement closed by the own-node (`B83OwnNode`) and
D-node components. -/
def DiagA (n p A2 a : ℕ) [Fact p.Prime] : Prop :=
  ∀ r : ℕ, r ≤ A2 → ∀ i i' : ℕ, i < 4 → i' < 4 →
    ∃ z : LocRing p, (z : ℚ) = (p : ℚ) ^ (-(((i : ℕ) : ℤ) + i' - 4)) *
        entB n (B83.eB A2 a r i * B83.eB A2 a r i') ∧
      redQ p z = B83.wtB p n A2 a 0 r * B83.hA p (i + i')

/-- the `C` diagonal blocks in the plain basis (Lemma C): `p^{-(i+i'-2)}`-scaled, `ĉ_rΨ_r(-r)²·h^C_{i+i'}`. -/
def DiagC (n p A2 a : ℕ) [Fact p.Prime] : Prop :=
  ∀ r : ℕ, A2 < r → r < a → ∀ i i' : ℕ, i < 3 → i' < 3 →
    ∃ z : LocRing p, (z : ℚ) = (p : ℚ) ^ (-(((i : ℕ) : ℤ) + i' - 2)) *
        entB n (B83.eB A2 a r i * B83.eB A2 a r i') ∧
      redQ p z = B83.wtB p n A2 a 1 r * B83.hC p (i + i')

theorem PF_AA (hb : BandPar n p A2 a) (r : Fin (A2 + 1)) (i i' : Fin 4) :
    PF hb (Sum.inl (Sum.inl (r, i))) (Sum.inl (Sum.inl (r, i'))) =
      B83.eB A2 a r.1 i.1 * B83.eB A2 a r.1 i'.1 := by
  have hr : r.1 < a := by have := r.2; have := hb.lt; omega
  have e1 : (ExZ n p 5 (toF hb (Sum.inl (Sum.inl (r, i))))).map (Int.castRingHom ℚ) =
      B83.eB A2 a r.1 i.1 := ExZ_inl_map hb _ _ hr
  have e2 : (ExZ n p 5 (toF hb (Sum.inl (Sum.inl (r, i'))))).map (Int.castRingHom ℚ) =
      B83.eB A2 a r.1 i'.1 := ExZ_inl_map hb _ _ hr
  unfold PF
  rw [Polynomial.map_mul, e1, e2]

theorem PF_CC (hb : BandPar n p A2 a) (r : Fin (a - 1 - A2)) (i i' : Fin 3) :
    PF hb (Sum.inl (Sum.inr (r, i))) (Sum.inl (Sum.inr (r, i'))) =
      B83.eB A2 a (A2 + 1 + r.1) i.1 * B83.eB A2 a (A2 + 1 + r.1) i'.1 := by
  have hr : A2 + 1 + r.1 < a := by have := r.2; omega
  have e1 : (ExZ n p 5 (toF hb (Sum.inl (Sum.inr (r, i))))).map (Int.castRingHom ℚ) =
      B83.eB A2 a (A2 + 1 + r.1) i.1 := ExZ_inl_map hb _ _ hr
  have e2 : (ExZ n p 5 (toF hb (Sum.inl (Sum.inr (r, i'))))).map (Int.castRingHom ℚ) =
      B83.eB A2 a (A2 + 1 + r.1) i'.1 := ExZ_inl_map hb _ _ hr
  unfold PF
  rw [Polynomial.map_mul, e1, e2]

theorem ZB_AA_val (hb : BandPar n p A2 a) (r : Fin (A2 + 1)) (i i' : Fin 4) :
    ((ZB hb (Sum.inl (Sum.inl (r, i))) (Sum.inl (Sum.inl (r, i'))) : LocRing p) : ℚ) =
      (p : ℚ) ^ (-(((i : ℕ) : ℤ) + i' - 4)) * entB n (B83.eB A2 a r.1 i.1 * B83.eB A2 a r.1 i'.1) := by
  rw [ZB_val, PF_AA hb]
  have := thr_val hb (Sum.inl (Sum.inl (r, i))) (Sum.inl (Sum.inl (r, i')))
  simp only [exo, eyo, bump] at this
  rw [this]
  congr 2
  ring

theorem ZB_CC_val (hb : BandPar n p A2 a) (r : Fin (a - 1 - A2)) (i i' : Fin 3) :
    ((ZB hb (Sum.inl (Sum.inr (r, i))) (Sum.inl (Sum.inr (r, i'))) : LocRing p) : ℚ) =
      (p : ℚ) ^ (-(((i : ℕ) : ℤ) + i' - 2)) *
        entB n (B83.eB A2 a (A2 + 1 + r.1) i.1 * B83.eB A2 a (A2 + 1 + r.1) i'.1) := by
  rw [ZB_val, PF_CC hb]
  have := thr_val hb (Sum.inl (Sum.inr (r, i))) (Sum.inl (Sum.inr (r, i')))
  simp only [exo, eyo, bump] at this
  have e : thrF hb (Sum.inl (Sum.inr (r, i))) (Sum.inl (Sum.inr (r, i'))) =
      ((i.1 : ℕ) : ℤ) + (i'.1 : ℕ) - 2 := by
    rw [this]; push_cast; ring
  rw [e]

theorem redQ_ZB_AA (hb : BandPar n p A2 a) (hdA : DiagA n p A2 a) (r r' : Fin (A2 + 1)) (i i' : Fin 4) :
    redQ p (ZB hb (Sum.inl (Sum.inl (r, i))) (Sum.inl (Sum.inl (r', i')))) =
      if r = r' then B83.wtB p n A2 a 0 r.1 * B83.hA p ((i : ℕ) + i') else 0 := by
  by_cases hrr : r = r'
  · subst hrr
    rw [if_pos rfl]
    obtain ⟨z, hz, hz2⟩ := hdA r.1 (by have := r.2; omega) i.1 i'.1 (by have := i.2; omega)
      (by have := i'.2; omega)
    have : ZB hb (Sum.inl (Sum.inl (r, i))) (Sum.inl (Sum.inl (r, i'))) = z :=
      Subtype.ext (by rw [ZB_AA_val, hz])
    rw [this, hz2]
  · rw [if_neg hrr]
    exact ZB_cross hb _ _ (by
      simp only [resid]
      exact fun h => hrr (Fin.ext h))

theorem redQ_ZB_CC (hb : BandPar n p A2 a) (hdC : DiagC n p A2 a) (r r' : Fin (a - 1 - A2)) (i i' : Fin 3) :
    redQ p (ZB hb (Sum.inl (Sum.inr (r, i))) (Sum.inl (Sum.inr (r', i')))) =
      if r = r' then B83.wtB p n A2 a 1 (A2 + 1 + r.1) * B83.hC p ((i : ℕ) + i') else 0 := by
  by_cases hrr : r = r'
  · subst hrr
    rw [if_pos rfl]
    obtain ⟨z, hz, hz2⟩ := hdC (A2 + 1 + r.1) (by omega) (by have := r.2; omega) i.1 i'.1
      (by have := i.2; omega) (by have := i'.2; omega)
    have : ZB hb (Sum.inl (Sum.inr (r, i))) (Sum.inl (Sum.inr (r, i'))) = z :=
      Subtype.ext (by rw [ZB_CC_val, hz])
    rw [this, hz2]
  · rw [if_neg hrr]
    exact ZB_cross hb _ _ (by
      simp only [resid]
      intro h
      exact hrr (Fin.ext (by omega)))

/-- **The reduced integral block is `intBlock`.**  Given the plain-basis diagonal entries (`DiagA`, `DiagC`),
the reduction mod `p` of the `A ∪ C` block of `Z` at a point with `b̄ ≠ 0` is `B83.intBlock` with the weights
`b̄·ĉ_rΨ_r(-r)²`; every off-residue entry vanishes. -/
theorem redAA_eq_intBlock (hb : BandPar n p A2 a) (hdA : DiagA n p A2 a) (hdC : DiagC n p A2 a)
    (ca cb cX : LocRing p) :
    (Matrix.of fun x x' : IA A2 a => redQ p (Zm hb ca cb cX (Sum.inl x) (Sum.inl x'))) =
      B83.intBlock (ℓ := p) (α := A2 + 1) (γ := a - 1 - A2)
        (fun r => redQ p cb * B83.wtB p n A2 a 0 r.val)
        (fun r => redQ p cb * B83.wtB p n A2 a 1 (A2 + 1 + r.val)) := by
  have hnz : ∀ x x' : IA A2 a, bump (Sum.inl x : IX n p A2 a) (Sum.inl x') = 0 := fun _ _ => rfl
  ext x x'
  simp only [Matrix.of_apply]
  rw [redQ_Zm hb ca cb cX _ _ (hnz x x')]
  rcases x with ⟨r, i⟩ | ⟨r, i⟩ <;> rcases x' with ⟨r', i'⟩ | ⟨r', i'⟩
  · rw [redQ_ZB_AA hb hdA]
    simp only [B83.intBlock, Matrix.fromBlocks_apply₁₁, Matrix.of_apply, B83.MA]
    by_cases hrr : r = r'
    · subst hrr; simp only [if_true]; ring
    · simp [hrr]
  · rw [ZB_cross hb (Sum.inl (r, i)) (Sum.inr (r', i')) (by simp only [resid]; have := r.2; omega)]
    simp [B83.intBlock]
  · rw [ZB_cross hb (Sum.inr (r, i)) (Sum.inl (r', i')) (by simp only [resid]; have := r'.2; omega)]
    simp [B83.intBlock]
  · rw [redQ_ZB_CC hb hdC]
    simp only [B83.intBlock, Matrix.fromBlocks_apply₂₂, Matrix.of_apply, B83.MC]
    by_cases hrr : r = r'
    · subst hrr; simp only [if_true]; ring
    · simp [hrr]

/-! ### Part 7: the determinant -/

theorem det_AA_ne (hb : BandPar n p A2 a) (hdA : DiagA n p A2 a) (hdC : DiagC n p A2 a)
    (ca cb cX : LocRing p) (hcb : redQ p cb ≠ 0) (h13 : p ≠ 13) (h24359 : p ≠ 24359) :
    (Matrix.of fun x x' : IA A2 a => redQ p (Zm hb ca cb cX (Sum.inl x) (Sum.inl x'))).det ≠ 0 := by
  have h5 : 5 ≤ p := by have := hb.p11; omega
  rw [redAA_eq_intBlock hb hdA hdC]
  refine B83.det_intBlock_ne _ _ (fun r => mul_ne_zero hcb ?_) (fun r => mul_ne_zero hcb ?_)
    (by have := hb.p11; omega) h13 h24359
  · exact B83.wtB_ne_zero h5 hb.ap hb.lt (by have := r.2; have := hb.lt; omega)
      (Or.inl ⟨rfl, by have := r.2; omega⟩)
  · exact B83.wtB_ne_zero h5 hb.ap hb.lt (by have := r.2; omega) (Or.inr ⟨rfl, by omega⟩)

/-- **The half block of `Z`**: `p^{-3}·(L_{(0,1,0)}(Π² t^{j+j'}))` reduced; `b̄` times it at a point. -/
theorem ZB_gg_val (hb : BandPar n p A2 a) (j j' : Fin (xtwo n p).toNat) :
    ((ZB hb (Sum.inr j) (Sum.inr j') : LocRing p) : ℚ) =
      (p : ℚ) ^ (-(3 : ℤ)) * entB n (B83Half.PiA a A2 ^ 2 * X ^ ((j : ℕ) + j')) := by
  rw [ZB_val]
  have := thr_val hb (Sum.inr j) (Sum.inr j')
  simp only [exo, eyo, bump] at this
  have e : PF hb (Sum.inr j) (Sum.inr j') = B83Half.PiA a A2 ^ 2 * X ^ ((j : ℕ) + j') := by
    have e1 : (ExZ n p 5 (toF hb (Sum.inr j))).map (Int.castRingHom ℚ) = X ^ (j : ℕ) * B83Half.PiA a A2 :=
      ExZ_inr_map hb j
    have e2 : (ExZ n p 5 (toF hb (Sum.inr j'))).map (Int.castRingHom ℚ) = X ^ (j' : ℕ) * B83Half.PiA a A2 :=
      ExZ_inr_map hb j'
    unfold PF
    rw [Polynomial.map_mul, e1, e2]
    ring
  rw [e, this]
  norm_num

theorem det_half_ne (hb : BandPar n p A2 a) (ca cb cX : LocRing p) (hcb : redQ p cb ≠ 0)
    (hBB : (Matrix.of fun j j' : Fin (xtwo n p).toNat => redQ p (ZB hb (Sum.inr j) (Sum.inr j'))).det ≠ 0) :
    (Matrix.of fun j j' : Fin (xtwo n p).toNat =>
      redQ p (Zm hb ca cb cX (Sum.inr j) (Sum.inr j'))).det ≠ 0 := by
  have hnz : ∀ j j' : Fin (xtwo n p).toNat, bump (Sum.inr j : IX n p A2 a) (Sum.inr j') = 0 := fun _ _ => rfl
  have e : (Matrix.of fun j j' : Fin (xtwo n p).toNat => redQ p (Zm hb ca cb cX (Sum.inr j) (Sum.inr j'))) =
      redQ p cb • (Matrix.of fun j j' : Fin (xtwo n p).toNat => redQ p (ZB hb (Sum.inr j) (Sum.inr j'))) := by
    ext j j'
    simp only [Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
    exact redQ_Zm hb ca cb cX _ _ (hnz j j')
  rw [e, Matrix.det_smul]
  exact mul_ne_zero (pow_ne_zero _ hcb) hBB

/-- **`det G ≠ 0`** for the Gram matrix of `L_n` on the E2 basis (in `intBlock`-plus-half coordinates) at an
integral point `(a, b, X)` (`a, b ∈ ℤ_(p)`, `p³X ∈ ℤ_(p)`, `b` a unit), from the plain-basis diagonal
entries `DiagA`, `DiagC` and the nonvanishing of the reduced half block `hBB`. -/
theorem det_gram_ne_zero (hb : BandPar n p A2 a) (hdA : DiagA n p A2 a) (hdC : DiagC n p A2 a)
    (ca cb cX : LocRing p) (hcb : redQ p cb ≠ 0) (h13 : p ≠ 13) (h24359 : p ≠ 24359)
    (hBB : (Matrix.of fun j j' : Fin (xtwo n p).toNat => redQ p (ZB hb (Sum.inr j) (Sum.inr j'))).det ≠ 0) :
    (Gm hb ca cb ((cX : ℚ) / (p : ℚ) ^ 3)).det ≠ 0 :=
  det_ne_zero_of_block (ℓ := p) (Gm hb ca cb ((cX : ℚ) / (p : ℚ) ^ 3)) (Zm hb ca cb cX) 4 exo eyo
    (Zm_scaling hb ca cb cX) (fun y x => Zm_BA hb ca cb cX y x)
    (det_AA_ne hb hdA hdC ca cb cX hcb h13 h24359) (det_half_ne hb ca cb cX hcb hBB)

/-- The same in the coordinates of the E2 family `FIdx n p 5` (the Gram matrix of the basis `elF`
of `ContentL2Main`, identified with `ExZ` by `B83Weighted.elF_band`). -/
theorem det_gramF_ne_zero (hb : BandPar n p A2 a) (hdA : DiagA n p A2 a) (hdC : DiagC n p A2 a)
    (ca cb cX : LocRing p) (hcb : redQ p cb ≠ 0) (h13 : p ≠ 13) (h24359 : p ≠ 24359)
    (hBB : (Matrix.of fun j j' : Fin (xtwo n p).toNat => redQ p (ZB hb (Sum.inr j) (Sum.inr j'))).det ≠ 0) :
    (Matrix.of fun x y : FIdx n p 5 => MvPolynomial.eval ![(ca : ℚ), (cb : ℚ), (cX : ℚ) / (p : ℚ) ^ 3]
      (laiL n (((ExZ n p 5 x) * (ExZ n p 5 y)).map (Int.castRingHom ℚ)))).det ≠ 0 := by
  have h := det_gram_ne_zero hb hdA hdC ca cb cX hcb h13 h24359 hBB
  have e : Gm hb ca cb ((cX : ℚ) / (p : ℚ) ^ 3) =
      (Matrix.of fun x y : FIdx n p 5 => MvPolynomial.eval ![(ca : ℚ), (cb : ℚ), (cX : ℚ) / (p : ℚ) ^ 3]
        (laiL n (((ExZ n p 5 x) * (ExZ n p 5 y)).map (Int.castRingHom ℚ)))).submatrix (fEquiv hb) (fEquiv hb) :=
    rfl
  rwa [e, Matrix.det_submatrix_equiv_self] at h


/-! ### Part 8: `elF` is the plain basis; node form of the entries; the half block -/

/-- **`elF` is `ExZ`** (hence the plain basis) in the band: the window factor `∏_{r ∈ D} shiftP p 0 r A`
is `1` since `μ_W = 0` (`B83Weighted.elF_band`). -/
theorem elF_eq_plain (hb : BandPar n p A2 a) (L : ℕ) (x : FIdx n p 5) :
    elF n p 5 0 (orthA (cLoc L) 0) x = (ExZ n p 5 x).map zphi :=
  elF_band 5 0 rfl (fun r hr hrs => band_mu hb.h1 hb.h2 r hr hrs) L x

theorem map_zphi_eq (f : ℤ[X]) :
    f.map zphi = (f.map (Int.castRingHom ℚ)).map (MvPolynomial.C : ℚ →+* MPT) := by
  rw [Polynomial.map_map]
  rfl

/-- `elF(e_{r,i}) = (X + r)^i Π/(X + r)^{μ_r}` (the basis of `B83OwnNode`), for `r ∈ A ∪ C`. -/
theorem elF_inl_plain (hb : BandPar n p A2 a) (L : ℕ) (r0 : Fin p) (i : Fin (mF n p 5 r0))
    (hr0 : (r0 : ℕ) < a) :
    elF n p 5 0 (orthA (cLoc L) 0) (Sum.inl ⟨r0, i⟩) =
      (B83.eB A2 a r0 i).map (MvPolynomial.C : ℚ →+* MPT) := by
  rw [elF_eq_plain hb L, map_zphi_eq, ExZ_inl_map hb r0 i hr0]

/-- `elF(g_j) = X^j Π`. -/
theorem elF_inr_plain (hb : BandPar n p A2 a) (L : ℕ) (j : Fin (xtwo n p).toNat) :
    elF n p 5 0 (orthA (cLoc L) 0) (Sum.inr j) =
      (X ^ (j : ℕ) * B83Half.PiA a A2).map (MvPolynomial.C : ℚ →+* MPT) := by
  rw [elF_eq_plain hb L, map_zphi_eq, ExZ_inr_map hb j]

/-- The entries of `L_n` at `(a, b, X' / p³)` as node sums, in the form of `B83OwnNode`
(`ownU`, `ownE`). -/
theorem eval_laiL_own (ca cb cX : LocRing p) (F : ℚ[X]) :
    MvPolynomial.eval ![(ca : ℚ), (cb : ℚ), (cX : ℚ) / (p : ℚ) ^ 3] (laiL n F) =
      ∑ k ∈ range (6 * n + 1), (laiCoef n k : ℚ) *
        (B83.ownU ca cb k * F.derivative.eval (-(k : ℚ)) + B83.ownE n ca cb cX k * F.eval (-(k : ℚ))) := by
  unfold laiL laiU laiV B83.ownU B83.ownE
  simp only [map_sum, map_mul, map_add, map_sub, MvPolynomial.eval_X, MvPolynomial.eval_C,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-- the `b`-channel `entB` is the node sum at the point `(0, 1, 0)`. -/
theorem entB_eq_own (F : ℚ[X]) :
    entB n F = ∑ k ∈ range (6 * n + 1), (laiCoef n k : ℚ) *
      (B83.ownU (0 : LocRing p) 1 k * F.derivative.eval (-(k : ℚ)) +
        B83.ownE n (0 : LocRing p) 1 0 k * F.eval (-(k : ℚ))) := by
  unfold entB B83.ownU B83.ownE
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Subring.coe_zero, Subring.coe_one, zero_div]
  ring

/-- **The half block, from its entries.**  If `z j j' ∈ ℤ_(p)` are the scaled `b`-entries
`p^{-3}·L_{(0,1,0)}(Π² t^{j+j'})` of the `g`-block (`ZB_gg_val`) and their reduction has nonzero
determinant, then `hBB` of `det_gram_ne_zero` holds. -/
theorem hBB_of (hb : BandPar n p A2 a) (z : Fin (xtwo n p).toNat → Fin (xtwo n p).toNat → LocRing p)
    (hz : ∀ j j', (z j j' : ℚ) = (p : ℚ) ^ (-(3 : ℤ)) * entB n (B83Half.PiA a A2 ^ 2 * X ^ ((j : ℕ) + j')))
    (hdet : (Matrix.of fun j j' => redQ p (z j j')).det ≠ 0) :
    (Matrix.of fun j j' : Fin (xtwo n p).toNat => redQ p (ZB hb (Sum.inr j) (Sum.inr j'))).det ≠ 0 := by
  have e : (Matrix.of fun j j' : Fin (xtwo n p).toNat => redQ p (ZB hb (Sum.inr j) (Sum.inr j'))) =
      Matrix.of fun j j' => redQ p (z j j') := by
    ext j j'
    simp only [Matrix.of_apply]
    congr 1
    exact Subtype.ext (by rw [ZB_gg_val, hz])
  rwa [e]


/-- Regression instance: `(n, p) = (30, 83)` is a band pair, `A₂ = 14`, `a = 23`, `K = 6`. -/
theorem bandPar_30_83 : BandPar 30 83 14 23 := ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩

end

end CatalanCore.Lai.B83Bridge

#print axioms CatalanCore.Lai.B83Bridge.BandPar.of_range
#print axioms CatalanCore.Lai.B83Bridge.ExZ_inl_map
#print axioms CatalanCore.Lai.B83Bridge.ExZ_inr_map
#print axioms CatalanCore.Lai.B83Bridge.toF_injective
#print axioms CatalanCore.Lai.B83Bridge.toF_surjective
#print axioms CatalanCore.Lai.B83Bridge.fEquiv
#print axioms CatalanCore.Lai.B83Bridge.thr_val
#print axioms CatalanCore.Lai.B83Bridge.Gm_decomp
#print axioms CatalanCore.Lai.B83Bridge.Gm_mem
#print axioms CatalanCore.Lai.B83Bridge.Zm_scaling
#print axioms CatalanCore.Lai.B83Bridge.Zm_BA
#print axioms CatalanCore.Lai.B83Bridge.redQ_Zm
#print axioms CatalanCore.Lai.B83Bridge.ZB_cross
#print axioms CatalanCore.Lai.B83Bridge.redQ_ZB_AA
#print axioms CatalanCore.Lai.B83Bridge.redQ_ZB_CC
#print axioms CatalanCore.Lai.B83Bridge.redAA_eq_intBlock
#print axioms CatalanCore.Lai.B83Bridge.det_AA_ne
#print axioms CatalanCore.Lai.B83Bridge.ZB_gg_val
#print axioms CatalanCore.Lai.B83Bridge.det_half_ne
#print axioms CatalanCore.Lai.B83Bridge.det_gram_ne_zero
#print axioms CatalanCore.Lai.B83Bridge.det_gramF_ne_zero
#print axioms CatalanCore.Lai.B83Bridge.elF_eq_plain
#print axioms CatalanCore.Lai.B83Bridge.elF_inl_plain
#print axioms CatalanCore.Lai.B83Bridge.elF_inr_plain
#print axioms CatalanCore.Lai.B83Bridge.eval_laiL_own
#print axioms CatalanCore.Lai.B83Bridge.entB_eq_own
#print axioms CatalanCore.Lai.B83Bridge.hBB_of
#print axioms CatalanCore.Lai.B83Bridge.bandPar_30_83
