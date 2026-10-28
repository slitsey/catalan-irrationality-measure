module

public import CatalanCore.Uniform.Content.UFWedge.Algebra
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Data.ZMod.Basic

@[expose] public section

/-!
# UF wedge, W3: integer certificates for the cross wedge (lane H9)

A joint type is data over `ℤ` after clearing one common denominator `Dn`: an `m × m` integer matrix
`M` (the fiber block at `X = u₀`, times `Dn`), integer vectors `s, u`, an integer `z`.  `fibZ` is the
bordered determinant computed by structural Laplace expansion (kernel friendly, `detZ_eq`).

If a bordered fiber `F` over `𝔽_p` is realised by `T` (`Dn · F = T` entrywise, up to relabelling) then
`Dn^(m+1) · F.A = fibZ T` and `Dn^(m+1) · F.B = fibZ (T with u = Dn, z = Dn)`, so
`Dn_J^(m_J+1) Dn_K^(m_K+1) · F_J.cross F_K = crossZ`, an integer independent of `p`.  Hence a nonzero
integer `crossZ` forces `F_J.cross F_K ≠ 0` for every prime `p ∤ crossZ` (Lemma-B style: the finitely
many bad primes divide `crossZ`).
-/

open Matrix Finset

namespace CatalanCore.Uniform.Content.UFWedge

/-- Sum of `f 0, …, f (n-1)`, by structural recursion on `ℕ`. -/
def sumN : ℕ → (ℕ → ℤ) → ℤ
  | 0, _ => 0
  | n + 1, f => f n + sumN n f

theorem sumN_eq (n : ℕ) (f : ℕ → ℤ) : sumN n f = ∑ i : Fin n, f i := by
  induction n with
  | zero => simp [sumN]
  | succ n ih => rw [sumN, Fin.sum_univ_castSucc, ih]; simp [add_comm]

/-- The sign `(-1)^j`. -/
def sgn (j : ℕ) : ℤ := if j % 2 = 0 then 1 else -1

theorem sgn_eq (j : ℕ) : sgn j = (-1) ^ j := by
  unfold sgn
  rcases Nat.even_or_odd j with h | h
  · rw [if_pos (Nat.even_iff.1 h), h.neg_one_pow]
  · rw [if_neg (by have := Nat.odd_iff.1 h; omega), h.neg_one_pow]

/-- Determinant by Laplace expansion along the first row, on `ℕ`-indexed entries (structural). -/
def detN : (n : ℕ) → (ℕ → ℕ → ℤ) → ℤ
  | 0, _ => 1
  | n + 1, M => sumN (n + 1) fun j =>
      sgn j * M 0 j * detN n (fun a b => M (a + 1) (if b < j then b else b + 1))

theorem coe_succAbove' {n : ℕ} (j : Fin (n + 1)) (b : Fin n) :
    ((j.succAbove b : Fin (n + 1)) : ℕ) = if (b : ℕ) < (j : ℕ) then (b : ℕ) else (b : ℕ) + 1 := by
  unfold Fin.succAbove
  by_cases h : Fin.castSucc b < j
  · rw [if_pos h, if_pos (by simpa [Fin.lt_def] using h)]; simp
  · rw [if_neg h, if_neg (by simpa [Fin.lt_def] using h)]; simp

theorem detN_eq (n : ℕ) (M : ℕ → ℕ → ℤ) :
    detN n M = (Matrix.of fun a b : Fin n => M a b).det := by
  induction n generalizing M with
  | zero => simp [detN]
  | succ n ih =>
    rw [detN, sumN_eq, Matrix.det_succ_row_zero]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ih, sgn_eq]
    congr 2
    ext a b
    simp [coe_succAbove']

/-- Cofactor `adj(M)_{ij}` from the `(n-1)`-minor deleting row `j` and column `i`. -/
def adjN : (n : ℕ) → (ℕ → ℕ → ℤ) → ℕ → ℕ → ℤ
  | 0, _, _, _ => 1
  | n + 1, M, i, j => sgn (j + i) *
      detN n (fun a b => M (if a < j then a else a + 1) (if b < i then b else b + 1))

theorem adjN_eq (n : ℕ) (M : ℕ → ℕ → ℤ) (i j : Fin n) :
    adjN n M i j = (Matrix.of fun a b : Fin n => M a b).adjugate i j := by
  cases n with
  | zero => exact i.elim0
  | succ n =>
    rw [adjN, Matrix.adjugate_fin_succ_eq_det_submatrix, detN_eq, sgn_eq]
    congr 2
    ext a b
    simp [coe_succAbove']

/-- Integer bordered fiber data (all entries scaled by a common denominator), as lists. -/
structure IntFib (m : ℕ) where
  M : List (List ℤ)
  s : List ℤ
  u : List ℤ
  z : ℤ

namespace IntFib

variable {m : ℕ}

/-- Entry accessors (default `0`). -/
def Mf (T : IntFib m) (i j : ℕ) : ℤ := (T.M.getD i []).getD j 0
def sf (T : IntFib m) (i : ℕ) : ℤ := T.s.getD i 0
def uf (T : IntFib m) (i : ℕ) : ℤ := T.u.getD i 0

/-- The `B`-datum: `u = Dn`, `z = Dn`. -/
def toB (Dn : ℤ) (T : IntFib m) : IntFib m :=
  { T with u := List.replicate m Dn, z := Dn }

theorem uf_toB (Dn : ℤ) (T : IntFib m) (i : ℕ) (hi : i < m) : (T.toB Dn).uf i = Dn := by
  simp [toB, uf, List.getD_eq_getElem?_getD, List.getElem?_replicate, hi]

end IntFib

/-- The bordered determinant `det M z - s adj(M) u` of integer data. -/
def fibZ (m : ℕ) (T : IntFib m) : ℤ :=
  detN m T.Mf * T.z - sumN m fun i => T.sf i * sumN m fun j => adjN m T.Mf i j * T.uf j

theorem fibZ_eq (m : ℕ) (T : IntFib m) :
    fibZ m T = fibA (Matrix.of fun i j : Fin m => T.Mf i j) (fun i : Fin m => T.sf i)
      (fun i : Fin m => T.uf i) T.z := by
  unfold fibZ fibA
  rw [detN_eq, sumN_eq]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sumN_eq]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [adjN_eq]

/-- The integer cross wedge of two certificates. -/
def crossZ (mJ mK : ℕ) (DJ DK : ℤ) (J : IntFib mJ) (K : IntFib mK) : ℤ :=
  fibZ mJ (J.toB DJ) * fibZ mK K - fibZ mJ J * fibZ mK (K.toB DK)


/-- **Shared per-type values.** `A` and `B` of each joint type are evaluated once
(`fibZ mJ J = aJ`, `fibZ mJ (J.toB DJ) = bJ`); a pair certificate is then the single integer
inequality `bJ aK - aJ bK ≠ 0`. -/
theorem crossZ_of_vals {mJ mK : ℕ} {DJ DK : ℤ} {J : IntFib mJ} {K : IntFib mK} {aJ bJ aK bK : ℤ}
    (haJ : fibZ mJ J = aJ) (hbJ : fibZ mJ (J.toB DJ) = bJ) (haK : fibZ mK K = aK)
    (hbK : fibZ mK (K.toB DK) = bK) : crossZ mJ mK DJ DK J K = bJ * aK - aJ * bK := by
  unfold crossZ; rw [haJ, hbJ, haK, hbK]

section Realize

variable {p : ℕ} [Fact p.Prime]

/-- A bordered fiber over `𝔽_p` is realised by integer data `T` with denominator `Dn`. -/
def FibD.Realizes (F : FibD (ZMod p)) (Dn : ℤ) {m : ℕ} (T : IntFib m) : Prop :=
  ∃ e : F.n ≃ Fin m, (∀ i j, (Dn : ZMod p) * F.M i j = (T.Mf (e i) (e j) : ZMod p)) ∧
    (∀ i, (Dn : ZMod p) * F.s i = (T.sf (e i) : ZMod p)) ∧
    (∀ i, (Dn : ZMod p) * F.u i = (T.uf (e i) : ZMod p)) ∧ (Dn : ZMod p) * F.z = (T.z : ZMod p)

theorem fibA_realized {F : FibD (ZMod p)} {Dn : ℤ} {m : ℕ} (T : IntFib m) (e : F.n ≃ Fin m)
    (hM : ∀ i j, (Dn : ZMod p) * F.M i j = (T.Mf (e i) (e j) : ZMod p))
    (hs : ∀ i, (Dn : ZMod p) * F.s i = (T.sf (e i) : ZMod p))
    (u : F.n → ZMod p) (hu : ∀ i, (Dn : ZMod p) * u i = (T.uf (e i) : ZMod p))
    (z : ZMod p) (hz : (Dn : ZMod p) * z = (T.z : ZMod p)) :
    (Dn : ZMod p) ^ (m + 1) * fibA F.M F.s u z = (fibZ m T : ZMod p) := by
  have h1 : (fibZ m T : ZMod p) =
      fibA (((Matrix.of fun i j : Fin m => T.Mf i j).map (Int.castRingHom (ZMod p))))
        (fun i : Fin m => (T.sf i : ZMod p)) (fun i : Fin m => (T.uf i : ZMod p)) (T.z : ZMod p) := by
    rw [fibZ_eq]
    have := map_fibA (Int.castRingHom (ZMod p)) (Matrix.of fun i j : Fin m => T.Mf i j)
      (fun i : Fin m => T.sf i) (fun i : Fin m => T.uf i) T.z
    simpa using this
  rw [h1]
  set M' : Matrix (Fin m) (Fin m) (ZMod p) := Matrix.of fun a b => F.M (e.symm a) (e.symm b) with hM'
  have h2 : fibA M' (fun a => F.s (e.symm a)) (fun a => u (e.symm a)) z = fibA F.M F.s u z :=
    fibA_equiv e F.M M' F.s u _ _ z (by intro i j; simp [M']) (by intro i; simp) (by intro i; simp)
  have h3 := fibA_smul (Dn : ZMod p) M' (fun a => F.s (e.symm a)) (fun a => u (e.symm a)) z
  rw [h2, Fintype.card_fin] at h3
  rw [← h3]
  congr 1
  · ext a b
    have := hM (e.symm a) (e.symm b)
    simpa [M'] using this
  · funext a
    have := hs (e.symm a)
    simpa using this
  · funext a
    have := hu (e.symm a)
    simpa using this

theorem FibD.Realizes.A_eq {F : FibD (ZMod p)} {Dn : ℤ} {m : ℕ} {T : IntFib m}
    (h : F.Realizes Dn T) : (Dn : ZMod p) ^ (m + 1) * F.A = (fibZ m T : ZMod p) := by
  obtain ⟨e, hM, hs, hu, hz⟩ := h
  exact fibA_realized T e hM hs F.u hu F.z hz

theorem FibD.Realizes.B_eq {F : FibD (ZMod p)} {Dn : ℤ} {m : ℕ} {T : IntFib m}
    (h : F.Realizes Dn T) : (Dn : ZMod p) ^ (m + 1) * F.B = (fibZ m (T.toB Dn) : ZMod p) := by
  obtain ⟨e, hM, hs, hu, hz⟩ := h
  exact fibA_realized (T.toB Dn) e hM hs (fun _ => 1)
    (fun i => by rw [IntFib.uf_toB Dn T _ (e i).2]; simp) 1 (by simp [IntFib.toB])

/-- The `p`-independent integer cross wedge controls the cross wedge modulo `p`. -/
theorem cross_realized {FJ FK : FibD (ZMod p)} {DJ DK : ℤ} {mJ mK : ℕ} {J : IntFib mJ}
    {K : IntFib mK} (hJ : FJ.Realizes DJ J) (hK : FK.Realizes DK K) :
    (DJ : ZMod p) ^ (mJ + 1) * (DK : ZMod p) ^ (mK + 1) * FJ.cross FK =
      (crossZ mJ mK DJ DK J K : ZMod p) := by
  unfold crossZ FibD.cross
  push_cast
  rw [← hJ.A_eq, ← hJ.B_eq, ← hK.A_eq, ← hK.B_eq]
  ring

/-- **(W3)** A nonzero integer cross wedge is nonzero modulo every prime not dividing it. -/
theorem cross_ne_of_cert {FJ FK : FibD (ZMod p)} {DJ DK : ℤ} {mJ mK : ℕ} {J : IntFib mJ}
    {K : IntFib mK} (hJ : FJ.Realizes DJ J) (hK : FK.Realizes DK K)
    (h : (crossZ mJ mK DJ DK J K : ZMod p) ≠ 0) : FJ.cross FK ≠ 0 := by
  intro h0
  apply h
  rw [← cross_realized hJ hK, h0, mul_zero]

/-- Bad primes divide the integer cross wedge: a prime exceeding it is good. -/
theorem cast_ne_zero_of_lt {c : ℤ} (hc : c ≠ 0) (hp : c.natAbs < p) : (c : ZMod p) ≠ 0 := by
  intro h
  have h1 := (ZMod.intCast_zmod_eq_zero_iff_dvd c p).1 h
  have h2 : p ∣ c.natAbs := Int.natCast_dvd.1 h1
  have := Nat.le_of_dvd (Int.natAbs_pos.2 hc) h2
  omega

end Realize

end CatalanCore.Uniform.Content.UFWedge
