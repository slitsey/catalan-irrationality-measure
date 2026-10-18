import CatalanLambda.Cert.LogBounds
import CatalanLambda.Cert.ArctanBounds
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Reduction of "`g ≥ m′` on a ray box" to a computation over `ℤ`/`ℚ`

Real statement: for `σ = ∑ (n_k/2^32) δ_{(X_k,Y_k)/2^40}`, `ρ = 1/1024`,
`g(x,y) = U_ρ^σ(x,y) − U^τ(x,y) + (999/1000) π y` with `U^τ` the closed form on `Re z < 0`:
`U^τ = 1 − x·log|z| − (1−x)·log|1−z| − y·arctan (y/(x²+y²−x))`.

Box `[xlo,xhi]×[ylo,yhi]` has integer corners in units of `2^-40`.
`box_sound`: if the rational number `boxLB` computed from scaled-integer log/arctan bounds is
`≥ m′`, then `g ≥ m′` at every point of the box.
-/

open Real

namespace CatalanLambda.Cert

abbrev Pt := ℤ × ℤ × ℕ

def qplusN (xlo xhi ylo yhi : ℤ) (p : Pt) : ℕ :=
  (max (xlo - p.1).natAbs (xhi - p.1).natAbs) ^ 2 +
    (max (ylo - p.2.1).natAbs (yhi - p.2.1).natAbs) ^ 2 + 2 ^ 60

def sigSum (xlo xhi ylo yhi : ℤ) : List Pt → ℤ
  | [] => 0
  | p :: ps => (p.2.2 : ℤ) * logUpS (qplusN xlo xhi ylo yhi p) + sigSum xlo xhi ylo yhi ps

noncomputable def Usig : List Pt → ℝ → ℝ → ℝ
  | [], _, _ => 0
  | p :: ps, x, y =>
    (p.2.2 : ℝ) / 2 ^ 32 *
        (-(1 / 2) * Real.log ((x - (p.1 : ℝ) / 2 ^ 40) ^ 2 + (y - (p.2.1 : ℝ) / 2 ^ 40) ^ 2 +
          (1 / 1024) ^ 2)) + Usig ps x y

noncomputable def Utau (x y : ℝ) : ℝ :=
  1 - x * (Real.log (x ^ 2 + y ^ 2) / 2) - (1 - x) * (Real.log ((1 - x) ^ 2 + y ^ 2) / 2)
    - y * Real.arctan (y / (x ^ 2 + y ^ 2 - x))

noncomputable def gfun (pts : List Pt) (x y : ℝ) : ℝ :=
  Usig pts x y - Utau x y + (999 / 1000) * Real.pi * y

/-! ### the sigma part -/

lemma dmax_sq (lo hi X : ℤ) (t : ℝ) (h1 : (lo : ℝ) / 2 ^ 40 ≤ t) (h2 : t ≤ (hi : ℝ) / 2 ^ 40) :
    (t - (X : ℝ) / 2 ^ 40) ^ 2 ≤
      ((max (lo - X).natAbs (hi - X).natAbs : ℕ) : ℝ) ^ 2 / 2 ^ 80 := by
  set M : ℝ := ((max (lo - X).natAbs (hi - X).natAbs : ℕ) : ℝ) with hM
  have ha : |((lo - X : ℤ) : ℝ)| ≤ M := by
    have := le_max_left (lo - X).natAbs (hi - X).natAbs
    have h : (((lo - X).natAbs : ℕ) : ℝ) ≤ M := by rw [hM]; exact Nat.cast_le.mpr this
    rwa [Nat.cast_natAbs, Int.cast_abs] at h
  have hb : |((hi - X : ℤ) : ℝ)| ≤ M := by
    have := le_max_right (lo - X).natAbs (hi - X).natAbs
    have h : (((hi - X).natAbs : ℕ) : ℝ) ≤ M := by rw [hM]; exact Nat.cast_le.mpr this
    rwa [Nat.cast_natAbs, Int.cast_abs] at h
  push_cast at ha hb
  rw [abs_le] at ha hb
  have e : (t - (X : ℝ) / 2 ^ 40) = (2 ^ 40 * t - X) / 2 ^ 40 := by field_simp
  have h3 : -M ≤ 2 ^ 40 * t - X := by
    have : (lo : ℝ) ≤ 2 ^ 40 * t := by
      have := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 2 ^ 40)
      calc (lo : ℝ) = 2 ^ 40 * ((lo : ℝ) / 2 ^ 40) := by field_simp
        _ ≤ _ := this
    linarith [ha.1]
  have h4 : 2 ^ 40 * t - X ≤ M := by
    have : 2 ^ 40 * t ≤ (hi : ℝ) := by
      have := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 2 ^ 40)
      calc 2 ^ 40 * t ≤ 2 ^ 40 * ((hi : ℝ) / 2 ^ 40) := this
        _ = hi := by field_simp
    linarith [hb.2]
  rw [e, div_pow]
  have : (2 ^ 40 * t - X) ^ 2 ≤ M ^ 2 := by nlinarith
  calc (2 ^ 40 * t - X) ^ 2 / (2 ^ 40) ^ 2 ≤ M ^ 2 / (2 ^ 40) ^ 2 := by gcongr
    _ = M ^ 2 / 2 ^ 80 := by norm_num

lemma Usig_ge (xlo xhi ylo yhi : ℤ) (x y : ℝ)
    (hx1 : (xlo : ℝ) / 2 ^ 40 ≤ x) (hx2 : x ≤ (xhi : ℝ) / 2 ^ 40)
    (hy1 : (ylo : ℝ) / 2 ^ 40 ≤ y) (hy2 : y ≤ (yhi : ℝ) / 2 ^ 40) :
    ∀ pts : List Pt, -((sigSum xlo xhi ylo yhi pts : ℤ) : ℝ) / 2 ^ 97 ≤ Usig pts x y := by
  intro pts
  induction pts with
  | nil => simp [sigSum, Usig]
  | cons p ps ih =>
    simp only [sigSum, Usig]
    have hq := dmax_sq xlo xhi p.1 x hx1 hx2
    have hq2 := dmax_sq ylo yhi p.2.1 y hy1 hy2
    set q : ℝ := (x - (p.1 : ℝ) / 2 ^ 40) ^ 2 + (y - (p.2.1 : ℝ) / 2 ^ 40) ^ 2 + (1 / 1024) ^ 2
      with hq_def
    have hqpos : 0 < q := by positivity
    have hN : 0 < qplusN xlo xhi ylo yhi p := by
      unfold qplusN; positivity
    have hqle : q ≤ ((qplusN xlo xhi ylo yhi p : ℕ) : ℝ) / 2 ^ 80 := by
      have e : ((qplusN xlo xhi ylo yhi p : ℕ) : ℝ) / 2 ^ 80 =
          ((max (xlo - p.1).natAbs (xhi - p.1).natAbs : ℕ) : ℝ) ^ 2 / 2 ^ 80 +
          ((max (ylo - p.2.1).natAbs (yhi - p.2.1).natAbs : ℕ) : ℝ) ^ 2 / 2 ^ 80 +
          2 ^ 60 / 2 ^ 80 := by
        simp only [qplusN, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat]; ring
      have : ((1 : ℝ) / 1024) ^ 2 = 2 ^ 60 / 2 ^ 80 := by norm_num
      rw [e, hq_def, this]
      linarith
    have hlog : Real.log q ≤ (logUpS (qplusN xlo xhi ylo yhi p) : ℝ) / 2 ^ 64 :=
      (Real.log_le_log hqpos hqle).trans (logUpS_spec hN)
    push_cast
    have hn : (0 : ℝ) ≤ (p.2.2 : ℝ) / 2 ^ 32 := by positivity
    have h1 : (p.2.2 : ℝ) / 2 ^ 32 * (-(1 / 2) * ((logUpS (qplusN xlo xhi ylo yhi p) : ℝ) / 2 ^ 64))
        ≤ (p.2.2 : ℝ) / 2 ^ 32 * (-(1 / 2) * Real.log q) := by
      apply mul_le_mul_of_nonneg_left _ hn
      linarith
    have e2 : -((p.2.2 : ℝ) * (logUpS (qplusN xlo xhi ylo yhi p) : ℝ) +
        ((sigSum xlo xhi ylo yhi ps : ℤ) : ℝ)) / 2 ^ 97 =
        (p.2.2 : ℝ) / 2 ^ 32 * (-(1 / 2) * ((logUpS (qplusN xlo xhi ylo yhi p) : ℝ) / 2 ^ 64)) +
        (-((sigSum xlo xhi ylo yhi ps : ℤ) : ℝ) / 2 ^ 97) := by ring
    rw [e2]
    linarith

/-! ### rational computation -/

/-- kernel-friendly `max`/`min` on `ℚ` (the `LinearOrder` ones go through classical decidability). -/
def qmax (a b : ℚ) : ℚ := if a ≤ b then b else a
def qmin (a b : ℚ) : ℚ := if a ≤ b then a else b

@[simp, norm_cast] lemma qmax_cast (a b : ℚ) : ((qmax a b : ℚ) : ℝ) = max (a : ℝ) (b : ℝ) := by
  unfold qmax
  split_ifs with h
  · exact (max_eq_right (by exact_mod_cast h)).symm
  · exact (max_eq_left (by exact_mod_cast (not_le.mp h).le)).symm

@[simp, norm_cast] lemma qmin_cast (a b : ℚ) : ((qmin a b : ℚ) : ℝ) = min (a : ℝ) (b : ℝ) := by
  unfold qmin
  split_ifs with h
  · exact (min_eq_left (by exact_mod_cast h)).symm
  · exact (min_eq_right (by exact_mod_cast (not_le.mp h).le)).symm

def PILO : ℚ := 314159265358979323846 / 10 ^ 20

lemma PILO_lt : (PILO : ℝ) < Real.pi := by
  have := Real.pi_gt_d20
  have e : (PILO : ℝ) = 3.14159265358979323846 := by
    unfold PILO; push_cast; norm_num
  rw [e]; exact this

def L1Q (xlo yhi : ℤ) : ℚ := (logUpS (xlo * xlo + yhi * yhi).toNat : ℚ) / 2 ^ 64
def lQ (xhi ylo : ℤ) : ℚ := (logLoS ((2 ^ 40 - xhi) ^ 2 + ylo ^ 2).toNat : ℚ) / 2 ^ 64
def vloQ (xlo ylo yhi : ℤ) : ℚ := (ylo : ℚ) * 2 ^ 40 / ((xlo : ℚ) * xlo + yhi * yhi - xlo * 2 ^ 40)

def boxLBg (Ls : ℚ) (xlo xhi ylo yhi : ℤ) : ℚ :=
  let L1 := L1Q xlo yhi
  let Aup : ℚ := (1 / 2) * qmax ((-(xhi : ℚ) / 2 ^ 40) * L1) ((-(xlo : ℚ) / 2 ^ 40) * L1)
  let l := lQ xhi ylo
  let Bup : ℚ := -(1 / 2) * qmin ((((2 : ℚ) ^ 40 - xhi) / 2 ^ 40) * l)
    ((((2 : ℚ) ^ 40 - xlo) / 2 ^ 40) * l)
  let th := thetaQ (vloQ xlo ylo yhi)
  let Cup : ℚ := -qmin ((ylo : ℚ) / 2 ^ 40 * th) ((yhi : ℚ) / 2 ^ 40 * th)
  Ls - (1 + Aup + Bup + Cup) + (999 / 1000) * PILO * ((ylo : ℚ) / 2 ^ 40)

def boxLB (pts : List Pt) (xlo xhi ylo yhi : ℤ) : ℚ :=
  boxLBg (-(sigSum xlo xhi ylo yhi pts : ℚ) / 2 ^ 97) xlo xhi ylo yhi

def boxOK (pts : List Pt) (mp : ℚ) (b : ℤ × ℤ × ℤ × ℤ) : Bool :=
  decide (mp ≤ boxLB pts b.1 b.2.1 b.2.2.1 b.2.2.2)

/-- main reduction lemma, with an abstract lower bound `Ls` for the sigma part -/
theorem box_sound_g (pts : List Pt) (Ls mp : ℚ) (xlo xhi ylo yhi : ℤ)
    (hxhi : xhi < 0) (hxlohi : xlo ≤ xhi) (hylo : 0 ≤ ylo)
    (hchk : mp ≤ boxLBg Ls xlo xhi ylo yhi)
    (x y : ℝ)
    (hx1 : (xlo : ℝ) / 2 ^ 40 ≤ x) (hx2 : x ≤ (xhi : ℝ) / 2 ^ 40)
    (hy1 : (ylo : ℝ) / 2 ^ 40 ≤ y) (hy2 : y ≤ (yhi : ℝ) / 2 ^ 40)
    (hS : (Ls : ℝ) ≤ Usig pts x y) :
    (mp : ℝ) ≤ gfun pts x y := by
  have hchk' : (mp : ℝ) ≤ ((boxLBg Ls xlo xhi ylo yhi : ℚ) : ℝ) := by exact_mod_cast hchk
  have hxhiR : (xhi : ℝ) ≤ -1 := by exact_mod_cast (by omega : xhi ≤ -1)
  have hxloR : (xlo : ℝ) ≤ -1 := by
    have : xlo ≤ -1 := by omega
    exact_mod_cast this
  have hyloR : (0 : ℝ) ≤ ylo := by exact_mod_cast hylo
  have hxneg : x < 0 := by
    have : x ≤ (xhi : ℝ) / 2 ^ 40 := hx2
    have h2 : (xhi : ℝ) / 2 ^ 40 < 0 := by
      apply div_neg_of_neg_of_pos <;> [linarith; positivity]
    linarith
  have hy0 : 0 ≤ y := by
    have : (0 : ℝ) ≤ (ylo : ℝ) / 2 ^ 40 := by positivity
    linarith
  have hp40 : (0 : ℝ) < 2 ^ 40 := by positivity
  -- (A)
  have hA : -x * (Real.log (x ^ 2 + y ^ 2) / 2) ≤
      (((1 / 2) * qmax ((-(xhi : ℚ) / 2 ^ 40) * L1Q xlo yhi)
        ((-(xlo : ℚ) / 2 ^ 40) * L1Q xlo yhi) : ℚ) : ℝ) := by
    have hN1 : 0 < (xlo * xlo + yhi * yhi).toNat := by
      have : 0 < xlo * xlo + yhi * yhi := by nlinarith
      omega
    have hN1c : (((xlo * xlo + yhi * yhi).toNat : ℕ) : ℝ) = (xlo : ℝ) * xlo + (yhi : ℝ) * yhi := by
      have : 0 ≤ xlo * xlo + yhi * yhi := by nlinarith
      have h := Int.toNat_of_nonneg this
      have h2 : (((xlo * xlo + yhi * yhi).toNat : ℕ) : ℤ) = xlo * xlo + yhi * yhi := h
      exact_mod_cast h2
    have hxsq : x ^ 2 ≤ ((xlo : ℝ) / 2 ^ 40) ^ 2 := by nlinarith
    have hysq : y ^ 2 ≤ ((yhi : ℝ) / 2 ^ 40) ^ 2 := by nlinarith
    have hpos : 0 < x ^ 2 + y ^ 2 := by nlinarith
    have hle : x ^ 2 + y ^ 2 ≤ (((xlo * xlo + yhi * yhi).toNat : ℕ) : ℝ) / 2 ^ 80 := by
      rw [hN1c]
      have : ((xlo : ℝ) / 2 ^ 40) ^ 2 + ((yhi : ℝ) / 2 ^ 40) ^ 2 =
          ((xlo : ℝ) * xlo + (yhi : ℝ) * yhi) / 2 ^ 80 := by ring
      linarith
    have hlog : Real.log (x ^ 2 + y ^ 2) ≤ (L1Q xlo yhi : ℝ) := by
      have := (Real.log_le_log hpos hle).trans (logUpS_spec hN1)
      unfold L1Q; push_cast; exact this
    set L1 : ℝ := (L1Q xlo yhi : ℝ) with hL1
    push_cast
    set a := -x with ha
    have ha0 : 0 ≤ a := by linarith
    have ha1 : -(xhi : ℝ) / 2 ^ 40 ≤ a := by
      rw [ha]; have : x ≤ (xhi : ℝ) / 2 ^ 40 := hx2; linarith [neg_div (2 ^ 40 : ℝ) (xhi : ℝ)]
    have ha2 : a ≤ -(xlo : ℝ) / 2 ^ 40 := by
      rw [ha]; have : (xlo : ℝ) / 2 ^ 40 ≤ x := hx1; linarith [neg_div (2 ^ 40 : ℝ) (xlo : ℝ)]
    have h1 : a * Real.log (x ^ 2 + y ^ 2) ≤ a * L1 := mul_le_mul_of_nonneg_left hlog ha0
    have h2 : a * L1 ≤ max ((-(xhi : ℝ) / 2 ^ 40) * L1) ((-(xlo : ℝ) / 2 ^ 40) * L1) := by
      rcases le_total 0 L1 with h | h
      · exact le_max_of_le_right (mul_le_mul_of_nonneg_right ha2 h)
      · exact le_max_of_le_left (mul_le_mul_of_nonpos_right ha1 h)
    have e : -x * (Real.log (x ^ 2 + y ^ 2) / 2) = a * Real.log (x ^ 2 + y ^ 2) / 2 := by
      rw [ha]; ring
    rw [e]
    linarith
  -- (B)
  have hB : -(1 / 2 : ℝ) * min (((2 ^ 40 - (xhi : ℝ)) / 2 ^ 40) * (lQ xhi ylo : ℝ))
        (((2 ^ 40 - (xlo : ℝ)) / 2 ^ 40) * (lQ xhi ylo : ℝ)) ≥
      -((1 - x) * (Real.log ((1 - x) ^ 2 + y ^ 2) / 2)) := by
    have hN2pos : 0 < (2 ^ 40 - xhi) ^ 2 + ylo ^ 2 := by nlinarith
    have hN2 : 0 < ((2 ^ 40 - xhi) ^ 2 + ylo ^ 2).toNat := by omega
    have hN2c : ((((2 ^ 40 - xhi) ^ 2 + ylo ^ 2).toNat : ℕ) : ℝ) =
        (2 ^ 40 - (xhi : ℝ)) ^ 2 + (ylo : ℝ) ^ 2 := by
      have h := Int.toNat_of_nonneg hN2pos.le
      have h2 : ((((2 ^ 40 - xhi) ^ 2 + ylo ^ 2).toNat : ℕ) : ℤ) = (2 ^ 40 - xhi) ^ 2 + ylo ^ 2 := h
      exact_mod_cast h2
    have hc1 : (2 ^ 40 - (xhi : ℝ)) / 2 ^ 40 ≤ 1 - x := by
      have : x ≤ (xhi : ℝ) / 2 ^ 40 := hx2
      have e : (2 ^ 40 - (xhi : ℝ)) / 2 ^ 40 = 1 - (xhi : ℝ) / 2 ^ 40 := by field_simp
      linarith
    have hc2 : 1 - x ≤ (2 ^ 40 - (xlo : ℝ)) / 2 ^ 40 := by
      have : (xlo : ℝ) / 2 ^ 40 ≤ x := hx1
      have e : (2 ^ 40 - (xlo : ℝ)) / 2 ^ 40 = 1 - (xlo : ℝ) / 2 ^ 40 := by field_simp
      linarith
    have hc0 : 0 < (2 ^ 40 - (xhi : ℝ)) / 2 ^ 40 := by
      apply div_pos _ hp40; linarith
    have hw : (((2 ^ 40 - (xhi : ℝ)) / 2 ^ 40) ^ 2 + ((ylo : ℝ) / 2 ^ 40) ^ 2) ≤
        (1 - x) ^ 2 + y ^ 2 := by
      have h1 : ((2 ^ 40 - (xhi : ℝ)) / 2 ^ 40) ^ 2 ≤ (1 - x) ^ 2 := by
        apply pow_le_pow_left₀ hc0.le hc1
      have h2 : ((ylo : ℝ) / 2 ^ 40) ^ 2 ≤ y ^ 2 := by
        apply pow_le_pow_left₀ (by positivity) hy1
      linarith
    have hwe : ((((2 ^ 40 - xhi) ^ 2 + ylo ^ 2).toNat : ℕ) : ℝ) / 2 ^ 80 =
        ((2 ^ 40 - (xhi : ℝ)) / 2 ^ 40) ^ 2 + ((ylo : ℝ) / 2 ^ 40) ^ 2 := by
      rw [hN2c]; field_simp
    have hwpos : 0 < ((2 ^ 40 - (xhi : ℝ)) / 2 ^ 40) ^ 2 + ((ylo : ℝ) / 2 ^ 40) ^ 2 := by positivity
    have hlog : (lQ xhi ylo : ℝ) ≤ Real.log ((1 - x) ^ 2 + y ^ 2) := by
      have h1 := logLoS_spec hN2
      have h2 : Real.log ((((2 ^ 40 - xhi) ^ 2 + ylo ^ 2).toNat : ℝ) / 2 ^ 80) ≤
          Real.log ((1 - x) ^ 2 + y ^ 2) := by
        apply Real.log_le_log (by rw [hwe]; exact hwpos)
        rw [hwe]; exact hw
      unfold lQ; push_cast; exact h1.trans h2
    set l : ℝ := (lQ xhi ylo : ℝ) with hl
    set c := 1 - x with hc
    have hcpos : 0 < c := by linarith
    have h1 : c * l ≤ c * Real.log ((1 - x) ^ 2 + y ^ 2) := mul_le_mul_of_nonneg_left hlog hcpos.le
    have h2 : min (((2 ^ 40 - (xhi : ℝ)) / 2 ^ 40) * l) (((2 ^ 40 - (xlo : ℝ)) / 2 ^ 40) * l) ≤ c * l := by
      rcases le_total 0 l with h | h
      · exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_right hc1 h)
      · exact (min_le_right _ _).trans (mul_le_mul_of_nonpos_right hc2 h)
    have e : -(c * (Real.log ((1 - x) ^ 2 + y ^ 2) / 2)) = -(c * Real.log ((1 - x) ^ 2 + y ^ 2)) / 2 := by
      ring
    rw [e]
    linarith
  -- (C)
  have hC : (-min ((ylo : ℝ) / 2 ^ 40 * (thetaQ (vloQ xlo ylo yhi) : ℝ))
        ((yhi : ℝ) / 2 ^ 40 * (thetaQ (vloQ xlo ylo yhi) : ℝ))) ≥
      -(y * Real.arctan (y / (x ^ 2 + y ^ 2 - x))) := by
    have hden : 0 < (xlo : ℝ) * xlo + yhi * yhi - xlo * 2 ^ 40 := by nlinarith
    have hv0 : 0 ≤ vloQ xlo ylo yhi := by
      unfold vloQ
      have : (0 : ℚ) < (xlo : ℚ) * xlo + yhi * yhi - xlo * 2 ^ 40 := by
        have h := hden
        exact_mod_cast h
      positivity
    have hvle : ((vloQ xlo ylo yhi : ℚ) : ℝ) ≤ y / (x ^ 2 + y ^ 2 - x) := by
      unfold vloQ
      push_cast
      have hd2 : 0 < x ^ 2 + y ^ 2 - x := by nlinarith
      rw [div_le_div_iff₀ hden hd2]
      -- ylo·Z·(x²+y²−x) ≤ y·(xlo²+yhi²−xlo·Z)
      have hxx : x ^ 2 - x ≤ ((xlo : ℝ) / 2 ^ 40) ^ 2 - (xlo : ℝ) / 2 ^ 40 := by nlinarith
      have hyy : y ^ 2 ≤ ((yhi : ℝ) / 2 ^ 40) ^ 2 := by nlinarith
      have hD : (x ^ 2 + y ^ 2 - x) * 2 ^ 80 ≤ (xlo : ℝ) * xlo + yhi * yhi - xlo * 2 ^ 40 := by
        have e : ((xlo : ℝ) * xlo + yhi * yhi - xlo * 2 ^ 40) =
            (((xlo : ℝ) / 2 ^ 40) ^ 2 + ((yhi : ℝ) / 2 ^ 40) ^ 2 - (xlo : ℝ) / 2 ^ 40) * 2 ^ 80 := by
          field_simp
        rw [e]; apply mul_le_mul_of_nonneg_right _ (by positivity); linarith
      have hyl : (ylo : ℝ) * 2 ^ 40 ≤ y * 2 ^ 80 := by
        have : (ylo : ℝ) / 2 ^ 40 ≤ y := hy1
        have e : (ylo : ℝ) * 2 ^ 40 = (ylo : ℝ) / 2 ^ 40 * 2 ^ 80 := by field_simp
        rw [e]; exact mul_le_mul_of_nonneg_right this (by positivity)
      calc (ylo : ℝ) * 2 ^ 40 * (x ^ 2 + y ^ 2 - x)
          ≤ y * 2 ^ 80 * (x ^ 2 + y ^ 2 - x) :=
            mul_le_mul_of_nonneg_right hyl hd2.le
        _ = y * ((x ^ 2 + y ^ 2 - x) * 2 ^ 80) := by ring
        _ ≤ y * ((xlo : ℝ) * xlo + yhi * yhi - xlo * 2 ^ 40) :=
            mul_le_mul_of_nonneg_left hD hy0
    have hth := thetaQ_le_arctan hv0 hvle
    set th : ℝ := (thetaQ (vloQ xlo ylo yhi) : ℝ) with hth_def
    have h1 : y * th ≤ y * Real.arctan (y / (x ^ 2 + y ^ 2 - x)) :=
      mul_le_mul_of_nonneg_left hth hy0
    have h2 : min ((ylo : ℝ) / 2 ^ 40 * th) ((yhi : ℝ) / 2 ^ 40 * th) ≤ y * th := by
      rcases le_total 0 th with h | h
      · exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_right hy1 h)
      · exact (min_le_right _ _).trans (mul_le_mul_of_nonpos_right hy2 h)
    linarith
  -- (D)
  have hD : (PILO : ℝ) * ((ylo : ℝ) / 2 ^ 40) ≤ Real.pi * y := by
    have h1 := PILO_lt
    have hyl0 : (0 : ℝ) ≤ (ylo : ℝ) / 2 ^ 40 := by positivity
    calc (PILO : ℝ) * ((ylo : ℝ) / 2 ^ 40) ≤ Real.pi * ((ylo : ℝ) / 2 ^ 40) :=
          mul_le_mul_of_nonneg_right h1.le hyl0
      _ ≤ Real.pi * y := mul_le_mul_of_nonneg_left hy1 Real.pi_pos.le
  -- assemble
  unfold gfun Utau
  simp only [boxLBg] at hchk'
  push_cast at hchk'
  have hA' := hA
  have hC' := hC
  push_cast at hA' hC'
  have hBc : -(1 / 2 : ℝ) * min (((2 ^ 40 - (xhi : ℝ)) / 2 ^ 40) * (lQ xhi ylo : ℝ))
        (((2 ^ 40 - (xlo : ℝ)) / 2 ^ 40) * (lQ xhi ylo : ℝ)) ≥
      -((1 - x) * (Real.log ((1 - x) ^ 2 + y ^ 2) / 2)) := hB
  nlinarith [hchk', hS, hA', hBc, hC', hD]

/-- original statement -/
theorem box_sound (pts : List Pt) (mp : ℚ) (xlo xhi ylo yhi : ℤ)
    (hxhi : xhi < 0) (hxlohi : xlo ≤ xhi) (hylo : 0 ≤ ylo)
    (hchk : boxOK pts mp (xlo, xhi, ylo, yhi) = true)
    (x y : ℝ)
    (hx1 : (xlo : ℝ) / 2 ^ 40 ≤ x) (hx2 : x ≤ (xhi : ℝ) / 2 ^ 40)
    (hy1 : (ylo : ℝ) / 2 ^ 40 ≤ y) (hy2 : y ≤ (yhi : ℝ) / 2 ^ 40) :
    (mp : ℝ) ≤ gfun pts x y := by
  simp only [boxOK, decide_eq_true_eq] at hchk
  refine box_sound_g pts _ mp xlo xhi ylo yhi hxhi hxlohi hylo hchk x y hx1 hx2 hy1 hy2 ?_
  have h := Usig_ge xlo xhi ylo yhi x y hx1 hx2 hy1 hy2 pts
  push_cast
  exact h

end CatalanLambda.Cert
