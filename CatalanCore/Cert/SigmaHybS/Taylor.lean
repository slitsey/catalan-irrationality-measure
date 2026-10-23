module

public import CatalanCore.Cert.SigmaHybS.Box

@[expose] public section

/-!
# Far-field first-order (tangent) model for the sigma part

For a macro box with centre `(x0,y0)` (integers, units `2^-40`), the points of the list split
as `pre ++ mid ++ suf`; `mid` is treated exactly (corner bound `sigSum`), the far points
`pre ++ suf` through `log q ≤ log q0 + (q - q0)/q0` (concavity of `log`), which gives, for every
cell box inside the macro, a bound with one gradient `(gx, gy)` and one Hessian bound `h`
computed once per macro.  Any split `pre, mid, suf` is sound; the choice only affects the loss.
-/

open Real

namespace CatalanCore.Cert.SigmaHybS

open CatalanLambda.Cert

def imax (a b : ℤ) : ℤ := if a ≤ b then b else a

lemma imax_ge_left (a b : ℤ) : a ≤ imax a b := by unfold imax; split_ifs with h <;> omega
lemma imax_ge_right (a b : ℤ) : b ≤ imax a b := by unfold imax; split_ifs with h <;> omega

def mp4 (gl gh a b : ℤ) : ℤ := imax (imax (gl * a) (gl * b)) (imax (gh * a) (gh * b))

def farQ (x0 y0 : ℤ) (p : Pt) : ℕ := (x0 - p.1).natAbs ^ 2 + (y0 - p.2.1).natAbs ^ 2 + 2 ^ 56
def farLo (x0 y0 : ℤ) (p : Pt) : ℕ := 2 ^ 100 / farQ x0 y0 p

abbrev FD := ℤ × ℤ × ℤ × ℤ × ℤ × ℤ

def farTerm (x0 y0 : ℤ) (p : Pt) : FD :=
  ((p.2.2 : ℤ) * logUpS (farQ x0 y0 p),
   (p.2.2 : ℤ) * (x0 - p.1) * (farLo x0 y0 p : ℤ),
   (p.2.2 : ℤ) * ((x0 - p.1).natAbs : ℤ),
   (p.2.2 : ℤ) * (y0 - p.2.1) * (farLo x0 y0 p : ℤ),
   (p.2.2 : ℤ) * ((y0 - p.2.1).natAbs : ℤ),
   (p.2.2 : ℤ) * ((farLo x0 y0 p : ℤ) + 1))

def fdAdd (a b : FD) : FD :=
  (a.1 + b.1, a.2.1 + b.2.1, a.2.2.1 + b.2.2.1, a.2.2.2.1 + b.2.2.2.1,
   a.2.2.2.2.1 + b.2.2.2.2.1, a.2.2.2.2.2 + b.2.2.2.2.2)

def farSum (x0 y0 : ℤ) : List Pt → FD
  | [] => (0, 0, 0, 0, 0, 0)
  | p :: ps => fdAdd (farTerm x0 y0 p) (farSum x0 y0 ps)

/-- the rational lower bound for `Usig` on the cell box, from the near sum `ns` and far data `fd`. -/
def sigTL (x0 y0 : ℤ) (fd : FD) (xlo xhi ylo yhi : ℤ) (ns : ℤ) : ℚ :=
  let ulo := xlo - x0
  let uhi := xhi - x0
  let vlo := ylo - y0
  let vhi := yhi - y0
  let lin : ℤ := 2 * (mp4 (fd.2.1 - fd.2.2.1) (fd.2.1 + fd.2.2.1) ulo uhi
    + mp4 (fd.2.2.2.1 - fd.2.2.2.2.1) (fd.2.2.2.1 + fd.2.2.2.2.1) vlo vhi)
  let quad : ℤ := fd.2.2.2.2.2 * (imax (ulo * ulo) (uhi * uhi) + imax (vlo * vlo) (vhi * vhi));
  -(ns : ℚ) / 2 ^ 97 - (fd.1 : ℚ) / 2 ^ 97 - ((lin + quad : ℤ) : ℚ) / 2 ^ 133

/-! ### real-valued sums -/

noncomputable def gxR (x0 y0 : ℤ) : List Pt → ℝ
  | [] => 0
  | p :: ps => (p.2.2 : ℝ) * ((x0 : ℝ) - p.1) / (farQ x0 y0 p : ℝ) + gxR x0 y0 ps

noncomputable def gyR (x0 y0 : ℤ) : List Pt → ℝ
  | [] => 0
  | p :: ps => (p.2.2 : ℝ) * ((y0 : ℝ) - p.2.1) / (farQ x0 y0 p : ℝ) + gyR x0 y0 ps

noncomputable def hR (x0 y0 : ℤ) : List Pt → ℝ
  | [] => 0
  | p :: ps => (p.2.2 : ℝ) / (farQ x0 y0 p : ℝ) + hR x0 y0 ps

lemma farQ_cast (x0 y0 : ℤ) (p : Pt) :
    (farQ x0 y0 p : ℝ) = ((x0 : ℝ) - p.1) ^ 2 + ((y0 : ℝ) - p.2.1) ^ 2 + 2 ^ 56 := by
  unfold farQ
  push_cast [Nat.cast_natAbs, Int.cast_abs, sq_abs]
  ring

lemma farQ_pos (x0 y0 : ℤ) (p : Pt) : 0 < farQ x0 y0 p := by
  unfold farQ; positivity

lemma farpt (x0 y0 : ℤ) (p : Pt) (x y : ℝ) :
    -(1 / 2 ^ 33) * ((p.2.2 : ℝ) * (logUpS (farQ x0 y0 p) : ℝ) / 2 ^ 64
      + 2 * (2 ^ 40 * x - x0) * ((p.2.2 : ℝ) * ((x0 : ℝ) - p.1) / (farQ x0 y0 p : ℝ))
      + 2 * (2 ^ 40 * y - y0) * ((p.2.2 : ℝ) * ((y0 : ℝ) - p.2.1) / (farQ x0 y0 p : ℝ))
      + ((2 ^ 40 * x - x0) ^ 2 + (2 ^ 40 * y - y0) ^ 2) * ((p.2.2 : ℝ) / (farQ x0 y0 p : ℝ)))
    ≤ (p.2.2 : ℝ) / 2 ^ 32 * (-(1 / 2) * Real.log ((x - (p.1 : ℝ) / 2 ^ 40) ^ 2
        + (y - (p.2.1 : ℝ) / 2 ^ 40) ^ 2 + (1 / 4096) ^ 2)) := by
  have hq0e := farQ_cast x0 y0 p
  have hNpos := farQ_pos x0 y0 p
  have hlogspec := logUpS_spec hNpos
  set q0 : ℝ := (farQ x0 y0 p : ℝ) with hq0
  have hq0pos : 0 < q0 := by rw [hq0]; exact_mod_cast hNpos
  set u : ℝ := 2 ^ 40 * x - x0 with hu
  set v : ℝ := 2 ^ 40 * y - y0 with hv
  set Δ : ℝ := 2 * ((x0 : ℝ) - p.1) * u + 2 * ((y0 : ℝ) - p.2.1) * v + u ^ 2 + v ^ 2 with hΔ
  have hQ : (x - (p.1 : ℝ) / 2 ^ 40) ^ 2 + (y - (p.2.1 : ℝ) / 2 ^ 40) ^ 2 + (1 / 4096) ^ 2
      = (q0 + Δ) / 2 ^ 80 := by
    rw [hq0e, hΔ, hu, hv]; field_simp; ring
  have hQpos : 0 < (x - (p.1 : ℝ) / 2 ^ 40) ^ 2 + (y - (p.2.1 : ℝ) / 2 ^ 40) ^ 2 + (1 / 4096) ^ 2 := by
    positivity
  have hqN : 0 < q0 + Δ := by
    rw [hQ] at hQpos
    exact (div_pos_iff_of_pos_right (by positivity)).mp hQpos
  rw [hQ]
  have hlog : Real.log ((q0 + Δ) / 2 ^ 80) ≤ (logUpS (farQ x0 y0 p) : ℝ) / 2 ^ 64 + Δ / q0 := by
    have e : (q0 + Δ) / 2 ^ 80 = q0 / 2 ^ 80 * ((q0 + Δ) / q0) := by field_simp
    rw [e, Real.log_mul (by positivity) (by positivity)]
    have h2 := Real.log_le_sub_one_of_pos (show 0 < (q0 + Δ) / q0 by positivity)
    have h3 : (q0 + Δ) / q0 - 1 = Δ / q0 := by field_simp; ring
    rw [h3] at h2
    linarith
  have hn : (0 : ℝ) ≤ (p.2.2 : ℝ) / 2 ^ 32 := by positivity
  have h4 := mul_le_mul_of_nonneg_left (show -(1 / 2) * ((logUpS (farQ x0 y0 p) : ℝ) / 2 ^ 64 + Δ / q0)
      ≤ -(1 / 2) * Real.log ((q0 + Δ) / 2 ^ 80) by linarith) hn
  refine le_trans (le_of_eq ?_) h4
  rw [hΔ]
  ring

lemma usig_append (a b : List Pt) (x y : ℝ) : Usig (a ++ b) x y = Usig a x y + Usig b x y := by
  induction a with
  | nil => simp [Usig]
  | cons p ps ih => simp only [List.cons_append, Usig, ih]; ring

theorem usig_far (x0 y0 : ℤ) (x y : ℝ) : ∀ fs : List Pt,
    -(1 / 2 ^ 33) * (((farSum x0 y0 fs).1 : ℝ) / 2 ^ 64
      + 2 * (2 ^ 40 * x - x0) * gxR x0 y0 fs + 2 * (2 ^ 40 * y - y0) * gyR x0 y0 fs
      + ((2 ^ 40 * x - x0) ^ 2 + (2 ^ 40 * y - y0) ^ 2) * hR x0 y0 fs) ≤ Usig fs x y := by
  intro fs
  induction fs with
  | nil => simp [farSum, gxR, gyR, hR, Usig]
  | cons p ps ih =>
    have hp := farpt x0 y0 p x y
    simp only [farSum, fdAdd, farTerm, gxR, gyR, hR, Usig]
    push_cast
    nlinarith [hp, ih]

lemma term_bd (n d q lo : ℝ) (hn : 0 ≤ n) (hq : 0 < q) (hlo0 : 0 ≤ lo)
    (h1 : lo * q ≤ 2 ^ 100) (h2 : 2 ^ 100 ≤ (lo + 1) * q) :
    (n * d * lo - n * |d|) / 2 ^ 100 ≤ n * d / q ∧ n * d / q ≤ (n * d * lo + n * |d|) / 2 ^ 100 := by
  have hr1 : lo ≤ 2 ^ 100 / q := by rw [le_div_iff₀ hq]; exact h1
  have hr2 : 2 ^ 100 / q ≤ lo + 1 := by rw [div_le_iff₀ hq]; exact h2
  have e : n * d / q = n * d * (2 ^ 100 / q) / 2 ^ 100 := by field_simp
  have hw : |d * (2 ^ 100 / q - lo)| ≤ |d| := by
    rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 ^ 100 / q - lo)]
    exact mul_le_of_le_one_right (abs_nonneg d) (by linarith)
  obtain ⟨w1, w2⟩ := abs_le.mp hw
  have hn1 := mul_le_mul_of_nonneg_left w1 hn
  have hn2 := mul_le_mul_of_nonneg_left w2 hn
  rw [e]
  constructor <;> (apply div_le_div_of_nonneg_right _ (by positivity) <;> nlinarith)

theorem farSum_bounds (x0 y0 : ℤ) : ∀ fs : List Pt,
    ((((farSum x0 y0 fs).2.1 : ℤ) : ℝ) - (((farSum x0 y0 fs).2.2.1 : ℤ) : ℝ)) / 2 ^ 100 ≤ gxR x0 y0 fs ∧
    gxR x0 y0 fs ≤ ((((farSum x0 y0 fs).2.1 : ℤ) : ℝ) + (((farSum x0 y0 fs).2.2.1 : ℤ) : ℝ)) / 2 ^ 100 ∧
    ((((farSum x0 y0 fs).2.2.2.1 : ℤ) : ℝ) - (((farSum x0 y0 fs).2.2.2.2.1 : ℤ) : ℝ)) / 2 ^ 100 ≤ gyR x0 y0 fs ∧
    gyR x0 y0 fs ≤ ((((farSum x0 y0 fs).2.2.2.1 : ℤ) : ℝ) + (((farSum x0 y0 fs).2.2.2.2.1 : ℤ) : ℝ)) / 2 ^ 100 ∧
    0 ≤ hR x0 y0 fs ∧ hR x0 y0 fs ≤ (((farSum x0 y0 fs).2.2.2.2.2 : ℤ) : ℝ) / 2 ^ 100 := by
  intro fs
  induction fs with
  | nil => simp [farSum, gxR, gyR, hR]
  | cons p ps ih =>
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := ih
    have hNpos := farQ_pos x0 y0 p
    have hq : (0 : ℝ) < (farQ x0 y0 p : ℝ) := by exact_mod_cast hNpos
    have hn : (0 : ℝ) ≤ (p.2.2 : ℝ) := by positivity
    have hlo1 : (farLo x0 y0 p : ℝ) * (farQ x0 y0 p : ℝ) ≤ 2 ^ 100 := by
      have : farLo x0 y0 p * farQ x0 y0 p ≤ 2 ^ 100 := Nat.div_mul_le_self _ _
      exact_mod_cast this
    have hlo2 : (2 : ℝ) ^ 100 ≤ ((farLo x0 y0 p : ℝ) + 1) * (farQ x0 y0 p : ℝ) := by
      have : 2 ^ 100 < farQ x0 y0 p * (2 ^ 100 / farQ x0 y0 p + 1) := Nat.lt_mul_div_succ _ hNpos
      have h2 : (2 : ℝ) ^ 100 ≤ (farQ x0 y0 p : ℝ) * ((farLo x0 y0 p : ℝ) + 1) := by
        have := this.le
        unfold farLo
        exact_mod_cast this
      linarith
    have hlo0 : (0 : ℝ) ≤ farLo x0 y0 p := by positivity
    obtain ⟨tx1, tx2⟩ := term_bd (p.2.2 : ℝ) ((x0 : ℝ) - p.1) _ _ hn hq hlo0 hlo1 hlo2
    obtain ⟨ty1, ty2⟩ := term_bd (p.2.2 : ℝ) ((y0 : ℝ) - p.2.1) _ _ hn hq hlo0 hlo1 hlo2
    have hh : (p.2.2 : ℝ) / (farQ x0 y0 p : ℝ) ≤ (p.2.2 : ℝ) * ((farLo x0 y0 p : ℝ) + 1) / 2 ^ 100 := by
      rw [div_le_div_iff₀ hq (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_left hlo2 hn]
    have hh0 : (0 : ℝ) ≤ (p.2.2 : ℝ) / (farQ x0 y0 p : ℝ) := by positivity
    simp only [farSum, fdAdd, farTerm, gxR, gyR, hR]
    push_cast [Int.natCast_natAbs, Int.cast_abs]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

lemma cast_imax_left (a b : ℤ) : (a : ℝ) ≤ (imax a b : ℤ) := by exact_mod_cast imax_ge_left a b
lemma cast_imax_right (a b : ℤ) : (b : ℝ) ≤ (imax a b : ℤ) := by exact_mod_cast imax_ge_right a b

lemma prod_le_mp4 (gl gh a b : ℤ) (g u : ℝ) (hg1 : (gl : ℝ) ≤ g) (hg2 : g ≤ gh)
    (hu1 : (a : ℝ) ≤ u) (hu2 : u ≤ b) : g * u ≤ (mp4 gl gh a b : ℤ) := by
  have s1 : g * u ≤ max (g * (a : ℝ)) (g * (b : ℝ)) := by
    rcases le_total 0 g with h | h
    · exact le_max_of_le_right (mul_le_mul_of_nonneg_left hu2 h)
    · exact le_max_of_le_left (mul_le_mul_of_nonpos_left hu1 h)
  have s2 : g * (a : ℝ) ≤ max ((gl : ℝ) * a) ((gh : ℝ) * a) := by
    rcases le_total 0 (a : ℝ) with h | h
    · exact le_max_of_le_right (mul_le_mul_of_nonneg_right hg2 h)
    · exact le_max_of_le_left (mul_le_mul_of_nonpos_right hg1 h)
  have s3 : g * (b : ℝ) ≤ max ((gl : ℝ) * b) ((gh : ℝ) * b) := by
    rcases le_total 0 (b : ℝ) with h | h
    · exact le_max_of_le_right (mul_le_mul_of_nonneg_right hg2 h)
    · exact le_max_of_le_left (mul_le_mul_of_nonpos_right hg1 h)
  have c1 : (gl : ℝ) * a ≤ (mp4 gl gh a b : ℤ) := by
    have := (cast_imax_left (gl * a) (gl * b)).trans (cast_imax_left (imax (gl * a) (gl * b)) (imax (gh * a) (gh * b)))
    unfold mp4; push_cast at this ⊢; exact this
  have c2 : (gl : ℝ) * b ≤ (mp4 gl gh a b : ℤ) := by
    have := (cast_imax_right (gl * a) (gl * b)).trans (cast_imax_left (imax (gl * a) (gl * b)) (imax (gh * a) (gh * b)))
    unfold mp4; push_cast at this ⊢; exact this
  have c3 : (gh : ℝ) * a ≤ (mp4 gl gh a b : ℤ) := by
    have := (cast_imax_left (gh * a) (gh * b)).trans (cast_imax_right (imax (gl * a) (gl * b)) (imax (gh * a) (gh * b)))
    unfold mp4; push_cast at this ⊢; exact this
  have c4 : (gh : ℝ) * b ≤ (mp4 gl gh a b : ℤ) := by
    have := (cast_imax_right (gh * a) (gh * b)).trans (cast_imax_right (imax (gl * a) (gl * b)) (imax (gh * a) (gh * b)))
    unfold mp4; push_cast at this ⊢; exact this
  exact s1.trans (max_le (s2.trans (max_le c1 c3)) (s3.trans (max_le c2 c4)))

lemma sq_le_imax (lo hi : ℤ) (u : ℝ) (h1 : (lo : ℝ) ≤ u) (h2 : u ≤ hi) :
    u ^ 2 ≤ (imax (lo * lo) (hi * hi) : ℤ) := by
  have a1 := cast_imax_left (lo * lo) (hi * hi)
  have a2 := cast_imax_right (lo * lo) (hi * hi)
  push_cast at a1 a2
  rcases le_total 0 u with h | h
  · nlinarith
  · nlinarith

theorem sigTL_sound (x0 y0 : ℤ) (pre mid suf : List Pt) (xlo xhi ylo yhi : ℤ) (x y : ℝ)
    (hx1 : (xlo : ℝ) / 2 ^ 40 ≤ x) (hx2 : x ≤ (xhi : ℝ) / 2 ^ 40)
    (hy1 : (ylo : ℝ) / 2 ^ 40 ≤ y) (hy2 : y ≤ (yhi : ℝ) / 2 ^ 40) :
    ((sigTL x0 y0 (farSum x0 y0 (pre ++ suf)) xlo xhi ylo yhi (sigSum xlo xhi ylo yhi mid) : ℚ) : ℝ)
      ≤ Usig (pre ++ mid ++ suf) x y := by
  have hmid := Usig_ge xlo xhi ylo yhi x y hx1 hx2 hy1 hy2 mid
  have hfar := usig_far x0 y0 x y (pre ++ suf)
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := farSum_bounds x0 y0 (pre ++ suf)
  have e : Usig (pre ++ mid ++ suf) x y = Usig mid x y + Usig (pre ++ suf) x y := by
    rw [usig_append, usig_append, usig_append]; ring
  rw [e]
  generalize farSum x0 y0 (pre ++ suf) = fd at *
  generalize gxR x0 y0 (pre ++ suf) = gx at *
  generalize gyR x0 y0 (pre ++ suf) = gy at *
  generalize hR x0 y0 (pre ++ suf) = hh at *
  generalize Usig (pre ++ suf) x y = UF at *
  have p2 : (0 : ℝ) < 2 ^ 100 := by positivity
  have hxl : (xlo : ℝ) ≤ 2 ^ 40 * x := by
    have := (div_le_iff₀ (by positivity : (0:ℝ) < 2 ^ 40)).mp hx1; linarith
  have hxh : 2 ^ 40 * x ≤ (xhi : ℝ) := by
    have := (le_div_iff₀ (by positivity : (0:ℝ) < 2 ^ 40)).mp hx2; linarith
  have hyl : (ylo : ℝ) ≤ 2 ^ 40 * y := by
    have := (div_le_iff₀ (by positivity : (0:ℝ) < 2 ^ 40)).mp hy1; linarith
  have hyh : 2 ^ 40 * y ≤ (yhi : ℝ) := by
    have := (le_div_iff₀ (by positivity : (0:ℝ) < 2 ^ 40)).mp hy2; linarith
  have hu1 : ((xlo - x0 : ℤ) : ℝ) ≤ 2 ^ 40 * x - x0 := by push_cast; linarith
  have hu2 : 2 ^ 40 * x - x0 ≤ ((xhi - x0 : ℤ) : ℝ) := by push_cast; linarith
  have hv1 : ((ylo - y0 : ℤ) : ℝ) ≤ 2 ^ 40 * y - y0 := by push_cast; linarith
  have hv2 : 2 ^ 40 * y - y0 ≤ ((yhi - y0 : ℤ) : ℝ) := by push_cast; linarith
  have gx1 : (((fd.2.1 - fd.2.2.1 : ℤ)) : ℝ) ≤ gx * 2 ^ 100 := by
    have := (div_le_iff₀ p2).mp b1; push_cast; linarith
  have gx2 : gx * 2 ^ 100 ≤ (((fd.2.1 + fd.2.2.1 : ℤ)) : ℝ) := by
    have := (le_div_iff₀ p2).mp b2; push_cast; linarith
  have gy1 : (((fd.2.2.2.1 - fd.2.2.2.2.1 : ℤ)) : ℝ) ≤ gy * 2 ^ 100 := by
    have := (div_le_iff₀ p2).mp b3; push_cast; linarith
  have gy2 : gy * 2 ^ 100 ≤ (((fd.2.2.2.1 + fd.2.2.2.2.1 : ℤ)) : ℝ) := by
    have := (le_div_iff₀ p2).mp b4; push_cast; linarith
  have px := prod_le_mp4 _ _ _ _ _ _ gx1 gx2 hu1 hu2
  have py := prod_le_mp4 _ _ _ _ _ _ gy1 gy2 hv1 hv2
  have qx := sq_le_imax _ _ _ hu1 hu2
  have qy := sq_le_imax _ _ _ hv1 hv2
  have hH : hh * 2 ^ 100 ≤ (fd.2.2.2.2.2 : ℝ) := by
    have := (le_div_iff₀ p2).mp b6; linarith
  have hq0 : (0 : ℝ) ≤ ((imax ((xlo - x0) * (xlo - x0)) ((xhi - x0) * (xhi - x0)) : ℤ) : ℝ)
      + ((imax ((ylo - y0) * (ylo - y0)) ((yhi - y0) * (yhi - y0)) : ℤ) : ℝ) := by
    nlinarith [sq_nonneg (2 ^ 40 * x - x0), sq_nonneg (2 ^ 40 * y - y0)]
  have hquad : ((2 ^ 40 * x - x0) ^ 2 + (2 ^ 40 * y - y0) ^ 2) * hh ≤
      (((imax ((xlo - x0) * (xlo - x0)) ((xhi - x0) * (xhi - x0)) : ℤ) : ℝ)
      + ((imax ((ylo - y0) * (ylo - y0)) ((yhi - y0) * (yhi - y0)) : ℤ) : ℝ)) * ((fd.2.2.2.2.2 : ℝ) / 2 ^ 100) := by
    apply mul_le_mul (by linarith) _ b5 hq0
    rw [le_div_iff₀ p2]; exact hH
  simp only [sigTL]
  push_cast
  push_cast at px py qx qy hquad
  generalize (2 : ℝ) ^ 40 * x - x0 = u at *
  generalize (2 : ℝ) ^ 40 * y - y0 = v at *
  nlinarith [hmid, hfar, px, py, hquad]

end CatalanCore.Cert.SigmaHybS
