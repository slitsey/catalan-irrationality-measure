module

public import CatalanMeasure.GenD.Signed.RouteI.FreeRowCap0
public import CatalanMeasure.CellCert.RawInts
public import CatalanMeasure.GenD.Signed.RouteI.RowCert.RawHex

@[expose] public section

set_option Elab.async false
set_option maxRecDepth 100000

/-!
# The row certificate: generic lemmas

The packed convolution guard with a tree-packed kernel, the piecewise radial cover with its small-`t`
end, one chunk of atoms through the moment engine, and the digit literal of the direct moments.

kcost: every `decide +kernel` here is on one literal or one power.
-/

namespace CatalanMeasure.GenD.Signed.RouteI.RowCert

open Real Set
open CatalanMeasure.GenD.Signed.RouteI.FreeRowCap0
open CatalanMeasure.GenD.Signed.RouteI.MarkedPilot
open CatalanMeasure.GenD.Signed.RouteI.MarkedSourceTail
open CatalanMeasure.GenD.Signed.Davis.CircleCheb

/-! ### The packed convolution guard with a tree-packed kernel -/

theorem hornerZ_cast (R : ℕ) : ∀ l : List ℕ,
    hornerZ (R : ℤ) (l.map Int.ofNat) = ((hornerPack R l : ℕ) : ℤ)
  | [] => rfl
  | a :: l => by
    simp only [List.map_cons, hornerZ, hornerPack, hornerZ_cast R l]
    push_cast
    rfl

theorem pack_horner (lg R : ℕ) (l : List ℕ) (hl : l.length ≤ 2 ^ lg) :
    (packT lg (R : ℤ) (l.map Int.ofNat)).toNat = hornerPack R l := by
  rw [packT_eq lg _ _ (by simpa using hl), pk_eq_horner, hornerZ_cast]
  simp

/-- The kernel row of the guard, tree-packed. -/
def kPack (p : BinPar) (N w lg : ℕ) : ℕ :=
  forceI (Int.ofNat (2 ^ (w + 1))) fun r =>
    (packT lg r (((List.range (2 * p.B)).map fun e => Kn N p.B (bdist e (p.B - 1))).map
      Int.ofNat)).toNat

/-- `hvCheck` with the tree-packed kernel row. -/
def hvCheck2 (p : BinPar) (N w M lg : ℕ) (L : List (ℕ × ℕ)) : Bool :=
  L.all (fun q => decide (q.1 < p.B)) && decide (M < 2 ^ w) &&
  decide (2 ^ 64 * (L.map Prod.snd).sum < 2 ^ w) &&
  decide (((kPack p N w lg *
      (L.map fun q => q.2 * (2 ^ (w + 1)) ^ q.1).sum) / (2 ^ (w + 1)) ^ (p.B - 1) %
        (2 ^ (w + 1)) ^ p.B +
      (2 ^ w - 1 - M) * (((2 ^ (w + 1)) ^ p.B - 1) / (2 ^ (w + 1) - 1))) &&&
    (2 ^ w * (((2 ^ (w + 1)) ^ p.B - 1) / (2 ^ (w + 1) - 1))) = 0)

theorem hvCheck2_eq {p : BinPar} {N w M lg : ℕ} {L : List (ℕ × ℕ)} (hl : 2 * p.B ≤ 2 ^ lg) :
    hvCheck2 p N w M lg L = hvCheck p N w M L := by
  have e : kPack p N w lg = hornerPack (2 ^ (w + 1))
      ((List.range (2 * p.B)).map fun e => Kn N p.B (bdist e (p.B - 1))) := by
    unfold kPack
    rw [forceI_eq]
    have := pack_horner lg (2 ^ (w + 1))
      ((List.range (2 * p.B)).map fun e => Kn N p.B (bdist e (p.B - 1))) (by simpa using hl)
    exact this
  unfold hvCheck2 hvCheck
  rw [e]

end CatalanMeasure.GenD.Signed.RouteI.RowCert

namespace CatalanMeasure.GenD.Signed.RouteI.RowCert

open Real Set
open CatalanMeasure.GenD.Signed.RouteI.FreeRowCap0
open CatalanMeasure.GenD.Signed.RouteI.MarkedPilot
open CatalanMeasure.GenD.Signed.RouteI.MarkedSourceTail
open CatalanMeasure.GenD.Signed.RouteI.CapFields
open CatalanMeasure.GenD.Signed.RouteI.CapFields.CapSource
open CatalanMeasure.GenD.Signed.RouteI.CapSourceData
open CatalanMeasure.GenD.Signed.RouteI.OrdHf (Cov Blk blkF sumF polK psiR bot mBlk sumEQ mc4)
open CatalanMeasure.GenD.Signed.RouteI.CompactHf (rawQ)
open CatalanMeasure.Signed.ChebSquare

/-! ### Logarithms by complex atoms

An atom with `Re r ≤ 1` majorises `log (1 - u)` for `0 ≤ u < 1`; the loss is of second order in
`Im r`, so `|q|` stays far from `1`. -/

theorem log_one_sub_le_cplx {u : ℝ} {q : ℂ} (h0 : 0 ≤ u) (h1 : u < 1) (hr : (rq q).re ≤ 1) :
    Real.log (1 - u) ≤ KQ q u := by
  unfold KQ
  have hp : 0 < 1 - u := by linarith
  refine Real.log_le_log hp ?_
  have h2 : 1 - u ≤ (1 - rq q * (u : ℂ)).re := by
    simp only [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero]
    nlinarith
  exact h2.trans (Complex.re_le_norm _)

theorem log_sub_atomC {c : ℚ} {q : ℚ × ℚ} (hc : 0 ≤ c) (hq : q.1 ^ 2 + q.2 ^ 2 < 1)
    (hr : rRe q ≤ 1) {t : ℝ} (h0 : 0 < t) (h1 : t < 1) :
    (c : ℝ) * Real.log (1 - t) ≤ avQ false [(c, q.1, q.2)] t := by
  rw [avQ_cons, avQ_nil]
  simp only [av, Bool.false_eq_true, ite_false, add_zero]
  have e : (rq (qOf q)).re ≤ 1 := by
    rw [rq_eq hq]
    show ((rRe q : ℚ) : ℝ) ≤ 1
    exact_mod_cast hr
  exact mul_le_mul_of_nonneg_left (log_one_sub_le_cplx h0.le h1 e) (by exact_mod_cast hc)

theorem log_t_atomC {c : ℚ} {q : ℚ × ℚ} (hc : 0 ≤ c) (hq : q.1 ^ 2 + q.2 ^ 2 < 1)
    (hr : rRe q ≤ 1) {t : ℝ} (h0 : 0 < t) (h1 : t ≤ 1) :
    (c : ℝ) * Real.log t ≤ avQ true [(c, -q.1, -q.2)] t := by
  rw [avQ_cons, avQ_nil]
  simp only [av, if_true, add_zero]
  have e0 : -qOf (-q.1, -q.2) = qOf q := by
    apply Complex.ext <;> simp [qOf]
  rw [e0]
  have e : (rq (qOf q)).re ≤ 1 := by
    rw [rq_eq hq]
    show ((rRe q : ℚ) : ℝ) ≤ 1
    exact_mod_cast hr
  have := log_one_sub_le_cplx (u := 1 - t) (q := qOf q) (by linarith) (by linarith) e
  rw [show (1 : ℝ) - (1 - t) = t by ring] at this
  exact mul_le_mul_of_nonneg_left this (by exact_mod_cast hc)

/-! ### Cutting the block series on a piece of the cover -/

/-- The block with its series cut at `n`. -/
def cutB (n : ℕ) (B : Blk) : Blk := ⟨B.rho, B.sg, B.M, B.D.take n⟩

/-- The blocks cut at the given degrees; `(n, y)`: degree and bound of the ratio. -/
def cutL : List (ℕ × ℚ) → List Blk → List Blk
  | p :: ps, B :: Bs => cutB p.1 B :: cutL ps Bs
  | _, Bs => Bs

/-- The tail of the cut blocks. -/
def tauQ (W : ℕ) : List (ℕ × ℚ) → List Blk → ℚ
  | p :: ps, B :: Bs => (l1 (B.D.drop p.1) : ℚ) / 2 ^ W * p.2 ^ (p.1 + 1) + tauQ W ps Bs
  | _, _ => 0

/-- The ratio bounds hold on `[b, a]`, and no radius lies inside. -/
def yOK (b a : ℚ) : List (ℕ × ℚ) → List Blk → Bool
  | p :: ps, B :: Bs =>
    decide (0 ≤ p.2) && decide (p.2 ≤ 1) &&
      ((decide (B.rho ≤ b) && decide (B.rho / b ≤ p.2)) ||
        (decide (a ≤ B.rho) && decide (a / B.rho ≤ p.2))) && yOK b a ps Bs
  | _, _ => true

theorem polK_append (y : ℝ) : ∀ (A B : List ℤ) (k : ℕ),
    polK (A ++ B) k y = polK A k y + polK B (k + A.length) y
  | [], B, k => by simp [polK]
  | a :: A, B, k => by
    simp only [List.cons_append, polK, polK_append y A B (k + 1), List.length_cons]
    rw [show k + 1 + A.length = k + (A.length + 1) by ring]
    ring

theorem l1_cons' (a : ℤ) (t : List ℤ) : l1 (a :: t) = |a| + l1 t := by
  simp [l1]

theorem l1_nonneg' : ∀ t : List ℤ, 0 ≤ l1 t
  | [] => by simp [l1]
  | a :: t => by
    rw [l1_cons']
    have := l1_nonneg' t
    have := abs_nonneg a
    omega

theorem polK_le {y : ℝ} (h0 : 0 ≤ y) (h1 : y ≤ 1) : ∀ (D : List ℤ) (k : ℕ),
    polK D k y ≤ ((l1 D : ℤ) : ℝ) * y ^ (k + 1)
  | [], k => by simp [polK, l1]
  | d :: t, k => by
    have ih := polK_le h0 h1 t (k + 1)
    simp only [polK]
    rw [l1_cons']
    push_cast
    have hp : (0 : ℝ) ≤ y ^ (k + 1) := by positivity
    have a : (d : ℝ) * y ^ (k + 1) ≤ |(d : ℝ)| * y ^ (k + 1) :=
      mul_le_mul_of_nonneg_right (le_abs_self _) hp
    have b : y ^ (k + 1 + 1) ≤ y ^ (k + 1) := by
      rw [pow_succ y (k + 1)]
      nlinarith
    have c : (0 : ℝ) ≤ ((l1 t : ℤ) : ℝ) := by exact_mod_cast l1_nonneg' t
    have := mul_le_mul_of_nonneg_left b c
    nlinarith

theorem psiR_nonneg {ρ x : ℝ} (hρ : 0 < ρ) (hx : 0 < x) : 0 ≤ psiR ρ x := by
  unfold psiR
  split_ifs <;> positivity

theorem psiR_le_one {ρ x : ℝ} (hρ : 0 < ρ) (hx : 0 < x) : psiR ρ x ≤ 1 := by
  unfold psiR
  split_ifs with h
  · rw [div_le_one hx]; exact h.le
  · rw [div_le_one hρ]; linarith

theorem blk_cut (W n : ℕ) (B : Blk) {x y : ℝ} (hρ : (0 : ℝ) < B.rho) (hx : 0 < x)
    (hy : psiR B.rho x ≤ y) (hy1 : y ≤ 1) :
    blkF W B x ≤ blkF W (cutB n B) x + ((l1 (B.D.drop n) : ℤ) : ℝ) / 2 ^ W * y ^ (n + 1) := by
  have p0 := psiR_nonneg hρ hx
  have p1 := psiR_le_one hρ hx
  have hd := polK_append (psiR B.rho x) (B.D.take n) (B.D.drop n) 0
  rw [List.take_append_drop] at hd
  have hq : (0 : ℝ) < 2 ^ W := by positivity
  have key : polK (B.D.drop n) (0 + (B.D.take n).length) (psiR B.rho x) ≤
      ((l1 (B.D.drop n) : ℤ) : ℝ) * y ^ (n + 1) := by
    by_cases hn : n ≤ B.D.length
    · have e : (B.D.take n).length = n := by simp [hn]
      rw [e, zero_add]
      have a := polK_le p0 p1 (B.D.drop n) n
      have c : (0 : ℝ) ≤ ((l1 (B.D.drop n) : ℤ) : ℝ) := by exact_mod_cast l1_nonneg' _
      exact a.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ p0 hy _) c)
    · have e : B.D.drop n = [] := List.drop_eq_nil_of_le (by omega)
      rw [e]
      simp [polK, l1]
  unfold blkF cutB
  simp only
  rw [hd, add_div]
  have : polK (B.D.drop n) (0 + (B.D.take n).length) (psiR B.rho x) / 2 ^ W ≤
      ((l1 (B.D.drop n) : ℤ) : ℝ) / 2 ^ W * y ^ (n + 1) := by
    rw [div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right key hq.le
  linarith

theorem psi_bound {ρ b a y x : ℝ} (hρ : 0 < ρ) (hb : 0 < b) (hx : x ∈ Icc b a)
    (h : (ρ ≤ b ∧ ρ / b ≤ y) ∨ (a ≤ ρ ∧ a / ρ ≤ y)) : psiR ρ x ≤ y := by
  obtain ⟨h1, h2⟩ := hx
  have hx0 : 0 < x := lt_of_lt_of_le hb h1
  unfold psiR
  rcases h with ⟨c, d⟩ | ⟨c, d⟩
  · split_ifs with hl
    · exact le_trans (div_le_div_of_nonneg_left hρ.le hb h1) d
    · have e1 : x = ρ := le_antisymm (not_lt.1 hl) (c.trans h1)
      have e2 : b = ρ := le_antisymm (h1.trans e1.le) c
      rw [e1]
      rw [e2] at d
      exact d
  · split_ifs with hl
    · linarith
    · exact le_trans (div_le_div_of_nonneg_right h2 hρ.le) d

theorem sumF_cut (W : ℕ) {b a : ℚ} (hb : 0 < b) {x : ℝ} (hx : x ∈ Icc (b : ℝ) a) :
    ∀ (P : List (ℕ × ℚ)) (Bs : List Blk), (∀ B ∈ Bs, 0 < B.rho) → yOK b a P Bs = true →
      sumF W Bs x ≤ sumF W (cutL P Bs) x + ((tauQ W P Bs : ℚ) : ℝ)
  | [], Bs, _, _ => by
    cases Bs <;> simp [cutL, tauQ]
  | _ :: _, [], _, _ => by simp [cutL, tauQ]
  | p :: ps, B :: Bs, h, hy => by
    simp only [yOK, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hy
    obtain ⟨⟨⟨y0, y1⟩, hc⟩, hr⟩ := hy
    have ih := sumF_cut W hb hx ps Bs (fun B hB => h B (List.mem_cons_of_mem _ hB)) hr
    have r0 := h B List.mem_cons_self
    have r0' : (0 : ℝ) < B.rho := by exact_mod_cast r0
    have hb' : (0 : ℝ) < b := by exact_mod_cast hb
    have hx0 : 0 < x := lt_of_lt_of_le hb' hx.1
    have hps : psiR B.rho x ≤ p.2 := by
      refine psi_bound r0' hb' hx ?_
      rcases hc with ⟨c, d⟩ | ⟨c, d⟩
      · left
        exact ⟨by exact_mod_cast c, by exact_mod_cast d⟩
      · right
        exact ⟨by exact_mod_cast c, by exact_mod_cast d⟩
    have hk := blk_cut W p.1 B r0' hx0 hps (by exact_mod_cast y1)
    simp only [sumF, cutL, tauQ, List.map_cons, List.sum_cons] at ih ⊢
    push_cast
    linarith

theorem cutL_mem : ∀ (P : List (ℕ × ℚ)) (Bs : List Blk) (B' : Blk), B' ∈ cutL P Bs →
    ∃ B ∈ Bs, B'.rho = B.rho ∧ B'.M = B.M ∧ B'.sg = B.sg
  | [], Bs, B', h => by
    cases Bs <;> simp only [cutL] at h
    · simp at h
    · exact ⟨B', h, rfl, rfl, rfl⟩
  | _ :: _, [], B', h => by simp [cutL] at h
  | p :: ps, B :: Bs, B', h => by
    simp only [cutL, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨B, List.mem_cons_self, rfl, rfl, rfl⟩
    · obtain ⟨B0, m, e⟩ := cutL_mem ps Bs B' h
      exact ⟨B0, List.mem_cons_of_mem _ m, e⟩

/-- The cover with cut blocks. -/
def Cov.cut (C : Cov) (P : List (ℕ × ℚ)) : Cov := ⟨C.W, cutL P C.Bs, C.s, C.Cl, C.α, C.β⟩

/-- All checks of a piece of the cover. -/
def pieceChk (C : Cov) (P : List (ℕ × ℚ)) (E K Bud' Bud : ℚ) (n : ℚ × ℚ) (ns : List (ℚ × ℚ)) : Bool :=
  decide (0 < n.1) && decide (0 < bot n ns) && decide (sumEQ C.W (cutL P C.Bs) ≤ E) &&
    (Cov.cut C P).chain E K Bud' n ns && (n :: ns).all (Cov.cut C P).nodeOK &&
    yOK (bot n ns) n.1 P C.Bs && decide (Bud' + tauQ C.W P C.Bs ≤ Bud)

theorem piece_cover (C : Cov) {P : List (ℕ × ℚ)} {E K Bud' Bud : ℚ} {n : ℚ × ℚ} {ns : List (ℚ × ℚ)}
    (hs : 0 ≤ C.s) (hα : 0 ≤ C.α)
    (hB : ∀ B ∈ C.Bs, 0 < B.rho ∧ 0 ≤ B.M ∧ Real.log B.rho ≤ B.sg)
    (hK : 2 * C.s + mc4 C.Cl 0 * C.α ^ 2 ≤ K)
    (h : pieceChk C P E K Bud' Bud n ns = true) :
    ∀ x ∈ Icc ((bot n ns : ℚ) : ℝ) n.1, C.Phi x ≤ Bud := by
  simp only [pieceChk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨h0, hb⟩, hE⟩, hc⟩, hn⟩, hy⟩, hτ⟩ := h
  intro x hx
  have hB' : ∀ B ∈ (Cov.cut C P).Bs, 0 < B.rho ∧ 0 ≤ B.M ∧ Real.log B.rho ≤ B.sg := by
    intro B hm
    obtain ⟨B0, m, e1, e2, e3⟩ := cutL_mem P C.Bs B hm
    rw [e1, e2, e3]
    exact hB B0 m
  have c1 := (Cov.cut C P).cover (E := E) (K := K) (Bud := Bud') hs hα hB'
    (by rw [OrdHf.sumEQ_cast]; exact_mod_cast hE) hK ns n h0 hc
    (fun m hm => List.all_eq_true.1 hn m hm) x hx
  have c2 := sumF_cut C.W hb hx P C.Bs (fun B hm => (hB B hm).1) hy
  have c3 : (Bud' : ℝ) + ((tauQ C.W P C.Bs : ℚ) : ℝ) ≤ Bud := by exact_mod_cast hτ
  unfold Cov.Phi at c1 ⊢
  simp only [Cov.cut] at c1
  linarith

theorem glue {f : ℝ → ℝ} {b m a : ℝ} {B : ℝ} (h1 : ∀ x ∈ Icc b m, f x ≤ B)
    (h2 : ∀ x ∈ Icc m a, f x ≤ B) : ∀ x ∈ Icc b a, f x ≤ B := by
  intro x hx
  rcases le_total x m with h | h
  · exact h1 x ⟨hx.1, h⟩
  · exact h2 x ⟨h, hx.2⟩

/-! ### Below the smallest radius -/

/-- The block bound below `x0`. -/
def smallY (W : ℕ) (x0 : ℚ) : List Blk → ℚ
  | [] => 0
  | B :: t => (B.M * B.sg + (l1 B.D : ℚ) / 2 ^ W * (x0 / B.rho)) + smallY W x0 t

theorem sumF_smallY (W : ℕ) {x0 : ℚ} {t : ℝ} (h0 : 0 < t) (ht : t ≤ x0) : ∀ Bs : List Blk,
    (∀ B ∈ Bs, 0 < B.rho ∧ 0 ≤ B.M ∧ Real.log B.rho ≤ B.sg) → (∀ B ∈ Bs, x0 ≤ B.rho) →
    sumF W Bs t ≤ ((smallY W x0 Bs : ℚ) : ℝ)
  | [], _, _ => by simp [sumF, smallY]
  | B :: Bs, h, h' => by
    have ih := sumF_smallY W h0 ht Bs (fun x hx => h x (List.mem_cons_of_mem _ hx))
      (fun x hx => h' x (List.mem_cons_of_mem _ hx))
    obtain ⟨r0, m0, sl⟩ := h B List.mem_cons_self
    have hx := h' B List.mem_cons_self
    have r0' : (0 : ℝ) < B.rho := by exact_mod_cast r0
    have m0' : (0 : ℝ) ≤ B.M := by exact_mod_cast m0
    have hx' : (x0 : ℝ) ≤ B.rho := by exact_mod_cast hx
    have hle : t ≤ B.rho := ht.trans hx'
    have e : sumF W (B :: Bs) t = blkF W B t + sumF W Bs t := by simp [sumF]
    rw [e]
    simp only [smallY]
    push_cast
    have hps : psiR B.rho t = t / B.rho := by
      unfold psiR
      rw [if_neg (not_lt.2 hle)]
    have p0 := psiR_nonneg r0' h0
    have p1 := psiR_le_one r0' h0
    have hq : (0 : ℝ) < 2 ^ W := by positivity
    have c : (0 : ℝ) ≤ ((l1 B.D : ℤ) : ℝ) := by exact_mod_cast l1_nonneg' _
    have a := polK_le p0 p1 B.D 0
    have b : psiR B.rho t ≤ x0 / B.rho := by
      rw [hps]
      exact div_le_div_of_nonneg_right ht r0'.le
    have d : polK B.D 0 (psiR B.rho t) / 2 ^ W ≤ ((l1 B.D : ℤ) : ℝ) / 2 ^ W * ((x0 : ℝ) / B.rho) := by
      rw [div_mul_eq_mul_div]
      refine div_le_div_of_nonneg_right ?_ hq.le
      refine a.trans ?_
      simp only [zero_add, pow_one]
      exact mul_le_mul_of_nonneg_left b c
    have f : (B.M : ℝ) * Real.log (max t B.rho) ≤ B.M * B.sg := by
      rw [max_eq_right hle]
      exact mul_le_mul_of_nonneg_left sl m0'
    unfold blkF
    linarith

theorem evC_spec (C : Cov) (x : ℚ) :
    ((C.evC x : ℚ) : ℝ) = rawQ C.Cl 0 ((C.α : ℝ) * x + C.β) := by
  have := OrdHf.evT_spec (C.α * x + C.β) C.Cl 0 1 (C.α * x + C.β)
    (by simp [basis_zero]) (by push_cast; simp [basis])
  push_cast at this
  exact this

theorem small_cover (C : Cov) {x0 Bud : ℚ} (hs : 0 ≤ C.s) (hα : C.α = 2) (hβ : C.β = -1)
    (h0 : 0 < x0) (h1 : x0 ≤ 1)
    (hB : ∀ B ∈ C.Bs, 0 < B.rho ∧ 0 ≤ B.M ∧ Real.log B.rho ≤ B.sg)
    (hx : ∀ B ∈ C.Bs, x0 ≤ B.rho)
    (hsm : smallY C.W x0 C.Bs + max (-C.evC 0) (-C.evC x0) + mc4 C.Cl 0 * C.α ^ 2 * x0 ^ 2 / 8 ≤ Bud) :
    ∀ t ∈ Ioc (0 : ℝ) x0, C.Phi t ≤ Bud := by
  intro t ht
  have h0' : (0 : ℝ) < x0 := by exact_mod_cast h0
  have h1' : (x0 : ℝ) ≤ 1 := by exact_mod_cast h1
  have a := sumF_smallY C.W ht.1 ht.2 C.Bs hB hx
  have hz : ∀ x ∈ Icc (0 : ℝ) x0, (C.α : ℝ) * x + C.β ∈ Icc (-1 : ℝ) 1 := by
    intro x hx
    rw [hα, hβ]
    push_cast
    constructor <;> linarith [hx.1, hx.2]
  have ce := OrdHf.CE_rawQ h0' hz C.Cl 0
  have e0 : -rawQ C.Cl 0 ((C.α : ℝ) * 0 + C.β) ≤ ((-C.evC 0 : ℚ) : ℝ) := by
    have := evC_spec C 0
    push_cast at this ⊢
    rw [this]
  have e1 : -rawQ C.Cl 0 ((C.α : ℝ) * x0 + C.β) ≤ ((-C.evC x0 : ℚ) : ℝ) := by
    have := evC_spec C x0
    push_cast at this ⊢
    rw [this]
  have m := OrdHf.CE.le_max h0' ce e0 e1 t ⟨ht.1.le, ht.2⟩
  have l : (0 : ℝ) ≤ Real.log (1 + t ^ 2) := Real.log_nonneg (by nlinarith [sq_nonneg t])
  have s' : (0 : ℝ) ≤ C.s := by exact_mod_cast hs
  have hb : ((smallY C.W x0 C.Bs + max (-C.evC 0) (-C.evC x0) + mc4 C.Cl 0 * C.α ^ 2 * x0 ^ 2 / 8 : ℚ) : ℝ) ≤ Bud := by
    exact_mod_cast hsm
  push_cast at hb
  have hm : max (((-C.evC x0 : ℚ) : ℝ)) (((-C.evC 0 : ℚ) : ℝ)) ≤
      max (-(C.evC 0 : ℝ)) (-(C.evC x0 : ℝ)) := by
    push_cast
    rw [max_comm]
  unfold Cov.Phi
  have q := mul_nonneg s' l
  simp only [sub_zero] at m
  have m' : -rawQ C.Cl 0 ((C.α : ℝ) * t + C.β) ≤ max (-(C.evC 0 : ℝ)) (-(C.evC x0 : ℝ)) +
      ((mc4 C.Cl 0 : ℚ) : ℝ) * (C.α : ℝ) ^ 2 * (x0 : ℝ) ^ 2 / 8 := by
    linarith
  nlinarith

/-! ### The radial hypotheses from a cover -/

theorem rad_phi (C : Cov) {dP : ℕ} (hdP : 0 < dP) {cl : List ℤ} (hCs : C.s = 39 / 29)
    (hα : C.α = 2) (hβ : C.β = -1) (hCl : C.Cl = cl.map fun d : ℤ => (d : ℚ) / dP) {Bud : ℚ} {t : ℝ}
    (h : C.Phi t ≤ Bud) :
    sumF C.W C.Bs t - 39 / 29 * Real.log (1 + t ^ 2) ≤ rawSum cl 0 (2 * t - 1) / dP + (Bud : ℝ) := by
  unfold Cov.Phi at h
  rw [hCs, hα, hβ, hCl, rawQ_scaled] at h
  push_cast at h
  have e : (2 : ℝ) * t + -1 = 2 * t - 1 := by ring
  rw [e] at h
  linarith

theorem hRad2_pos {R : OrdHf.RadLit}
    (hR : OrdHf.RadOK R capSource (auxT Sign.pos) (tgt Sign.pos) (sumP (auxT Sign.pos)) 16)
    (hRs : R.s = 1) (C : Cov) {dP : ℕ} (hdP : 0 < dP) {cl : List ℤ} {x0 Bud : ℚ}
    (hW : C.W = R.W) (hBs : C.Bs = R.Bs) (hCs : C.s = 39 / 29) (hα : C.α = 2) (hβ : C.β = -1)
    (hCl : C.Cl = cl.map fun d : ℤ => (d : ℚ) / dP)
    (hsm : ∀ t ∈ Ioc (0 : ℝ) x0, C.Phi t ≤ Bud) (hcv : ∀ t ∈ Icc (x0 : ℝ) 1, C.Phi t ≤ Bud)
    {dom : Set ℝ} (hd : ∀ t ∈ dom, t ∈ Ioc (0 : ℝ) 1) :
    ∀ t ∈ dom, capSource.radialA (Trunc.finite 384) Sign.pos (sgOf Sign.pos * t) -
        39 / 29 * Real.log (1 + t ^ 2) + (((0 : ℚ) : ℝ)) * Real.log t ≤
      rawSum cl 0 (2 * t - 1) / dP + ((Bud : ℝ) + ((OrdHf.errS R 16 : ℚ) : ℝ)) := by
  intro t ht
  obtain ⟨t0, t1⟩ := hd t ht
  have hP : C.Phi t ≤ Bud := by
    rcases le_total t (x0 : ℝ) with h | h
    · exact hsm t ⟨t0, h⟩
    · exact hcv t ⟨h, t1⟩
  have a := rad_phi C hdP hCs hα hβ hCl hP
  have b := radP_le hR hRs t0
  rw [hW, hBs] at a
  simp only [sgOf, one_mul, Rat.cast_zero, zero_mul, add_zero]
  linarith

theorem hRad2_neg {R : OrdHf.RadLit}
    (hR : OrdHf.RadOK R capSource (auxT Sign.neg) (tgt Sign.neg) (sumP (auxT Sign.neg)) 16)
    (hRs : R.s = -1) {rns : List ℕ} {rb nm : ℕ} (hrn : OrdHf.rnOK R rns rb = true)
    (hf : OrdHf.fbOK R = true) {Dm : List ℤ} (hDm : Dm = OrdHf.truncD R.sh nm (OrdHf.mirF R rns rb 16))
    {Tm : ℤ} (hTm : OrdHf.abs1 ((OrdHf.mirF R rns rb 16).drop nm) = Tm)
    (C : Cov) {dP : ℕ} (hdP : 0 < dP) {cl : List ℤ} {x0 Bud : ℚ}
    (hW : C.W = R.W) (hBs : C.Bs = R.Bs ++ [mBlk Dm]) (hCs : C.s = 39 / 29) (hα : C.α = 2)
    (hβ : C.β = -1) (hCl : C.Cl = cl.map fun d : ℤ => (d : ℚ) / dP)
    (hsm : ∀ t ∈ Ioc (0 : ℝ) x0, C.Phi t ≤ Bud) (hcv : ∀ t ∈ Icc (x0 : ℝ) 1, C.Phi t ≤ Bud)
    {dom : Set ℝ} (hd : ∀ t ∈ dom, t ∈ Ioc (0 : ℝ) 1) :
    ∀ t ∈ dom, capSource.radialA (Trunc.finite 384) Sign.neg (sgOf Sign.neg * t) -
        39 / 29 * Real.log (1 + t ^ 2) + (((0 : ℚ) : ℝ)) * Real.log t ≤
      rawSum cl 0 (2 * t - 1) / dP + ((Bud : ℝ) + ((errN R Tm : ℚ) : ℝ)) := by
  intro t ht
  obtain ⟨t0, t1⟩ := hd t ht
  have hP : C.Phi t ≤ Bud := by
    rcases le_total t (x0 : ℝ) with h | h
    · exact hsm t ⟨t0, h⟩
    · exact hcv t ⟨h, t1⟩
  have a := rad_phi C hdP hCs hα hβ hCl hP
  have b := radN_le hR hRs hrn hf hDm hTm t0 t1
  rw [hW, hBs] at a
  have e : sgOf Sign.neg * t = -t := by simp [sgOf]
  rw [e]
  simp only [Rat.cast_zero, zero_mul, add_zero]
  linarith

end CatalanMeasure.GenD.Signed.RouteI.RowCert

namespace CatalanMeasure.GenD.Signed.RouteI.RowCert

open Real Set
open CatalanMeasure.GenD.Signed.RouteI.FreeRowCap0
open CatalanMeasure.GenD.Signed.RouteI.MarkedPilot
open CatalanMeasure.GenD.Signed.RouteI.MarkedSourceTail

/-! ### One chunk of atoms through the moment engine -/

/-- The scale of the row polynomial. -/
def dPc : ℕ := 2 ^ 80

/-- GD6: the radix of the rounded complex products of the row engine; the one place where it is written. -/
def rowD : ℕ := 2 ^ 128 + 51

/-- The engine at degree `I * bs - 1` for atoms. -/
def pG (bs I lg lI : ℕ) : EPar :=
  ⟨Int.ofNat rowD, bs, I, lg, lI, Int.ofNat (2 ^ 384 + 2), Int.ofNat ((2 ^ 384 + 2) ^ bs)⟩

/-- The moment check with the radices forced to literals once (GrpN fix: scale `(1, 2^16 D^2)`, strict lists). -/
def momG (s : Bool) (bs I lg lI : ℕ) (E : List Ent) (c : List ℤ) : Bool :=
  forceI (Int.ofNat rowD) fun d => forceI (Int.ofNat (2 ^ 384 + 2)) fun b =>
    forceI (Int.ofNat ((2 ^ 384 + 2) ^ bs)) fun cc =>
    forceI (Int.ofNat (2 ^ 16 * rowD ^ 2)) fun sc =>
      forceI (Int.ofNat 1) fun dp =>
        grpListS s dp sc (moments ⟨d, bs, I, lg, lI, b, cc⟩ E) == c

/-- All checks of a chunk. -/
def grpB (s : Bool) (bs I lg lI : ℕ) (ρ : ℚ) (A : List QA) (E : List Ent) (c : List ℤ) : Bool :=
  decide (bs ≤ 2 ^ lg) && decide (I ≤ 2 ^ lI) && decide (1 ≤ I * bs) && decide (bs ≤ 2 ^ 13) &&
  decide (I ≤ 2 ^ 13) && decide (I * bs ≤ 2 ^ 13) && decide (A.length ≤ 1024) &&
  decide (0 ≤ ρ) && decide (ρ < 1) && A.all (fun a => decide (a.2.1 ^ 2 + a.2.2 ^ 2 ≤ ρ ^ 2)) &&
  decide ((A.map fun a => |a.1|).sum * (4 * (ρ ^ (I * bs) * (1 - ρ)⁻¹ / ((I * bs : ℕ) : ℚ))) ≤
    1 / 10 ^ 11) &&
  decide ((E.map fun e => |e.1|).sum ≤ 2 ^ 100) &&
  entB (Int.ofNat rowD) (2 ^ 96) (1 / 2 ^ 126) (1 / 2 ^ 96) A E &&
  momG s bs I lg lI E c

theorem pG_ok {bs I lg lI : ℕ} (h1 : bs ≤ 2 ^ lg) (h2 : I ≤ 2 ^ lI) : (pG bs I lg lI).OK where
  D_pos := by simp only [pG]; decide +kernel -- kcost: one literal
  B_pos := by simp only [pG]; decide +kernel -- kcost: one literal
  B_even := ⟨Int.ofNat (2 ^ 383 + 1), by simp only [pG]; decide +kernel⟩ -- kcost: one product
  C_eq := by
    simp only [pG]
    have : Int.ofNat (2 ^ 384 + 2) ^ bs = ((((2 ^ 384 + 2) ^ bs : ℕ)) : ℤ) := by push_cast; rfl
    rw [this]
    rfl
  lg := h1
  lI := h2

theorem pG_D (bs I lg lI : ℕ) : ((pG bs I lg lI).D : ℝ) = 2 ^ 128 + 51 := by
  have : (pG bs I lg lI).D = 2 ^ 128 + 51 := by simp only [pG, rowD]; decide +kernel -- kcost: one power
  rw [this]
  push_cast
  norm_num

set_option exponentiation.threshold 2000 in
theorem eta_le {bs I lg lI : ℕ} (hb : bs ≤ 2 ^ 13) (hI : I ≤ 2 ^ 13) (hbI : I * bs ≤ 2 ^ 13) :
    etaOf (pG bs I lg lI) ((1 / 2 ^ 126 : ℚ) : ℝ) ≤ 1 / 2 ^ 100 := by
  unfold etaOf
  rw [pG_D]
  have b' : ((pG bs I lg lI).bs : ℝ) ≤ 2 ^ 13 := by
    show (bs : ℝ) ≤ 2 ^ 13
    exact_mod_cast hb
  have i' : ((pG bs I lg lI).I : ℝ) ≤ 2 ^ 13 := by
    show (I : ℝ) ≤ 2 ^ 13
    exact_mod_cast hI
  have m' : ((pG bs I lg lI).I : ℝ) * ((pG bs I lg lI).bs : ℝ) ≤ 2 ^ 13 := by
    show (I : ℝ) * (bs : ℝ) ≤ 2 ^ 13
    exact_mod_cast hbI
  set b : ℝ := ((pG bs I lg lI).bs : ℝ)
  set i : ℝ := ((pG bs I lg lI).I : ℝ)
  have b0 : 0 ≤ b := by simp [b]
  have i0 : 0 ≤ i := by simp [i]
  have hu : 2 * (((1 / 2 ^ 126 : ℚ) : ℝ)) + 2 / (2 ^ 128 + 51) ≤ 1 / 2 ^ 124 := by norm_num
  have hu0 : 0 ≤ 2 * (((1 / 2 ^ 126 : ℚ) : ℝ)) + 2 / ((2 : ℝ) ^ 128 + 51) := by positivity
  set u : ℝ := 2 * (((1 / 2 ^ 126 : ℚ) : ℝ)) + 2 / (2 ^ 128 + 51)
  have h2 : (2 : ℝ) / (2 ^ 128 + 51) ≤ 1 / 2 ^ 124 := by norm_num
  have e1 : i * b * u ≤ 2 ^ 13 * (1 / 2 ^ 124) := mul_le_mul m' hu hu0 (by norm_num)
  have e2 : b * u ≤ 2 ^ 13 * (1 / 2 ^ 124) := mul_le_mul b' hu hu0 (by norm_num)
  have e3 : i * (2 / (2 ^ 128 + 51)) ≤ 2 ^ 13 * (1 / 2 ^ 124) :=
    mul_le_mul i' h2 (by positivity) (by norm_num)
  have : 2 * (i * (2 * (b * u) + 2 / (2 ^ 128 + 51))) + b * u =
      4 * (i * b * u) + 2 * (i * (2 / (2 ^ 128 + 51))) + b * u := by ring
  rw [this]
  norm_num at e1 e2 e3 ⊢
  linarith

theorem eta_nonneg (bs I lg lI : ℕ) : 0 ≤ etaOf (pG bs I lg lI) ((1 / 2 ^ 126 : ℚ) : ℝ) := by
  unfold etaOf
  rw [pG_D]
  have b0 : (0 : ℝ) ≤ ((pG bs I lg lI).bs : ℝ) := by simp
  have i0 : (0 : ℝ) ≤ ((pG bs I lg lI).I : ℝ) := by simp
  positivity

set_option exponentiation.threshold 2000 in
/-- **One chunk.** -/
theorem grp_chunk {s : Bool} {bs I lg lI : ℕ} {ρ : ℚ} {A : List QA} {E : List Ent} {c : List ℤ}
    (h : grpB s bs I lg lI ρ A E c = true) : Close dPc (avQ s A) c (1 / 10 ^ 10) := by
  simp only [grpB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hl, hI⟩, hIb⟩, hb13⟩, hI13⟩, hbI⟩, hlen⟩, hρ0⟩, hρ1⟩, hmod⟩, htail⟩, hE⟩, hent⟩,
    hmom⟩ := h
  have hp := pG_ok (bs := bs) (I := I) hl hI
  have hη := eta_le (lg := lg) (lI := lI) hb13 hI13 hbI
  have hη0 := eta_nonneg bs I lg lI
  have hDr : ((pG bs I lg lI).D : ℝ) = 2 ^ 128 + 51 := pG_D bs I lg lI
  set p := pG bs I lg lI with hpd
  have hbs : (p.bs : ℝ) ≤ 2 ^ 13 := by
    show (bs : ℝ) ≤ 2 ^ 13
    exact_mod_cast hb13
  have hIr : (p.I : ℝ) ≤ 2 ^ 13 := by
    show (I : ℝ) ≤ 2 ^ 13
    exact_mod_cast hI13
  have hbI' : (p.I : ℝ) * (p.bs : ℝ) ≤ 2 ^ 13 := by
    show (I : ℝ) * (bs : ℝ) ≤ 2 ^ 13
    exact_mod_cast hbI
  have b0 : (0 : ℝ) ≤ (p.bs : ℝ) := by simp
  have i0 : (0 : ℝ) ≤ (p.I : ℝ) := by simp
  have hu : 2 * (((1 / 2 ^ 126 : ℚ) : ℝ)) + 2 / (p.D : ℝ) ≤ 1 / 2 ^ 124 := by
    rw [hDr]; norm_num
  have hu0 : 0 ≤ 2 * (((1 / 2 ^ 126 : ℚ) : ℝ)) + 2 / (p.D : ℝ) := by rw [hDr]; positivity
  have hd2 : 2 / (p.D : ℝ) ≤ 1 / 2 ^ 124 := by rw [hDr]; norm_num
  have hb1 : (p.bs : ℝ) * (2 * (((1 / 2 ^ 126 : ℚ) : ℝ)) + 2 / (p.D : ℝ)) ≤ 1 / 2 ^ 111 := by
    have := mul_le_mul hbs hu hu0 (by norm_num)
    norm_num at this ⊢
    linarith
  have hI1 : (p.I : ℝ) * (2 * ((p.bs : ℝ) * (2 * (((1 / 2 ^ 126 : ℚ) : ℝ)) + 2 / (p.D : ℝ))) +
      2 / (p.D : ℝ)) ≤ 1 := by
    have a : 2 * ((p.bs : ℝ) * (2 * (((1 / 2 ^ 126 : ℚ) : ℝ)) + 2 / (p.D : ℝ))) + 2 / (p.D : ℝ) ≤
        1 / 2 ^ 100 := by
      norm_num at hb1 hd2 ⊢
      linarith
    have := mul_le_mul hIr a (by rw [hDr]; positivity) (by norm_num)
    refine this.trans ?_
    norm_num
  have hg : ((E.map fun e => |e.1|).sum) * (2 * p.D ^ 2) < p.B / 2 := by
    have e1 : p.D = 2 ^ 128 + 51 := by simp only [hpd, pG, rowD]; decide +kernel -- kcost: one power
    have e2 : p.B = 2 ^ 384 + 2 := by simp only [hpd, pG]; decide +kernel -- kcost: one power
    rw [e1, e2]
    have : (2 : ℤ) ^ 100 * (2 * (2 ^ 128 + 51) ^ 2) < (2 ^ 384 + 2) / 2 := by
      decide +kernel -- kcost: two powers
    refine lt_of_le_of_lt ?_ this
    exact mul_le_mul_of_nonneg_right hE (by positivity)
  obtain ⟨M, hM⟩ : ∃ M, M + 1 = p.I * p.bs := ⟨I * bs - 1, by
    show I * bs - 1 + 1 = I * bs
    omega⟩
  have hclose := group_ok s hp (dP := dPc) (by norm_num [dPc]) (Dz := 2 ^ 96) (by norm_num)
    (ε := 1 / 2 ^ 126) (δ := 1 / 2 ^ 96) hent
    (by linarith [show (1 / 2 ^ 111 : ℝ) ≤ 1 by norm_num]) hI1 (hη.trans (by norm_num)) hη0 hg hM
  have hm : grpList s ((dPc : ℕ) : ℤ) (2 ^ 96 * p.D ^ 2) (moments p E) = c := by
    have h2 := hmom
    unfold momG at h2
    simp only [forceI_eq] at h2
    have e1 : (2 : ℤ) ^ 96 * p.D ^ 2 = (2 : ℤ) ^ 80 * Int.ofNat (2 ^ 16 * rowD ^ 2) := by
      simp only [hpd, pG, rowD]
      decide +kernel -- kcost: two powers
    have e2 : ((dPc : ℕ) : ℤ) = (2 : ℤ) ^ 80 * Int.ofNat 1 := by
      simp only [dPc]
      decide +kernel -- kcost: one power
    rw [e1, e2, grpList_scale s ((2 : ℤ) ^ 80) (Int.ofNat 1) (Int.ofNat (2 ^ 16 * rowD ^ 2)) (by norm_num),
      ← grpListS_eq]
    exact beq_iff_eq.1 h2
  rw [hm] at hclose
  refine Close.mono hclose ?_
  have ha := atail_le hρ0 hρ1 M A fun a ha => (by simpa using List.all_eq_true.1 hmod a ha)
  have hMr : (M : ℝ) + 1 = (p.I : ℝ) * (p.bs : ℝ) := by exact_mod_cast hM
  have hMn : M + 1 = I * bs := hM
  have hMq : ((I * bs : ℕ) : ℚ) = (M : ℚ) + 1 := by
    rw [← hMn]
    push_cast
    rfl
  have ht' : (((A.map fun a => |a.1|).sum : ℚ) : ℝ) * (4 * ((ρ : ℝ) ^ (M + 1) * (1 - (ρ : ℝ))⁻¹ /
      ((M : ℝ) + 1))) ≤ 1 / 10 ^ 11 := by
    rw [hMn]
    rw [hMq] at htail
    have : (((A.map fun a => |a.1|).sum * (4 * (ρ ^ (I * bs) * (1 - ρ)⁻¹ / ((M : ℚ) + 1))) : ℚ) : ℝ) ≤
        ((1 / 10 ^ 11 : ℚ) : ℝ) := by exact_mod_cast htail
    push_cast at this ⊢
    exact this
  have hat : atail (A.map aR) M ≤ 1 / 10 ^ 11 := ha.trans ht'
  have hM13 : (M : ℝ) ≤ 2 ^ 13 := by
    have : (M : ℝ) + 1 ≤ 2 ^ 13 := by rw [hMr]; exact hbI'
    linarith
  have hAl : (A.length : ℝ) ≤ 1024 := by exact_mod_cast hlen
  have hEr : (((E.map fun e => |e.1|).sum : ℤ) : ℝ) / ((2 ^ 96 : ℤ) : ℝ) ≤ 16 := by
    have : (((E.map fun e => |e.1|).sum : ℤ) : ℝ) ≤ 2 ^ 100 := by exact_mod_cast hE
    have e : ((2 ^ 96 : ℤ) : ℝ) = 2 ^ 96 := by norm_num
    rw [e, div_le_iff₀ (by norm_num)]
    linarith
  have hE0 : (0 : ℝ) ≤ (((E.map fun e => |e.1|).sum : ℤ) : ℝ) / ((2 ^ 96 : ℤ) : ℝ) := by
    refine div_nonneg ?_ (by norm_num)
    exact_mod_cast List.sum_nonneg (by
      intro x hx
      obtain ⟨e, _, rfl⟩ := List.mem_map.1 hx
      exact abs_nonneg _)
  have c3 := mul_le_mul hEr hη hη0 (by norm_num)
  have c4 : (A.length : ℝ) * ((1 / 2 ^ 96 : ℚ) : ℝ) ≤ 1024 * (1 / 2 ^ 96) := by
    push_cast
    exact mul_le_mul_of_nonneg_right hAl (by norm_num)
  have hd : ((dPc : ℕ) : ℝ) = 2 ^ 80 := by norm_num [dPc]
  rw [hd]
  have c5 : 2 * (1 / 2 ^ 80 + 2 * ((A.length : ℝ) * ((1 / 2 ^ 96 : ℚ) : ℝ) +
      (((E.map fun e => |e.1|).sum : ℤ) : ℝ) / ((2 ^ 96 : ℤ) : ℝ) *
        etaOf p ((1 / 2 ^ 126 : ℚ) : ℝ))) ≤ 1 / 2 ^ 77 := by
    norm_num at c3 c4 ⊢
    linarith
  have c6 := mul_le_mul hM13 c5 (by
    have q1 : (0 : ℝ) ≤ (A.length : ℝ) * ((1 / 2 ^ 96 : ℚ) : ℝ) := by positivity
    have q2 := mul_nonneg hE0 hη0
    positivity) (by norm_num)
  have c7 : (2 : ℝ) ^ 13 * (1 / 2 ^ 77) ≤ 1 / 10 ^ 12 := by norm_num
  have c8 : (1 : ℝ) / 10 ^ 11 + 1 / 10 ^ 12 ≤ 1 / 10 ^ 10 := by norm_num
  linarith

end CatalanMeasure.GenD.Signed.RouteI.RowCert

namespace CatalanMeasure.GenD.Signed.RouteI.RowCert

open Real Set
open CatalanMeasure.GenD.Signed.RouteI.FreeRowCap0
open CatalanMeasure.GenD.Signed.RouteI.MarkedPilot
open CatalanMeasure.GenD.Signed.RouteI.MarkedSourceTail

/-! ### The digits of the direct moments as a literal -/

theorem sdig_add {B a : ℤ} (y : ℤ) (hB : 0 < B) (he : 2 ∣ B) (h1 : -(B / 2) ≤ a) (h2 : a < B / 2) :
    sdig B (a + B * y) = a := by
  obtain ⟨c, rfl⟩ := he
  have hc : 0 < c := by omega
  have e : 2 * c / 2 = c := by omega
  unfold sdig
  rw [e] at h1 h2 ⊢
  have : (a + 2 * c * y + c) % (2 * c) = a + c := by
    rw [show a + 2 * c * y + c = (a + c) + 2 * c * y by ring, Int.add_mul_emod_self_left]
    exact Int.emod_eq_of_lt (by omega) (by omega)
  rw [this]
  ring

theorem unpk_pk {B : ℤ} (hB : 0 < B) (he : 2 ∣ B) : ∀ d : List ℤ,
    (∀ a ∈ d, -(B / 2) ≤ a ∧ a < B / 2) → unpk B d.length (pk B d) = d
  | [], _ => rfl
  | a :: t, h => by
    have ih := unpk_pk hB he t fun x hx => h x (List.mem_cons_of_mem _ hx)
    obtain ⟨h1, h2⟩ := h a List.mem_cons_self
    have e1 : sdig B (a + B * pk B t) = a := sdig_add _ hB he h1 h2
    have e2 : (a + B * pk B t - a) / B = pk B t := by
      rw [show a + B * pk B t - a = B * pk B t by ring]
      exact Int.mul_ediv_cancel_left _ hB.ne'
    simp only [List.length_cons, pk, unpk, forceI_eq, e1, e2, ih]

/-- The digit literal of a run. -/
def digOK (B : ℤ) (lg : ℕ) (acc : ℤ) (d : List ℤ) : Bool :=
  d.all (fun a => decide (-(B / 2) ≤ a) && decide (a < B / 2)) && decide (d.length ≤ 2 ^ lg) &&
    forceI B fun b => packT lg b d == acc

theorem moments_lit {p : EPar} (h : p.OK) {E : List Ent} {acc : ℤ} {d : List ℤ} {lg : ℕ}
    (hr : run p E 0 = acc) (hl : d.length = p.I * p.bs) (hd : digOK p.B lg acc d = true) :
    moments p E = d := by
  simp only [digOK, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, forceI_eq,
    beq_iff_eq] at hd
  obtain ⟨⟨h1, h2⟩, h3⟩ := hd
  rw [packT_eq lg _ _ h2] at h3
  unfold moments
  rw [hr, ← h3, ← hl]
  exact unpk_pk h.B_pos h.B_even d h1

end CatalanMeasure.GenD.Signed.RouteI.RowCert

namespace CatalanMeasure.GenD.Signed.RouteI.RowCert

open Real Set
open CatalanMeasure.GenD.Signed.RouteI.FreeRowCap0
open CatalanMeasure.GenD.Signed.RouteI.MarkedPilot
open CatalanMeasure.GenD.Signed.RouteI.MarkedSourceTail
open CatalanMeasure.Signed.ChebSquare

/-! ### Chunks of the direct stream -/

/-- The checks of the direct stream on a prefix. -/
structure OwnPre (p : EPar) (q : LPar) (Dz : ℤ) (ε1 ε2 δ g : ℚ) (A : List Ev) (E : List Ent)
    (acc : ℤ) : Prop where
  own : ownB q.kP p.D Dz ε1 ε2 δ A E = true
  lg : ∀ e ∈ A, lgOK q e.1 = true
  nu : ∀ e ∈ A, nuOK q.kP g e = true
  rn : run p E 0 = acc

theorem ownB_append {kP : ℕ} {D Dz : ℤ} {ε1 ε2 δ : ℚ} : ∀ {A A' : List Ev} {E E' : List Ent},
    ownB kP D Dz ε1 ε2 δ A E = true → ownB kP D Dz ε1 ε2 δ A' E' = true →
    ownB kP D Dz ε1 ε2 δ (A ++ A') (E ++ E') = true
  | [], _, [], _, _, h => h
  | [], _, _ :: _, _, h, _ => by simp [ownB] at h
  | _ :: _, _, [], _, h, _ => by simp [ownB] at h
  | a :: A, A', e :: E, E', h, h' => by
    simp only [ownB, Bool.and_eq_true] at h
    simp only [List.cons_append, ownB, Bool.and_eq_true]
    exact ⟨h.1, ownB_append h.2 h'⟩

/-- The engine at forced radices. -/
def pO (D B C : ℤ) (bs I lg lI : ℕ) : EPar := ⟨D, bs, I, lg, lI, B, C⟩

/-- The checks of one chunk of the direct stream. -/
def ownCk (D B C : ℤ) (bs I lg lI : ℕ) (q : LPar) (Dz : ℤ) (ε1 ε2 δ g : ℚ) (A : List Ev)
    (E : List Ent) (a0 a1 : ℤ) : Bool :=
  forceI D fun d => forceI B fun b => forceI C fun c =>
    ownB q.kP d Dz ε1 ε2 δ A E && A.all (fun e => lgOK q e.1) && A.all (nuOK q.kP g) &&
      run ⟨d, bs, I, lg, lI, b, c⟩ E a0 == a1

theorem OwnPre.base (p : EPar) (q : LPar) (Dz : ℤ) (ε1 ε2 δ g : ℚ) (L : List Ev) :
    OwnPre p q Dz ε1 ε2 δ g (L.take 0) [] 0 where
  own := by simp [ownB]
  lg := by simp
  nu := by simp
  rn := rfl

theorem OwnPre.step {D B C : ℤ} {bs I lg lI : ℕ} {q : LPar} {Dz : ℤ} {ε1 ε2 δ g : ℚ}
    {L : List Ev} {a n : ℕ} {E E' : List Ent} {a0 a1 : ℤ}
    (h : OwnPre (pO D B C bs I lg lI) q Dz ε1 ε2 δ g (L.take a) E a0)
    (hc : ownCk D B C bs I lg lI q Dz ε1 ε2 δ g ((L.drop a).take n) E' a0 a1 = true) :
    OwnPre (pO D B C bs I lg lI) q Dz ε1 ε2 δ g (L.take (a + n)) (E ++ E') a1 := by
  simp only [ownCk, forceI_eq, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hc
  obtain ⟨⟨⟨c1, c2⟩, c3⟩, c4⟩ := hc
  rw [List.take_add]
  refine ⟨ownB_append h.own c1, fun e he => ?_, fun e he => ?_, ?_⟩
  · rcases List.mem_append.1 he with he | he
    · exact h.lg e he
    · exact c2 e he
  · rcases List.mem_append.1 he with he | he
    · exact h.nu e he
    · exact c3 e he
  · rw [run_append, h.rn]
    exact c4

/-- Chunks of an atom list by position. -/
theorem close_step (s : Bool) {dP : ℕ} {L : List QA} {a n : ℕ} {u v : List ℤ} {e1 e2 : ℝ}
    (h1 : Close dP (avQ s (L.take a)) u e1) (h2 : Close dP (avQ s ((L.drop a).take n)) v e2) :
    Close dP (avQ s (L.take (a + n))) (addZ u v) (e1 + e2) := by
  rw [List.take_add]
  exact Close.append s h1 h2

/-! ### The constant term of the direct list -/

theorem evS_Adir0 : ∀ G : List GS, evS (G.map segR) (Adir 0) =
    -Real.log 4 * (((G.map gW).sum : ℚ) : ℝ)
  | [] => by simp [evS]
  | g :: G => by
    have ih := evS_Adir0 G
    unfold evS at ih ⊢
    simp only [List.map_cons, List.sum_cons]
    rw [ih]
    simp only [Adir, segR, gW]
    push_cast
    ring

theorem c0_close {G : List GS} {dP : ℕ} (hd : 0 < dP) {c0 : ℤ} {δ : ℚ} {m : ℚ}
    (hm : (G.map gW).sum = m) (hm0 : 0 ≤ m)
    (h1 : -(2 * (6931471803 / 10 ^ 10)) * m - (c0 : ℚ) / dP ≤ δ)
    (h2 : (c0 : ℚ) / dP + 2 * (6931471808 / 10 ^ 10) * m ≤ δ) :
    |evS (G.map segR) (Adir 0) - (c0 : ℝ) / dP| ≤ δ := by
  rw [evS_Adir0, hm]
  have e4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have l1 := Real.log_two_gt_d9
  have l2 := Real.log_two_lt_d9
  have m0 : (0 : ℝ) ≤ m := by exact_mod_cast hm0
  have h1' : -(2 * ((6931471803 : ℝ) / 10 ^ 10)) * m - (c0 : ℝ) / dP ≤ δ := by
    have := (Rat.cast_le (K := ℝ)).2 h1
    push_cast at this
    exact this
  have h2' : (c0 : ℝ) / dP + 2 * ((6931471808 : ℝ) / 10 ^ 10) * m ≤ δ := by
    have := (Rat.cast_le (K := ℝ)).2 h2
    push_cast at this
    exact this
  rw [e4, abs_le]
  have a1 : ((6931471803 : ℝ) / 10 ^ 10) * m ≤ Real.log 2 * m :=
    mul_le_mul_of_nonneg_right (by norm_num at l1 ⊢; linarith) m0
  have a2 : Real.log 2 * m ≤ ((6931471808 : ℝ) / 10 ^ 10) * m :=
    mul_le_mul_of_nonneg_right (by norm_num at l2 ⊢; linarith) m0
  constructor <;> nlinarith

end CatalanMeasure.GenD.Signed.RouteI.RowCert

namespace CatalanMeasure.GenD.Signed.RouteI.RowCert

open Real Set
open CatalanMeasure.GenD.Signed.RouteI.FreeRowCap0
open CatalanMeasure.GenD.Signed.RouteI.MarkedPilot
open CatalanMeasure.GenD.Signed.RouteI.MarkedSourceTail

/-! ### Keys -/

def keyB (G : List GS) : Bool :=
  G.all fun g => decide (2000000000000 ≤ g.1) && decide (g.1 < g.2.1)

theorem keyB_spec {G : List GS} (h : keyB G = true) :
    ∀ g ∈ G, 2000000000000 ≤ g.1 ∧ g.1 < g.2.1 := by
  intro g hg
  have := List.all_eq_true.1 h g hg
  simpa using this

theorem keyB_real {G : List GS} (h : keyB G = true) :
    ∀ g ∈ G.map segR, 2 ≤ g.lo ∧ g.lo < g.hi := by
  intro g hg
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hg
  obtain ⟨h1, h2⟩ := keyB_spec h a ha
  have e1 : (2000000000000 : ℝ) ≤ (a.1 : ℝ) := by exact_mod_cast h1
  have e2 : (a.1 : ℝ) < (a.2.1 : ℝ) := by exact_mod_cast h2
  simp only [segR]
  constructor
  · rw [le_div_iff₀ (by norm_num)]
    norm_num
    linarith
  · exact div_lt_div_of_pos_right e2 (by norm_num)

theorem posB_real {G : List GS} (h : (G.all fun g => decide (0 ≤ g.2.2)) = true) :
    ∀ g ∈ G.map segR, 0 ≤ g.rho := by
  intro g hg
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hg
  have h1 : 0 ≤ a.2.2 := by simpa using List.all_eq_true.1 h a ha
  simp only [segR]
  exact_mod_cast h1

theorem keyE_real {E : List Ev} (h : (E.all fun e => decide (2000000000000 ≤ e.1)) = true) :
    ∀ e ∈ E.map atomR, 2 ≤ e.1 := by
  intro e he
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 he
  have h1 : 2000000000000 ≤ a.1 := by simpa using List.all_eq_true.1 h a ha
  have e1 : (2000000000000 : ℝ) ≤ (a.1 : ℝ) := by exact_mod_cast h1
  simp only [atomR]
  rw [le_div_iff₀ (by norm_num)]
  norm_num
  linarith

end CatalanMeasure.GenD.Signed.RouteI.RowCert

namespace CatalanMeasure.GenD.Signed.RouteI.RowCert

open Real Set
open CatalanMeasure.GenD.Signed.RouteI.FreeRowCap0
open CatalanMeasure.GenD.Signed.RouteI.MarkedPilot
open CatalanMeasure.GenD.Signed.RouteI.MarkedSourceTail
open CatalanMeasure.GenD.Signed.RouteI.OrdHf (Cov Blk sumEQ mc4 bot)

/-! ### Pieces with their ends -/

/-- A piece of the cover between the given ends. -/
def pieceEnd (C : Cov) (P : List (ℕ × ℚ)) (E K Bud' : ℚ) (n : ℚ × ℚ) (ns : List (ℚ × ℚ))
    (b a : ℚ) : Bool :=
  pieceChk C P E K Bud' 0 n ns && decide (bot n ns = b) && decide (n.1 = a)

theorem piece_range (C : Cov) {P : List (ℕ × ℚ)} {E K Bud' : ℚ} {n : ℚ × ℚ} {ns : List (ℚ × ℚ)}
    {b a : ℚ} (hs : 0 ≤ C.s) (hα : 0 ≤ C.α)
    (hB : ∀ B ∈ C.Bs, 0 < B.rho ∧ 0 ≤ B.M ∧ Real.log B.rho ≤ B.sg)
    (hK : 2 * C.s + mc4 C.Cl 0 * C.α ^ 2 ≤ K)
    (h : pieceEnd C P E K Bud' n ns b a = true) :
    ∀ x ∈ Icc ((b : ℚ) : ℝ) ((a : ℚ) : ℝ), C.Phi x ≤ ((0 : ℚ) : ℝ) := by
  simp only [pieceEnd, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have := piece_cover C hs hα hB hK h1
  rw [h2, h3] at this
  exact this

/-- The class checks one at a time. -/
theorem allChk_of {R : OrdHf.RadLit} {T : List CatalanMeasure.GenD.Signed.RouteI.CapSourceData.Tr}
    (h : ∀ i < 16, (R.chk T i && OrdHf.radChk (R.B i).rho (R.B i).sg (R.eta i) i) = true) :
    R.allChk T = true := by
  unfold OrdHf.RadLit.allChk
  rw [List.all_eq_true]
  intro i hi
  exact h i (List.mem_range.1 hi)

/-- Natural numbers below sixteen, one by one. -/
theorem lt16 {p : ℕ → Prop} (h0 : p 0) (h1 : p 1) (h2 : p 2) (h3 : p 3) (h4 : p 4) (h5 : p 5)
    (h6 : p 6) (h7 : p 7) (h8 : p 8) (h9 : p 9) (h10 : p 10) (h11 : p 11) (h12 : p 12) (h13 : p 13)
    (h14 : p 14) (h15 : p 15) : ∀ i < 16, p i := by
  intro i hi
  interval_cases i <;> assumption

end CatalanMeasure.GenD.Signed.RouteI.RowCert

namespace CatalanMeasure.GenD.Signed.RouteI.RowCert

open CatalanMeasure.GenD.Signed.RouteI.FreeRowCap0
open CatalanMeasure.GenD.Signed.Davis.CircleCheb

/-! ### The square by natural packs

A tree pack at the radix `2 ^ K` on signed integers makes the kernel build many literals with the same
low word. On natural numbers, after an offset, the same pack is linear. -/

def pairN (C : ℕ) : List ℕ → List ℕ
  | [] => []
  | [a] => [a]
  | a :: b :: t => (a + C * b) :: pairN C t

def packN : ℕ → ℕ → List ℕ → ℕ
  | 0, _, l => l.headD 0
  | n + 1, C, l => packN n (C * C) (pairN C l)

def offL (H : ℤ) (l : List ℤ) : List ℕ := l.map fun a => (a + H).toNat

theorem pairN_cast (C : ℕ) : ∀ l : List ℕ,
    (pairN C l).map (fun a : ℕ => (a : ℤ)) = pairUp (C : ℤ) (l.map fun a : ℕ => (a : ℤ))
  | [] => rfl
  | [_] => rfl
  | a :: b :: t => by
    simp only [pairN, List.map_cons, pairUp, pairN_cast C t]
    push_cast
    rfl

theorem packN_cast : ∀ (n C : ℕ) (l : List ℕ),
    ((packN n C l : ℕ) : ℤ) = packT n (C : ℤ) (l.map fun a : ℕ => (a : ℤ))
  | 0, C, [] => rfl
  | 0, C, a :: t => rfl
  | n + 1, C, l => by
    simp only [packN, packT]
    rw [packN_cast n, pairN_cast]
    push_cast
    rfl

theorem pk_off (B H : ℤ) : ∀ l : List ℤ,
    pk B (l.map fun a => a + H) = pk B l + H * pk B (List.replicate l.length 1)
  | [] => by simp [pk]
  | a :: t => by
    have ih := pk_off B H t
    simp only [List.map_cons, pk, List.length_cons, List.replicate_succ, ih]
    ring

theorem offL_cast (H : ℤ) : ∀ l : List ℤ, (∀ a ∈ l, 0 ≤ a + H) →
    (offL H l).map (fun a : ℕ => (a : ℤ)) = l.map fun a => a + H
  | [], _ => rfl
  | a :: t, h => by
    have ih := offL_cast H t fun x hx => h x (List.mem_cons_of_mem _ hx)
    have h0 := h a List.mem_cons_self
    unfold offL at ih ⊢
    simp only [List.map_cons, ih, Int.toNat_of_nonneg h0]

theorem pack_off {lg C : ℕ} {H : ℤ} {l : List ℤ} (hl : l.length ≤ 2 ^ lg)
    (h : ∀ a ∈ l, 0 ≤ a + H) :
    packT lg (C : ℤ) l = ((packN lg C (offL H l) : ℕ) : ℤ) -
      H * ((packN lg C (List.replicate l.length 1) : ℕ) : ℤ) := by
  have h1 : ((packN lg C (offL H l) : ℕ) : ℤ) = pk (C : ℤ) (l.map fun a => a + H) := by
    rw [packN_cast, offL_cast H l h, packT_eq lg _ _ (by simpa using hl)]
  have h2 : ((packN lg C (List.replicate l.length 1) : ℕ) : ℤ) =
      pk (C : ℤ) (List.replicate l.length 1) := by
    rw [packN_cast, List.map_replicate, packT_eq lg _ _ (by simpa using hl)]
    rfl
  rw [h1, h2, pk_off, packT_eq lg _ _ hl]
  ring

/-- The square from its packs. -/
theorem kron_packs {K m lgs lgq : ℕ} {d c : ℤ} {s q : List ℤ} {x1 x2 r y1 y2 u : ℕ}
    (h1 : s.length ≤ 2 ^ lgs) (h2 : q.length ≤ 2 ^ lgq)
    (h3 : s.all (fun a => decide (0 ≤ a + ((2 ^ (K - 1) : ℕ) : ℤ))) = true)
    (h4 : q.all (fun a => decide (0 ≤ a + ((2 ^ (K - 1) : ℕ) : ℤ))) = true)
    (p1 : packN lgs (2 ^ K) (offL ((2 ^ (K - 1) : ℕ) : ℤ) s) = x1)
    (p2 : packN lgs (2 ^ K) (offL ((2 ^ (K - 1) : ℕ) : ℤ) s.reverse) = x2)
    (p3 : packN lgs (2 ^ K) (List.replicate s.length 1) = r)
    (p4 : packN lgq (2 ^ K) (offL ((2 ^ (K - 1) : ℕ) : ℤ) q) = y1)
    (p5 : packN lgq (2 ^ K) (offL ((2 ^ (K - 1) : ℕ) : ℤ) q.reverse) = y2)
    (p6 : packN lgq (2 ^ K) (List.replicate q.length 1) = u)
    (hf : 2 * d * (pow2 (K * (2 * m)) * ((x1 : ℤ) - ((2 ^ (K - 1) : ℕ) : ℤ) * (r : ℤ)) +
        ((x2 : ℤ) - ((2 ^ (K - 1) : ℕ) : ℤ) * (r : ℤ))) +
      (pow2 (K * m) * ((y1 : ℤ) - ((2 ^ (K - 1) : ℕ) : ℤ) * (u : ℤ)) +
        ((y2 : ℤ) - ((2 ^ (K - 1) : ℕ) : ℤ) * (u : ℤ))) *
      (pow2 (K * m) * ((y1 : ℤ) - ((2 ^ (K - 1) : ℕ) : ℤ) * (u : ℤ)) +
        ((y2 : ℤ) - ((2 ^ (K - 1) : ℕ) : ℤ) * (u : ℤ))) =
      2 * (2 * d * c) * pow2 (K * (2 * m))) : kronEq K m lgs lgq d c s q = true := by
  simp only [List.all_eq_true, decide_eq_true_eq] at h3 h4
  have e1 := pack_off (C := 2 ^ K) (H := ((2 ^ (K - 1) : ℕ) : ℤ)) h1 h3
  have e2 := pack_off (C := 2 ^ K) (H := ((2 ^ (K - 1) : ℕ) : ℤ)) (l := s.reverse)
    (by simpa using h1) (fun a ha => h3 a (by simpa using ha))
  have e3 := pack_off (C := 2 ^ K) (H := ((2 ^ (K - 1) : ℕ) : ℤ)) h2 h4
  have e4 := pack_off (C := 2 ^ K) (H := ((2 ^ (K - 1) : ℕ) : ℤ)) (l := q.reverse)
    (by simpa using h2) (fun a ha => h4 a (by simpa using ha))
  rw [List.length_reverse] at e2 e4
  unfold kronEq liftK
  rw [decide_eq_true_eq]
  have p : pow2 K = (((2 ^ K : ℕ)) : ℤ) := rfl
  rw [p, e1, e2, e3, e4, p1, p2, p3, p4, p5, p6]
  exact hf

end CatalanMeasure.GenD.Signed.RouteI.RowCert

namespace CatalanMeasure.GenD.Signed.RouteI.RowCert

open CatalanMeasure.GenD.Signed.RouteI.FreeRowCap0
open CatalanMeasure.GenD.Signed.RouteI.MarkedPilot
open CatalanMeasure.GenD.Signed.RouteI.MarkedSourceTail
open CatalanMeasure.GenD.Signed.RouteI.CapFields

/-- A cell list against a chain and further segments, positive side. -/
theorem bind_two_pos {l : List YCell} {A E : List Ev} {G : List GS} {n : ℕ}
    (hl : ∀ F : ℝ → ℝ, evC l F = -evQ A F) (hs : sumW E = 0)
    (hc : cancelB n A (mergeA n E (segEv G)) = true) (F : ℝ → ℝ) :
    evC l F = evS ((chainQ 0 E ++ G).map segR) (fun y => 1 * F (1 * y)) := by
  have h1 := atoms_of_chain E hs (fun y => 1 * F (1 * y))
  rw [evE_atomR] at h1
  have h2 := evS_segEv G (fun y => 1 * F (1 * y))
  have e : evS ((chainQ 0 E ++ G).map segR) (fun y => 1 * F (1 * y)) =
      evS ((chainQ 0 E).map segR) (fun y => 1 * F (1 * y)) +
        evS (G.map segR) (fun y => 1 * F (1 * y)) := by
    unfold evS
    simp [List.map_append, List.sum_append]
  rw [hl, e, h1, h2, cancelB_eq hc, evQ_mergeA]
  simp only [one_mul]
  ring

/-- A cell list against a chain and further segments, negative side. -/
theorem bind_two_neg {l : List YCell} {A E : List Ev} {G : List GS} {n : ℕ}
    (hl : ∀ F : ℝ → ℝ, evC l F = -evQ A F) (hs : sumW E = 0)
    (hc : cancelB n A (mirror (mergeA n E (segEv G))) = true) (F : ℝ → ℝ) :
    evC l F = evS ((chainQ 0 E ++ G).map segR) (fun y => -1 * F (-1 * y)) := by
  have h1 := atoms_of_chain E hs (fun y => -1 * F (-1 * y))
  rw [evE_atomR] at h1
  have h2 := evS_segEv G (fun y => -1 * F (-1 * y))
  have e : evS ((chainQ 0 E ++ G).map segR) (fun y => -1 * F (-1 * y)) =
      evS ((chainQ 0 E).map segR) (fun y => -1 * F (-1 * y)) +
        evS (G.map segR) (fun y => -1 * F (-1 * y)) := by
    unfold evS
    simp [List.map_append, List.sum_append]
  have m : evQ (mergeA n E (segEv G)) (fun y => F (-y)) =
      evQ E (fun y => F (-y)) + evQ (segEv G) (fun y => F (-y)) := evQ_mergeA ..
  have c1 : evQ E (fun y => -1 * F (-1 * y)) = -evQ E (fun y => F (-y)) := by
    rw [← evQ_fun_neg]
    exact evQ_congr fun y => by simp
  have c2 : evQ (segEv G) (fun y => -1 * F (-1 * y)) = -evQ (segEv G) (fun y => F (-y)) := by
    rw [← evQ_fun_neg]
    exact evQ_congr fun y => by simp
  rw [hl, e, h1, h2, cancelB_eq hc, evQ_mirror, m, c1, c2]
  ring

end CatalanMeasure.GenD.Signed.RouteI.RowCert
