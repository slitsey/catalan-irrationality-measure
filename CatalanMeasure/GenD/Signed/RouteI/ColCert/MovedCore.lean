module

public import CatalanMeasure.GenD.Signed.RouteI.FreeColCert
public import CatalanMeasure.GenD.Signed.RouteI.ColCert.Pack
public import CatalanMeasure.GenD.Signed.RouteI.RowCert.Moved

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

/-!
# Moved column caps (G31): theory

kcost: no computation here; the per-unit check `finMv` is priced in the data modules.

For a finite trial list `ws` over `D`, `k(s) = 2 Σ ws_k T_{k+1}(s)/((k+1) D)` is turned into an integer
polynomial `b` in `s` (`bPoly`), then, on a unit `s = (M + d z)/10^12`, into the exact integer polynomial
`PkL M d b` in `z` by a Horner scheme.  The kernel computes that polynomial by Kronecker packing (one big
multiplication per Horner step, `pkP`), decodes its balanced digits with shifts (`decodeHs`), and rounds.
-/

namespace CatalanMeasure.GenD.Signed.RouteI.ColCert.Moved

open Real Set
open CatalanMeasure.GenD.Signed.RouteI.FreeColCert
open CatalanMeasure.GenD.Signed.RouteI.RowCertMoved (refT movSeq barrierTrialT_movSeq basis_add_two basis_one)
open CatalanMeasure.Signed.ChebSquare (basis)
open OAI.InternalCatalan
open intervalIntegral MeasureTheory
open CatalanMeasure.GenD.Signed.RouteI.CapFields CatalanMeasure.GenD.Signed.RouteI.CapSourceData
open CatalanMeasure.GenD.Signed.RouteI.FreeColCap0
open CatalanMeasure.GenD.Signed.RouteI.MarkedPilot (lnormOK)

/-! ### Constants as natural-number powers (the kernel accelerates `Nat.pow`, not `Int.pow`) -/

def lamN : ℕ := 1000000000000
def lamC : ℤ := 1000000000000
def lamP (K : ℕ) : ℤ := ((lamN ^ K : ℕ) : ℤ)
def P2 (n : ℕ) : ℤ := ((2  ^ n : ℕ) : ℤ)

theorem P2_eq (n : ℕ) : P2 n = 2 ^ n := by unfold P2; push_cast; rfl

theorem lamP_cast (K : ℕ) : ((lamP K : ℤ) : ℝ) = Lam ^ K := by
  unfold lamP lamN Lam; push_cast; norm_num

theorem lamC_cast : ((lamC : ℤ) : ℝ) = Lam := by unfold lamC Lam; norm_num

theorem lamP_succ (K : ℕ) : lamP (K + 1) = lamC * lamP K := by
  unfold lamP lamC lamN; push_cast; ring

theorem lamP_zero : lamP 0 = 1 := by simp [lamP]

theorem lamP_pos (K : ℕ) : 0 < lamP K := by unfold lamP lamN; positivity

theorem Lam_pos : (0 : ℝ) < Lam := by unfold Lam; norm_num

/-! ### Integer lists -/

def smulL (c : ℤ) (l : List ℤ) : List ℤ := l.map (fun a => c * a)

theorem evalZ_smulL (c : ℤ) : ∀ (l : List ℤ) (z : ℝ), evalZ (smulL c l) z = c * evalZ l z
  | [], z => by simp [smulL, evalZ]
  | a :: t, z => by
    have ih := evalZ_smulL c t z
    simp only [smulL, List.map_cons, evalZ] at ih ⊢
    rw [ih]; push_cast; ring

def mulLin (M d : ℤ) (r : List ℤ) : List ℤ := addL (smulL M r) (0 :: smulL d r)

theorem evalZ_mulLin (M d : ℤ) (r : List ℤ) (z : ℝ) :
    evalZ (mulLin M d r) z = ((M : ℝ) + d * z) * evalZ r z := by
  simp only [mulLin, evalZ_addL, evalZ_smulL, evalZ]; push_cast; ring

/-! ### The monomial form of `Σ w_k T_{k+1}(s)/(k+1)` -/

def chebStep (p : List ℤ × List ℤ) : List ℤ × List ℤ :=
  (p.2, addL (smulL 2 (0 :: p.2)) (smulL (-1) p.1))

def chebPair : ℕ → List ℤ × List ℤ
  | 0 => ([1], [0, 1])
  | n + 1 => chebStep (chebPair n)

theorem chebPair_spec (s : ℝ) : ∀ n : ℕ,
    evalZ (chebPair n).1 s = basis n s ∧ evalZ (chebPair n).2 s = basis (n + 1) s
  | 0 => by
    refine ⟨by simp [chebPair, evalZ], ?_⟩
    simp [chebPair, evalZ, basis_one]
  | n + 1 => by
    obtain ⟨h1, h2⟩ := chebPair_spec s n
    refine ⟨by simpa [chebPair, chebStep] using h2, ?_⟩
    simp only [chebPair, chebStep, evalZ_addL, evalZ_smulL, evalZ]
    rw [h1, h2, basis_add_two n]
    push_cast; ring

def lcmTo : ℕ → ℕ
  | 0 => 1
  | n + 1 => Nat.lcm (lcmTo n) (n + 1)

theorem dvd_lcmTo : ∀ (n j : ℕ), 1 ≤ j → j ≤ n → j ∣ lcmTo n
  | 0, j, h1, h2 => by omega
  | n + 1, j, h1, h2 => by
    by_cases hj : j = n + 1
    · subst hj; exact Nat.dvd_lcm_right _ _
    · exact (dvd_lcmTo n j h1 (by omega)).trans (Nat.dvd_lcm_left _ _)

theorem lcmTo_pos : ∀ n, 0 < lcmTo n
  | 0 => by simp [lcmTo]
  | n + 1 => by
    unfold lcmTo; exact Nat.lcm_pos (lcmTo_pos n) (by omega)

def bAcc (L : ℤ) : List ℤ → ℕ → List ℤ × List ℤ → List ℤ
  | [], _, _ => []
  | w :: ws, k, p => addL (smulL (w * (L / ((k + 1 : ℕ) : ℤ))) p.2) (bAcc L ws (k + 1) (chebStep p))

def bPoly (ws : List ℤ) : List ℤ := bAcc ((lcmTo ws.length : ℕ) : ℤ) ws 0 (chebPair 0)

theorem bAcc_spec (L : ℤ) (s : ℝ) : ∀ (ws : List ℤ) (k : ℕ),
    (∀ j, k < j → j ≤ k + ws.length → (j : ℤ) ∣ L) →
    evalZ (bAcc L ws k (chebPair k)) s = (L : ℝ) * refT ws k s
  | [], k, _ => by simp [bAcc, evalZ, refT]
  | w :: ws, k, hd => by
    have hl : (w :: ws).length = ws.length + 1 := rfl
    rw [hl] at hd
    obtain ⟨q, hq⟩ := hd (k + 1) (by omega) (by omega)
    have ih := bAcc_spec L s ws (k + 1) (fun j h1 h2 => hd j (by omega) (by omega))
    have h2 := (chebPair_spec s k).2
    simp only [bAcc, evalZ_addL, evalZ_smulL]
    rw [show chebStep (chebPair k) = chebPair (k + 1) from rfl, ih, h2]
    have hdiv : (L / ((k + 1 : ℕ) : ℤ)) = q := by
      rw [hq]; exact Int.mul_ediv_cancel_left _ (by positivity)
    rw [hdiv]
    simp only [refT]
    have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hLc : (L : ℝ) = ((k : ℝ) + 1) * q := by
      have := congrArg (Int.cast : ℤ → ℝ) hq
      push_cast at this
      exact this
    rw [hLc]
    push_cast
    field_simp

theorem bPoly_spec (ws : List ℤ) (s : ℝ) :
    evalZ (bPoly ws) s = ((lcmTo ws.length : ℕ) : ℝ) * refT ws 0 s := by
  have := bAcc_spec ((lcmTo ws.length : ℕ) : ℤ) s ws 0 (fun j h1 h2 => by
    rw [Int.natCast_dvd_natCast]; exact dvd_lcmTo _ j (by omega) (by omega))
  simpa [bPoly, chebPair] using this


/-! ### The shifted polynomial `Λ^K b((M + d z)/Λ)` and its Kronecker-packed Horner form -/

def PkL (M d : ℤ) : List ℤ → List ℤ
  | [] => []
  | c0 :: c' => addL [c0 * lamP c'.length] (mulLin M d (PkL M d c'))

theorem PkL_spec (M d : ℤ) (z : ℝ) : ∀ c : List ℤ,
    Lam * evalZ (PkL M d c) z = Lam ^ c.length * evalZ c (((M : ℝ) + d * z) / Lam)
  | [] => by simp [PkL, evalZ]
  | c0 :: c' => by
    have ih := PkL_spec M d z c'
    simp only [PkL, evalZ_addL, evalZ_mulLin, List.length_cons]
    have e1 : evalZ [c0 * lamP c'.length] z = ((c0 * lamP c'.length : ℤ) : ℝ) := by simp [evalZ]
    rw [e1]
    show _ = _ * ((c0 : ℝ) + (((M : ℝ) + d * z) / Lam) * evalZ c' (((M : ℝ) + d * z) / Lam))
    have hL : (Lam : ℝ) ≠ 0 := Lam_pos.ne'
    have hy : Lam * (((M : ℝ) + d * z) * evalZ (PkL M d c') z) =
        ((M : ℝ) + d * z) * (Lam ^ c'.length * evalZ c' (((M : ℝ) + d * z) / Lam)) := by
      rw [← ih]; ring
    have h3 : Lam ^ (c'.length + 1) * ((c0 : ℝ) + (((M : ℝ) + d * z) / Lam) * evalZ c' (((M : ℝ) + d * z) / Lam)) =
        c0 * Lam ^ (c'.length + 1) + ((M : ℝ) + d * z) * (Lam ^ c'.length * evalZ c' (((M : ℝ) + d * z) / Lam)) := by
      rw [pow_succ]; field_simp
    rw [h3]
    push_cast
    rw [lamP_cast]
    linear_combination hy

theorem len_addL : ∀ a b : List ℤ, (addL a b).length = max a.length b.length
  | [], b => by simp [addL]
  | a :: t, [] => by simp [addL]
  | a :: t, b :: r => by
    simp only [addL, List.length_cons, len_addL t r]; omega

theorem len_mulLin (M d : ℤ) (r : List ℤ) : (mulLin M d r).length = r.length + 1 := by
  simp [mulLin, len_addL, smulL]

theorem PkL_length (M d : ℤ) : ∀ c : List ℤ, (PkL M d c).length = c.length
  | [] => by simp [PkL]
  | c0 :: c' => by
    simp only [PkL, len_addL, len_mulLin, PkL_length M d c', List.length_cons, List.length_nil]
    omega

def pkStep (X c0 : ℤ) (r : ℤ × ℤ) : ℤ × ℤ := (c0 * r.2 + X * r.1, lamC * r.2)

def pkP (X : ℤ) : List ℤ → ℤ × ℤ
  | [] => (0, 1)
  | c0 :: c' => pkStep X c0 (pkP X c')

theorem pack_addL (W : ℕ) : ∀ a b : List ℤ,
    PackKr.pack W (addL a b) = PackKr.pack W a + PackKr.pack W b
  | [], b => by simp [addL, PackKr.pack]
  | a :: l, [] => by simp [addL, PackKr.pack]
  | a :: l, b :: r => by simp only [addL, PackKr.pack, pack_addL W l r]; ring

theorem pack_smulL (W : ℕ) (c : ℤ) : ∀ a : List ℤ, PackKr.pack W (smulL c a) = c * PackKr.pack W a
  | [] => by simp [smulL, PackKr.pack]
  | a :: t => by
    have ih := pack_smulL W c t
    simp only [smulL, List.map_cons, PackKr.pack] at ih ⊢
    rw [ih]; ring

theorem pack_mulLin (W : ℕ) (M d : ℤ) (r : List ℤ) :
    PackKr.pack W (mulLin M d r) = (M + d * 2 ^ W) * PackKr.pack W r := by
  simp only [mulLin, pack_addL, pack_smulL, PackKr.pack]; ring

theorem pkP_spec (W : ℕ) (M d : ℤ) : ∀ c : List ℤ,
    (pkP (M + d * P2 W) c).1 = PackKr.pack W (PkL M d c) ∧ (pkP (M + d * P2 W) c).2 = lamP c.length
  | [] => by simp [pkP, PkL, PackKr.pack, lamP_zero]
  | c0 :: c' => by
    obtain ⟨h1, h2⟩ := pkP_spec W M d c'
    constructor
    · simp only [pkP, pkStep, PkL, pack_addL, pack_mulLin, PackKr.pack, h1, h2]
      rw [P2_eq]; ring
    · simp only [pkP, pkStep, List.length_cons, h2, lamP_succ]

/-! ### Norm bounds -/

def nrm : List ℤ → ℤ
  | [] => 0
  | a :: t => |a| + nrm t

theorem nrm_nonneg : ∀ l : List ℤ, 0 ≤ nrm l
  | [] => by simp [nrm]
  | a :: t => by have := nrm_nonneg t; simp only [nrm]; positivity

theorem abs_le_nrm : ∀ (l : List ℤ) (a : ℤ), a ∈ l → |a| ≤ nrm l
  | [], a, h => by simp at h
  | b :: t, a, h => by
    have := nrm_nonneg t
    simp only [nrm]
    rcases List.mem_cons.1 h with rfl | h
    · linarith
    · have := abs_le_nrm t a h
      have := abs_nonneg b
      linarith

theorem nrm_addL : ∀ a b : List ℤ, nrm (addL a b) ≤ nrm a + nrm b
  | [], b => by simp [addL, nrm]
  | a :: l, [] => by simp [addL, nrm]
  | a :: l, b :: r => by
    have ih := nrm_addL l r
    simp only [addL, nrm]
    have := abs_add_le a b
    linarith

theorem nrm_smulL (c : ℤ) : ∀ l : List ℤ, nrm (smulL c l) = |c| * nrm l
  | [] => by simp [smulL, nrm]
  | a :: t => by
    have ih := nrm_smulL c t
    simp only [smulL, List.map_cons, nrm] at ih ⊢
    rw [ih, abs_mul]; ring

theorem nrm_mulLin (M d : ℤ) (r : List ℤ) : nrm (mulLin M d r) ≤ (|M| + |d|) * nrm r := by
  have h := nrm_addL (smulL M r) (0 :: smulL d r)
  simp only [mulLin, nrm, nrm_smulL, abs_zero, zero_add] at h ⊢
  linarith

theorem PkL_nrm (M d : ℤ) (hM : |M| + |d| ≤ lamC) : ∀ c : List ℤ,
    lamC * nrm (PkL M d c) ≤ lamP c.length * nrm c
  | [] => by simp [PkL, nrm]
  | c0 :: c' => by
    have ih := PkL_nrm M d hM c'
    have hP := lamP_pos c'.length
    have hr := nrm_nonneg (PkL M d c')
    have hc := nrm_nonneg c'
    have hmd : 0 ≤ |M| + |d| := by positivity
    have h1 := nrm_addL [c0 * lamP c'.length] (mulLin M d (PkL M d c'))
    have h2 := nrm_mulLin M d (PkL M d c')
    have h3 : nrm [c0 * lamP c'.length] = |c0| * lamP c'.length := by
      simp [nrm, abs_mul, abs_of_pos hP]
    have hC : (0 : ℤ) < lamC := by unfold lamC; norm_num
    have h4 : (|M| + |d|) * (lamC * nrm (PkL M d c')) ≤ lamC * (lamP c'.length * nrm c') := by
      calc (|M| + |d|) * (lamC * nrm (PkL M d c')) ≤ (|M| + |d|) * (lamP c'.length * nrm c') :=
            mul_le_mul_of_nonneg_left ih hmd
        _ ≤ lamC * (lamP c'.length * nrm c') := mul_le_mul_of_nonneg_right hM (by positivity)
    have e : nrm (PkL M d (c0 :: c')) ≤ |c0| * lamP c'.length + (|M| + |d|) * nrm (PkL M d c') := by
      simp only [PkL]; linarith
    have : lamC * nrm (PkL M d (c0 :: c')) ≤ lamC * (|c0| * lamP c'.length + (|M| + |d|) * nrm (PkL M d c')) :=
      mul_le_mul_of_nonneg_left e hC.le
    simp only [List.length_cons, nrm, lamP_succ]
    nlinarith

/-! ### Decoding the packed integer with shifts -/

def packN (W : ℕ) : List ℕ → ℕ
  | [] => 0
  | a :: t => a + (packN W t <<< W)

def digN (mask W : ℕ) : ℕ → ℕ → List ℕ × ℕ
  | 0, x => ([], x)
  | n + 1, x =>
    let r := digN mask W n (x >>> W)
    ((x &&& mask) :: r.1, r.2)

theorem digN_packN (W : ℕ) : ∀ u : List ℕ, (∀ a ∈ u, a < 2 ^ W) →
    digN (2 ^ W - 1) W u.length (packN W u) = (u, 0)
  | [], _ => by simp [digN, packN]
  | a :: t, h => by
    have ha : a < 2 ^ W := h a (by simp)
    have ih := digN_packN W t (fun b hb => h b (by simp [hb]))
    have hx : (packN W (a :: t)) = a + 2 ^ W * packN W t := by
      simp [packN, Nat.shiftLeft_eq, mul_comm]
    have hsr : packN W (a :: t) >>> W = packN W t := by
      rw [Nat.shiftRight_eq_div_pow, hx]
      rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt ha, zero_add]
    have hand : packN W (a :: t) &&& (2 ^ W - 1) = a := by
      rw [Nat.and_two_pow_sub_one_eq_mod, hx, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]
    simp only [List.length_cons, digN, hsr, hand, ih]

theorem packN_shift (W h : ℕ) : ∀ l : List ℤ, (∀ a ∈ l, -(h : ℤ) ≤ a) →
    ((packN W (l.map fun (a : ℤ) => (a + (h : ℤ)).toNat) : ℕ) : ℤ) =
      PackKr.pack W l + ((packN W (List.replicate l.length h) : ℕ) : ℤ)
  | [], _ => by simp [packN, PackKr.pack]
  | a :: t, hh => by
    have ih := packN_shift W h t (fun b hb => hh b (by simp [hb]))
    have ha : 0 ≤ a + h := by have := hh a (by simp); omega
    simp only [List.map_cons, List.length_cons, List.replicate_succ, packN, PackKr.pack,
      Nat.shiftLeft_eq]
    push_cast
    rw [ih, Int.toNat_of_nonneg ha]
    ring

/-- The balanced digits of the packed integer, as a list of integers. -/
def decodeHs (W : ℕ) (b : List ℤ) (M d : ℤ) : List ℤ :=
  let h : ℕ := 2 ^ (W - 1)
  let C : ℕ := packN W (List.replicate b.length h)
  let x : ℕ := ((pkP (M + d * P2 W) b).1 + (C : ℤ)).toNat
  (digN (2 ^ W - 1) W b.length x).1.map (fun (u : ℕ) => (Int.ofNat u) - (Int.ofNat h))

theorem map_sub_toNat : ∀ (l : List ℤ) (h : ℕ), (∀ a ∈ l, -(h : ℤ) ≤ a) →
    (l.map fun (a : ℤ) => (a + (h : ℤ)).toNat).map (fun (u : ℕ) => (Int.ofNat u) - (Int.ofNat h)) = l
  | [], _, _ => rfl
  | a :: t, h, hh => by
    have ha : 0 ≤ a + h := by have := hh a (by simp); omega
    simp only [List.map_cons, List.cons.injEq]
    refine ⟨?_, map_sub_toNat t h (fun b hb => hh b (by simp [hb]))⟩
    show ((a + h).toNat : ℤ) - h = a
    rw [Int.toNat_of_nonneg ha]; ring

theorem decodeHs_eq (W : ℕ) (hW : 1 ≤ W) (b : List ℤ) (M d : ℤ)
    (hr : ∀ a ∈ PkL M d b, |a| < 2 ^ (W - 1)) :
    decodeHs W b M d = PkL M d b := by
  set Hs := PkL M d b with hHs
  have hlen : Hs.length = b.length := PkL_length M d b
  have hh : ∀ a ∈ Hs, -((2 ^ (W - 1) : ℕ) : ℤ) ≤ a := by
    intro a ha; have := hr a ha; push_cast; have := neg_abs_le a; linarith
  have hV := (pkP_spec W M d b).1
  have hsh := packN_shift W (2 ^ (W - 1)) Hs hh
  rw [hlen] at hsh
  have hxeq : (pkP (M + d * P2 W) b).1 + ((packN W (List.replicate b.length (2 ^ (W - 1))) : ℕ) : ℤ)
        = ((packN W (Hs.map fun a => (a + ((2 ^ (W - 1) : ℕ) : ℤ)).toNat) : ℕ) : ℤ) := by
    rw [hsh, hV]
  have hlu : (Hs.map fun a => (a + ((2 ^ (W - 1) : ℕ) : ℤ)).toNat).length = b.length := by
    simp [hlen]
  have hu : ∀ a ∈ Hs.map (fun a => (a + ((2 ^ (W - 1) : ℕ) : ℤ)).toNat), a < 2 ^ W := by
    intro a ha
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ha
    have h1 := abs_lt.1 (hr x hx)
    have h2W : (2 : ℤ) ^ W = 2 * 2 ^ (W - 1) := by
      rw [← pow_succ']; congr 1; omega
    have : (((x + ((2 ^ (W - 1) : ℕ) : ℤ)).toNat : ℕ) : ℤ) < (2 : ℤ) ^ W := by
      rw [Int.toNat_of_nonneg (by push_cast; linarith [h1.1])]
      push_cast; linarith [h1.2]
    exact_mod_cast this
  show (digN (2 ^ W - 1) W b.length
      (((pkP (M + d * P2 W) b).1 + ((packN W (List.replicate b.length (2 ^ (W - 1))) : ℕ) : ℤ)).toNat)).1.map
      (fun (u : ℕ) => (Int.ofNat u) - (Int.ofNat (2 ^ (W - 1)))) = Hs
  rw [hxeq, Int.toNat_natCast, ← hlu, digN_packN W _ hu]
  exact map_sub_toNat Hs _ hh

/-! ### Rounding -/

def roundL (N : ℤ) (l : List ℤ) : List ℤ := l.map (fun h => P2 65 * h / N)

theorem round_err (N : ℤ) (hN : 0 < N) (z : ℝ) (hz : |z| ≤ 1) : ∀ l : List ℤ,
    |(2 : ℝ) ^ 65 * evalZ l z / N - evalZ (roundL N l) z| ≤ l.length
  | [] => by simp [roundL, evalZ]
  | a :: t => by
    have ih := round_err N hN z hz t
    have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    have r1 := rnd_abs (P2 65 * a) N hN.ne'
    have e : ((P2 65 * a : ℤ) : ℝ) / N = 2 ^ 65 * a / N := by rw [P2_eq]; push_cast; ring
    rw [e] at r1
    simp only [roundL, List.map_cons, evalZ, List.length_cons] at ih ⊢
    set E := evalZ t z
    set E' := evalZ (List.map (fun h => P2 65 * h / N) t) z
    set r : ℝ := ((P2 65 * a / N : ℤ) : ℝ)
    have key : (2 : ℝ) ^ 65 * ((a : ℝ) + z * E) / N - (r + z * E') =
        ((2 : ℝ) ^ 65 * a / N - r) + z * ((2 : ℝ) ^ 65 * E / N - E') := by
      field_simp; ring
    have hzz : |z * ((2 : ℝ) ^ 65 * E / N - E')| ≤ t.length := by
      rw [abs_mul]
      calc |z| * |(2 : ℝ) ^ 65 * E / N - E'| ≤ 1 * t.length := by gcongr
        _ = _ := one_mul _
    push_cast
    rw [key]
    calc _ ≤ |(2 : ℝ) ^ 65 * a / N - r| + |z * ((2 : ℝ) ^ 65 * E / N - E')| := abs_add_le _ _
      _ ≤ 1 + t.length := add_le_add r1 hzz
      _ = _ := by ring

/-! ### The polynomial bound for `2 T(ws, s)` on a unit -/

theorem k_poly (ws : List ℤ) (D : ℕ) (hD : 0 < D) (W : ℕ) (hW : 1 ≤ W) (b : List ℤ)
    (hb : b = bPoly ws) (hbl : b.length = ws.length + 1) (M d : ℤ) (hMd : |M| + |d| ≤ lamC)
    (hbd : lamP b.length * nrm b < lamC * P2 (W - 1)) (z : ℝ) (hz : |z| ≤ 1) :
    2 * barrierTrialT (movSeq ws D) (((M : ℝ) + d * z) / Lam) * 2 ^ 64 ≤
      evalZ (roundL ((lcmTo ws.length : ℤ) * D * lamP ws.length) (decodeHs W b M d)) z +
        ((roundL ((lcmTo ws.length : ℤ) * D * lamP ws.length) (decodeHs W b M d)).length : ℝ) := by
  have hC : (0 : ℤ) < lamC := by unfold lamC; norm_num
  have hr : ∀ a ∈ PkL M d b, |a| < 2 ^ (W - 1) := by
    intro a ha
    have h1 := abs_le_nrm (PkL M d b) a ha
    have h2 := PkL_nrm M d hMd b
    have h3 : lamC * nrm (PkL M d b) < lamC * P2 (W - 1) := lt_of_le_of_lt h2 hbd
    have h4 : nrm (PkL M d b) < P2 (W - 1) := lt_of_mul_lt_mul_left h3 hC.le
    rw [P2_eq] at h4
    exact lt_of_le_of_lt h1 h4
  rw [decodeHs_eq W hW b M d hr]
  have hLpos := lcmTo_pos ws.length
  have hNpos : 0 < (lcmTo ws.length : ℤ) * D * lamP ws.length := by
    have := lamP_pos ws.length
    positivity
  have herr := round_err _ hNpos z hz (PkL M d b)
  have hlenR : (roundL ((lcmTo ws.length : ℤ) * D * lamP ws.length) (PkL M d b)).length =
      (PkL M d b).length := by simp [roundL]
  have hspec := PkL_spec M d z b
  rw [hbl] at hspec
  have hEv : evalZ (PkL M d b) z = Lam ^ ws.length * evalZ b (((M : ℝ) + d * z) / Lam) := by
    have : Lam * evalZ (PkL M d b) z = Lam * (Lam ^ ws.length * evalZ b (((M : ℝ) + d * z) / Lam)) := by
      rw [hspec]; ring
    exact mul_left_cancel₀ Lam_pos.ne' this
  have hbv : evalZ b (((M : ℝ) + d * z) / Lam) = ((lcmTo ws.length : ℕ) : ℝ) * refT ws 0 (((M : ℝ) + d * z) / Lam) := by
    rw [hb]; exact bPoly_spec ws _
  rw [hbv] at hEv
  have hbT := barrierTrialT_movSeq ws D (((M : ℝ) + d * z) / Lam)
  rw [hbT]
  have hNr : (((lcmTo ws.length : ℤ) * D * lamP ws.length : ℤ) : ℝ) = (lcmTo ws.length : ℝ) * D * Lam ^ ws.length := by
    push_cast; rw [lamP_cast]
  rw [hNr, hEv] at herr
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have hLr : (0 : ℝ) < (lcmTo ws.length : ℝ) := by exact_mod_cast hLpos
  have hLamK : (0 : ℝ) < Lam ^ ws.length := pow_pos Lam_pos _
  have e : (2 : ℝ) ^ 65 * (Lam ^ ws.length * ((lcmTo ws.length : ℝ) * refT ws 0 (((M : ℝ) + d * z) / Lam))) /
      ((lcmTo ws.length : ℝ) * D * Lam ^ ws.length) =
      2 * (refT ws 0 (((M : ℝ) + d * z) / Lam) / D) * 2 ^ 64 := by
    field_simp
  rw [e] at herr
  have := (abs_le.1 herr).1
  rw [hlenR]
  have hl : ((PkL M d b).length : ℝ) = (PkL M d b).length := rfl
  linarith [(abs_le.1 herr).2]

/-! ### One unit: the bound of the anchor-0 field (copy of `unit_field`, without the cap) -/

structure UnitV' (u : UnitD) : Prop where
  ok : u.ok = true
  h0 : ∀ c ∈ u.c0, c.chk col0 = true
  h1 : ∀ c ∈ u.c1, c.chk col0 = true
  hr : ∀ c ∈ u.rw, c.chk row0 = true

theorem UnitV'_of_V {u : UnitD} (h : u.V) : UnitV' u := ⟨h.ok, h.h0, h.h1, h.hr⟩

set_option maxHeartbeats 800000 in
theorem unit_bound {u : UnitD} (hu : UnitV' u) {z : ℝ} (hz : |z| ≤ 1) (h0 : 0 < (u.M : ℝ) + u.δ * z)
    (h1 : (u.M : ℝ) + u.δ * z < Lam) :
    capSource.colField 0 (((u.M : ℝ) + u.δ * z) / Lam) ≤
      (evalZ u.Q z + (u.E : ℝ) + (LqI : ℝ)) / 2 ^ 64 := by
  obtain ⟨hok, hc0, hc1, hcr⟩ := hu
  simp only [UnitD.ok, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨t0, t1⟩, tr⟩, hn⟩, hn1⟩, hδ⟩, a0⟩, a1⟩, ar⟩, hct⟩, hns⟩, hl⟩, hr⟩ := hok
  have T0 := tile_up col0 2 Tc u.M u.δ Tc_pos hz u.c0 0 u.n0 t0 hc0 a0
  have T1 := tile_up col0 2 Tc u.M u.δ Tc_pos hz u.c1 u.n1 lenC t1 hc1 a1
  have T2 := ns_up 2 u.M u.δ hz u.near hns
  have T3 := tile_up row0 (-1) Trw (2 * u.M) (2 * u.δ) Trw_pos hz u.rw 0 lenR tr hcr ar
  have T4 := lQ_up u hl hz h0
  have T5 := rQ_up u hr hz h1
  set y : ℝ := ((u.M : ℝ) + u.δ * z) / Lam with hy
  have e3 : ((((2 * u.M : ℤ) : ℝ)) + ((2 * u.δ : ℕ) : ℝ) * z) / Lam = 2 * y := by
    rw [hy]; push_cast; ring
  rw [e3, seg_full row0_len] at T3
  rw [← near_pot u hct] at T2
  have hsp : col0 = seg col0 0 u.n0 ++ (seg col0 u.n0 u.n1 ++ seg col0 u.n1 lenC) := by
    rw [seg_append col0 hn hn1, seg_append col0 (Nat.zero_le _) (hn.trans hn1), seg_full col0_len]
  have hcol : potL (capSource.refCol 0) y = potL ((seg col0 0 u.n0).map (mkCell 1 Tc)) y +
      (potL ((seg col0 u.n0 u.n1).map (mkCell 1 Tc)) y +
        potL ((seg col0 u.n1 lenC).map (mkCell 1 Tc)) y) := by
    rw [refCol0]
    conv_lhs => rw [hsp]
    rw [List.map_append, List.map_append, potL_append, potL_append]
  have hrow : potL (capSource.refRow 0) (2 * y) = potL (row0.map (mkCell 1 Trw)) (2 * y) := by
    rw [refRow0]
  have hLc : ((Lq : ℚ) : ℝ) ≤ physL (capSource.refRow 0) (fun u => Real.log |u|) := L_cert
  have hLq : ((Lq : ℚ) : ℝ) = -6905432 / 10 ^ 7 := by norm_num [Lq]
  rw [hLq] at hLc
  have hLI : (6905432 : ℝ) * 2 ^ 64 / 10 ^ 7 ≤ LqI := by
    have := floor_up (6905432 * 2 ^ 64) (10 ^ 7) (by norm_num)
    unfold LqI
    norm_num at this ⊢
  have hQ : evalZ u.Q z = evalZ (sumQ 2 Tc u.M u.δ u.c0) z + (evalZ (sumQ 2 Tc u.M u.δ u.c1) z +
      (evalZ (nsQ 2 u.M u.δ u.near) z + (evalZ (sumQ (-1) Trw (2 * u.M) (2 * u.δ) u.rw) z +
        (evalZ u.lQ z + evalZ u.rQ z)))) := by
    simp only [UnitD.Q, evalZ_addL]
  have hE : (u.E : ℝ) = (sumE 2 Tc u.M u.δ u.c0 : ℝ) + ((sumE 2 Tc u.M u.δ u.c1 : ℝ) +
      ((nsE 2 u.M u.δ u.near : ℝ) + ((sumE (-1) Trw (2 * u.M) (2 * u.δ) u.rw : ℝ) +
        ((u.lE : ℝ) + u.rE)))) := by
    simp only [UnitD.E]; push_cast; ring
  rw [hQ, hE]
  unfold CapSource.colField
  rw [hcol, hrow]
  push_cast at T0 T1 T2 T3
  have ey : (((u.M : ℝ) + u.δ * z) / Lam) = y := rfl
  have e2 : (((2 : ℝ) * u.M + 2 * u.δ * z) / Lam) = 2 * y := by rw [hy]; ring
  linarith

/-- `s` in a unit's range as `(M + δ z)/Λ`. -/
theorem unit_z {u : UnitD} (hδ : 0 < u.δ) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (h1 : ((u.M - u.δ : ℤ) : ℝ) / 10 ^ 12 ≤ s) (h2 : s ≤ ((u.M + u.δ : ℤ) : ℝ) / 10 ^ 12) :
    ∃ z : ℝ, |z| ≤ 1 ∧ 0 < (u.M : ℝ) + u.δ * z ∧ (u.M : ℝ) + u.δ * z < Lam ∧
      s = ((u.M : ℝ) + u.δ * z) / Lam := by
  have hδr : (0 : ℝ) < u.δ := by exact_mod_cast hδ
  have hL : (Lam : ℝ) = 10 ^ 12 := by norm_num [Lam]
  push_cast at h1 h2
  rw [div_le_iff₀ (by norm_num)] at h1
  rw [le_div_iff₀ (by norm_num)] at h2
  refine ⟨(s * 10 ^ 12 - u.M) / u.δ, ?_, ?_, ?_, ?_⟩
  · rw [abs_le]
    constructor
    · rw [le_div_iff₀ hδr]; linarith
    · rw [div_le_iff₀ hδr]; linarith
  · have : (u.M : ℝ) + u.δ * ((s * 10 ^ 12 - u.M) / u.δ) = s * 10 ^ 12 := by field_simp; ring
    rw [this]; positivity
  · have : (u.M : ℝ) + u.δ * ((s * 10 ^ 12 - u.M) / u.δ) = s * 10 ^ 12 := by field_simp; ring
    rw [this, hL]; nlinarith
  · have : (u.M : ℝ) + u.δ * ((s * 10 ^ 12 - u.M) / u.δ) = s * 10 ^ 12 := by field_simp; ring
    rw [this, hL]; field_simp

theorem unit_delta_pos {u : UnitD} (hu : UnitV' u) : 0 < u.δ := by
  have hok := hu.ok
  simp only [UnitD.ok, Bool.and_eq_true, decide_eq_true_eq] at hok
  exact hok.1.1.1.1.1.1.1.2

/-! ### The data structure and the per-unit check -/

structure MvLits where
  ws : List ℤ
  D : ℕ
  W : ℕ
  b : List ℤ

def MvLits.N (m : MvLits) : ℤ := (lcmTo m.ws.length : ℤ) * m.D * lamP m.ws.length

def MvLits.R (m : MvLits) (u : UnitD) : List ℤ := roundL m.N (decodeHs m.W m.b u.M (u.δ : ℤ))

def MvLits.ok (m : MvLits) (u : UnitD) : Bool :=
  decide (0 < m.D) && decide (1 ≤ m.W) && decide (m.b.length = m.ws.length + 1) &&
    decide (|u.M| + |(u.δ : ℤ)| ≤ lamC) && decide (lamP m.b.length * nrm m.b < lamC * P2 (m.W - 1))

/-- `s ↦ (cn/cd) log (1 + (3/4) s)` through `log 4 + log(1 + 3 s / 4) = log ((4Λ + 3M + 3δz)/Λ)`. -/
def gTz (u : UnitD) : ℤ := 4 * lamC + 3 * u.M
def gD (u : UnitD) : ℤ := -(3 * (u.δ : ℤ))
def K4 (cn cd : ℤ) : ℤ := (cn * 13862943606 * P2 64) / (cd * 10000000000)
def gQ (cn cd : ℤ) (u : UnitD) : List ℤ := addL (logQ cn cd (gTz u) (gD u)) [-K4 cn cd]
def gE (cn cd : ℤ) (u : UnitD) : ℤ := logE cn cd (gTz u) (gD u)

theorem evalZ_single (a : ℤ) (z : ℝ) : evalZ [a] z = a := by simp [evalZ]

theorem g_up {u : UnitD} {cn cd : ℤ} (h : logOK cn cd (gTz u) (gD u) = true) {z : ℝ} (hz : |z| ≤ 1)
    (h0 : 0 < (u.M : ℝ) + u.δ * z) :
    (cn : ℝ) / cd * Real.log (1 + 3 / 4 * (((u.M : ℝ) + u.δ * z) / Lam)) ≤
      (evalZ (gQ cn cd u) z + (gE cn cd u : ℝ)) / 2 ^ 64 := by
  have hl := log_up h hz
  have hcn : 0 ≤ cn ∧ 0 < cd := by
    have h' := h
    simp only [logOK, Bool.and_eq_true, decide_eq_true_eq] at h'
    obtain ⟨⟨⟨⟨⟨hcn, hcd⟩, hT⟩, hd⟩, h45⟩, hln⟩ := h'
    exact ⟨hcn, hcd⟩
  obtain ⟨hcn, hcd⟩ := hcn
  have hcnr : (0 : ℝ) ≤ cn := by exact_mod_cast hcn
  have hcdr : (0 : ℝ) < cd := by exact_mod_cast hcd
  have hY : (((gTz u : ℤ) : ℝ) - ((gD u : ℤ) : ℝ) * z) / Lam = 4 * (1 + 3 / 4 * (((u.M : ℝ) + u.δ * z) / Lam)) := by
    unfold gTz gD lamC
    have : (Lam : ℝ) = 10 ^ 12 := by norm_num [Lam]
    rw [this]; push_cast; ring
  rw [hY] at hl
  have hpos : 0 < 1 + 3 / 4 * (((u.M : ℝ) + u.δ * z) / Lam) := by
    have : 0 < ((u.M : ℝ) + u.δ * z) / Lam := div_pos h0 Lam_pos
    positivity
  rw [Real.log_mul (by norm_num) hpos.ne'] at hl
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have h2 := Real.log_two_gt_d9
  have hK : ((K4 cn cd : ℤ) : ℝ) ≤ (cn : ℝ) * 13862943606 * 2 ^ 64 / (cd * 10000000000) := by
    have hb : (0 : ℤ) < cd * 10000000000 := by positivity
    have := Int.ediv_mul_le (cn * 13862943606 * P2 64) hb.ne'
    have hc : (((K4 cn cd) * (cd * 10000000000) : ℤ) : ℝ) ≤ ((cn * 13862943606 * P2 64 : ℤ) : ℝ) := by
      unfold K4; exact_mod_cast this
    push_cast at hc
    rw [P2_eq] at hc; push_cast at hc
    rw [le_div_iff₀ (by positivity)]
    linarith
  have hev : evalZ (gQ cn cd u) z = evalZ (logQ cn cd (gTz u) (gD u)) z - K4 cn cd := by
    unfold gQ; rw [evalZ_addL, evalZ_single]; push_cast; ring
  have hge : (gE cn cd u : ℝ) = (logE cn cd (gTz u) (gD u) : ℝ) := rfl
  rw [hev, hge]
  set c : ℝ := (cn : ℝ) / cd with hc
  have hc0 : 0 ≤ c := by positivity
  have hlog4 : (cn : ℝ) * 13862943606 * 2 ^ 64 / (cd * 10000000000) ≤ c * Real.log 4 * 2 ^ 64 := by
    rw [h4, hc]
    have : (cn : ℝ) * 13862943606 * 2 ^ 64 / (cd * 10000000000) =
        (cn : ℝ) / cd * (2 * 0.6931471803) * 2 ^ 64 := by
      field_simp; norm_num <;> ring
    rw [this]
    have : (cn : ℝ) / cd * (2 * 0.6931471803) ≤ (cn : ℝ) / cd * (2 * Real.log 2) := by gcongr
    nlinarith [this, (by positivity : (0 : ℝ) < 2 ^ 64)]
  have e : c * (Real.log 4 + Real.log (1 + 3 / 4 * (((u.M : ℝ) + u.δ * z) / Lam))) =
      c * Real.log 4 + c * Real.log (1 + 3 / 4 * (((u.M : ℝ) + u.δ * z) / Lam)) := by ring
  rw [e] at hl
  have hl' := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ 64)).1 hl
  rw [le_div_iff₀ (by positivity)]
  nlinarith [hl', hlog4, hK]

/-- The combined check of one unit, for three caps (numerators over `10^9`).  `Q` and `E` are computed
once. -/
def finAux (u : UnitD) (Q : List ℤ) (E : ℤ) (m0 m1 : MvLits) (c0 c1 c2 : ℤ) : Bool :=
  m0.ok u && m1.ok u &&
    decide ((supB (addL Q (m0.R u)) + E + LqI + ((m0.R u).length : ℤ)) * 1000000000 ≤ c0 * P2 64) &&
    logOK 1 25 (gTz u) (gD u) && logOK 51 500 (gTz u) (gD u) &&
    decide ((supB (addL (addL Q (m1.R u)) (gQ 1 25 u)) + E + LqI + ((m1.R u).length : ℤ) + gE 1 25 u) *
      1000000000 ≤ c1 * P2 64) &&
    decide ((supB (addL (addL Q (m1.R u)) (gQ 51 500 u)) + E + LqI + ((m1.R u).length : ℤ) + gE 51 500 u) *
      1000000000 ≤ c2 * P2 64)

def finMv (u : UnitD) (m0 m1 : MvLits) (c0 c1 c2 : ℤ) : Bool := finAux u u.Q u.E m0 m1 c0 c1 c2

/-- The three left-hand sides, for reading off the caps (not used in proofs). -/
def mvVals (u : UnitD) (m0 m1 : MvLits) : ℤ × ℤ × ℤ :=
  ((supB (addL u.Q (m0.R u)) + u.E + LqI + ((m0.R u).length : ℤ)),
   (supB (addL (addL u.Q (m1.R u)) (gQ 1 25 u)) + u.E + LqI + ((m1.R u).length : ℤ) + gE 1 25 u),
   (supB (addL (addL u.Q (m1.R u)) (gQ 51 500 u)) + u.E + LqI + ((m1.R u).length : ℤ) + gE 51 500 u))

theorem base_le (u : UnitD) (hu : UnitV' u) (m : MvLits) (hb : m.b = bPoly m.ws) (hm : m.ok u = true)
    {z : ℝ} (hz : |z| ≤ 1) (h0 : 0 < (u.M : ℝ) + u.δ * z) (h1 : (u.M : ℝ) + u.δ * z < Lam) :
    capSource.colField 0 (((u.M : ℝ) + u.δ * z) / Lam) +
        2 * barrierTrialT (movSeq m.ws m.D) (((u.M : ℝ) + u.δ * z) / Lam) ≤
      (evalZ (addL u.Q (m.R u)) z + (u.E : ℝ) + (LqI : ℝ) + ((m.R u).length : ℝ)) / 2 ^ 64 := by
  simp only [MvLits.ok, Bool.and_eq_true, decide_eq_true_eq] at hm
  obtain ⟨⟨⟨⟨hD, hW⟩, hbl⟩, hMd⟩, hbd⟩ := hm
  have h := unit_bound hu hz h0 h1
  have k := k_poly m.ws m.D hD m.W hW m.b hb hbl u.M (u.δ : ℤ) hMd hbd z hz
  have hc : (((u.δ : ℤ)) : ℝ) = (u.δ : ℝ) := by push_cast; rfl
  rw [hc] at k
  unfold MvLits.R MvLits.N
  rw [evalZ_addL]
  have e64 : (0 : ℝ) < 2 ^ 64 := by positivity
  rw [le_div_iff₀ e64] at h ⊢
  push_cast at k ⊢
  nlinarith [h, k]

theorem log_le (u : UnitD) (hu : UnitV' u) (m : MvLits) (hb : m.b = bPoly m.ws) (hm : m.ok u = true)
    {cn cd : ℤ} (hg : logOK cn cd (gTz u) (gD u) = true)
    {z : ℝ} (hz : |z| ≤ 1) (h0 : 0 < (u.M : ℝ) + u.δ * z) (h1 : (u.M : ℝ) + u.δ * z < Lam) :
    capSource.colField 0 (((u.M : ℝ) + u.δ * z) / Lam) +
        2 * barrierTrialT (movSeq m.ws m.D) (((u.M : ℝ) + u.δ * z) / Lam) +
        (cn : ℝ) / cd * Real.log (1 + 3 / 4 * (((u.M : ℝ) + u.δ * z) / Lam)) ≤
      (evalZ (addL (addL u.Q (m.R u)) (gQ cn cd u)) z + (u.E : ℝ) + (LqI : ℝ) + ((m.R u).length : ℝ) +
        (gE cn cd u : ℝ)) / 2 ^ 64 := by
  have h := base_le u hu m hb hm hz h0 h1
  have g := g_up hg hz h0
  rw [evalZ_addL, evalZ_addL]
  rw [evalZ_addL] at h
  linarith [h, g]


/-! ### The cap statement on a unit, and the cover -/

/-- The moved cap on the `s`-range of one unit: `F_C(s) + extra(s) ≤ cap`. -/
def MvCapU (extra : ℝ → ℝ) (cap : ℝ) (u : UnitD) : Prop :=
  ∀ s : ℝ, 0 < s → s < 1 → ((u.M - u.δ : ℤ) : ℝ) / 10 ^ 12 ≤ s → s ≤ ((u.M + u.δ : ℤ) : ℝ) / 10 ^ 12 →
    capSource.colField 0 s + extra s ≤ cap

theorem to_cap_real (X c : ℤ) (S : ℝ) (hS : S ≤ (X : ℝ)) (h : X * 1000000000 ≤ c * P2 64) :
    S / 2 ^ 64 ≤ (c : ℝ) / 10 ^ 9 := by
  have h' : ((X * 1000000000 : ℤ) : ℝ) ≤ ((c * P2 64 : ℤ) : ℝ) := by exact_mod_cast h
  rw [P2_eq] at h'
  push_cast at h'
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [hS]

theorem cap0_of_fin (u : UnitD) (hu : UnitV' u) (m0 m1 : MvLits) (hb0 : m0.b = bPoly m0.ws)
    {c0 c1 c2 : ℤ} (h : finMv u m0 m1 c0 c1 c2 = true) :
    MvCapU (fun s => 2 * barrierTrialT (movSeq m0.ws m0.D) s) ((c0 : ℝ) / 10 ^ 9) u := by
  simp only [finMv, finAux, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hm0, hm1⟩, hc0⟩, hg1⟩, hg2⟩, hc1⟩, hc2⟩ := h
  intro s hs0 hs1 h1 h2
  obtain ⟨z, hz, h0, h1', rfl⟩ := unit_z (unit_delta_pos hu) hs0 hs1 h1 h2
  have key := base_le u hu m0 hb0 hm0 hz h0 h1'
  have hs := evalZ_le_supB (addL u.Q (m0.R u)) z hz
  refine key.trans ?_
  have := to_cap_real (supB (addL u.Q (m0.R u)) + u.E + LqI + ((m0.R u).length : ℤ)) c0
    (evalZ (addL u.Q (m0.R u)) z + (u.E : ℝ) + (LqI : ℝ) + ((m0.R u).length : ℝ)) (by push_cast; linarith) hc0
  exact this

theorem cap1_of_fin (u : UnitD) (hu : UnitV' u) (m0 m1 : MvLits) (hb1 : m1.b = bPoly m1.ws)
    {c0 c1 c2 : ℤ} (h : finMv u m0 m1 c0 c1 c2 = true) :
    MvCapU (fun s => 2 * barrierTrialT (movSeq m1.ws m1.D) s + (1 / 25 : ℝ) * Real.log (1 + 3 / 4 * s))
      ((c1 : ℝ) / 10 ^ 9) u := by
  simp only [finMv, finAux, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hm0, hm1⟩, hc0⟩, hg1⟩, hg2⟩, hc1⟩, hc2⟩ := h
  intro s hs0 hs1 h1 h2
  obtain ⟨z, hz, h0, h1', rfl⟩ := unit_z (unit_delta_pos hu) hs0 hs1 h1 h2
  have key := log_le u hu m1 hb1 hm1 hg1 hz h0 h1'
  have e : (((1 : ℤ) : ℝ) / ((25 : ℤ) : ℝ)) = 1 / 25 := by norm_num
  rw [e] at key
  have hfin := to_cap_real (supB (addL (addL u.Q (m1.R u)) (gQ 1 25 u)) + u.E + LqI + ((m1.R u).length : ℤ) + gE 1 25 u) c1
    (evalZ (addL (addL u.Q (m1.R u)) (gQ 1 25 u)) z + (u.E : ℝ) + (LqI : ℝ) + ((m1.R u).length : ℝ) +
      (gE 1 25 u : ℝ)) (by
        have hs := evalZ_le_supB (addL (addL u.Q (m1.R u)) (gQ 1 25 u)) z hz
        push_cast; linarith) hc1
  beta_reduce
  linarith [key, hfin]

theorem cap2_of_fin (u : UnitD) (hu : UnitV' u) (m0 m1 : MvLits) (hb1 : m1.b = bPoly m1.ws)
    {c0 c1 c2 : ℤ} (h : finMv u m0 m1 c0 c1 c2 = true) :
    MvCapU (fun s => 2 * barrierTrialT (movSeq m1.ws m1.D) s + (51 / 500 : ℝ) * Real.log (1 + 3 / 4 * s))
      ((c2 : ℝ) / 10 ^ 9) u := by
  simp only [finMv, finAux, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hm0, hm1⟩, hc0⟩, hg1⟩, hg2⟩, hc1⟩, hc2⟩ := h
  intro s hs0 hs1 h1 h2
  obtain ⟨z, hz, h0, h1', rfl⟩ := unit_z (unit_delta_pos hu) hs0 hs1 h1 h2
  have key := log_le u hu m1 hb1 hm1 hg2 hz h0 h1'
  have e : (((51 : ℤ) : ℝ) / ((500 : ℤ) : ℝ)) = 51 / 500 := by norm_num
  rw [e] at key
  have hfin := to_cap_real (supB (addL (addL u.Q (m1.R u)) (gQ 51 500 u)) + u.E + LqI + ((m1.R u).length : ℤ) + gE 51 500 u) c2
    (evalZ (addL (addL u.Q (m1.R u)) (gQ 51 500 u)) z + (u.E : ℝ) + (LqI : ℝ) + ((m1.R u).length : ℝ) +
      (gE 51 500 u : ℝ)) (by
        have hs := evalZ_le_supB (addL (addL u.Q (m1.R u)) (gQ 51 500 u)) z hz
        push_cast; linarith) hc2
  beta_reduce
  linarith [key, hfin]

theorem chain_sound_gen (P : ℝ → Prop) : ∀ (us : List (ℤ × ℤ)) (a b : ℤ), chain a us b = true →
    (∀ u ∈ us, ∀ s : ℝ, (u.1 : ℝ) / 10 ^ 12 ≤ s → s ≤ (u.2 : ℝ) / 10 ^ 12 → P s) →
    ∀ s : ℝ, (a : ℝ) / 10 ^ 12 ≤ s → s ≤ (b : ℝ) / 10 ^ 12 → P s
  | [], a, b, h, _ => by simp [chain] at h
  | [u], a, b, h, hu => by
    simp only [chain, decide_eq_true_eq] at h
    intro s h1 h2
    exact hu u (by simp) s (by rw [h.1]; exact h1) (by rw [h.2]; exact h2)
  | u :: v :: us, a, b, h, hu => by
    simp only [chain, Bool.and_eq_true, decide_eq_true_eq] at h
    intro s h1 h2
    by_cases hs : s ≤ (u.2 : ℝ) / 10 ^ 12
    · exact hu u (by simp) s (by rw [h.1]; exact h1) hs
    · exact chain_sound_gen P (v :: us) u.2 b h.2
        (fun w hw => hu w (List.mem_cons_of_mem _ hw)) s (le_of_lt (not_le.1 hs)) h2

/-- **Generic consumer.** A left end unit, interior units chained from `a` to `b`, and a right end unit,
each carrying the moved cap, give the cap on all of `(0,1)`. -/
theorem moved_of_units (extra : ℝ → ℝ) (cap : ℝ) (uL uR : UnitD) (us : List UnitD) (a b : ℤ)
    (hL : MvCapU extra cap uL) (hR : MvCapU extra cap uR) (hU : ∀ u ∈ us, MvCapU extra cap u)
    (hch : chain a (us.map rng) b = true)
    (hLa : uL.M - uL.δ ≤ 0) (hLb : a ≤ uL.M + uL.δ)
    (hRa : uR.M - uR.δ ≤ b) (hRb : lamZ ≤ uR.M + uR.δ) :
    ∀ s ∈ Set.Ioo (0 : ℝ) 1, capSource.colField 0 s + extra s ≤ cap := by
  intro s hs
  by_cases h1 : s ≤ (a : ℝ) / 10 ^ 12
  · refine hL s hs.1 hs.2 ?_ ?_
    · have : ((uL.M - uL.δ : ℤ) : ℝ) ≤ 0 := by exact_mod_cast hLa
      exact (div_nonpos_of_nonpos_of_nonneg this (by norm_num)).trans hs.1.le
    · refine h1.trans ?_
      apply div_le_div_of_nonneg_right _ (by norm_num)
      exact_mod_cast hLb
  by_cases h2 : (b : ℝ) / 10 ^ 12 ≤ s
  · refine hR s hs.1 hs.2 ?_ ?_
    · refine le_trans ?_ h2
      apply div_le_div_of_nonneg_right _ (by norm_num)
      exact_mod_cast hRa
    · have : ((lamZ : ℤ) : ℝ) ≤ ((uR.M + uR.δ : ℤ) : ℝ) := by exact_mod_cast hRb
      have e : ((lamZ : ℤ) : ℝ) = 10 ^ 12 := by norm_num [lamZ]
      rw [e] at this
      rw [le_div_iff₀ (by norm_num)]
      linarith [hs.2]
  have := chain_sound_gen (fun s => 0 < s → s < 1 → capSource.colField 0 s + extra s ≤ cap)
    (us.map rng) a b hch (by
      intro v hv s h1 h2 h3 h4
      obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hv
      exact hU u hu s h3 h4 h1 h2) s (le_of_lt (not_le.1 h1)) (le_of_lt (not_le.1 h2))
  exact this hs.1 hs.2


end CatalanMeasure.GenD.Signed.RouteI.ColCert.Moved
