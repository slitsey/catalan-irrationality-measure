module

public import CatalanMeasure.GenD.Signed.RouteI.CompactInstance

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000

/-!
# Route I `CompactCells`: the δ̂ form of the compact caps on cells (GP Lemma 7.5, ledger G15/G16, check C7)

Generic. For a Chebyshev majorant `chebSum P D (affine lo u)` of a compact field (the polynomials
`posP`, `negP`, `nearP` with their tails `eps` of `CompactInstance`, which are the right hand sides of
`PosHf`, `NegHf`, `NearHf`), a cap `M = MN/MD` and a chord piece `α + β · 2u/(1 + u²)` of `δ̂/58`
(`δ̂` is affine in `t = 2x/(1 + x²)` on a segment of the chord table), one cell
`[u0/Q, u1/Q]` is certified by the integer polynomial

  `N(z) = (M − eps − α − chebSum P D y) (1 + u²) − 2 β u`,   `u = (u0 + u1 + (u1 − u0) z)/(2Q)`,

scaled by a positive integer, in the local variable `z ∈ [−1, 1]`: its coefficient list is computed
by the kernel (Chebyshev recurrence in the ring `ℤ[z]`, `cloc`), and the cell is accepted when
`N_0 ≥ Σ_{k ≥ 1} |N_k|` (centred form). Then `chebSum P D y + eps + dseg(u) ≤ M` on the cell
(`cell_le`). `ordCap_of_chain`, `nearCap_of_chain` turn a chain of accepted cells that covers
the window `[lo, umax]` into `OrdCap`, `NearCap` for the node correction `d` (`CapFields`).

Nothing about the chord table is assumed here: the pieces `dseg_i` enter through the hypothesis
`hd : d ≤ dseg_i` on each cell, supplied by the table (G13/G14/G16).

kcost: one cell is one `cloc` pass: `P.length` steps on lists of at most `P.length + 1` integers
(about 17k multiplications of numbers of at most about 8000 bits by numbers of at most 100 bits).
-/

namespace CatalanMeasure.GenD.Signed.RouteI.CompactCells

open CatalanMeasure.Signed.ChebSquare
open CatalanMeasure.GenD.Signed.RouteI.CompactCap
open CatalanMeasure.GenD.Signed.RouteI.CapFields
open CatalanMeasure.GenD.Signed.RouteI.CapFields.CapSource
open Set

noncomputable section

/-! ### Integer polynomials in `z` -/

/-- Horner evaluation of a list `a₀ + a₁ z + …`. -/
def evalP : List ℤ → ℝ → ℝ
  | [], _ => 0
  | a :: l, z => (a : ℝ) + z * evalP l z

def addP : List ℤ → List ℤ → List ℤ
  | [], b => b
  | a :: l, [] => a :: l
  | a :: l, b :: r => (a + b) :: addP l r

theorem evalP_addP : ∀ (a b : List ℤ) (z : ℝ), evalP (addP a b) z = evalP a z + evalP b z
  | [], b, z => by simp [addP, evalP]
  | a :: l, [], z => by simp [addP, evalP]
  | a :: l, b :: r, z => by
    simp only [addP, evalP, evalP_addP l r z]; push_cast; ring

def smulP (c : ℤ) (l : List ℤ) : List ℤ := l.map (c * ·)

theorem evalP_smulP (c : ℤ) : ∀ (l : List ℤ) (z : ℝ), evalP (smulP c l) z = (c : ℝ) * evalP l z
  | [], z => by simp [smulP, evalP]
  | a :: l, z => by
    have := evalP_smulP c l z
    simp only [smulP, List.map_cons, evalP] at this ⊢
    push_cast; rw [this]; ring

/-- `(A + B z) · l`. -/
def linP (A B : ℤ) (l : List ℤ) : List ℤ := addP (smulP A l) (0 :: smulP B l)

theorem evalP_linP (A B : ℤ) (l : List ℤ) (z : ℝ) :
    evalP (linP A B l) z = ((A : ℝ) + B * z) * evalP l z := by
  simp only [linP, evalP_addP, evalP_smulP, evalP]
  push_cast; ring

def mulP : List ℤ → List ℤ → List ℤ
  | [], _ => []
  | a :: l, b => addP (smulP a b) (0 :: mulP l b)

theorem evalP_mulP : ∀ (a b : List ℤ) (z : ℝ), evalP (mulP a b) z = evalP a z * evalP b z
  | [], b, z => by simp [mulP, evalP]
  | a :: l, b, z => by
    simp only [mulP, evalP_addP, evalP_smulP, evalP, evalP_mulP l b z]
    push_cast; ring

theorem abs_evalP_le : ∀ (l : List ℤ) {z : ℝ}, |z| ≤ 1 → |evalP l z| ≤ (l1 l : ℝ)
  | [], z, _ => by simp [evalP, l1]
  | a :: l, z, hz => by
    have ih := abs_evalP_le l hz
    simp only [evalP, l1]
    push_cast
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul]
    have h0 : 0 ≤ |evalP l z| := abs_nonneg _
    have : |z| * |evalP l z| ≤ 1 * (l1 l : ℝ) := mul_le_mul hz ih h0 zero_le_one
    have : |z| * |evalP l z| ≤ (l1 l : ℝ) := by linarith
    linarith

theorem evalP_ge (a : ℤ) (l : List ℤ) {z : ℝ} (hz : |z| ≤ 1) :
    (a : ℝ) - (l1 l : ℝ) ≤ evalP (a :: l) z := by
  have h := abs_evalP_le l hz
  have h1 : |z * evalP l z| ≤ (l1 l : ℝ) := by
    rw [abs_mul]
    have h0 : 0 ≤ |evalP l z| := abs_nonneg _
    have : |z| * |evalP l z| ≤ 1 * (l1 l : ℝ) := mul_le_mul hz h h0 zero_le_one
    linarith
  have := (abs_le.mp h1).1
  simp only [evalP]
  linarith

/-! ### Chebyshev recurrence in `ℤ[z]` -/

theorem basis_rec (n : ℕ) (y : ℝ) : basis (n + 2) y = 2 * y * basis (n + 1) y - basis n y := by
  unfold basis
  have h := Polynomial.Chebyshev.T_add_two ℝ (n : ℤ)
  push_cast
  rw [h]
  simp

theorem basis_one_y (y : ℝ) : basis 1 y = y := by
  unfold basis
  simp

/-- `S_{k+2} = 2 (A + B z) S_{k+1} − E² S_k`, so that `S_k = E^k T_k((A + B z)/E)`. -/
def sNext (A B E : ℤ) (s0 s1 : List ℤ) : List ℤ :=
  addP (smulP 2 (linP A B s1)) (smulP (-(E ^ 2)) s0)

/-- Horner accumulation `acc ↦ E acc + p_k S_k` along the Chebyshev list. -/
def cloc (A B E : ℤ) : List ℤ → List ℤ → List ℤ → List ℤ → List ℤ
  | [], _, _, acc => acc
  | p :: ps, s0, s1, acc => cloc A B E ps s1 (sNext A B E s0 s1) (addP (smulP E acc) (smulP p s0))

theorem eval_cloc (A B E : ℤ) {z y : ℝ} (hy : (E : ℝ) * y = (A : ℝ) + B * z) :
    ∀ (ps : List ℤ) (k : ℕ) (s0 s1 acc : List ℤ),
      evalP s0 z = (E : ℝ) ^ k * basis k y → evalP s1 z = (E : ℝ) ^ (k + 1) * basis (k + 1) y →
      (E : ℝ) * evalP (cloc A B E ps s0 s1 acc) z =
        (E : ℝ) ^ (ps.length + 1) * evalP acc z + (E : ℝ) ^ (k + ps.length) * rawSum ps k y
  | [], k, s0, s1, acc, _, _ => by simp [cloc, rawSum]
  | p :: ps, k, s0, s1, acc, h0, h1 => by
    have hn : evalP (sNext A B E s0 s1) z = (E : ℝ) ^ (k + 1 + 1) * basis (k + 1 + 1) y := by
      simp only [sNext, evalP_addP, evalP_smulP, evalP_linP, h0, h1]
      rw [basis_rec]
      push_cast
      have : (A : ℝ) + B * z = E * y := hy.symm
      rw [this]
      ring
    have ih := eval_cloc A B E hy ps (k + 1) s1 (sNext A B E s0 s1)
      (addP (smulP E acc) (smulP p s0)) h1 hn
    simp only [cloc]
    rw [ih]
    simp only [evalP_addP, evalP_smulP, h0, List.length_cons, rawSum_cons]
    ring

/-- One accepted cell: `u ∈ [u0/Q, u1/Q]`, chord piece `α = a/2^60`, `β = b/2^60`. -/
structure CellData where
  u0 : ℤ
  u1 : ℤ
  a : ℤ
  b : ℤ

/-- `E`, `A`, `B` of the cell: `y = affine lo u = (A + B z)/E`, `u = (u0 + u1 + (u1 - u0) z)/(2Q)`,
`lo = loN/loD`. -/
def cE (loN loD Q : ℤ) : ℤ := 2 * Q * (loD - loN)
def cA (loN loD Q : ℤ) (c : CellData) : ℤ := 2 * loD * (c.u0 + c.u1) - 2 * Q * (loN + loD)
def cB (loD : ℤ) (c : CellData) : ℤ := 2 * loD * (c.u1 - c.u0)

/-- `E · Σ p_k T_k(y) = E^len · cLz`-scaled: the Chebyshev sum in `z`. -/
def cLz (P : List ℤ) (loN loD Q : ℤ) (c : CellData) : List ℤ :=
  cloc (cA loN loD Q c) (cB loD c) (cE loN loD Q) P [1] [cA loN loD Q c, cB loD c] []

/-- Common denominator of `M - eps - α` and the numerator `m`. -/
def cDen (MD eD : ℤ) : ℤ := MD * eD * 2 ^ 60
def cm (MN MD eN eD : ℤ) (c : CellData) : ℤ := MN * eD * 2 ^ 60 - eN * MD * 2 ^ 60 - c.a * MD * eD

def cG (P : List ℤ) (D : ℕ) (loN loD MN MD eN eD Q : ℤ) (c : CellData) : List ℤ :=
  addP [cm MN MD eN eD c * D * (cE loN loD Q) ^ P.length]
    (smulP (-(cDen MD eD * cE loN loD Q)) (cLz P loN loD Q c))

/-- The scaled integer polynomial `N(z)` of one cell. -/
def cellN (P : List ℤ) (D : ℕ) (loN loD MN MD eN eD Q : ℤ) (c : CellData) : List ℤ :=
  addP (smulP (2 ^ 60) (mulP (cG P D loN loD MN MD eN eD Q c)
      [(2 * Q) ^ 2 + (c.u0 + c.u1) ^ 2, 2 * (c.u0 + c.u1) * (c.u1 - c.u0), (c.u1 - c.u0) ^ 2]))
    (smulP (-(2 * c.b * (2 * Q) * (cDen MD eD * D * (cE loN loD Q) ^ P.length)))
      [c.u0 + c.u1, c.u1 - c.u0])

def cellChk (P : List ℤ) (D : ℕ) (loN loD MN MD eN eD Q : ℤ) (c : CellData) : Bool :=
  decide (c.u0 < c.u1) &&
    decide (l1 (cellN P D loN loD MN MD eN eD Q c).tail ≤ (cellN P D loN loD MN MD eN eD Q c).headD 0)

/-! ### One cell -/

theorem cellN_eval {P : List ℤ} {D : ℕ} {loN loD MN MD eN eD Q : ℤ} (hD : 0 < D) (hQ : 0 < Q)
    (hloD : 0 < loD) (hlo : loN < loD) (hMD : 0 < MD) (heD : 0 < eD) (c : CellData) {z u : ℝ}
    (hu : ((2 * Q : ℤ) : ℝ) * u = ((c.u0 + c.u1 : ℤ) : ℝ) + ((c.u1 - c.u0 : ℤ) : ℝ) * z) :
    evalP (cellN P D loN loD MN MD eN eD Q c) z =
      (((cDen MD eD : ℤ) : ℝ) * (D : ℝ) * (((cE loN loD Q) ^ P.length : ℤ) : ℝ) *
          ((2 * Q : ℤ) : ℝ) ^ 2 * 2 ^ 60) *
        (((MN : ℝ) / MD - (eN : ℝ) / eD - (c.a : ℝ) / 2 ^ 60 - chebSum P D (affine ((loN : ℝ) / loD) u)) *
            (1 + u ^ 2) - 2 * ((c.b : ℝ) / 2 ^ 60) * u) := by
  have hQ' : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hloD' : (0 : ℝ) < loD := by exact_mod_cast hloD
  have hlo' : (loN : ℝ) < loD := by exact_mod_cast hlo
  have hMD' : (0 : ℝ) < MD := by exact_mod_cast hMD
  have heD' : (0 : ℝ) < eD := by exact_mod_cast heD
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have hE' : (0 : ℝ) < (cE loN loD Q : ℤ) := by
    unfold cE; push_cast; have : (0 : ℝ) < (loD : ℝ) - loN := by linarith
    positivity
  set y : ℝ := affine ((loN : ℝ) / loD) u with hyd
  have hy : ((cE loN loD Q : ℤ) : ℝ) * y = ((cA loN loD Q c : ℤ) : ℝ) + ((cB loD c : ℤ) : ℝ) * z := by
    have hδ : (0 : ℝ) < (loD : ℝ) - loN := by linarith
    have key : y = (2 * (loD : ℝ) * u - loN - loD) / ((loD : ℝ) - loN) := by
      rw [hyd]; unfold affine
      field_simp
      ring
    rw [key]
    unfold cE cA cB
    push_cast at hu ⊢
    have e : (2 * (Q : ℝ) * ((loD : ℝ) - loN)) * ((2 * (loD : ℝ) * u - loN - loD) / ((loD : ℝ) - loN)) =
        2 * (Q : ℝ) * (2 * (loD : ℝ) * u - loN - loD) := by
      field_simp
    rw [e]
    linear_combination (2 * (loD : ℝ)) * hu
  have hL := eval_cloc (cA loN loD Q c) (cB loD c) (cE loN loD Q) hy
    P 0 [1] [cA loN loD Q c, cB loD c]  []
    (by simp [evalP]) (by
      simp only [evalP, zero_add, pow_one, basis_one_y]
      linear_combination (-1 : ℝ) * hy)
  have hLz : ((cE loN loD Q : ℤ) : ℝ) * evalP (cLz P loN loD Q c) z =
      ((cE loN loD Q : ℤ) : ℝ) ^ P.length * rawSum P 0 y := by
    have := hL
    simp only [evalP, zero_add, mul_zero, add_zero] at this
    unfold cLz
    simpa using this
  have hcs : chebSum P D y = rawSum P 0 y / D := rfl
  have hq : evalP [(2 * Q) ^ 2 + (c.u0 + c.u1) ^ 2, 2 * (c.u0 + c.u1) * (c.u1 - c.u0), (c.u1 - c.u0) ^ 2] z =
      ((2 * Q : ℤ) : ℝ) ^ 2 * (1 + u ^ 2) := by
    simp only [evalP]
    push_cast at hu ⊢
    have : (c.u0 + c.u1 : ℝ) + (c.u1 - c.u0) * z = 2 * Q * u := hu.symm
    calc _ = (2 * (Q : ℝ)) ^ 2 + ((c.u0 + c.u1 : ℝ) + (c.u1 - c.u0) * z) ^ 2 := by ring
      _ = _ := by rw [this]; ring
  have hl : evalP [c.u0 + c.u1, c.u1 - c.u0] z = ((2 * Q : ℤ) : ℝ) * u := by
    simp only [evalP]
    push_cast at hu ⊢
    linear_combination (-1 : ℝ) * hu
  have hG : evalP (cG P D loN loD MN MD eN eD Q c) z =
      ((cm MN MD eN eD c : ℤ) : ℝ) * D * ((cE loN loD Q : ℤ) : ℝ) ^ P.length -
        ((cDen MD eD : ℤ) : ℝ) * (((cE loN loD Q : ℤ) : ℝ) * evalP (cLz P loN loD Q c) z) := by
    unfold cG
    simp only [evalP_addP, evalP_smulP, evalP]
    push_cast
    ring
  unfold cellN
  rw [evalP_addP, evalP_smulP, evalP_mulP, evalP_smulP, hq, hl, hG, hLz, hcs]
  unfold cDen cm
  push_cast
  field_simp
  ring

/-- One accepted cell bounds the majorant plus the chord piece by the cap. -/
theorem cell_le {P : List ℤ} {D : ℕ} {loN loD MN MD eN eD Q : ℤ} (hD : 0 < D) (hQ : 0 < Q)
    (hloD : 0 < loD) (hlo : loN < loD) (hMD : 0 < MD) (heD : 0 < eD) {c : CellData}
    (h : cellChk P D loN loD MN MD eN eD Q c = true) {u : ℝ}
    (hu0 : (c.u0 : ℝ) / Q ≤ u) (hu1 : u ≤ (c.u1 : ℝ) / Q) :
    chebSum P D (affine ((loN : ℝ) / loD) u) + (eN : ℝ) / eD +
        ((c.a : ℝ) / 2 ^ 60 + ((c.b : ℝ) / 2 ^ 60) * (2 * u / (1 + u ^ 2))) ≤ (MN : ℝ) / MD := by
  simp only [cellChk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hlt, hchk⟩ := h
  have hQ' : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hlt' : (c.u0 : ℝ) < c.u1 := by exact_mod_cast hlt
  set hN : ℝ := (c.u1 : ℝ) - c.u0 with hhN
  have hNpos : 0 < hN := by rw [hhN]; linarith
  set z : ℝ := (2 * Q * u - (c.u0 + c.u1)) / hN with hz
  have hu : ((2 * Q : ℤ) : ℝ) * u = ((c.u0 + c.u1 : ℤ) : ℝ) + ((c.u1 - c.u0 : ℤ) : ℝ) * z := by
    push_cast
    rw [hz, ← hhN]
    field_simp
    ring
  have hzb : |z| ≤ 1 := by
    rw [abs_le, hz]
    constructor
    · rw [le_div_iff₀ hNpos, hhN]
      have : (c.u0 : ℝ) ≤ Q * u := by rw [div_le_iff₀ hQ'] at hu0; linarith
      nlinarith
    · rw [div_le_iff₀ hNpos, hhN]
      have : Q * u ≤ (c.u1 : ℝ) := by rw [le_div_iff₀ hQ'] at hu1; linarith
      nlinarith
  have hev := cellN_eval (P := P) (MN := MN) (eN := eN) hD hQ hloD hlo hMD heD c hu
  have hNn : 0 ≤ evalP (cellN P D loN loD MN MD eN eD Q c) z := by
    generalize cellN P D loN loD MN MD eN eD Q c = L at hchk ⊢
    cases L with
    | nil => simp [evalP]
    | cons a t =>
      have hg := evalP_ge a t hzb
      have : (l1 t : ℝ) ≤ (a : ℝ) := by exact_mod_cast hchk
      linarith
  rw [hev] at hNn
  have hW : 0 < ((cDen MD eD : ℤ) : ℝ) * (D : ℝ) * (((cE loN loD Q) ^ P.length : ℤ) : ℝ) *
      ((2 * Q : ℤ) : ℝ) ^ 2 * 2 ^ 60 := by
    have hMD' : (0 : ℝ) < MD := by exact_mod_cast hMD
    have heD' : (0 : ℝ) < eD := by exact_mod_cast heD
    have hD' : (0 : ℝ) < D := by exact_mod_cast hD
    have hE : (0 : ℝ) < (cE loN loD Q : ℤ) := by
      have : (0 : ℝ) < (loD : ℝ) - loN := by
        have : (loN : ℝ) < loD := by exact_mod_cast hlo
        linarith
      unfold cE; push_cast; positivity
    unfold cDen; push_cast
    positivity
  have hX := nonneg_of_mul_nonneg_right hNn hW
  have hu1' : (1 : ℝ) + u ^ 2 ≠ 0 := by positivity
  have e : 2 * u / (1 + u ^ 2) = 2 * u / (1 + u ^ 2) := rfl
  have h2 : ((c.b : ℝ) / 2 ^ 60) * (2 * u / (1 + u ^ 2)) * (1 + u ^ 2) = 2 * ((c.b : ℝ) / 2 ^ 60) * u := by
    field_simp
  have hpos : (0 : ℝ) < 1 + u ^ 2 := by positivity
  by_contra hcon
  push_neg at hcon
  have : ((MN : ℝ) / MD - (eN : ℝ) / eD - (c.a : ℝ) / 2 ^ 60 - chebSum P D (affine ((loN : ℝ) / loD) u)) *
      (1 + u ^ 2) - 2 * ((c.b : ℝ) / 2 ^ 60) * u < 0 := by
    rw [← h2]
    nlinarith
  linarith

/-! ### Chains of cells and the caps -/

/-- The chained cells start at or before `a` and reach `hi` (all in units of `1/Q`). -/
def cover : List CellData → ℤ → ℤ → Bool
  | [], _, _ => false
  | c :: rest, a, hi => decide (c.u0 ≤ a) && (decide (hi ≤ c.u1) || cover rest c.u1 hi)

theorem cover_spec {Q : ℤ} (hQ : 0 < Q) : ∀ (cs : List CellData) (a hi : ℤ), cover cs a hi = true →
    ∀ u : ℝ, (a : ℝ) / Q ≤ u → u ≤ (hi : ℝ) / Q →
      ∃ c ∈ cs, (c.u0 : ℝ) / Q ≤ u ∧ u ≤ (c.u1 : ℝ) / Q
  | [], a, hi, h, u, _, _ => by simp [cover] at h
  | c :: rest, a, hi, h, u, h1, h2 => by
    simp only [cover, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true] at h
    obtain ⟨h0, h3 | h3⟩ := h
    · refine ⟨c, List.mem_cons_self .., ?_, ?_⟩
      · have : (c.u0 : ℝ) ≤ a := by exact_mod_cast h0
        have hQ' : (0 : ℝ) < Q := by exact_mod_cast hQ
        calc (c.u0 : ℝ) / Q ≤ a / Q := by gcongr
          _ ≤ u := h1
      · have : (hi : ℝ) ≤ c.u1 := by exact_mod_cast h3
        have hQ' : (0 : ℝ) < Q := by exact_mod_cast hQ
        calc u ≤ hi / Q := h2
          _ ≤ c.u1 / Q := by gcongr
    · by_cases hu : u ≤ (c.u1 : ℝ) / Q
      · refine ⟨c, List.mem_cons_self .., ?_, hu⟩
        have : (c.u0 : ℝ) ≤ a := by exact_mod_cast h0
        have hQ' : (0 : ℝ) < Q := by exact_mod_cast hQ
        calc (c.u0 : ℝ) / Q ≤ a / Q := by gcongr
          _ ≤ u := h1
      · push_neg at hu
        obtain ⟨c', hc', r1, r2⟩ := cover_spec hQ rest c.u1 hi h3 u hu.le h2
        exact ⟨c', List.mem_cons_of_mem _ hc', r1, r2⟩

/-- **GP Lemma 7.5 consumer (ordinary caps).**  `OrdCap t σ d G (MN/MD)` from `hf` (the source below its
Chebyshev majorant plus tail), accepted cells covering the window, and the chord pieces `hd`. -/
theorem ordCap_of_chain (S : CapSource) (t : Trunc) (σ : Sign) (d : ℝ → ℝ) (G : ℝ → Prop) (c : ℝ)
    {P : List ℤ} {D : ℕ} {loN loD MN MD eN eD Q : ℤ} (hD : 0 < D) (hQ : 0 < Q) (hloD : 0 < loD)
    (hlo : loN < loD) (hMD : 0 < MD) (heD : 0 < eD) (hloeq : ordLo σ = (loN : ℝ) / loD)
    (hc : c = (MN : ℝ) / MD)
    (hf : ∀ u ∈ ordDom σ, S.ordField t σ ((if σ = Sign.neg then -1 else 1) * u) ≤
      chebSum P D (affine (ordLo σ) u) + (eN : ℝ) / eD)
    (cs : List CellData) (hchk : cs.all (cellChk P D loN loD MN MD eN eD Q) = true)
    {a hi : ℤ} (hcov : cover cs a hi = true) (ha : (a : ℝ) / Q ≤ ordLo σ)
    (hG : ∀ u ∈ ordDom σ, G ((if σ = Sign.neg then -1 else 1) * u) → u ≤ (hi : ℝ) / Q)
    (hd : ∀ cl ∈ cs, ∀ u ∈ ordDom σ, (cl.u0 : ℝ) / Q ≤ u → u ≤ (cl.u1 : ℝ) / Q →
      G ((if σ = Sign.neg then -1 else 1) * u) →
      d ((if σ = Sign.neg then -1 else 1) * u) ≤ (cl.a : ℝ) / 2 ^ 60 + ((cl.b : ℝ) / 2 ^ 60) * (2 * u / (1 + u ^ 2))) :
    S.OrdCap t σ d G c := by
  intro u hu hGu
  have hu' := hu
  rw [ordDom_eq] at hu'
  obtain ⟨cl, hcl, r1, r2⟩ := cover_spec hQ cs a hi hcov u (ha.trans hu'.1) (hG u hu hGu)
  have hcell := cell_le (P := P) hD hQ hloD hlo hMD heD (List.all_eq_true.1 hchk cl hcl) r1 r2
  rw [← hloeq] at hcell
  have := hf u hu
  have := hd cl hcl u hu r1 r2 hGu
  rw [hc]
  linarith

/-- Near caps: cells over `[1/10, hi/Q]`; `hz0` is the zero region `(0, 1/10]` (zero geometry plus
a bound on `d`), `hf` the near `hf` on `[1/10,1]`. -/
theorem nearCap_of_chain (S : CapSource) (t : Trunc) (d : ℝ → ℝ) (G : ℝ → Prop) (c : ℝ)
    {P : List ℤ} {D : ℕ} {loN loD MN MD eN eD Q : ℤ} (hD : 0 < D) (hQ : 0 < Q) (hloD : 0 < loD)
    (hlo : loN < loD) (hMD : 0 < MD) (heD : 0 < eD) (hloeq : (1 / 10 : ℝ) = (loN : ℝ) / loD)
    (hc : c = (MN : ℝ) / MD)
    (hf : ∀ y ∈ Icc (1 / 10 : ℝ) 1, S.nearField t y ≤ chebSum P D (affine (1 / 10) y) + (eN : ℝ) / eD)
    (hz0 : ∀ y ∈ Ioc (0 : ℝ) (1 / 10), G y → S.nearField t y + d y ≤ c)
    (cs : List CellData) (hchk : cs.all (cellChk P D loN loD MN MD eN eD Q) = true)
    {a hi : ℤ} (hcov : cover cs a hi = true) (ha : (a : ℝ) / Q ≤ 1 / 10)
    (hG : ∀ y ∈ Ioo (0 : ℝ) 1, G y → y ≤ (hi : ℝ) / Q)
    (hd : ∀ cl ∈ cs, ∀ y ∈ Ioo (0 : ℝ) 1, (cl.u0 : ℝ) / Q ≤ y → y ≤ (cl.u1 : ℝ) / Q → G y →
      d y ≤ (cl.a : ℝ) / 2 ^ 60 + ((cl.b : ℝ) / 2 ^ 60) * (2 * y / (1 + y ^ 2))) :
    S.NearCap t d G c := by
  intro y hy hGy
  by_cases h : y ≤ 1 / 10
  · exact hz0 y ⟨hy.1, h⟩ hGy
  · push_neg at h
    obtain ⟨cl, hcl, r1, r2⟩ := cover_spec hQ cs a hi hcov y (ha.trans h.le) (hG y hy hGy)
    have hcell := cell_le (P := P) hD hQ hloD hlo hMD heD (List.all_eq_true.1 hchk cl hcl) r1 r2
    rw [← hloeq] at hcell
    have := hf y ⟨h.le, hy.2.le⟩
    have := hd cl hcl y hy r1 r2 hGy
    rw [hc]
    linarith

end

end CatalanMeasure.GenD.Signed.RouteI.CompactCells
