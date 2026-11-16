module

public import CatalanCore.Zeta5.CostOut.ExtSum
public import CatalanCore.Zeta5.CostOut.ExtInt

@[expose] public section

/-!
# ZC19 (discrete half): `γ_p^ext = (2 p Γ(K/p))/2 + O(1)` with `2 p Γ(K/p) = GZ2`

`gammaExt H` is the exponent of `zc18_ext`. `gammaExt_close`: `|γ_p^ext - GZ2/2| ≤ 83`
(`64` for the zero class, `19` for the ordinary classes, `ExtInt.ext_int_close`).
-/

open Finset

namespace CatalanCore.Zeta5.CostOut

open Apery

/-- `γ_p^ext = 2 ∑ w` of `zc18_ext`. -/
noncomputable def gammaExt {p n : ℕ} (H : ExtHyp p n) : ℚ :=
  2 * ∑ s : (Σ a : Fin (p / 2 + 1), Fin (extL p n a)),
    winner H.m_pos (extL p n) (Bse p (40 * n) (3 * n)) s

/-- The closed `2 p Γ(K/p)` at the parameters of `K = 40 n`, `p`. -/
def pGam2 (n p : ℕ) : ℤ :=
  GZ2 n p ((40 * n % p : ℕ) : ℤ) ((92 * n / p : ℕ) : ℤ) ((40 * n / p : ℕ) : ℤ)
    ((80 * n / p : ℕ) : ℤ)

namespace ExtHyp

variable {p n : ℕ} (H : Apery.ExtHyp p n)
include H

theorem gammaExt_close :
    |gammaExt H - (pGam2 n p : ℚ) / 2| ≤ 83 := by
  have hp0 : 0 < p := by have := H.h101; omega
  have hpo := H.p_odd
  have hq := q_bounds H
  have hT2 := H.T_ge2
  have hT6 := H.T_le6
  have hN3 : 3 * n ≤ p / 2 := by have := H.hout; omega
  have hsplit := gammaExt_split H
  have hord := ord_class_sum H
  have hz := zeroPart_bound H
  -- the closed ordinary sum as an integer
  have hint := ext_int_close (n := n) (p := p) (v := 40 * n % p) (E := extE p n) (m := p / 2)
    (T := extT p n) (T0 := 92 * n / p) (q := 40 * n / p) (q2 := 80 * n / p)
    (r0 := 92 * n % p) (r2 := 80 * n % p) (by omega) H.h101 H.hpK H.hout
    (Nat.div_add_mod (40 * n) p)
    (Nat.mod_lt _ hp0) (by omega)
    (by have := H.tot_eq; rw [H.tot_val] at this; exact this) H.E_lt hT2 hT6
    (by have := Nat.div_add_mod (92 * n) p; linarith) (Nat.mod_lt _ hp0)
    ⟨(Nat.le_div_iff_mul_le hp0).mpr (by have := H.hpK; omega),
     by have : 92 * n / p < 7 := (Nat.div_lt_iff_lt_mul hp0).mpr (by have := H.hout; omega); omega⟩
    (by have := Nat.div_add_mod (80 * n) p; linarith) (Nat.mod_lt _ hp0)
    ⟨(Nat.le_div_iff_mul_le hp0).mpr (by have := H.hpK; omega),
     by have : 80 * n / p < 6 := (Nat.div_lt_iff_lt_mul hp0).mpr (by have := H.hout; omega); omega⟩
    (nHn p n) (nNHn p n) (loN p n) rfl rfl rfl
  rw [min_eq_left hN3] at hord
  have hE : (∑ i : Fin (p / 2), ((extL p n i.succ : ℕ) : ℚ) *
        (((extL p n i.succ : ℕ) : ℚ) + 6 * (lN p n ((i : ℕ) + 1) : ℚ)
          - (lK p n ((i : ℕ) + 1) : ℚ) - 5))
      = ((extGamZ ((p / 2 : ℕ) : ℤ) (3 * (n : ℤ)) (extE p n : ℤ) (nHn p n : ℤ) (nNHn p n : ℤ)
          (extT p n : ℤ) ((40 * n / p : ℕ) : ℤ) (loN p n : ℤ) : ℤ) : ℚ) := by
    rw [hord]
    unfold extGamZ
    generalize p / 2 = m
    generalize 40 * n / p = q
    push_cast
    ring
  have hgam : gammaExt H = zeroPart H + ((extGamZ ((p / 2 : ℕ) : ℤ) (3 * (n : ℤ)) (extE p n : ℤ)
      (nHn p n : ℤ) (nNHn p n : ℤ) (extT p n : ℤ) ((40 * n / p : ℕ) : ℤ) (loN p n : ℤ) : ℤ) : ℚ) := by
    unfold gammaExt
    rw [hsplit, hE]
  obtain ⟨h1, h2⟩ := hint
  have h1' : (-2 : ℚ) ≤ 2 * ((extGamZ ((p / 2 : ℕ) : ℤ) (3 * (n : ℤ)) (extE p n : ℤ)
      (nHn p n : ℤ) (nNHn p n : ℤ) (extT p n : ℤ) ((40 * n / p : ℕ) : ℤ) (loN p n : ℤ) : ℤ) : ℚ)
      - (pGam2 n p : ℚ) := by
    exact_mod_cast h1
  have h2' : 2 * ((extGamZ ((p / 2 : ℕ) : ℤ) (3 * (n : ℤ)) (extE p n : ℤ)
      (nHn p n : ℤ) (nNHn p n : ℤ) (extT p n : ℤ) ((40 * n / p : ℕ) : ℤ) (loN p n : ℤ) : ℤ) : ℚ)
      - (pGam2 n p : ℚ) ≤ 38 := by
    exact_mod_cast h2
  rw [abs_le] at hz ⊢
  rw [hgam]
  constructor <;> linarith [hz.1, hz.2]

end ExtHyp

end CatalanCore.Zeta5.CostOut
