module

public import CatalanCore.Uniform.Content.UFWedge.Shift
public import CatalanCore.Uniform.Content.UFWedge.Cert

@[expose] public section

/-!
# UF wedge: kill certificates (W1 + W2 + W3 assembled) (lane H9)

`KillCert D … t0 tv` certifies the nonvanishing of the wedge at the node of value `tv`, relative to
the representative `t0`: `tv` is a chain shift of a run start `ts` (`ShiftData`, W2), the fibers of
`t0` and `ts` at `X = u₀` are realised by integer data (`Realizes`, supplied per family) and the
integer cross wedge `crossZ` is nonzero modulo `p` (W3; automatic when `0 < |crossZ| < p`).
`KillCert.wedgeC_ne` / `wedgeR_ne` give the `wedgeC` / `wedgeR` hypotheses of the UF cells.
-/

open Polynomial Matrix Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Arith.Hybrid.Periodic CatalanCore.Uniform.Content.UFMember
  CatalanCore.Uniform.Content.Hybrid CatalanCore.Uniform.Content.UFMoments

namespace CatalanCore.Uniform.Content.UFWedge

variable {p N : ℕ} [Fact p.Prime] {Fr : Frame} {ι κ : Type} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ]

section Cert

variable (D : PoleData Fr p N) (hN : N < p * p) (c : ι → ℕ) (xs ys : κ → ℕ)
  (hc : ∀ a, c a < N) (hx : ∀ i, xs i < N) (hy : ∀ j, ys j < N)

/-- **A wedge certificate** for the node of value `tv` against the representative `t0`. -/
structure KillCert (t0 tv : ℕ) where
  ts : ℕ
  hshift : ShiftData D c ts tv
  u0 : ZMod p
  mJ : ℕ
  mK : ℕ
  DJ : ℤ
  DK : ℤ
  J : IntFib mJ
  K : IntFib mK
  hJ : (nodeFib (evP p u0) Fr c (sLift c xs ys (hint_of_poleData D hN hc hx hy)).toBlocks₁₁
    t0).Realizes DJ J
  hK : (nodeFib (evP p u0) Fr c (sLift c xs ys (hint_of_poleData D hN hc hx hy)).toBlocks₁₁
    ts).Realizes DK K
  hnz : (crossZ mJ mK DJ DK J K : ZMod p) ≠ 0

variable {D hN c xs ys hc hx hy}

/-- **(W2 + W3)** the cross wedge of `t0` and `tv` is nonzero at `u₀`. -/
theorem KillCert.cross_ne {t0 tv : ℕ} (C : KillCert D hN c xs ys hc hx hy t0 tv) (hR : RegRed D)
    (htv : tv < N) :
    (nodeFib (evP p C.u0) Fr c (sLift c xs ys (hint_of_poleData D hN hc hx hy)).toBlocks₁₁
        t0).cross
      (nodeFib (evP p C.u0) Fr c (sLift c xs ys (hint_of_poleData D hN hc hx hy)).toBlocks₁₁
        tv) ≠ 0 := by
  have hiso := nodeFib_iso_shift D hN c xs ys hc hx hy hR C.ts tv htv C.hshift
  have hiso' := Iso.map (Polynomial.evalRingHom C.u0) hiso
  have e1 : (nodeFib (psiP p) Fr c (sLift c xs ys (hint_of_poleData D hN hc hx hy)).toBlocks₁₁
      C.ts).map (Polynomial.evalRingHom C.u0) =
      nodeFib (evP p C.u0) Fr c (sLift c xs ys (hint_of_poleData D hN hc hx hy)).toBlocks₁₁ C.ts :=
    rfl
  have e2 : (nodeFib (psiP p) Fr c (sLift c xs ys (hint_of_poleData D hN hc hx hy)).toBlocks₁₁
      tv).map (Polynomial.evalRingHom C.u0) =
      nodeFib (evP p C.u0) Fr c (sLift c xs ys (hint_of_poleData D hN hc hx hy)).toBlocks₁₁ tv :=
    rfl
  rw [e1, e2] at hiso'
  rw [hiso'.cross_right]
  exact cross_ne_of_cert C.hJ C.hK C.hnz

/-- Build the nonvanishing from a nonzero integer smaller than `p`. -/
theorem crossZ_cast_ne {mJ mK : ℕ} {DJ DK : ℤ} {J : IntFib mJ} {K : IntFib mK}
    (hz : crossZ mJ mK DJ DK J K ≠ 0) (hp : (crossZ mJ mK DJ DK J K).natAbs < p) :
    (crossZ mJ mK DJ DK J K : ZMod p) ≠ 0 := cast_ne_zero_of_lt hz hp

variable (D hN c xs ys hc hx hy)

theorem sLift_col_eq_loew (t : κ) :
    (fun a => (sLift c xs ys (hint_of_poleData D hN hc hx hy)).toBlocks₁₂ a t) =
      loewRow p Fr c (ys t) := by
  funext a
  exact sLift_col_entry D hN c xs ys hc hx hy a t

theorem sLift_row_eq_loew (t : κ) :
    (fun a => (sLift c xs ys (hint_of_poleData D hN hc hx hy)).toBlocks₂₁ t a) =
      loewRow p Fr c (xs t) := by
  funext a
  exact sLift_row_entry D hN c xs ys hc hx hy t a

variable {D hN c xs ys hc hx hy}

/-- **Column kill from a certificate.** -/
theorem KillCert.wedgeC_ne {t0 : ℕ} (t : κ) (C : KillCert D hN c xs ys hc hx hy t0 (ys t))
    (hR : RegRed D) (ht0 : t0 < N) :
    wedgeC (sLift c xs ys (hint_of_poleData D hN hc hx hy)) Fr c ys
      (dirOf Fr c (sLift c xs ys (hint_of_poleData D hN hc hx hy)).toBlocks₁₁ t0
        (loewRow p Fr c t0)) t ≠ 0 := by
  refine wedgeC_ne_zero_of_eval D hN c xs ys hc hx hy t0 ht0 t C.u0 ?_
  rw [sLift_col_eq_loew D hN c xs ys hc hx hy t]
  exact C.cross_ne hR (hy t)

/-- **Row kill from a certificate.** -/
theorem KillCert.wedgeR_ne {t0 : ℕ} (t : κ) (C : KillCert D hN c xs ys hc hx hy t0 (xs t))
    (hR : RegRed D) (ht0 : t0 < N) :
    wedgeR (sLift c xs ys (hint_of_poleData D hN hc hx hy)) Fr c xs
      (dirOf Fr c (sLift c xs ys (hint_of_poleData D hN hc hx hy)).toBlocks₁₁ t0
        (loewRow p Fr c t0)) t ≠ 0 := by
  refine wedgeR_ne_zero_of_eval D hN c xs ys hc hx hy t0 ht0 t C.u0 ?_
  rw [sLift_row_eq_loew D hN c xs ys hc hx hy t]
  exact C.cross_ne hR (hx t)

end Cert

end CatalanCore.Uniform.Content.UFWedge
