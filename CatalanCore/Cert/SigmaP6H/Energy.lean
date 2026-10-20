module

public import CatalanCore.Cert.SigmaP6H.Data
public import CatalanCore.Cert.SigmaP6.IBound
public import CatalanCore.Decay.Rect.IrhoAppend
public import CatalanCore.Decay.Rect.EnergyGen

@[expose] public section

/-!
# `I_ρ(σ_h) ≤ Ibound` for the P6 hybrid data (P6DECAY)

`I_ρ(wtH) = (64/81) (I(σ_P6) + 2 I(σ_P6, λ) + I(λ))` (`Irho_append_div`), `I(σ_P6) ≤ IBOUND`
(`SigmaP6.I_ok`), and the cross and `λλ` terms from the scaled-integer lower log bounds (`logLoS`)
exactly as `SigmaP6.IBound`: `699 * 32 + 32 * 32` pair logs, kernel-checked in chunks.
The 32 atoms are given by a formula (`lamPt`), no table.
-/

open Real
open CatalanLambda.Decay (krho Irho)

namespace CatalanCore.Cert.SigmaP6H

open CatalanCore.Cert.SigmaP6 (Pt Jr row_eq pair_le cpt sum_sigma ptAt iRow qII iChunk sigD_chunks
  cS mS I_ok IBOUND)

set_option maxRecDepth 100000

/-- The `k`-th correction atom `1 + k/128 - 1/2048` (scale `2^40`), weight `1/256` (scale `2^32`). -/
def lamPt (k : Fin 32) : Pt := ((2 : ℤ) ^ 40 + ((k : ℕ) : ℤ) * 2 ^ 33 - 2 ^ 29, 0, 2 ^ 24)

def lamP : List Pt := List.ofFn lamPt

/-- Integer total of `A` against `B` (generic `EnergyGen.iTotL` at this frame's `iRow`). -/
abbrev iTotL (B A : List Pt) : ℤ := CatalanCore.Decay.EnergyGen.iTotL iRow B A

lemma sum_lam (f : Pt → ℝ) : ∑ k : Fin 32, f (lamPt k) = (lamP.map f).sum := by
  unfold lamP; rw [List.map_ofFn, List.sum_ofFn]; rfl

lemma cpt_lamPt (k : Fin 32) : cpt (lamPt k) = lamC k := by
  unfold cpt lamPt lamC
  apply Complex.ext
  · simp only [Complex.ofReal_re]
    push_cast
    ring
  · simp

lemma lamW_eq (k : Fin 32) : lamW k = ((lamPt k).2.2 : ℝ) / 2 ^ 32 := by
  unfold lamW lamPt; norm_num

lemma iTotL_append (B a b : List Pt) : iTotL B (a ++ b) = iTotL B a + iTotL B b := by
  induction a with
  | nil => simp [iTotL, CatalanCore.Decay.EnergyGen.iTotL]
  | cons p ps ih =>
    simp only [List.cons_append, iTotL, CatalanCore.Decay.EnergyGen.iTotL] at ih ⊢
    rw [ih]; ring

theorem X1_0 : iTotL lamP (iChunk 0) = (2028625047015848599058920597132148736 : ℤ) := by decide +kernel
theorem X1_1 : iTotL lamP (iChunk 1) = (1089337204742110077302765585201889280 : ℤ) := by decide +kernel
theorem X1_2 : iTotL lamP (iChunk 2) = (1026312287779777111350506078003527680 : ℤ) := by decide +kernel
theorem X1_3 : iTotL lamP (iChunk 3) = (983442563978048471413357688479809536 : ℤ) := by decide +kernel
theorem X1_4 : iTotL lamP (iChunk 4) = (948993377425175411117755814274662400 : ℤ) := by decide +kernel
theorem X1_5 : iTotL lamP (iChunk 5) = (919130031831770001341435551693144064 : ℤ) := by decide +kernel
theorem X1_6 : iTotL lamP (iChunk 6) = (893082781993383695840476942189985792 : ℤ) := by decide +kernel
theorem X1_7 : iTotL lamP (iChunk 7) = (869686150651855432740253268082425856 : ℤ) := by decide +kernel
theorem X1_8 : iTotL lamP (iChunk 8) = (848945585688358613116204894902026240 : ℤ) := by decide +kernel
theorem X1_9 : iTotL lamP (iChunk 9) = (829895243739349007226175889948540928 : ℤ) := by decide +kernel
theorem X1_10 : iTotL lamP (iChunk 10) = (812260313815050719920578831509880832 : ℤ) := by decide +kernel
theorem X1_11 : iTotL lamP (iChunk 11) = (796063472539590766514401638875136000 : ℤ) := by decide +kernel
theorem X1_12 : iTotL lamP (iChunk 12) = (781152180169067076727594206170710016 : ℤ) := by decide +kernel
theorem X1_13 : iTotL lamP (iChunk 13) = (767150319128588144793233599603146752 : ℤ) := by decide +kernel
theorem X1_14 : iTotL lamP (iChunk 14) = (753986422997413527317013799431569408 : ℤ) := by decide +kernel
theorem X1_15 : iTotL lamP (iChunk 15) = (740839099085758680329349703695073280 : ℤ) := by decide +kernel
theorem X1_16 : iTotL lamP (iChunk 16) = (718204827987489111956987520367984640 : ℤ) := by decide +kernel
theorem X1_17 : iTotL lamP (iChunk 17) = (663595038177885010333307687426588672 : ℤ) := by decide +kernel
theorem X1_18 : iTotL lamP (iChunk 18) = (618117975464632972984141177728008192 : ℤ) := by decide +kernel
theorem X1_19 : iTotL lamP (iChunk 19) = (574656114207412854455132640704987136 : ℤ) := by decide +kernel
theorem X1_20 : iTotL lamP (iChunk 20) = (530612631003398764893650592827703296 : ℤ) := by decide +kernel
theorem X1_21 : iTotL lamP (iChunk 21) = (486186425102011838323267454162173952 : ℤ) := by decide +kernel
theorem X1_22 : iTotL lamP (iChunk 22) = (441440378423085641247350293220294656 : ℤ) := by decide +kernel
theorem X1_23 : iTotL lamP (iChunk 23) = (124392851256815683046391907983818752 : ℤ) := by decide +kernel

def X1 : ℤ := 19246108324203877213350253363615236096
def X2 : ℤ := -31010487649079415610499673568856506368

theorem X1_val : iTotL lamP SigmaP6.sigD = X1 := by
  conv_lhs => rw [sigD_chunks]
  simp only [iTotL_append]
  rw [X1_0, X1_1, X1_2, X1_3, X1_4, X1_5, X1_6, X1_7, X1_8, X1_9, X1_10, X1_11, X1_12, X1_13, X1_14, X1_15, X1_16, X1_17, X1_18, X1_19, X1_20, X1_21, X1_22, X1_23]
  unfold X1; norm_num

theorem X2_val : iTotL lamP lamP = X2 := by decide +kernel

theorem cross_le : ∑ k : Fin 699, ∑ l : Fin 32, mS k * lamW l *
      krho (1 / 2048 : ℝ) (cS k) (lamC l) ≤ -(X1 : ℝ) / 2 ^ 129 := by
  refine CatalanCore.Decay.EnergyGen.sum2_le_gen row_eq _ SigmaP6.sigD lamP (fun k : Fin 699 => ptAt k) lamPt
    sum_sigma sum_lam (fun k l => ?_) X1 X1_val
  have := pair_le (ptAt k) (lamPt l)
  rw [cpt_lamPt] at this
  rw [lamW_eq]
  exact this

theorem ll_le : Irho (1 / 2048 : ℝ) lamC lamW ≤ -(X2 : ℝ) / 2 ^ 129 := by
  unfold Irho
  refine CatalanCore.Decay.EnergyGen.sum2_le_gen row_eq _ lamP lamP lamPt lamPt
    sum_lam sum_lam (fun k l => ?_) X2 X2_val
  have := pair_le (lamPt k) (lamPt l)
  rw [cpt_lamPt, cpt_lamPt] at this
  rw [lamW_eq, lamW_eq]
  exact this

theorem Irho_hyb_expand :
    Irho (1 / 2048 : ℝ) cH wtH
      = (64 / 81) * (Irho (1 / 2048 : ℝ) cS mS
        + 2 * ∑ k : Fin 699, ∑ l : Fin 32, mS k * lamW l * krho (1 / 2048 : ℝ) (cS k) (lamC l)
        + Irho (1 / 2048 : ℝ) lamC lamW) := by
  have h := CatalanCore.Decay.Irho_append_div (1 / 2048 : ℝ) (1 + 1 / 8) (by norm_num) cS mS lamC lamW
  have e : (fun k : Fin (699 + 32) => (Fin.append mS lamW k) / (1 + (1 / 8 : ℝ))) = wtH := rfl
  rw [e] at h
  unfold cH
  rw [h]
  ring

def IboundP6H : ℚ := 164460768 / 10 ^ 8

theorem I_ok_P6H : Irho (1 / 2048 : ℝ) cH wtH ≤ (IboundP6H : ℝ) := by
  rw [Irho_hyb_expand]
  have h1 := I_ok
  have h2 := cross_le
  have h3 := ll_le
  have hX : (64 / 81 : ℝ) * ((IBOUND : ℝ) + 2 * (-(X1 : ℝ) / 2 ^ 129) + (-(X2 : ℝ) / 2 ^ 129))
      ≤ (IboundP6H : ℝ) := by
    unfold IBOUND X1 X2 IboundP6H
    push_cast
    norm_num
  refine le_trans ?_ hX
  have := mul_le_mul_of_nonneg_left
    (show Irho (1 / 2048 : ℝ) cS mS
        + 2 * ∑ k : Fin 699, ∑ l : Fin 32, mS k * lamW l * krho (1 / 2048 : ℝ) (cS k) (lamC l)
        + Irho (1 / 2048 : ℝ) lamC lamW
        ≤ (IBOUND : ℝ) + 2 * (-(X1 : ℝ) / 2 ^ 129) + (-(X2 : ℝ) / 2 ^ 129) by linarith)
    (by norm_num : (0 : ℝ) ≤ 64 / 81)
  exact this

end CatalanCore.Cert.SigmaP6H
