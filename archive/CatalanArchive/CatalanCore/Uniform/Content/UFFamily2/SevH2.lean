module

public import CatalanCore.Uniform.Content.UFFamily2.Gen
public import CatalanCore.Uniform.Content.UFFamily2.SevHLayer

@[expose] public section

/-!
# UF family H through the generic window template (lane H, H11)

The same layer as `SevH.layerH`, now obtained from `layerGen`: the family contributes only the
affine data `N = 14 m`, `k = k₁`, `lo = p`, `m = r/12`, the arithmetic `winH` (omega), and the two
family-specific ingredients already proved in `SevH` (`noSing`, `killH`).  This is the shape of the
text that a bank family needs (about 40 lines).
-/

open Polynomial Matrix Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Arith.Hybrid.Periodic CatalanCore.Uniform.Content.UFMember
  CatalanCore.Uniform.Content.Hybrid CatalanCore.Uniform.Content.UFMoments
  CatalanCore.Uniform.Content.UFWedge CatalanCore.Uniform.Content.Smith
  CatalanCore.Uniform CatalanCore.Uniform.Content.Shape CatalanCore.Uniform.Content.UFWire
  CatalanCore.Uniform.Content.Member CatalanCore.Uniform.Content.Wire
  CatalanCore.Uniform.Content.UFFamily CatalanCore.Uniform.Content.UFFamily.SevE

namespace CatalanCore.Uniform.Content.UFFamily2.SevH

variable {Fr : Frame}

theorem winH {r p : ℕ} (h : Valid r p) :
    Win cE cE_pos 7 5 r p (14 * (r / 12)) (k1 p) p (r / 12) := by
  have hr12 := h.hr12
  have hr0 := h.hr0
  have hlo := h.hlo
  have hhi := h.hhi
  have hk := h.k1_spec
  have hk1 := h.k1_lo
  have hk2 := h.k1_hi
  have hpr := h.p_lt_r
  have hp29 := h.p_big
  have h2p := h.two_p
  have hd1 : (k1 p - 1) / p = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
  have hd2 : r / p = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
  have hd3 : p / p = 1 := Nat.div_self (by omega)
  exact
    { hr2 := by omega
      hr0 := hr0
      hbs := borderSize_H h
      hrN := by omega
      hNp := hNp_H h
      hpm := by omega
      hp2 := by omega
      hq0 := by norm_num
      hqp := by omega
      ho0 := by norm_num
      hop := by omega
      hk1 := hk1
      hk2 := by omega
      hkN := by omega
      hkp := by omega
      hdiv := by rw [hd1, hd2]
      hlo1 := by omega
      hr3 := by omega
      hqd := by rw [hd3, hd2]
      hNl := by omega }

/-- **The UF debit layer of family H**, through the generic template. -/
noncomputable def layerH2 (T : TwoTermData Fr 7 5) {depth : ℕ} :
    DebitLayer (altGeom cE cE_pos) Fr depth :=
  layerGen T (validH Fr) (fun r _ => 14 * (r / 12)) (fun _ p => k1 p) (fun _ p => p)
    (fun r _ => r / 12) (fun r p _ h => winH h.1) (fun r p _ h => hsq_H h.1)
    (fun r p _ h => h.2.2.1) (fun r p _ h => h.2.2.2)
    (fun r p _ h a Δ ha hb => noSing (T := T) h.1 _ rfl a Δ ha hb)
    (fun r p _ h v hv1 hv2 =>
      killH T h.1 (winH h.1).hNp (hsq_H h.1) h.2.2.1 h.2.2.2 h.2.1 rfl _ _ _ _ _ _
        Subtype.val_injective (alt_core_lt cE cE_pos) (alt_hcov cE cE_pos r) v hv1 hv2)

theorem layerH2_base (T : TwoTermData Fr 7 5) {depth : ℕ} (r p : ℕ) :
    (layerH2 (depth := depth) T).base r p = baseGen (r / 12) r p (k1 p) p := rfl

/-- The generic price specialises to the pilot price. -/
theorem baseGen_eq_baseH (r p : ℕ) : baseGen (r / 12) r p (k1 p) p = baseH r p := by
  unfold baseGen baseH
  rfl

end CatalanCore.Uniform.Content.UFFamily2.SevH

