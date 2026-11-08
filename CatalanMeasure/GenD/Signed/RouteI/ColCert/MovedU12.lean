module

public import CatalanMeasure.GenD.Signed.RouteI.ColCert.MovedCaps
public import CatalanMeasure.GenD.Signed.RouteI.ColCert.U12

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

/-!
# Moved column caps (G31): the unit checks of block 12

Each theorem `Vn_mv` is `finMv Vn m0 m1 cap0n cap1n cap2n = true`: the exact moved polynomials of the three
caps C0, C1, C2 (packed Horner, shifts, rounding) added to the unit's `Q`, `E`, with the logarithm items.
-/

namespace CatalanMeasure.GenD.Signed.RouteI.ColCert.Moved

theorem V361_mv : finMv V361 m0 m1 cap0n cap1n cap2n = true := by
  -- kcost: 2.4 s measured per unit (one unit, 3 caps), 8 Nov
  decide +kernel

theorem V362_mv : finMv V362 m0 m1 cap0n cap1n cap2n = true := by
  -- kcost: 2.4 s measured per unit (one unit, 3 caps), 8 Nov
  decide +kernel

theorem V363_mv : finMv V363 m0 m1 cap0n cap1n cap2n = true := by
  -- kcost: 2.4 s measured per unit (one unit, 3 caps), 8 Nov
  decide +kernel

theorem V364_mv : finMv V364 m0 m1 cap0n cap1n cap2n = true := by
  -- kcost: 2.4 s measured per unit (one unit, 3 caps), 8 Nov
  decide +kernel

theorem V365_mv : finMv V365 m0 m1 cap0n cap1n cap2n = true := by
  -- kcost: 2.4 s measured per unit (one unit, 3 caps), 8 Nov
  decide +kernel

theorem V366_mv : finMv V366 m0 m1 cap0n cap1n cap2n = true := by
  -- kcost: 2.4 s measured per unit (one unit, 3 caps), 8 Nov
  decide +kernel

theorem V367_mv : finMv V367 m0 m1 cap0n cap1n cap2n = true := by
  -- kcost: 2.4 s measured per unit (one unit, 3 caps), 8 Nov
  decide +kernel

theorem V368_mv : finMv V368 m0 m1 cap0n cap1n cap2n = true := by
  -- kcost: 2.4 s measured per unit (one unit, 3 caps), 8 Nov
  decide +kernel

theorem V369_mv : finMv V369 m0 m1 cap0n cap1n cap2n = true := by
  -- kcost: 2.4 s measured per unit (one unit, 3 caps), 8 Nov
  decide +kernel

theorem V370_mv : finMv V370 m0 m1 cap0n cap1n cap2n = true := by
  -- kcost: 2.4 s measured per unit (one unit, 3 caps), 8 Nov
  decide +kernel

theorem V371_mv : finMv V371 m0 m1 cap0n cap1n cap2n = true := by
  -- kcost: 2.4 s measured per unit (one unit, 3 caps), 8 Nov
  decide +kernel

theorem V372_mv : finMv V372 m0 m1 cap0n cap1n cap2n = true := by
  -- kcost: 2.4 s measured per unit (one unit, 3 caps), 8 Nov
  decide +kernel

theorem V373_mv : finMv V373 m0 m1 cap0n cap1n cap2n = true := by
  -- kcost: 2.4 s measured per unit (one unit, 3 caps), 8 Nov
  decide +kernel

theorem V374_mv : finMv V374 m0 m1 cap0n cap1n cap2n = true := by
  -- kcost: 2.4 s measured per unit (one unit, 3 caps), 8 Nov
  decide +kernel

theorem V375_mv : finMv V375 m0 m1 cap0n cap1n cap2n = true := by
  -- kcost: 2.4 s measured per unit (one unit, 3 caps), 8 Nov
  decide +kernel

theorem V376_mv : finMv V376 m0 m1 cap0n cap1n cap2n = true := by
  -- kcost: 2.4 s measured per unit (one unit, 3 caps), 8 Nov
  decide +kernel

theorem V377_mv : finMv V377 m0 m1 cap0n cap1n cap2n = true := by
  -- kcost: 2.4 s measured per unit (one unit, 3 caps), 8 Nov
  decide +kernel

theorem V378_mv : finMv V378 m0 m1 cap0n cap1n cap2n = true := by
  -- kcost: 2.4 s measured per unit (one unit, 3 caps), 8 Nov
  decide +kernel

theorem V379_mv : finMv V379 m0 m1 cap0n cap1n cap2n = true := by
  -- kcost: 2.4 s measured per unit (one unit, 3 caps), 8 Nov
  decide +kernel

theorem V380_mv : finMv V380 m0 m1 cap0n cap1n cap2n = true := by
  -- kcost: 2.4 s measured per unit (one unit, 3 caps), 8 Nov
  decide +kernel

theorem V381_mv : finMv V381 m0 m1 cap0n cap1n cap2n = true := by
  -- kcost: 2.4 s measured per unit (one unit, 3 caps), 8 Nov
  decide +kernel

theorem V382_mv : finMv V382 m0 m1 cap0n cap1n cap2n = true := by
  -- kcost: 2.4 s measured per unit (one unit, 3 caps), 8 Nov
  decide +kernel

theorem V383_mv : finMv V383 m0 m1 cap0n cap1n cap2n = true := by
  -- kcost: 2.4 s measured per unit (one unit, 3 caps), 8 Nov
  decide +kernel

theorem V384_mv : finMv V384 m0 m1 cap0n cap1n cap2n = true := by
  -- kcost: 2.4 s measured per unit (one unit, 3 caps), 8 Nov
  decide +kernel

theorem V385_mv : finMv V385 m0 m1 cap0n cap1n cap2n = true := by
  -- kcost: 2.4 s measured per unit (one unit, 3 caps), 8 Nov
  decide +kernel

theorem L12_mv : ∀ u ∈ L12, finMv u m0 m1 cap0n cap1n cap2n = true :=
  List.forall_mem_cons.2 ⟨V361_mv, List.forall_mem_cons.2 ⟨V362_mv, List.forall_mem_cons.2 ⟨V363_mv, List.forall_mem_cons.2 ⟨V364_mv, List.forall_mem_cons.2 ⟨V365_mv, List.forall_mem_cons.2 ⟨V366_mv, List.forall_mem_cons.2 ⟨V367_mv, List.forall_mem_cons.2 ⟨V368_mv, List.forall_mem_cons.2 ⟨V369_mv, List.forall_mem_cons.2 ⟨V370_mv, List.forall_mem_cons.2 ⟨V371_mv, List.forall_mem_cons.2 ⟨V372_mv, List.forall_mem_cons.2 ⟨V373_mv, List.forall_mem_cons.2 ⟨V374_mv, List.forall_mem_cons.2 ⟨V375_mv, List.forall_mem_cons.2 ⟨V376_mv, List.forall_mem_cons.2 ⟨V377_mv, List.forall_mem_cons.2 ⟨V378_mv, List.forall_mem_cons.2 ⟨V379_mv, List.forall_mem_cons.2 ⟨V380_mv, List.forall_mem_cons.2 ⟨V381_mv, List.forall_mem_cons.2 ⟨V382_mv, List.forall_mem_cons.2 ⟨V383_mv, List.forall_mem_cons.2 ⟨V384_mv, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CatalanMeasure.GenD.Signed.RouteI.ColCert.Moved
