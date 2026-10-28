module

public import CatalanCore.Uniform.Content.UFWedge.Eval
public import CatalanCore.Uniform.Content.UFMoments.AltShift
public import CatalanCore.Uniform.Content.UFMoments.TypeDataLift

@[expose] public section

/-!
# UF wedge, W2: the fiber of a node depends only on its joint type (lane H9)

`nodeFib ρ c Q t` is the bordered fiber of an index `t` (Loewner row `ℓ`, prefix `PF1`).  If `t` is a
chain shift of `t₀` (`ShiftData`), the fibers are isomorphic modulo `p` (`nodeFib_iso_shift`): the
first-order shadow of `typeData_of_shift`.  Hence the cross wedge, and the wedge of every killed node
of a run, equals that of the first node of the run (`cross_shift`).
-/

open Polynomial Matrix Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Arith.Hybrid.Periodic CatalanCore.Uniform.Content.UFMember
  CatalanCore.Uniform.Content.Hybrid CatalanCore.Uniform.Content.UFMoments

namespace CatalanCore.Uniform.Content.UFWedge

variable {p N : ℕ} [Fact p.Prime] {Fr : Frame} {ι κ : Type} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ]

/-- The bordered fiber of an index `t` against the core `c` (Loewner row, prefix `PF1`). -/
noncomputable def nodeFib {R : Type*} [CommRing R] (ρ : (LocRing p)[X] →+* R) (Fr : Frame)
    (c : ι → ℕ) (Q : Matrix ι ι (LocRing p)[X]) (t : ℕ) : FibD R :=
  fibOf ρ Fr c Q (loewRow p Fr c t) (PF1 p Fr t) ((t : ℕ) : ZMod p)

theorem psiP_eq_of_phiP {g g' : (LocRing p)[X]} (h : phiP p g = phiP p g') : psiP p g = psiP p g' :=
  RatFunc.algebraMap_injective (ZMod p) h

theorem phiP_eq_of_sq {g g' : (LocRing p)[X]} {x : GaussLoc p}
    (h : algebraMap (LocRing p)[X] (GaussLoc p) g =
      algebraMap (LocRing p)[X] (GaussLoc p) g' + UFMoments.piL p ^ 2 * x) : phiP p g = phiP p g' := by
  have := congrArg (res p) h
  simpa [res_algebraMap, map_add, map_mul, map_pow, res_piL] using this

theorem Iso.map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) {F G : FibD R}
    (h : F.Iso G) : (F.map f).Iso (G.map f) := by
  obtain ⟨e, hM, hs, hu, hz⟩ := h
  refine ⟨e, fun (i j : F.n) => ?_, fun (i : F.n) => ?_, fun (i : F.n) => ?_, ?_⟩
  · show f (G.M (e i) (e j)) = f (F.M i j); rw [hM]
  · show f (G.s (e i)) = f (F.s i); rw [hs]
  · show f (G.u (e i)) = f (F.u i); rw [hu]
  · show f G.z = f F.z; rw [hz]

section Shift

variable (D : PoleData Fr p N) (hN : N < p * p) (c : ι → ℕ) (xs ys : κ → ℕ)
  (hc : ∀ a, c a < N) (hx : ∀ i, xs i < N) (hy : ∀ j, ys j < N)

/-- **(W2) Shift invariance of the fiber.** -/
theorem nodeFib_iso_shift (hR : RegRed D) (t0 t : ℕ) (ht : t < N) (hS : ShiftData D c t0 t) :
    (nodeFib (psiP p) Fr c (sLift c xs ys (hint_of_poleData D hN hc hx hy)).toBlocks₁₁ t0).Iso
      (nodeFib (psiP p) Fr c (sLift c xs ys (hint_of_poleData D hN hc hx hy)).toBlocks₁₁ t) := by
  obtain ⟨Δ, rfl, hwt, e, hce, hwc⟩ := hS
  obtain ⟨e', κ₁, hDD, hss, hℓ, hκ, -⟩ := typeData_of_shift D hN c xs ys hc hx hy hR t0 Δ
    (loewRow p Fr c t0) (loewRow p Fr c (t0 + Δ)) (fun a => rfl) (fun a => rfl) e hce hwc hwt ht
    (rfH p (red p (Fp Fr (t0 + Δ) - Fp Fr t0)) * (rfH p (red p Fr.norm))⁻¹) (fun _ => 0)
    (by simp)
  have hn := algebraMap_PF1 (Fr := Fr) D
  -- residues of the prefix values
  have hκ0 : res p (ellL p Fr (t0 + Δ) - ellL p Fr t0) = 0 := by
    rw [hκ, map_mul, res_piL, zero_mul]
  have hPF : ∀ a b : ℕ, res p (ellL p Fr a) = res p (ellL p Fr b) →
      phiP p (PF1 p Fr a) = phiP p (PF1 p Fr b) := by
    intro a b hab
    rw [← res_algebraMap, ← res_algebraMap, hn a, hn b, map_mul, map_mul, hab]
  refine ⟨e'.symm, fun i j => ?_, fun i => ?_, fun i => ?_, ?_⟩
  · obtain ⟨x, hx'⟩ := hDD i j
    exact psiP_eq_of_phiP (phiP_eq_of_sq hx')
  · obtain ⟨x, hx'⟩ := hss i
    exact psiP_eq_of_phiP (phiP_eq_of_sq hx')
  · obtain ⟨x, hx'⟩ := hℓ i
    refine psiP_eq_of_phiP (hPF _ _ ?_)
    have h1 := congrArg (res p) hx'
    rw [map_add, map_add, hκ0, add_zero, map_mul, map_pow, res_piL,
      zero_pow (by norm_num), zero_mul, add_zero] at h1
    exact h1
  · exact psiP_eq_of_phiP (hPF _ _ (sub_eq_zero.1 (by rw [← map_sub]; exact hκ0)))

end Shift

end CatalanCore.Uniform.Content.UFWedge
