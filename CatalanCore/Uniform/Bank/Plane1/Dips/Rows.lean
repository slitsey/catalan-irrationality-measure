module
public import CatalanCore.Uniform.Bank.Plane1.ContentClosed
public import CatalanCore.Uniform.Bank.Plane1.Rows
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 1600000
/-! The dip interface consumes the full generic content certificate and P120.
Geometry, deletion depth, budget and threshold are parameters. -/
namespace CatalanCore.Uniform.Bank.Plane1.Dips
open CatalanCore CatalanCore.Uniform CatalanCore.Measure CatalanFrames.P6
open CatalanCore.Uniform.Content.Shape CatalanCore.Uniform.Content.BankShared
open CatalanCore.Uniform.Content.BankShared.KTerm CatalanCore.Uniform.Content.BankShared.Check
open CatalanCore.Uniform.Content.SmallPrimes CatalanCore.Uniform.Bank.Plane1
structure DipBankOK (g : ℚ) (hg : 0<g) (depth : ℕ) (σ : Support)
    (a b c : ℤ) (h0 : a+b+c=0) (kd : KBankDataC) (B : SmallBudget) (N0 : ℕ) : Prop where
  check : kcheckC kd=true
  alpha : g=2*kd.α
  hdepth : depth≤kd.depth
  control : AltQ g hg kd.cF (NodeFamily.polynomial (planeFrame σ a b c h0) (altGeom g hg).geometry)
  cat : KCatValid g hg (planeFrame σ a b c h0) depth kd.shifts kd.Q kd.Pbad N0 kd.kcat
  «prefix» : ∀ n j0 j1 j2, KCatValid g hg (planeFrame σ a b c h0) depth kd.shifts kd.Q kd.Pbad N0 [kbrPre n j0 [j1,j2]]
  d1x : KCatValid g hg (planeFrame σ a b c h0) depth kd.shifts kd.Q kd.Pbad N0 [⟨kD1xE,[],0⟩]
  pre : PreValid g hg (planeFrame σ a b c h0) depth kd.M B kd.t0 kd.α0b

theorem dip_content_closed (g : ℚ) (hg : 0<g) (depth : ℕ) (σ : Support)
    (a b c : ℤ) (h0 : a+b+c=0) (kd : KBankDataC) (B : SmallBudget) (N0 : ℕ)
    (hok : DipBankOK g hg depth σ a b c h0 kd B N0) :
    HasScaledContent (AltEven g hg (planeFrame σ a b c h0) depth) (altGeom g hg).scale (kd.Λ:ℝ) := by
  exact hasScaledContent_of_kcheckC kd hok.check g hg hok.alpha
    (planeFrame σ a b c h0).const depth _ hok.hdepth hok.control B N0
    hok.cat hok.«prefix» hok.d1x hok.pre

theorem dip_point (g : ℚ) (hg : 0<g) (depth : ℕ) (σ : Support)
    (a b c : ℤ) (h0 : a+b+c=0) (ha : a≠0) (kd : KBankDataC) (B : SmallBudget) (N0 : ℕ)
    (hok : DipBankOK g hg depth σ a b c h0 kd B N0) {D cc : ℝ}
    (hD : HasScaledDecay ((altGeom g hg).family (planeFrame σ a b c h0) depth) (altGeom g hg).scale D cc)
    (hη : (kd.Λ:ℝ)<D) (hcc : 0<cc)
    (hnv : ∃ R0 : ℕ,∀ s : ℕ,R0≤s → ∀ x : ℚ,∃ n,
      (((altGeom g hg).family (planeFrame σ a b c h0) depth).restrictAdm (fun i => i.1%2=0)).Adm n ∧
      (altGeom g hg).scale n=2*s ∧
      (((altGeom g hg).family (planeFrame σ a b c h0) depth).restrictAdm (fun i => i.1%2=0)).evalQ n x≠0) :
    MeasureLBAt (chi3L2+((planeT σ a b:ℚ):ℝ)*Real.pi^2) (cc/(D-(kd.Λ:ℝ))) ∧
      Irrational (chi3L2+((planeT σ a b:ℚ):ℝ)*Real.pi^2) := by
  have hu : planeU σ a≠0 := by
    unfold planeU
    have hs : (σ.sgn:ℚ)≠0 := by cases σ <;> simp [Support.sgn]
    have ha' : (a:ℚ)≠0 := by exact_mod_cast ha
    positivity
  exact alt_point g hg (planeFrame σ a b c h0) depth
    (dip_content_closed g hg depth σ a b c h0 kd B N0 hok) hD hη hcc hnv
    (u := planeU σ a) (v := 0) hu (by simpa using plane_const σ a b c h0 ha)
end CatalanCore.Uniform.Bank.Plane1.Dips
#print axioms CatalanCore.Uniform.Bank.Plane1.Dips.dip_content_closed
#print axioms CatalanCore.Uniform.Bank.Plane1.Dips.dip_point
