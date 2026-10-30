module
public import CatalanMeasure.GenD.Uniform.W.SlotsT.GlueLB
@[expose] public section
set_option Elab.async false

/-!
# Theorem MT (b) with Lemma S: the certificate needs only the main-window equations

`MTGlueOKS` is `MTGlueOK` with the overflow equations replaced by the shifted main-window
equations: a digit `J'+1` of `J2` with `J' ∈ J1` needs no equation of its own, only the single global
condition `ψ_s(y) + ψ_s(u) = 0` (Lemma S, `J2_of_shift`) and the unit bound `(s+3)(J'+2) < p`.
-/

namespace CatalanMeasure.GenD.Uniform.W.SlotsT
open Module Polynomial CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W
  CatalanMeasure.GenD.Uniform.W.Thin CatalanMeasure.GenD.Uniform.W.Slots
noncomputable section

/-- The certificate of Theorem MT (b) with the shifted overflow equations. -/
def MTGlueOKS (P : Parameters) (N p s K D1 elo : ℕ) (k0 : ℤ) [Fact p.Prime] : Prop :=
  D1 ≤ (p - 1) / 2 ∧ p ≤ P.h N + (p - 1) / 2 ∧ P.h N + (p - 1) / 2 - p < p ∧
    s * p + 1 ≤ P.H N ∧ p ≤ P.H N - 1 - s * p ∧ P.H N - 1 - s * p < 2 * p ∧
    P.h N + D1 ≤ (P.H N - 1 - s * p) + 1 ∧ elo ≤ P.H N - 1 - s * p - p + 1 ∧
    1 ≤ s ∧ (∀ k : Fin K, (k0 + (k : ℕ)).natAbs ≤ s) ∧
    ∃ (y u : Fin K → ZMod p) (A B : ZMod p) (J1 J2 : Finset ℕ), y ≠ 0 ∧ u ≠ 0 ∧
      (∀ J, J ∈ J1 →
        (⟨tyMap p K k0, gyMap p K k0⟩ : Prof p K).psi (P.H N) J s y = A ∧
        (⟨tpTy p K k0, tpGy p K k0⟩ : Prof p K).psi (P.H N) J s u = B) ∧
      (∀ J, J ∈ J1 → (s + 3) * (J + 2) < p) ∧
      ZoneZ.psiS s ((⟨tyMap p K k0, gyMap p K k0⟩ : Prof p K).Gy y)
          ((⟨tyMap p K k0, gyMap p K k0⟩ : Prof p K).Ty y) (3 / 2) +
        ZoneZ.psiS s ((⟨tpTy p K k0, tpGy p K k0⟩ : Prof p K).Gy u)
          ((⟨tpTy p K k0, tpGy p K k0⟩ : Prof p K).Ty u) (3 / 2) = 0 ∧
      (∀ J, J ∈ J2 → (∃ J', J = J' + 1 ∧ J' ∈ J1) ∨
        ((⟨tyMap p K k0, gyMap p K k0⟩ : Prof p K).psi (P.H N) J ((s : ℤ) + 1) y +
          (⟨tpTy p K k0, tpGy p K k0⟩ : Prof p K).psi (P.H N) J ((s : ℤ) + 1) u = A + B)) ∧
      (∀ j, P.b N ≤ j → j < P.L N →
        P.H N - 1 - s * p - (P.h N + D1 - 1) ≤ j % p → j / p ∈ J1) ∧
      (∀ j, P.b N ≤ j → j < P.L N → j % p + elo + p ≤ P.H N - 1 - s * p → j / p ∈ J2)

variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

theorem MTGlueOKS.toOK (hp2 : p ≠ 2) {s K D1 elo : ℕ} {k0 : ℤ}
    (h : MTGlueOKS P N p s K D1 elo k0) : MTGlueOK P N p s K D1 elo k0 := by
  obtain ⟨hD, hph, hv, hs, hpη, hη2, hdeg, helo, hs1, hk, y, u, A, B, J1, J2, hy, hu, hJ1, hun, hΨ,
    hJ2, hc1, hc2⟩ := h
  refine ⟨hD, hph, hv, hs, hpη, hη2, hdeg, helo, y, u, A, B, J1, J2, hy, hu, hJ1, ?_, hc1, hc2⟩
  intro J hJ
  rcases hJ2 J hJ with ⟨J', rfl, hJ'⟩ | hd
  · have hpo := p_odd_half hp2
    have hp3 : 3 ≤ p := by have := (Fact.out : p.Prime).two_le; omega
    have hHs : s + 3 ≤ P.H N := by nlinarith
    obtain ⟨e1, e2⟩ := hJ1 J' hJ'
    exact J2_of_shift (⟨tyMap p K k0, gyMap p K k0⟩ : Prof p K) (⟨tpTy p K k0, tpGy p K k0⟩ : Prof p K)
      (shiftUnits_of_lt hp2 s J' (hun J' hJ')) (P.H N) hHs y u
      (gyMap_natDegree_le' hp2 hs1 k0 hk y) (tyMap_natDegree_le' hp2 k0 hk y)
      (tpGy_natDegree_le' hp2 k0 hk u) (tpTy_natDegree_le' hp2 hs1 k0 hk u) hΨ A B e1 e2
  · exact hd

theorem mtGlueVal1_le_of_okS (hP : Admissible P) (hN : 0 < N) (hp2 : p ≠ 2) (hH : P.H N < p ^ 2)
    {s K D1 elo : ℕ} {k0 : ℤ} (h : MTGlueOKS P N p s K D1 elo k0) :
    mtGlueVal1 P N p s K D1 elo k0 ≤ nullity P N p :=
  mtGlueVal1_le_of_ok hP hN hp2 hH (h.toOK hp2)

/-- **`mtGlueLBS`**: Theorem MT (b), one profile pair and Lemma S, for a fixed window. -/
def mtGlueLBS (P : Parameters) (hP : Admissible P) (s K D1 elo : ℕ) (k0 : ℤ) : NullityLB P :=
  NullityLB.ofWindow P
    (fun N p => ∃ hp : p.Prime, haveI : Fact p.Prime := ⟨hp⟩; MTGlueOKS P N p s K D1 elo k0)
    (fun N p => open Classical in
      if hp : p.Prime then haveI : Fact p.Prime := ⟨hp⟩; mtGlueVal1 P N p s K D1 elo k0 else 0)
    (fun N p hN hp hp2 hH hApp => by
      haveI : Fact p.Prime := ⟨hp⟩
      obtain ⟨hp', hok⟩ := hApp
      simp only [dif_pos hp]
      exact mtGlueVal1_le_of_okS hP hN hp2 hH hok)

#print axioms MTGlueOKS.toOK
#print axioms mtGlueLBS

end
end CatalanMeasure.GenD.Uniform.W.SlotsT
