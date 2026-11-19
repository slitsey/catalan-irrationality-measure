module
public import CatalanCore.Li2.NVMod.PolynomialCompute
public import CatalanCore.Li2.NVMod.PolynomialChecker
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace CatalanCore.Li2.NVMod.PolynomialCompute
open PolynomialCert

def Data.toCertificate (D : PolynomialCompute.Data) : PolynomialCert.Data :=
  ⟨D.moments,D.u,D.v,D.k,D.degree,D.bits,D.kBound⟩
theorem bounds_transfer (n p : ℕ) (D : PolynomialCompute.Data) :
    PolynomialCompute.boundsCheck n p D=PolynomialCert.boundsCheck n p D.toCertificate := by
  rfl
theorem bounds_nat_transfer (n p : ℕ) (D : PolynomialCompute.Data) :
    PolynomialCompute.boundsCheckNat n p D=PolynomialCert.boundsCheck n p D.toCertificate := by
  have hn (c : ℤ) (b : ℕ) : c.natAbs≤b ↔ |c|≤(b:ℤ) := by
    rw [←Int.natCast_natAbs,Nat.cast_le]
  simp only [PolynomialCompute.boundsCheckNat,PolynomialCert.boundsCheck,Data.toCertificate]
  simp_rw [hn]
  rfl
theorem step_transfer : ∀ (cur prev : List ℤ),
    PolynomialCompute.djStepZ cur prev=PolynomialCert.djStepZ cur prev := by
  intro cur
  induction cur with
  | nil=>intro prev;cases prev <;> rfl
  | cons a tail ih=>
    intro prev
    cases tail with
    | nil=>cases prev <;> rfl
    | cons b tail=>
      cases tail with
      | nil=>cases prev <;> rfl
      | cons c cs=>
        cases prev with
        | nil=>rfl
        | cons p0 ps=>
          cases ps with
          | nil=>rfl
          | cons p1 ps=>
            cases ps with
            | nil=>rfl
            | cons p2 ps=>
              simp only [PolynomialCompute.djStepZ,PolynomialCert.djStepZ]
              rw [ih]
              rfl
theorem loop_transfer (fuel : ℕ) (prev cur : List ℤ) :
    PolynomialCompute.djLoopZ fuel prev cur=PolynomialCert.djLoopZ fuel prev cur := by
  induction fuel generalizing prev cur with
  | zero=>rfl
  | succ f ih=>
    simp only [PolynomialCompute.djLoopZ,PolynomialCert.djLoopZ,step_transfer]
    cases PolynomialCert.djStepZ cur prev <;> simp only [ih]
theorem eval_transfer (n : ℕ) (m : List ℤ) :
    PolynomialCompute.djEvalZ n m=PolynomialCert.djEvalZ n m := by
  simp only [PolynomialCompute.djEvalZ,PolynomialCert.djEvalZ,loop_transfer]
theorem arithmetic_transfer (n p : ℕ) (D : PolynomialCompute.Data) :
    PolynomialCompute.arithmeticCheck n p D=PolynomialCert.arithmeticCheck n p D.toCertificate := by
  unfold PolynomialCompute.arithmeticCheck PolynomialCert.arithmeticCheck
  dsimp only [Data.toCertificate]
  rw [show PolynomialCompute.horner ((2:ℤ)^D.bits)=PolynomialCert.horner ((2:ℤ)^D.bits) from rfl]
  rw [eval_transfer]
  rfl

theorem polynomial_identity (n p : ℕ) (D : PolynomialCompute.Data)
    (hb : PolynomialCompute.boundsCheck n p D=true)
    (ha : PolynomialCompute.arithmeticCheck n p D=true) :
    DataSupport.coefficientsPoly D.u*PolynomialCert.determinantPolynomial n D.toCertificate+
      DataSupport.coefficientsPoly D.v*PolynomialCert.residuePolynomial p=
        1+Polynomial.C (p:ℤ)*DataSupport.coefficientsPoly D.k := by
  exact PolynomialCert.polynomial_identity n p D.toCertificate
    ((bounds_transfer n p D).symm.trans hb) ((arithmetic_transfer n p D).symm.trans ha)

def interiorChecked (I : EndpointInput) (D : PolynomialCompute.Data)
    (hb : PolynomialCompute.boundsCheck I.key.size I.p D=true)
    (ha : PolynomialCompute.arithmeticCheck I.key.size I.p D=true)
    (hm : ∀ e<2*I.key.size-1,
      (PolynomialCert.momentPolynomial D.toCertificate e).map (Int.castRingHom (ZMod I.p))=
        (I.mz e).map (Int.castRingHom (ZMod I.p))) : PolynomialCert.InteriorChecked I :=
  ⟨D.toCertificate,(bounds_transfer _ _ D).symm.trans hb,
    (arithmetic_transfer _ _ D).symm.trans ha,hm⟩
#print axioms bounds_transfer
#print axioms arithmetic_transfer
#print axioms polynomial_identity
end CatalanCore.Li2.NVMod.PolynomialCompute


