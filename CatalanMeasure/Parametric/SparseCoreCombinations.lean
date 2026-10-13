module
public import CatalanMeasure.Parametric.PolynomialCombinations
public import CatalanMeasure.Parametric.SparseFilteredRelation
public import CatalanMeasure.Parametric.SupportedDigitRelation
@[expose] public section
namespace CatalanMeasure.Parametric
open Polynomial Matrix OAI.InternalCatalan
noncomputable section

def sparseCoreFamily (P : Parameters) (N p : ℕ) : Fin (P.g N) → (ZMod p)[X] :=
  fun d =>(sparseRowCore P N p (d.val+1)).map (Int.castRingHom (ZMod p))

def sparseLowCoreFamily (P : Parameters) (N p : ℕ) : Fin (P.g N) → (ZMod p)[X] :=
  fun d =>(sparseRowCore P N (2*p) (d.val+1)).map (Int.castRingHom (ZMod p))

def sparsePFamily (P : Parameters) (N p k : ℕ) : Fin (P.g N) → (ZMod p)[X] :=
  fun d =>(sparseRowPDelta P N p k (d.val+1)).map (Int.castRingHom (ZMod p))

def sparseDFamily (P : Parameters) (N p k : ℕ) : Fin (P.g N) → (ZMod p)[X] :=
  fun d =>(sparseRowDDelta P N p k (d.val+1)).map (Int.castRingHom (ZMod p))

theorem sparseCombination_identities {P : Parameters} {N p : ℕ} [hp : Fact p.Prime]
    (hp2 : p≠2) (hcut : 3*p+P.g N ≤ P.C N) (c : Fin (P.g N) → ZMod p) :
    let Q :=polynomialCombination (sparseCoreFamily P N p) c
    let Qlo :=polynomialCombination (sparseLowCoreFamily P N p) c
    let F :=fun k =>polynomialCombination (sparsePFamily P N p k) c
    let G :=fun k =>polynomialCombination (sparseDFamily P N p k) c
    Q=X^p*Qlo ∧ X*oddPrimeWeight p*F 0=0 ∧ G 0=X^p*Q ∧
      X*oddPrimeWeight p*F 1=(1-X^(2*p))*Q ∧ G 1=Q ∧
      X*oddPrimeWeight p*F 2=2*(1-X^(2*p))*Qlo ∧ G 2=2*Qlo-X^p*Q :=by
  have hmode (d : Fin (P.g N)) : 0<d.val+1 ∧ d.val+1 ≤ P.g N ∧ 3*p+(d.val+1) ≤ P.C N :=by
    have :=d.isLt
    omega
  dsimp only
  have hshift : ∀ d : Fin (P.g N),sparseCoreFamily P N p d=X^p*sparseLowCoreFamily P N p d :=by
    intro d
    simp only [sparseCoreFamily,sparseLowCoreFamily,sparseRowCore_shift P N p (d.val+1) (hmode d).1 (by omega),
      Polynomial.map_mul,Polynomial.map_pow,Polynomial.map_X]
  have hF0 : ∀ d : Fin (P.g N),sparsePFamily P N p 0 d=0 :=by
    intro d
    exact sparseRowPDelta_zero_mod (hmode d).2.1 (hmode d).2.2
  have hG0 : ∀ d : Fin (P.g N),sparseDFamily P N p 0 d=X^p*sparseCoreFamily P N p d :=by
    intro d
    simpa only [sparseDFamily,sparseCoreFamily,Polynomial.map_mul,Polynomial.map_pow,Polynomial.map_X]
      using sparseRowDDelta_zero_mod (hmode d).1 (hmode d).2.1 (hmode d).2.2
  have hF1 : ∀ d : Fin (P.g N),X*oddPrimeWeight p*sparsePFamily P N p 1 d=
      (1-X^(2*p))*sparseCoreFamily P N p d :=by
    intro d
    exact sparseRowPDelta_one_weighted_mod hp2 (hmode d).1 (hmode d).2.1 (hmode d).2.2
  have hG1 : ∀ d : Fin (P.g N),sparseDFamily P N p 1 d=sparseCoreFamily P N p d :=by
    intro d
    exact sparseRowDDelta_one_mod hp2 (hmode d).1 (hmode d).2.1 (hmode d).2.2
  have hF2 : ∀ d : Fin (P.g N),X*oddPrimeWeight p*sparsePFamily P N p 2 d=
      2*(1-X^(2*p))*sparseLowCoreFamily P N p d :=by
    intro d
    exact sparseRowPDelta_two_weighted_mod hp2 (hmode d).1 (hmode d).2.1 (hmode d).2.2
  have hG2 : ∀ d : Fin (P.g N),sparseDFamily P N p 2 d=
      2*sparseLowCoreFamily P N p d-X^p*sparseCoreFamily P N p d :=by
    intro d
    simpa only [sparseDFamily,sparseCoreFamily,sparseLowCoreFamily,Polynomial.map_sub,Polynomial.map_mul,
      Polynomial.map_ofNat,Polynomial.map_pow,Polynomial.map_X]
      using sparseRowDDelta_two_mod hp2 (hmode d).1 (hmode d).2.1 (hmode d).2.2
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · rw [polynomialCombination_congr _ _ c hshift,← polynomialCombination_mul_left]
  · have hz :=polynomialCombination_congr _ _ c hF0
    rw [hz]
    simp [polynomialCombination]
  · rw [polynomialCombination_congr _ _ c hG0,← polynomialCombination_mul_left]
  · rw [polynomialCombination_mul_left,polynomialCombination_congr _ _ c hF1,← polynomialCombination_mul_left]
  · exact polynomialCombination_congr _ _ c hG1
  · rw [polynomialCombination_mul_left,polynomialCombination_congr _ _ c hF2,← polynomialCombination_mul_left]
  · rw [polynomialCombination_congr _ _ c hG2,polynomialCombination_sub,
      ← polynomialCombination_mul_left,← polynomialCombination_mul_left]

def sparseBadCoefficientMap (P : Parameters) (N p : ℕ) [Fact p.Prime] :
    (Fin (P.g N) → ZMod p) →ₗ[ZMod p] (Fin (P.H N-3*p-P.b N) → ZMod p) :=
  polynomialCoefficientMap (sparseCoreFamily P N p) (2*p+P.b N) (P.H N-3*p-P.b N)

theorem sparseCombination_support {P : Parameters} {N p : ℕ} [hp : Fact p.Prime]
    (hcut : 3*p+P.g N ≤ P.C N) (hhi : P.H N ≤ 4*p)
    (c : Fin (P.g N) → ZMod p) (hc : sparseBadCoefficientMap P N p c=0) :
    let Q :=polynomialCombination (sparseCoreFamily P N p) c
    (∀ i,Q.coeff i≠0 → 2*p ≤ i ∧ i<3*p) ∧
      (∀ i,Q.coeff i≠0 → P.L N-p ≤ i ∧ i<2*p+P.b N) :=by
  let Q :=polynomialCombination (sparseCoreFamily P N p) c
  have hp0 :=hp.out.pos
  have hpC : p<P.C N :=by omega
  have hu (d : Fin (P.g N)) (i : ℕ) (hi : P.H N-p ≤ i) :
      (sparseCoreFamily P N p d).coeff i=0 :=by
    simp only [sparseCoreFamily,coeff_map,sparseRowCore_coeff_above P N p (d.val+1) hpC hi,map_zero]
  have hcount : P.H N-p-(2*p+P.b N)=P.H N-3*p-P.b N :=by omega
  have hupper :=polynomialCombination_kernel_support _ c (2*p+P.b N) (P.H N-p)
    (P.H N-3*p-P.b N) hu hcount hc
  have hlower (i : ℕ) (hi : i<P.L N-p) : Q.coeff i=0 :=by
    apply polynomialCombination_coeff_zero
    intro d
    have hd :=d.isLt
    have hC : P.C N=P.L N+P.g N :=rfl
    have hz :=sparseRowCore_coeff_below P N p (d.val+1) (by omega) (by omega) (i:=i) (by omega)
    simp only [sparseCoreFamily,coeff_map,hz,map_zero]
  have hblocklo (i : ℕ) (hi : i<2*p) : Q.coeff i=0 :=by
    apply polynomialCombination_coeff_zero
    intro d
    have hd :=d.isLt
    have hz :=sparseRowCore_coeff_below P N p (d.val+1) (by omega) (by omega) (i:=i) (by omega)
    simp only [sparseCoreFamily,coeff_map,hz,map_zero]
  have hblockhi (i : ℕ) (hi : 3*p ≤ i) : Q.coeff i=0 :=by
    apply polynomialCombination_coeff_zero
    intro d
    exact hu d i (by omega)
  constructor
  · intro i hi
    constructor
    · by_contra hh
      exact hi (hblocklo i (by omega))
    · by_contra hh
      exact hi (hblockhi i (by omega))
  · intro i hi
    constructor
    · by_contra hh
      exact hi (hlower i (by omega))
    · by_contra hh
      exact hi (hupper i (by omega))

end
end CatalanMeasure.Parametric
