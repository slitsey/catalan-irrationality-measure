module
public import CatalanCore.Li2.NVMod.PolynomialSound
public import CatalanCore.Li2.NVMod.PolynomialBound
public import CatalanCore.Li2.NVMod.PolynomialDJ
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
open Polynomial Finset
open scoped BigOperators
namespace CatalanCore.Li2.NVMod.PolynomialCert
open DataSupport
structure Data where
  moments : List (List ℤ)
  u : List ℤ
  v : List ℤ
  k : List ℤ
  degree : ℕ
  bits : ℕ
  kBound : ℕ

def horner (x : ℤ) (xs : List ℤ) : ℤ := xs.foldr (fun c acc=>c+x*acc) 0

def determinantBound (n d p : ℕ) : ℕ := n.factorial*(d+1)^(n-1)*p^n

def residualBound (n p : ℕ) (C : Data) : ℕ :=
  (p+1)*p*determinantBound n C.degree p+(p+1)*p+1+p*C.kBound

def boundsCheck (n p : ℕ) (C : Data) : Bool :=
  decide (C.moments.length=2*n-1 ∧
    C.u.length≤p+1 ∧ C.v.length≤n*C.degree+1) &&
  C.moments.all (fun xs=>decide (xs.length≤C.degree+1) &&
    xs.all (fun c=>decide (|c|≤(p:ℤ)))) &&
  C.u.all (fun c=>decide (|c|≤(p:ℤ))) &&
  C.v.all (fun c=>decide (|c|≤(p:ℤ))) &&
  C.k.all (fun c=>decide (|c|≤(C.kBound:ℤ))) &&
  decide (residualBound n p C<2^C.bits)

def arithmeticCheck (n p : ℕ) (C : Data) : Bool :=
  let x : ℤ:=2^C.bits
  match djEvalZ n (C.moments.map (horner x)) with
  | none=>false
  | some F=>decide (horner x C.u*F+horner x C.v*horner x (List.replicate (p-1) 1)=
      1+(p:ℤ)*horner x C.k)

noncomputable section

def momentPolynomial (C : Data) (e : ℕ) : ℤ[X] := coefficientsPoly (C.moments.getD e [])
def determinantPolynomial (n : ℕ) (C : Data) : ℤ[X] :=
  (Matrix.of fun i j : Fin n=>momentPolynomial C (i.val+j.val)).det

theorem horner_spec (x : ℤ) (xs : List ℤ) :
    horner x xs=(coefficientsPoly xs).eval x := by
  induction xs with
  | nil=>simp [horner,coefficientsPoly]
  | cons a as ih=>simpa [horner,coefficientsPoly] using congrArg (fun z : ℤ=>a+x*z) ih

theorem coefficients_degree (xs : List ℤ) (d : ℕ) (h : xs.length≤d+1) :
    (coefficientsPoly xs).natDegree≤d := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  rw [coefficientsPoly_coeff]
  exact List.getD_eq_default _ _ (by omega)

theorem coefficients_bound (xs : List ℤ) (b : ℤ) (hb : 0≤b)
    (h : ∀ a∈xs,|a|≤b) (j : ℕ) : |(coefficientsPoly xs).coeff j|≤b := by
  rw [coefficientsPoly_coeff]
  by_cases hj : j<xs.length
  · rw [List.getD_eq_getElem _ _ hj]
    exact h _ (List.getElem_mem _)
  · rw [List.getD_eq_default _ _ (by omega),abs_zero]
    exact hb

theorem ones_polynomial (m : ℕ) : coefficientsPoly (List.replicate m (1:ℤ))=
    ∑ j∈range m,X^j := by
  induction m with
  | zero=>simp [coefficientsPoly]
  | succ m ih=>
    rw [List.replicate_succ,coefficientsPoly,ih,Finset.sum_range_succ']
    simp only [Polynomial.C_1,pow_zero,mul_sum,pow_succ']
    ring

theorem determinant_eval (n : ℕ) (C : Data) (x : ℤ) :
    (determinantPolynomial n C).eval x=
      (Matrix.of fun i j : Fin n=>(C.moments.map (horner x)).getD (i.val+j.val) 0).det := by
  rw [determinantPolynomial,eval_det]
  congr 1
  apply Matrix.ext
  intro i j
  change (coefficientsPoly (C.moments.getD (i.val+j.val) [])).eval x=_
  rw [←horner_spec]
  change horner x (C.moments.getD (i.val+j.val) [])=
    (C.moments.map (horner x)).getD (i.val+j.val) 0
  simpa only [horner,List.foldr_nil] using
    (List.getD_map C.moments [] (n:=i.val+j.val) (horner x)).symm

/-- Numerical integer DJ and the supplied Bezout values imply the residual vanishes. -/
theorem arithmetic_eval (n p : ℕ) (C : Data) (h : arithmeticCheck n p C=true) :
    (coefficientsPoly C.u*determinantPolynomial n C+
      coefficientsPoly C.v*residuePolynomial p-1-Polynomial.C (p:ℤ)*coefficientsPoly C.k).eval
        ((2:ℤ)^C.bits)=0 := by
  unfold arithmeticCheck at h
  cases hd : djEvalZ n (C.moments.map (horner ((2:ℤ)^C.bits))) with
  | none=>simp [hd] at h
  | some z=>
    have hh : horner ((2:ℤ)^C.bits) C.u*z+
        horner ((2:ℤ)^C.bits) C.v*horner ((2:ℤ)^C.bits) (List.replicate (p-1) 1)=
          1+(p:ℤ)*horner ((2:ℤ)^C.bits) C.k := by simpa [hd] using h
    have hz := djEvalZ_det n (C.moments.map (horner ((2:ℤ)^C.bits))) z hd
    rw [←determinant_eval] at hz
    simp only [Polynomial.eval_sub,Polynomial.eval_add,Polynomial.eval_mul,
      Polynomial.eval_one,Polynomial.eval_C]
    rw [←horner_spec,←horner_spec,←horner_spec,←hz,
      show residuePolynomial p=coefficientsPoly (List.replicate (p-1) (1:ℤ)) from (ones_polynomial _).symm,
      ←horner_spec]
    linarith

/-- All supplied coefficients, including the quotient of the Bezout identity,
are bounded by the same checked header that selects the radix. -/
theorem bounds_sound (n p : ℕ) (C : Data) (h : boundsCheck n p C=true) :
    ∀ j,|(coefficientsPoly C.u*determinantPolynomial n C+
      coefficientsPoly C.v*residuePolynomial p-1-Polynomial.C (p:ℤ)*coefficientsPoly C.k).coeff j|<
        (2:ℤ)^C.bits := by
  have hb : (C.moments.length=2*n-1 ∧ C.u.length≤p+1 ∧ C.v.length≤n*C.degree+1) ∧
      (∀ xs∈C.moments,xs.length≤C.degree+1 ∧ ∀ c∈xs,|c|≤(p:ℤ)) ∧
      (∀ c∈C.u,|c|≤(p:ℤ)) ∧ (∀ c∈C.v,|c|≤(p:ℤ)) ∧
      (∀ c∈C.k,|c|≤(C.kBound:ℤ)) ∧ residualBound n p C<2^C.bits := by
    simpa [boundsCheck,and_assoc] using h
  have hdet (j : ℕ) : |(determinantPolynomial n C).coeff j|≤
      (determinantBound n C.degree p:ℤ) := by
    have hm (i k : Fin n) : (momentPolynomial C (i.val+k.val)).natDegree≤C.degree ∧
        ∀ j,|(momentPolynomial C (i.val+k.val)).coeff j|≤(p:ℤ) := by
      have hi : i.val+k.val<C.moments.length := by rw [hb.1.1];have hi:=i.isLt;have hk:=k.isLt;omega
      have hh := hb.2.1 (C.moments.getD (i.val+k.val) []) (by
        rw [List.getD_eq_getElem _ _ hi];exact List.getElem_mem hi)
      exact ⟨coefficients_degree _ _ hh.1,coefficients_bound _ _ (by positivity) hh.2⟩
    simpa only [determinantPolynomial,determinantBound,Nat.cast_mul,Nat.cast_pow,
      Nat.cast_add,Nat.cast_one] using det_coeff_bound n C.degree (p:ℤ) (by positivity)
        (Matrix.of fun i k : Fin n=>momentPolynomial C (i.val+k.val)) hm j
  have hu := coefficients_bound C.u (p:ℤ) (by positivity) hb.2.2.1
  have hv := coefficients_bound C.v (p:ℤ) (by positivity) hb.2.2.2.1
  have hk := coefficients_bound C.k (C.kBound:ℤ) (by positivity) hb.2.2.2.2.1
  have hg (j : ℕ) : |(residuePolynomial p).coeff j|≤(1:ℤ) := by
    rw [show residuePolynomial p=coefficientsPoly (List.replicate (p-1) (1:ℤ)) from
      (ones_polynomial _).symm]
    apply coefficients_bound _ _ (by norm_num)
    intro a ha
    simp only [List.mem_replicate] at ha
    rw [ha.2]
    norm_num
  have huf := coeff_mul_bound (coefficientsPoly C.u) (determinantPolynomial n C) p
    (p:ℤ) (determinantBound n C.degree p:ℤ)
    (coefficients_degree _ _ hb.1.2.1) (by positivity) (by positivity) hu hdet
  have hGdeg : (residuePolynomial p).natDegree≤p := by
    rw [show residuePolynomial p=coefficientsPoly (List.replicate (p-1) (1:ℤ)) from
      (ones_polynomial _).symm]
    apply coefficients_degree
    simp only [List.length_replicate]
    omega
  have hvg := coeff_mul_bound (residuePolynomial p) (coefficientsPoly C.v) p
    1 (p:ℤ) hGdeg (by norm_num) (by positivity) hg hv
  intro j
  have hone : |(1:ℤ[X]).coeff j|≤(1:ℤ) := by
    simp only [Polynomial.coeff_one]
    split_ifs <;> norm_num
  have hmul : |(Polynomial.C (p:ℤ)*coefficientsPoly C.k).coeff j|≤(p:ℤ)*C.kBound := by
    rw [Polynomial.coeff_C_mul,abs_mul,abs_of_nonneg (by positivity : (0:ℤ)≤p)]
    exact mul_le_mul_of_nonneg_left (hk j) (by positivity)
  have hl := abs_add_le ((coefficientsPoly C.u*determinantPolynomial n C+
    coefficientsPoly C.v*residuePolynomial p-1).coeff j)
    (-((Polynomial.C (p:ℤ)*coefficientsPoly C.k).coeff j))
  have hl2 := abs_add_le ((coefficientsPoly C.u*determinantPolynomial n C+
    coefficientsPoly C.v*residuePolynomial p).coeff j) (-((1:ℤ[X]).coeff j))
  have hl3 := abs_add_le ((coefficientsPoly C.u*determinantPolynomial n C).coeff j)
    ((coefficientsPoly C.v*residuePolynomial p).coeff j)
  have hle : |(coefficientsPoly C.u*determinantPolynomial n C+
      coefficientsPoly C.v*residuePolynomial p-1-Polynomial.C (p:ℤ)*coefficientsPoly C.k).coeff j|≤
      (residualBound n p C:ℤ) := by
    simp only [Polynomial.coeff_sub,Polynomial.coeff_add,abs_neg,←sub_eq_add_neg] at hl hl2 hl3 ⊢
    have hufj:=huf j
    have hvgj:=hvg j
    rw [mul_comm (residuePolynomial p) (coefficientsPoly C.v)] at hvgj
    simp only [residualBound,Nat.cast_add,Nat.cast_mul,Nat.cast_one] at *
    linarith
  apply hle.trans_lt
  exact_mod_cast hb.2.2.2.2.2

/-- A single integer identity, together with its checked coefficient bound,
is a genuine polynomial identity. -/
theorem polynomial_identity (n p : ℕ) (C : Data)
    (hb : boundsCheck n p C=true) (ha : arithmeticCheck n p C=true) :
    coefficientsPoly C.u*determinantPolynomial n C+
      coefficientsPoly C.v*residuePolynomial p=1+Polynomial.C (p:ℤ)*coefficientsPoly C.k := by
  have hz := radix_zero _ ((2:ℤ)^C.bits) (by positivity) (bounds_sound n p C hb)
    (arithmetic_eval n p C ha)
  linear_combination hz

structure InteriorChecked (I : EndpointInput) where
  data : Data
  bounds : boundsCheck I.key.size I.p data=true
  arithmetic : arithmeticCheck I.key.size I.p data=true
  moments : ∀ e<2*I.key.size-1,
    (momentPolynomial data e).map (Int.castRingHom (ZMod I.p))=
      (I.mz e).map (Int.castRingHom (ZMod I.p))

theorem interior_sound (I : EndpointInput) [Fact I.p.Prime]
    (h : InteriorChecked I) (r : ZMod I.p) (hr : r≠0) (h1 : r≠1) :
    (I.F.map (Int.castRingHom (ZMod I.p))).eval r≠0 := by
  have hh := bezout_nonzero (determinantPolynomial I.key.size h.data)
    (coefficientsPoly h.data.u) (coefficientsPoly h.data.v) (coefficientsPoly h.data.k) I.p
    (polynomial_identity _ _ h.data h.bounds h.arithmetic) r hr h1
  have hm := determinant_mod (n:=I.key.size) (p:=I.p) (momentPolynomial h.data) I.mz h.moments
  change (determinantPolynomial I.key.size h.data).map (Int.castRingHom (ZMod I.p))=
    I.F.map (Int.castRingHom (ZMod I.p)) at hm
  rwa [hm] at hh
#print axioms polynomial_identity
#print axioms interior_sound
end
end CatalanCore.Li2.NVMod.PolynomialCert
