module
public import CatalanCore.Li2.DecayCert.Simple.FixedPoint
public import CatalanCore.Linalg.PackedMatrix
@[expose] public section
set_option Elab.async false
namespace CatalanCore.Li2.DecayCert.Simple
open CatalanCore.Linalg.PackedMatrix
def boxAddList : List FBox → List FBox → List FBox
  | [],ys => ys
  | xs,[] => xs
  | x::xs,y::ys => boxAddF x y::boxAddList xs ys
def synthBoxF (c : FBox) : List FBox → List FBox×FBox
  | [] => ([],boxZero)
  | a::t =>
    let p:=t.foldl (fun (st : List FBox×FBox) b =>
      (st.2::st.1,boxAddF b (boxMulF c st.2))) ([],a)
    (p.1.reverse,p.2)
def tshiftBoxF (c : FBox) : ℕ → List FBox → List FBox
  | 0,_ => []
  | n+1,ds => let p:=synthBoxF c ds; p.2::tshiftBoxF c n p.1
structure IntTaylorModel where
  coeff : List FBox
  remainder : ℤ
  deriving DecidableEq
def modelAddF (a b : IntTaylorModel) : IntTaylorModel :=
  ⟨boxAddList a.coeff b.coeff,a.remainder+b.remainder⟩
def modelScaleF (k : ℤ) (a : IntTaylorModel) : IntTaylorModel :=
  ⟨a.coeff.map (boxScaleF k),(absI k)*a.remainder⟩
def xlogBoxF (sg dir : ℤ) (x0 : FBox) (R : ℤ) (lg : FBox) (J : ℕ) :
    Option IntTaylorModel :=
  if J<2 ∨ R<0 ∨ x0.1≤(absI dir)*R then none else do
    let inv ← boxDivF boxOne x0
    let rho ← boxDivF ((absI dir)*R,(absI dir)*R) x0
    if S≤rho.2 then none else do
      let cs := (List.range (J-1)).foldl (fun (st : List FBox×FBox) i =>
        let j:=i+2
        let a:=boxDivNatF (j*(j-1)) (boxScaleF (sg*(-1:ℤ)^j*dir^j) st.2)
        (a::st.1,boxMulF st.2 inv)) ([],inv)
      let err ← boxDivF (boxDivNatF (J*(J+1)) (boxMulF x0 (boxPowF rho (J+1))))
        (boxSubF boxOne rho)
      pure ⟨boxScaleF sg (boxMulF x0 lg)::
        boxScaleF (sg*dir) (boxAddF lg boxOne)::cs.1.reverse,(absI sg)*max err.2 0⟩
def logAffineBoxF (mass d : FBox) (R : ℤ) (lg : FBox) (J : ℕ) :
    Option IntTaylorModel :=
  if J=0 ∨ R<0 ∨ d.1≤R then none else do
    let inv ← boxDivF boxOne d
    let rho ← boxDivF (R,R) d
    if S≤rho.2 then none else do
      let cs := (List.range J).foldl (fun (st : List FBox×FBox) i =>
        let j:=i+1
        let a:=boxDivNatF j (boxScaleF ((-1:ℤ)^(j+1)) (boxMulF mass st.2))
        (a::st.1,boxMulF st.2 inv)) ([],inv)
      let err ← boxDivF (boxDivNatF (J+1) (boxMulF (boxAbsF mass) (boxPowF rho (J+1))))
        (boxSubF boxOne rho)
      pure ⟨boxMulF mass lg::cs.1.reverse,max err.2 0⟩
/-- Finite MP jets by Horner in t=1/d. MU[k-1] encloses mu_k/k.
The remainder uses |mu_k| <= mass*h^k, once for the whole finite sum. -/
def mpChoose (k j : ℕ) : ℕ := (k+j-1).descFactorial j/j.factorial

theorem mpChoose_eq (k j : ℕ) : mpChoose k j=(k+j-1).choose j :=
  (Nat.choose_eq_descFactorial_div_factorial _ _).symm

def mpBoxF (MU : List FBox) (mass : FBox) (h : ℚ) (d : FBox) (R : ℤ) (J : ℕ) : Option IntTaylorModel :=
  if R<0 ∨ h<0 ∨ J=0 then none else do
    let inv ← boxDivF boxOne d
    let dist:=boxSubF d (boxOfQ h)
    if dist.1≤R then none else do
      let eta ← boxDivF (R,R) dist
      if S≤eta.2 then none else do
        let cs:=(List.range (J+1)).map (fun j=>
          let weights:=MU.zipIdx |>.map (fun a=>boxScaleF (mpChoose (a.2+1) j) a.1)
          let v:=weights.reverse.foldl (fun acc a=>boxMulF (boxAddF acc a) inv) boxZero
          boxScaleF (-2*(-1:ℤ)^j) (boxMulF v (boxPowF inv j)))
        let err ← boxDivF (boxDivNatF (J+1) (boxMulF (boxScaleF 2 (boxAbsF mass)) (boxPowF eta (J+1))))
          (boxSubF boxOne eta)
        pure ⟨cs,max err.2 0⟩

def upMulF (a b : ℤ) : ℤ := ceilDiv (a*b) S
def midF (a : FBox) : ℤ := (a.1+a.2)/2
def widthF (a : FBox) : ℤ := max (midF a-a.1) (a.2-midF a)
/-- Exact ascending-coefficient update for (C+E*u)*p+a. -/
def shiftStepInt (C E : ℤ) : ℤ → List ℤ → List ℤ
  | a,[]=>[a]
  | a,b::bs=>(C*b+a)::shiftStepInt C E (E*b) bs

/-- Homogeneous Taylor shift: coefficients divided by the returned denominator. -/
def shiftMidInt (C E den : ℤ) (ds : List ℤ) : List ℤ×ℤ :=
  ds.foldl (fun st a=>let d:=den*st.2; (shiftStepInt C E (a*d) st.1,d)) ([],1)

/-! Kronecker form of the exact homogeneous shift (coordinator, 18 Nov). The Horner recursion of
`shiftMidInt` is evaluated once at u = R and the coefficients are read back as balanced radix-R
digits (`Linalg.PackedMatrix.signedUnpack`); `kronShift_eq` proves equality under `kronOK`. -/
theorem absI_eq_abs (a : ℤ) : absI a = |a| := by simp [absI, abs_eq_max_neg]

/-- ℓ¹ norm, structural. -/
def kronN1 : List ℤ → ℤ
  | [] => 0
  | a::l => absI a + kronN1 l

/-- Kronecker accumulator: the same Horner recursion evaluated at u = R. -/
def kronAcc (R C E den : ℤ) (ds : List ℤ) : ℤ×ℤ :=
  ds.foldl (fun st a=>let d:=den*st.2; (st.1*(C+E*R)+a*d,d)) (0,1)
def kronShift (R H C E den : ℤ) (ds : List ℤ) : List ℤ×ℤ :=
  let st:=kronAcc R C E den ds
  ((signedUnpack R H ds.length st.1).1,st.2)
def kronOK (R H C E den : ℤ) (ds : List ℤ) : Bool :=
  decide (0<R ∧ 0≤H ∧ 2*H≤R ∧ kronN1 ds*(absI C+absI E+absI den+1)^ds.length<H)

theorem kronN1_nonneg : ∀ l : List ℤ, 0 ≤ kronN1 l
  | [] => le_rfl
  | a::l => by simp only [kronN1, absI_eq_abs]; linarith [abs_nonneg a, kronN1_nonneg l]

theorem kron_le_n1 : ∀ (l : List ℤ) (x : ℤ), x ∈ l → |x| ≤ kronN1 l
  | [],x,h => by simp at h
  | a::l,x,h => by
    simp only [kronN1, absI_eq_abs]
    rcases List.mem_cons.mp h with rfl | h
    · linarith [kronN1_nonneg l]
    · linarith [kron_le_n1 l x h, abs_nonneg a]

theorem kron_pack_step (R C E : ℤ) : ∀ (l : List ℤ) (a : ℤ),
    signedPack R (shiftStepInt C E a l) = (C+E*R)*signedPack R l + a
  | [],a => by simp [shiftStepInt,signedPack]
  | b::bs,a => by
    simp only [shiftStepInt,signedPack]
    rw [kron_pack_step R C E bs (E*b)]; ring

theorem kron_length_step (C E : ℤ) : ∀ (l : List ℤ) (a : ℤ),
    (shiftStepInt C E a l).length = l.length + 1
  | [],a => by simp [shiftStepInt]
  | b::bs,a => by simp [shiftStepInt,kron_length_step C E bs]

theorem kronN1_step (C E : ℤ) : ∀ (l : List ℤ) (a : ℤ),
    kronN1 (shiftStepInt C E a l) ≤ |a| + (|C| + |E|) * kronN1 l
  | [],a => by simp [shiftStepInt, kronN1, absI_eq_abs]
  | b::bs,a => by
    simp only [shiftStepInt, kronN1, absI_eq_abs]
    have h := kronN1_step C E bs (E*b)
    have h1 : |C*b+a| ≤ |C| * |b| + |a| := by
      calc |C*b+a| ≤ |C*b| + |a| := abs_add_le _ _
        _ = _ := by rw [abs_mul]
    have h2 : |E*b| = |E| * |b| := abs_mul _ _
    rw [h2] at h
    nlinarith [abs_nonneg C, abs_nonneg E, abs_nonneg b, kronN1_nonneg bs]

/-- Joint invariant of the two folds, generalized over the start state. -/
theorem kron_fold_inv (R C E den M : ℤ) (hM1 : 1 ≤ M) (hden : |den| ≤ M) (hCE : |C| + |E| ≤ M) :
    ∀ (ds : List ℤ) (l : List ℤ) (v d A : ℤ) (k : ℕ),
      v = signedPack R l → |d| ≤ M^k → kronN1 l ≤ A * M^k → 0 ≤ A →
      (ds.foldl (fun st a=>let d:=den*st.2; (st.1*(C+E*R)+a*d,d)) (v,d)).1 =
          signedPack R (ds.foldl (fun st a=>let d:=den*st.2; (shiftStepInt C E (a*d) st.1,d)) (l,d)).1 ∧
      (ds.foldl (fun st a=>let d:=den*st.2; (st.1*(C+E*R)+a*d,d)) (v,d)).2 =
          (ds.foldl (fun st a=>let d:=den*st.2; (shiftStepInt C E (a*d) st.1,d)) (l,d)).2 ∧
      (ds.foldl (fun st a=>let d:=den*st.2; (shiftStepInt C E (a*d) st.1,d)) (l,d)).1.length =
          l.length + ds.length ∧
      kronN1 (ds.foldl (fun st a=>let d:=den*st.2; (shiftStepInt C E (a*d) st.1,d)) (l,d)).1 ≤
          (A + kronN1 ds) * M^(k + ds.length)
  | [],l,v,d,A,k,hv,hd,hl,hA => by
    simp only [List.foldl_nil, List.length_nil, add_zero, kronN1]
    exact ⟨hv, trivial, trivial, hl⟩
  | a::ds,l,v,d,A,k,hv,hd,hl,hA => by
    simp only [List.foldl_cons]
    have hpk : 0 ≤ M^k := pow_nonneg (by linarith) k
    have hd' : |den*d| ≤ M^(k+1) := by
      rw [abs_mul, pow_succ]
      calc |den| * |d| ≤ M * M^k := mul_le_mul hden hd (abs_nonneg _) (by linarith)
        _ = M^k * M := by ring
    have hl' : kronN1 (shiftStepInt C E (a*(den*d)) l) ≤ (A + |a|) * M^(k+1) := by
      have h := kronN1_step C E l (a*(den*d))
      have hx : |a*(den*d)| ≤ |a| * M^(k+1) := by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left hd' (abs_nonneg a)
      have hy : (|C| + |E|) * kronN1 l ≤ M * (A * M^k) :=
        mul_le_mul hCE hl (kronN1_nonneg l) (by linarith)
      have hz : M * (A * M^k) ≤ A * M^(k+1) := by rw [pow_succ]; nlinarith
      nlinarith
    obtain ⟨h1,h2,h3,h4⟩ := kron_fold_inv R C E den M hM1 hden hCE ds (shiftStepInt C E (a*(den*d)) l)
      (v*(C+E*R)+a*(den*d)) (den*d) (A + |a|) (k+1)
      (by rw [kron_pack_step, hv]; ring) hd' hl' (by linarith [abs_nonneg a])
    refine ⟨h1, h2, ?_, ?_⟩
    · rw [h3, kron_length_step]; simp only [List.length_cons]; omega
    · have e1 : A + |a| + kronN1 ds = A + kronN1 (a::ds) := by simp only [kronN1, absI_eq_abs]; ring
      have e2 : k + 1 + ds.length = k + (a::ds).length := by simp only [List.length_cons]; omega
      rw [e1, e2] at h4; exact h4

/-- Unpacking a pack of in-range digits returns them with zero carry. -/
theorem kron_unpack_pack (R H : ℤ) (hR : 0 < R) : ∀ (q : List ℤ),
    (∀ x ∈ q, DigitRange R H x) → signedUnpack R H q.length (signedPack R q) = (q, 0)
  | [],_ => by simp [signedUnpack,signedPack]
  | a::q,h => by
    have ha := h a (by simp)
    have hq := kron_unpack_pack R H hR q (fun x hx => h x (by simp [hx]))
    dsimp [DigitRange] at ha
    have hd : (a + R*signedPack R q + H) % R - H = a := by
      have : (a + R*signedPack R q + H) % R = (a + H) % R := by
        rw [show a + R*signedPack R q + H = (a + H) + R*signedPack R q by ring, Int.add_mul_emod_self_left]
      rw [this, Int.emod_eq_of_lt (by omega) (by omega)]; ring
    have hq' : (a + R*signedPack R q - a) / R = signedPack R q := by
      rw [show a + R*signedPack R q - a = R*signedPack R q by ring, Int.mul_ediv_cancel_left _ hR.ne']
    simp only [signedUnpack, signedPack, List.length_cons, hd, hq', hq]

theorem kronShift_eq (R H C E den : ℤ) (ds : List ℤ) (hok : kronOK R H C E den ds = true) :
    kronShift R H C E den ds = shiftMidInt C E den ds := by
  simp only [kronOK, decide_eq_true_eq, absI_eq_abs] at hok
  obtain ⟨hR, hH, h2H, hA⟩ := hok
  have hM1 : (1:ℤ) ≤ |C| + |E| + |den| + 1 := by
    linarith [abs_nonneg C, abs_nonneg E, abs_nonneg den]
  obtain ⟨h1, h2, h3, h4⟩ := kron_fold_inv R C E den (|C| + |E| + |den| + 1) hM1
    (by linarith [abs_nonneg C, abs_nonneg E]) (by linarith [abs_nonneg den])
    ds [] 0 1 0 0 (by simp [signedPack]) (by simp) (by simp [kronN1]) le_rfl
  simp only [zero_add, List.length_nil] at h3 h4
  have hrange : ∀ x ∈ (shiftMidInt C E den ds).1, DigitRange R H x := by
    intro x hx
    have hx' := kron_le_n1 _ x hx
    unfold shiftMidInt at hx'
    dsimp [DigitRange]
    constructor <;> linarith [neg_abs_le x, le_abs_self x]
  unfold kronShift kronAcc
  unfold shiftMidInt at hrange ⊢
  dsimp only
  rw [h1, h2]
  have hu := kron_unpack_pack R H hR _ hrange
  rw [h3] at hu
  rw [hu]
/-- Radix of the Kronecker shift used by `midPolyBoxF`. -/
def kronL : ℕ := 4096
/-- The shift used by `midPolyBoxF`: Kronecker when its digit bound holds, exact fold otherwise. -/
def shiftMidK (C E den : ℤ) (ds : List ℤ) : List ℤ×ℤ :=
  if kronOK (2^kronL) (2^(kronL-1)) C E den ds then kronShift (2^kronL) (2^(kronL-1)) C E den ds
  else shiftMidInt C E den ds
theorem shiftMidK_eq (C E den : ℤ) (ds : List ℤ) : shiftMidK C E den ds = shiftMidInt C E den ds := by
  unfold shiftMidK; split
  · exact kronShift_eq _ _ _ _ _ _ (by assumption)
  · rfl

/-- Homogeneous scalar Horner evaluation; result is numerator/denominator. -/
def evalHomInt (n den : ℤ) (ds : List ℤ) : ℤ×ℤ :=
  ds.foldl (fun st a=>let d:=den*st.2; (n*st.1+a*d,d)) (0,1)

/-- Source coefficient uncertainty is bounded once by width. Only J+1 shifted
coefficients are converted to boxes; the discarded tail and source widths are
one exact integer remainder each. All decoded model values have scale S. -/
def midPolyBoxF (ds : List ℤ) (width : ℤ) (c e r : ℚ) (J : ℕ) : Option IntTaylorModel :=
  if width<0 ∨ r<0 then none else
    let den:ℤ:=(c.den:ℤ)*(e.den:ℤ)
    let C:=c.num*(e.den:ℤ)
    let E:=e.num*(c.den:ℤ)
    let sh:=shiftMidK C E den ds
    let co:=(sh.1.take (J+1)).map (fun a=>(a/sh.2,ceilDiv a sh.2))
    let tail:=evalHomInt r.num r.den ((sh.1.drop (J+1)).reverse.map absI)
    let tailBound:=ceilDiv (tail.1*r.num^(J+1)) (tail.2*sh.2*(r.den:ℤ)^(J+1))
    let z:=|c|+|e| *r
    let widths:=evalHomInt z.num z.den (List.replicate ds.length 1)
    let widthBound:=ceilDiv (width*widths.1) widths.2
    some ⟨co,tailBound+widthBound⟩

def qmaxF (a1 a2 R : ℤ) : ℤ :=
  let ep:=ceilDiv (a1*R*S+a2*R*R) (S*S)
  let em:=ceilDiv (-a1*R*S+a2*R*R) (S*S)
  if a2<0 ∧ (absI a1)*S≤-2*a2*R then max (max ep em) (ceilDiv (a1*a1) (-4*a2))
  else max ep em
def modelUpperF (R : ℤ) (m : IntTaylorModel) : ℤ :=
  let a0:=midF (m.coeff[0]?.getD boxZero)
  let a1:=midF (m.coeff[1]?.getD boxZero)
  let a2:=midF (m.coeff[2]?.getD boxZero)
  let tail0:=(m.coeff.drop 3).reverse.foldl
    (fun acc a => |midF a|+upMulF acc R) 0
  let tail:=upMulF (upMulF (upMulF tail0 R) R) R
  let widths:=m.coeff.reverse.foldl (fun acc a => widthF a+upMulF acc R) 0
  a0+qmaxF a1 a2 R+m.remainder+tail+widths

def modelRangeF (radius : ℚ) (m : IntTaylorModel) : ℤ×ℤ :=
  let R:=(boxOfQ radius).2
  (-modelUpperF R ⟨m.coeff.map boxNegF,m.remainder⟩,modelUpperF R m)
def modelValidF (radius : ℚ) (m : IntTaylorModel) : Bool :=
  decide (0≤radius ∧ 0≤m.remainder) && m.coeff.all (fun a=>decide (a.1≤a.2))

theorem modelValidF_spec (radius : ℚ) (m : IntTaylorModel) :
    modelValidF radius m=true ↔ 0≤radius ∧ 0≤m.remainder ∧ ∀a∈m.coeff,a.1≤a.2 := by
  simp only [modelValidF,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true]
  tauto
#print axioms modelValidF_spec

noncomputable section
 def evalIntAsc : List ℤ → ℝ → ℝ
  | [],_=>0
  | a::xs,u=>(a:ℝ)+u*evalIntAsc xs u
 theorem shiftStepInt_value (C E a : ℤ) (xs : List ℤ) (u : ℝ) :
    evalIntAsc (shiftStepInt C E a xs) u=((C:ℝ)+(E:ℝ)*u)*evalIntAsc xs u+(a:ℝ) := by
  induction xs generalizing a with
  | nil=>simp [shiftStepInt,evalIntAsc]
  | cons b xs ih=>
    simp only [shiftStepInt,evalIntAsc,ih,Int.cast_add,Int.cast_mul]
    ring
 theorem shiftMidInt_fold_value (C E den : ℤ) (hden : den≠0) (ds xs : List ℤ)
    (power : ℤ) (v u : ℝ) (h : evalIntAsc xs u=(power:ℝ)*v) :
    let out:=ds.foldl (fun st a=>let d:=den*st.2; (shiftStepInt C E (a*d) st.1,d)) (xs,power)
    evalIntAsc out.1 u=(out.2:ℝ)*ds.foldl (fun acc a=>(((C:ℝ)+(E:ℝ)*u)/(den:ℝ))*acc+(a:ℝ)) v := by
  induction ds generalizing xs power v with
  | nil=>exact h
  | cons a ds ih=>
    simp only [List.foldl_cons]
    apply ih
    rw [shiftStepInt_value,h]
    push_cast
    have hd : (den:ℝ)≠0 := by exact_mod_cast hden
    field_simp
 theorem shiftMidInt_value (C E den : ℤ) (hden : den≠0) (ds : List ℤ) (u : ℝ) :
    evalIntAsc (shiftMidInt C E den ds).1 u=
      ((shiftMidInt C E den ds).2:ℝ)*ds.foldl
        (fun acc a=>(((C:ℝ)+(E:ℝ)*u)/(den:ℝ))*acc+(a:ℝ)) 0 := by
  exact shiftMidInt_fold_value C E den hden ds [] 1 0 u (by simp [evalIntAsc])

 theorem evalHomInt_fold_value (n den : ℤ) (hden : den≠0) (ds : List ℤ)
    (num power : ℤ) (v : ℝ) (h : (num:ℝ)=(power:ℝ)*v) :
    let out:=ds.foldl (fun st a=>let d:=den*st.2; (n*st.1+a*d,d)) (num,power)
    (out.1:ℝ)=(out.2:ℝ)*ds.foldl (fun acc a=>(n:ℝ)/(den:ℝ)*acc+(a:ℝ)) v := by
  induction ds generalizing num power v with
  | nil=>exact h
  | cons a ds ih=>
    simp only [List.foldl_cons]
    apply ih
    push_cast
    rw [h]
    have hd : (den:ℝ)≠0 := by exact_mod_cast hden
    field_simp
 theorem evalHomInt_value (n den : ℤ) (hden : den≠0) (ds : List ℤ) :
    ((evalHomInt n den ds).1:ℝ)=((evalHomInt n den ds).2:ℝ)*
      ds.foldl (fun acc a=>(n:ℝ)/(den:ℝ)*acc+(a:ℝ)) 0 := by
  exact evalHomInt_fold_value n den hden ds 0 1 0 (by simp)
 theorem gridRatio_sound (a den : ℤ) (hd : 0<den) :
    Contains (a/den,ceilDiv a den) ((a:ℝ)/(den:ℝ)/(S:ℝ)) := by
  constructor
  · exact div_le_div_of_nonneg_right (ediv_le_real a den hd) S_real_pos.le
  · exact div_le_div_of_nonneg_right (ceilDiv_ge a den hd.ne') S_real_pos.le
 theorem boxHornerMul_fold_sound (inv : FBox) (t : ℝ) (ht : Contains inv t)
    (boxes : List FBox) (values : List ℝ) (h : List.Forall₂ Contains boxes values)
    (acc : FBox) (a : ℝ) (ha : Contains acc a) :
    Contains (boxes.foldl (fun acc b=>boxMulF (boxAddF acc b) inv) acc)
      (values.foldl (fun a b=>(a+b)*t) a) := by
  induction h generalizing acc a with
  | nil=>exact ha
  | @cons b v bs vs hb hbs ih=>
    apply ih
    exact boxMulF_sound (boxAddF acc b) inv (a+v) t (boxAddF_sound acc b a v ha hb) ht
 theorem boxHornerMul_sound (inv : FBox) (t : ℝ) (ht : Contains inv t)
    (boxes : List FBox) (values : List ℝ) (h : List.Forall₂ Contains boxes values) :
    Contains (boxes.foldl (fun acc b=>boxMulF (boxAddF acc b) inv) boxZero)
      (values.foldl (fun a b=>(a+b)*t) 0) :=
  boxHornerMul_fold_sound inv t ht boxes values h boxZero 0 boxZero_sound
#print axioms shiftStepInt_value
#print axioms shiftMidInt_value
#print axioms shiftMidK_eq
#print axioms evalHomInt_value
#print axioms gridRatio_sound
#print axioms boxHornerMul_sound
end
end CatalanCore.Li2.DecayCert.Simple
