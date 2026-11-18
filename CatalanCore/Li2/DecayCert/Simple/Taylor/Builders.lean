module
public import CatalanCore.Li2.DecayCert.Simple.Taylor.Range
public import CatalanCore.Li2.DecayCert.Simple.Taylor.Analytic
public import CatalanCore.Li2.DecayCert.Lattice.FarMacro
/-! Soundness of the lattice Taylor-box builders (`ModelsF`): `xlogBoxF` encloses `sg·xlog(x+dir·u)`,
`logAffineBoxF` encloses `M·log(x+u)`, and `midPolyBoxF` encloses the Taylor shift `u ↦ q(c+e·u)` of any
polynomial whose coefficients lie within `width` of the integer midpoints, `polyExactF` encloses a Horner
value at `|x| ≤ 1`, and `mpBoxF`/`mpBoxKF` enclose the multipole sum `-2 Σ_k w_k (x+u)^-(k+1)` with the
binomial-majorant remainder. -/
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 1000000
namespace CatalanCore.Li2.DecayCert.Simple
open CatalanCore.Li2.DecayCert.LatticeSimple
noncomputable section

/-- Coefficients of `k·f(d·u)` from those of `f(u)`. -/
def scaledList (k d : ℝ) : List ℝ → List ℝ
  | [] => []
  | c::a => k*c::scaledList (k*d) d a

theorem evalModel_scaledList (d u : ℝ) : ∀ (a : List ℝ) (k : ℝ),
    evalModel (scaledList k d a) u=k*evalModel a (d*u)
  | [], k => by simp [scaledList,evalModel_nil']
  | c::a, k => by
    simp only [scaledList,evalModel_cons,evalModel_scaledList d u a (k*d)]
    ring

theorem scaledList_map (k d : ℝ) (f : ℕ → ℝ) : ∀ (n s : ℕ),
    scaledList (k*d^s) d ((List.range' s n).map f)=(List.range' s n).map (fun j => k*d^j*f j)
  | 0, s => by simp [scaledList]
  | n+1, s => by
    simp only [List.range'_succ,List.map_cons,scaledList]
    rw [show k*d^s*d=k*d^(s+1) by ring,scaledList_map k d f n (s+1)]

theorem contains_pt (q : ℤ) : Contains (q,q) (dec S q) := ⟨le_rfl,le_rfl⟩

theorem range'_map_one {α : Type*} (f : ℕ → α) (n : ℕ) :
    (List.range' 0 (n+1)).map f=f 0::(List.range n).map (fun i => f (i+1)) := by
  rw [List.range'_eq_map_range,List.range_succ_eq_map]
  simp [List.map_map,Function.comp_def,Nat.add_comm]

/-- The jet step of `xlogBoxF`. -/
def xlogStep (sg dir : ℤ) (inv : FBox) (st : List FBox×FBox) (i : ℕ) : List FBox×FBox :=
  let j:=i+2
  (boxDivNatF (j*(j-1)) (boxScaleF (sg*(-1:ℤ)^j*dir^j) st.2)::st.1,boxMulF st.2 inv)

/-- Real value of the jet coefficient of `sg·xlog(x+dir·u)` at `u^j`, `j ≥ 2`. -/
def xlogJet (sg dir : ℤ) (x : ℝ) (j : ℕ) : ℝ :=
  (sg:ℝ)*(dir:ℝ)^j*((-1:ℝ)^j/((j:ℝ)*((j:ℝ)-1)*x^(j-1)))

theorem xlogStep_fold (sg dir : ℤ) (x : ℝ) (hx : 0<x) (inv : FBox) (hinv : Contains inv (1/x)) :
    ∀ n : ℕ, List.Forall₂ Contains ((List.range n).foldl (xlogStep sg dir inv) ([],inv)).1.reverse
        ((List.range n).map (fun i => xlogJet sg dir x (i+2))) ∧
      Contains ((List.range n).foldl (xlogStep sg dir inv) ([],inv)).2 (1/x^(n+1))
  | 0 => by simpa using hinv
  | n+1 => by
    obtain ⟨h1,h2⟩ := xlogStep_fold sg dir x hx inv hinv n
    rw [List.range_succ,List.foldl_append,List.map_append]
    simp only [List.foldl_cons,List.foldl_nil,xlogStep,List.reverse_cons,List.map_cons,List.map_nil]
    refine ⟨List.rel_append h1 (List.Forall₂.cons ?_ List.Forall₂.nil),?_⟩
    · have hn : (0:ℕ)<(n+2)*(n+2-1) := Nat.mul_pos (by omega) (by omega)
      have h := boxDivNatF_sound _ hn _ _ (boxScaleF_sound (sg*(-1:ℤ)^(n+2)*dir^(n+2)) _ _ h2)
      simp only [show n+2-1=n+1 from rfl] at h ⊢
      convert h using 1
      unfold xlogJet
      have hx0 : x ≠ 0 := hx.ne'
      simp only [show n+2-1=n+1 from rfl]
      have hn1 : (n:ℝ)+1 ≠ 0 := by positivity
      have hn2 : (n:ℝ)+2 ≠ 0 := by positivity
      have hxn : x^(n+1) ≠ 0 := pow_ne_zero _ hx0
      push_cast
      rw [show ((n:ℝ)+2-1) = (n:ℝ)+1 by ring]
      field_simp
      try ring
    · have h := boxMulF_sound _ _ _ _ h2 hinv
      convert h using 1
      field_simp
      ring

#print axioms xlogStep_fold

theorem xlogCoeff_val (x r : ℚ) (J : ℕ) (j : ℕ) (hj : j<J+1) :
    (xlogScalarCoeff x 1 8 j).value=
      if j=0 then (x:ℝ)*Real.log (x:ℝ)
      else if j=1 then Real.log (x:ℝ)+1
      else (((-1:ℚ)^j/((j:ℚ)*(j-1)*x^(j-1)):ℚ):ℝ) := by
  have h := xlogModel_coeff x r J 8 j hj
  have he : seGet (xlogModel x r J 8).coeff j=xlogScalarCoeff x 1 8 j := by
    simp [xlogModel,seGet,hj]
  rwa [he] at h

/-- `xlogBoxF` encloses `sg·xlog(x+dir·u)` on `|u| ≤ R/S`. -/
theorem xlogBoxF_sound (sg dir : ℤ) (x0 : FBox) (R : ℤ) (lg : FBox) (J : ℕ) (x : ℚ)
    (hx : Contains x0 (x:ℝ)) (hlg : Contains lg (Real.log (x:ℝ))) (m : IntTaylorModel)
    (hm : xlogBoxF sg dir x0 R lg J=some m) :
    ModelsF m (dec S R) (fun u => (sg:ℝ)*xlog ((x:ℝ)+(dir:ℝ)*u)) := by
  unfold xlogBoxF at hm
  split_ifs at hm with hg
  push_neg at hg
  obtain ⟨hJ,hR,hxR⟩ := hg
  cases hinv : boxDivF boxOne x0 with
  | none => simp [hinv,bind,Option.bind] at hm
  | some inv =>
  cases hrho : boxDivF (absI dir*R,absI dir*R) x0 with
  | none => simp [hinv,hrho,bind,Option.bind] at hm
  | some rho =>
  simp only [hinv,hrho,bind,Option.bind] at hm
  split_ifs at hm with hS
  cases herr : boxDivF (boxDivNatF (J*(J+1)) (boxMulF x0 (boxPowF rho (J+1)))) (boxSubF boxOne rho) with
  | none => simp [herr] at hm
  | some err =>
  simp only [herr,Option.pure_def,Option.some.injEq] at hm
  subst hm
  -- real facts
  have hSR : (0:ℝ)<(S:ℝ) := S_real_pos
  set r : ℚ := ((absI dir*R:ℤ):ℚ)/(S:ℚ) with hr
  have hrR : (r:ℝ)=dec S (absI dir*R) := by rw [hr]; unfold dec; push_cast; ring
  have hx1 : dec S x0.1 ≤ (x:ℝ) := hx.1
  have hlt : dec S (absI dir*R) < dec S x0.1 := by
    unfold dec; exact (div_lt_div_iff_of_pos_right hSR).2 (by exact_mod_cast hxR)
  have hdR : 0 ≤ absI dir*R := mul_nonneg (by rw [absI_eq_abs]; exact abs_nonneg _) hR
  have hr0 : (0:ℚ) ≤ r := by
    have : (0:ℝ) ≤ (r:ℝ) := by rw [hrR]; unfold dec; exact div_nonneg (by exact_mod_cast hdR) hSR.le
    exact_mod_cast this
  have hra : r<x := by
    have : (r:ℝ)<(x:ℝ) := by rw [hrR]; linarith
    exact_mod_cast this
  have hxpos : (0:ℝ)<(x:ℝ) := by
    have : (0:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr0
    have : (r:ℝ)<(x:ℝ) := by exact_mod_cast hra
    linarith
  have hM := xlogModel_sound x r J 8 hJ hr0 hra
  set cv := (xlogModel x r J 8).coeff.map ScalarExpr.value with hcvdef
  have hinvC : Contains inv (1/(x:ℝ)) := boxDivF_sound _ _ _ _ _ boxOne_sound hx hinv
  have hrhoC : Contains rho ((r:ℝ)/(x:ℝ)) := by
    rw [hrR]; exact boxDivF_sound _ _ _ _ _ (contains_pt _) hx hrho
  -- coefficients
  have hcv : cv=(List.range (J+1)).map (fun j => (xlogScalarCoeff x 1 8 j).value) := by
    simp only [hcvdef,xlogModel,List.map_map]; rfl
  refine ⟨scaledList sg dir cv,?_,?_⟩
  · obtain ⟨n,rfl⟩ : ∃ n, J=n+1 := ⟨J-1,by omega⟩
    have hfold := (xlogStep_fold sg dir (x:ℝ) hxpos inv hinvC n).1
    have hsc : scaledList (sg:ℝ) (dir:ℝ) cv=(List.range' 0 (n+2)).map
        (fun j => (sg:ℝ)*(dir:ℝ)^j*(xlogScalarCoeff x 1 8 j).value) := by
      have h := scaledList_map (sg:ℝ) (dir:ℝ) (fun j => (xlogScalarCoeff x 1 8 j).value) (n+2) 0
      rw [pow_zero,mul_one] at h
      rw [hcv,List.range_eq_range']
      exact h
    rw [hsc]
    simp only [List.range'_succ,List.map_cons]
    refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ ?_)
    · rw [xlogCoeff_val x r (n+1) 0 (by omega)]
      simp only [↓reduceIte,pow_zero,mul_one]
      exact boxScaleF_sound _ _ _ (boxMulF_sound _ _ _ _ hx hlg)
    · rw [xlogCoeff_val x r (n+1) 1 (by omega)]
      simp only [one_ne_zero,↓reduceIte,pow_one]
      have h := boxScaleF_sound (sg*dir) _ _ (boxAddF_sound _ _ _ _ hlg boxOne_sound)
      push_cast at h
      convert h using 1
      ring
    · convert hfold using 1
      · simp only [Nat.add_sub_cancel]; rfl
      rw [List.range'_eq_map_range,List.map_map]
      apply List.map_congr_left
      intro i hi
      simp only [Function.comp_apply]
      rw [xlogCoeff_val x r (n+1) (0+1+1+i) (by simp at hi; omega)]
      rw [if_neg (by omega),if_neg (by omega)]
      unfold xlogJet
      rw [show 0+1+1+i=i+2 by omega]
      push_cast
      ring_nf
  · intro u hu
    show |(sg:ℝ)*xlog ((x:ℝ)+(dir:ℝ)*u)-evalModel (scaledList (sg:ℝ) (dir:ℝ) cv) u| ≤
      dec S ((absI sg)*max err.2 0)
    rw [evalModel_scaledList]
    have hdu : |(dir:ℝ)*u| ≤ (r:ℝ) := by
      rw [abs_mul,hrR]
      have : dec S (absI dir*R)=|(dir:ℝ)| * dec S R := by
        unfold dec; rw [absI_eq_abs]; push_cast; ring
      rw [this]; exact mul_le_mul_of_nonneg_left hu (abs_nonneg _)
    have h1 : |xlog ((x:ℝ)+(dir:ℝ)*u)-evalModel cv ((dir:ℝ)*u)| ≤ (xlogError x r J:ℝ) :=
      hM.2.2 _ hdu
    have hpow := boxPowF_sound rho _ hrhoC (J+1)
    have hnum := boxMulF_sound x0 _ _ _ hx hpow
    have hJJ : 0<J*(J+1) := Nat.mul_pos (by omega) (by omega)
    have hdiv := boxDivNatF_sound _ hJJ _ _ hnum
    have hden := boxSubF_sound boxOne rho 1 _ boxOne_sound hrhoC
    have hE := boxDivF_sound _ _ _ _ _ hdiv hden herr
    have hEq : (xlogError x r J:ℝ)=(x:ℝ)*((r:ℝ)/(x:ℝ))^(J+1)/(((J*(J+1):ℕ):ℝ))/(1-(r:ℝ)/(x:ℝ)) := by
      unfold xlogError; push_cast; rw [div_div]; congr 1; ring
    have hle : (xlogError x r J:ℝ) ≤ dec S (max err.2 0) := by
      rw [hEq]
      refine hE.2.trans ?_
      unfold dec
      exact div_le_div_of_nonneg_right (by exact_mod_cast le_max_left _ _) hSR.le
    calc |(sg:ℝ)*xlog ((x:ℝ)+(dir:ℝ)*u)-(sg:ℝ)*evalModel cv ((dir:ℝ)*u)|
        = |(sg:ℝ)| * |xlog ((x:ℝ)+(dir:ℝ)*u)-evalModel cv ((dir:ℝ)*u)| := by rw [← mul_sub,abs_mul]
      _ ≤ |(sg:ℝ)| * dec S (max err.2 0) := mul_le_mul_of_nonneg_left (h1.trans hle) (abs_nonneg _)
      _ = dec S ((absI sg)*max err.2 0) := by unfold dec; rw [absI_eq_abs]; push_cast; ring

#print axioms xlogBoxF_sound

/-- The jet step of `logAffineBoxF`. -/
def logStep (mass inv : FBox) (st : List FBox×FBox) (i : ℕ) : List FBox×FBox :=
  let j:=i+1
  (boxDivNatF j (boxScaleF ((-1:ℤ)^(j+1)) (boxMulF mass st.2))::st.1,boxMulF st.2 inv)

/-- Real value of the jet coefficient of `M·log(x+u)` at `u^j`, `j ≥ 1`. -/
def logJet (M x : ℝ) (j : ℕ) : ℝ := M*((-1:ℝ)^(j+1)/((j:ℝ)*x^j))

theorem logStep_fold (mass : FBox) (M x : ℝ) (hM : Contains mass M) (hx : 0<x) (inv : FBox)
    (hinv : Contains inv (1/x)) :
    ∀ n : ℕ, List.Forall₂ Contains ((List.range n).foldl (logStep mass inv) ([],inv)).1.reverse
        ((List.range n).map (fun i => logJet M x (i+1))) ∧
      Contains ((List.range n).foldl (logStep mass inv) ([],inv)).2 (1/x^(n+1))
  | 0 => by simpa using hinv
  | n+1 => by
    obtain ⟨h1,h2⟩ := logStep_fold mass M x hM hx inv hinv n
    rw [List.range_succ,List.foldl_append,List.map_append]
    simp only [List.foldl_cons,List.foldl_nil,logStep,List.reverse_cons,List.map_cons,List.map_nil]
    refine ⟨List.rel_append h1 (List.Forall₂.cons ?_ List.Forall₂.nil),?_⟩
    · have h := boxDivNatF_sound (n+1) (by omega) _ _
        (boxScaleF_sound ((-1:ℤ)^(n+1+1)) _ _ (boxMulF_sound _ _ _ _ hM h2))
      convert h using 1
      unfold logJet
      have hx0 : x ≠ 0 := hx.ne'
      have hn1 : (n:ℝ)+1 ≠ 0 := by positivity
      push_cast
      field_simp
      try ring
    · have h := boxMulF_sound _ _ _ _ h2 hinv
      convert h using 1
      field_simp
      ring

theorem logAffineCoeff_real (x : ℝ) (j : ℕ) (hj : j ≠ 0) :
    logAffineCoeff (x:ℂ) 1 j=(-1:ℝ)^(j+1)/((j:ℝ)*x^j) := by
  simp only [logAffineCoeff,hj,ite_false,logUnitCoeff]
  have he : -(-1:ℂ)^j/(j:ℂ)*(1/(x:ℂ))^j=(((-1:ℝ)^(j+1)/((j:ℝ)*x^j):ℝ):ℂ) := by
    push_cast; rw [pow_succ,div_pow,one_pow]; ring
  rw [he,Complex.ofReal_re]

/-- `logAffineBoxF` encloses `M·log(x+u)` on `|u| ≤ R/S`. -/
theorem logAffineBoxF_sound (mass d : FBox) (R : ℤ) (lg : FBox) (J : ℕ) (M x : ℝ)
    (hM : Contains mass M) (hx : Contains d x) (hlg : Contains lg (Real.log x)) (m : IntTaylorModel)
    (hm : logAffineBoxF mass d R lg J=some m) :
    ModelsF m (dec S R) (fun u => M*Real.log (x+u)) := by
  unfold logAffineBoxF at hm
  split_ifs at hm with hg
  push_neg at hg
  obtain ⟨hJ,hR,hxR⟩ := hg
  cases hinv : boxDivF boxOne d with
  | none => simp [hinv,bind,Option.bind] at hm
  | some inv =>
  cases hrho : boxDivF (R,R) d with
  | none => simp [hinv,hrho,bind,Option.bind] at hm
  | some rho =>
  simp only [hinv,hrho,bind,Option.bind] at hm
  split_ifs at hm with hS
  cases herr : boxDivF (boxDivNatF (J+1) (boxMulF (boxAbsF mass) (boxPowF rho (J+1)))) (boxSubF boxOne rho) with
  | none => simp [herr] at hm
  | some err =>
  simp only [herr,Option.pure_def,Option.some.injEq] at hm
  subst hm
  have hSR : (0:ℝ)<(S:ℝ) := S_real_pos
  set r : ℝ := dec S R with hr
  have hr0 : 0 ≤ r := by rw [hr]; unfold dec; exact div_nonneg (by exact_mod_cast hR) hSR.le
  have hrx : r<x := by
    have : dec S R<dec S d.1 := by
      unfold dec; exact (div_lt_div_iff_of_pos_right hSR).2 (by exact_mod_cast hxR)
    linarith [hx.1]
  have hxpos : 0<x := hr0.trans_lt hrx
  have hT := logAffine_taylor_remainder (x:ℂ) 1 r hr0 (by simpa [abs_of_pos hxpos] using hrx) J
  simp only [norm_one,one_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hxpos] at hT
  set cv := (List.range (J+1)).map (logAffineCoeff (x:ℂ) 1) with hcv
  have hinvC : Contains inv (1/x) := boxDivF_sound _ _ _ _ _ boxOne_sound hx hinv
  have hrhoC : Contains rho (r/x) := boxDivF_sound _ _ _ _ _ (contains_pt _) hx hrho
  refine ⟨scaledList M 1 cv,?_,?_⟩
  · obtain ⟨n,rfl⟩ : ∃ n, J=n+1 := ⟨J-1,by omega⟩
    have hfold := (logStep_fold mass M x hM hxpos inv hinvC (n+1)).1
    have hsc : scaledList M 1 cv=(List.range' 0 (n+2)).map (fun j => M*1^j*logAffineCoeff (x:ℂ) 1 j) := by
      have h := scaledList_map M 1 (fun j => logAffineCoeff (x:ℂ) 1 j) (n+2) 0
      rw [pow_zero,mul_one] at h
      rw [hcv,List.range_eq_range']
      exact h
    rw [hsc,range'_map_one]
    refine List.Forall₂.cons ?_ ?_
    · simp only [pow_zero,mul_one,logAffineCoeff,↓reduceIte,Complex.norm_real,Real.norm_eq_abs,
        abs_of_pos hxpos]
      exact boxMulF_sound _ _ _ _ hM hlg
    · convert hfold using 1
      · rfl
      apply List.map_congr_left
      intro i hi
      simp only [one_pow,mul_one]
      rw [logAffineCoeff_real x (i+1) (by omega)]
      rfl
  · intro u hu
    show |M*Real.log (x+u)-evalModel (scaledList M 1 cv) u| ≤ dec S (max err.2 0)
    rw [evalModel_scaledList,one_mul]
    have h1 := hT.2.2 u hu
    have hlog : Real.log ‖(x:ℂ)+(u:ℂ)‖=Real.log (x+u) := by
      have hxu : 0 ≤ x+u := by linarith [(abs_le.mp hu).1]
      rw [← Complex.ofReal_add,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hxu]
    simp only at h1
    rw [hlog] at h1
    have hpow := boxPowF_sound rho _ hrhoC (J+1)
    have hnum := boxMulF_sound _ _ _ _ (boxAbsF_sound _ _ hM) hpow
    have hdiv := boxDivNatF_sound (J+1) (by omega) _ _ hnum
    have hden := boxSubF_sound boxOne rho 1 _ boxOne_sound hrhoC
    have hE := boxDivF_sound _ _ _ _ _ hdiv hden herr
    have hle : |M| * ((r/x)^(J+1)/(((J+1:ℕ):ℝ)*(1-r/x))) ≤ dec S (max err.2 0) := by
      have he : |M| * ((r/x)^(J+1)/(((J+1:ℕ):ℝ)*(1-r/x)))=|M| * (r/x)^(J+1)/((J+1:ℕ):ℝ)/(1-r/x) := by
        rw [div_div,mul_div_assoc]
      rw [he]
      refine hE.2.trans ?_
      unfold dec
      exact div_le_div_of_nonneg_right (by exact_mod_cast le_max_left _ _) hSR.le
    calc |M*Real.log (x+u)-M*evalModel cv u| = |M| * |Real.log (x+u)-evalModel cv u| := by
          rw [← mul_sub,abs_mul]
      _ ≤ |M| * ((r/x)^(J+1)/(((J+1:ℕ):ℝ)*(1-r/x))) := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      _ ≤ _ := hle

#print axioms logAffineBoxF_sound

/-! ### `midPolyBoxF` -/

/-! ### `midPolyBoxF`: Taylor shift of a polynomial known to within `width` per coefficient -/

theorem evalIntAsc_split (u : ℝ) : ∀ (k : ℕ) (L : List ℤ),
    evalIntAsc L u=evalIntAsc (L.take k) u+u^k*evalIntAsc (L.drop k) u
  | 0, L => by simp [evalIntAsc]
  | k+1, [] => by simp [evalIntAsc]
  | k+1, a::L => by
    simp only [List.take_succ_cons,List.drop_succ_cons,evalIntAsc]
    rw [evalIntAsc_split u k L]
    ring

theorem evalIntAsc_abs_le (u r : ℝ) (hu : |u| ≤ r) : ∀ L : List ℤ,
    |evalIntAsc L u| ≤ evalIntAsc (L.map absI) r
  | [] => by simp [evalIntAsc]
  | a::L => by
    simp only [List.map_cons,evalIntAsc]
    have ih := evalIntAsc_abs_le u r hu L
    have hr : 0 ≤ r := (abs_nonneg u).trans hu
    rw [absI_eq_abs]
    push_cast
    calc |(a:ℝ)+u*evalIntAsc L u| ≤ |(a:ℝ)|+|u| *|evalIntAsc L u| := by
          rw [← abs_mul]; exact abs_add_le _ _
      _ ≤ |(a:ℝ)|+r*evalIntAsc (L.map absI) r := by
          have := mul_le_mul hu ih (abs_nonneg _) hr
          linarith

theorem foldl_reverse_evalIntAsc (x : ℝ) (L : List ℤ) :
    L.reverse.foldl (fun acc (a:ℤ) => x*acc+(a:ℝ)) 0=evalIntAsc L x := by
  rw [List.foldl_reverse]
  induction L with
  | nil => simp [evalIntAsc]
  | cons a L ih => simp only [List.foldr_cons,evalIntAsc,ih]; ring

theorem evalModel_map_div (k u : ℝ) : ∀ L : List ℤ,
    evalModel (L.map (fun (a:ℤ) => (a:ℝ)/k)) u=evalIntAsc L u/k
  | [] => by simp [evalModel_nil',evalIntAsc]
  | a::L => by
    simp only [List.map_cons,evalModel_cons,evalIntAsc,evalModel_map_div k u L]
    ring

theorem shiftMidInt_snd (C E den : ℤ) : ∀ (ds : List ℤ) (xs : List ℤ) (p : ℤ),
    (ds.foldl (fun st a=>let d:=den*st.2; (shiftStepInt C E (a*d) st.1,d)) (xs,p)).2=den^ds.length*p
  | [], xs, p => by simp
  | a::ds, xs, p => by
    simp only [List.foldl_cons,List.length_cons]
    rw [shiftMidInt_snd C E den ds]
    ring

theorem evalHomInt_snd (n den : ℤ) : ∀ (ds : List ℤ) (num p : ℤ),
    (ds.foldl (fun st a=>let d:=den*st.2; (n*st.1+a*d,d)) (num,p)).2=den^ds.length*p
  | [], num, p => by simp
  | a::ds, num, p => by
    simp only [List.foldl_cons,List.length_cons]
    rw [evalHomInt_snd n den ds]
    ring

theorem foldl_replicate_one (x : ℝ) : ∀ (n : ℕ) (acc : ℝ),
    (List.replicate n (1:ℤ)).foldl (fun acc (a:ℤ) => x*acc+(a:ℝ)) acc=x^n*acc+∑ k ∈ Finset.range n,x^k
  | 0, acc => by simp
  | n+1, acc => by
    rw [List.replicate_succ,List.foldl_cons,foldl_replicate_one x n,Finset.sum_range_succ]
    push_cast
    ring

/-- Coefficientwise perturbation of a descending Horner evaluation. -/
theorem horner_perturb (t w : ℝ) (ds : List ℤ) (q : List ℝ)
    (hq : List.Forall₂ (fun a x => |x-dec S a| ≤ w) ds q) :
    ∀ acc1 acc2 : ℝ, |q.foldl (fun acc b => t*acc+b) acc1-ds.foldl (fun acc a => t*acc+dec S a) acc2| ≤
      |t|^ds.length*|acc1-acc2|+w*∑ k ∈ Finset.range ds.length,|t|^k := by
  induction hq with
  | nil => intro acc1 acc2; simp
  | @cons a x ds q hax _ ih =>
    intro acc1 acc2
    simp only [List.foldl_cons,List.length_cons]
    refine (ih _ _).trans ?_
    have hw : 0 ≤ w := (abs_nonneg _).trans hax
    have h1 : |t*acc1+x-(t*acc2+dec S a)| ≤ |t| *|acc1-acc2|+w := by
      have : t*acc1+x-(t*acc2+dec S a)=t*(acc1-acc2)+(x-dec S a) := by ring
      rw [this]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul]
      linarith
    have hp : 0 ≤ |t|^ds.length := by positivity
    calc |t|^ds.length*|t*acc1+x-(t*acc2+dec S a)|+w*∑ k ∈ Finset.range ds.length,|t|^k
        ≤ |t|^ds.length*(|t| *|acc1-acc2|+w)+w*∑ k ∈ Finset.range ds.length,|t|^k := by
          gcongr
      _ = |t|^(ds.length+1)*|acc1-acc2|+w*∑ k ∈ Finset.range (ds.length+1),|t|^k := by
          rw [Finset.sum_range_succ]; ring

theorem foldl_dec (t : ℝ) : ∀ (ds : List ℤ) (acc : ℝ),
    ds.foldl (fun acc (a:ℤ) => t*acc+dec S a) (acc/(S:ℝ))=(ds.foldl (fun acc (a:ℤ) => t*acc+(a:ℝ)) acc)/(S:ℝ)
  | [], acc => by simp
  | a::ds, acc => by
    simp only [List.foldl_cons]
    rw [← foldl_dec t ds]
    congr 1
    unfold dec
    ring

/-- `shiftMidInt_value` with a typed fold (no coerced list). -/
theorem shiftMidInt_val (C E den : ℤ) (hden : den≠0) (ds : List ℤ) (u : ℝ) :
    evalIntAsc (shiftMidInt C E den ds).1 u=((shiftMidInt C E den ds).2:ℝ)*
      ds.foldl (fun acc (a:ℤ) => (((C:ℝ)+(E:ℝ)*u)/(den:ℝ))*acc+(a:ℝ)) 0 := by
  have key : ∀ (ds xs : List ℤ) (power : ℤ) (v : ℝ), evalIntAsc xs u=(power:ℝ)*v →
      evalIntAsc (ds.foldl (fun st a=>let d:=den*st.2; (shiftStepInt C E (a*d) st.1,d)) (xs,power)).1 u=
      ((ds.foldl (fun st a=>let d:=den*st.2; (shiftStepInt C E (a*d) st.1,d)) (xs,power)).2:ℝ)*
        ds.foldl (fun acc (a:ℤ) => (((C:ℝ)+(E:ℝ)*u)/(den:ℝ))*acc+(a:ℝ)) v := by
    intro ds
    induction ds with
    | nil => intro xs power v h; exact h
    | cons a ds ih =>
      intro xs power v h
      simp only [List.foldl_cons]
      apply ih
      rw [shiftStepInt_value,h]
      push_cast
      have hd : (den:ℝ)≠0 := by exact_mod_cast hden
      field_simp
  exact key ds [] 1 0 (by simp [evalIntAsc])

/-- `evalHomInt_value` with a typed fold (no coerced list). -/
theorem evalHomInt_val (n den : ℤ) (hden : den≠0) (ds : List ℤ) :
    ((evalHomInt n den ds).1:ℝ)=((evalHomInt n den ds).2:ℝ)*
      ds.foldl (fun acc (a:ℤ) => (n:ℝ)/(den:ℝ)*acc+(a:ℝ)) 0 := by
  have key : ∀ (ds : List ℤ) (num power : ℤ) (v : ℝ), (num:ℝ)=(power:ℝ)*v →
      ((ds.foldl (fun st a=>let d:=den*st.2; (n*st.1+a*d,d)) (num,power)).1:ℝ)=
      ((ds.foldl (fun st a=>let d:=den*st.2; (n*st.1+a*d,d)) (num,power)).2:ℝ)*
        ds.foldl (fun acc (a:ℤ) => (n:ℝ)/(den:ℝ)*acc+(a:ℝ)) v := by
    intro ds
    induction ds with
    | nil => intro num power v h; exact h
    | cons a ds ih =>
      intro num power v h
      simp only [List.foldl_cons]
      apply ih
      push_cast
      rw [h]
      have hd : (den:ℝ)≠0 := by exact_mod_cast hden
      field_simp
  exact key ds 0 1 0 (by simp)

/-- `midPolyBoxF` encloses `u ↦ q(c+e·u)` on `|u| ≤ r`, for any real descending coefficient list `q`
within `width/S` of the integer midpoints `ds/S`. -/
theorem midPolyBoxF_sound (ds : List ℤ) (width : ℤ) (c e r : ℚ) (J : ℕ) (q : List ℝ)
    (hq : List.Forall₂ (fun a x => |x-dec S a| ≤ dec S width) ds q) (m : IntTaylorModel)
    (hm : midPolyBoxF ds width c e r J=some m) :
    ModelsF m (r:ℝ) (fun u => q.foldl (fun acc b => ((c:ℝ)+(e:ℝ)*u)*acc+b) 0) := by
  unfold midPolyBoxF at hm
  split_ifs at hm with hg
  push_neg at hg
  obtain ⟨hw,hr⟩ := hg
  simp only [Option.some.injEq] at hm
  subst hm
  rw [shiftMidK_eq]
  have hSR : (0:ℝ)<(S:ℝ) := S_real_pos
  have hden : (0:ℤ)<(c.den:ℤ)*(e.den:ℤ) := by positivity
  set den : ℤ := (c.den:ℤ)*(e.den:ℤ) with hdendef
  set C : ℤ := c.num*(e.den:ℤ) with hC
  set E : ℤ := e.num*(c.den:ℤ) with hE
  set sh := shiftMidInt C E den ds with hsh
  have hsh2 : 0<sh.2 := by
    rw [hsh,shiftMidInt,shiftMidInt_snd]; simp only [mul_one]; positivity
  have hsh2R : (0:ℝ)<(sh.2:ℝ) := by exact_mod_cast hsh2
  refine ⟨(sh.1.take (J+1)).map (fun (a:ℤ) => (a:ℝ)/((sh.2:ℝ)*(S:ℝ))),?_,?_⟩
  · rw [List.forall₂_map_left_iff,List.forall₂_map_right_iff,List.forall₂_same]
    intro a _
    rw [← div_div]
    exact gridRatio_sound a sh.2 hsh2
  · intro u hu
    have hr0 : (0:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
    set t : ℝ := (c:ℝ)+(e:ℝ)*u with ht
    have hCE : ((C:ℝ)+(E:ℝ)*u)/(den:ℝ)=t := by
      rw [ht,hC,hE,hdendef]
      have hc : (c:ℝ)=(c.num:ℝ)/(c.den:ℝ) := Rat.cast_def c
      have he : (e:ℝ)=(e.num:ℝ)/(e.den:ℝ) := Rat.cast_def e
      have hcd : (c.den:ℝ) ≠ 0 := by positivity
      have hed : (e.den:ℝ) ≠ 0 := by positivity
      rw [hc,he]
      push_cast
      field_simp
    -- exact shift value
    have hval := shiftMidInt_val C E den hden.ne' ds u
    rw [← hsh,hCE] at hval
    -- P(t) = ds-Horner at t with coefficients ds/S
    have hP : ds.foldl (fun acc a => t*acc+dec S a) 0=evalIntAsc sh.1 u/((sh.2:ℝ)*(S:ℝ)) := by
      have := foldl_dec t ds 0
      rw [zero_div] at this
      rw [this,hval]
      field_simp
    have hsplit := evalIntAsc_split u (J+1) sh.1
    have hmod := evalModel_map_div ((sh.2:ℝ)*(S:ℝ)) u (sh.1.take (J+1))
    -- width part
    have hpert := horner_perturb t (dec S width) ds q hq 0 0
    simp only [sub_self,abs_zero,mul_zero,zero_add] at hpert
    set z : ℚ := |c|+|e| *r with hz
    have htz : |t| ≤ (z:ℝ) := by
      rw [ht,hz]; push_cast
      have h1 := abs_add_le (c:ℝ) ((e:ℝ)*u)
      rw [abs_mul] at h1
      have h2 := mul_le_mul_of_nonneg_left hu (abs_nonneg (e:ℝ))
      linarith
    have hsumz : ∑ k ∈ Finset.range ds.length,|t|^k ≤ ∑ k ∈ Finset.range ds.length,(z:ℝ)^k :=
      Finset.sum_le_sum (fun k _ => pow_le_pow_left₀ (abs_nonneg _) htz k)
    have hz0 : (0:ℤ) < (z.den:ℤ) := by positivity
    have hwid := evalHomInt_val z.num (z.den:ℤ) hz0.ne' (List.replicate ds.length 1)
    rw [foldl_replicate_one,mul_zero,zero_add] at hwid
    have hzr : ((z.num:ℝ)/((z.den:ℤ):ℝ))=(z:ℝ) := by
      rw [Rat.cast_def]; push_cast; rfl
    rw [hzr] at hwid
    have hw2 : (0:ℤ)<(evalHomInt z.num (z.den:ℤ) (List.replicate ds.length 1)).2 := by
      unfold evalHomInt; rw [evalHomInt_snd]; simp only [mul_one]; positivity
    -- tail part
    have hrd : (0:ℤ)<(r.den:ℤ) := by positivity
    have htail := evalHomInt_val r.num (r.den:ℤ) hrd.ne' (((sh.1.drop (J+1)).reverse).map absI)
    have hrr : ((r.num:ℝ)/((r.den:ℤ):ℝ))=(r:ℝ) := by
      rw [Rat.cast_def]; push_cast; rfl
    rw [hrr] at htail
    have hfoldT : List.foldl (fun acc (a:ℤ) => (r:ℝ)*acc+(a:ℝ)) 0 (((sh.1.drop (J+1)).reverse).map absI)=
        evalIntAsc ((sh.1.drop (J+1)).map absI) (r:ℝ) := by
      rw [show ((sh.1.drop (J+1)).reverse).map absI=((sh.1.drop (J+1)).map absI).reverse by simp,
        foldl_reverse_evalIntAsc]
    rw [hfoldT] at htail
    have ht2 : (0:ℤ)<(evalHomInt r.num (r.den:ℤ) (((sh.1.drop (J+1)).reverse).map absI)).2 := by
      unfold evalHomInt; rw [evalHomInt_snd]; simp only [mul_one]; positivity
    set T := evalIntAsc ((sh.1.drop (J+1)).map absI) (r:ℝ) with hT
    have hT0 : 0 ≤ T := (abs_nonneg _).trans (evalIntAsc_abs_le u r hu _)
    have hdrop := evalIntAsc_abs_le u r hu (sh.1.drop (J+1))
    -- remainder bounds
    have hTB : T*(r:ℝ)^(J+1)/(sh.2:ℝ)/(S:ℝ) ≤ dec S (ceilDiv
        ((evalHomInt r.num (r.den:ℤ) (((sh.1.drop (J+1)).reverse).map absI)).1*r.num^(J+1))
        ((evalHomInt r.num (r.den:ℤ) (((sh.1.drop (J+1)).reverse).map absI)).2*sh.2*(r.den:ℤ)^(J+1))) := by
      unfold dec
      apply div_le_div_of_nonneg_right _ hSR.le
      refine le_trans (le_of_eq ?_) (ceilDiv_ge _ _ (by positivity))
      push_cast
      rw [htail]
      have hrq : (r:ℝ)=(r.num:ℝ)/(r.den:ℝ) := Rat.cast_def r
      have hrd0 : (r.den:ℝ) ≠ 0 := by positivity
      rw [hrq,div_pow]
      field_simp
    have hWB : dec S width*∑ k ∈ Finset.range ds.length,(z:ℝ)^k ≤ dec S (ceilDiv
        (width*(evalHomInt z.num (z.den:ℤ) (List.replicate ds.length 1)).1)
        (evalHomInt z.num (z.den:ℤ) (List.replicate ds.length 1)).2) := by
      unfold dec
      rw [div_mul_eq_mul_div]
      apply div_le_div_of_nonneg_right _ hSR.le
      refine le_trans (le_of_eq ?_) (ceilDiv_ge _ _ (by positivity))
      push_cast
      rw [hwid]
      field_simp
    have hdw0 : 0 ≤ dec S width := by unfold dec; exact div_nonneg (by exact_mod_cast hw) hSR.le
    show |q.foldl (fun acc b => t*acc+b) 0-evalModel _ u| ≤ dec S (_+_)
    rw [hmod,dec_add]
    have hsum : q.foldl (fun acc b => t*acc+b) 0-evalIntAsc (sh.1.take (J+1)) u/((sh.2:ℝ)*(S:ℝ))=
        (q.foldl (fun acc b => t*acc+b) 0-ds.foldl (fun acc a => t*acc+dec S a) 0)+
          u^(J+1)*evalIntAsc (sh.1.drop (J+1)) u/(sh.2:ℝ)/(S:ℝ) := by
      rw [hP,hsplit]; field_simp; ring
    rw [hsum]
    refine (abs_add_le _ _).trans ?_
    have hA : |u^(J+1)*evalIntAsc (sh.1.drop (J+1)) u/(sh.2:ℝ)/(S:ℝ)| ≤ T*(r:ℝ)^(J+1)/(sh.2:ℝ)/(S:ℝ) := by
      have hnum : |u|^(J+1)*|evalIntAsc (sh.1.drop (J+1)) u| ≤ T*(r:ℝ)^(J+1) := by
        rw [mul_comm T]
        exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hu _) hdrop (abs_nonneg _) (by positivity)
      rw [abs_div,abs_div,abs_mul,abs_pow,abs_of_pos hsh2R,abs_of_pos hSR]
      exact div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hnum hsh2R.le) hSR.le
    have hB := hpert.trans (mul_le_mul_of_nonneg_left hsumz hdw0)
    linarith [hTB,hWB]

#print axioms midPolyBoxF_sound
/-- Horner perturbation at `|t| ≤ 1` with per-coefficient widths. -/
theorem horner_perturb_unit (t : ℝ) (ht : |t| ≤ 1) (p : List FBox) (vals : List ℝ)
    (h : List.Forall₂ Contains p vals) :
    ∀ acc1 acc2 : ℝ, |vals.foldl (fun acc b => t*acc+b) acc1-(p.map midF).foldl (fun acc (a:ℤ) => t*acc+dec S a) acc2| ≤
      |acc1-acc2|+dec S (p.map widthF).sum := by
  induction h with
  | nil => intro acc1 acc2; simp [dec]
  | @cons a x p vals hax _ ih =>
    intro acc1 acc2
    simp only [List.map_cons,List.foldl_cons,List.sum_cons,dec_add]
    refine (ih _ _).trans ?_
    have hm := midpoint_error a x hax
    have h1 : |t*acc1+x-(t*acc2+dec S (midF a))| ≤ |acc1-acc2|+dec S (widthF a) := by
      have : t*acc1+x-(t*acc2+dec S (midF a))=t*(acc1-acc2)+(x-dec S (midF a)) := by ring
      rw [this]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul]
      have := mul_le_of_le_one_left (abs_nonneg (acc1-acc2)) ht
      linarith
    linarith

/-- `polyExactF x p` encloses the Horner value of any coefficients in the boxes `p`, at `|x| ≤ 1`. -/
theorem polyExactF_sound (x : ℚ) (hx : |(x:ℝ)| ≤ 1) (p : List FBox) (vals : List ℝ)
    (h : List.Forall₂ Contains p vals) :
    Contains (polyExactF x p) (vals.foldl (fun acc b => (x:ℝ)*acc+b) 0) := by
  have hSR : (0:ℝ)<(S:ℝ) := S_real_pos
  have hxd : (0:ℤ)<(x.den:ℤ) := by positivity
  have hq := evalHomInt_val x.num (x.den:ℤ) hxd.ne' (p.map midF)
  have hxr : ((x.num:ℝ)/((x.den:ℤ):ℝ))=(x:ℝ) := by rw [Rat.cast_def]; push_cast; rfl
  rw [hxr] at hq
  have hq2 : (0:ℤ)<(evalHomInt x.num (x.den:ℤ) (p.map midF)).2 := by
    unfold evalHomInt; rw [evalHomInt_snd]; simp only [mul_one]; positivity
  have hq2R : (0:ℝ)<((evalHomInt x.num (x.den:ℤ) (p.map midF)).2:ℝ) := by exact_mod_cast hq2
  set H := (p.map midF).foldl (fun acc (a:ℤ) => (x:ℝ)*acc+(a:ℝ)) 0 with hH
  have hdecH : (p.map midF).foldl (fun acc (a:ℤ) => (x:ℝ)*acc+dec S a) 0=H/(S:ℝ) := by
    have := foldl_dec (x:ℝ) (p.map midF) 0
    rwa [zero_div] at this
  have hpert := horner_perturb_unit (x:ℝ) hx p vals h 0 0
  rw [sub_self,abs_zero,zero_add,hdecH] at hpert
  have hratio : ((evalHomInt x.num (x.den:ℤ) (p.map midF)).1:ℝ)/
      ((evalHomInt x.num (x.den:ℤ) (p.map midF)).2:ℝ)=H := by
    rw [hq]; field_simp
  have hsum : (p.map widthF).foldl (·+·) 0=(p.map widthF).sum := (List.sum_eq_foldl).symm
  unfold polyExactF
  simp only [hsum]
  rw [abs_le] at hpert
  constructor
  · unfold dec
    have hf := ediv_le_real (evalHomInt x.num (x.den:ℤ) (p.map midF)).1 _ hq2
    rw [hratio] at hf
    have hf' := div_le_div_of_nonneg_right hf hSR.le
    rw [Int.cast_sub,sub_div]
    unfold dec at hpert
    linarith [hpert.1]
  · unfold dec
    have hc := ceilDiv_ge (evalHomInt x.num (x.den:ℤ) (p.map midF)).1 _ hq2.ne'
    rw [hratio] at hc
    have hc' := div_le_div_of_nonneg_right hc hSR.le
    rw [Int.cast_add,add_div]
    unfold dec at hpert
    linarith [hpert.2]

#print axioms polyExactF_sound

/-- One Taylor order of the multipole majorant: with `|w k| ≤ M h^(k+1)/(k+1)`,
`Σ_k |w k| x^-(k+1) C(N+k,k) (r/x)^N ≤ M (r/(x-h))^N / N`. -/
theorem mp_majorant_term (x h r M : ℝ) (hx : 0 < x) (hh : 0 ≤ h) (hr : 0 ≤ r) (hM : 0 ≤ M)
    (hsep : h+r < x) (n N1 : ℕ) (w : ℕ → ℝ)
    (hw : ∀ k < n, |w k| ≤ M*h^(k+1)/((k+1:ℕ):ℝ)) :
    ∑ k ∈ Finset.range n, |w k| * (x^(-((k+1:ℕ):ℤ))*((((N1+1)+k).choose k:ℝ)*(r/x)^(N1+1))) ≤
      M*(r/(x-h))^(N1+1)/((N1+1:ℕ):ℝ) := by
  have ha0 : 0 ≤ h/x := div_nonneg hh hx.le
  have ha1 : h/x < 1 := (div_lt_one hx).mpr (by linarith)
  have hs := hasSum_choose_mul_geometric_of_norm_lt_one N1 (r := h/x)
    (by rw [Real.norm_eq_abs,abs_of_nonneg ha0]; exact ha1)
  have hpart : ∑ k ∈ Finset.range n, (((k+1)+N1).choose N1:ℝ)*(h/x)^(k+1) ≤ 1/(1-h/x)^(N1+1) := by
    have h1 : ∑ k ∈ Finset.range n, (((k+1)+N1).choose N1:ℝ)*(h/x)^(k+1) ≤
        ∑ m ∈ Finset.range (n+1), ((m+N1).choose N1:ℝ)*(h/x)^m := by
      rw [Finset.sum_range_succ']; simp only [le_add_iff_nonneg_right]; positivity
    exact h1.trans (sum_le_hasSum _ (fun m _ => by positivity) hs)
  have hNpos : (0:ℝ) < ((N1+1:ℕ):ℝ) := by positivity
  have hq0 : 0 ≤ (r/x)^(N1+1) := by positivity
  have hk : ∀ k ∈ Finset.range n,
      |w k| * (x^(-((k+1:ℕ):ℤ))*((((N1+1)+k).choose k:ℝ)*(r/x)^(N1+1))) ≤
        M*(r/x)^(N1+1)/((N1+1:ℕ):ℝ)*((((k+1)+N1).choose N1:ℝ)*(h/x)^(k+1)) := by
    intro k hkn
    have hwk := hw k (Finset.mem_range.mp hkn)
    have e := Nat.choose_succ_right_eq (N1+1+k) k
    have e2 : (N1+1+k).choose (k+1)=((k+1)+N1).choose N1 := by
      rw [show N1+1+k=(k+1)+N1 by omega]; exact Nat.choose_symm_add
    rw [e2,show N1+1+k-k=N1+1 by omega] at e
    have hC : (((k+1)+N1).choose N1:ℝ)=((N1+1+k).choose k:ℝ)*((N1+1:ℕ):ℝ)/((k+1:ℕ):ℝ) := by
      have hk1 : ((k+1:ℕ):ℝ) ≠ 0 := by positivity
      rw [eq_div_iff hk1]; exact_mod_cast e
    have hxk : x^(-((k+1:ℕ):ℤ))=(x^(k+1))⁻¹ := by rw [zpow_neg,zpow_natCast]
    rw [hxk,hC]
    have hxp : 0 < x^(k+1) := pow_pos hx _
    calc |w k| * ((x^(k+1))⁻¹*((((N1+1)+k).choose k:ℝ)*(r/x)^(N1+1)))
        ≤ M*h^(k+1)/((k+1:ℕ):ℝ)*((x^(k+1))⁻¹*((((N1+1)+k).choose k:ℝ)*(r/x)^(N1+1))) :=
          mul_le_mul_of_nonneg_right hwk (by positivity)
      _ = _ := by
          have hk1 : ((k+1:ℕ):ℝ) ≠ 0 := by positivity
          rw [div_pow h x]
          field_simp
  have hsum := Finset.sum_le_sum hk
  rw [← Finset.mul_sum] at hsum
  refine hsum.trans ?_
  have hxh : 0 < x-h := by linarith
  have h1a : 0 < 1-h/x := by linarith
  calc M*(r/x)^(N1+1)/((N1+1:ℕ):ℝ)*∑ k ∈ Finset.range n, (((k+1)+N1).choose N1:ℝ)*(h/x)^(k+1)
      ≤ M*(r/x)^(N1+1)/((N1+1:ℕ):ℝ)*(1/(1-h/x)^(N1+1)) :=
        mul_le_mul_of_nonneg_left hpart (by positivity)
    _ = _ := by
        have e : 1-h/x=(x-h)/x := by field_simp
        rw [e,div_pow,div_pow,div_pow]
        field_simp

#print axioms mp_majorant_term

/-- Tail of one inverse power as a series: `invPowerTail x r k J = Σ_{j} x^-k C(j+J+1+k-1,…) (r/x)^(j+J+1)`. -/
theorem invPowerTail_hasSum (x r : ℝ) (hx : 0 < x) (hr : 0 ≤ r) (hrx : r < x) (k J : ℕ) :
    HasSum (fun j : ℕ => x^(-((k+1:ℕ):ℤ))*((((j+J)+1)+k).choose k:ℝ)*(r/x)^((j+J)+1))
      (invPowerTail x r (k+1) J) := by
  have hq0 : 0 ≤ r/x := div_nonneg hr hx.le
  have hq1 : r/x < 1 := (div_lt_one hx).mpr hrx
  have hs := hasSum_choose_mul_geometric_of_norm_lt_one k (r := r/x)
    (by rw [Real.norm_eq_abs,abs_of_nonneg hq0]; exact hq1)
  have ht := ((hasSum_nat_add_iff' (J+1)).2 hs).mul_left (x^(-((k+1:ℕ):ℤ)))
  convert ht using 1
  · funext j; rw [show j+J+1=j+(J+1) by omega]; ring
  · unfold invPowerTail
    congr 1
    rw [zpow_neg,zpow_natCast,one_div]
    congr 1
    apply Finset.sum_congr rfl; intro j _
    rw [show k+1+j-1=j+k by omega,Nat.choose_symm_add]

/-- Multipole majorant: with `|w k| ≤ M h^(k+1)/(k+1)` and `η = r/(x-h)`, the Taylor tails of
`Σ_k w k (x+u)^-(k+1)` sum to at most `M η^(J+1)/((J+1)(1-η))`. -/
theorem mp_majorant (x h r M : ℝ) (hx : 0 < x) (hh : 0 ≤ h) (hr : 0 ≤ r) (hM : 0 ≤ M)
    (hsep : h+r < x) (n J : ℕ) (w : ℕ → ℝ)
    (hw : ∀ k < n, |w k| ≤ M*h^(k+1)/((k+1:ℕ):ℝ)) :
    ∑ k ∈ Finset.range n, |w k| * invPowerTail x r (k+1) J ≤
      M*(r/(x-h))^(J+1)/(((J+1:ℕ):ℝ)*(1-r/(x-h))) := by
  have hrx : r < x := by linarith
  have hxh : 0 < x-h := by linarith
  have he0 : 0 ≤ r/(x-h) := div_nonneg hr hxh.le
  have he1 : r/(x-h) < 1 := (div_lt_one hxh).mpr (by linarith)
  have hL := hasSum_sum (s := Finset.range n) (fun k _ =>
    (invPowerTail_hasSum x r hx hr hrx k J).mul_left (|w k|))
  have hJ : (0:ℝ) < ((J+1:ℕ):ℝ) := by positivity
  have hG := (hasSum_geometric_of_lt_one he0 he1).mul_left (M*(r/(x-h))^(J+1)/((J+1:ℕ):ℝ))
  have hle := hasSum_le (fun j => ?_) hL hG
  · refine hle.trans_eq ?_
    field_simp
  · have ht := mp_majorant_term x h r M hx hh hr hM hsep n (j+J) w hw
    have hj : ((J+1:ℕ):ℝ) ≤ (((j+J)+1:ℕ):ℝ) := by exact_mod_cast (by omega : J+1 ≤ (j+J)+1)
    calc ∑ k ∈ Finset.range n, |w k| * (x^(-((k+1:ℕ):ℤ))*((((j+J)+1)+k).choose k:ℝ)*(r/x)^((j+J)+1))
        = ∑ k ∈ Finset.range n, |w k| * (x^(-((k+1:ℕ):ℤ))*(((((j+J)+1)+k).choose k:ℝ)*(r/x)^((j+J)+1))) := by
          apply Finset.sum_congr rfl; intro k _; ring
      _ ≤ M*(r/(x-h))^((j+J)+1)/(((j+J)+1:ℕ):ℝ) := ht
      _ ≤ M*(r/(x-h))^((j+J)+1)/((J+1:ℕ):ℝ) :=
          div_le_div_of_nonneg_left (by positivity) hJ hj
      _ = M*(r/(x-h))^(J+1)/((J+1:ℕ):ℝ)*(r/(x-h))^j := by ring

#print axioms mp_majorant

/-! ### `mpBoxF` -/

theorem foldr_horner_range' (t : ℝ) (g : ℕ → ℝ) : ∀ (n s : ℕ),
    ((List.range' s n).map g).foldr (fun b a => (a+b)*t) 0 =
      ∑ k ∈ Finset.range n, g (s+k)*t^(k+1)
  | 0,s => by simp
  | n+1,s => by
    rw [List.range'_succ,List.map_cons,List.foldr_cons,foldr_horner_range' t g n (s+1),
      Finset.sum_range_succ']
    simp only [add_zero,zero_add,pow_one]
    rw [add_mul,Finset.sum_mul]
    have : ∀ k ∈ Finset.range n, g (s+1+k)*t^(k+1)*t=g (s+(k+1))*t^(k+1+1) := by
      intro k _; rw [show s+1+k=s+(k+1) by omega]; ring
    rw [Finset.sum_congr rfl this]

theorem forall₂_zipIdx_scale (c : ℕ → ℤ) (w : ℕ → ℝ) : ∀ (l : List FBox) (s : ℕ),
    List.Forall₂ Contains l ((List.range' s l.length).map w) →
    List.Forall₂ Contains ((l.zipIdx s).map (fun a => boxScaleF (c a.2) a.1))
      ((List.range' s l.length).map (fun k => (c k:ℝ)*w k))
  | [],s,_ => by simp
  | b::l,s,h => by
    simp only [List.zipIdx_cons,List.map_cons,List.length_cons,List.range'_succ] at h ⊢
    cases h with
    | cons hb hl => exact .cons (boxScaleF_sound _ _ _ hb) (forall₂_zipIdx_scale c w l (s+1) hl)

/-- `mpBoxF` encloses the Taylor jet of `u ↦ -2 Σ_{k<n} w k (x+u)^-(k+1)` on `|u| ≤ R/S`, given
`MU[k] ∋ w k`, `|w k| ≤ |M| h^(k+1)/(k+1)` and `x ∈ d`. -/
theorem mpBoxF_sound (MU : List FBox) (mass : FBox) (h : ℚ) (d : FBox) (R : ℤ) (J : ℕ) (M x : ℝ)
    (w : ℕ → ℝ) (hM : Contains mass M) (hx : Contains d x)
    (hMU : List.Forall₂ Contains MU ((List.range MU.length).map w))
    (hw : ∀ k < MU.length, |w k| ≤ |M| * (h:ℝ)^(k+1)/((k+1:ℕ):ℝ))
    (m : IntTaylorModel) (hm : mpBoxF MU mass h d R J=some m) :
    ModelsF m (dec S R) (fun u => -2*∑ k ∈ Finset.range MU.length, w k*(x+u)^(-((k+1:ℕ):ℤ))) := by
  unfold mpBoxF at hm
  split_ifs at hm with hg
  push_neg at hg
  obtain ⟨hR,hh,hJ⟩ := hg
  cases hinv : boxDivF boxOne d with
  | none => simp [hinv,bind,Option.bind] at hm
  | some inv =>
  simp only [hinv,bind,Option.bind] at hm
  split_ifs at hm with hdist
  cases heta : boxDivF (R,R) (boxSubF d (boxOfQ h)) with
  | none => simp [heta] at hm
  | some eta =>
  simp only [heta] at hm
  split_ifs at hm with hS
  cases herr : boxDivF (boxDivNatF (J+1) (boxMulF (boxScaleF 2 (boxAbsF mass)) (boxPowF eta (J+1))))
      (boxSubF boxOne eta) with
  | none => simp [herr] at hm
  | some err =>
  simp only [herr,Option.pure_def,Option.some.injEq] at hm
  subst hm
  have hSR : (0:ℝ)<(S:ℝ) := S_real_pos
  set n := MU.length with hn
  set r : ℝ := dec S R with hr
  have hr0 : 0 ≤ r := by rw [hr]; unfold dec; exact div_nonneg (by exact_mod_cast hR) hSR.le
  have hh0 : (0:ℝ) ≤ (h:ℝ) := by exact_mod_cast hh
  have hdC : Contains (boxSubF d (boxOfQ h)) (x-h) := boxSubF_sound _ _ _ _ hx (boxOfQ_sound h)
  have hsep : (h:ℝ)+r < x := by
    have : dec S R < dec S (boxSubF d (boxOfQ h)).1 := by
      unfold dec; exact (div_lt_div_iff_of_pos_right hSR).2 (by exact_mod_cast (not_le.mp hdist))
    linarith [hdC.1]
  have hxpos : 0 < x := by linarith
  have hxh : 0 < x-h := by linarith
  have hinvC : Contains inv (1/x) := boxDivF_sound _ _ _ _ _ boxOne_sound hx hinv
  have hetaC : Contains eta (r/(x-h)) := boxDivF_sound _ _ _ _ _ (contains_pt _) hdC heta
  -- real coefficients
  let a : List ℝ := (List.range (J+1)).map (fun j => -2*∑ k ∈ Finset.range n,
    w k*((-1:ℝ)^j*((k+1+j-1).choose j:ℝ)/x^(k+1+j)))
  refine ⟨a,?_,?_⟩
  · simp only [a]
    rw [List.forall₂_map_left_iff,List.forall₂_map_right_iff]
    apply List.forall₂_same.mpr
    intro j _
    have hW := forall₂_zipIdx_scale (fun k => (mpChoose (k+1) j:ℤ)) w MU 0
      (by rw [← List.range_eq_range']; exact hMU)
    have hv := boxHornerMul_sound inv (1/x) hinvC _ _ (List.forall₂_reverse_iff.mpr hW)
    have hfold : ((List.range' 0 MU.length).map (fun k => ((mpChoose (k+1) j:ℤ):ℝ)*w k)).reverse.foldl
        (fun a b => (a+b)*(1/x)) 0 = ∑ k ∈ Finset.range n, ((mpChoose (0+k+1) j:ℤ):ℝ)*w (0+k)*(1/x)^(k+1) := by
      rw [List.foldl_reverse]; exact foldr_horner_range' (1/x) _ n 0
    rw [hfold] at hv
    have hc := boxScaleF_sound (-2*(-1:ℤ)^j) _ _ (boxMulF_sound _ _ _ _ hv (boxPowF_sound inv _ hinvC j))
    convert hc using 1
    push_cast
    rw [Finset.mul_sum,Finset.sum_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl; intro k _
    simp only [zero_add,mpChoose_eq]
    have hx0 : x ≠ 0 := hxpos.ne'
    simp only [one_div,inv_pow]
    field_simp
    ring
  · intro u hu
    have hmodel (k : ℕ) := inverse_real_taylor_model x r hxpos hr0 (by linarith) (k+1) J (by omega)
    have hev : evalModel a u = -2*∑ k ∈ Finset.range n, w k*evalModel (invPowerTaylor x (k+1) J) u := by
      simp only [a,invPowerTaylor,evalModel_range]
      rw [Finset.mul_sum]
      simp_rw [Finset.mul_sum,Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro k _
      apply Finset.sum_congr rfl; intro j _
      ring
    rw [hev]
    have hsplit : -2*∑ k ∈ Finset.range n, w k*(x+u)^(-((k+1:ℕ):ℤ))-
        -2*∑ k ∈ Finset.range n, w k*evalModel (invPowerTaylor x (k+1) J) u =
        -2*∑ k ∈ Finset.range n, w k*((x+u)^(-((k+1:ℕ):ℤ))-evalModel (invPowerTaylor x (k+1) J) u) := by
      rw [← mul_sub,← Finset.sum_sub_distrib]; congr 1
      apply Finset.sum_congr rfl; intro k _; ring
    rw [hsplit,abs_mul]
    have hsum : |∑ k ∈ Finset.range n, w k*((x+u)^(-((k+1:ℕ):ℤ))-evalModel (invPowerTaylor x (k+1) J) u)| ≤
        ∑ k ∈ Finset.range n, |w k| * invPowerTail x r (k+1) J := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left ((hmodel k).2.2 u hu) (abs_nonneg _)
    have hmaj := mp_majorant x h r |M| hxpos hh0 hr0 (abs_nonneg M) hsep n J w hw
    -- the box error
    have hpow := boxPowF_sound eta _ hetaC (J+1)
    have hnum := boxMulF_sound _ _ _ _ (boxScaleF_sound 2 _ _ (boxAbsF_sound _ _ hM)) hpow
    have hdiv := boxDivNatF_sound (J+1) (by omega) _ _ hnum
    have hden := boxSubF_sound boxOne eta 1 _ boxOne_sound hetaC
    have hE := boxDivF_sound _ _ _ _ _ hdiv hden herr
    have hEle : 2*(|M| * (r/(x-h))^(J+1)/(((J+1:ℕ):ℝ)*(1-r/(x-h)))) ≤ dec S (max err.2 0) := by
      refine le_trans (le_of_eq ?_) (hE.2.trans ?_)
      · push_cast; rw [div_div]; ring
      · unfold dec
        exact div_le_div_of_nonneg_right (by exact_mod_cast le_max_left _ _) hSR.le
    calc |(-2:ℝ)| * |∑ k ∈ Finset.range n, w k*((x+u)^(-((k+1:ℕ):ℤ))-evalModel (invPowerTaylor x (k+1) J) u)|
        ≤ 2*(|M| * (r/(x-h))^(J+1)/(((J+1:ℕ):ℝ)*(1-r/(x-h)))) := by
          rw [show |(-2:ℝ)|=2 by norm_num]
          exact mul_le_mul_of_nonneg_left (hsum.trans hmaj) (by norm_num)
      _ ≤ _ := hEle

#print axioms mpBoxF_sound

theorem mpBoxF_sep (MU : List FBox) (mass : FBox) (h : ℚ) (d : FBox) (R : ℤ) (J : ℕ) (x : ℝ)
    (hx : Contains d x) (m : IntTaylorModel) (hm : mpBoxF MU mass h d R J=some m) :
    0 ≤ (h:ℝ) ∧ 0 ≤ dec S R ∧ (h:ℝ)+dec S R < x := by
  unfold mpBoxF at hm
  split_ifs at hm with hg
  push_neg at hg
  obtain ⟨hR,hh,-⟩ := hg
  cases hinv : boxDivF boxOne d with
  | none => simp [hinv,bind,Option.bind] at hm
  | some inv =>
  simp only [hinv,bind,Option.bind] at hm
  split_ifs at hm with hdist
  have hSR : (0:ℝ)<(S:ℝ) := S_real_pos
  have hdC : Contains (boxSubF d (boxOfQ h)) (x-h) := boxSubF_sound _ _ _ _ hx (boxOfQ_sound h)
  have : dec S R < dec S (boxSubF d (boxOfQ h)).1 := by
    unfold dec; exact (div_lt_div_iff_of_pos_right hSR).2 (by exact_mod_cast (not_le.mp hdist))
  refine ⟨by exact_mod_cast hh,?_,by linarith [hdC.1]⟩
  unfold dec; exact div_nonneg (by exact_mod_cast hR) hSR.le

/-- `mpBoxKF` encloses the same function: the first `K` moments go through `mpBoxF`, the rest into
`mpCutTail`'s geometric bound `2|M| q^(K+1)/(1-q)`, `q = h/(x-R/S)`. -/
theorem mpBoxKF_sound (MU : List FBox) (mass : FBox) (h : ℚ) (d : FBox) (R : ℤ) (J K : ℕ) (M x : ℝ)
    (w : ℕ → ℝ) (hM : Contains mass M) (hx : Contains d x)
    (hMU : List.Forall₂ Contains MU ((List.range MU.length).map w))
    (hw : ∀ k < MU.length, |w k| ≤ |M| * (h:ℝ)^(k+1)/((k+1:ℕ):ℝ))
    (m : IntTaylorModel) (hm : mpBoxKF MU mass h d R J K=some m) :
    ModelsF m (dec S R) (fun u => -2*∑ k ∈ Finset.range MU.length, w k*(x+u)^(-((k+1:ℕ):ℤ))) := by
  unfold mpBoxKF at hm
  split_ifs at hm with hlen
  · exact mpBoxF_sound MU mass h d R J M x w hM hx hMU hw m hm
  push_neg at hlen
  cases h0 : mpBoxF (MU.take K) mass h d R J with
  | none => simp [h0,bind,Option.bind] at hm
  | some m0 =>
  cases ht : mpCutTail mass h d R K with
  | none => simp [h0,ht,bind,Option.bind] at hm
  | some t =>
  simp only [h0,ht,bind,Option.bind,Option.pure_def,Option.some.injEq] at hm
  subst hm
  have hlenK : (MU.take K).length=K := by simp [List.length_take]; omega
  have hMU0 : List.Forall₂ Contains (MU.take K) ((List.range (MU.take K).length).map w) := by
    rw [hlenK]
    have := List.forall₂_take K hMU
    rwa [← List.map_take,List.take_range,min_eq_left hlen.le] at this
  have hw0 : ∀ k < (MU.take K).length, |w k| ≤ |M| * (h:ℝ)^(k+1)/((k+1:ℕ):ℝ) :=
    fun k hk => hw k (by rw [hlenK] at hk; omega)
  obtain ⟨a,ha,hae⟩ := mpBoxF_sound _ mass h d R J M x w hM hx hMU0 hw0 m0 h0
  obtain ⟨hh0,hr0,hsep⟩ := mpBoxF_sep _ mass h d R J x hx m0 h0
  set r := dec S R
  have hSR : (0:ℝ)<(S:ℝ) := S_real_pos
  -- the cut tail box
  unfold mpCutTail at ht
  cases hq : boxDivF (boxOfQ h) (boxSubF d (R,R)) with
  | none => simp [hq,bind,Option.bind] at ht
  | some q =>
  simp only [hq,bind,Option.bind] at ht
  split_ifs at ht with hqS
  cases htt : boxDivF (boxMulF (boxScaleF 2 (boxAbsF mass)) (boxPowF q (K+1))) (boxSubF boxOne q) with
  | none => simp [htt] at ht
  | some tb =>
  simp only [htt,Option.pure_def,Option.some.injEq] at ht
  subst ht
  have hxr : 0 < x-r := by linarith
  set qv := (h:ℝ)/(x-r)
  have hq0 : 0 ≤ qv := div_nonneg hh0 hxr.le
  have hq1 : qv < 1 := (div_lt_one hxr).mpr (by linarith)
  have hqC : Contains q qv := boxDivF_sound _ _ _ _ _ (boxOfQ_sound h) (boxSubF_sound _ _ _ _ hx (contains_pt R)) hq
  have hpow := boxPowF_sound q _ hqC (K+1)
  have hnum := boxMulF_sound _ _ _ _ (boxScaleF_sound 2 _ _ (boxAbsF_sound _ _ hM)) hpow
  have hden := boxSubF_sound boxOne q 1 _ boxOne_sound hqC
  have hT := boxDivF_sound _ _ _ _ _ hnum hden htt
  have hTle : 2*|M| * qv^(K+1)/(1-qv) ≤ dec S (max tb.2 0) := by
    refine le_trans (le_of_eq (by push_cast; ring)) (hT.2.trans ?_)
    unfold dec; exact div_le_div_of_nonneg_right (by exact_mod_cast le_max_left _ _) hSR.le
  refine ⟨a,ha,fun u hu => ?_⟩
  have h1 := hae u hu
  rw [hlenK] at h1
  have hxu : x-r ≤ x+u := by linarith [(abs_le.mp hu).1]
  have hxu0 : 0 < x+u := hxr.trans_le hxu
  -- tail terms
  have htail : |∑ k ∈ Finset.Ico K MU.length, w k*(x+u)^(-((k+1:ℕ):ℤ))| ≤ |M| * qv^(K+1)/(1-qv) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hterm : ∀ k ∈ Finset.Ico K MU.length, |w k*(x+u)^(-((k+1:ℕ):ℤ))| ≤ |M| * qv^(k+1) := by
      intro k hk
      have hk' := Finset.mem_Ico.mp hk
      rw [abs_mul,zpow_neg,zpow_natCast,abs_inv,abs_of_pos (pow_pos hxu0 _)]
      have hwk := hw k hk'.2
      have hk1 : (1:ℝ) ≤ ((k+1:ℕ):ℝ) := by exact_mod_cast (by omega : 1 ≤ k+1)
      have hp : (x-r)^(k+1) ≤ (x+u)^(k+1) := pow_le_pow_left₀ hxr.le hxu _
      have hpr : 0 < (x-r)^(k+1) := pow_pos hxr _
      calc |w k| * ((x+u)^(k+1))⁻¹ ≤ |M| * (h:ℝ)^(k+1)/((k+1:ℕ):ℝ) * ((x-r)^(k+1))⁻¹ :=
            mul_le_mul hwk (inv_anti₀ hpr hp) (by positivity) (by positivity)
        _ ≤ |M| * (h:ℝ)^(k+1) * ((x-r)^(k+1))⁻¹ := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact div_le_self (by positivity) hk1
        _ = |M| * qv^(k+1) := by rw [div_pow]; field_simp
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.mul_sum]
    have hg : ∑ k ∈ Finset.Ico K MU.length, qv^(k+1) ≤ qv^(K+1)/(1-qv) := by
      have e : ∑ k ∈ Finset.Ico K MU.length, qv^(k+1)=qv*∑ k ∈ Finset.Ico K MU.length, qv^k := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; ring
      have hgeo : ∑ k ∈ Finset.Ico K MU.length, qv^k ≤ qv^K/(1-qv) := by
        rw [Finset.sum_Ico_eq_sum_range]
        have e2 : ∑ i ∈ Finset.range (MU.length-K), qv^(K+i)=qv^K*∑ i ∈ Finset.range (MU.length-K), qv^i := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; rw [pow_add]
        rw [e2,div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left (sum_le_hasSum _ (fun i _ => by positivity)
          (hasSum_geometric_of_lt_one hq0 hq1)) (by positivity)
      rw [e]
      calc qv*∑ k ∈ Finset.Ico K MU.length, qv^k ≤ qv*(qv^K/(1-qv)) :=
            mul_le_mul_of_nonneg_left hgeo hq0
        _ = qv^(K+1)/(1-qv) := by ring
    calc |M| * ∑ k ∈ Finset.Ico K MU.length, qv^(k+1) ≤ |M| * (qv^(K+1)/(1-qv)) :=
          mul_le_mul_of_nonneg_left hg (abs_nonneg _)
      _ = _ := by ring
  have hsplit := Finset.sum_range_add_sum_Ico (fun k => w k*(x+u)^(-((k+1:ℕ):ℤ))) hlen.le
  show |-2*∑ k ∈ Finset.range MU.length, w k*(x+u)^(-((k+1:ℕ):ℤ))-evalModel a u| ≤ dec S (m0.remainder+max tb.2 0)
  rw [← hsplit,dec_add]
  have e : -2*(∑ k ∈ Finset.range K, w k*(x+u)^(-((k+1:ℕ):ℤ))+
      ∑ k ∈ Finset.Ico K MU.length, w k*(x+u)^(-((k+1:ℕ):ℤ)))-evalModel a u =
      (-2*∑ k ∈ Finset.range K, w k*(x+u)^(-((k+1:ℕ):ℤ))-evalModel a u)+
      (-2)*∑ k ∈ Finset.Ico K MU.length, w k*(x+u)^(-((k+1:ℕ):ℤ)) := by ring
  rw [e]
  refine (abs_add_le _ _).trans (add_le_add h1 ?_)
  rw [abs_mul,show |(-2:ℝ)|=2 by norm_num]
  calc 2*|∑ k ∈ Finset.Ico K MU.length, w k*(x+u)^(-((k+1:ℕ):ℤ))| ≤ 2*(|M| * qv^(K+1)/(1-qv)) :=
        mul_le_mul_of_nonneg_left htail (by norm_num)
    _ = 2*|M| * qv^(K+1)/(1-qv) := by ring
    _ ≤ _ := hTle

#print axioms mpBoxKF_sound

end
end CatalanCore.Li2.DecayCert.Simple
