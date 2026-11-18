module
public import CatalanCore.Li2.DecayCert.Lattice.Bernstein.Arithmetic
public import CatalanCore.Li2.DecayCert.Lattice.Bernstein.Range
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 600000
namespace CatalanCore.Li2.DecayCert.BernsteinGrid

def lget {α : Type} [Zero α] (xs : List α) (i : ℕ) : α := xs[i]?.getD 0

theorem lget_map_range {α : Type} [Zero α] (n i : ℕ) (f : ℕ→α) :
    lget ((List.range n).map f) i=if i<n then f i else 0 := by
  by_cases hi : i<n
  · simp [lget,List.getElem?_range hi,hi]
  · have hh : ((List.range n).map f)[i]?=none :=
      List.getElem?_eq_none (by simp; omega)
    simp [lget,hh,hi]

def TableEncloses (S : ℤ) (xs : List (ℤ×ℤ)) (ys : List ℚ) : Prop :=
  xs.length=ys.length ∧ ∀ i : ℕ, Encloses S (lget xs i) (lget ys i)

def bernStep (A B D c : ℤ) : List (ℤ×ℤ)→List (ℤ×ℤ)
  | [] => [(c,c)]
  | xs@(_::_) => (List.range (xs.length+1)).map (fun k : ℕ =>
      affineBoxRow xs.length k A B D c (lget xs k) (if k=0 then (0,0) else lget xs (k-1)))

def exactStep (S A B D c : ℤ) : List ℚ→List ℚ
  | [] => [(c:ℚ)/(S:ℚ)]
  | ys@(_::_) => (List.range (ys.length+1)).map (fun k : ℕ =>
      (c:ℚ)/(S:ℚ)+
        (((ys.length-k:ℕ):ℚ)*(A:ℚ)*lget ys k+
          (k:ℚ)*(B:ℚ)*(if k=0 then 0 else lget ys (k-1)))/((ys.length:ℚ)*(D:ℚ)))

theorem bernStep_sound (S A B D c : ℤ) (hS : 0<S) (hD : 0<D)
    (xs : List (ℤ×ℤ)) (ys : List ℚ) (h : TableEncloses S xs ys) :
    TableEncloses S (bernStep A B D c xs) (exactStep S A B D c ys) := by
  have hs : (S:ℚ)≠0 := by exact_mod_cast hS.ne'
  have hc : (S:ℚ)*((c:ℚ)/(S:ℚ))=(c:ℚ) := by field_simp
  cases xs with
  | nil =>
    cases ys with
    | nil =>
      refine ⟨rfl,?_⟩
      intro i
      cases i <;> simp [bernStep,exactStep,lget,Encloses,hc]
    | cons y ys => simp [TableEncloses] at h
  | cons x xs =>
    cases ys with
    | nil => simp [TableEncloses] at h
    | cons y ys =>
      have hn : (y::ys).length=(x::xs).length := h.1.symm
      dsimp only [bernStep,exactStep]
      rw [hn]
      refine ⟨by simp,?_⟩
      intro i
      by_cases hi : i<(x::xs).length+1
      · simp only [lget_map_range,hi,ite_true]
        apply affineBoxRow_sound S (x::xs).length i A B D c _ _ _ _ hS (by simp) hD (h.2 i)
        by_cases hz : i=0
        · subst i
          simp [Encloses]
        · simpa only [hz,ite_false] using h.2 (i-1)
      · simp only [lget_map_range,hi,ite_false]
        simp [Encloses]

def bernInts (A B D : ℤ) : List ℤ→List (ℤ×ℤ)
  | [] => []
  | c::cs => bernStep A B D c (bernInts A B D cs)

def exactControls (S A B D : ℤ) : List ℤ→List ℚ
  | [] => []
  | c::cs => exactStep S A B D c (exactControls S A B D cs)

theorem bernInts_sound (S A B D : ℤ) (hS : 0<S) (hD : 0<D) (cs : List ℤ) :
    TableEncloses S (bernInts A B D cs) (exactControls S A B D cs) := by
  induction cs with
  | nil => exact ⟨rfl,by intro i; simp [bernInts,exactControls,lget,Encloses]⟩
  | cons c cs ih => exact bernStep_sound S A B D c hS hD _ _ ih

#print axioms bernStep_sound
#print axioms bernInts_sound
theorem midpoint_sound (S : ℤ) (u v : ℤ×ℤ) (x y : ℚ) (hS : 0<S)
    (hu : Encloses S u x) (hv : Encloses S v y) :
    Encloses S ((u.1+v.1)/2,-((-(u.2+v.2))/2)) ((x+y)/2) := by
  have huO : u.1≤u.2 := by exact_mod_cast hu.1.trans hu.2
  have hvO : v.1≤v.2 := by exact_mod_cast hv.1.trans hv.2
  have h := affineBoxRow_sound S 2 1 1 1 1 0 u v x y hS (by decide) (by decide) hu hv
  simpa [affineBoxRow,min_eq_left huO,max_eq_right huO,min_eq_left hvO,max_eq_right hvO] using h

theorem table_nil (S : ℤ) : TableEncloses S [] [] :=
  ⟨rfl,by intro i; simp [lget,Encloses]⟩

theorem table_cons_iff (S : ℤ) (x : ℤ×ℤ) (y : ℚ) (xs : List (ℤ×ℤ)) (ys : List ℚ) :
    TableEncloses S (x::xs) (y::ys)↔Encloses S x y ∧ TableEncloses S xs ys := by
  constructor
  · intro h
    refine ⟨?_,⟨Nat.succ.inj h.1,?_⟩⟩
    · simpa only [lget,List.getElem?_cons_zero,Option.getD_some] using h.2 0
    · intro i
      simpa only [lget,List.getElem?_cons_succ] using h.2 (i+1)
  · rintro ⟨hxy,hlen,hall⟩
    refine ⟨congrArg Nat.succ hlen,?_⟩
    intro i
    cases i with
    | zero => simpa only [lget,List.getElem?_cons_zero,Option.getD_some] using hxy
    | succ i => simpa only [lget,List.getElem?_cons_succ] using hall i

def avgRow : List (ℤ×ℤ)→List (ℤ×ℤ)
  | a::b::xs => ((a.1+b.1)/2,-((-(a.2+b.2))/2))::avgRow (b::xs)
  | _ => []

def exactAvg : List ℚ→List ℚ
  | a::b::xs => ((a+b)/2)::exactAvg (b::xs)
  | _ => []

theorem avgRow_sound (S : ℤ) (hS : 0<S) (xs : List (ℤ×ℤ)) (ys : List ℚ)
    (h : TableEncloses S xs ys) : TableEncloses S (avgRow xs) (exactAvg ys) := by
  induction xs generalizing ys with
  | nil =>
    have hy : ys=[] := List.eq_nil_of_length_eq_zero h.1.symm
    subst ys
    exact table_nil S
  | cons a xs ih =>
    cases ys with
    | nil => simp [TableEncloses] at h
    | cons c ys =>
      rcases (table_cons_iff S a c xs ys).mp h with ⟨hac,ht⟩
      cases xs with
      | nil =>
        have hy : ys=[] := List.eq_nil_of_length_eq_zero ht.1.symm
        subst ys
        exact table_nil S
      | cons b xs =>
        cases ys with
        | nil => simp [TableEncloses] at ht
        | cons d ys =>
          have hbd := ((table_cons_iff S b d xs ys).mp ht).1
          apply (table_cons_iff S _ _ _ _).mpr
          exact ⟨midpoint_sound S a b c d hS hac hbd,ih (d::ys) ht⟩

#print axioms midpoint_sound
#print axioms avgRow_sound
theorem headD_eq_lget {α : Type} [Zero α] (xs : List α) : xs.headD 0=lget xs 0 := by
  cases xs <;> rfl

theorem table_head (S : ℤ) (xs : List (ℤ×ℤ)) (ys : List ℚ) (h : TableEncloses S xs ys) :
    Encloses S (xs.headD 0) (ys.headD 0) := by
  simpa only [headD_eq_lget] using h.2 0

theorem table_last (S : ℤ) (xs : List (ℤ×ℤ)) (ys : List ℚ) (h : TableEncloses S xs ys) :
    Encloses S (xs.getLastD 0) (ys.getLastD 0) := by
  simpa only [List.getLastD_eq_getLast?,List.getLast?_eq_getElem?,lget,h.1] using h.2 (xs.length-1)

theorem table_append (S : ℤ) (xs us : List (ℤ×ℤ)) (ys vs : List ℚ)
    (h : TableEncloses S xs ys) (hu : TableEncloses S us vs) :
    TableEncloses S (xs++us) (ys++vs) := by
  induction xs generalizing ys with
  | nil =>
    have hy : ys=[] := List.eq_nil_of_length_eq_zero h.1.symm
    subst ys
    exact hu
  | cons x xs ih =>
    cases ys with
    | nil => simp [TableEncloses] at h
    | cons y ys =>
      have hc := (table_cons_iff S x y xs ys).mp h
      exact (table_cons_iff S x y (xs++us) (ys++vs)).mpr ⟨hc.1,ih ys hc.2⟩

def splitFuel : ℕ→List (ℤ×ℤ)→List (ℤ×ℤ)×List (ℤ×ℤ)
  | 0,_ => ([],[])
  | n+1,xs =>
    let rest := splitFuel n (avgRow xs)
    (xs.headD 0::rest.1,rest.2++[xs.getLastD 0])

def exactSplitFuel : ℕ→List ℚ→List ℚ×List ℚ
  | 0,_ => ([],[])
  | n+1,ys =>
    let rest := exactSplitFuel n (exactAvg ys)
    (ys.headD 0::rest.1,rest.2++[ys.getLastD 0])

theorem splitFuel_sound (S : ℤ) (hS : 0<S) (n : ℕ)
    (xs : List (ℤ×ℤ)) (ys : List ℚ) (h : TableEncloses S xs ys) :
    TableEncloses S (splitFuel n xs).1 (exactSplitFuel n ys).1 ∧
      TableEncloses S (splitFuel n xs).2 (exactSplitFuel n ys).2 := by
  induction n generalizing xs ys with
  | zero => exact ⟨table_nil S,table_nil S⟩
  | succ n ih =>
    have ha := avgRow_sound S hS xs ys h
    have hp := ih (avgRow xs) (exactAvg ys) ha
    dsimp only [splitFuel,exactSplitFuel]
    constructor
    · exact (table_cons_iff S _ _ _ _).mpr ⟨table_head S xs ys h,hp.1⟩
    · apply table_append S _ _ _ _ hp.2
      exact (table_cons_iff S _ _ [] []).mpr ⟨table_last S xs ys h,table_nil S⟩

def splitInts (xs : List (ℤ×ℤ)) : List (ℤ×ℤ)×List (ℤ×ℤ) := splitFuel xs.length xs

def exactSplit (ys : List ℚ) : List ℚ×List ℚ := exactSplitFuel ys.length ys

theorem splitInts_sound (S : ℤ) (hS : 0<S)
    (xs : List (ℤ×ℤ)) (ys : List ℚ) (h : TableEncloses S xs ys) :
    TableEncloses S (splitInts xs).1 (exactSplit ys).1 ∧
      TableEncloses S (splitInts xs).2 (exactSplit ys).2 := by
  unfold splitInts exactSplit
  rw [← h.1]
  exact splitFuel_sound S hS xs.length xs ys h

theorem bernInts_length (A B D : ℤ) (cs : List ℤ) : (bernInts A B D cs).length=cs.length := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    dsimp only [bernInts]
    have hs (xs : List (ℤ×ℤ)) : (bernStep A B D c xs).length=xs.length+1 := by
      cases xs <;> simp [bernStep]
    rw [hs,ih,List.length_cons]

theorem bernInts_foldr (A B D : ℤ) (cs : List ℤ) :
    bernInts A B D cs=cs.foldr (bernStep A B D) [] := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simpa only [bernInts,List.foldr_cons] using congrArg (bernStep A B D c) ih

#print axioms splitInts_sound
#print axioms bernInts_foldr
end CatalanCore.Li2.DecayCert.BernsteinGrid
