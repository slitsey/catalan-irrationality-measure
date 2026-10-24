module
public import CatalanCore.Arith.Hybrid.D1Quarter
@[expose] public section
open CatalanCore.Arith.Hybrid
open Finset
namespace CatalanArchive.CatalanCore.Arith.Hybrid.D1QuarterPrefix

/-- The two nearest-multiple strips indexed by n. -/
noncomputable def quarterD1Pair (n : ℕ) : List Piece :=
  [mkPiece 1 (4*(n+1)) 1 (2*(2*n+1)) 11 (-4*((n+1 : ℕ) : ℤ)) 100 4,
   mkPiece 1 (2*(2*n+1)) 1 (4*n) 9 (4*(n : ℤ)) 100 4]

/-- A finite refinement, with the unmodified constant prefix below its first strip. -/
noncomputable def quarterD1Prefix (K : ℕ) : List Piece :=
  ((List.range K).reverse).flatMap (fun j => quarterD1Pair (j+1))

private lemma left_key {r m p n x : ℕ} (hp : 0<p)
    (hm1 : r≤4*m) (hm2 : 4*m≤r+3)
    (hhi : p*(2*(2*n+1))≤r)
    (hw : x≤2*r+2*m-min (m%p) (p-m%p)) :
    4*x+4*((n+1)*p)≤11*r+100 := by
  have hnp : n*p≤m := by nlinarith
  have hhalf : 2*(n*p)+p≤2*m := by nlinarith
  have hd := dist_ge p m n hp hnp
  have hs : (n+1)*p=n*p+p := by ring
  rw [hs] at hd ⊢
  have hm : m%p≤m := Nat.mod_le _ _
  generalize n*p=k at *
  generalize m%p=s0 at *
  omega

private lemma right_key {r m p n x : ℕ} (hp : 0<p)
    (hm1 : r≤4*m) (hm2 : 4*m≤r+3)
    (hlo : r<p*(2*(2*n+1))) (hhi : p*(4*n)≤r)
    (hw : x≤2*r+2*m-min (m%p) (p-m%p)) :
    4*x≤9*r+4*(n*p)+100 := by
  have hnp : n*p≤m := by nlinarith
  have hhalf : 4*m≤4*(n*p)+2*p+2 := by nlinarith
  have hd := dist_ge p m n hp hnp
  have hs : (n+1)*p=n*p+p := by ring
  rw [hs] at hd
  have hm : m%p≤m := Nat.mod_le _ _
  generalize n*p=k at *
  generalize m%p=s0 at *
  omega

/-- A single proof covers every strip, modulus, residue and node level. -/
theorem quarterD1Pair_covers {M : ℕ} {c : ZMod M} {r m : ℕ} {w : ℕ→ℕ}
    (hm1 : r≤4*m) (hm2 : 4*m≤r+3)
    (hw : ∀ p : ℕ, p.Prime → (p : ZMod M)=c →
      w p≤2*r+2*m-min (m%p) (p-m%p)) (n : ℕ) (hn : 0<n) :
    ∀ P∈quarterD1Pair n, Covers c (fun p => (w p : ℝ)) r P := by
  intro P hP
  simp only [quarterD1Pair, List.mem_cons, List.mem_nil_iff, or_false] at hP
  rcases hP with rfl | rfl
  · intro p hlo hhi hp hc
    rw [floor_mk_t] at hhi
    have ht := (Nat.le_div_iff_mul_le (by positivity : 0<2*(2*n+1))).mp hhi
    simp only [one_mul] at ht
    have hk := left_key hp.pos hm1 hm2 ht (hw p hp hc)
    apply real_of_int_bound 4 11 (-4*((n+1 : ℕ) : ℤ)) 100 (by norm_num)
    have hh : (4 : ℤ)*(w p)+4*(((n+1 : ℕ) : ℤ)*p)≤11*r+100 := by exact_mod_cast hk
    push_cast at hh ⊢
    nlinarith
  · intro p hlo hhi hp hc
    rw [floor_mk_s] at hlo
    rw [floor_mk_t] at hhi
    have hs := (Nat.div_lt_iff_lt_mul (by positivity : 0<2*(2*n+1))).mp hlo
    have ht := (Nat.le_div_iff_mul_le (by positivity : 0<4*n)).mp hhi
    simp only [one_mul] at hs ht
    have hk := right_key hp.pos hm1 hm2 hs ht (hw p hp hc)
    apply real_of_int_bound 4 9 (4*(n : ℤ)) 100 (by norm_num)
    have hh : (4 : ℤ)*(w p)≤9*r+4*((n : ℤ)*p)+100 := by exact_mod_cast hk
    nlinarith

theorem quarterD1Prefix_covers {M : ℕ} {c : ZMod M} {r m : ℕ} {w : ℕ→ℕ}
    (hm1 : r≤4*m) (hm2 : 4*m≤r+3)
    (hw : ∀ p : ℕ, p.Prime → (p : ZMod M)=c →
      w p≤2*r+2*m-min (m%p) (p-m%p)) (K : ℕ) :
    ∀ P∈quarterD1Prefix K, Covers c (fun p => (w p : ℝ)) r P := by
  intro P hP
  obtain ⟨j,hj,hP⟩ := List.mem_flatMap.mp hP
  exact quarterD1Pair_covers hm1 hm2 hw (j+1) (by omega) P hP

lemma quarterD1Prefix16_chain : Chain (1/68) (quarterD1Prefix 16) := by
  norm_num [quarterD1Prefix, quarterD1Pair, List.range_succ, Chain, mkPiece]
lemma quarterD1Prefix16_end : lastEnd (1/68) (quarterD1Prefix 16)=(1/4 : ℝ) := by
  norm_num [quarterD1Prefix, quarterD1Pair, List.range_succ, lastEnd, mkPiece]
lemma quarterD1Prefix16_integral :
    (5/2 : ℝ)*(1/68)+listInt (quarterD1Prefix 16)=
      (5/2 : ℝ)*(1/4)-(3163/768-339258406689121/82516315939200) := by
  norm_num [quarterD1Prefix, quarterD1Pair, List.range_succ, listInt, Piece.int, mkPiece]
end CatalanArchive.CatalanCore.Arith.Hybrid.D1QuarterPrefix
