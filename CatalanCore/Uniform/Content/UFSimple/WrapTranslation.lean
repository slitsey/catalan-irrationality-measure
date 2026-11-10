module

public import CatalanCore.Uniform.Content.UFSimple.WrapExpr
public import CatalanCore.Uniform.Content.UFSimple.WrapPrefixClosed

@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 1200000

/-! Generic lattice covariance of full-wrap prices. All natural arguments are
arbitrary; only the positive prefix index prevents lower-window truncation. -/
namespace CatalanCore.Uniform.Content.UFSimple.WrapExpr
open CatalanCore.Uniform.Content.UFSimple

theorem closedBound_translate (d A p t0 tv w L : ℕ)
    (hd : 2*d≤p) (hw : p≤w) (ht : w≤t0) :
    closedBound d (A+L) p (t0+L) (tv+L) (w+L) = closedBound d A p t0 tv w+2*L := by
  have ho : min (tv+1) (A+2*d)-t0≤A := by omega
  have hshift : min (tv+L+1) (A+L+2*d)-(t0+L) =
      min (tv+1) (A+2*d)-t0 := by omega
  by_cases hwin : w≤tv
  · have hb := WrapPrefixClosed.beta3_translate d A p w tv L hw hwin
    unfold closedBound
    rw [hshift,hb]
    have hwlen : tv+L+1-(w+L)=tv+1-w := by omega
    rw [hwlen]
    omega
  · have hz : min (tv+1) (A+2*d)-t0=0 := by omega
    unfold closedBound
    rw [hshift,hz]
    simp only [Nat.zero_sub, Nat.add_zero]
    omega

theorem dim_shift (m p h : ℕ) : dim (m+h*p) p=dim m p := by
  simp [dim,Nat.add_mod,Nat.mul_mod]

theorem dim_le (m p : ℕ) : dim m p≤m :=
  le_trans (Nat.min_le_left _ _) (Nat.mod_le _ _)

theorem twice_dim_le (m p : ℕ) : 2*dim m p≤p := by
  by_cases hp : p=0
  · subst p; simp [dim]
  · have h := Nat.mod_lt m (Nat.pos_of_ne_zero hp)
    unfold dim
    omega

theorem candidate_cov (a b t ν r p m k j : ℕ) (z : Bool) (hν : 1≤ν) :
    candidate (r+t*b*p) p (m+t*a*p) k (ν+a*t) j z =
      candidate r p m k ν j z+t*(2*b+2*a)*p := by
  by_cases hp : p=0
  · subst p; simp [candidate]
  have hp0 : 0<p := Nat.pos_of_ne_zero hp
  let L := t*(b+a)*p
  have hdim : dim (m+t*a*p) p=dim m p := dim_shift m p (t*a)
  have hvirt : virtual (r+t*b*p) (m+t*a*p) p=virtual r m p+L := by
    unfold virtual
    rw [hdim]
    have hd := dim_le m p
    have he : t*b*p+t*a*p=L := by dsimp [L];ring
    omega
  have hB : p*((r+t*b*p)/p)+(ν+a*t+j)*p =
      p*(r/p)+(ν+j)*p+L := by
    rw [Nat.add_mul_div_right _ _ hp0]
    dsimp [L]
    ring
  have hBp : p≤p*(r/p)+(ν+j)*p := by
    have hh : p≤(ν+j)*p := by
      simpa only [Nat.one_mul] using Nat.mul_le_mul_right p (show 1≤ν+j by omega)
    omega
  unfold candidate
  rw [hdim,hvirt,hB]
  let A := virtual r m p
  let B := p*(r/p)+(ν+j)*p
  let lo := if z then k else 0
  let hi := if z then p-1 else k-1
  have htv : min (B+L+hi) (A+L+p-1) = min (B+hi) (A+p-1)+L := by omega
  have ht0 : max (A+L) (B+L+lo)=max A (B+lo)+L := by omega
  change closedBound (dim m p) (A+L) p (max (A+L) (B+L+lo))
    (min (B+L+hi) (A+L+p-1)) (B+L+lo) = _
  rw [htv,ht0,show B+L+lo=(B+lo)+L by omega]
  rw [closedBound_translate _ _ _ _ _ _ _ (twice_dim_le m p) (by dsimp [B];omega) (by omega)]
  have he : 2*L=t*(2*b+2*a)*p := by dsimp [L];ring
  rw [he]

theorem wrap_cov (a b t ν r p m k : ℕ) (hν : 1≤ν) :
    (tWrap (ν+a*t)).evalN (r+t*b*p) p (m+t*a*p) k =
      (tWrap ν).evalN r p m k+t*(2*b+2*a)*p := by
  simp only [evalN_tWrap,price,candidate_cov a b t ν r p m k _ _ hν]
  omega

end CatalanCore.Uniform.Content.UFSimple.WrapExpr
#print axioms CatalanCore.Uniform.Content.UFSimple.WrapExpr.closedBound_translate
#print axioms CatalanCore.Uniform.Content.UFSimple.WrapExpr.candidate_cov
#print axioms CatalanCore.Uniform.Content.UFSimple.WrapExpr.wrap_cov
