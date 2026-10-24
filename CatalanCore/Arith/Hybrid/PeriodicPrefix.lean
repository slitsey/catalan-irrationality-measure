module
public import CatalanCore.Arith.Hybrid.D1Exact
@[expose] public section
namespace CatalanCore.Arith.Hybrid

/-! Shared nearest-multiple arithmetic for periodic prefix strips.
The period p, strip index n, dimensions and rounding slacks are inputs. -/
theorem periodic_left {r m p n x L : ℕ} (hp : 0 < p)
    (hn : n*p ≤ m) (hhalf : 2*(n*p)+p ≤ 2*m+2*L)
    (hw : x ≤ 2*r+2*m-min (m%p) (p-m%p)) :
    x+(n+1)*p ≤ 2*r+3*m+2*L := by
  have hd := dist_ge p m n hp hn
  have hs : (n+1)*p=n*p+p := by ring
  rw [hs] at hd ⊢
  have hm := Nat.mod_le m p
  generalize n*p=k at *
  generalize m%p=s0 at *
  omega

theorem periodic_right {r m p n x U : ℕ} (hp : 0 < p)
    (hn : n*p ≤ m) (hhalf : 2*m ≤ 2*(n*p)+p+2*U)
    (hw : x ≤ 2*r+2*m-min (m%p) (p-m%p)) :
    x ≤ 2*r+m+n*p+2*U := by
  have hd := dist_ge p m n hp hn
  have hs : (n+1)*p=n*p+p := by ring
  rw [hs] at hd
  have hm := Nat.mod_le m p
  generalize n*p=k at *
  generalize m%p=s0 at *
  omega
end CatalanCore.Arith.Hybrid
