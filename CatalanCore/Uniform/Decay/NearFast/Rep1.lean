import CatalanCore.Uniform.Decay.NearFast.Basic
set_option Elab.async false

namespace CatalanCore.Uniform.Decay.NearFast

open Finset CatalanCore.Uniform.Decay.Tools CatalanCore.Uniform.Decay.NearCells

theorem prodDen_dvd (a : ℕ → ℚ) : ∀ N k, k < N → (a k).den ∣ prodDen a N := by
  intro N
  induction N with
  | zero => intro k h; omega
  | succ N ih =>
    intro k h
    unfold prodDen
    by_cases hk : k < N
    · exact Dvd.dvd.mul_right (ih k hk) _
    · have : k = N := by omega
      subst this; exact Dvd.intro_left _ rfl

theorem fwI_cast (a : ℕ → ℚ) (d k : ℕ) (hk : k ≤ d) :
    ((fwI a d k : ℤ) : ℚ) = wq a k * (fDw a d : ℚ) :=
  sc_cast _ _ (prodDen_dvd (wq a) (d + 1) k (by omega))

theorem fwI_castC (a : ℕ → ℚ) (d k : ℕ) (hk : k ≤ d) :
    ((fwI a d k : ℤ) : ℂ) = (wq a k : ℂ) * (fDw a d : ℂ) := by
  have := congrArg (fun x : ℚ => (x : ℂ)) (fwI_cast a d k hk)
  simpa using this

theorem gget_map_range (f : ℕ → GZ) (n m : ℕ) (h : m < n) :
    gget ((List.range n).map f) m = f m := by
  simp [gget, List.getD_eq_getElem?_getD, List.getElem?_map, h]

theorem PBc_rep (a : ℕ → ℚ) (d : ℕ) (z0 e : CQ) {Dp : List ℤ} {Zp Ep : List GZ}
    (hD : ∀ i, i < d + 2 → iget Dp i = (fD z0 e : ℤ) ^ i)
    (hZ : ∀ i, i < d + 2 → (gget Zp i).toC = (fZ z0 e).toC ^ i) (m : ℕ)
    (hE : (gget Ep m).toC = (fE z0 e).toC ^ m) :
    (PBc a d z0 e m).toC * ((fDw a d : ℂ) * (fD z0 e : ℂ) ^ (d + 1)) = (fPBm a d Dp Zp Ep m).toC := by
  unfold PBc fPBm
  rw [GZ.toC_mul, toC_sumG, hE]
  simp only [CQ.toC_sumTo, CQ.toC_smul, CQ.toC_mul, CQ.toC_pow, GZ.toC_smul]
  rw [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k < d + 1 := Finset.mem_range.1 hk
  rw [hZ (k + 1 - m) (by omega), fZ_toC, fE_toC]
  have hdk : iget Dp (d - k) = (fD z0 e : ℤ) ^ (d - k) := hD (d - k) (by omega)
  rw [hdk]
  have hw := fwI_castC a d k (by omega)
  rcases Nat.lt_or_ge (k + 1) m with hlt | hge
  · have h0 : (chooseFast (k + 1) m) = 0 := by
      rw [chooseFast_eq]; exact Nat.choose_eq_zero_of_lt hlt
    rw [h0, Nat.choose_eq_zero_of_lt hlt]; simp
  · have key : (fD z0 e : ℂ) ^ (d + 1) =
        (fD z0 e : ℂ) ^ (d - k) * (fD z0 e : ℂ) ^ m * (fD z0 e : ℂ) ^ (k + 1 - m) := by
      rw [← pow_add, ← pow_add]; congr 1; omega
    rw [key, chooseFast_eq]
    push_cast
    rw [hw]
    simp only [mul_pow]
    ring

end CatalanCore.Uniform.Decay.NearFast
