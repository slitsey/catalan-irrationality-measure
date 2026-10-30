import CatalanCore.Uniform.Bank.Sevenths.PrimeBound
import CatalanCore.Uniform.Content.RankProducer.RationalLoads
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Sevenths
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer

theorem rank_rational_mem (p : ℕ) [Fact p.Prime] (q : ℚ)
    (hp : rankPrimeCutoff < p) (hq : q.den ≤ rankPrimeCutoff) : q ∈ S p :=
  rational_mem_of_den_lt p q (hq.trans_lt hp)

theorem rank_castV_ne_zero_of_fst (p : ℕ) [Fact p.Prime] (v : ℚ × ℚ)
    (hp : rankPrimeCutoff < p) (hv : v.1 ≠ 0)
    (hd : v.1.den ≤ rankPrimeCutoff) (hi : (v.1⁻¹).den ≤ rankPrimeCutoff) :
    castV p v ≠ 0 :=
  castV_ne_zero_of_fst p v (rational_red_ne_zero p v.1 hv
    (rank_rational_mem p v.1 hp hd) (rank_rational_mem p v.1⁻¹ hp hi))

theorem rank_castV_ne_zero_of_snd (p : ℕ) [Fact p.Prime] (v : ℚ × ℚ)
    (hp : rankPrimeCutoff < p) (hv : v.2 ≠ 0)
    (hd : v.2.den ≤ rankPrimeCutoff) (hi : (v.2⁻¹).den ≤ rankPrimeCutoff) :
    castV p v ≠ 0 :=
  castV_ne_zero_of_snd p v (rational_red_ne_zero p v.2 hv
    (rank_rational_mem p v.2 hp hd) (rank_rational_mem p v.2⁻¹ hp hi))

#print axioms rank_castV_ne_zero_of_fst
end CatalanCore.Uniform.Bank.Sevenths
