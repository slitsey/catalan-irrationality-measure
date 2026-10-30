module
public import CatalanMeasure.GenD.Uniform.W.Prof.Pilot.Check146
public import CatalanMeasure.GenD.Uniform.W.Prof.Count
@[expose] public section
set_option Elab.async false

/-!
# Pilot consequences (L0146, knot packet k152_25)

From the kernel-checked packet: for every prime `p ∤ D`, `dim V_p = 4` and every chart restricted
to `V_p` has rank at most the stored `r_j`.  Together with `ofPacketWindow` (chart
identification supplied separately) this is the L0146 cell of the `B = 532` set.
-/

namespace CatalanMeasure.GenD.Uniform.W.Prof.Pilot146
open CatalanMeasure.GenD.Uniform.W.Prof Module
noncomputable section

theorem packet_D_ne_zero : packet.D ≠ 0 := by decide +kernel

theorem packet_dim_eq (p : ℕ) [Fact p.Prime] (hp : ¬ (p : ℤ) ∣ packet.D) :
    Function.Injective (emb packet p packet.n) :=
  emb_injective packet_sound rfl (not_dvd_delta hp)

theorem packet_rank_le (p : ℕ) [Fact p.Prime] (hp : ¬ (p : ℤ) ∣ packet.D)
    (j : Fin packet.charts.length) :
    finrank (ZMod p) (LinearMap.range (chartMap packet (packet.chart j) p packet.n)) ≤
      (packet.chart j).r :=
  finrank_chartMap_le packet_sound (packet_sound.chart _ (List.get_mem _ _)) rfl
    (not_dvd_qdelta hp j)

end
end CatalanMeasure.GenD.Uniform.W.Prof.Pilot146
