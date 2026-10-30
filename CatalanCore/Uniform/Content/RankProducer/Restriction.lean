module

public import CatalanCore.Uniform.Content.RankProducer.Cert

@[expose] public section
set_option Elab.async false
namespace CatalanCore.Uniform.Content.RankProducer
open CatalanCore CatalanCore.Uniform.Content.Hybrid
/-- Rebalancing may discard killed coordinates without changing any local matrix. -/
def trim (c : FibreCert) (kr kc : Finset ℕ) : FibreCert := { c with kr := kr, kc := kc }

theorem trim_ok (c : FibreCert) (h : c.Ok) (kr kc : Finset ℕ)
    (hr : kr ⊆ c.kr) (hc : kc ⊆ c.kc) : (trim c kr kc).Ok := by
  refine ⟨h.hLL, h.hPP, hr.trans h.kr_sub, hc.trans h.kc_sub, ?_, ?_⟩
  · intro d hd e he
    exact h.hrow d (hr hd) e he
  · intro d hd e he
    exact h.hcol d hd e (hc he)

theorem trim_integral (c : FibreCert) (p : ℕ) [Fact p.Prime]
    (h : c.Integral p) (kr kc : Finset ℕ) : (trim c kr kc).Integral p := ⟨h.lq, h.pq⟩

theorem trim_realizes {p : ℕ} [Fact p.Prime] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {B : ℕ} {f e : ℕ → ℚ} (PS : PoleSplit p B f e) (a b : ι → ℕ) (x : ZMod p)
    (c : FibreCert) (h : Realizes PS a b x c) (kr kc : Finset ℕ) :
    Realizes PS a b x (trim c kr kc) :=
  ⟨h.r_mem, h.r_cov, h.c_mem, h.c_cov, h.lf_r, h.lf_c, h.ee_r⟩


#print axioms trim_ok
end CatalanCore.Uniform.Content.RankProducer
