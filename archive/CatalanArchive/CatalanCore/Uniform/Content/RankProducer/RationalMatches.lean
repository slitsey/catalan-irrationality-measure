import CatalanCore.Uniform.Content.RankProducer.LineScores
set_option Elab.async false
namespace CatalanCore.Uniform.Content.RankProducer

/-- Number of killed row loads on a fixed rational line. This finite count is computable. -/
def rationalRowMatches (c : FibreCert) (v : ℚ × ℚ) : ℕ :=
  (c.kr.filter (fun d => (c.rload d).1 * v.2 - (c.rload d).2 * v.1 = 0)).card

/-- Number of killed column loads on a fixed rational line. -/
def rationalColMatches (c : FibreCert) (v : ℚ × ℚ) : ℕ :=
  (c.kc.filter (fun d => (c.cload d).1 * v.2 - (c.cload d).2 * v.1 = 0)).card

end CatalanCore.Uniform.Content.RankProducer
