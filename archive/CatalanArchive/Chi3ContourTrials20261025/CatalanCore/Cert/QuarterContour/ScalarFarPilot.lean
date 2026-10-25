module
public import CatalanCore.Cert.SigmaQuarterContour.Data
public import CatalanCore.Cert.QuarterContour.RawMacroNums
public import CatalanCore.Cert.QuarterContour.ScalarFar
@[expose] public section
namespace CatalanCore.Cert.QuarterContour.ScalarFarPilot
open CatalanCore.Cert.SigmaP6 CatalanCore.Cert.SigmaQuarter
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
def sample : Macro := raw_macro% [-118480051372,1997537280,2270,2401,-355215951177928933392948880920,-19851469489131309050549746208,524113431416798837792,2160348492126355351605346304,489123777193816621056,6251753556478520848,-118471925933,-118471661739,1977404620,1978033767,-78981283956,-78981107826,1318269746,1318689178,-118472188077,-118471923883,1978033766,1978662912,-78981458718,-78981282588,1318689177,1319108608,-118472450221,-118472186028,1978662912,1979292058,-78981633481,-78981457352,1319108608,1319528039,-118472712365,-118472448171,1979292057,1979921204,-78981808244,-78981632114,1319528038,1319947470,-118472974509,-118472710315,1979921203,1980550349,-78981983006,-78981806876,1319947468,1320366900,-118473236653,-118472972459,1980550348,1981179495,-78982157769,-78981981639,1320366898,1320786330,-118473498797,-118473234603,1981179494,1981808640,-78982332532,-78982156402,1320786329,1321205760,-118473760941,-118473496748,1981808640,1982437786,-78982507294,-78982331165,1321205760,1321625191]

set_option profiler true in
private theorem scalarL : ScalarFar.sumL sample.x0 sample.y0
    (macroFar SigmaQuarterContour.pts sample) = sample.fd.1 := by decide +kernel

set_option profiler true in
private theorem scalarAx : ScalarFar.sumAx sample.x0 sample.y0
    (macroFar SigmaQuarterContour.pts sample) = sample.fd.2.1 := by decide +kernel

set_option profiler true in
private theorem scalarEx : ScalarFar.sumEx sample.x0 sample.y0
    (macroFar SigmaQuarterContour.pts sample) = sample.fd.2.2.1 := by decide +kernel

set_option profiler true in
private theorem scalarAy : ScalarFar.sumAy sample.x0 sample.y0
    (macroFar SigmaQuarterContour.pts sample) = sample.fd.2.2.2.1 := by decide +kernel

set_option profiler true in
private theorem scalarEy : ScalarFar.sumEy sample.x0 sample.y0
    (macroFar SigmaQuarterContour.pts sample) = sample.fd.2.2.2.2.1 := by decide +kernel

set_option profiler true in
private theorem scalarH : ScalarFar.sumH sample.x0 sample.y0
    (macroFar SigmaQuarterContour.pts sample) = sample.fd.2.2.2.2.2 := by decide +kernel

theorem far_checked : SigmaQuarter.farOK SigmaQuarterContour.pts sample :=
  ScalarFar.farOK_of_components _ _ scalarL scalarAx scalarEx scalarAy scalarEy scalarH
end CatalanCore.Cert.QuarterContour.ScalarFarPilot
#print axioms CatalanCore.Cert.QuarterContour.ScalarFarPilot.far_checked
