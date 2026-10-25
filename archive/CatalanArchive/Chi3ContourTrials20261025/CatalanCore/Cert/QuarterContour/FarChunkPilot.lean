module
public import CatalanCore.Cert.QuarterContour.FarChunks
public import CatalanCore.Cert.QuarterContour.FarChunkData
public import CatalanCore.Cert.QuarterContour.RawMacroNums
@[expose] public section
namespace CatalanCore.Cert.QuarterContour.FarChunkPilot
open CatalanCore.Cert.SigmaP6 CatalanCore.Cert.SigmaQuarter
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
def sample : Macro := raw_macro% [-118480051372,1997537280,2270,2401,-355215951177928933392948880920,-19851469489131309050549746208,524113431416798837792,2160348492126355351605346304,489123777193816621056,6251753556478520848,-118471925933,-118471661739,1977404620,1978033767,-78981283956,-78981107826,1318269746,1318689178,-118472188077,-118471923883,1978033766,1978662912,-78981458718,-78981282588,1318689177,1319108608,-118472450221,-118472186028,1978662912,1979292058,-78981633481,-78981457352,1319108608,1319528039,-118472712365,-118472448171,1979292057,1979921204,-78981808244,-78981632114,1319528038,1319947470,-118472974509,-118472710315,1979921203,1980550349,-78981983006,-78981806876,1319947468,1320366900,-118473236653,-118472972459,1980550348,1981179495,-78982157769,-78981981639,1320366898,1320786330,-118473498797,-118473234603,1981179494,1981808640,-78982332532,-78982156402,1320786329,1321205760,-118473760941,-118473496748,1981808640,1982437786,-78982507294,-78982331165,1321205760,1321625191]
def parts : List (List Pt) := [FarChunkData.p00,FarChunkData.p01,FarChunkData.p02,FarChunkData.p03,FarChunkData.p04,FarChunkData.p05,FarChunkData.p06,FarChunkData.p07,FarChunkData.p08,FarChunkData.p09,FarChunkData.p10,FarChunkData.p11,FarChunkData.p12,FarChunkData.p13,FarChunkData.p14,FarChunkData.p15,FarChunkData.p16,FarChunkData.p17,FarChunkData.p18,FarChunkData.p19,FarChunkData.p20,FarChunkData.p21,FarChunkData.p22,FarChunkData.p23,FarChunkData.p24,FarChunkData.p25,FarChunkData.p26,FarChunkData.p27,FarChunkData.p28,FarChunkData.p29,FarChunkData.p30,FarChunkData.p31,FarChunkData.p32,FarChunkData.p33,FarChunkData.p34,(FarChunkData.p35.take 30),(FarChunkData.p37.drop 33),FarChunkData.p38,FarChunkData.p39,FarChunkData.p40,FarChunkData.p41,FarChunkData.p42,FarChunkData.p43,FarChunkData.p44,FarChunkData.p45,FarChunkData.p46]
def fd00 : FD := (572742649096665003385744,11135088266984351055808,24106715472353984,-24641894360629641216,57931768156651520,17502223392)
def fd01 : FD := (302299042427688288432800,7252633953425801545888,13983336314742464,-17008294210249424896,33606510186594304,12080719992)
def fd02 : FD := (214454680864759414443152,6494572274855234492608,11176168558563008,-16124449514395271168,26862147989405696,11451794016)
def fd03 : FD := (156492535122962217719096,6257115702621345529504,9584187759313600,-16467102523673018368,23037814533783552,11695540984)
def fd04 : FD := (110292229922729166163728,6262418215219205112096,8510776045040320,-17501526921258729472,20459580947431424,12428305688)
def fd05 : FD := (69526797473664941237560,6446063512574713573376,7742720068706368,-19165350888849539072,18615160074665984,13609090000)
def fd06 : FD := (30307704049282830793064,6673684389699016220096,7058610107340800,-21149796420908744704,16972369156374528,15016898480)
def fd07 : FD := (-8108812167956274297872,7125507060993028070304,6609761316263936,-24119115130892451840,15895131979776000,17123171656)
def fd08 : FD := (-47828533997958644047072,7624796772341493043072,6175628933879808,-27627345962857398272,14853214236049408,19612090976)
def fd09 : FD := (-91452704152966174793192,8402263660695184165664,5912004165236160,-32672091417742934016,14221377704820736,23191235416)
def fd10 : FD := (-139143681395181904023264,9293516326873849826272,5652122708868608,-38883144205699907584,13598589328556032,27596018840)
def fd11 : FD := (-195825120104944623875040,10557079805533565120416,5519980449080320,-47654099343414132736,13283237678809088,33816274248)
def fd12 : FD := (-266172634117925757556352,12299429819020470432832,5493874619142720,-60091958129506910208,13223300512612352,42635709216)
def fd13 : FD := (-360767653339151828508472,14875048465404447825248,5639122123856960,-78922489720676024320,13576240947527680,55986972872)
def fd14 : FD := (-507937758199157956484440,19236753313675021717024,6142999614272064,-111262639655106379776,14793472855769088,78913231800)
def fd15 : FD := (-782000954574273977527256,27817443312453231281152,7417125461455552,-176179448851700121600,17867547075411968,124927172336)
def fd16 : FD := (-1621247136274485562626216,55127474209609199410688,12098579645840832,-385104935614848434176,29156092616376320,273001308976)
def fd17 : FD := (-934520990226750806111860008,30790243925301909685811520,5344285985070726464,-241866424868691829063680,12885684521439068160,171399258158880)
def fd18 : FD := (-3464958406073400875398544456,113053145026728743770538880,16720011116772341696,-963596314576991884410880,40329341652192722944,682672799222672)
def fd19 : FD := (-5266416945286757866424127984,171465013328309083769538720,20501453653614394304,-1627109028611856879058944,49478137811628457984,1152298643458232)
def fd20 : FD := (-6947289212414978815777541032,228301910258881266583931968,21741516268401609664,-2430506147230451387334656,52506161474994962432,1720460511018496)
def fd21 : FD := (-8597240875157973026434079024,288383801827872907141723552,21558306525523982208,-3470221486324784253894656,52105587049813245952,2455090876461608)
def fd22 : FD := (-10243153017734541540574500816,354682649821087491659678624,20484127262036846784,-4864301315740848529342464,49557472665531318272,3439102651656888)
def fd23 : FD := (-11864604104608393748997099016,428981228100641278034590144,18799548053249030080,-6768285238628366008451072,45536041424662822912,4781417463343840)
def fd24 : FD := (-13463231320593900256830820352,514452927048769730340629504,16757652840057795648,-9439609151769978903986176,40650119025429315584,6662021331128272)
def fd25 : FD := (-14965903968042531378534416008,612247994203442148622705760,14473280230636848320,-13230766437261206576693248,35174202916614438912,9326239604221224)
def fd26 : FD := (-16348133240367525830852230032,726257420538247911944528352,12116089021775207296,-18761526550484376407769088,29516186538078109696,13204393630584312)
def fd27 : FD := (-17529628590378361103223705888,859322460793118734388309248,9784889956478457280,-27018736315935123320078336,23912470991769436160,18978021638112752)
def fd28 : FD := (-18429716179306205212471726104,1015585771885912700581561632,7579786084306213760,-39733844795097023298666496,18602993683694354432,27836268464454536)
def fd29 : FD := (-18939555546483363582288888088,1199350034925636243104904512,5580342380962116032,-60036753330979276307038208,13778189335904911360,41912601337094848)
def fd30 : FD := (-18962635909670931818639066240,1417663241536219719014760800,3857935767720833984,-94149310966490555572289536,9609601284759879680,65412339241946152)
def fd31 : FD := (-18380025004561020790710722376,1678876559822911013462885312,2456368386879349696,-155385440438264127361122304,6202588057097469952,107242215644344928)
def fd32 : FD := (-17098926417409160317507005848,1997511898342700292286169792,1398220846873187584,-276483708835262766349549568,3612519826507956224,189122048854136368)
def fd33 : FD := (-15061227353160985037077646904,2403338744437364509669460416,675496361739118976,-554852309990228066065448960,1822222254338998272,376074645519225232)
def fd34 : FD := (-12282688412518869641802263808,3001697434152929974961814272,248765727083212608,-1391806975248201233482121216,740159250532139008,960542682799265872)
def fd35 : FD := (-4627984474578278506975517864,1809112104635649605766029888,37558939347294592,-1575209869344220065545846784,137725670567444480,1218681419910605616)
def fd36 : FD := (-18073347079738838162938055032,-14637378794166393362326136064,1004100898529299008,5111207751963435018926161920,204572203407114240,2558754624178031472)
def fd37 : FD := (-37605379402762209315471410000,-12545724070623988392524987584,8739022072966594816,969791912037149292437176320,564020535424450560,485493773914031696)
def fd38 : FD := (-30213528273510333640529213448,-5976911812267355218889246592,17243101568930684160,203859982382815021891584000,564023092272168960,102055658729352032)
def fd39 : FD := (-25980933643006829130358723376,-3959449921717838000509759840,25747127345156365312,88350635871887330535014400,564022708745011200,44229781001088520)
def fd40 : FD := (-9656301831266700555467959376,-1295181554461359494097463136,12895716564790852000,23069048708574205999841280,229203611882618880,11548745131694272)
def fd41 : FD := (-2660856575200745498141496,-230602620217526362769120,25609844101455232,1293911946436175462400,134042741637120,647753658184)
def fd42 : FD := (-2702018430860646706036512,-264404145704215685831584,81317418211934784,861713923936238960640,258593186119680,431388285544)
def fd43 : FD := (-135231588647252279828389768,-31346762546651461285717088,21798288086944932576,66743598997567564677120,46365956426956800,33412966071664)
def fd44 : FD := (-143532335646586609316620448,-253665120787259326233063072,233340223519414075872,471766347738895047720960,430870469227315200,236174204773472)
def fd45 : FD := (8070189579174100638994416,-2613911295329296582767072,2974464975860119552,4347525746309159976960,4946988965560320,2176445334376)
def fds : List FD := [fd00,fd01,fd02,fd03,fd04,fd05,fd06,fd07,fd08,fd09,fd10,fd11,fd12,fd13,fd14,fd15,fd16,fd17,fd18,fd19,fd20,fd21,fd22,fd23,fd24,fd25,fd26,fd27,fd28,fd29,fd30,fd31,fd32,fd33,fd34,fd35,fd36,fd37,fd38,fd39,fd40,fd41,fd42,fd43,fd44,fd45]

set_option profiler true in
theorem partition_checked : parts.flatten = macroFar SigmaQuarterContour.pts sample := by
  rw [←FarChunkData.witness_reconstruction]
  decide +kernel

set_option profiler true in
private theorem chunk00_checked : FastMacros.farSum sample.x0 sample.y0 FarChunkData.p00 = fd00 := by decide +kernel

set_option profiler true in
private theorem chunk01_checked : FastMacros.farSum sample.x0 sample.y0 FarChunkData.p01 = fd01 := by decide +kernel

set_option profiler true in
private theorem chunk02_checked : FastMacros.farSum sample.x0 sample.y0 FarChunkData.p02 = fd02 := by decide +kernel

set_option profiler true in
private theorem chunk03_checked : FastMacros.farSum sample.x0 sample.y0 FarChunkData.p03 = fd03 := by decide +kernel

set_option profiler true in
private theorem chunk04_checked : FastMacros.farSum sample.x0 sample.y0 FarChunkData.p04 = fd04 := by decide +kernel

set_option profiler true in
private theorem chunk05_checked : FastMacros.farSum sample.x0 sample.y0 FarChunkData.p05 = fd05 := by decide +kernel

set_option profiler true in
private theorem chunk06_checked : FastMacros.farSum sample.x0 sample.y0 FarChunkData.p06 = fd06 := by decide +kernel

set_option profiler true in
private theorem chunk07_checked : FastMacros.farSum sample.x0 sample.y0 FarChunkData.p07 = fd07 := by decide +kernel

set_option profiler true in
private theorem chunk08_checked : FastMacros.farSum sample.x0 sample.y0 FarChunkData.p08 = fd08 := by decide +kernel

set_option profiler true in
private theorem chunk09_checked : FastMacros.farSum sample.x0 sample.y0 FarChunkData.p09 = fd09 := by decide +kernel

set_option profiler true in
private theorem chunk10_checked : FastMacros.farSum sample.x0 sample.y0 FarChunkData.p10 = fd10 := by decide +kernel

set_option profiler true in
private theorem chunk11_checked : FastMacros.farSum sample.x0 sample.y0 FarChunkData.p11 = fd11 := by decide +kernel

set_option profiler true in
private theorem chunk12_checked : FastMacros.farSum sample.x0 sample.y0 FarChunkData.p12 = fd12 := by decide +kernel

set_option profiler true in
private theorem chunk13_checked : FastMacros.farSum sample.x0 sample.y0 FarChunkData.p13 = fd13 := by decide +kernel

set_option profiler true in
private theorem chunk14_checked : FastMacros.farSum sample.x0 sample.y0 FarChunkData.p14 = fd14 := by decide +kernel

set_option profiler true in
private theorem chunk15_checked : FastMacros.farSum sample.x0 sample.y0 FarChunkData.p15 = fd15 := by decide +kernel

set_option profiler true in
private theorem chunk16_checked : FastMacros.farSum sample.x0 sample.y0 FarChunkData.p16 = fd16 := by decide +kernel

set_option profiler true in
private theorem chunk17_checked : FastMacros.farSum sample.x0 sample.y0 FarChunkData.p17 = fd17 := by decide +kernel

set_option profiler true in
private theorem chunk18_checked : FastMacros.farSum sample.x0 sample.y0 FarChunkData.p18 = fd18 := by decide +kernel

set_option profiler true in
private theorem chunk19_checked : FastMacros.farSum sample.x0 sample.y0 FarChunkData.p19 = fd19 := by decide +kernel

set_option profiler true in
private theorem chunk20_checked : FastMacros.farSum sample.x0 sample.y0 FarChunkData.p20 = fd20 := by decide +kernel

set_option profiler true in
private theorem chunk21_checked : FastMacros.farSum sample.x0 sample.y0 FarChunkData.p21 = fd21 := by decide +kernel

set_option profiler true in
private theorem chunk22_checked : FastMacros.farSum sample.x0 sample.y0 FarChunkData.p22 = fd22 := by decide +kernel

set_option profiler true in
private theorem chunk23_checked : FastMacros.farSum sample.x0 sample.y0 FarChunkData.p23 = fd23 := by decide +kernel

set_option profiler true in
private theorem chunk24_checked : FastMacros.farSum sample.x0 sample.y0 FarChunkData.p24 = fd24 := by decide +kernel

set_option profiler true in
private theorem chunk25_checked : FastMacros.farSum sample.x0 sample.y0 FarChunkData.p25 = fd25 := by decide +kernel

set_option profiler true in
private theorem chunk26_checked : FastMacros.farSum sample.x0 sample.y0 FarChunkData.p26 = fd26 := by decide +kernel

set_option profiler true in
private theorem chunk27_checked : FastMacros.farSum sample.x0 sample.y0 FarChunkData.p27 = fd27 := by decide +kernel

set_option profiler true in
private theorem chunk28_checked : FastMacros.farSum sample.x0 sample.y0 FarChunkData.p28 = fd28 := by decide +kernel

set_option profiler true in
private theorem chunk29_checked : FastMacros.farSum sample.x0 sample.y0 FarChunkData.p29 = fd29 := by decide +kernel

set_option profiler true in
private theorem chunk30_checked : FastMacros.farSum sample.x0 sample.y0 FarChunkData.p30 = fd30 := by decide +kernel

set_option profiler true in
private theorem chunk31_checked : FastMacros.farSum sample.x0 sample.y0 FarChunkData.p31 = fd31 := by decide +kernel

set_option profiler true in
private theorem chunk32_checked : FastMacros.farSum sample.x0 sample.y0 FarChunkData.p32 = fd32 := by decide +kernel

set_option profiler true in
private theorem chunk33_checked : FastMacros.farSum sample.x0 sample.y0 FarChunkData.p33 = fd33 := by decide +kernel

set_option profiler true in
private theorem chunk34_checked : FastMacros.farSum sample.x0 sample.y0 FarChunkData.p34 = fd34 := by decide +kernel

set_option profiler true in
private theorem chunk35_checked : FastMacros.farSum sample.x0 sample.y0 (FarChunkData.p35.take 30) = fd35 := by decide +kernel

set_option profiler true in
private theorem chunk36_checked : FastMacros.farSum sample.x0 sample.y0 (FarChunkData.p37.drop 33) = fd36 := by decide +kernel

set_option profiler true in
private theorem chunk37_checked : FastMacros.farSum sample.x0 sample.y0 FarChunkData.p38 = fd37 := by decide +kernel

set_option profiler true in
private theorem chunk38_checked : FastMacros.farSum sample.x0 sample.y0 FarChunkData.p39 = fd38 := by decide +kernel

set_option profiler true in
private theorem chunk39_checked : FastMacros.farSum sample.x0 sample.y0 FarChunkData.p40 = fd39 := by decide +kernel

set_option profiler true in
private theorem chunk40_checked : FastMacros.farSum sample.x0 sample.y0 FarChunkData.p41 = fd40 := by decide +kernel

set_option profiler true in
private theorem chunk41_checked : FastMacros.farSum sample.x0 sample.y0 FarChunkData.p42 = fd41 := by decide +kernel

set_option profiler true in
private theorem chunk42_checked : FastMacros.farSum sample.x0 sample.y0 FarChunkData.p43 = fd42 := by decide +kernel

set_option profiler true in
private theorem chunk43_checked : FastMacros.farSum sample.x0 sample.y0 FarChunkData.p44 = fd43 := by decide +kernel

set_option profiler true in
private theorem chunk44_checked : FastMacros.farSum sample.x0 sample.y0 FarChunkData.p45 = fd44 := by decide +kernel

set_option profiler true in
private theorem chunk45_checked : FastMacros.farSum sample.x0 sample.y0 FarChunkData.p46 = fd45 := by decide +kernel

set_option profiler true in
theorem rows_checked : List.Forall₂
    (fun ps fd => FastMacros.farSum sample.x0 sample.y0 ps = fd) parts fds := by
  exact List.Forall₂.cons chunk00_checked (List.Forall₂.cons chunk01_checked (List.Forall₂.cons chunk02_checked (List.Forall₂.cons chunk03_checked (List.Forall₂.cons chunk04_checked (List.Forall₂.cons chunk05_checked (List.Forall₂.cons chunk06_checked (List.Forall₂.cons chunk07_checked (List.Forall₂.cons chunk08_checked (List.Forall₂.cons chunk09_checked (List.Forall₂.cons chunk10_checked (List.Forall₂.cons chunk11_checked (List.Forall₂.cons chunk12_checked (List.Forall₂.cons chunk13_checked (List.Forall₂.cons chunk14_checked (List.Forall₂.cons chunk15_checked (List.Forall₂.cons chunk16_checked (List.Forall₂.cons chunk17_checked (List.Forall₂.cons chunk18_checked (List.Forall₂.cons chunk19_checked (List.Forall₂.cons chunk20_checked (List.Forall₂.cons chunk21_checked (List.Forall₂.cons chunk22_checked (List.Forall₂.cons chunk23_checked (List.Forall₂.cons chunk24_checked (List.Forall₂.cons chunk25_checked (List.Forall₂.cons chunk26_checked (List.Forall₂.cons chunk27_checked (List.Forall₂.cons chunk28_checked (List.Forall₂.cons chunk29_checked (List.Forall₂.cons chunk30_checked (List.Forall₂.cons chunk31_checked (List.Forall₂.cons chunk32_checked (List.Forall₂.cons chunk33_checked (List.Forall₂.cons chunk34_checked (List.Forall₂.cons chunk35_checked (List.Forall₂.cons chunk36_checked (List.Forall₂.cons chunk37_checked (List.Forall₂.cons chunk38_checked (List.Forall₂.cons chunk39_checked (List.Forall₂.cons chunk40_checked (List.Forall₂.cons chunk41_checked (List.Forall₂.cons chunk42_checked (List.Forall₂.cons chunk43_checked (List.Forall₂.cons chunk44_checked (List.Forall₂.cons chunk45_checked (List.Forall₂.nil))))))))))))))))))))))))))))))))))))))))))))))

set_option profiler true in
theorem total_checked : FarChunks.foldFD fds = sample.fd := by decide +kernel

set_option profiler true in
theorem far_checked : SigmaQuarter.farOK SigmaQuarterContour.pts sample :=
  FarChunks.farOK_of_chunks _ _ parts fds partition_checked rows_checked total_checked
end CatalanCore.Cert.QuarterContour.FarChunkPilot
#print axioms CatalanCore.Cert.QuarterContour.FarChunkPilot.far_checked
