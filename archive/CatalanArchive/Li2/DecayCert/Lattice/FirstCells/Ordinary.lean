module
public import CatalanArchive.Li2.DecayCert.Lattice.FirstCells.Sources
public import CatalanMeasure.CellCert.RawInts
public meta import CatalanArchive.Li2.DecayCert.Lattice.FirstCells.Sources
public meta import CatalanCore.Li2.DecayCert.Lattice.Gates.Lists.Stieltjes
public meta import CatalanCore.Li2.DecayCert.PolynomialList
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open Set Polynomial MeasureTheory
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert.LatticeFirst
open LatticeGate

namespace OrdinaryData
def decodePairs : List ℤ → List ℤ
  | a::e::rest => a*2^e.toNat :: decodePairs rest
  | _ => []
def denominators : Array ℤ := (decodePairs (raw_ints% [1,96,3125,6,144241474581317378125,9,219102799889021097371875,12,332817153031423046907878125,15,505549255454731608253066871875,18,767929319035737312936408578378125,21,1166484635615284978350404630556371875,24,354378032299923576422852926763025775625,27,2691501155317919562931567978765180765871875,30,4088390254927919816093051759744309583359378125,33,6210264797235510200645345623051606257122895371875,36,9433392227000739994780280001415389904569678069878125,39,14329322792814124052071245322149977265041340988144871875,42,21766241322284654435096221644345815465597796960992060378125,45,6612584113710078017382232135552258738448610716749387942874375,48,50222576343628042542018053069519405118517198393711601426130878125,51,76288093465970996621325422612599976375027624360047922566292803871875,54,23176322794961988773558663389707872822733392280582558875639753816275625,57,176024171627736304735178048444831294088660114371024534660483930234613371875,60,267380716702531446892735455587698735720674713729586268149275090026377711878125,63,16246052346845810713202606281508575182388195606209661652749954470002709773714875,66,123388767574293932366773794708057628510238345629162380252635904199670580731364475625,69,937137689726762416325646970807697688535260235053488278018769692396498060654713192371875,72,1423512150694952110398657748656892788885060297046248694310511162750280554134509339212878125,75,2162314956905632255695561120209820146316406591213251766657666456217676161730319686264361871875,78,656911283907931079280311468319743360450924322410585886710599069398930017933671120687113136675625,81,997848240256147309426793120377690164524954045741679961913399986416974697241246432323724854610274375,84,303146295389817552603859749970742271982681039096322372429290915873476913021890666139947610830601355125,87,2302396113485664312026314801027787555708462491936568418600464506059057154401259609332902104258417292174375,90,3497339696384724089967972182761209297121154525251647427854105584703707817535513346576678296368535866812875625,93,5312458998808395892661349745614276922327033723857252442910386383164932174836444773449974332183805981688758074375,96,8069625219189953360952590263588086645014764226539166460780876916027531973576559610870511010587201286185223514975625,99,12257760707949539155286984610390303613777426860112993853926152035445821067862794048912306225081958753715354519247974375,102,3723907703075069995376185924636574237865582280102327532822764988368440440416716832059558631179899069378724702947534615125,105,28283079004855156614882132097614781336589097417377177611788900086658305144964964339492347803811333431931414118886525401874375,108,42961997008374982898005958656276852850278838976995932792307339231633965515201780831688876313989415483103818046588632085447175625,111,65259273455721599022071051198884539479573556406056821911514848292851993617591505083335403120949922118834699612768132137794259774375,114,19825767275848221782905185354221123093894446436160062496718210911368435661024299244317295468144586339701981742358958543461896119455125,117,150576702460067244441164882765309429898128320682635674662574811871843268845479552760589859080558133250036551333216290137593101027261674375,120,228726011036842144306129456920505024015256919116923589812451139233329925376283440643335995943367804406805521475155544719003920460410483375625,123,1737174053824816086005053225311235657395876300693034664625566402477140783232872731686136889189878474469687935603806362140834775896817621237871875,126,2638767387759895634641675849247766963584336100752719655566235365362776849730733679431241934679425402719455974182181864091928024587265966660327378125,129,160331506480291258760828224600294320707384261481735246272204460799442321389639378362242259951121887469234144991309370062225546773922280134281491494875,132,6088588958589060551442451829196176828862917329768895977186964398858822154771555393306149821643853676644166656044973328113015138739698588099339639517878125,135,9248566628096782977641084328548992603042771423918952989346998921866550853097992642432041579077013734822489150532314485403669995745602155322896912427656871875,138])).toArray
def denomAt (i : ℕ) : ℤ := denominators[i]?.getD 0
def parentScale : ℤ := denomAt 0
def sharedTableCheck : Bool := decide (denominators.size=46 ∧ parentScale=2^96) && denominators.toList.all (fun n => decide (0<n))
def qv0 : ℚ := ((((raw_ints% [21591])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 1:ℚ)
def qv1 : ℚ := ((((raw_ints% [-8459248939358259500433])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 2:ℚ)
def qv2 : ℚ := ((((raw_ints% [117997973180832416074887177])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 3:ℚ)
def qv3 : ℚ := ((((raw_ints% [-1634228182904017989301522456617])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 4:ℚ)
def qv4 : ℚ := ((((raw_ints% [24056689846984649288083661016597057])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 5:ℚ)
def qv5 : ℚ := ((((raw_ints% [-346551906002682071371763850246660311361])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 6:ℚ)
def qv6 : ℚ := ((((raw_ints% [5311912927766148022426132790316821485133241])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 7:ℚ)
def qv7 : ℚ := ((((raw_ints% [-15699874413987736103285760456379644055417149381])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 8:ℚ)
def qv8 : ℚ := ((((raw_ints% [1242447582708374330653622684134828130010692127122289])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 9:ℚ)
def qv9 : ℚ := ((((raw_ints% [-18670793194191912071731439129646087288219354921649507569])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 10:ℚ)
def qv10 : ℚ := ((((raw_ints% [303535109406765592439580019724246306017334294172566952402537])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 11:ℚ)
def qv11 : ℚ := ((((raw_ints% [-4610729229841250002496267048913590685570363527402495570558186889])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 12:ℚ)
def qv12 : ℚ := ((((raw_ints% [76725013394746502503638075971743760022344067964312430071013616303009])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 13:ℚ)
def qv13 : ℚ := ((((raw_ints% [-1173050927428570916912565690335291322159336484019056899993384701208389793])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 14:ℚ)
def qv14 : ℚ := ((((raw_ints% [3986619801386290252631000204404187755435637160210425573434950561960606636549])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 15:ℚ)
def qv15 : ℚ := ((((raw_ints% [-305763496413244683269068919721479439833629053050457697562542989599007269181797433])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 16:ℚ)
def qv16 : ℚ := ((((raw_ints% [5296839518217656955684242598956923011364844272735587182570598773760059050943513250513])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 17:ℚ)
def qv17 : ℚ := ((((raw_ints% [-16263405826473355881466100658506795538888093842191591364543631737333613197822998599270621])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 18:ℚ)
def qv18 : ℚ := ((((raw_ints% [1434433610831895461963457178493179181594016891585274007245472103644691781793843170748595173577])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 19:ℚ)
def qv19 : ℚ := ((((raw_ints% [-21995647396827918089191970216329754364657367218668907690765049810541002709200878980041187529747177])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 20:ℚ)
def qv20 : ℚ := ((((raw_ints% [15790876217542490554780586046301017195741001225841701965421224706042350650421500389501906905751188777])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 21:ℚ)
def qv21 : ℚ := ((((raw_ints% [-1207299662459562911195077481495225686776548908134841051743414752201095254486419554510024499350007191246029])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 22:ℚ)
def qv22 : ℚ := ((((raw_ints% [110167703534427869044637682238609164139846270058764585130834410663529786148885181125662260022001155982221759097])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 23:ℚ)
def qv23 : ℚ := ((((raw_ints% [-1677564436176814569903542029088719731529143781974571385837048275093720305143973255566601871283575649412583478718873])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 24:ℚ)
def qv24 : ℚ := ((((raw_ints% [31119693349344177688331862962221453531187493639055339715373418962204339741357141788480917496247047829192160876790001201])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 25:ℚ)
def qv25 : ℚ := ((((raw_ints% [-94268104180244902543389101103390233768948887538520665894515475935018571063610673706997080447154744690886185083018304657597])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 26:ℚ)
def qv26 : ℚ := ((((raw_ints% [1777022564795606863709293816768354465240909085391624449553080354474246129003359194217242367314374889945038718758159556509777877])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 27:ℚ)
def qv27 : ℚ := ((((raw_ints% [-5348736208964102361162013555422994662539453264759243101872614579047211011075091889982752649665479040341226041479594173961724938161])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 28:ℚ)
def qv28 : ℚ := ((((raw_ints% [512212603753356987875024587855526754893460784194235432638701278048455094915044939231240276589169407665245415586937618957096923335381933])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 29:ℚ)
def qv29 : ℚ := ((((raw_ints% [-7652679656721395018604954201792224507152433672897751157889600315058130583372740611004561499652171727043148316126014413081503066013527782573])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 30:ℚ)
def qv30 : ℚ := ((((raw_ints% [148903669403128604443723125207717258682127419317032783706577596166154631996035201052155465857550512199798729254908692812516900805375923243569093])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 31:ℚ)
def qv31 : ℚ := ((((raw_ints% [-2206744615989911366308721173150367839604974088422630762122769114724452529208691116318426131245891833249821277068014384216311835029584399028409534821])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 32:ℚ)
def qv32 : ℚ := ((((raw_ints% [43620804831065836055732496591946205178874217470241863804788038381744033906235999059367735944688912794202367805551593410403928368919893004762993264847133])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 33:ℚ)
def qv33 : ℚ := ((((raw_ints% [-128155400538258123703197587883329871821570749363748058241969596580225379885792319737287947833210513080831570829672209041029274296093825936921458792106183097])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 34:ℚ)
def qv34 : ℚ := ((((raw_ints% [12867794794851164281843009383738696069523857137910441910014761330538204013016951721692809788388033802577535085771955763276877023912452863137780342341497528276661])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 35:ℚ)
def qv35 : ℚ := ((((raw_ints% [-187239048028245651304310097823772105775027471615678570590386543425215474000032966031196945388359846836101362086066374974494445989560172369694780206681509697302357077])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 36:ℚ)
def qv36 : ℚ := ((((raw_ints% [3820052074222454392158726759767727689163981317051055146347257721241636112520802938474041401194914896027287585021957163029639676501072015059964297687099555943155863071117])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 37:ℚ)
def qv37 : ℚ := ((((raw_ints% [-11005462676071687094158449855203435642802505044166338741120821361254364357612211904762514908744557218898909415598701184004846799065574083272773326234615365956848041786634473])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 38:ℚ)
def qv38 : ℚ := ((((raw_ints% [1140662685661936285565666476038550546948161867873881596286105058997734420783921396773371936014979023639018738027086142173117851612227643953121764029475002020124888905379655165093])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 39:ℚ)
def qv39 : ℚ := ((((raw_ints% [-16257085053467855321004621214320124694052623695303870686848425297568135443438026186844856401785905350371735814096327306525608827539324807910355075186088750951878855768710565777141573])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 40:ℚ)
def qv40 : ℚ := ((((raw_ints% [1712124894470267198029340666203672936434321506040060925410892366417024853092131571311187492377147790353511004995320535661542172670695058325084104556723425162535388680991908737345416849649])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 41:ℚ)
def qv41 : ℚ := ((((raw_ints% [-24131068589108019472582301915618973474295801405818319224051523659240665795629542432753825900590138245137448742814287609778517781899363565875197678090403853453754074253366327879318133006789233])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 42:ℚ)
def qv42 : ℚ := ((((raw_ints% [20660736733518701242943593119101439902901054036221738742556171430791091834013108952117734623069845380221478704462443440012552948976949264630770774223077161563512312116017298655924484647084984401])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 43:ℚ)
def qv43 : ℚ := ((((raw_ints% [-7195806819730568498773918618865420115439612503298769315889454725608831250554429079500639404289319509417971296657086035337903397076303779769813236474359023482812356267079658577082863235259070794074889])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 44:ℚ)
def qv44 : ℚ := ((((raw_ints% [156538368590408941025328794930909813770517835243587177213929641522423592027569293718208640513634197668841824922406549765082046426610946829851187080680323822300663516971565881261522591211805857892902009121])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 45:ℚ)

def values : List ℚ := [qv0,qv1,qv2,qv3,qv4,qv5,qv6,qv7,qv8,qv9,qv10,qv11,qv12,qv13,qv14,qv15,qv16,qv17,qv18,qv19,qv20,qv21,qv22,qv23,qv24,qv25,qv26,qv27,qv28,qv29,qv30,qv31,qv32,qv33,qv34,qv35,qv36,qv37,qv38,qv39,qv40,qv41,qv42,qv43,qv44]
end OrdinaryData
def mu : List ℚ := OrdinaryData.values
#eval ("real ordinary all45",ordinaryMomentFast second center 44 mu)
set_option trace.profiler true in
theorem ordinaryMoment0_ok : coeffQ mu 0=arcList (realMomentList second center 0) := by decide +kernel
set_option trace.profiler true in
theorem ordinaryMoment1_ok : coeffQ mu 1=arcList (realMomentList second center 1) := by decide +kernel
set_option trace.profiler true in
theorem ordinaryMoment2_ok : coeffQ mu 2=arcList (realMomentList second center 2) := by decide +kernel
set_option trace.profiler true in
theorem ordinaryMoment3_ok : coeffQ mu 3=arcList (realMomentList second center 3) := by decide +kernel
set_option trace.profiler true in
theorem ordinaryMoment4_ok : coeffQ mu 4=arcList (realMomentList second center 4) := by decide +kernel
set_option trace.profiler true in
theorem ordinaryMoment5_ok : coeffQ mu 5=arcList (realMomentList second center 5) := by decide +kernel
set_option trace.profiler true in
theorem ordinaryMoment6_ok : coeffQ mu 6=arcList (realMomentList second center 6) := by decide +kernel
set_option trace.profiler true in
theorem ordinaryMoment7_ok : coeffQ mu 7=arcList (realMomentList second center 7) := by decide +kernel
set_option trace.profiler true in
theorem ordinaryMoment8_ok : coeffQ mu 8=arcList (realMomentList second center 8) := by decide +kernel
set_option trace.profiler true in
theorem ordinaryMoment9_ok : coeffQ mu 9=arcList (realMomentList second center 9) := by decide +kernel
set_option trace.profiler true in
theorem ordinaryMoment10_ok : coeffQ mu 10=arcList (realMomentList second center 10) := by decide +kernel
set_option trace.profiler true in
theorem ordinaryMoment11_ok : coeffQ mu 11=arcList (realMomentList second center 11) := by decide +kernel
set_option trace.profiler true in
theorem ordinaryMoment12_ok : coeffQ mu 12=arcList (realMomentList second center 12) := by decide +kernel
set_option trace.profiler true in
theorem ordinaryMoment13_ok : coeffQ mu 13=arcList (realMomentList second center 13) := by decide +kernel
set_option trace.profiler true in
theorem ordinaryMoment14_ok : coeffQ mu 14=arcList (realMomentList second center 14) := by decide +kernel
set_option trace.profiler true in
theorem ordinaryMoment15_ok : coeffQ mu 15=arcList (realMomentList second center 15) := by decide +kernel
set_option trace.profiler true in
theorem ordinaryMoment16_ok : coeffQ mu 16=arcList (realMomentList second center 16) := by decide +kernel
set_option trace.profiler true in
theorem ordinaryMoment17_ok : coeffQ mu 17=arcList (realMomentList second center 17) := by decide +kernel
set_option trace.profiler true in
theorem ordinaryMoment18_ok : coeffQ mu 18=arcList (realMomentList second center 18) := by decide +kernel
set_option trace.profiler true in
theorem ordinaryMoment19_ok : coeffQ mu 19=arcList (realMomentList second center 19) := by decide +kernel
set_option trace.profiler true in
theorem ordinaryMoment20_ok : coeffQ mu 20=arcList (realMomentList second center 20) := by decide +kernel
set_option trace.profiler true in
theorem ordinaryMoment21_ok : coeffQ mu 21=arcList (realMomentList second center 21) := by decide +kernel
set_option trace.profiler true in
theorem ordinaryMoment22_ok : coeffQ mu 22=arcList (realMomentList second center 22) := by decide +kernel
set_option trace.profiler true in
theorem ordinaryMoment23_ok : coeffQ mu 23=arcList (realMomentList second center 23) := by decide +kernel
set_option trace.profiler true in
theorem ordinaryMoment24_ok : coeffQ mu 24=arcList (realMomentList second center 24) := by decide +kernel
set_option trace.profiler true in
theorem ordinaryMoment25_ok : coeffQ mu 25=arcList (realMomentList second center 25) := by decide +kernel
set_option trace.profiler true in
theorem ordinaryMoment26_ok : coeffQ mu 26=arcList (realMomentList second center 26) := by decide +kernel
set_option trace.profiler true in
theorem ordinaryMoment27_ok : coeffQ mu 27=arcList (realMomentList second center 27) := by decide +kernel
set_option trace.profiler true in
theorem ordinaryMoment28_ok : coeffQ mu 28=arcList (realMomentList second center 28) := by decide +kernel
set_option trace.profiler true in
theorem ordinaryMoment29_ok : coeffQ mu 29=arcList (realMomentList second center 29) := by decide +kernel
set_option trace.profiler true in
theorem ordinaryMoment30_ok : coeffQ mu 30=arcList (realMomentList second center 30) := by decide +kernel
set_option trace.profiler true in
theorem ordinaryMoment31_ok : coeffQ mu 31=arcList (realMomentList second center 31) := by decide +kernel
set_option trace.profiler true in
theorem ordinaryMoment32_ok : coeffQ mu 32=arcList (realMomentList second center 32) := by decide +kernel
set_option trace.profiler true in
theorem ordinaryMoment33_ok : coeffQ mu 33=arcList (realMomentList second center 33) := by decide +kernel
set_option trace.profiler true in
theorem ordinaryMoment34_ok : coeffQ mu 34=arcList (realMomentList second center 34) := by decide +kernel
set_option trace.profiler true in
theorem ordinaryMoment35_ok : coeffQ mu 35=arcList (realMomentList second center 35) := by decide +kernel
set_option trace.profiler true in
theorem ordinaryMoment36_ok : coeffQ mu 36=arcList (realMomentList second center 36) := by decide +kernel
set_option trace.profiler true in
theorem ordinaryMoment37_ok : coeffQ mu 37=arcList (realMomentList second center 37) := by decide +kernel
set_option trace.profiler true in
theorem ordinaryMoment38_ok : coeffQ mu 38=arcList (realMomentList second center 38) := by decide +kernel
set_option trace.profiler true in
theorem ordinaryMoment39_ok : coeffQ mu 39=arcList (realMomentList second center 39) := by decide +kernel
set_option trace.profiler true in
theorem ordinaryMoment40_ok : coeffQ mu 40=arcList (realMomentList second center 40) := by decide +kernel
set_option trace.profiler true in
theorem ordinaryMoment41_ok : coeffQ mu 41=arcList (realMomentList second center 41) := by decide +kernel
set_option trace.profiler true in
theorem ordinaryMoment42_ok : coeffQ mu 42=arcList (realMomentList second center 42) := by decide +kernel
set_option trace.profiler true in
theorem ordinaryMoment43_ok : coeffQ mu 43=arcList (realMomentList second center 43) := by decide +kernel
set_option trace.profiler true in
theorem ordinaryMoment44_ok : coeffQ mu 44=arcList (realMomentList second center 44) := by decide +kernel
theorem ordinary_table_fast : ordinaryMomentFast second center 44 mu=true := by
  simp only [ordinaryMomentFast,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true]
  constructor
  · decide +kernel
  · intro k hk
    have h : k≤44 := by have := List.mem_range.mp hk;omega
    interval_cases k <;> first
    | exact ordinaryMoment0_ok
    | exact ordinaryMoment1_ok
    | exact ordinaryMoment2_ok
    | exact ordinaryMoment3_ok
    | exact ordinaryMoment4_ok
    | exact ordinaryMoment5_ok
    | exact ordinaryMoment6_ok
    | exact ordinaryMoment7_ok
    | exact ordinaryMoment8_ok
    | exact ordinaryMoment9_ok
    | exact ordinaryMoment10_ok
    | exact ordinaryMoment11_ok
    | exact ordinaryMoment12_ok
    | exact ordinaryMoment13_ok
    | exact ordinaryMoment14_ok
    | exact ordinaryMoment15_ok
    | exact ordinaryMoment16_ok
    | exact ordinaryMoment17_ok
    | exact ordinaryMoment18_ok
    | exact ordinaryMoment19_ok
    | exact ordinaryMoment20_ok
    | exact ordinaryMoment21_ok
    | exact ordinaryMoment22_ok
    | exact ordinaryMoment23_ok
    | exact ordinaryMoment24_ok
    | exact ordinaryMoment25_ok
    | exact ordinaryMoment26_ok
    | exact ordinaryMoment27_ok
    | exact ordinaryMoment28_ok
    | exact ordinaryMoment29_ok
    | exact ordinaryMoment30_ok
    | exact ordinaryMoment31_ok
    | exact ordinaryMoment32_ok
    | exact ordinaryMoment33_ok
    | exact ordinaryMoment34_ok
    | exact ordinaryMoment35_ok
    | exact ordinaryMoment36_ok
    | exact ordinaryMoment37_ok
    | exact ordinaryMoment38_ok
    | exact ordinaryMoment39_ok
    | exact ordinaryMoment40_ok
    | exact ordinaryMoment41_ok
    | exact ordinaryMoment42_ok
    | exact ordinaryMoment43_ok
    | exact ordinaryMoment44_ok
theorem ordinary_table : ordinaryMomentCheck second center 44 mu=true := by
  rw [← ordinaryMomentFast_eq]
  exact ordinary_table_fast
#print axioms ordinary_table
theorem actual_source_moments : mu.length=45 ∧ ∀k≤44,
    moment second.measure (center:ℂ) k=(coeffQ mu k:ℂ) :=
  ordinaryMomentCheck_sound second center 44 mu second_positive ordinary_table
#print axioms actual_source_moments
end CatalanCore.Li2.DecayCert.LatticeFirst
