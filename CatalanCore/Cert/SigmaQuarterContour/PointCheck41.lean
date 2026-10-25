module
public import CatalanCore.Cert.SigmaQuarterContour.Data
@[expose] public section
namespace CatalanCore.Cert.SigmaQuarterContour
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
theorem point_1312_ok : pointOK 1312 = true := by decide +kernel
theorem point_1313_ok : pointOK 1313 = true := by decide +kernel
theorem point_1314_ok : pointOK 1314 = true := by decide +kernel
theorem point_1315_ok : pointOK 1315 = true := by decide +kernel
theorem point_1316_ok : pointOK 1316 = true := by decide +kernel
theorem point_1317_ok : pointOK 1317 = true := by decide +kernel
theorem point_1318_ok : pointOK 1318 = true := by decide +kernel
theorem point_1319_ok : pointOK 1319 = true := by decide +kernel
theorem point_1320_ok : pointOK 1320 = true := by decide +kernel
theorem point_1321_ok : pointOK 1321 = true := by decide +kernel
theorem point_1322_ok : pointOK 1322 = true := by decide +kernel
theorem point_1323_ok : pointOK 1323 = true := by decide +kernel
theorem point_1324_ok : pointOK 1324 = true := by decide +kernel
theorem point_1325_ok : pointOK 1325 = true := by decide +kernel
theorem point_1326_ok : pointOK 1326 = true := by decide +kernel
theorem point_1327_ok : pointOK 1327 = true := by decide +kernel
theorem point_1328_ok : pointOK 1328 = true := by decide +kernel
theorem point_1329_ok : pointOK 1329 = true := by decide +kernel
theorem point_1330_ok : pointOK 1330 = true := by decide +kernel
theorem point_1331_ok : pointOK 1331 = true := by decide +kernel
theorem point_1332_ok : pointOK 1332 = true := by decide +kernel
theorem point_1333_ok : pointOK 1333 = true := by decide +kernel
theorem point_1334_ok : pointOK 1334 = true := by decide +kernel
theorem point_1335_ok : pointOK 1335 = true := by decide +kernel
theorem point_1336_ok : pointOK 1336 = true := by decide +kernel
theorem point_1337_ok : pointOK 1337 = true := by decide +kernel
theorem point_1338_ok : pointOK 1338 = true := by decide +kernel
theorem point_1339_ok : pointOK 1339 = true := by decide +kernel
theorem point_1340_ok : pointOK 1340 = true := by decide +kernel
theorem point_1341_ok : pointOK 1341 = true := by decide +kernel
theorem point_1342_ok : pointOK 1342 = true := by decide +kernel
theorem point_1343_ok : pointOK 1343 = true := by decide +kernel
theorem checkChunk_41 : (checkChunk 41).all pointOK = true := by
  have h : checkChunk 41 = [1312,1313,1314,1315,1316,1317,1318,1319,1320,1321,1322,1323,1324,1325,1326,1327,1328,1329,1330,1331,1332,1333,1334,1335,1336,1337,1338,1339,1340,1341,1342,1343] := by decide +kernel
  rw [h]
  simp only [List.all_cons, List.all_nil, point_1312_ok, point_1313_ok, point_1314_ok, point_1315_ok, point_1316_ok, point_1317_ok, point_1318_ok, point_1319_ok, point_1320_ok, point_1321_ok, point_1322_ok, point_1323_ok, point_1324_ok, point_1325_ok, point_1326_ok, point_1327_ok, point_1328_ok, point_1329_ok, point_1330_ok, point_1331_ok, point_1332_ok, point_1333_ok, point_1334_ok, point_1335_ok, point_1336_ok, point_1337_ok, point_1338_ok, point_1339_ok, point_1340_ok, point_1341_ok, point_1342_ok, point_1343_ok, Bool.and_self]
end CatalanCore.Cert.SigmaQuarterContour
