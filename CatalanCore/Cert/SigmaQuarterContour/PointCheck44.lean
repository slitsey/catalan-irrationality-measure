module
public import CatalanCore.Cert.SigmaQuarterContour.Data
@[expose] public section
namespace CatalanCore.Cert.SigmaQuarterContour
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
theorem pointGroup44_0 : ([1408,1409,1410,1411,1412,1413,1414,1415] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup44_1 : ([1416,1417,1418,1419,1420,1421,1422,1423] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup44_2 : ([1424,1425,1426,1427,1428,1429,1430,1431] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup44_3 : ([1432,1433,1434,1435,1436,1437,1438,1439] : List ℕ).all pointOK = true := by decide +kernel
theorem checkChunk_44 : (checkChunk 44).all pointOK = true := by
  have h : checkChunk 44 = [1408,1409,1410,1411,1412,1413,1414,1415] ++ [1416,1417,1418,1419,1420,1421,1422,1423] ++ [1424,1425,1426,1427,1428,1429,1430,1431] ++ [1432,1433,1434,1435,1436,1437,1438,1439] := by decide +kernel
  rw [h]
  simp only [List.all_append, pointGroup44_0, pointGroup44_1, pointGroup44_2, pointGroup44_3, Bool.and_self]
end CatalanCore.Cert.SigmaQuarterContour
