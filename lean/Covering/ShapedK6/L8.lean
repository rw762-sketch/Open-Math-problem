import Covering.ShapedBound
namespace Covering.ShapedK6
def l8 : List ℕ := [1378125, 1403325, 1414875, 1476225, 1486485, 1488375, 1528065, 1537305, 1576575, 1588125, 1594323, 1607445, 1620675, 1640625, 1715175, 1756755, 1764735]
theorem l8_ok : l8.all check2 = true := by decide +kernel
end Covering.ShapedK6
