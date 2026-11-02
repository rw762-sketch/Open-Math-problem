import Covering.ShapedBound
namespace Covering.ShapedK6
def l7 : List ℕ := [1091475, 1126125, 1148175, 1156155, 1157625, 1171875, 1188495, 1216215, 1250235, 1257795, 1260525, 1265625, 1276275, 1299375, 1334025, 1366365, 1366875]
theorem l7_ok : l7.all check2 = true := by decide +kernel
end Covering.ShapedK6
