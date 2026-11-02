import Covering.ShapedBound
namespace Covering.ShapedK6
def l9 : List ℕ := [1771875, 1786785, 1816815, 1819125, 1867635, 1876875, 1913625, 1929375, 1964655, 1980825, 2027025, 2066715, 2083725, 2096325, 2109375]
theorem l9_ok : l9.all check2 = true := by decide +kernel
end Covering.ShapedK6
