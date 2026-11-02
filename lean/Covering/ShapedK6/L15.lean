import Covering.ShapedBound
namespace Covering.ShapedK6
def l15 : List ℕ := [4822335, 4849845, 4862025, 4879875, 4891425, 4921875, 5053125, 5145525, 5150145, 5270265, 5294205, 5315625, 5360355]
theorem l15_ok : l15.all check2 = true := by decide +kernel
end Covering.ShapedK6
