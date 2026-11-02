import Covering.ShapedBound
namespace Covering.ShapedK6
def l16 : List ℕ := [5450445, 5457375, 5602905, 5630625, 5740875, 5780775, 5788125, 5859375, 5893965, 5942475, 6081075, 6200145]
theorem l16_ok : l16.all check2 = true := by decide +kernel
end Covering.ShapedK6
