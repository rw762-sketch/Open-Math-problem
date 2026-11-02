import Covering.ShapedBound
namespace Covering.ShapedK6
def l13 : List ℕ := [3648645, 3678675, 3750705, 3773385, 3781575, 3796875, 3828825, 3898125, 4002075, 4099095, 4100625, 4129125]
theorem l13_ok : l13.all check2 = true := by decide +kernel
end Covering.ShapedK6
