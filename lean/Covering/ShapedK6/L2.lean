import Covering.ShapedBound
namespace Covering.ShapedK6
def l2 : List ℕ := [99225, 105105, 108045, 114345, 118125, 121275, 127575, 128625, 135135, 138915, 139755, 140625, 144375, 151875, 155925, 164025, 165165, 165375, 169785, 177147, 178605, 180075, 190575, 195195, 196875, 202125, 212625]
theorem l2_ok : l2.all check2 = true := by decide +kernel
end Covering.ShapedK6
