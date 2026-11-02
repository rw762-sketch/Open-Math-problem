import Covering.ShapedBound
namespace Covering.ShapedK6
def l17 : List ℕ := [6251175, 6288975, 6302625, 6328125, 6381375, 6441435, 6496875, 6621615, 6670125, 6806835, 6831825, 6834375, 6847995]
theorem l17_ok : l17.all check2 = true := by decide +kernel
end Covering.ShapedK6
