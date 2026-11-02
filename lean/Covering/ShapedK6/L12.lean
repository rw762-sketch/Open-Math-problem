import Covering.ShapedBound
namespace Covering.ShapedK6
def l12 : List ℕ := [3087315, 3112725, 3189375, 3215625, 3274425, 3318315, 3378375, 3444525, 3468465, 3472875, 3493875, 3515625, 3565485, 3609375]
theorem l12_ok : l12.all check2 = true := by decide +kernel
end Covering.ShapedK6
