import Covering.ShapedBound
namespace Covering.ShapedK6
def l14 : List ℕ := [4134375, 4209975, 4244625, 4339335, 4357815, 4428675, 4459455, 4465125, 4501875, 4584195, 4611915, 4729725, 4764375, 4782969]
theorem l14_ok : l14.all check2 = true := by decide +kernel
end Covering.ShapedK6
