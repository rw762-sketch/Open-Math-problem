import Covering.ShapedBound
namespace Covering.ShapedK6
def l3 : List ℕ := [218295, 225225, 229635, 231525, 234375, 252105, 253125, 255255, 259875, 266805, 273375, 275625, 280665, 282975, 295245, 297675, 315315, 317625, 324135, 328125, 343035, 354375, 363825]
theorem l3_ok : l3.all check2 = true := by decide +kernel
end Covering.ShapedK6
