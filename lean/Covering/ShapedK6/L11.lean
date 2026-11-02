import Covering.ShapedBound
namespace Covering.ShapedK6
def l11 : List ℕ := [2546775, 2627625, 2657205, 2679075, 2701125, 2773155, 2807805, 2837835, 2858625, 2917215, 2927925, 2934855, 2953125, 3031875]
theorem l11_ok : l11.all check2 = true := by decide +kernel
end Covering.ShapedK6
