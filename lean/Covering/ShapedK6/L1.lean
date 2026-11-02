import Covering.ShapedBound
namespace Covering.ShapedK6
def l1 : List ℕ := [30375, 31185, 32805, 33075, 36015, 38115, 39375, 40425, 42525, 45045, 46305, 46875, 50625, 51975, 54675, 55125, 56595, 59049, 59535, 63525, 65625, 70875, 72765, 75075, 76545, 77175, 84375, 86625, 88935, 91125, 91875, 93555, 98415]
theorem l1_ok : l1.all check2 = true := by decide +kernel
end Covering.ShapedK6
