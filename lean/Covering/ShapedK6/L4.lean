import Covering.ShapedBound
namespace Covering.ShapedK6
def l4 : List ℕ := [375375, 382725, 385875, 396165, 405405, 416745, 419265, 421875, 433125, 444675, 455625, 459375, 467775, 492075, 495495, 496125, 509355, 525525, 531441, 535815, 540225]
theorem l4_ok : l4.all check2 = true := by decide +kernel
end Covering.ShapedK6
