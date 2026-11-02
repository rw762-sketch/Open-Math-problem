import Covering.ShapedBound
namespace Covering.ShapedK6
def l5 : List ℕ := [571725, 585585, 590625, 606375, 622545, 637875, 643125, 654885, 675675, 688905, 694575, 698775, 703125, 721875, 735735, 756315, 759375, 765765, 779625]
theorem l5_ok : l5.all check2 = true := by decide +kernel
end Covering.ShapedK6
