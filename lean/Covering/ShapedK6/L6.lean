import Covering.ShapedBound
namespace Covering.ShapedK6
def l6 : List ℕ := [800415, 820125, 825825, 826875, 841995, 848925, 885735, 893025, 900375, 945945, 952875, 972405, 975975, 978285, 984375, 1010625, 1029105, 1063125]
theorem l6_ok : l6.all check2 = true := by decide +kernel
end Covering.ShapedK6
