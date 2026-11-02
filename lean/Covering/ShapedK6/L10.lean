import Covering.ShapedBound
namespace Covering.ShapedK6
def l10 : List ℕ := [2147145, 2165625, 2207205, 2223375, 2268945, 2278125, 2296875, 2297295, 2338875, 2401245, 2460375, 2477475, 2480625, 2525985, 2537535]
theorem l10_ok : l10.all check2 = true := by decide +kernel
end Covering.ShapedK6
