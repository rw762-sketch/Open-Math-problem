import Covering.TowerCheck
namespace Covering
example : check2 12 = false := by decide +kernel
example : check2 80 = false := by decide +kernel
example : towerCheck 675675 = true := by decide +kernel
example : towerCheck 4729725 = true := by decide +kernel
example : towerCheck 6891885 = false := by decide +kernel
end Covering
