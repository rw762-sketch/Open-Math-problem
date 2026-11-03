import Covering.Check
namespace Covering
-- controls: 12 hosts the classic covering, so no certificate may fire
example : check 12 = false := by decide +kernel
example : densCheck 945 = false := by decide +kernel   -- 945 is abundant
example : phiCheck 945 = true := by decide +kernel
-- the three stragglers of the prime-only capacity certificate
example : phiCheck 10395 = true := by decide +kernel
example : phiCheck 12285 = true := by decide +kernel
example : phiCheck 17325 = true := by decide +kernel
-- the first L the φ-certificate cannot exclude
example : phiCheck 675675 = false := by decide +kernel
end Covering
