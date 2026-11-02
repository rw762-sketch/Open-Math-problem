import Covering.Check
namespace Covering.ScanK

theorem c0 : scanChunk 0 500 = true := by decide +kernel
theorem c1 : scanChunk 500 500 = true := by decide +kernel
theorem c2 : scanChunk 1000 500 = true := by decide +kernel
theorem c3 : scanChunk 1500 500 = true := by decide +kernel
theorem c4 : scanChunk 2000 500 = true := by decide +kernel
theorem c5 : scanChunk 2500 500 = true := by decide +kernel
theorem c6 : scanChunk 3000 500 = true := by decide +kernel
theorem c7 : scanChunk 3500 500 = true := by decide +kernel
theorem c8 : scanChunk 4000 500 = true := by decide +kernel
theorem c9 : scanChunk 4500 500 = true := by decide +kernel
end Covering.ScanK
