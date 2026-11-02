import Covering.Check
namespace Covering.ScanK

theorem c100 : scanChunk 50000 500 = true := by decide +kernel
theorem c101 : scanChunk 50500 500 = true := by decide +kernel
theorem c102 : scanChunk 51000 500 = true := by decide +kernel
theorem c103 : scanChunk 51500 500 = true := by decide +kernel
theorem c104 : scanChunk 52000 500 = true := by decide +kernel
theorem c105 : scanChunk 52500 500 = true := by decide +kernel
theorem c106 : scanChunk 53000 500 = true := by decide +kernel
theorem c107 : scanChunk 53500 500 = true := by decide +kernel
theorem c108 : scanChunk 54000 500 = true := by decide +kernel
theorem c109 : scanChunk 54500 500 = true := by decide +kernel
end Covering.ScanK
