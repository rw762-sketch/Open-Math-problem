import Covering.TowerCheck
import Covering.ScanT.C0
import Covering.ScanT.C1
import Covering.ScanT.C2
import Covering.ScanT.C3
import Covering.ScanT.C4
import Covering.ScanT.C5
import Covering.ScanT.C6
import Covering.ScanT.C7
import Covering.ScanT.C8
import Covering.ScanT.C9
import Covering.ScanT.C10
import Covering.ScanT.C11
import Covering.ScanT.C12
import Covering.ScanT.C13
import Covering.ScanT.C14
import Covering.ScanT.C15
import Covering.ScanT.C16
import Covering.ScanT.C17
import Covering.ScanT.C18
import Covering.ScanT.C19
import Covering.ScanT.C20
import Covering.ScanT.C21
import Covering.ScanT.C22
import Covering.ScanT.C23
import Covering.ScanT.C24
namespace Covering
open ScanT

theorem All1M_scan : scanChunk2 0 1000000 = true := by
  have h : scanChunk2 0 40000 = true := c0
  have h : scanChunk2 0 80000 = true := scanChunk2_append 0 40000 40000 h c1
  have h : scanChunk2 0 120000 = true := scanChunk2_append 0 80000 40000 h c2
  have h : scanChunk2 0 160000 = true := scanChunk2_append 0 120000 40000 h c3
  have h : scanChunk2 0 200000 = true := scanChunk2_append 0 160000 40000 h c4
  have h : scanChunk2 0 240000 = true := scanChunk2_append 0 200000 40000 h c5
  have h : scanChunk2 0 280000 = true := scanChunk2_append 0 240000 40000 h c6
  have h : scanChunk2 0 320000 = true := scanChunk2_append 0 280000 40000 h c7
  have h : scanChunk2 0 360000 = true := scanChunk2_append 0 320000 40000 h c8
  have h : scanChunk2 0 400000 = true := scanChunk2_append 0 360000 40000 h c9
  have h : scanChunk2 0 440000 = true := scanChunk2_append 0 400000 40000 h c10
  have h : scanChunk2 0 480000 = true := scanChunk2_append 0 440000 40000 h c11
  have h : scanChunk2 0 520000 = true := scanChunk2_append 0 480000 40000 h c12
  have h : scanChunk2 0 560000 = true := scanChunk2_append 0 520000 40000 h c13
  have h : scanChunk2 0 600000 = true := scanChunk2_append 0 560000 40000 h c14
  have h : scanChunk2 0 640000 = true := scanChunk2_append 0 600000 40000 h c15
  have h : scanChunk2 0 680000 = true := scanChunk2_append 0 640000 40000 h c16
  have h : scanChunk2 0 720000 = true := scanChunk2_append 0 680000 40000 h c17
  have h : scanChunk2 0 760000 = true := scanChunk2_append 0 720000 40000 h c18
  have h : scanChunk2 0 800000 = true := scanChunk2_append 0 760000 40000 h c19
  have h : scanChunk2 0 840000 = true := scanChunk2_append 0 800000 40000 h c20
  have h : scanChunk2 0 880000 = true := scanChunk2_append 0 840000 40000 h c21
  have h : scanChunk2 0 920000 = true := scanChunk2_append 0 880000 40000 h c22
  have h : scanChunk2 0 960000 = true := scanChunk2_append 0 920000 40000 h c23
  have h : scanChunk2 0 1000000 = true := scanChunk2_append 0 960000 40000 h c24
  exact h

/-- Every covering of ℤ by finitely many classes with distinct odd moduli > 1 has lcm > 1000000.
Mathematics kernel-checked; the scan uses native_decide. -/
theorem odd_covering_lcm_gt_1000000 (S : Finset Cls) (hgt : ∀ c ∈ S, 1 < c.d)
    (hodd : ∀ c ∈ S, Odd c.d) (hinj : ∀ c ∈ S, ∀ c' ∈ S, c.d = c'.d → c = c')
    (hcov : CoversZ S) : 1000000 < S.lcm (·.d) :=
  odd_covering_lcm_gt_of_scan2 1000000
    (fun L hL hodd => scanChunk2_spec 0 1000000 All1M_scan L (by omega) (by omega) hodd)
    S hgt hodd hinj hcov

end Covering
