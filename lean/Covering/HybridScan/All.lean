import Covering.HybridScan.C0
import Covering.HybridScan.C1
import Covering.HybridScan.C2
import Covering.HybridScan.C3
import Covering.HybridScan.C4
import Covering.HybridScan.C5
import Covering.HybridScan.C6
import Covering.HybridScan.C7
import Covering.HybridScan.C8
import Covering.HybridScan.C9
import Covering.HybridScan.C10
import Covering.HybridScan.C11
import Covering.HybridScan.C12
import Covering.HybridScan.C13
import Covering.HybridScan.C14
import Covering.HybridScan.C15
import Covering.HybridScan.C16
import Covering.ShapedBound

/-
Kernel-only lcm bound from the distorted tower certificate: prime replacement reduces to shaped
moduli; every shaped odd `L ≤ 1527701174` lies in the bucket `lk (L % 17)` (`gen_in`); each bucket
member carries an explicit certificate (exposure order, caps δ = k/200) checked by `hyb`.
-/

namespace Covering.HybridScan
open Covering Covering.Hybrid

def lk : ℕ → List ℕ
  | 0 => l0
  | 1 => l1
  | 2 => l2
  | 3 => l3
  | 4 => l4
  | 5 => l5
  | 6 => l6
  | 7 => l7
  | 8 => l8
  | 9 => l9
  | 10 => l10
  | 11 => l11
  | 12 => l12
  | 13 => l13
  | 14 => l14
  | 15 => l15
  | 16 => l16
  | _ => []

def chk (L : ℕ) : Bool := decide (L ∈ lk (L % 17))

theorem chk_sound (L : ℕ) (hL : chk L = true) (S : Finset Cls) : ¬ IsCovering L S := by
  have h : L ∈ lk (L % 17) := by simpa [chk] using hL
  have hk : L % 17 < 17 := Nat.mod_lt _ (by norm_num)
  generalize L % 17 = k at h hk
  interval_cases k
  · exact l0_sound L (by simpa [lk] using h) S
  · exact l1_sound L (by simpa [lk] using h) S
  · exact l2_sound L (by simpa [lk] using h) S
  · exact l3_sound L (by simpa [lk] using h) S
  · exact l4_sound L (by simpa [lk] using h) S
  · exact l5_sound L (by simpa [lk] using h) S
  · exact l6_sound L (by simpa [lk] using h) S
  · exact l7_sound L (by simpa [lk] using h) S
  · exact l8_sound L (by simpa [lk] using h) S
  · exact l9_sound L (by simpa [lk] using h) S
  · exact l10_sound L (by simpa [lk] using h) S
  · exact l11_sound L (by simpa [lk] using h) S
  · exact l12_sound L (by simpa [lk] using h) S
  · exact l13_sound L (by simpa [lk] using h) S
  · exact l14_sound L (by simpa [lk] using h) S
  · exact l15_sound L (by simpa [lk] using h) S
  · exact l16_sound L (by simpa [lk] using h) S

theorem gen_in : chkGen chk 1527701174 OP 1 = true := by decide +kernel

end Covering.HybridScan

namespace Covering

/-- **Every odd distinct covering system has lcm `> 1527701174`**, i.e. `≥ 1 527 701 175`.
Checked by the kernel alone: prime replacement + the distorted tower certificate on the 1638
shaped moduli. -/
theorem odd_covering_lcm_gt_1527701174 (S : Finset Cls) (hgt : ∀ c ∈ S, 1 < c.d)
    (hodd : ∀ c ∈ S, Odd c.d) (hinj : ∀ c ∈ S, ∀ c' ∈ S, c.d = c'.d → c = c')
    (hcov : CoversZ S) : 1527701174 < S.lcm (·.d) :=
  odd_covering_lcm_gt_of_chkGen' HybridScan.chk 1527701174 (by norm_num) (by decide) HybridScan.gen_in
    (fun L hL S' hS' => HybridScan.chk_sound L hL S' hS') S hgt hodd hinj hcov

end Covering
