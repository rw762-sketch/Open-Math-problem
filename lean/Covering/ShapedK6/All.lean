import Covering.ShapedK6.L0
import Covering.ShapedK6.L1
import Covering.ShapedK6.L2
import Covering.ShapedK6.L3
import Covering.ShapedK6.L4
import Covering.ShapedK6.L5
import Covering.ShapedK6.L6
import Covering.ShapedK6.L7
import Covering.ShapedK6.L8
import Covering.ShapedK6.L9
import Covering.ShapedK6.L10
import Covering.ShapedK6.L11
import Covering.ShapedK6.L12
import Covering.ShapedK6.L13
import Covering.ShapedK6.L14
import Covering.ShapedK6.L15
import Covering.ShapedK6.L16
import Covering.ShapedK6.L17
import Covering.ShapedK6.L18

/-
Kernel-only (no `native_decide`) lcm bound: prime replacement reduces to shaped moduli; every
shaped odd `L ≤ 6891884` lies in the explicit list `big` (`gen_in`, by the generator), and every
member of `big` passes the density-or-tower check (`l*_ok`, one file per chunk).
-/

namespace Covering.ShapedK6
open Covering

def big : List ℕ := l0 ++ l1 ++ l2 ++ l3 ++ l4 ++ l5 ++ l6 ++ l7 ++ l8 ++ l9 ++ l10 ++ l11 ++ l12 ++ l13 ++ l14 ++ l15 ++ l16 ++ l17 ++ l18

theorem big_all : big.all check2 = true := by
  simp only [big, List.all_append, l0_ok, l1_ok, l2_ok, l3_ok, l4_ok, l5_ok, l6_ok, l7_ok, l8_ok, l9_ok, l10_ok, l11_ok, l12_ok, l13_ok, l14_ok, l15_ok, l16_ok, l17_ok, l18_ok, Bool.and_self]

theorem gen_in : chkGen (fun L => decide (L ∈ big)) 6891884 OP 1 = true := by decide +kernel

end Covering.ShapedK6

namespace Covering

/-- **Every odd distinct covering system has lcm `> 6891884`**, checked by the kernel alone
(prime replacement + density/tower certificate on the 363 shaped moduli). -/
theorem odd_covering_lcm_gt_6891884_kernel (S : Finset Cls) (hgt : ∀ c ∈ S, 1 < c.d)
    (hodd : ∀ c ∈ S, Odd c.d) (hinj : ∀ c ∈ S, ∀ c' ∈ S, c.d = c'.d → c = c')
    (hcov : CoversZ S) : 6891884 < S.lcm (·.d) := by
  apply odd_covering_lcm_gt_of_chkGen' (fun L => decide (L ∈ ShapedK6.big)) 6891884 (by norm_num)
    (by decide) ShapedK6.gen_in _ S hgt hodd hinj hcov
  intro L hL S' hS'
  have hmem : L ∈ ShapedK6.big := by simpa using hL
  exact no_covering_of_check2 (List.all_eq_true.mp ShapedK6.big_all L hmem) S' hS'

end Covering
