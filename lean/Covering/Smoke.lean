import Covering.Basic
namespace Covering

/-- The classic covering {0 mod 2, 0 mod 3, 1 mod 4, 5 mod 6, 7 mod 12}. -/
def classic : List Cls := [⟨0,2⟩, ⟨0,3⟩, ⟨1,4⟩, ⟨5,6⟩, ⟨7,12⟩]

theorem classic_covers : CoversInt classic :=
  coversInt_of_check (L := 12) (by decide) (by decide) (by decide)

/-- Dropping one class must fail the finite check. -/
example : checkBelow [⟨0,2⟩, ⟨0,3⟩, ⟨1,4⟩, ⟨5,6⟩] 12 = false := by decide

/-- Timing probe: 1 (mod 1) covers everything; L = 50000 tests kernel evaluation cost. -/
theorem probe : checkBelow [⟨0,1⟩] 50000 = true := by decide +kernel

end Covering
