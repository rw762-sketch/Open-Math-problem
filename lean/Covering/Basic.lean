/-
Covering systems: a kernel-checkable verifier and the bridge from
a finite check over [0, L) to a covering of all of ℤ.

Core Lean only (no mathlib), so that the trusted base is the Lean kernel.
-/

namespace Covering

/-- A congruence class `r (mod d)`. -/
structure Cls where
  r : Nat
  d : Nat
deriving Repr, DecidableEq

/-- `x` lies in the class `c`, as a statement over ℤ. -/
def Cls.mem (c : Cls) (x : Int) : Prop := (c.d : Int) ∣ x - c.r

/-- A list of classes covers ℤ. -/
def CoversInt (cs : List Cls) : Prop := ∀ x : Int, ∃ c ∈ cs, c.mem x

/-- Decidable membership test for a natural number. -/
def hitNat (cs : List Cls) (n : Nat) : Bool :=
  cs.any (fun c => n % c.d == c.r % c.d)

/-- `checkBelow cs k = true` iff every `n < k` is hit. Structural recursion on `k`
so that the kernel can evaluate it by `decide`. -/
def checkBelow (cs : List Cls) : Nat → Bool
  | 0 => true
  | k + 1 => hitNat cs k && checkBelow cs k

/-- Every modulus divides `L` and is positive. -/
def modsDivide (cs : List Cls) (L : Nat) : Bool :=
  cs.all (fun c => 0 < c.d && L % c.d == 0)

/-- Distinct odd moduli `> 1`, except that modulus `K` may appear up to `T` times. -/
def oddDistinctExcept (cs : List Cls) (K T : Nat) : Bool :=
  cs.all (fun c => 1 < c.d && c.d % 2 == 1) &&
  (cs.map (·.d)).all (fun d =>
    (cs.filter (fun c => c.d == d)).length ≤ (if d == K then T else 1))

theorem hitNat_spec {cs : List Cls} {n : Nat} (h : hitNat cs n = true) :
    ∃ c ∈ cs, n % c.d = c.r % c.d := by
  unfold hitNat at h
  rcases List.any_eq_true.mp h with ⟨c, hc, hn⟩
  exact ⟨c, hc, by simpa using hn⟩

theorem checkBelow_spec {cs : List Cls} {L : Nat} (h : checkBelow cs L = true) :
    ∀ n, n < L → hitNat cs n = true := by
  induction L with
  | zero => intro n hn; exact absurd hn (Nat.not_lt_zero n)
  | succ k ih =>
    intro n hn
    unfold checkBelow at h
    rcases Bool.and_eq_true_iff.mp h with ⟨h1, h2⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hn with hlt | heq
    · exact ih h2 n hlt
    · subst heq; exact h1

theorem modsDivide_spec {cs : List Cls} {L : Nat} (h : modsDivide cs L = true) :
    ∀ c ∈ cs, 0 < c.d ∧ c.d ∣ L := by
  intro c hc
  unfold modsDivide at h
  have := List.all_eq_true.mp h c hc
  rcases Bool.and_eq_true_iff.mp this with ⟨h1, h2⟩
  refine ⟨by simpa using h1, ?_⟩
  exact Nat.dvd_of_mod_eq_zero (by simpa using h2)

/-- Key arithmetic step: if `n ≡ r (mod d)` as naturals then `d ∣ (n : ℤ) - r`. -/
theorem int_dvd_of_nat_mod_eq {n r d : Nat} (h : n % d = r % d) :
    (d : Int) ∣ (n : Int) - (r : Int) := by
  have hn := Nat.div_add_mod n d
  have hr := Nat.div_add_mod r d
  -- n - r = d * (n/d - r/d) in ℤ
  have : (n : Int) - r = (d : Int) * ((n / d : Nat) - (r / d : Nat)) := by
    have e1 : (n : Int) = (d : Int) * (n / d : Nat) + (n % d : Nat) := by
      exact_mod_cast hn.symm
    have e2 : (r : Int) = (d : Int) * (r / d : Nat) + (r % d : Nat) := by
      exact_mod_cast hr.symm
    rw [e1, e2, h, Int.mul_sub]
    omega
  exact ⟨_, this⟩

/-- The bridge: a kernel-checked finite verification over `[0, L)` plus divisibility
of every modulus by `L` yields a covering of all of ℤ. -/
theorem coversInt_of_check {cs : List Cls} {L : Nat} (hL : 0 < L)
    (hdiv : modsDivide cs L = true) (hchk : checkBelow cs L = true) :
    CoversInt cs := by
  intro x
  have hLpos : (0 : Int) < L := by exact_mod_cast hL
  -- reduce x modulo L
  let m : Int := x % (L : Int)
  have hm0 : 0 ≤ m := Int.emod_nonneg x (by omega)
  have hmL : m < L := Int.emod_lt_of_pos x hLpos
  let n : Nat := m.toNat
  have hn : (n : Int) = m := Int.toNat_of_nonneg hm0
  have hnL : n < L := by
    have : (n : Int) < L := by rw [hn]; exact hmL
    exact_mod_cast this
  rcases hitNat_spec (checkBelow_spec hchk n hnL) with ⟨c, hc, hmod⟩
  refine ⟨c, hc, ?_⟩
  unfold Cls.mem
  rcases modsDivide_spec hdiv c hc with ⟨hdpos, hdL⟩
  -- x - r = (x - m) + (m - r); d ∣ L ∣ x - m, and d ∣ n - r = m - r
  have h1 : (c.d : Int) ∣ x - m := by
    have hx : x - m = (L : Int) * (x / L) := by
      have := Int.emod_add_ediv x L
      -- x % L + L * (x / L) = x
      show x - x % (L:Int) = (L:Int) * (x / L)
      omega
    rw [hx]
    exact Int.dvd_trans (Int.ofNat_dvd.mpr hdL) (Int.dvd_mul_right _ _)
  have h2 : (c.d : Int) ∣ m - c.r := by
    rw [← hn]; exact int_dvd_of_nat_mod_eq hmod
  have : x - (c.r : Int) = (x - m) + (m - c.r) := by omega
  rw [this]
  exact Int.dvd_add h1 h2

end Covering
