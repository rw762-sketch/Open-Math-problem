/-
Counting residues in congruence classes and in CRT "avoidance" sets.

Everything is stated for a fixed period `L > 0` and sets of residues in `Finset.range L`.
-/
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Zify
import Mathlib.Tactic.Positivity

namespace Covering

open Finset

/-- Residues `n < L` with `n ≡ r (mod d)`. -/
def cls (L r d : ℕ) : Finset ℕ := (range L).filter (fun n => n ≡ r [MOD d])

/-- Residues `n < L` avoiding the class `a p (mod p)` for every `p ∈ Q`. -/
def avoid (L : ℕ) (Q : Finset ℕ) (a : ℕ → ℕ) : Finset ℕ :=
  (range L).filter (fun n => ∀ p ∈ Q, ¬ n ≡ a p [MOD p])

theorem mem_cls {L r d n : ℕ} : n ∈ cls L r d ↔ n < L ∧ n ≡ r [MOD d] := by
  simp [cls]

theorem mem_avoid {L n : ℕ} {Q : Finset ℕ} {a : ℕ → ℕ} :
    n ∈ avoid L Q a ↔ n < L ∧ ∀ p ∈ Q, ¬ n ≡ a p [MOD p] := by
  simp [avoid]

/-- Exact size of a class when the modulus divides the period. -/
theorem card_cls {L r d : ℕ} (hd : 0 < d) (hdL : d ∣ L) : (cls L r d).card = L / d := by
  have h := Nat.count_modEq_card L hd r
  rw [Nat.count_eq_card_filter_range] at h
  unfold cls
  rw [h]
  simp [Nat.mod_eq_zero_of_dvd hdL]

end Covering

namespace Covering
open Finset

theorem avoid_empty (L : ℕ) (a : ℕ → ℕ) : avoid L ∅ a = range L := by
  ext n; simp [avoid]

/-- Peeling one prime off the avoidance set. -/
theorem cls_inter_avoid_insert (L r d q : ℕ) (Q : Finset ℕ) (a : ℕ → ℕ) :
    cls L r d ∩ avoid L (insert q Q) a =
      (cls L r d ∩ avoid L Q a) \ (cls L (a q) q) := by
  ext n
  simp only [mem_inter, mem_cls, mem_avoid, mem_sdiff, mem_insert, forall_eq_or_imp]
  tauto

/-- CRT: intersecting with a class mod a coprime `q` is a class mod `d*q`. -/
theorem cls_inter_cls (L r d q s : ℕ) (h : Nat.Coprime d q) :
    ∃ r', cls L r d ∩ cls L s q = cls L r' (d * q) := by
  obtain ⟨k, hk1, hk2⟩ := Nat.chineseRemainder h r s
  refine ⟨k, ?_⟩
  ext n
  simp only [mem_inter, mem_cls]
  constructor
  · rintro ⟨⟨hn, h1⟩, _, h2⟩
    refine ⟨hn, ?_⟩
    exact (Nat.modEq_and_modEq_iff_modEq_mul h).mp ⟨h1.trans hk1.symm, h2.trans hk2.symm⟩
  · rintro ⟨hn, h12⟩
    rcases (Nat.modEq_and_modEq_iff_modEq_mul h).mpr h12 with ⟨h1, h2⟩
    exact ⟨⟨hn, h1.trans hk1⟩, hn, h2.trans hk2⟩

end Covering

namespace Covering
open Finset

/-- The CRT product count. For a finite set `Q` of primes dividing `L`, residues `a`, and a
modulus `d ∣ L` coprime to every element of `Q`:
`#(cls r d ∩ avoid Q a) · ∏_{p∈Q} p = (L/d) · ∏_{p∈Q} (p-1)`. -/
theorem card_cls_inter_avoid (L : ℕ) (a : ℕ → ℕ) (Q : Finset ℕ)
    (hQp : ∀ p ∈ Q, p.Prime) (hQL : ∀ p ∈ Q, p ∣ L) :
    ∀ d r, 0 < d → d ∣ L → (∀ p ∈ Q, Nat.Coprime p d) →
      (cls L r d ∩ avoid L Q a).card * ∏ p ∈ Q, p = (L / d) * ∏ p ∈ Q, (p - 1) := by
  induction Q using Finset.induction_on with
  | empty =>
    intro d r hd hdL _
    rw [avoid_empty, prod_empty, prod_empty, mul_one, mul_one]
    have : cls L r d ∩ range L = cls L r d :=
      inter_eq_left.mpr (filter_subset _ _)
    rw [this, card_cls hd hdL]
  | insert q Q hq ih =>
    intro d r hd hdL hcop
    have hqp : q.Prime := hQp q (mem_insert_self q Q)
    have hqL : q ∣ L := hQL q (mem_insert_self q Q)
    have hQp' : ∀ p ∈ Q, p.Prime := fun p hp => hQp p (mem_insert_of_mem hp)
    have hQL' : ∀ p ∈ Q, p ∣ L := fun p hp => hQL p (mem_insert_of_mem hp)
    have hcop' : ∀ p ∈ Q, Nat.Coprime p d := fun p hp => hcop p (mem_insert_of_mem hp)
    have hdq : Nat.Coprime d q := (hcop q (mem_insert_self q Q)).symm
    have hcopq : ∀ p ∈ Q, Nat.Coprime p q := fun p hp => by
      have hne : p ≠ q := fun h => hq (h ▸ hp)
      exact (Nat.coprime_primes (hQp' p hp) hqp).mpr hne
    have hcop2 : ∀ p ∈ Q, Nat.Coprime p (d * q) :=
      fun p hp => Nat.Coprime.mul_right (hcop' p hp) (hcopq p hp)
    have hdqL : d * q ∣ L := Nat.Coprime.mul_dvd_of_dvd_of_dvd hdq hdL hqL
    obtain ⟨r', hr'⟩ := cls_inter_cls L r d q (a q) hdq
    rw [cls_inter_avoid_insert]
    have hAC : (cls L r d ∩ avoid L Q a) ∩ cls L (a q) q = cls L r' (d * q) ∩ avoid L Q a := by
      rw [inter_right_comm, hr']
    have h1 := ih hQp' hQL' d r hd hdL hcop'
    have h2 := ih hQp' hQL' (d * q) r' (Nat.mul_pos hd hqp.pos) hdqL hcop2
    rw [← hAC] at h2
    have hsub := card_sdiff_add_card_inter (cls L r d ∩ avoid L Q a) (cls L (a q) q)
    rw [prod_insert hq, prod_insert hq]
    have hk : L / (d * q) * q = L / d := by
      rw [← Nat.div_div_eq_div_mul]
      exact Nat.div_mul_cancel (Nat.dvd_div_of_mul_dvd hdqL)
    have hq1 : 1 ≤ q := hqp.one_lt.le
    rw [← hsub] at h1
    set x := ((cls L r d ∩ avoid L Q a) \ cls L (a q) q).card
    set y := ((cls L r d ∩ avoid L Q a) ∩ cls L (a q) q).card
    set P := ∏ p ∈ Q, p
    set X := ∏ p ∈ Q, (p - 1)
    set m := L / d
    set k := L / (d * q)
    zify [hq1] at h1 h2 hk ⊢
    linear_combination (q : ℤ) * h1 - (q : ℤ) * h2 - (X : ℤ) * hk

end Covering
