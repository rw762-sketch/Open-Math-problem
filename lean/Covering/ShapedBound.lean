/-
End-to-end lcm bounds from a finite check over shaped (initial-run) moduli.

`odd_covering_lcm_gt_of_chkGen`: if `check2` (density or tower certificate) holds for every shaped
odd `L ≤ N`, as verified by `chkGen`, then every odd distinct covering of ℤ has lcm `> N`.
-/
import Covering.Shaped
import Covering.TowerCheck

namespace Covering

open Finset

theorem OP_small : ∀ p < 53, p.Prime → p ≠ 2 → p ∈ OP := by decide

theorem OP_primes : ∀ p ∈ OP, p.Prime ∧ 2 < p := by decide

theorem OP_sorted : OP.Sorted (· < ·) := by decide

theorem OP_pairwise : OP.Pairwise Nat.Coprime := by decide

theorem OP_lt53 : ∀ p ∈ OP, p < 53 := by decide

theorem list_prod_dvd {L : ℕ} : ∀ ps : List ℕ, ps.Pairwise Nat.Coprime → (∀ p ∈ ps, p ∣ L) →
    ps.prod ∣ L := by
  intro ps
  induction ps with
  | nil => intro _ _; simp
  | cons p rest ih =>
    intro hpw hd
    rw [List.pairwise_cons] at hpw
    rw [List.prod_cons]
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (Nat.coprime_list_prod_right_iff.mpr hpw.1)
      (hd p (List.mem_cons_self ..)) (ih hpw.2 (fun r hr => hd r (List.mem_cons_of_mem _ hr)))

theorem primes_in_OP {L N : ℕ} (hodd : Odd L) (hL0 : L ≠ 0) (hsh : Shaped L) (hLN : L ≤ N)
    (hN : N < OP.prod) : ∀ q, q.Prime → q ∣ L → q ∈ OP := by
  intro q hq hqL
  by_contra hnot
  have hq2 : q ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hqL)
  have hq53 : 53 ≤ q := by
    by_contra h
    exact hnot (OP_small q (by omega) hq hq2)
  have hqF : q ∈ L.primeFactors := Nat.mem_primeFactors.mpr ⟨hq, hqL, hL0⟩
  have hall : ∀ p ∈ OP, p ∣ L := fun p hp =>
    hsh q hqF p (OP_primes p hp).1 (OP_primes p hp).2 (lt_of_lt_of_le (OP_lt53 p hp) hq53)
  have := Nat.le_of_dvd (Nat.pos_of_ne_zero hL0) (list_prod_dvd OP OP_pairwise hall)
  omega

theorem odd_covering_lcm_gt_of_chkGen (N : ℕ) (hN : N < 2 ^ 64) (hNP : N < OP.prod)
    (h : chkGen check2 N OP 1 = true)
    (S : Finset Cls) (hgt : ∀ c ∈ S, 1 < c.d) (hodd : ∀ c ∈ S, Odd c.d)
    (hinj : ∀ c ∈ S, ∀ c' ∈ S, c.d = c'.d → c = c') (hcov : CoversZ S) :
    N < S.lcm (·.d) := by
  by_contra hle
  push_neg at hle
  have hS := isCovering_lcm S hgt hinj hcov
  obtain ⟨L', hL'le, hL'odd, hsh, S', hS'⟩ := reduce_to_shaped _ (lcm_odd S hodd) S hS
  have hL'N : L' ≤ N := hL'le.trans hle
  have hL'0 : L' ≠ 0 := hS'.pos.ne'
  have hL'1 : L' ≠ 1 := by
    intro h1
    obtain ⟨c, hc, _⟩ := hS'.cov 0 hS'.pos
    have := Nat.le_of_dvd hS'.pos (hS'.dvd c hc)
    have := hS'.gt c hc
    omega
  have hG : Gen OP L' := gen_of_shaped OP OP_sorted OP_primes 1 L' hL'0
    (primes_in_OP hL'odd hL'0 hsh hL'N hNP) (fun p _ => Nat.coprime_one_left p)
    (by rw [one_mul]; exact hsh)
  have hc := chkGen_complete hN OP L' hG (fun p hp => by have := (OP_primes p hp).2; omega)
    1 Nat.one_pos (by rw [one_mul]; exact hL'N) h
  rw [one_mul] at hc
  have hc2 : check2 L' = true := by
    simp only [Bool.or_eq_true, beq_iff_eq] at hc
    rcases hc with h1 | h1
    · exact absurd h1 hL'1
    · exact h1
  exact no_covering_of_check2 hc2 S' hS'

end Covering
